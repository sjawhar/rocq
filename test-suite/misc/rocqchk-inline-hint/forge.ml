(* Forge .vo files whose delta resolvers carry an inline hint with an open
   term, M.d -> Inline (0, Some (Rel 1)), and the clients that use them. A
   substitution through such a resolver puts the term in place of the
   constant, under binders and without lifting, so that the nearest binder
   captures its Rel 1:
   - sealed: in the implementation resolver of a sealed module, through which
     the sealing check substitutes the expected signature;
   - functor: in the resolver of a functor's argument, through which a
     functor application substitutes the functor's body.

   Like misc/rocqchk-delta-alias/forge.ml, this uses only the OCaml standard
   library: it is an untrusted file producer, not another path through the
   kernel API. The value layouts it relies on are checker/values.ml's:

   - library segment: (compiled_library, _, _); compiled_library fields
     0 name, 1 root module_body, 4 dependencies (dirpath, vodigest) array;
   - summary segment: field 1, the same dependencies;
   - module_body: 0 implementation wrapper [Struct is tag 1 [resolver;
     structure]], 1 signature, 3 delta resolver;
   - signature: NoFunctor (tag 0) [structure]; structure: list of
     (label, field); field tags 0 constant, 3 module;
   - constant_body: 2 body (Def is tag 1 [term]), 3 type;
   - term: Rel is tag 0 [int]; Const is tag 10 [(constant, instance)];
     constant: Same (tag 0) [kn]; kn: [modpath; label; hash];
   - delta resolver: [root; module map; kernel-name map], the last an Int.Map
     from a name's stored hash to a KerName.Map of delta hints, Inline being
     tag 0 [level; univ_abstracted constr option]; maps are the standard
     library's AVL nodes [l; key; data; r; height].

   Commands (each writes a new file; the inputs are left as they are):
     forge.ml sealed DONOR_LIB.vo HONEST_LIB.vo OUT.vo
     forge.ml functor HONEST_LIB.vo OUT.vo
     forge.ml client CLIENT.vo LIB.vo LIB_DIRPATH OUT.vo *)

let fail fmt = Printf.ksprintf failwith fmt
let say fmt = Printf.ksprintf (fun s -> print_string s; print_newline ()) fmt

(* {1 Segments} *)

type segment = {
  name : string;
  pos : int64;
  len : int64;
  hash : string;
}

let input_int64 ch =
  let rec go i accu =
    if i = 0 then accu
    else
      go (i - 1)
        (Int64.logor (Int64.shift_left accu 8)
           (Int64.of_int (input_byte ch)))
  in
  go 8 0L

let output_int64 ch n =
  for shift = 7 downto 0 do
    output_byte ch
      (Int64.to_int (Int64.logand 255L (Int64.shift_right_logical n (8 * shift))))
  done

let read_segments ch =
  seek_in ch 8;
  let summary_pos = input_int64 ch in
  LargeFile.seek_in ch summary_pos;
  let n = input_binary_int ch in
  Array.init n (fun _ ->
      let name = really_input_string ch (input_binary_int ch) in
      let pos = input_int64 ch in
      let len = input_int64 ch in
      let hash = really_input_string ch 16 in
      { name; pos; len; hash })

let read_vo file =
  let input = open_in_bin file in
  let header = really_input_string input 8 in
  let segments = read_segments input in
  let contents =
    Array.map
      (fun segment ->
        LargeFile.seek_in input segment.pos;
        segment.name, really_input_string input (Int64.to_int segment.len))
      segments
  in
  close_in input;
  header, segments, contents

let write_vo file header contents =
  let temporary = file ^ ".forged" in
  let output = open_out_bin temporary in
  output_string output header;
  output_int64 output 0L;
  let rewritten =
    Array.map
      (fun (name, data) ->
        let pos = LargeFile.pos_out output in
        output_string output data;
        let hash = Digest.string data in
        output_string output hash;
        { name; pos; len = Int64.of_int (String.length data); hash })
      contents
  in
  let summary_pos = LargeFile.pos_out output in
  output_binary_int output (Array.length rewritten);
  Array.iter
    (fun segment ->
      output_binary_int output (String.length segment.name);
      output_string output segment.name;
      output_int64 output segment.pos;
      output_int64 output segment.len;
      output_string output segment.hash)
    rewritten;
  LargeFile.seek_out output 8L;
  output_int64 output summary_pos;
  close_out output;
  Sys.rename temporary file

let segment_value contents name =
  match Array.find_opt (fun (n, _) -> String.equal n name) contents with
  | Some (_, data) -> Obj.repr (Marshal.from_string data 0)
  | None -> fail "no %s segment" name

(* Rewrite the segments named in [edits] with their functions, keep the
   others byte for byte, and write [dst] with fresh segment checksums. *)
let rewrite_vo ~src ~dst edits =
  let header, _, contents = read_vo src in
  List.iter
    (fun (name, _) ->
      if not (Array.exists (fun (n, _) -> String.equal n name) contents) then
        fail "%s has no %s segment" src name)
    edits;
  let contents =
    Array.map
      (fun (name, data) ->
        match List.assoc_opt name edits with
        | None -> name, data
        | Some edit ->
          let value = edit (Obj.repr (Marshal.from_string data 0)) in
          name, Marshal.to_string (Obj.obj value) [])
      contents
  in
  write_vo dst header contents

(* {1 Values} *)

let field = Obj.field
let tag = Obj.tag
let size = Obj.size
let is_block o = not (Obj.is_int o)
let to_str (o : Obj.t) : string = Obj.obj o
let to_int (o : Obj.t) : int = Obj.obj o
let empty = Obj.repr 0

let block t fields =
  let b = Obj.new_block t (Array.length fields) in
  Array.iteri (fun i v -> Obj.set_field b i v) fields;
  b

let expect what t o =
  if Obj.is_int o || tag o <> t then
    fail "%s: expected a block with tag %d, found %s" what t
      (if Obj.is_int o then Printf.sprintf "the integer %d" (to_int o)
       else Printf.sprintf "tag %d" (tag o))

(* [o] with field [i] replaced by [f] of it; [o] is copied only when the field
   changes, so that a value shared with another part of the file is never
   modified in place. *)
let upd i f o =
  let x = field o i in
  let y = f x in
  if y == x then o
  else begin
    let o' = Obj.dup o in
    Obj.set_field o' i y;
    o'
  end

let set i v o = upd i (fun _ -> v) o

let map_array f a =
  let res = ref a in
  for i = 0 to size a - 1 do
    let x = field a i in
    let y = f x in
    if y != x then begin
      if !res == a then res := Obj.dup a;
      Obj.set_field !res i y
    end
  done;
  !res

let rec list_of o = if Obj.is_int o then [] else field o 0 :: list_of (field o 1)

let rec map_list f l =
  if Obj.is_int l then l
  else
    let hd = field l 0 and tl = field l 1 in
    let hd' = f hd and tl' = map_list f tl in
    if hd' == hd && tl' == tl then l else block 0 [| hd'; tl' |]

(* {1 Names} *)

let dp_to_string dp = String.concat "." (List.rev_map to_str (list_of dp))

let rec mp_to_string mp =
  match tag mp with
  | 0 -> dp_to_string (field mp 0)
  | 1 ->
    let mbid = field mp 0 in
    Printf.sprintf "<%s#%d>" (to_str (field mbid 1)) (to_int (field mbid 0))
  | 2 -> mp_to_string (field mp 0) ^ "." ^ to_str (field mp 1)
  | t -> fail "module path with tag %d" t

let kn_mp kn = field kn 0
let kn_label kn = to_str (field kn 1)
let kn_hash kn = to_int (field kn 2)
let kn_to_string kn = mp_to_string (kn_mp kn) ^ "." ^ kn_label kn

let cst_user c = field c 0

let mp_is_dot name mp = tag mp = 2 && String.equal (to_str (field mp 1)) name

(* {1 Terms} *)

(* Copy-on-write map of [fc] over the Const nodes of a term. [fc] gets the
   (constant, instance) pair and returns its replacement, or None. *)
let rec map_constr fc c =
  if Obj.is_int c then c
  else
    let m = map_constr fc in
    match tag c with
    | 5 -> c |> upd 0 m |> upd 2 m (* Cast *)
    | 6 | 7 -> c |> upd 1 m |> upd 2 m (* Prod, Lambda *)
    | 8 -> c |> upd 1 m |> upd 2 m |> upd 3 m (* LetIn *)
    | 9 -> c |> upd 0 m |> upd 1 (map_array m) (* App *)
    | 10 -> (* Const *)
      (match fc (field c 0) with Some p -> block 10 [| p |] | None -> c)
    | 13 -> (* Case: info, instance, params, return, invert, scrutinee, branches *)
      c
      |> upd 2 (map_array m)
      |> upd 3 (upd 0 (upd 1 m))
      |> upd 4 (fun iv -> if Obj.is_int iv then iv else upd 0 (map_array m) iv)
      |> upd 5 m
      |> upd 6 (map_array (upd 1 m))
    | 14 | 15 -> (* Fix, CoFix: (_, (names, types, bodies)) *)
      upd 0 (upd 1 (fun prec -> prec |> upd 1 (map_array m) |> upd 2 (map_array m))) c
    | 16 -> upd 2 m c (* Proj *)
    | 20 -> c |> upd 1 (map_array m) |> upd 2 m |> upd 3 m (* Array *)
    | _ -> c

(* The type and, for a definition, the body of a constant_body. *)
let map_cb fc cb =
  cb
  |> upd 3 (map_constr fc)
  |> upd 2 (fun body -> if is_block body && tag body = 1 then upd 0 (map_constr fc) body else body)

let cb_constants cb =
  let acc = ref [] in
  ignore (map_cb (fun p -> acc := field p 0 :: !acc; None) cb);
  List.rev !acc

(* {1 Structures and modules} *)

let item_label item = to_str (field item 0)
let item_field item = field item 1

let struc_find struc name =
  match List.find_opt (fun it -> String.equal (item_label it) name) (list_of struc) with
  | Some it -> item_field it
  | None -> fail "no field %s" name

let struc_update struc name f =
  let found = ref false in
  let struc =
    map_list
      (fun it ->
        if String.equal (item_label it) name then begin
          found := true;
          upd 1 f it
        end
        else it)
      struc
  in
  if not !found then fail "no field %s" name;
  struc

let nofunctor what sign =
  expect (what ^ "'s signature (NoFunctor)") 0 sign;
  field sign 0

let module_of struc name =
  let sfb = struc_find struc name in
  expect ("field " ^ name ^ " (a module)") 3 sfb;
  field sfb 0

let impl_of mb = field (field mb 0) 0

(* The first constant mentioned by a constant of [struc] whose user name has
   label [label] and a module path satisfying [in_mp]. *)
let find_kn struc ~label ~in_mp =
  let found = ref None in
  List.iter
    (fun it ->
      let sfb = item_field it in
      if Option.is_none !found && tag sfb = 0 then
        List.iter
          (fun c ->
            let u = cst_user c in
            if Option.is_none !found && String.equal (kn_label u) label && in_mp (kn_mp u)
            then found := Some u)
          (cb_constants (field sfb 0)))
    (list_of struc);
  match !found with
  | Some kn -> kn
  | None -> fail "no constant labelled %s is mentioned there" label

let root_struc disk =
  let root = field (field disk 0) 1 in
  if is_block (impl_of root) then fail "the library's root module is not a plain structure";
  nofunctor "the library" (field root 1)

let set_root_struc disk struc =
  let compiled = field disk 0 in
  Obj.set_field compiled 1 (upd 1 (set 0 struc) (field compiled 1))

(* {1 Delta resolvers} *)

let height m = if Obj.is_int m then 0 else to_int (field m 4)

let create l k d r =
  let hl = height l and hr = height r in
  block 0 [| l; k; d; r; Obj.repr (if hl >= hr then hl + 1 else hr + 1) |]

(* The standard library's Map.bal. *)
let bal l k d r =
  let hl = height l and hr = height r in
  if hl > hr + 2 then begin
    let ll = field l 0 and lv = field l 1 and ld = field l 2 and lr = field l 3 in
    if height ll >= height lr then create ll lv ld (create lr k d r)
    else
      create (create ll lv ld (field lr 0)) (field lr 1) (field lr 2)
        (create (field lr 3) k d r)
  end
  else if hr > hl + 2 then begin
    let rl = field r 0 and rv = field r 1 and rd = field r 2 and rr = field r 3 in
    if height rr >= height rl then create (create l k d rl) rv rd rr
    else
      create (create l k d (field rl 0)) (field rl 1) (field rl 2)
        (create (field rl 3) rv rd rr)
  end
  else create l k d r

let rec map_add cmp k d m =
  if Obj.is_int m then create empty k d empty
  else
    let c = cmp k (field m 1) in
    if c = 0 then create (field m 0) k d (field m 3)
    else if c < 0 then bal (map_add cmp k d (field m 0)) (field m 1) (field m 2) (field m 3)
    else bal (field m 0) (field m 1) (field m 2) (map_add cmp k d (field m 3))

let rec map_find cmp k m =
  if Obj.is_int m then None
  else
    let c = cmp k (field m 1) in
    if c = 0 then Some (field m 2)
    else map_find cmp k (field m (if c < 0 then 0 else 3))

let int_compare a b = compare (to_int a) (to_int b)

(* KerName.compare: the label, then the module path. Only the label part is
   needed for the names this file adds. *)
let kn_compare a b =
  if a == b then 0
  else
    let c = String.compare (kn_label a) (kn_label b) in
    if c <> 0 then c
    else if compare (kn_mp a) (kn_mp b) = 0 then 0
    else fail "two names labelled %s share a hash bucket; ModPath.compare is not reimplemented here" (kn_label a)

(* HMap.add: bucket by the name's stored hash, then a KerName.Map. *)
let hmap_add kn hint hmap =
  let h = kn_hash kn in
  if h < 0 then fail "%s carries no hash" (kn_to_string kn);
  let bucket = match map_find int_compare (Obj.repr h) hmap with Some b -> b | None -> empty in
  map_add int_compare (Obj.repr h) (map_add kn_compare kn hint bucket) hmap

(* The hint Inline (0, Some t) for [kn], with t the open term Rel 1 and an
   empty universe context: UVars.AbstractContext.empty is laid out as
   (([||], [||]), (ElimConstraints.empty, UnivConstraints.empty)), empty sets
   being the integer 0 (checker/values.ml, v_abs_context and v_cstrs). *)
let rel1 = block 0 [| Obj.repr 1 |]
let empty_abstract_context =
  block 0 [| block 0 [| Obj.repr [||]; Obj.repr [||] |]; block 0 [| Obj.repr 0; Obj.repr 0 |] |]
let open_term = block 0 [| rel1; empty_abstract_context |]

let add_open_inline reso kn =
  upd 2 (hmap_add kn (block 0 [| Obj.repr 0; block 0 [| open_term |] |])) reso

(* {1 The forgeries} *)

(* Case sealed. [disk] is honest/Lib.vo, where M : S with
   S = sig d : bool; lem : forall b, eq bool b b end, and M's implementation
   is d := true, lem := fun b => eq_refl bool b. [donor] is donor/Lib.vo,
   whose M has the signature lem : forall b, eq bool b d.
   - M's stored signature (module_body field 1): the field lem becomes
     donor/Lib.vo's, so that the expected lem reads forall b, eq bool b M.d;
   - M's implementation resolver (the Struct (reso, _) of field 0) gets
     M.d -> Inline (0, Some (Rel 1)).
   M's implementation and its signature resolver are left as they are. The
   name M.d is taken from donor/Lib.vo's lem type, hash included. *)
let forge_sealed ~donor disk =
  let root = root_struc disk in
  let dsig = nofunctor "donor's module M" (field (module_of (root_struc donor) "M") 1) in
  let dkn = find_kn dsig ~label:"d" ~in_mp:(mp_is_dot "M") in
  let dlem = struc_find dsig "lem" in
  expect "donor's M.lem (a constant)" 0 dlem;
  let mb = module_of root "M" in
  let i = impl_of mb in
  if not (is_block i && tag i = 1) then fail "M's implementation is not Struct";
  say "forge: M's signature field lem is donor/Lib.vo's";
  let mb = upd 1 (upd 0 (fun struc -> struc_update struc "lem" (fun _ -> dlem))) mb in
  say "forge: M's implementation resolver gets %s -> Inline (0, Some (Rel 1))" (kn_to_string dkn);
  let mb = upd 0 (upd 0 (upd 0 (fun reso -> add_open_inline reso dkn))) mb in
  set_root_struc disk (struc_update root "M" (set 0 mb));
  disk

(* Case functor. [disk] is honest/Lib.vo, where A := struct d := true end,
   use_d := A.d names A.d, and F (P : XS) proves
   lem : (forall b, eq bool b P.d) -> eq bool true false. A's delta resolver
   (module_body field 3, through which F A substitutes F's parameter) gets
   A.d -> Inline (0, Some (Rel 1)). Nothing else changes. *)
let forge_functor disk =
  let root = root_struc disk in
  let dkn = find_kn root ~label:"d" ~in_mp:(mp_is_dot "A") in
  let a = module_of root "A" in
  say "forge: A's delta resolver gets %s -> Inline (0, Some (Rel 1))" (kn_to_string dkn);
  let a = upd 3 (fun reso -> add_open_inline reso dkn) a in
  set_root_struc disk (struc_update root "A" (set 0 a));
  disk

(* The client: record the library segment's checksum of [lib] as the
   dependency [lib_dp]'s, in the summary and in the compiled library
   (Safe_typing.import compares the latter with the library rocqchk loads). *)
let patch_deps ~what ~lib_dp ~digest deps =
  let n = ref 0 in
  for i = 0 to size deps - 1 do
    let d = field deps i in
    if String.equal (dp_to_string (field d 0)) lib_dp then begin
      Obj.set_field deps i (block 0 [| field d 0; block 0 [| Obj.repr digest |] |]);
      incr n
    end
  done;
  if !n = 0 then fail "the %s records no dependency %s" what lib_dp

let library_hash file =
  let _, segments, _ = read_vo file in
  match Array.find_opt (fun s -> String.equal s.name "library") segments with
  | Some s -> s.hash
  | None -> fail "%s has no library segment" file

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [ "sealed"; donor; src; dst ] ->
    let _, _, contents = read_vo donor in
    let donor = segment_value contents "library" in
    rewrite_vo ~src ~dst [ "library", forge_sealed ~donor ]
  | [ "functor"; src; dst ] -> rewrite_vo ~src ~dst [ "library", forge_functor ]
  | [ "client"; src; lib; lib_dp; dst ] ->
    let digest = library_hash lib in
    rewrite_vo ~src ~dst
      [ ("summary", fun sd -> patch_deps ~what:"summary" ~lib_dp ~digest (field sd 1); sd);
        ("library", fun disk ->
            patch_deps ~what:"library" ~lib_dp ~digest (field (field disk 0) 4); disk) ]
  | _ ->
    prerr_endline
      "usage: forge.ml sealed DONOR_LIB.vo LIB.vo OUT.vo | functor LIB.vo OUT.vo\n\
      \       | client CLIENT.vo LIB.vo LIB_DIRPATH OUT.vo";
    exit 2
