(* Forge a .vo file whose functor records, in the delta resolver of its
   body, an alias that changes label, for rocqchk_alias_label.sh: in
   F (P : S), F.k becomes an alias of P.X.d. F.k := P.X.d converts with its
   target. A functor application rebuilds a name's canonical part with the
   user name's label (Mod_subst.subst_con0_flat), so (F.k, P.X.d) becomes
   (G.k, A.X.k) in G := F A: a field that F never named.

   Like ../rocqchk-sigalias/forge.ml, whose segment reading and writing and
   value helpers are copied here unchanged, this uses only the OCaml
   standard library: it is an untrusted file producer, not another path
   through the kernel API. The value layouts it relies on are
   checker/values.ml's:

   - library segment: (compiled_library, _, _); compiled_library fields
     0 name, 1 root module_body, 4 dependencies (dirpath, vodigest) array;
   - summary segment: field 1, the same dependencies;
   - module_body: 0 implementation wrapper, 1 signature, 2 algebraic type,
     3 delta resolver; module_type_body: 1 signature, 3 delta resolver;
   - signature: NoFunctor (tag 0) [structure] | MoreFunctor (tag 1)
     [mbid; module_type_body; signature]; structure: list of (label, field);
     field tags 0 constant, 1 inductive, 2 rules, 3 module, 4 module type;
   - constant_body: 2 body (Undef 0 | Def 1 [term] | ...), 3 type;
   - term: Const is tag 10 [(constant, instance)]; constant: Same (tag 0)
     [kn] | Dual (tag 1) [user kn; canonical kn]; kn: [modpath; label; hash];
   - delta resolver: [root; module map; kernel-name map], the last an Int.Map
     from a name's stored hash to a KerName.Map of delta hints, Equiv being
     tag 1 [kn]; maps are the standard library's AVL nodes [l; key; data; r;
     height].

   Commands (each writes a new file; the input is left as it is):
     forge.ml label HONEST_LIB.vo OUT.vo
     forge.ml client CLIENT.vo LIB.vo LIB_DIRPATH OUT.vo *)

let fail fmt = Printf.ksprintf failwith fmt
let say fmt = Printf.ksprintf (fun s -> print_string s; print_newline ()) fmt

(* {1 Segments, as upstream's forge.ml} *)

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
  Sys.rename temporary file;
  rewritten

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
  let segments = write_vo dst header contents in
  Array.iter
    (fun s ->
      say "wrote %s: segment %s, %Ld bytes, checksum %s" dst s.name s.len
        (Digest.to_hex s.hash))
    segments

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

let kn_equal a b =
  a == b
  || (String.equal (kn_label a) (kn_label b) && compare (kn_mp a) (kn_mp b) = 0)

let cst_user c = field c 0

let dual user canonical = block 1 [| user; canonical |]

let mp_is_dot name mp = tag mp = 2 && String.equal (to_str (field mp 1)) name
let mp_is_bound mp = tag mp = 1

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

(* A rewrite of Const nodes that counts what it changes. *)
let counted count f p =
  match f p with
  | Some _ as r -> incr count; r
  | None -> None

(* Name the constant [user] as an alias of [canonical] where a term mentions
   it: (user) becomes (user, canonical). *)
let retarget ~user ~canonical p =
  let c = field p 0 in
  if kn_equal (cst_user c) user then Some (block 0 [| dual (cst_user c) canonical; field p 1 |])
  else None

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

let impl_kind i =
  if Obj.is_int i then
    match to_int i with 0 -> "Abstract" | 1 -> "FullStruct" | n -> Printf.sprintf "implementation %d" n
  else
    match tag i with 0 -> "Algebraic" | 1 -> "Struct" | t -> Printf.sprintf "implementation tag %d" t

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
  let i = impl_of root in
  if is_block i then fail "the library's root module has a %s implementation" (impl_kind i);
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

let add_equiv reso user canonical = upd 2 (hmap_add user (block 1 [| canonical |])) reso

let vodigest_to_string v =
  if tag v = 0 then Digest.to_hex (to_str (field v 0))
  else Printf.sprintf "vodigest tag %d" (tag v)

(* {1 Forgeries} *)

(* The constant fields of a structure, each rewritten by [map_cb fc]. *)
let map_consts fc =
  map_list (upd 1 (fun sfb -> if tag sfb = 0 then upd 0 (map_cb fc) sfb else sfb))

(* <P#n>.X: the module path MPdot (MPbound _, X). *)
let mp_is_px mp = mp_is_dot "X" mp && mp_is_bound (field mp 0)

(* In the body of functor F (P : S), whose fields are k := P.X.d and
   lemma : eq bool k false := P.X.f, record that F.k is an alias of P.X.d,
   from label k to label d: F's delta resolver (module_body field 3, the
   resolver of F's body) gets the entry, and every mention of F.k (lemma's
   type) is named (user F.k, canonical P.X.d), which is how a term must name
   it once the resolver says so (Typeops.check_constant refuses any other
   canonical name). F.k's own declaration is not changed: it converts with
   its target P.X.d. Names are taken from the file, hash included, never
   rebuilt. *)
let forge_label disk =
  let root = root_struc disk in
  let fmb = module_of root "F" in
  let sign = field fmb 1 in
  expect "F's signature (MoreFunctor)" 1 sign;
  let body = nofunctor "F's body" (field sign 2) in
  let fk = find_kn body ~label:"k" ~in_mp:(mp_is_dot "F") in
  let xd = find_kn body ~label:"d" ~in_mp:mp_is_px in
  say "forging: in F's body, %s becomes an alias of %s" (kn_to_string fk) (kn_to_string xd);
  let in_body = ref 0 and in_impl = ref 0 in
  let rename count = map_consts (counted count (retarget ~user:fk ~canonical:xd)) in
  let sign = upd 2 (upd 0 (rename in_body)) sign in
  let fmb =
    fmb
    |> set 1 sign
    |> upd 0 (upd 0 (fun i -> if is_block i && tag i = 1 then upd 1 (rename in_impl) i else i))
    |> upd 3 (fun reso -> add_equiv reso fk xd)
  in
  if !in_body = 0 then fail "F's body does not mention %s" (kn_to_string fk);
  say "forging: renamed %d mention(s) of %s in F's body, %d in F's %s implementation"
    !in_body (kn_to_string fk) !in_impl (impl_kind (impl_of fmb));
  set_root_struc disk (struc_update root "F" (set 0 fmb));
  disk

(* The client: record [digest] as the dependency [lib_dp]'s, in the summary
   and in the compiled library (Safe_typing.import compares the latter with
   the library rocqchk loads). *)
let patch_deps ~what ~lib_dp ~digest deps =
  let n = ref 0 in
  for i = 0 to size deps - 1 do
    let d = field deps i in
    if String.equal (dp_to_string (field d 0)) lib_dp then begin
      say "forging: %s dependency %s: %s -> %s" what lib_dp (vodigest_to_string (field d 1))
        (Digest.to_hex digest);
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
  | [ "label"; src; dst ] -> rewrite_vo ~src ~dst [ "library", forge_label ]
  | [ "client"; src; lib; lib_dp; dst ] ->
    let digest = library_hash lib in
    rewrite_vo ~src ~dst
      [ ("summary", fun sd -> patch_deps ~what:"summary" ~lib_dp ~digest (field sd 1); sd);
        ("library", fun disk ->
            patch_deps ~what:"library" ~lib_dp ~digest (field (field disk 0) 4); disk) ]
  | _ ->
    prerr_endline
      "usage: ocaml forge.ml label LIB.vo OUT.vo | client CLIENT.vo LIB.vo LIB_DIRPATH OUT.vo";
    exit 2
