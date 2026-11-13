(* Forge the .vo files of rocqchk_register_type.sh: a library that
   registers as the int63 primitive type a constant that Primitive did not
   declare. The typing of an int63 literal uses the registered constant:
   when the axiom zero's type unfolds to Empty_set and zero gets the body
   Int 0, boom : False := match zero return False with end is a closed
   proof of False; when a sealed module's implementation defines its int as
   Empty_set, its int_empty : int -> False applied to a literal is one.
   coqc registers a primitive type only for the constant that Primitive
   declares, so the registration is written here. It also forges a library
   whose axiom add : int -> int -> False becomes the primitive operator
   Int63add, which coqc declares only with the type int -> int -> int.

   It uses only the OCaml standard library, and these value layouts, from
   checker/values.ml:

   - library segment: (compiled_library, _, _); compiled_library has 6
     fields, 1 the root module_body and 4 the dependencies, an array of
     (dirpath, vodigest); summary segment: field 1, the same dependencies;
   - module_body: 1 signature, NoFunctor (tag 0) [structure]; 4
     mod_retroknowledge, ModBodyVal (tag 0) [list of retro_action];
   - structure: a list of (label, field); SFBconst is tag 0
     [constant_body], SFBmodule tag 3 [module_body];
   - constant_body: 2 body, Undef (tag 0) [inline] | Def (tag 1) [term] |
     Primitive (tag 3) [primitive], the enum CPrimitives.t having
     Int63add = 2; 3 type;
   - term: Prod is tag 6 [binder; domain; codomain]; Const tag 10
     [(constant, instance)]; Int tag 17 [uint63], an immediate integer on a
     64-bit platform;
   - constant: Same (tag 0) [kn] | Dual (tag 1) [user kn; canonical kn];
   - retro_action: Register_type is tag 1 [prim_type; constant], the enum
     prim_type having PT_int63 = 0.

   Commands (each writes a new file; the inputs are left as they are):
     forge.ml regtype LIB.vo OUT.vo
       zero := Int 0, and the registration of the constant that zero's type
       names, as LIB.vo names it;
     forge.ml dual LIB.vo OUT.vo
       zero := Int 0, and the registration of the name whose user name is
       the one of the parameter carrier, read from carrier_alias's body, and
       whose canonical name is the one of the constant that zero's type
       names;
     forge.ml register LIB.vo OUT.vo PATH
       the registration of PATH.int, the constant that the domain of the
       type of PATH.int_empty names in the signature of the module PATH
       (labels separated by dots), by its user name;
     forge.ml primop LIB.vo OUT.vo
       add, an axiom, becomes the primitive operator Int63add, whatever its
       type;
     forge.ml client CLIENT.vo LIB.vo LIB_DIRPATH OUT.vo
       CLIENT.vo, recording LIB.vo's digest as the one of LIB_DIRPATH.

   misc/rocqchk_repeated_label.sh runs regtype too, and
   misc/rocqchk-repeated-label/forge.ml copies the code of this file that
   reads and writes the segments of a .vo file, edits its values, prints
   names and writes a client. *)

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
let to_str (o : Obj.t) : string = Obj.obj o
let to_int (o : Obj.t) : int = Obj.obj o

let block t fields =
  let b = Obj.new_block t (Array.length fields) in
  Array.iteri (fun i v -> Obj.set_field b i v) fields;
  b

let expect what t o =
  if Obj.is_int o || tag o <> t then
    fail "%s: expected a block with tag %d, found %s" what t
      (if Obj.is_int o then Printf.sprintf "the integer %d" (to_int o)
       else Printf.sprintf "tag %d" (tag o))

(* [o] with field [i] replaced by [f] of it; [o] is copied only when the
   field changes, so that a value shared with another part of the file is
   never modified in place. *)
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
  | 1 -> "<bound module>"
  | 2 -> mp_to_string (field mp 0) ^ "." ^ to_str (field mp 1)
  | t -> fail "module path with tag %d" t

let kn_to_string kn = mp_to_string (field kn 0) ^ "." ^ to_str (field kn 1)

let cst_to_string c =
  if tag c = 0 then kn_to_string (field c 0)
  else
    Printf.sprintf "%s, canonical name %s" (kn_to_string (field c 0))
      (kn_to_string (field c 1))

(* {1 The library} *)

let root_module disk = field (field disk 0) 1

let set_root_module disk mb = Obj.set_field (field disk 0) 1 mb

let root_struc disk =
  let sign = field (root_module disk) 1 in
  expect "the library's signature (NoFunctor)" 0 sign;
  field sign 0

let item_label item = to_str (field item 0)

(* The constant_body of the field [name] of [struc]. *)
let struc_find struc name =
  match List.find_opt (fun it -> String.equal (item_label it) name) (list_of struc) with
  | Some it ->
    let sfb = field it 1 in
    expect ("field " ^ name ^ " (a constant)") 0 sfb;
    field sfb 0
  | None -> fail "no field %s" name

(* [struc] with [f] applied to the constant_body of its field [name]. *)
let struc_update struc name f =
  ignore (struc_find struc name);
  map_list
    (fun it -> if String.equal (item_label it) name then upd 1 (upd 0 f) it else it)
    struc

(* The constant of the term [c], which must be a Const. *)
let const_of what c =
  expect what 10 c;
  field (field c 0) 0

(* The structure of the signature of the module [path] of the library. *)
let module_struc disk path =
  let enter struc name =
    match List.find_opt (fun it -> String.equal (item_label it) name) (list_of struc) with
    | Some it ->
      let sfb = field it 1 in
      expect ("field " ^ name ^ " (a module)") 3 sfb;
      let sign = field (field sfb 0) 1 in
      expect ("the signature of " ^ name ^ " (NoFunctor)") 0 sign;
      field sign 0
    | None -> fail "no field %s" name
  in
  List.fold_left enter (root_struc disk) (String.split_on_char '.' path)

(* [disk] with Register_type (PT_int63, registered) added to the root
   module's retroknowledge. *)
let add_registration disk registered =
  let retro = field (root_module disk) 4 in
  expect "mod_retroknowledge (ModBodyVal)" 0 retro;
  let actions = field retro 0 in
  say "forging: the library's retroknowledge (%d action(s)) gets Register_type (PT_int63, %s)"
    (List.length (list_of actions)) (cst_to_string registered);
  let action = block 1 [| Obj.repr 0; registered |] in
  set_root_module disk (set 4 (block 0 [| block 0 [| action; actions |] |]) (root_module disk));
  disk

let forge ~dual disk =
  if Sys.word_size <> 64 then fail "Int 0 is written as a 64-bit immediate integer";
  let compiled = field disk 0 in
  if size compiled <> 6 then fail "compiled_library has %d fields, not 6" (size compiled);
  let root = root_struc disk in
  let zero = struc_find root "zero" in
  expect "zero's body (Undef)" 0 (field zero 2);
  let int = const_of "zero's type (a constant)" (field zero 3) in
  expect "the constant of zero's type (Same)" 0 int;
  let registered =
    if not dual then int
    else
      let alias = field (struc_find root "carrier_alias") 2 in
      expect "carrier_alias's body (Def)" 1 alias;
      let carrier = const_of "carrier_alias's body (a constant)" (field alias 0) in
      expect "the constant carrier (Same)" 0 carrier;
      block 1 [| field carrier 0; field int 0 |]
  in
  let int0 = block 17 [| Obj.repr 0 |] in
  let root = struc_update root "zero" (set 2 (block 1 [| int0 |])) in
  set_root_module disk (upd 1 (set 0 root) (root_module disk));
  say "forging: zero's body becomes Def (Int 0)";
  add_registration disk registered

let register path disk =
  let compiled = field disk 0 in
  if size compiled <> 6 then fail "compiled_library has %d fields, not 6" (size compiled);
  let ty = field (struc_find (module_struc disk path) "int_empty") 3 in
  expect (path ^ ".int_empty's type (a product)") 6 ty;
  let int = const_of ("the domain of " ^ path ^ ".int_empty's type (a constant)") (field ty 1) in
  say "forging: %s.int_empty's type names %s" path (cst_to_string int);
  add_registration disk (block 0 [| field int 0 |])

let primop disk =
  let compiled = field disk 0 in
  if size compiled <> 6 then fail "compiled_library has %d fields, not 6" (size compiled);
  let root = root_struc disk in
  expect "add's body (Undef)" 0 (field (struc_find root "add") 2);
  let root = struc_update root "add" (set 2 (block 3 [| Obj.repr 2 |])) in
  set_root_module disk (upd 1 (set 0 root) (root_module disk));
  say "forging: add's body becomes Primitive Int63add";
  disk

(* {1 The client} *)

(* Record [digest] as the dependency [lib_dp]'s, in the summary and in the
   compiled library (Safe_typing.import compares the latter with the
   library rocqchk loads). *)
let patch_deps ~what ~lib_dp ~digest deps =
  let n = ref 0 in
  for i = 0 to size deps - 1 do
    let d = field deps i in
    if String.equal (dp_to_string (field d 0)) lib_dp then begin
      say "forging: %s dependency %s gets the digest %s" what lib_dp (Digest.to_hex digest);
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
  | [ "regtype"; src; dst ] -> rewrite_vo ~src ~dst [ "library", forge ~dual:false ]
  | [ "dual"; src; dst ] -> rewrite_vo ~src ~dst [ "library", forge ~dual:true ]
  | [ "register"; src; dst; path ] -> rewrite_vo ~src ~dst [ "library", register path ]
  | [ "primop"; src; dst ] -> rewrite_vo ~src ~dst [ "library", primop ]
  | [ "client"; src; lib; lib_dp; dst ] ->
    let digest = library_hash lib in
    rewrite_vo ~src ~dst
      [ ("summary", fun sd -> patch_deps ~what:"summary" ~lib_dp ~digest (field sd 1); sd);
        ("library", fun disk ->
            patch_deps ~what:"library" ~lib_dp ~digest (field (field disk 0) 4); disk) ]
  | _ ->
    prerr_endline
      "usage: ocaml forge.ml regtype LIB.vo OUT.vo | dual LIB.vo OUT.vo\n\
      \       | register LIB.vo OUT.vo PATH | primop LIB.vo OUT.vo\n\
      \       | client CLIENT.vo LIB.vo LIB_DIRPATH OUT.vo";
    exit 2
