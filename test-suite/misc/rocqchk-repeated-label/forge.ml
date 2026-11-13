(* Forge the .vo files of rocqchk_repeated_label.sh: give a label of a
   library's structure to a second field, which coqc never does
   (Safe_typing.add_field).

   It uses only the OCaml standard library. The code that reads and writes
   the segments of a .vo file, edits its values, prints names and writes a
   client is a copy of the code of misc/rocqchk-register-type/forge.ml. It
   relies on these value layouts, from checker/values.ml:

   - library segment: (compiled_library, _, _); compiled_library field 1
     is the root module_body, field 4 the dependencies, an array of
     (dirpath, vodigest); summary segment: field 1, the same dependencies;
   - module_body and module_type_body: 1 signature, NoFunctor (tag 0)
     [structure]; 3 the delta resolver, whose field 0 is its root;
   - structure: a list of (label, field); SFBconst is tag 0
     [constant_body], SFBmodule tag 3 [module_body], SFBmodtype tag 4
     [module_type_body];
   - constant_body field 2: Undef is tag 0 [inline], an option, None being
     the integer 0;
   - module path: MPfile is tag 0 [dirpath], MPbound tag 1, MPdot tag 2
     [module path; label].

   Commands (each writes a new file; the input is left as it is):
     forge.ml param LIB.vo OUT.vo LABEL
       insert before the constant LABEL of the library a parameter with
       the same label and the same type;
     forge.ml rename LIB.vo OUT.vo FROM TO
       give the field FROM of the library the label TO. A module or a
       module type also gets the root of its delta resolver renamed, from
       the path that ends in FROM to the one that ends in TO;
     forge.ml client CLIENT.vo LIB.vo LIB_DIRPATH OUT.vo
       CLIENT.vo, recording LIB.vo's digest as the one of LIB_DIRPATH. *)

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

(* Whether [mp] is MPdot (_, [name]). *)
let mp_is_dot name mp = tag mp = 2 && String.equal (to_str (field mp 1)) name

(* {1 The library} *)

let root_module disk = field (field disk 0) 1

let set_root_module disk mb = Obj.set_field (field disk 0) 1 mb

let root_struc disk =
  let sign = field (root_module disk) 1 in
  expect "the library's signature (NoFunctor)" 0 sign;
  field sign 0

(* [disk] with [struc] as the structure of the root module's signature. *)
let set_root_struc disk struc =
  set_root_module disk (upd 1 (set 0 struc) (root_module disk))

let item_label item = to_str (field item 0)
let item_field item = field item 1

(* The constant_body of the field [name] of [struc]. *)
let struc_find struc name =
  match List.find_opt (fun it -> String.equal (item_label it) name) (list_of struc) with
  | Some it ->
    let sfb = item_field it in
    expect ("field " ^ name ^ " (a constant)") 0 sfb;
    field sfb 0
  | None -> fail "no field %s" name

(* {1 The forgeries} *)

let param label disk =
  let root = root_struc disk in
  let cb = struc_find root label in
  let undef = block 0 [| Obj.repr 0 |] in
  let item = block 0 [| Obj.repr label; block 0 [| set 2 undef cb |] |] in
  let rec insert l =
    if Obj.is_int l then fail "no field %s" label
    else if String.equal (item_label (field l 0)) label then block 0 [| item; l |]
    else block 0 [| field l 0; insert (field l 1) |]
  in
  set_root_struc disk (insert root);
  say "forging: a parameter %s, with the type of the constant %s, inserted before it" label label;
  disk

let rename from_label to_label disk =
  let root = root_struc disk in
  let rename_root mb =
    let reso = field mb 3 in
    let mp = field reso 0 in
    if not (mp_is_dot from_label mp) then
      fail "the root of %s's delta resolver is %s" from_label (mp_to_string mp);
    let mp' = block 2 [| field mp 0; Obj.repr to_label |] in
    say "forging: the root of %s's delta resolver becomes %s" from_label (mp_to_string mp');
    set 3 (set 0 mp' reso) mb
  in
  let found = ref false in
  let rename_item item =
    if not (String.equal (item_label item) from_label) then item
    else begin
      if !found then fail "two fields %s" from_label;
      found := true;
      let sfb = item_field item in
      let sfb = if tag sfb = 3 || tag sfb = 4 then upd 0 rename_root sfb else sfb in
      block 0 [| Obj.repr to_label; sfb |]
    end
  in
  let root = map_list rename_item root in
  if not !found then fail "no field %s" from_label;
  set_root_struc disk root;
  say "forging: the field %s gets the label %s" from_label to_label;
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
  | [ "param"; src; dst; label ] -> rewrite_vo ~src ~dst [ "library", param label ]
  | [ "rename"; src; dst; from_label; to_label ] ->
    rewrite_vo ~src ~dst [ "library", rename from_label to_label ]
  | [ "client"; src; lib; lib_dp; dst ] ->
    let digest = library_hash lib in
    rewrite_vo ~src ~dst
      [ ("summary", fun sd -> patch_deps ~what:"summary" ~lib_dp ~digest (field sd 1); sd);
        ("library", fun disk ->
            patch_deps ~what:"library" ~lib_dp ~digest (field (field disk 0) 4); disk) ]
  | _ ->
    prerr_endline
      "usage: ocaml forge.ml param LIB.vo OUT.vo LABEL\n\
      \       | rename LIB.vo OUT.vo FROM TO\n\
      \       | client CLIENT.vo LIB.vo LIB_DIRPATH OUT.vo";
    exit 2
