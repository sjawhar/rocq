(* Give Loop.vo the functor coqc refuses to write: in the body of F, the
   modules Grow and Same, applications of G in the honest file, become
   applications of F itself.
     Grow := F Loc,  Same := F X
   Like misc/rocqchk-alias-cycle/forge.ml, whose reading and writing of the
   .vo format of lib/objFile.ml this repeats, this uses no Rocq OCaml library:
   it is an untrusted file producer, not another path through the kernel API.
   The positions of the fields it reads are those of checker/values.ml, and
   each block is checked to have the expected shape before it is used. *)

type segment = {
  name : string;
  pos : int64;
  len : int64;
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
      let _hash = really_input_string ch 16 in
      { name; pos; len })

let field v i = Obj.field v i

let expect what v ~tag ~size =
  if Obj.is_int v || Obj.tag v <> tag || Obj.size v <> size then
    failwith ("unexpected shape of " ^ what)

(* The structure of the library: library = (compiled, _, _), compiled =
   (dirpath, module_body, ...), module_body = (mod_expr, mod_type, ...) and
   the mod_type of a library is [NoFunctor structure]. *)
let structure_of_library disk =
  let signature = field (field (field disk 0) 1) 1 in
  expect "the library's signature (NoFunctor)" signature ~tag:0 ~size:1;
  field signature 0

let is_label name label =
  not (Obj.is_int label) && Obj.tag label = Obj.string_tag
  && String.equal (Obj.obj label) name

(* The module_body of the field [name] of a structure: a structure is a list
   of (label, structure_field_body), and [SFBmodule mb] has tag 3. *)
let module_body structure name =
  let rec loop cell =
    if Obj.is_int cell then failwith ("no module " ^ name)
    else
      let item = field cell 0 in
      if is_label name (field item 0) then begin
        let sfb = field item 1 in
        expect (name ^ " (SFBmodule)") sfb ~tag:3 ~size:1;
        field sfb 0
      end
      else loop (field cell 1)
  in
  loop structure

(* The body of the functor F, which the honest file declares without an
   ascription: its implementation is FullStruct (the immediate 1), and its
   signature, module_body field 1, is MoreFunctor (tag 1) [mbid; parameter
   type; NoFunctor (tag 0) [structure]]. *)
let functor_body mb =
  let wrapper = field mb 0 in
  expect "F's implementation wrapper" wrapper ~tag:0 ~size:1;
  let impl = field wrapper 0 in
  if not (Obj.is_int impl) || (Obj.obj impl : int) <> 1 then
    failwith "F's implementation is not FullStruct";
  let sign = field mb 1 in
  expect "F's signature (MoreFunctor)" sign ~tag:1 ~size:3;
  let body = field sign 2 in
  expect "F's body (NoFunctor)" body ~tag:0 ~size:1;
  field body 0

(* The MEident block at the head of the application that is the expression of
   [mb]: the implementation wrapper (tag 0) [implementation], Algebraic (tag 0)
   [expression], MENoFunctor (tag 0) [algebraic expression], MEapply (tag 1)
   [head; argument], and the head MEident (tag 0) [module path]. *)
let application_head what mb =
  let wrapper = field mb 0 in
  expect (what ^ "'s implementation wrapper") wrapper ~tag:0 ~size:1;
  let impl = field wrapper 0 in
  expect (what ^ "'s implementation (Algebraic)") impl ~tag:0 ~size:1;
  let me = field impl 0 in
  expect (what ^ "'s expression (MENoFunctor)") me ~tag:0 ~size:1;
  let app = field me 0 in
  expect (what ^ "'s expression (MEapply)") app ~tag:1 ~size:2;
  let head = field app 0 in
  expect (what ^ "'s head (MEident)") head ~tag:0 ~size:1;
  head

let forge data =
  let disk = Obj.repr (Marshal.from_string data 0) in
  let structure = structure_of_library disk in
  let body = functor_body (module_body structure "F") in
  let g = field (application_head "Grow" (module_body body "Grow")) 0 in
  (* ModPath: MPfile (tag 0) [dirpath], MPbound (tag 1), MPdot (tag 2)
     [module path; label]. *)
  expect "G's path (MPdot)" g ~tag:2 ~size:2;
  if not (is_label "G" (field g 1)) then failwith "Grow does not apply G";
  let f = Obj.dup g in
  Obj.set_field f 1 (Obj.repr "F");
  List.iter
    (fun name ->
      let head = application_head name (module_body body name) in
      Obj.set_field head 0 f;
      Printf.printf "forge: %s now applies F\n" name)
    [ "Grow"; "Same" ];
  Marshal.to_string (Obj.obj disk) []

let () =
  let file = Sys.argv.(1) in
  let input = open_in_bin file in
  let header = really_input_string input 8 in
  let segments = read_segments input in
  let found = ref false in
  let contents =
    Array.map
      (fun segment ->
        LargeFile.seek_in input segment.pos;
        let data = really_input_string input (Int64.to_int segment.len) in
        let data =
          if String.equal segment.name "library" then begin
            found := true;
            forge data
          end
          else data
        in
        segment.name, data)
      segments
  in
  close_in input;
  if not !found then failwith ("no library segment in " ^ file);
  let temporary = file ^ ".forged" in
  let output = open_out_bin temporary in
  output_string output header;
  output_int64 output 0L;
  let rewritten =
    Array.map
      (fun (name, data) ->
        let pos = LargeFile.pos_out output in
        output_string output data;
        output_string output (Digest.string data);
        name, pos, Int64.of_int (String.length data), Digest.string data)
      contents
  in
  let summary_pos = LargeFile.pos_out output in
  output_binary_int output (Array.length rewritten);
  Array.iter
    (fun (name, pos, len, hash) ->
      output_binary_int output (String.length name);
      output_string output name;
      output_int64 output pos;
      output_int64 output len;
      output_string output hash)
    rewritten;
  LargeFile.seek_out output 8L;
  output_int64 output summary_pos;
  close_out output;
  Sys.rename temporary file
