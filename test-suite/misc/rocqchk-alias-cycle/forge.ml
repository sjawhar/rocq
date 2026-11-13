(* Give Cycle.vo the alias cycles coqc refuses to write: the expression of
   each module below, an alias of Defines or of Outer in the honest file,
   becomes an alias of the path beside it.
     Self -> Self,  Ping -> Pong,  Pong -> Ping,  Up -> Down,  Down -> Up.C
   Like misc/rocqchk-primitive-type/forge.ml, this reads the .vo format of
   lib/objFile.ml without Rocq's OCaml libraries: it is an untrusted file
   producer, not another path through the kernel API. The positions of the
   fields it reads are those of checker/values.ml, and each block is checked
   to have the expected shape before it is used. *)

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

let block tag fields =
  let b = Obj.new_block tag (Array.length fields) in
  Array.iteri (Obj.set_field b) fields;
  b

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

(* The list cell of the structure whose item is the module [name]: a
   structure is a list of (label, structure_field_body), and [SFBmodule mb]
   has tag 3. *)
let module_cell structure name =
  let rec loop cell =
    if Obj.is_int cell then failwith ("no module " ^ name ^ " in the library")
    else
      let item = field cell 0 in
      if is_label name (field item 0) then begin
        expect (name ^ " (SFBmodule)") (field item 1) ~tag:3 ~size:1;
        cell
      end
      else loop (field cell 1)
  in
  loop structure

(* The MEident block of the module of [cell]: module_body field 0 is the
   implementation wrapper (tag 0) [implementation], the implementation is
   Algebraic (tag 0) [expression], the expression MENoFunctor (tag 0)
   [algebraic expression], and that MEident (tag 0) [module path]. *)
let alias_target what cell =
  let mb = field (field (field cell 0) 1) 0 in
  let wrapper = field mb 0 in
  expect (what ^ "'s implementation wrapper") wrapper ~tag:0 ~size:1;
  let impl = field wrapper 0 in
  expect (what ^ "'s implementation (Algebraic)") impl ~tag:0 ~size:1;
  let me = field impl 0 in
  expect (what ^ "'s expression (MENoFunctor)") me ~tag:0 ~size:1;
  let alg = field me 0 in
  expect (what ^ "'s expression (MEident)") alg ~tag:0 ~size:1;
  field alg 0

(* Rebuild the item of [cell] with the module's expression [MEident target],
   copying every block on the way, which may be shared with other items. *)
let set_alias_target cell target =
  let item = field cell 0 in
  let sfb = field item 1 in
  let mb = Obj.dup (field sfb 0) in
  Obj.set_field mb 0 (block 0 [| block 0 [| block 0 [| block 0 [| target |] |] |] |]);
  Obj.set_field cell 0 (block 0 [| field item 0; block 3 [| mb |] |])

(* ModPath: MPfile (tag 0) [dirpath], MPbound (tag 1), MPdot (tag 2)
   [module path; label]. *)
let dot mp label = block 2 [| mp; Obj.repr label |]

let forge data =
  let disk = Obj.repr (Marshal.from_string data 0) in
  let structure = structure_of_library disk in
  let defines = alias_target "Self" (module_cell structure "Self") in
  expect "Defines' path (MPdot)" defines ~tag:2 ~size:2;
  let file = field defines 0 in
  expect "the library's path (MPfile)" file ~tag:0 ~size:1;
  List.iter
    (fun (name, target) ->
      let cell = module_cell structure name in
      ignore (alias_target name cell);
      set_alias_target cell target;
      Printf.printf "forge: %s is now an alias\n" name)
    [ "Self", dot file "Self";
      "Ping", dot file "Pong";
      "Pong", dot file "Ping";
      "Up", dot file "Down";
      "Down", dot (dot file "Up") "C" ];
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
