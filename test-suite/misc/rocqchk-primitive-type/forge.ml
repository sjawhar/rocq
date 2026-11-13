(* Give Bogus.vo the declarations coqc refuses to write:
     Primitive bogus : False := #int63_head0.     (mode primitive and both)
     Definition oops : False := bogus.            (mode both)
   by setting the type of the compiled constants bogus, and oops, to the term
   False, taken from the body of false_prop. Like
   misc/norec-validation-order/corrupt.ml, this reads the .vo format of
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

(* The structure of the library: library = (compiled, _, _), compiled =
   (dirpath, module_body, ...), module_body = (mod_expr, mod_type, ...) and
   the mod_type of a library is [NoFunctor structure]. *)
let structure_of_library disk =
  let signature = field (field (field disk 0) 1) 1 in
  expect "the library's signature (NoFunctor)" signature ~tag:0 ~size:1;
  field signature 0

(* The constant_body of the field [name]: a structure is a list of
   (label, structure_field_body), and [SFBconst cb] has tag 0. A
   constant_body has 9 fields; const_body is field 2 and const_type field
   3. *)
let constant structure name =
  let rec loop cell =
    if Obj.is_int cell then failwith ("no field " ^ name ^ " in the library")
    else
      let item = field cell 0 in
      let label = field item 0 in
      if not (Obj.is_int label) && Obj.tag label = Obj.string_tag
         && String.equal (Obj.obj label) name
      then begin
        let body = field item 1 in
        expect (name ^ " (SFBconst)") body ~tag:0 ~size:1;
        let cb = field body 0 in
        expect (name ^ "'s constant_body") cb ~tag:0 ~size:9;
        cb
      end
      else loop (field cell 1)
  in
  loop structure

(* const_body: Undef 0, Def 1, OpaqueDef 2, Primitive 3, Symbol 4.
   Constr.t: Prod 6, Const 10, Ind 11. *)
let const_body cb = field cb 2
let const_type cb = field cb 3
let set_const_type cb t = Obj.set_field cb 3 t

let forge mode data =
  let disk = Obj.repr (Marshal.from_string data 0) in
  let structure = structure_of_library disk in
  let false_prop = constant structure "false_prop" in
  let def = const_body false_prop in
  expect "false_prop's body (Def)" def ~tag:1 ~size:1;
  let false_term = field def 0 in
  expect "false_prop's body (Ind False)" false_term ~tag:11 ~size:1;
  let retype name ~body_tag =
    let cb = constant structure name in
    expect (name ^ "'s body") (const_body cb) ~tag:body_tag ~size:1;
    expect (name ^ "'s type (int -> int)") (const_type cb) ~tag:6 ~size:3;
    set_const_type cb false_term;
    Printf.printf "forge: %s now has the type False\n" name
  in
  retype "bogus" ~body_tag:3;
  (match mode with
   | "primitive" -> ()
   | "both" -> retype "oops" ~body_tag:1
   | _ -> failwith "expected the mode primitive or both");
  Marshal.to_string (Obj.obj disk) []

let () =
  let file = Sys.argv.(1) in
  let mode = Sys.argv.(2) in
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
            forge mode data
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
