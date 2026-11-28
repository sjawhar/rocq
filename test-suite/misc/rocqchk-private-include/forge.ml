(* The forger of misc/rocqchk_private_include.sh.

   usage: ocaml misc/rocqchk-private-include/forge.ml <src.vo> <dst.vo> <label>
            [<edit> <module> <constant> [<argument>]]

   It reads <src.vo>, makes every inductive block with the label <label>
   private and open to matching (mind_private: None becomes Some false) in
   every structure of the library, module types and functor parameters
   included (with <label> written <module>.<label>, only in the structures
   of the module <module>), and writes <dst.vo> with fresh segment
   checksums. Applied to a library in which a module N includes a module M
   and matches on its copy of M's inductive, this gives the .vo that a
   compiler without the fix of rocq-prover/rocq#21113 writes when M's
   inductive is private.

   The optional edit changes the constant <constant> of each structure of
   the module <module>, so that an Include copy is no longer the same
   declaration as the constant it copies, or no longer has that constant:
   - swap: swap the bodies of the first two branches of the match under the
     lambdas of its body;
   - rename <name>: give it the label <name>;
   - noguard: record it as checked without the guard condition;
   - irrelevant: record it as irrelevant;
   - univs <module'> <other>, type <module'> <other>, body <module'>
     <other>: give it the universes, the type or the body of the constant
     <other> of the module <module'>, as the source file has it (the
     library's own constants are in the module named "");
   - annot: mark the binder of the first lambda of its body irrelevant;
   - kerpair <module'> <other>: give the first constant that its body names
     the user name of the first constant that the body of <module'>.<other>
     names, and keep its canonical name.
   Every other byte of every segment stays as it is.

   It uses only the OCaml standard library: a forger is an untrusted file
   producer, not another path through the kernel API. The value layouts it
   relies on are checker/values.ml's:

   - a .vo: an 8-byte header, the position of the segment table (8 bytes,
     big-endian), each segment followed by its MD5, then the table: a count,
     then for each segment its name, position, length and MD5;
   - library segment: (compiled_library, _, _), compiled_library's field 1
     the root module_body;
   - module_body: field 0 the implementation wrapper (tag 0) [implementation],
     an implementation being Abstract (0) | FullStruct (1) | Algebraic (tag 0)
     | Struct (tag 1) [resolver; structure]; field 1 the signature, NoFunctor
     (tag 0) [structure] | MoreFunctor (tag 1) [mbid; module_type_body;
     signature];
   - structure: a list of (label, field); field tags 0 constant, 1 inductive
     [mutual_inductive_body], 2 rules, 3 module [module_body], 4 module type;
   - mutual_inductive_body: 13 fields, field 11 mind_private (bool option);
   - module_type_body: field 1 its signature;
   - constant_body: 9 fields, 2 the body, Def (tag 1) [term] | OpaqueDef
     (tag 2) [Indirect (tag 0) [substitutions; cookings; library; index]],
     4 the relevance (Relevant 0, Irrelevant 1), 6 the universes, 8 the
     typing flags, whose field 0 is check_guarded;
   - term: Const (tag 10) [(constant, instance)], a constant being Same
     (tag 0) [kn] or Dual (tag 1) [user kn; canonical kn]; Lambda (tag 7)
     [binder annotation (name, relevance); type; body]; App (tag 9) [head;
     arguments]; Case (tag 13) with field 6 its branches, an array of
     (names, body). *)

let fail fmt = Printf.ksprintf failwith fmt

let input_int64 ch =
  let rec go i accu =
    if i = 0 then accu
    else go (i - 1) (Int64.logor (Int64.shift_left accu 8) (Int64.of_int (input_byte ch)))
  in
  go 8 0L

let output_int64 ch n =
  for shift = 7 downto 0 do
    output_byte ch (Int64.to_int (Int64.logand 255L (Int64.shift_right_logical n (8 * shift))))
  done

let read_vo file =
  let ch = open_in_bin file in
  let header = really_input_string ch 8 in
  let table = input_int64 ch in
  LargeFile.seek_in ch table;
  let n = input_binary_int ch in
  let entries =
    List.init n (fun _ ->
        let name = really_input_string ch (input_binary_int ch) in
        let pos = input_int64 ch in
        let len = input_int64 ch in
        let _hash = really_input_string ch 16 in
        name, pos, len)
  in
  let segments =
    List.map
      (fun (name, pos, len) ->
        LargeFile.seek_in ch pos;
        name, really_input_string ch (Int64.to_int len))
      entries
  in
  close_in ch;
  header, segments

let write_vo file header segments =
  let ch = open_out_bin file in
  output_string ch header;
  output_int64 ch 0L;
  let table =
    List.map
      (fun (name, data) ->
        let pos = LargeFile.pos_out ch in
        let hash = Digest.string data in
        output_string ch data;
        output_string ch hash;
        name, pos, String.length data, hash)
      segments
  in
  let table_pos = LargeFile.pos_out ch in
  output_binary_int ch (List.length table);
  List.iter
    (fun (name, pos, len, hash) ->
      output_binary_int ch (String.length name);
      output_string ch name;
      output_int64 ch pos;
      output_int64 ch (Int64.of_int len);
      output_string ch hash)
    table;
  LargeFile.seek_out ch 8L;
  output_int64 ch table_pos;
  close_out ch

let field = Obj.field
let is_block o = not (Obj.is_int o)

(* [o] with field [i] replaced by [f] of it, copied only when the field
   changes, so that a value shared with another part of the file is never
   changed in place. *)
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

let block tag fields =
  let b = Obj.new_block tag (Array.length fields) in
  Array.iteri (Obj.set_field b) fields;
  b

let rec list_of l = if Obj.is_int l then [] else field l 0 :: list_of (field l 1)

let rec map_list f l =
  if Obj.is_int l then l
  else
    let hd = field l 0 and tl = field l 1 in
    let hd' = f hd and tl' = map_list f tl in
    if hd' == hd && tl' == tl then l else block 0 [| hd'; tl' |]

let label_of item : string = Obj.obj (field item 0)

let opened = ref 0
let edited = ref 0

(* The term [c] with the bodies of the first two branches of the match under
   its lambdas swapped. *)
let rec swap_branches c =
  if Obj.is_int c then fail "no match in the body"
  else match Obj.tag c with
    | 7 -> upd 2 swap_branches c
    | 13 ->
      upd 6
        (fun brs ->
          if Obj.size brs < 2 then fail "a match with fewer than two branches";
          let b0 = field brs 0 and b1 = field brs 1 in
          block 0 (Array.init (Obj.size brs) (fun i ->
              if i = 0 then set 1 (field b1 1) b0
              else if i = 1 then set 1 (field b0 1) b1
              else field brs i)))
        c
    | t -> fail "a term with tag %d before the match" t

type action =
  | Swap
  | Rename of string
  | Noguard
  | Irrelevant
  | Univs of string * string
  | Type of string * string
  | Body of string * string
  | Annot
  | Kerpair of string * string

type edit = {
  modname : string;
  constant : string;
  action : action;
}

let parse_edit = function
  | [] -> None
  | kind :: modname :: constant :: args ->
    let action = match kind, args with
      | "swap", [] -> Swap
      | "rename", [ name ] -> Rename name
      | "noguard", [] -> Noguard
      | "irrelevant", [] -> Irrelevant
      | "univs", [ m; c ] -> Univs (m, c)
      | "type", [ m; c ] -> Type (m, c)
      | "body", [ m; c ] -> Body (m, c)
      | "annot", [] -> Annot
      | "kerpair", [ m; c ] -> Kerpair (m, c)
      | _ -> fail "unknown edit %s" (String.concat " " (kind :: args))
    in
    Some { modname; constant; action }
  | _ -> fail "an edit needs a module and a constant"

let edit : edit option ref = ref None

(* With a label <module>.<label>, only the inductives of the structures of
   the module <module> are made private. *)
let only_in : string option ref = ref None

(* Each constant_body of each module of the library, by the labels of the
   module and of the constant, as the source file has them. *)
let constants : (string * string, Obj.t) Hashtbl.t = Hashtbl.create 17

let constant m c =
  match Hashtbl.find_opt constants (m, c) with
  | Some cb -> cb
  | None -> fail "no constant %s.%s" m c

let rec collect_struc modname struc =
  List.iter
    (fun item ->
      let sfb = field item 1 in
      match Obj.tag sfb with
      | 0 -> Hashtbl.replace constants (modname, label_of item) (field sfb 0)
      | 3 -> collect_module (label_of item) (field sfb 0)
      | _ -> ())
    (list_of struc)

and collect_sign modname sign =
  if Obj.tag sign = 0 then collect_struc modname (field sign 0)

and collect_module modname mb = collect_sign modname (field mb 1)

(* The first Const node of the term [c]: the node itself, or the first Const
   node of the body of a lambda or of the head of an application. *)
let rec first_const c =
  if Obj.is_int c then None
  else match Obj.tag c with
    | 10 -> Some c
    | 7 -> first_const (field c 2)
    | 9 -> first_const (field c 0)
    | _ -> None

let user_of cst = field cst 0
let canonical_of cst = if Obj.tag cst = 1 then field cst 1 else field cst 0

(* The term [c] with its first Const node given the constant [cst]. *)
let rec set_first_const cst c =
  if Obj.is_int c then fail "no constant in the body"
  else match Obj.tag c with
    | 10 -> upd 0 (set 0 cst) c
    | 7 -> upd 2 (set_first_const cst) c
    | 9 -> upd 0 (set_first_const cst) c
    | t -> fail "a term with tag %d before the constant" t

let transparent_body cb =
  let body = field cb 2 in
  if is_block body && Obj.tag body = 1 then field body 0
  else fail "no transparent body"

(* The structure item [item], a constant, with the edit [action] applied. *)
let edit_item action item =
  incr edited;
  let cb f = upd 1 (upd 0 f) item in
  match action with
  | Rename name -> set 0 (Obj.repr name) item
  | Swap ->
    cb (upd 2 (fun body ->
        if is_block body && Obj.tag body = 1 then upd 0 swap_branches body
        else fail "no transparent body to swap"))
  | Noguard -> cb (upd 8 (set 0 (Obj.repr false)))
  | Irrelevant -> cb (set 4 (Obj.repr 1))
  | Univs (m, c) -> cb (set 6 (field (constant m c) 6))
  | Type (m, c) -> cb (set 3 (field (constant m c) 3))
  | Body (m, c) -> cb (set 2 (field (constant m c) 2))
  | Annot ->
    let annot c =
      if is_block c && Obj.tag c = 7 then upd 0 (set 1 (Obj.repr 1)) c
      else fail "the body is not a lambda"
    in
    cb (upd 2 (upd 0 annot))
  | Kerpair (m, c) ->
    let donor = match first_const (transparent_body (constant m c)) with
      | Some node -> field (field node 0) 0
      | None -> fail "%s.%s names no constant" m c
    in
    cb (upd 2 (upd 0 (fun body ->
        let mine = match first_const body with
          | Some node -> field (field node 0) 0
          | None -> fail "the body names no constant"
        in
        set_first_const (block 1 [| user_of donor; canonical_of mine |]) body)))

let edit_struc e struc =
  map_list
    (fun item ->
      if String.equal (label_of item) e.constant && Obj.tag (field item 1) = 0
      then edit_item e.action item
      else item)
    struc

let rec map_struc ~here ~m label struc =
  let struc =
    map_list
      (fun item ->
        let name = label_of item in
        upd 1
          (fun sfb ->
            match Obj.tag sfb with
            | 1 when String.equal name label
                     && (match !only_in with None -> true | Some q -> String.equal q m) ->
              upd 0
                (fun mib ->
                  if Obj.size mib <> 13 then fail "inductive %s: %d fields, not 13" name (Obj.size mib);
                  if Obj.is_int (field mib 11) && (Obj.obj (field mib 11) : int) = 0 then begin
                    incr opened;
                    set 11 (block 0 [| Obj.repr false |]) mib
                  end
                  else fail "inductive %s is private already" name)
                sfb
            | 3 ->
              let here = match !edit with Some e -> String.equal e.modname name | None -> false in
              upd 0 (map_module ~here ~m:name label) sfb
            | 4 -> upd 0 (upd 1 (map_sign ~here:false ~m:name label)) sfb
            | _ -> sfb)
          item)
      struc
  in
  match !edit with Some e when here -> edit_struc e struc | Some _ | None -> struc

and map_sign ~here ~m label sign =
  match Obj.tag sign with
  | 0 -> upd 0 (map_struc ~here ~m label) sign
  | 1 -> sign |> upd 1 (upd 1 (map_sign ~here:false ~m label)) |> upd 2 (map_sign ~here ~m label)
  | t -> fail "signature with tag %d" t

and map_module ~here ~m label mb =
  mb
  |> upd 0 (upd 0 (fun impl ->
      if is_block impl && Obj.tag impl = 1 then upd 1 (map_struc ~here ~m label) impl else impl))
  |> upd 1 (map_sign ~here ~m label)

let () =
  let args = Array.to_list Sys.argv in
  match args with
  | _ :: src :: dst :: label :: rest ->
    edit := parse_edit rest;
    let label = match String.index_opt label '.' with
      | Some i ->
        only_in := Some (String.sub label 0 i);
        String.sub label (i + 1) (String.length label - i - 1)
      | None -> label
    in
    let header, segments = read_vo src in
    let segments =
      List.map
        (fun (name, data) ->
          if String.equal name "library" then begin
            let v = Obj.repr (Marshal.from_string data 0) in
            collect_module "" (field (field v 0) 1);
            let v = upd 0 (upd 1 (map_module ~here:false ~m:"" label)) v in
            name, Marshal.to_string (Obj.obj v) []
          end
          else name, data)
        segments
    in
    if !opened = 0 then fail "no inductive %s in %s" label src;
    if !edit <> None && !edited = 0 then fail "the edit changed nothing in %s" src;
    write_vo dst header segments;
    Printf.printf "forge: %s: %d copies of inductive %s made private and open, %d constants edited\n"
      dst !opened label !edited
  | _ ->
    prerr_endline "usage: forge.ml <src.vo> <dst.vo> <label> [<edit> <module> <constant> [<argument>]]";
    exit 2
