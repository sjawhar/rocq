(* Give Bogus.vo the declarations coqc refuses to write:
     Primitive bogus : False := #int63_head0.
     Definition oops : False := bogus.
   by setting the type of the compiled constants bogus and oops to the term
   False, taken from the body of false_prop. The file is rewritten in place.
   The helpers, and the value layouts they rely on, are those of
   misc/rocqchk_forge_lib.ml. This file adds checker/values.ml's layouts of
   a constant_body's body Primitive, tag 3, and of a term Prod, tag 6
   [binder; domain; codomain]. Each block is checked to have the expected
   shape before it is used.

   Command:
     forge.ml BOGUS.vo *)

#use "./misc/rocqchk_forge_lib.ml";;

(* const_body is field 2 of a constant_body: Undef 0, Def 1, OpaqueDef 2,
   Primitive 3, Symbol 4; const_type is field 3. [struc] with the type of
   the constant [name], whose body has tag [body_tag] and whose type is a
   product, set to [false_term]. *)
let retype false_term struc name ~body_tag =
  let cb = constant_of struc name in
  expect ~size:1 (name ^ "'s body") body_tag (field cb 2);
  expect ~size:3 (name ^ "'s type (int -> int)") 6 (field cb 3);
  say "forge: %s now has the type False" name;
  struc_update struc name (upd 0 (set 3 false_term))

let forge disk =
  let struc = root_struc disk in
  let def = field (constant_of struc "false_prop") 2 in
  expect ~size:1 "false_prop's body (Def)" 1 def;
  let false_term = field def 0 in
  expect ~size:1 "false_prop's body (Ind False)" 11 false_term;
  let struc = retype false_term struc "bogus" ~body_tag:3 in
  let struc = retype false_term struc "oops" ~body_tag:1 in
  set_root_struc disk struc;
  disk

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [ file ] -> rewrite_vo ~src:file ~dst:file [ "library", forge ]
  | _ ->
    prerr_endline "usage: forge.ml BOGUS.vo";
    exit 2
