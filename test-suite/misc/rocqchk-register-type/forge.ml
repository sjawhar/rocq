(* Forge the .vo files of rocqchk_register_type.sh: give a parameter the
   body Int 0, the int63 literal 0, and register a constant as the int63
   primitive type, which coqc does only for a parameter that Primitive
   declares. The typing of Int 0 uses the registered constant, so with a
   definition int : Set := Empty_set registered, Int 0 has a type that
   unfolds to Empty_set. The helpers, and the value layouts they rely on,
   are those of misc/rocqchk_forge_lib.ml; this file also relies on these,
   from checker/values.ml:

   - compiled_library field 6: comp_retro, a list of retro_action;
   - retro_action: Register_ind (tag 0) [prim_ind; inductive] |
     Register_type (tag 1) [prim_type; constant], the enum prim_type
     having PT_int63 = 0;
   - constant_body field 2: Undef is tag 0 [inline], Def tag 1 [term];
   - term: Int is tag 17 [uint63], an immediate integer on a 64-bit
     platform.

   Commands (each writes a new file; the input is left as it is):
     forge.ml int0 LIB.vo OUT.vo LABEL
       the parameter LABEL of the library gets the body Int 0;
     forge.ml register LIB.vo OUT.vo NAME [CANONICAL]
       the library's retroknowledge gets the registration of the constant
       NAME as the int63 type, named with the canonical name CANONICAL if it
       is given. NAME and CANONICAL are full names, such as RegType.Lib.M.int,
       of constants that a declaration of the library names;
     forge.ml client CLIENT.vo LIB.vo LIB_DIRPATH OUT.vo *)

#use "./misc/rocqchk_forge_lib.ml";;

(* The constants that the declarations of a structure name, in its
   modules, their implementations, module types and functors too. A
   signature is NoFunctor (tag 0) [structure] | MoreFunctor (tag 1) [mbid;
   module type; signature]; a module, and a module type, has its signature
   in field 1. *)
let rec sign_constants acc sign =
  match tag sign with
  | 0 -> struc_constants acc (field sign 0)
  | 1 -> sign_constants (sign_constants acc (field (field sign 1) 1)) (field sign 2)
  | t -> fail "signature tag %d" t

and struc_constants acc struc =
  List.fold_left
    (fun acc it ->
      let sfb = item_field it in
      match tag sfb with
      | 0 -> List.rev_append (cb_constants (field sfb 0)) acc
      | 3 ->
        let mb = field sfb 0 in
        let acc = sign_constants acc (field mb 1) in
        let i = impl_of mb in
        if is_block i && tag i = 1 then struc_constants acc (field i 1) else acc
      | 4 -> sign_constants acc (field (field sfb 0) 1)
      | _ -> acc)
    acc (list_of struc)

(* The kernel name, hash included, of the constant named [name] in the
   library: it is taken from the file, never rebuilt. *)
let find_constant disk name =
  match
    List.find_opt
      (fun c -> String.equal (kn_to_string (cst_user c)) name)
      (struc_constants [] (root_struc disk))
  with
  | Some c -> cst_user c
  | None -> fail "no declaration of the library names a constant %s" name

let int0 label disk =
  if Sys.word_size <> 64 then fail "Int 0 is written as a 64-bit immediate integer";
  let root = root_struc disk in
  let cb = constant_of root label in
  expect ~size:1 (label ^ "'s body (Undef)") 0 (field cb 2);
  let int0 = block 17 [| Obj.repr 0 |] in
  set_root_struc disk (struc_update root label (upd 0 (set 2 (block 1 [| int0 |]))));
  say "forging: %s's body becomes Def (Int 0)" label;
  disk

let register name canonical disk =
  let compiled = field disk 0 in
  if size compiled <> 7 then fail "compiled_library has %d fields, not 7" (size compiled);
  let user = find_constant disk name in
  let cst, named =
    match canonical with
    | None -> block 0 [| user |], ""
    | Some c ->
      let can = find_constant disk c in
      dual user can, " with the canonical name " ^ kn_to_string can
  in
  let action = block 1 [| Obj.repr 0; cst |] in
  let retro = field compiled 6 in
  say "forging: the library's retroknowledge (%d action(s)) gets Register_type (prim_type 0, %s%s)"
    (List.length (list_of retro)) (kn_to_string user) named;
  Obj.set_field compiled 6 (block 0 [| action; retro |]);
  disk

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [ "int0"; src; dst; label ] -> rewrite_vo ~src ~dst [ "library", int0 label ]
  | [ "register"; src; dst; name ] -> rewrite_vo ~src ~dst [ "library", register name None ]
  | [ "register"; src; dst; name; canonical ] ->
    rewrite_vo ~src ~dst [ "library", register name (Some canonical) ]
  | [ "client"; src; lib; lib_dp; dst ] -> client ~src ~lib ~lib_dp ~dst
  | _ ->
    prerr_endline
      "usage: ocaml forge.ml int0 LIB.vo OUT.vo LABEL\n\
      \       | register LIB.vo OUT.vo NAME [CANONICAL]\n\
      \       | client CLIENT.vo LIB.vo LIB_DIRPATH OUT.vo";
    exit 2
