(* Forge the .vo files of rocqchk_register_type.sh: give a parameter the
   body Int 0, the int63 literal 0, and register a constant as the int63
   primitive type, which coqc does only for a parameter that Primitive
   declares. The typing of Int 0 uses the registered constant, so with a
   definition int : Set := Empty_set registered, Int 0 has a type that
   unfolds to Empty_set. Also print, rewrite and repeat a stored
   registration of a primitive inductive type, for
   rocqchk_register_ind_canonical.sh. The helpers, and the value layouts
   they rely on, are those of misc/rocqchk_forge_lib.ml; this file also
   relies on these, from checker/values.ml:

   - compiled_library field 6: comp_retro, a list of retro_action, newest
     first (Safe_typing.add_retroknowledge prepends);
   - retro_action: Register_ind (tag 0) [prim_ind; inductive] |
     Register_type (tag 1) [prim_type; constant];
   - inductive: the tuple [mutual inductive; index];
   - prim_ind: an enum of immediate integers, PIT_bool = 0, PIT_carry 1,
     PIT_pair 2, PIT_cmp 3, PIT_f_cmp 4, PIT_f_class 5
     (kernel/cPrimitives.mli, checker/values.ml v_prim_ind); prim_type: an
     enum, PT_int63 = 0, PT_float64 1, PT_string 2, PT_array 3;
   - mutual inductive, and constant: Same (tag 0) [kn] | Dual (tag 1)
     [user kn; canonical kn];
   - constant_body field 2: Undef is tag 0 [inline], Def tag 1 [term];
   - term: Int is tag 17 [uint63], an immediate integer on a 64-bit
     platform.

   retro, ind-canonical and ind-repeat read a constant_body only at its
   fields 2 and 3 (map_cb, cb_inductives), and compiled_library only at
   fields 1 and 6, so that they also read upstream's layout, whose
   constant_body has 10 fields.

   Commands (each writes a new file; the input is left as it is):
     forge.ml int0 LIB.vo OUT.vo LABEL
       the parameter LABEL of the library gets the body Int 0;
     forge.ml register LIB.vo OUT.vo NAME [CANONICAL]
       the library's retroknowledge gets the registration of the constant
       NAME as the int63 type, named with the canonical name CANONICAL if it
       is given. NAME and CANONICAL are full names, such as RegType.Lib.M.int,
       of constants that a declaration of the library names;
     forge.ml client CLIENT.vo LIB.vo LIB_DIRPATH OUT.vo
     forge.ml retro LIB.vo
       print each stored action of the library, in stored order, on one
       line, then "actions: <n>", and nothing else on the standard output:
         Register_ind <k>/<n>: user=<kn> canonical=<kn> index=<i> prim=<prim_ind>
         Register_type <k>/<n>: constant=<kn> prim=<prim_type>
       A Same name prints the same name in both halves of an inductive; the
       constant of a Register_type prints its user half, and its canonical
       half after it, as canonical=<kn>, only when it is a Dual name;
     forge.ml ind-canonical LIB.vo OUT.vo USER CANONICAL
       the one stored Register_ind whose mutual inductive has the user half
       USER gets the mutual inductive Dual (that user half, CANONICAL), in a
       fresh action, also when CANONICAL is USER; every other action stays
       as it is;
     forge.ml ind-repeat LIB.vo OUT.vo USER CANONICAL first|last
       a fresh copy of that one action, with the mutual inductive Dual (its
       user half, CANONICAL) and the same index and primitive, goes just
       before it (first) or just after it (last) in the stored list.
     USER and CANONICAL are full names, such as RegInd.Lib.B. CANONICAL is
     the canonical half of an inductive that a constant of the library
     names, in its type or its body; its kernel name, hash included, is
     taken from there. ind-canonical and ind-repeat write nothing and exit
     1 when no stored Register_ind, or more than one, has the user half
     USER, or when no constant of the library names an inductive with the
     canonical half CANONICAL.

   misc/rocqchk_repeated_label.sh runs int0 and register too, and
   misc/rocqchk_register_ind_canonical.sh runs retro, ind-canonical,
   ind-repeat and client. *)

#use "./misc/rocqchk_forge_lib.ml";;

(* The constants that the declarations of a structure name, in its
   modules, their implementations, module types and functors too; with
   [~names:cb_inductives], the mutual inductives that they name. A
   signature is NoFunctor (tag 0) [structure] | MoreFunctor (tag 1) [mbid;
   module type; signature]; a module, and a module type, has its signature
   in field 1. *)
let rec sign_constants ?(names = cb_constants) acc sign =
  match tag sign with
  | 0 -> struc_constants ~names acc (field sign 0)
  | 1 ->
    sign_constants ~names (sign_constants ~names acc (field (field sign 1) 1)) (field sign 2)
  | t -> fail "signature tag %d" t

and struc_constants ?(names = cb_constants) acc struc =
  List.fold_left
    (fun acc it ->
      let sfb = item_field it in
      match tag sfb with
      | 0 -> List.rev_append (names (field sfb 0)) acc
      | 3 ->
        let mb = field sfb 0 in
        let acc = sign_constants ~names acc (field mb 1) in
        let i = impl_of mb in
        if is_block i && tag i = 1 then struc_constants ~names acc (field i 1) else acc
      | 4 -> sign_constants ~names acc (field (field sfb 0) 1)
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

(* {1 Registrations of primitive inductive types} *)

(* forge.ml ind-canonical and ind-repeat refuse their arguments this way:
   a message on the standard error, exit status 1, and no file written. *)
let refuse fmt = Printf.ksprintf (fun s -> prerr_endline ("forge.ml: " ^ s); exit 1) fmt

let prim_ind_names = [| "bool"; "carry"; "pair"; "cmp"; "f_cmp"; "f_class" |]
let prim_type_names = [| "int63_type"; "float64_type"; "string_type"; "array_type" |]

let enum_name what names o =
  if is_block o then fail "%s: expected an immediate integer, found a block" what;
  let n = to_int o in
  if n < 0 || n >= Array.length names then fail "%s: no value %d" what n;
  names.(n)

(* The (user, canonical) halves of a constant or a mutual inductive: a Same
   name gives its one name for both. *)
let halves what m =
  if Obj.is_int m then fail "%s: expected Same or Dual, found the integer %d" what (to_int m);
  match tag m, size m with
  | 0, 1 -> field m 0, field m 0
  | 1, 2 -> field m 0, field m 1
  | t, s -> fail "%s: expected Same (tag 0, 1 field) or Dual (tag 1, 2 fields), found tag %d with %d fields" what t s

(* The stored action list of the library. *)
let retro_of disk =
  let compiled = field disk 0 in
  if size compiled <> 7 then fail "compiled_library has %d fields, not 7" (size compiled);
  field compiled 6

(* [disk] with the action list [retro]; the compiled library is copied, not
   changed in place. *)
let with_retro retro disk = upd 0 (set 6 retro) disk

(* The inductive (mutual inductive, index) of the Register_ind action [a],
   after a check of both layouts. *)
let ind_of_action what a =
  expect ~size:2 what 0 a;
  let ind = field a 1 in
  expect ~size:2 (what ^ "'s inductive") 0 ind;
  if is_block (field ind 1) then fail "%s: the index is not an immediate integer" what;
  ind

let retro file =
  let actions = list_of (retro_of (library_value file)) in
  let n = List.length actions in
  List.iteri
    (fun k a ->
      let what = Printf.sprintf "action %d/%d" (k + 1) n in
      if Obj.is_int a then fail "%s: expected a block, found the integer %d" what (to_int a);
      match tag a with
      | 0 ->
        let ind = ind_of_action what a in
        let user, canonical = halves (what ^ "'s mutual inductive") (field ind 0) in
        say "Register_ind %d/%d: user=%s canonical=%s index=%d prim=%s" (k + 1) n
          (kn_to_string user) (kn_to_string canonical) (to_int (field ind 1))
          (enum_name (what ^ "'s prim_ind") prim_ind_names (field a 0))
      | 1 ->
        expect ~size:2 what 1 a;
        let cst = field a 1 in
        let user, canonical = halves (what ^ "'s constant") cst in
        say "Register_type %d/%d: constant=%s%s prim=%s" (k + 1) n (kn_to_string user)
          (if tag cst = 1 then " canonical=" ^ kn_to_string canonical else "")
          (enum_name (what ^ "'s prim_type") prim_type_names (field a 0))
      | t -> fail "%s: retro_action tag %d" what t)
    actions;
  say "actions: %d" n

(* The one stored Register_ind action whose mutual inductive has the user
   half [user]. *)
let find_ind_action retro user =
  let named a =
    is_block a && tag a = 0
    && (let ind = ind_of_action "a Register_ind action" a in
        let u, _ = halves "a Register_ind action's mutual inductive" (field ind 0) in
        String.equal (kn_to_string u) user)
  in
  match List.filter named (list_of retro) with
  | [ a ] -> a
  | [] -> refuse "no stored Register_ind action has the user name %s" user
  | l -> refuse "%d stored Register_ind actions have the user name %s, not one" (List.length l) user

(* The kernel name, hash included, of the canonical half [name] of a mutual
   inductive that a constant of the library names: it is taken from the
   file, never rebuilt. *)
let find_canonical disk name =
  let canonical m = snd (halves "an inductive a constant names" m) in
  match
    List.find_opt
      (fun m -> String.equal (kn_to_string (canonical m)) name)
      (struc_constants ~names:cb_inductives [] (root_struc disk))
  with
  | Some m -> canonical m
  | None -> refuse "no constant of the library names an inductive with the canonical name %s" name

(* A fresh Register_ind action: [a]'s primitive and index, and the mutual
   inductive Dual ([a]'s user half, [can]), in fresh blocks. *)
let with_canonical a can =
  let ind = field a 1 in
  let user, _ = halves "the Register_ind action's mutual inductive" (field ind 0) in
  block 0 [| field a 0; block 0 [| dual user can; field ind 1 |] |]

let ind_canonical user canonical disk =
  let retro = retro_of disk in
  let a = find_ind_action retro user in
  let can = find_canonical disk canonical in
  let fresh = with_canonical a can in
  say "forging: the Register_ind of %s gets the mutual inductive Dual (%s, %s)" user user
    (kn_to_string can);
  with_retro (map_list (fun b -> if b == a then fresh else b) retro) disk

(* [l] with [fresh] just before the cell that holds [a] ([first]), or just
   after it; only the cells up to that one are copied. *)
let rec insert_next_to a fresh ~first l =
  if Obj.is_int l then fail "the Register_ind action is not in the action list"
  else if field l 0 == a then
    if first then block 0 [| fresh; l |] else upd 1 (fun tl -> block 0 [| fresh; tl |]) l
  else upd 1 (insert_next_to a fresh ~first) l

let ind_repeat user canonical ~first disk =
  let retro = retro_of disk in
  let a = find_ind_action retro user in
  let can = find_canonical disk canonical in
  let fresh = with_canonical a can in
  say "forging: a copy of the Register_ind of %s, with the mutual inductive Dual (%s, %s), goes %s it"
    user user (kn_to_string can) (if first then "just before" else "just after");
  with_retro (insert_next_to a fresh ~first retro) disk

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [ "int0"; src; dst; label ] -> rewrite_vo ~src ~dst [ "library", int0 label ]
  | [ "register"; src; dst; name ] -> rewrite_vo ~src ~dst [ "library", register name None ]
  | [ "register"; src; dst; name; canonical ] ->
    rewrite_vo ~src ~dst [ "library", register name (Some canonical) ]
  | [ "client"; src; lib; lib_dp; dst ] -> client ~src ~lib ~lib_dp ~dst
  | [ "retro"; src ] -> retro src
  | [ "ind-canonical"; src; dst; user; canonical ] ->
    rewrite_vo ~src ~dst [ "library", ind_canonical user canonical ]
  | [ "ind-repeat"; src; dst; user; canonical; ("first" | "last" as where) ] ->
    rewrite_vo ~src ~dst [ "library", ind_repeat user canonical ~first:(where = "first") ]
  | _ ->
    prerr_endline
      "usage: ocaml forge.ml int0 LIB.vo OUT.vo LABEL\n\
      \       | register LIB.vo OUT.vo NAME [CANONICAL]\n\
      \       | client CLIENT.vo LIB.vo LIB_DIRPATH OUT.vo\n\
      \       | retro LIB.vo\n\
      \       | ind-canonical LIB.vo OUT.vo USER CANONICAL\n\
      \       | ind-repeat LIB.vo OUT.vo USER CANONICAL first|last";
    exit 2
