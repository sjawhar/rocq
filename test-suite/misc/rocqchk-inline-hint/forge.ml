(* Forge .vo files whose delta resolvers carry an inline hint with an open
   term, M.d -> Inline (0, Some (Rel 1)), and the clients that use them. A
   substitution through such a resolver puts the term in place of the
   constant, under binders and without lifting, so that the nearest binder
   captures its Rel 1:
   - sealed: in the implementation resolver of a sealed module, through which
     the sealing check substitutes the expected signature;
   - functor: in the resolver of a functor's argument, through which a
     functor application substitutes the functor's body.

   The helpers, and the value layouts they rely on, are those of
   misc/rocqchk_forge_lib.ml. This file adds checker/values.ml's layouts of
   a term Rel, tag 0 [int], and of the delta hint Inline, tag 0 [level;
   univ_abstracted constr option].

   Commands (each writes a new file; the inputs are left as they are):
     forge.ml sealed DONOR_LIB.vo HONEST_LIB.vo OUT.vo
     forge.ml functor HONEST_LIB.vo OUT.vo
     forge.ml client CLIENT.vo LIB.vo LIB_DIRPATH OUT.vo *)

#use "./misc/rocqchk_forge_lib.ml";;

(* The hint Inline (0, Some t) for [kn], with t the open term Rel 1 and an
   empty universe context: UVars.AbstractContext.empty is laid out as
   (([||], [||]), (ElimConstraints.empty, UnivConstraints.empty)), empty sets
   being the integer 0 (checker/values.ml, v_abs_context and v_cstrs). *)
let rel1 = block 0 [| Obj.repr 1 |]
let empty_abstract_context =
  block 0 [| block 0 [| Obj.repr [||]; Obj.repr [||] |]; block 0 [| Obj.repr 0; Obj.repr 0 |] |]
let open_term = block 0 [| rel1; empty_abstract_context |]

let add_open_inline reso kn =
  upd 2 (hmap_add kn (block 0 [| Obj.repr 0; block 0 [| open_term |] |])) reso

(* {1 The forgeries} *)

(* Case sealed. [disk] is honest/Lib.vo, where M : S with
   S = sig d : bool; lem : forall b, eq bool b b end, and M's implementation
   is d := true, lem := fun b => eq_refl bool b. [donor] is donor/Lib.vo,
   whose M has the signature lem : forall b, eq bool b d.
   - M's stored signature (module_body field 1): the field lem becomes
     donor/Lib.vo's, so that the expected lem reads forall b, eq bool b M.d;
   - M's implementation resolver (the Struct (reso, _) of field 0) gets
     M.d -> Inline (0, Some (Rel 1)).
   M's implementation and its signature resolver are left as they are. The
   name M.d is taken from donor/Lib.vo's lem type, hash included. *)
let forge_sealed ~donor disk =
  let root = root_struc disk in
  let dsig = nofunctor "donor's module M" (field (module_of (root_struc donor) "M") 1) in
  let dkn = find_kn dsig ~label:"d" ~in_mp:(mp_is_dot "M") in
  let dlem = struc_find dsig "lem" in
  expect "donor's M.lem (a constant)" 0 dlem;
  let mb = module_of root "M" in
  let i = impl_of mb in
  if not (is_block i && tag i = 1) then fail "M's implementation is not Struct";
  say "forge: M's signature field lem is donor/Lib.vo's";
  let mb = upd 1 (upd 0 (fun struc -> struc_update struc "lem" (fun _ -> dlem))) mb in
  say "forge: M's implementation resolver gets %s -> Inline (0, Some (Rel 1))" (kn_to_string dkn);
  let mb = upd 0 (upd 0 (upd 0 (fun reso -> add_open_inline reso dkn))) mb in
  set_root_struc disk (struc_update root "M" (set 0 mb));
  disk

(* Case functor. [disk] is honest/Lib.vo, where A := struct d := true end,
   use_d := A.d names A.d, and F (P : XS) proves
   lem : (forall b, eq bool b P.d) -> eq bool true false. A's delta resolver
   (module_body field 3, through which F A substitutes F's parameter) gets
   A.d -> Inline (0, Some (Rel 1)). Nothing else changes. *)
let forge_functor disk =
  let root = root_struc disk in
  let dkn = find_kn root ~label:"d" ~in_mp:(mp_is_dot "A") in
  let a = module_of root "A" in
  say "forge: A's delta resolver gets %s -> Inline (0, Some (Rel 1))" (kn_to_string dkn);
  let a = upd 3 (fun reso -> add_open_inline reso dkn) a in
  set_root_struc disk (struc_update root "A" (set 0 a));
  disk

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [ "sealed"; donor; src; dst ] ->
    rewrite_vo ~src ~dst [ "library", forge_sealed ~donor:(library_value donor) ]
  | [ "functor"; src; dst ] -> rewrite_vo ~src ~dst [ "library", forge_functor ]
  | [ "client"; src; lib; lib_dp; dst ] -> client ~src ~lib ~lib_dp ~dst
  | _ ->
    prerr_endline
      "usage: forge.ml sealed DONOR_LIB.vo LIB.vo OUT.vo | functor LIB.vo OUT.vo\n\
      \       | client CLIENT.vo LIB.vo LIB_DIRPATH OUT.vo";
    exit 2
