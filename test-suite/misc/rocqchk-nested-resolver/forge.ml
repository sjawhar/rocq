(* Forge a .vo file whose module A's delta resolver records an alias of a
   declaration of its submodule X that the resolver of X does not, and the
   client that uses it. A functor applied to A (R : T := F A) substitutes the
   functor's parameter with A's whole resolver, so that R's signature, as
   rocqchk computes it, may name the alias's target where coqc named the
   declaration of X. The helpers, and the value layouts they rely on, are
   those of misc/rocqchk_forge_lib.ml.

   Commands (each writes a new file; the input is left as it is):
     forge.ml sealed HONEST_LIB.vo OUT.vo         A.X.d -> A.X.c
     forge.ml same-label HONEST_LIB.vo OUT.vo     A.X.d -> A.Y.d
     forge.ml inductive HONEST_LIB.vo OUT.vo      A.X.I -> A.Y.I
     forge.ml client CLIENT.vo LIB.vo LIB_DIRPATH OUT.vo *)

#use "./misc/rocqchk_forge_lib.ml";;

(* A.<x>: the module path MPdot (MPdot (_, A), x). *)
let mp_is_a x mp = mp_is_dot x mp && mp_is_dot "A" (field mp 0)

(* The corruption the test is about: A's delta resolver (module_body field
   3; for a sealed A, its signature's resolver) gets the entry
   [user] -> Equiv [canonical]. A.X's own resolver, A's implementation and
   every term of A are left as they are. *)
let alias_in_a ~user ~canonical root =
  let a = module_of root "A" in
  say "forge: A's delta resolver gets %s -> Equiv %s" (kn_to_string user) (kn_to_string canonical);
  struc_update root "A" (set 0 (upd 3 (fun reso -> add_equiv reso user canonical) a))

(* Whether the alias is between constants or between inductives. *)
type kind = Constant | Inductive

(* R : T := F A, where R.c' names A.<cm>.<cl> and the type of R.e names
   A.X.<ul>. Record in A's resolver that A.X.<ul> is an alias of
   A.<cm>.<cl>, and, in T and in R's stored signature (T's, as coqc copied
   it), make e's type name A.<cm>.<cl> instead of A.X.<ul>: a plain name,
   with no alias. This is the signature that the check of R computes from
   F's body with A's forged resolver, as the alias makes the two names
   convertible. The names are taken from R's stored signature, hash
   included, never rebuilt. *)
let forge_nested kind ~ul ~cm ~cl disk =
  let root = root_struc disk in
  let rsig = sig_struc root "R" in
  let names = match kind with Constant -> cb_constants | Inductive -> cb_inductives in
  let canonical = find_kn ~names rsig ~label:cl ~in_mp:(mp_is_a cm) in
  let user = find_kn ~names rsig ~label:ul ~in_mp:(mp_is_a "X") in
  say "forge: A.%s.%s is %s, A.X.%s is %s" cm cl (kn_to_string canonical) ul (kn_to_string user);
  let root = alias_in_a ~user ~canonical root in
  (* [p] is the (constant, instance) pair of a Const node, or the
     ((inductive, index), instance) pair of an Ind node. *)
  let to_canonical count p =
    match kind with
    | Constant ->
      if kn_equal (cst_user (field p 0)) user then begin
        incr count;
        Some (block 0 [| block 0 [| canonical |]; field p 1 |])
      end
      else None
    | Inductive ->
      let ind = field p 0 in
      if kn_equal (cst_user (field ind 0)) user then begin
        incr count;
        Some (block 0 [| block 0 [| block 0 [| canonical |]; field ind 1 |]; field p 1 |])
      end
      else None
  in
  let rename count cb =
    match kind with
    | Constant -> map_cb (to_canonical count) cb
    | Inductive -> map_cb ~fi:(to_canonical count) (fun _ -> None) cb
  in
  let in_t = ref 0 and in_r = ref 0 in
  let e_type count = upd 1 (upd 0 (fun struc -> struc_update struc "e" (upd 0 (rename count)))) in
  expect "field T (a module type)" 4 (struc_find root "T");
  let root = struc_update root "T" (upd 0 (e_type in_t)) in
  let r = module_of root "R" in
  if is_block (impl_of r) && tag (impl_of r) = 1 then
    fail "R has a Struct implementation, not the algebraic F A";
  let root = struc_update root "R" (set 0 (e_type in_r r)) in
  if !in_t <> 1 || !in_r <> 1 then
    fail "expected one mention of %s in T.e and in R.e, found %d and %d" (kn_to_string user) !in_t !in_r;
  set_root_struc disk root;
  disk

let () =
  let forge kind ~ul ~cm ~cl src dst = rewrite_vo ~src ~dst [ "library", forge_nested kind ~ul ~cm ~cl ] in
  match List.tl (Array.to_list Sys.argv) with
  | [ "sealed"; src; dst ] -> forge Constant ~ul:"d" ~cm:"X" ~cl:"c" src dst
  | [ "same-label"; src; dst ] -> forge Constant ~ul:"d" ~cm:"Y" ~cl:"d" src dst
  | [ "inductive"; src; dst ] -> forge Inductive ~ul:"I" ~cm:"Y" ~cl:"I" src dst
  | [ "client"; src; lib; lib_dp; dst ] -> client ~src ~lib ~lib_dp ~dst
  | _ ->
    prerr_endline
      "usage: forge.ml sealed|same-label|inductive LIB.vo OUT.vo | client CLIENT.vo LIB.vo LIB_DIRPATH OUT.vo";
    exit 2
