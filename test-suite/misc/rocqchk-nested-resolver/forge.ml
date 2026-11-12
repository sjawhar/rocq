(* Forge a .vo file whose module A's delta resolver records the alias
   A.X.d -> A.X.c that the resolver of its submodule X does not, and the
   client that uses it. A functor applied to A (R : T := F A) substitutes the
   functor's parameter with A's whole resolver, so that R's signature, as
   rocqchk computes it, may say A.X.c where coqc said A.X.d. The helpers,
   and the value layouts they rely on, are those of
   misc/rocqchk_forge_lib.ml.

   Commands (each writes a new file; the input is left as it is):
     forge.ml sealed HONEST_LIB.vo OUT.vo
     forge.ml client CLIENT.vo LIB.vo LIB_DIRPATH OUT.vo *)

#use "./misc/rocqchk_forge_lib.ml";;

(* A.X: the module path MPdot (MPdot (_, A), X). *)
let mp_is_ax mp = mp_is_dot "X" mp && mp_is_dot "A" (field mp 0)

(* The kernel names of A.X.c and A.X.d, as R's stored signature mentions
   them: R.c' is a definition of A.X.c and R.e's type mentions A.X.d. Names
   are taken from the file, hash included, never rebuilt. *)
let ax_names root =
  let rsig = nofunctor "module R" (field (module_of root "R") 1) in
  let xc = find_kn rsig ~label:"c" ~in_mp:mp_is_ax in
  let xd = find_kn rsig ~label:"d" ~in_mp:mp_is_ax in
  say "forge: A.X.c is %s, A.X.d is %s" (kn_to_string xc) (kn_to_string xd);
  xc, xd

(* The corruption the test is about: A's delta resolver (module_body field
   3; for a sealed A, its signature's resolver) gets the entry
   A.X.d -> Equiv A.X.c. A.X's own resolver, A's implementation and every
   term of A are left as they are. *)
let alias_in_a ~xc ~xd root =
  let a = module_of root "A" in
  say "forge: A's delta resolver gets %s -> Equiv %s" (kn_to_string xd) (kn_to_string xc);
  struc_update root "A" (set 0 (upd 3 (fun reso -> add_equiv reso xd xc) a))

(* R : T := F A. In T and in R's stored signature (T's, as coqc copied it),
   e's type eq bool A.X.d false becomes eq bool A.X.c false: the constant
   A.X.d is replaced by the constant A.X.c, a plain name with no alias. This
   is the signature that the check of R computes from F's body with A's
   forged resolver, as the alias A.X.d -> A.X.c makes the two names
   convertible. *)
let forge_sealed disk =
  let root = root_struc disk in
  let xc, xd = ax_names root in
  let root = alias_in_a ~xc ~xd root in
  let to_xc count p =
    let c = field p 0 in
    if kn_equal (cst_user c) xd then begin
      incr count;
      Some (block 0 [| block 0 [| xc |]; field p 1 |])
    end
    else None
  in
  let in_t = ref 0 and in_r = ref 0 in
  let e_type count = upd 1 (upd 0 (fun struc -> struc_update struc "e" (upd 0 (map_cb (to_xc count))))) in
  expect "field T (a module type)" 4 (struc_find root "T");
  let root = struc_update root "T" (upd 0 (e_type in_t)) in
  let r = module_of root "R" in
  if is_block (impl_of r) && tag (impl_of r) = 1 then
    fail "R has a Struct implementation, not the algebraic F A";
  let root = struc_update root "R" (set 0 (e_type in_r r)) in
  if !in_t <> 1 || !in_r <> 1 then
    fail "expected one mention of %s in T.e and in R.e, found %d and %d" (kn_to_string xd) !in_t !in_r;
  set_root_struc disk root;
  disk

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [ "sealed"; src; dst ] -> rewrite_vo ~src ~dst [ "library", forge_sealed ]
  | [ "client"; src; lib; lib_dp; dst ] -> client ~src ~lib ~lib_dp ~dst
  | _ ->
    prerr_endline "usage: forge.ml sealed LIB.vo OUT.vo | client CLIENT.vo LIB.vo LIB_DIRPATH OUT.vo";
    exit 2
