(* Forge a .vo file whose functor records, in the delta resolver of its
   body, an alias that changes label, for rocqchk_alias_label.sh: in
   F (P : S), F.k becomes an alias of P.X.d. F.k := P.X.d converts with its
   target. A functor application rebuilds a name's canonical part with the
   user name's label (Mod_subst.subst_con0_flat), so (F.k, P.X.d) becomes
   (G.k, A.X.k) in G := F A: a field that F never named. The helpers, and
   the value layouts they rely on, are those of misc/rocqchk_forge_lib.ml.

   Commands (each writes a new file; the input is left as it is):
     forge.ml label HONEST_LIB.vo OUT.vo
     forge.ml client CLIENT.vo LIB.vo LIB_DIRPATH OUT.vo *)

#use "./misc/rocqchk_forge_lib.ml";;

(* <P#n>.X: the module path MPdot (MPbound _, X). *)
let mp_is_px mp = mp_is_dot "X" mp && mp_is_bound (field mp 0)

(* In the body of functor F (P : S), whose fields are k := P.X.d and
   lemma : eq bool k false := P.X.f, record that F.k is an alias of P.X.d,
   from label k to label d: F's delta resolver (module_body field 3, the
   resolver of F's body) gets the entry, and every mention of F.k (lemma's
   type) is named (user F.k, canonical P.X.d), which is how a term must name
   it once the resolver says so (Typeops.check_constant refuses any other
   canonical name). F.k's own declaration is not changed: it converts with
   its target P.X.d. Names are taken from the file, hash included, never
   rebuilt. *)
let forge_label disk =
  let root = root_struc disk in
  let fmb = module_of root "F" in
  let sign = field fmb 1 in
  expect "F's signature (MoreFunctor)" 1 sign;
  let body = nofunctor "F's body" (field sign 2) in
  let fk = find_kn body ~label:"k" ~in_mp:(mp_is_dot "F") in
  let xd = find_kn body ~label:"d" ~in_mp:mp_is_px in
  say "forging: in F's body, %s becomes an alias of %s" (kn_to_string fk) (kn_to_string xd);
  let in_body = ref 0 and in_impl = ref 0 in
  let rename count = map_consts (counted count (retarget ~user:fk ~canonical:xd)) in
  let sign = upd 2 (upd 0 (rename in_body)) sign in
  let fmb =
    fmb
    |> set 1 sign
    |> upd 0 (upd 0 (fun i -> if is_block i && tag i = 1 then upd 1 (rename in_impl) i else i))
    |> upd 3 (fun reso -> add_equiv reso fk xd)
  in
  if !in_body = 0 then fail "F's body does not mention %s" (kn_to_string fk);
  say "forging: renamed %d mention(s) of %s in F's body, %d in F's %s implementation"
    !in_body (kn_to_string fk) !in_impl (impl_kind (impl_of fmb));
  set_root_struc disk (struc_update root "F" (set 0 fmb));
  disk

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [ "label"; src; dst ] -> rewrite_vo ~src ~dst [ "library", forge_label ]
  | [ "client"; src; lib; lib_dp; dst ] -> client ~src ~lib ~lib_dp ~dst
  | _ ->
    prerr_endline
      "usage: ocaml forge.ml label LIB.vo OUT.vo | client CLIENT.vo LIB.vo LIB_DIRPATH OUT.vo";
    exit 2
