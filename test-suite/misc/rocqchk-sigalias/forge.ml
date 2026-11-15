(* Forge .vo files whose module signatures record a delta-resolver alias
   between two declared-only fields (Parameters), for rocqchk_sigalias.sh.
   The helpers, and the value layouts they rely on, are those of
   misc/rocqchk_forge_lib.ml.

   Commands (each writes a new file; the input is left as it is):
     forge.ml sealed HONEST_LIB.vo OUT.vo
     forge.ml cross HONEST_LIB.vo OUT.vo
     forge.ml functor DONOR_LIB.vo HONEST_LIB.vo OUT.vo
     forge.ml client CLIENT.vo LIB.vo LIB_DIRPATH OUT.vo *)

#use "./misc/rocqchk_forge_lib.ml";;

(* Cases "sealed" and "cross". In module [um]'s signature, record that
   [um].[ul] is an alias of [tm].[tl]: add the entry to [um]'s delta
   resolver (module_body field 3), and, in the type of field [rf], name
   [um].[ul] as (user [um].[ul], canonical [tm].[tl]), which is how a term
   must name it once the resolver says so (Typeops.check_constant refuses
   any other canonical name). The module's implementation, with the resolver
   of its Struct, is not touched. *)
let forge_alias ~um ~ul ~tm ~tl ~rf disk =
  let root = root_struc disk in
  let user = find_kn (sig_struc root um) ~label:ul ~in_mp:(mp_is_dot um) in
  let canonical = find_kn (sig_struc root tm) ~label:tl ~in_mp:(mp_is_dot tm) in
  say "forging: in %s's signature, %s becomes an alias of %s" um (kn_to_string user)
    (kn_to_string canonical);
  let count = ref 0 in
  let rename = counted count (retarget ~user ~canonical) in
  let mb = module_of root um in
  let mb =
    mb
    |> upd 1 (upd 0 (fun struc -> struc_update struc rf (upd 0 (map_cb rename))))
    |> upd 3 (fun reso -> add_equiv reso user canonical)
  in
  if !count = 0 then fail "%s.%s does not mention %s" um rf (kn_to_string user);
  say "forging: renamed %d mention(s) of %s in %s.%s" !count (kn_to_string user) um rf;
  set_root_struc disk (struc_update root um (set 0 mb));
  disk

(* Case "functor". [disk] is donor/Lib.vo: F (X : T) proves true = false from
   X.f : X.c = false. Put the honest T and M back, then make the type of F's
   parameter read as the honest T: f's type names X.d, as (user X.d,
   canonical X.c), and the parameter's resolver says X.d is an alias of X.c.
   Every mention of X.d in F's body becomes (X.d, X.c) too. *)
let forge_functor ~honest disk =
  let honest_root = root_struc honest in
  let root =
    List.fold_left
      (fun struc name -> struc_update struc name (fun _ -> struc_find honest_root name))
      (root_struc disk) [ "T"; "M" ]
  in
  say "forging: fields T and M are honest/Lib.vo's";
  let fmb = module_of root "F" in
  let sign = field fmb 1 in
  expect "F's signature (MoreFunctor)" 1 sign;
  let mtb = field sign 1 in
  let param = nofunctor "F's parameter" (field mtb 1) in
  let body = nofunctor "F's body" (field sign 2) in
  let xc = find_kn param ~label:"c" ~in_mp:mp_is_bound in
  let xd = find_kn body ~label:"d" ~in_mp:mp_is_bound in
  if compare (kn_mp xc) (kn_mp xd) <> 0 then
    fail "X.c is %s but X.d is %s" (kn_to_string xc) (kn_to_string xd);
  say "forging: in F's parameter type, %s becomes an alias of %s" (kn_to_string xd) (kn_to_string xc);
  let in_f = ref 0 and in_body = ref 0 and in_impl = ref 0 in
  (* f's type: X.c = false becomes (X.d, canonical X.c) = false *)
  let to_xd p =
    let c = field p 0 in
    if kn_equal (cst_user c) xc then Some (block 0 [| dual xd xc; field p 1 |]) else None
  in
  let param = struc_update param "f" (upd 0 (map_cb (counted in_f to_xd))) in
  let mtb = mtb |> upd 1 (set 0 param) |> upd 3 (fun reso -> add_equiv reso xd xc) in
  let rename count = map_consts (counted count (retarget ~user:xd ~canonical:xc)) in
  let sign = sign |> set 1 mtb |> upd 2 (upd 0 (rename in_body)) in
  let fmb = set 1 sign fmb in
  let fmb =
    upd 0
      (upd 0 (fun i -> if is_block i && tag i = 1 then upd 1 (rename in_impl) i else i))
      fmb
  in
  if !in_f = 0 then fail "F's parameter's f does not mention %s" (kn_to_string xc);
  say "forging: renamed %d mention(s) of %s in the parameter's f, %d of %s in F's body, %d in F's %s implementation"
    !in_f (kn_to_string xc) !in_body (kn_to_string xd) !in_impl (impl_kind (impl_of fmb));
  set_root_struc disk (struc_update root "F" (set 0 fmb));
  disk

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [ "sealed"; src; dst ] ->
    rewrite_vo ~src ~dst [ "library", forge_alias ~um:"M" ~ul:"d" ~tm:"M" ~tl:"c" ~rf:"f" ]
  | [ "cross"; src; dst ] ->
    rewrite_vo ~src ~dst [ "library", forge_alias ~um:"M2" ~ul:"c" ~tm:"M1" ~tl:"c" ~rf:"f" ]
  | [ "functor"; donor; honest; dst ] ->
    rewrite_vo ~src:donor ~dst [ "library", forge_functor ~honest:(library_value honest) ]
  | [ "client"; src; lib; lib_dp; dst ] -> client ~src ~lib ~lib_dp ~dst
  | _ ->
    prerr_endline
      "usage: ocaml forge.ml sealed LIB.vo OUT.vo | cross LIB.vo OUT.vo\n\
      \       | functor DONOR_LIB.vo HONEST_LIB.vo OUT.vo | client CLIENT.vo LIB.vo LIB_DIRPATH OUT.vo";
    exit 2
