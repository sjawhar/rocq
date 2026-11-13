(* Replace the rewrite-rule block in the declared type of the alias N by the
   block of another compiled copy of the same logical library, whose rule
   differs, leaving N's target S unchanged. The file is rewritten in place.
   The helpers, and the value layouts they rely on, are those of
   misc/rocqchk_forge_lib.ml: a rewrite-rule block is the field SFBrules
   (tag 2) [rewrite_rules_body].

   Command:
     forge.ml ALIAS.vo DONOR.vo *)

#use "./misc/rocqchk_forge_lib.ml";;

(* The structure of the type of the module [name] of [root]. *)
let sig_struc root name = nofunctor ("module " ^ name) (field (module_of root name) 1)

(* The payload of the field [name] of [struc], which must be an SFBrules. *)
let rules struc name =
  let sfb = struc_find struc name in
  expect ~size:1 (name ^ " (a rewrite-rule block)") 2 sfb;
  field sfb 0

let forge ~donor disk =
  let root = root_struc disk in
  let marshal v = Marshal.to_string v [] in
  let s_rules root = marshal (rules (sig_struc root "S") "f_rew") in
  let before = s_rules root in
  let donor_rules = rules (sig_struc (root_struc donor) "N") "f_rew" in
  if String.equal (marshal (rules (sig_struc root "N") "f_rew")) (marshal donor_rules) then
    fail "the donor's rule block is the target's";
  (* An alias's type shares unchanged fields with its target's (substitution
     keeps a field that it does not change): struc_update copies the
     structure down to the new field, and S's type is left as it is. *)
  let root =
    struc_update root "N"
      (upd 0 (upd 1 (upd 0 (fun struc ->
           struc_update struc "f_rew" (fun _ -> block 2 [| donor_rules |])))))
  in
  if not (String.equal before (s_rules root)) then fail "the forge changed S's rule block";
  set_root_struc disk root;
  disk

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [ file; donor ] ->
    rewrite_vo ~src:file ~dst:file [ "library", forge ~donor:(library_value donor) ]
  | _ ->
    prerr_endline "usage: forge.ml ALIAS.vo DONOR.vo";
    exit 2
