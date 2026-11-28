#use "./misc/rocqchk_forge_lib.ml";;

(* The forger of misc/rocqchk_private_functor.sh.

   usage: ocaml misc/rocqchk-private-functor/forge.ml <src.vo> <dst.vo> <module> <label>

   It makes the inductive block <label> of the module <module> of the
   library private and open to matching (mind_private: None becomes
   Some false), in that module's type and in its implementation when it has
   one, and writes <dst.vo>: the .vo that a compiler without check_private
   writes when that inductive is private. The helpers, and the value layouts
   they rely on, are those of misc/rocqchk_forge_lib.ml; this file also
   relies on mutual_inductive_body's 13 fields, field 11 being mind_private
   (checker/values.ml, v_ind_pack). *)

let private_open = block 0 [| Obj.repr false |]

let make_private label struc =
  struc_update struc label (fun sfb ->
      expect ~size:1 ("field " ^ label ^ " (an inductive)") 1 sfb;
      upd 0 (fun mib ->
          expect ~size:13 (label ^ "'s mutual_inductive_body") 0 mib;
          if not (Obj.is_int (field mib 11)) then fail "%s is private already" label;
          set 11 private_open mib) sfb)

let () =
  match Sys.argv with
  | [| _; src; dst; m; label |] ->
    rewrite_vo ~src ~dst [ "library", fun disk ->
        let struc = root_struc disk in
        let struc = struc_update struc m (fun sfb ->
            expect ~size:1 ("field " ^ m ^ " (a module)") 3 sfb;
            upd 0 (fun mb ->
                mb
                |> upd 1 (fun sign -> set 0 (make_private label (nofunctor m sign)) sign)
                |> upd 0 (upd 0 (fun impl ->
                    if is_block impl && tag impl = 1 then upd 1 (make_private label) impl
                    else impl)))
              sfb)
        in
        set_root_struc disk struc;
        disk ]
  | _ -> prerr_endline "usage: forge.ml <src.vo> <dst.vo> <module> <label>"; exit 2
