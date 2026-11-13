open Pp
open Util
open Names
open Conversion
open Declarations
open Mod_declarations
open Environ

(** {6 Checking constants } *)

(** {6 Compiling the VM bytecode}

    The checker never reads the [vmlibrary] segment of a [.vo] file, and it does
    not trust the code descriptors [const_body_code] stored in the declarations
    either: both are attacker-controlled data that the typechecker has no way to
    validate. Instead it recompiles the bytecode of every constant from the body
    it is about to check, and records it in a table of its own, so that the code
    the VM runs agrees with the checked body by construction.

    With [-merge-inductives] the body it compiles is the one the file holds, and
    the body it checks is that one with the merges of earlier libraries applied
    ([Safe_checking.import]), so the two are no longer the same term and the
    agreement is no longer by construction. It still holds, by the four-part
    argument stated where the merge is applied; a change to the relocation
    tables of [Vmemitcodes] can break it. *)

let push_bytecode vmtab code =
  let open Vmemitcodes in
  match code with
  | None -> vmtab, None
  | Some (BCdefined (mask, code, patches)) ->
    let vmtab, index = Vmlibrary.add code vmtab in
    vmtab, Some (BCdefined (mask, index, patches))
  | Some BCconstant -> vmtab, Some BCconstant
  | Some (BCalias kn) -> vmtab, Some (BCalias kn)

let compile_constant_bytecode env vmtab c cb =
  let code =
    Vmbytegen.compile_constant_body ~name:c ~fail_on_error:false env
      cb.const_universes cb.const_body
  in
  let vmtab, code = push_bytecode vmtab code in
  vmtab, { cb with const_body_code = code }

(* The environment is threaded exactly as in [Modops.add_structure], so that
   each constant is compiled in the environment it is declared in. *)
let rec compile_structure env vmtab mp res struc =
  let fold (env, vmtab, accu) (lab, sfb) = match sfb with
  | SFBconst cb ->
    let c = Mod_subst.constant_of_delta_kn res (KerName.make mp lab) in
    let vmtab, cb = compile_constant_bytecode env vmtab c cb in
    Environ.add_constant c cb env, vmtab, (lab, SFBconst cb) :: accu
  | SFBmind mib ->
    let mind = Mod_subst.mind_of_delta_kn res (KerName.make mp lab) in
    Environ.add_mind mind mib env, vmtab, (lab, sfb) :: accu
  | SFBmodule mb ->
    let mp = MPdot (mp, lab) in
    let vmtab, mb = compile_module_bytecode env vmtab mp mb in
    Modops.add_module mp mb env, vmtab, (lab, SFBmodule mb) :: accu
  | SFBmodtype mtb ->
    let mp = MPdot (mp, lab) in
    let vmtab, mtb = compile_module_bytecode env vmtab mp mtb in
    add_modtype mp mtb env, vmtab, (lab, SFBmodtype mtb) :: accu
  | SFBrules rrb ->
    Environ.add_rewrite_rules rrb.rewrules_rules env, vmtab, (lab, sfb) :: accu
  in
  let (_ : env), vmtab, accu = List.fold_left fold (env, vmtab, []) struc in
  vmtab, List.rev accu

and compile_signature env vmtab mp res = function
  | MoreFunctor (arg_id, mtb, body) ->
    let vmtab, mtb = compile_module_bytecode env vmtab (MPbound arg_id) mtb in
    let env = Modops.add_module_parameter arg_id mtb env in
    let vmtab, body = compile_signature env vmtab mp res body in
    vmtab, MoreFunctor (arg_id, mtb, body)
  | NoFunctor struc ->
    let vmtab, struc = compile_structure env vmtab mp res struc in
    vmtab, NoFunctor struc

and compile_module_bytecode : 'a. env -> Vmlibrary.t -> ModPath.t ->
  'a generic_module_body -> Vmlibrary.t * 'a generic_module_body =
  fun env vmtab mp mb ->
  let vmtab, sign = compile_signature env vmtab mp (mod_delta mb) (mod_type mb) in
  vmtab, Mod_declarations.set_signature sign mb

let indirect_accessor : (Opaqueproof.opaque -> Opaqueproof.opaque_proofterm) ref =
  ref (fun _ -> assert false)

let set_indirect_accessor f = indirect_accessor := f

let register_opacified_constant env opac kn cb =
  let rec gather_consts s c =
    match Constr.kind c with
    | Constr.Const (c, _) -> Cset.add c s
    | _ -> Constr.fold gather_consts s c
  in
  let wo_body =
    Cset.fold
      (fun kn s ->
        if Declareops.constant_has_body (lookup_constant kn env) then s else
          match Cmap.find_opt kn opac with
          | None -> Cset.add kn s
          | Some s' -> Cset.union s' s)
      (gather_consts Cset.empty cb)
      Cset.empty
  in
  Cmap.add kn wo_body opac

exception BadConstant of Constant.t * Pp.t

let pr_prim_type prm = str (CPrimitives.prim_type_to_string prm)

(* The universe instance at which coqc gives a primitive declared as [cb]
   its type: empty for a monomorphic constant, the abstract instance for a
   polymorphic one, whose universe context has the size of the primitive's
   ([expected]) and no constraints
   ([Constant_typing.adjust_primitive_univ_entry]). [refuse] is called
   otherwise. [Typeops.type_of_prim_type] and [Typeops.type_of_prim]
   assert the length of the instance, so it is tested here. *)
let primitive_instance refuse cb expected =
  let u = match cb.const_universes with
    | Monomorphic -> UVars.Instance.empty
    | Polymorphic auctx ->
      let constraints = UVars.UContext.constraints (UVars.AbstractContext.repr auctx) in
      let () =
        if not (PConstraints.is_empty constraints)
        then refuse (str "its universe context has constraints")
      in
      UVars.make_abstract_instance auctx
  in
  let () =
    if UVars.Instance.length u <> UVars.AbstractContext.size expected
    then refuse (str "its universe instance has the wrong length")
  in
  u

(* Typeops types a primitive literal with the constant registered for its
   primitive type ([Typeops.type_of_int] and the like), and conversion
   unfolds that constant, so the typing of every literal trusts the
   registration. A definition [int : Set := Empty_set] registered as the
   int63 type would give [Int 0] the type Empty_set, and [match] on it a
   closed proof of False. coqc registers only the constant that [Primitive]
   declares, a parameter whose type is the primitive type's
   ([Constant_typing.infer_primitive]), and rocqchk refuses any other. [env]
   holds the constant's universe context. *)
let check_register_type (type a) env kn cb (prm : a CPrimitives.prim_type) =
  let refuse why =
    raise (BadConstant (kn, str "is registered as the primitive type " ++
                            pr_prim_type prm ++ str ", but " ++ why ++ str "."))
  in
  let () = match cb.const_body with
    | Undef _ -> ()
    | Def _ | OpaqueDef _ | Primitive _ | Symbol _ -> refuse (str "it is not a parameter")
  in
  let u = primitive_instance refuse cb (CPrimitives.typ_univs prm) in
  match conv env (Typeops.type_of_prim_type env u prm) cb.const_type with
  | Result.Ok () -> ()
  | Result.Error () -> refuse (str "its type is not the primitive type's")

(* A constant whose body is [Primitive op] is the operator [op], which
   reduction computes by its own rules, whatever the constant's type says.
   coqc declares it with the operator's type
   ([Constant_typing.check_primitive_type]): any other, say
   [add : int -> int -> False], would make [add 0 0] a closed proof of
   False. [env] holds the constant's universe context. *)
let check_primitive_operator env kn cb op =
  let refuse why =
    raise (BadConstant (kn, str "is the primitive operator " ++
                            str (CPrimitives.to_string op) ++ str ", but " ++ why ++ str "."))
  in
  let u = primitive_instance refuse cb (CPrimitives.univs op) in
  match conv env (Typeops.type_of_prim env u op) cb.const_type with
  | Result.Ok () -> ()
  | Result.Error () -> refuse (str "its type is not the operator's")

(* A library's registrations are in the environment before any of its
   constants is checked ([Safe_checking.env_of_library]), and so are a
   module's ([check_module]), which refuses a registration of a constant
   that the module's own body does not declare: each registered constant is
   checked here, in an environment that registers it, where the module's
   own body declares it ([own]). The environment finds a constant by its
   user name, and so a registration of [kn]; the registered name must also
   have [kn]'s canonical name, which conversion compares, and coqc
   registers a constant as one primitive type only. *)
let check_registered_type env kn cb =
  let open Retroknowledge in
  let retro = Environ.retroknowledge env in
  let registered c prm = match c with
    | Some c when Constant.UserOrd.equal c kn -> [c, prm]
    | Some _ | None -> []
  in
  let open CPrimitives in
  match registered retro.retro_int63 (PTE PT_int63)
        @ registered retro.retro_float64 (PTE PT_float64)
        @ registered retro.retro_string (PTE PT_string)
        @ registered retro.retro_array (PTE PT_array) with
  | [] -> ()
  | [c, PTE prm] ->
    let () =
      if not (Constant.CanOrd.equal c kn) then
        raise (BadConstant (kn, str "is registered as the primitive type " ++
                                pr_prim_type prm ++ str " under the canonical name " ++
                                KerName.print (Constant.canonical c) ++ str ", not its own."))
    in
    check_register_type env kn cb prm
  | _ :: _ :: _ ->
    raise (BadConstant (kn, str "is registered as more than one primitive type."))

let check_constant_declaration env opac kn cb opacify ~own =
  Flags.if_verbose Feedback.msg_notice (str "  checking cst:" ++ Constant.print kn);
  let env = CheckFlags.set_local_flags cb.const_typing_flags env in
  let poly, env =
    match cb.const_universes with
    | Monomorphic ->
      (* Monomorphic universes are stored at the library level, the
         ones in const_universes should not be needed *)
      false, env
    | Polymorphic auctx ->
      let ctx = UVars.AbstractContext.repr auctx in
      (* [env] contains De Bruijn universe variables *)
      let () = check_ucontext ctx env in
      let env = push_context ~strict:false ctx env in
      true, env
  in
  let ty = cb.const_type in
  let jty = Typeops.infer_type env ty in
  if not (Sorts.relevance_equal cb.const_relevance (Sorts.relevance_of_sort jty.utj_type))
  then raise Pp.(BadConstant (kn, str "incorrect const_relevance"));
  let () = if own then check_registered_type env kn cb in
  let check env bd () =
    let j = Typeops.infer env bd in
    match conv_leq env j.uj_type ty with
    | Result.Ok () -> ()
    | Result.Error () -> Type_errors.error_actual_type env j ty
  in
  (* The body of an opaque constant, cooked: fetched from its library's
     table and discharged by [CheckLibrary.indirect_accessor], then
     substituted
     ([subst_mps_list]), with the environment extended by its private
     universes. A pure function of the stored proof and its cooking
     information (kernel/discharge.ml), and of nothing that the checking
     changes: the table is the library's file as the main process hashed
     it when it interned the library, which the process that reads it
     checks (CheckLibrary.read_opaque_table). [note_cook] counts this
     where it runs, so that a test can tell the main process from a
     worker. *)
  let cook o =
    CheckWorkers.note_cook ();
    let c, u = !indirect_accessor o in
    let env = match u, cb.const_universes with
      | Opaqueproof.PrivateMonomorphic (), Monomorphic -> env
      | Opaqueproof.PrivatePolymorphic local, Polymorphic _ ->
        push_subgraph local env
      | _ -> assert false
    in
    c, env
  in
  match cb.const_body with
  | Undef _ | Symbol _ -> opac
  | Primitive op ->
    check_primitive_operator env kn cb op;
    opac
  | Def c ->
    (* A transparent body may be unfolded by later checks, which rely on
       it being well-typed, so it is checked here. *)
    check env c ();
    if opacify then register_opacified_constant env opac kn c else opac
  | OpaqueDef o when opacify ->
    (* A constant of a sealed module that its signature declares without
       a body: what it uses is recorded from its body, which is therefore
       cooked here, in the main process. Its check is still deferred. *)
    let c, env = cook o in
    CheckWorkers.defer kn (check env c);
    register_opacified_constant env opac kn c
  | OpaqueDef o ->
    (* Nothing else that is checked looks into an opaque body, so its check
       can be postponed, and possibly run in another process, and so can
       its cooking: the main process keeps no cooked body while the check
       waits. The process that runs the check reads the table it needs
       ([CheckLibrary.indirect_accessor]), and a check handed back cooks
       again in the process that runs it. With -j 1, [defer] runs the
       closure at once, so the order of effects is as before. *)
    CheckWorkers.defer kn (fun () -> let c, env = cook o in check env c ());
    opac

let check_constant_declaration env opac kn cb opacify ~own =
  let opac = NewProfile.profile "check_constant" ~args:(fun () ->
      [("name", `String (Constant.to_string kn))])
      (fun () -> check_constant_declaration env opac kn cb opacify ~own)
      ()
  in
  Environ.add_constant kn cb env, opac

let check_quality_mask env qmask lincheck =
  let open Sorts.Quality in
  match qmask with
  | PQConstant QSProp -> if Environ.sprop_allowed env then lincheck else Type_errors.error_not_allowed_sprop env
  | PQConstant (QProp | QType) -> lincheck
  | PQVar qio -> Partial_subst.maybe_add_quality qio () lincheck

let check_instance_mask env udecl umask lincheck =
  match udecl, umask with
    | Monomorphic, ([||], [||]) -> lincheck
    | Polymorphic uctx, (qmask, umask) ->
        let lincheck = Array.fold_left_i (fun i lincheck mask -> check_quality_mask env mask lincheck) lincheck qmask in
        let lincheck = Array.fold_left_i (fun i lincheck mask -> Partial_subst.maybe_add_univ mask () lincheck) lincheck umask in
        if (Array.length qmask, Array.length umask) <> UVars.AbstractContext.size uctx then CErrors.anomaly Pp.(str "Bad univ mask length.");
        lincheck
    | _ -> CErrors.anomaly Pp.(str "Bad univ mask length.")

let rec get_holes_profiles env nargs ndecls lincheck el =
  List.fold_left (get_holes_profiles_elim env nargs ndecls) lincheck el

and get_holes_profiles_elim env nargs ndecls lincheck = function
  | PEApp args -> Array.fold_left (get_holes_profiles_parg env nargs ndecls) lincheck args
  | PECase (ind, ret, brs) ->
      let mib, mip = Inductive.lookup_mind_specif env ind in
      let lincheck = get_holes_profiles_parg env (nargs + mip.mind_nrealargs + 1) (ndecls + mip.mind_nrealdecls + 1) lincheck ret in
      Array.fold_left3 (fun lincheck nargs_b ndecls_b -> get_holes_profiles_parg env (nargs + nargs_b) (ndecls + ndecls_b) lincheck) lincheck mip.mind_consnrealargs mip.mind_consnrealdecls brs
  | PEProj proj ->
      let () = lookup_projection (Projection.make proj false) env |> ignore in
      lincheck

and get_holes_profiles_headelim env nargs ndecls lincheck (h, el) =
  let lincheck = get_holes_profiles_head env nargs ndecls lincheck h in
  get_holes_profiles env nargs ndecls lincheck el

and get_holes_profiles_parg env nargs ndecls lincheck = function
  | EHoleIgnored -> lincheck
  | EHole i -> Partial_subst.add_term i nargs lincheck
  | ERigid hel ->
      get_holes_profiles_headelim env nargs ndecls lincheck hel

and get_holes_profiles_head env nargs ndecls lincheck = function
  | PHRel n -> if n <= ndecls then lincheck else Type_errors.error_unbound_rel env n
  | PHSymbol (c, u) ->
      let cb = lookup_constant c env in
      check_instance_mask env cb.const_universes u lincheck
  | PHConstr (c, u) ->
      let (mib, _) = Inductive.lookup_mind_specif env (inductive_of_constructor c) in
      check_instance_mask env mib.mind_universes u lincheck
  | PHInd (ind, u) ->
      let (mib, _) = Inductive.lookup_mind_specif env ind in
      check_instance_mask env mib.mind_universes u lincheck
  | PHInt _  | PHFloat _ | PHString _ -> lincheck
  | PHSort PSSProp -> if Environ.sprop_allowed env then lincheck else Type_errors.error_not_allowed_sprop env
  | PHSort PSType io -> Partial_subst.maybe_add_univ io () lincheck
  | PHSort PSQSort (qio, uio) ->
      lincheck
      |> Partial_subst.maybe_add_quality qio ()
      |> Partial_subst.maybe_add_univ uio ()
  | PHSort _ -> lincheck
  | PHLambda (tys, bod) ->
      let lincheck = Array.fold_left_i (fun i -> get_holes_profiles_parg env (nargs + i) (ndecls + i)) lincheck tys in
      let lincheck = get_holes_profiles_headelim env (nargs + Array.length tys) (ndecls + Array.length tys) lincheck bod in
      lincheck
  | PHProd (tys, bod) ->
      let lincheck = Array.fold_left_i (fun i -> get_holes_profiles_parg env (nargs + i) (ndecls + i)) lincheck tys in
      let lincheck = get_holes_profiles_parg env (nargs + Array.length tys) (ndecls + Array.length tys) lincheck bod in
      lincheck

let check_rhs env holes_profile rhs =
  let rec check i c = match Constr.kind c with
    | App (f, args) when Constr.isRel f ->
        let n = Constr.destRel f in
        if n <= i then () else
          if n - i > Array.length holes_profile then CErrors.anomaly Pp.(str "Malformed right-hand-side substitution site");
          let d = holes_profile.(n-i-1) in
          if Array.length args >= d then () else CErrors.anomaly Pp.(str "Malformed right-hand-side substitution site")
    | Rel n when n > i ->
        if n - i > Array.length holes_profile then CErrors.anomaly Pp.(str "Malformed right-hand-side substitution site");
        let d = holes_profile.(n-i-1) in
        if d = 0 then () else CErrors.anomaly Pp.(str "Malformed right-hand-side substitution site")
    | _ -> Constr.iter_with_binders succ check i c
  in
  check 0 rhs

let check_rewrite_rule env lab i (symb, rule) =
  Flags.if_verbose Feedback.msg_notice (str "  checking rule:" ++ Id.print lab ++ str"#" ++ Pp.int i);
  let { nvars; lhs_pat; rhs } = rule in
  let symb_cb = Environ.lookup_constant symb env in
  let () =
    match symb_cb.const_body with Symbol _ -> ()
    | _ -> ignore @@ invalid_arg "Rule defined on non-symbol"
  in
  let lincheck = Partial_subst.make nvars in
  let lincheck = check_instance_mask env symb_cb.const_universes (fst lhs_pat) lincheck in
  let lincheck = get_holes_profiles env 0 0 lincheck (snd lhs_pat) in
  let holes_profile, _, _ = Partial_subst.to_arrays lincheck in
  let () = check_rhs env holes_profile rhs in
  ()

let check_rewrite_rules_body env lab rrb =
  List.iteri (check_rewrite_rule env lab) rrb.rewrules_rules

(** {6 Checking modules } *)

(** We currently ignore the [mod_type_alg] and [typ_expr_alg] fields.
    The only delicate part is when [mod_expr] is an algebraic expression :
    we need to expand it before checking it is indeed a subtype of [mod_type].
    Fortunately, [mod_expr] cannot contain any [MEwith]. *)

let lookup_module mp env =
  try Environ.lookup_module mp env
  with Not_found ->
    failwith ("Unknown module: "^ModPath.to_string mp)

let mk_mtb sign delta = Mod_declarations.make_module_type sign delta

let rec collect_constants_without_body sign mp accu =
  let collect_field s lab = function
  | SFBconst cb ->
     let c = Constant.make2 mp lab in
     if Declareops.constant_has_body cb then s else Cset.add c s
  | SFBmodule msb -> collect_constants_without_body (mod_type msb) (MPdot(mp,lab)) s
  | SFBmind _ | SFBrules _ | SFBmodtype _ -> s in
  match sign with
  | MoreFunctor _ -> Cset.empty  (* currently ignored *)
  | NoFunctor struc ->
     List.fold_left (fun s (lab,mb) -> collect_field s lab mb) accu struc

let rec check_mexpr env opac mse mp_mse res = match mse with
  | MEident mp ->
    let mb = lookup_module mp env in
    let mb = Modops.strengthen_and_subst_module_body mp mb mp_mse false in
    mod_type mb, mod_delta mb
  | MEapply (f,mp) ->
    let sign, delta = check_mexpr env opac f mp_mse res in
    let farg_id, farg_b, fbody_b = Modops.destr_functor sign in
    let state = (Environ.universes env, Conversion.checked_universes) in
    let _ : UGraph.t = Subtyping.check_subtypes state env mp (MPbound farg_id) farg_b in
    let mp_delta =
      let mb = lookup_module mp env in
      match mod_type mb with
      | NoFunctor _ -> mod_delta mb
      | MoreFunctor _ -> Mod_subst.empty_delta_resolver mp
    in
    let subst = Mod_subst.map_mbid farg_id mp mp_delta in
    Modops.subst_signature subst mp_mse fbody_b, Mod_subst.subst_codom_delta_resolver subst delta
  | MEwith _ -> CErrors.user_err Pp.(str "Unsupported 'with' constraint in module implementation")

let rec check_mexpression env opac sign mbtyp mp_mse res = match sign with
  | MEMoreFunctor body ->
    let arg_id, mtb, mbtyp = Modops.destr_functor mbtyp in
    let env' = Modops.add_module_parameter arg_id mtb env in
    let body, delta = check_mexpression env' opac body mbtyp mp_mse res in
    MoreFunctor(arg_id,mtb,body), delta
  | MENoFunctor me -> check_mexpr env opac me mp_mse res

(* A module's own body is the structure in which coqc declares its fields:
   its signature if it is a [FullStruct], as the library is, its
   implementation if it is a [Struct], and none if it is [Algebraic] or
   [Abstract]. A sealed module's signature, the type of an algebraic module
   and a module type only describe fields that an own body declares, the
   implementation of the sealed module for instance, possibly as a
   definition. [check_module] checks the registrations of a module's fields
   in its own body, and in the own bodies of the modules there ([own]).

   Whether [c], user and canonical name alike, is the name that
   [check_module] gives a constant of the own body of the module [mb] at
   [mp], or of the own body of a module there. *)
let rec module_declares c mp mb =
  match Mod_declarations.mod_expr mb with
  | FullStruct -> sign_declares c mp (mod_delta mb) (mod_type mb)
  | Struct (reso, struc) -> struc_declares c mp reso struc
  | Algebraic _ | Abstract -> false

and sign_declares c mp delta = function
  | MoreFunctor (_, _, body) -> sign_declares c mp delta body
  | NoFunctor struc -> struc_declares c mp delta struc

and struc_declares c mp delta struc =
  let field_declares (lab, field) = match field with
    | SFBconst _ ->
      let kn = Mod_subst.constant_of_delta_kn delta (KerName.make mp lab) in
      Constant.UserOrd.equal kn c && Constant.CanOrd.equal kn c
    | SFBmodule mb -> module_declares c (MPdot (mp, lab)) mb
    | SFBmind _ | SFBrules _ | SFBmodtype _ -> false
  in
  List.exists field_declares struc

(* coqc records the registration of a primitive type in the module or
   library whose [Primitive] declares the constant, and in those around it.
   [check_registered_type] checks a registered constant where the own body
   of the module declares it; one that it does not declare, a definition of
   another library, or a field of a sealed module's signature that its
   implementation defines, would not be checked, and every literal typed
   with it would trust it. A module that is not in an own body ([own] is
   false: in a signature, the type of an algebraic module or a module type)
   declares nothing, and coqc gives it no registration. Its registrations
   would still be applied when the library is loaded
   ([Modops.add_module]). A library's registrations are in the environment
   before this runs ([Safe_checking.env_of_library]), but none of its
   constants has been checked yet. *)
let check_registrations_declared ~own mp mb =
  let check = function
    | Retroknowledge.Register_ind _ -> ()
    | Retroknowledge.Register_type (prm, c) ->
      if not (own && module_declares c mp mb) then
        let canonical = Constant.canonical c in
        let canonical =
          if KerName.equal (Constant.user c) canonical then mt ()
          else str "(canonical name " ++ KerName.print canonical ++ str ")" ++ spc ()
        in
        raise (BadConstant (c, canonical ++ str "is registered as the primitive type " ++
                               pr_prim_type prm ++ str " in " ++ ModPath.print mp ++
                               str ", which does not declare it."))
  in
  List.iter check (mod_retroknowledge mb)

(* [own]: whether [mb] is in an own body (see [module_declares]); its
   signature is an own body if, besides, it is a [FullStruct], and its
   implementation if it is a [Struct]. *)
let rec check_module env opac mp mb opacify ~own =
  Flags.if_verbose Feedback.msg_notice (str "  checking module: " ++ str (ModPath.to_string mp));
  let () = check_registrations_declared ~own mp mb in
  let env = Modops.add_retroknowledge (mod_retroknowledge mb) env in
  let delta_mb = mod_delta mb in
  let opac =
    let own = own && match Mod_declarations.mod_expr mb with
      | FullStruct -> true
      | Struct _ | Algebraic _ | Abstract -> false
    in
    check_signature env opac (mod_type mb) mp delta_mb opacify ~own
  in
  let optsign, opac = match Mod_declarations.mod_expr mb with
    | Struct (reso, sign_struct) ->
      let opacify = collect_constants_without_body (mod_type mb) mp opacify in
      (* TODO: a bit wasteful, we recheck the types of parameters twice *)
      let sign_struct = Modops.annotate_struct_body sign_struct (mod_type mb) in
      (* The implementation is checked in its own right, hence its bytecode is
         compiled too; it is local to this check and never exported. *)
      let vmtab, sign_struct =
        compile_signature env (Environ.vm_library env) mp reso sign_struct in
      let env = Environ.set_vm_library vmtab env in
      let opac = check_signature env opac sign_struct mp reso opacify ~own in
      Some (sign_struct, reso), opac
    | Algebraic me -> Some (check_mexpression env opac me (mod_type mb) mp delta_mb), opac
    | Abstract|FullStruct -> None, opac
  in
  let () = match optsign with
  | None -> ()
  | Some (sign,delta) ->
    let mtb1 = mk_mtb sign delta
    and mtb2 = mk_mtb (mod_type mb) delta_mb in
    let state = (Environ.universes env, Conversion.checked_universes) in
    let env = Modops.add_module mp (module_body_of_type mtb1) env in
    let _ : UGraph.t = Subtyping.check_subtypes state env mp mp mtb2 in
    ()
  in
  opac

and check_module_type env mp mty =
  Flags.if_verbose Feedback.msg_notice (str "  checking module type: " ++ str (ModPath.to_string @@ mp));
  let _ : _ Cmap.t =
    check_signature env Cmap.empty (mod_type mty) mp (mod_delta mty) Cset.empty ~own:false in
  ()

and check_structure_field env opac mp lab res opacify ~own = function
  | SFBconst cb ->
      let kn = KerName.make mp lab in
      let kn = Mod_subst.constant_of_delta_kn res kn in
      let () = Check_stat.record_constant kn cb in
      check_constant_declaration env opac kn cb (Cset.mem kn opacify) ~own
  | SFBmind mib ->
      let kn = KerName.make mp lab in
      let kn = Mod_subst.mind_of_delta_kn res kn in
      let () =
        let indices_matter = (Environ.typing_flags env).indices_matter in
        Check_stat.record_inductive ~indices_matter kn mib
      in
      CheckInductive.check_inductive env kn mib, opac
  | SFBmodule msb ->
      let mp = MPdot(mp, lab) in
      let opac = check_module env opac mp msb opacify ~own in
      Modops.add_module mp msb env, opac
  | SFBmodtype mty ->
      let mp = MPdot (mp, lab) in
      let () = check_module_type env mp mty in
      add_modtype mp mty env, opac
  | SFBrules rrb ->
      check_rewrite_rules_body env lab rrb;
      Environ.add_rewrite_rules rrb.rewrules_rules env, opac

and check_signature env opac sign mp_mse res opacify ~own = match sign with
  | MoreFunctor (arg_id, mtb, body) ->
      let () = check_module_type env (MPbound arg_id) mtb in
      let env' = Modops.add_module_parameter arg_id mtb env in
      let opac = check_signature env' opac body mp_mse res Cset.empty ~own in
      opac
  | NoFunctor struc ->
      let (_:env), opac = List.fold_left (fun (env, opac) (lab,mb) ->
        check_structure_field env opac mp_mse lab res opacify ~own mb) (env, opac) struc
      in
      opac

let check_module env opac mp mb =
  NewProfile.profile "check_module"
    ~args:(fun () -> [("name", `String (ModPath.to_string mp))])
    (fun () -> check_module env opac mp mb Cset.empty ~own:true)
    ()
