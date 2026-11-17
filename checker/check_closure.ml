(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The statement report of [rocqchk -statement-report FILE]: for each
    request, whether a constant has the type of another one, and the axioms
    and relaxed typing flags the first one rests on.

    The closure follows what [Print Assumptions] walks (vernac/assumptions.ml,
    which the checker cannot link): the body and the type of a constant, the
    parameters, arities and constructor types of an inductive block, and, for
    a constant that a module signature leaves without a body, the body that the
    module's implementation gives it. The implementation is read from the
    environment, which keeps the implementation of every module it holds, so
    an object that only the implementation declares is found too, whether its
    library was checked, loaded with -norec, or admitted. *)

open Util
open Names
open Declarations
open Mod_declarations

(** {6 Requests} *)

type request = {
  req_name : string;
  req_model : string;
  req_trusted : string option;
}

let usage_error file lineno =
  CErrors.user_err
    Pp.(str "-statement-report: line " ++ int lineno ++ str " of " ++ str file ++
        str " is not `<name> <model-constant> [<trusted-constant>|-]`.")

(* Tokens are separated by single spaces: two spaces in a row make an empty
   token, which is refused, so no token can contain a space. *)
let parse_line file lineno line =
  let tokens = String.split_on_char ' ' line in
  if List.exists (fun t -> String.equal t "") tokens then usage_error file lineno;
  match tokens with
  | [name; model] | [name; model; "-"] ->
    { req_name = name; req_model = model; req_trusted = None }
  | [name; model; trusted] ->
    { req_name = name; req_model = model; req_trusted = Some trusted }
  | _ -> usage_error file lineno

let read_requests file =
  let ch =
    try open_in file
    with Sys_error msg ->
      CErrors.user_err Pp.(str "-statement-report: cannot read " ++ str file ++ str ": " ++ str msg)
  in
  let rec loop lineno acc =
    match input_line ch with
    | exception End_of_file -> List.rev acc
    | line ->
      if String.exists (fun c -> c = '\t' || c = '\r') line then usage_error file lineno;
      if String.equal line "" || line.[0] = '#' then loop (lineno + 1) acc
      else loop (lineno + 1) (parse_line file lineno line :: acc)
  in
  Fun.protect ~finally:(fun () -> close_in_noerr ch) (fun () -> loop 1 [])

(** {6 Implementations hidden by module signatures}

    The report resolves a term in the declaration view that typed it. A public
    declaration uses its environment view; a bodyless public declaration falls
    back to its implementation and then follows that implementation's fields.
    This prevents an independent signature proof from replacing a proof
    witness that depends on a relaxed kernel check. *)

type view = Public | Implementation

type vref = view * GlobRef.t

type field_index = {
  constants : constant_body Id.Map.t;
  minds : mutual_inductive_body Id.Map.t;
  modules : module_body Id.Map.t;
}

let empty_field_index = {
  constants = Id.Map.empty;
  minds = Id.Map.empty;
  modules = Id.Map.empty;
}

let index_fields fields =
  let add_mind label mib index =
    let minds = Id.Map.add label mib index.minds in
    let minds = Array.fold_left (fun minds mip ->
        Id.Map.add mip.mind_typename mib minds) minds mib.mind_packets in
    { index with minds }
  in
  List.fold_left (fun index (label, field) -> match field with
      | SFBconst cb -> { index with constants = Id.Map.add label cb index.constants }
      | SFBmind mib -> add_mind label mib index
      | SFBmodule mb -> { index with modules = Id.Map.add label mb index.modules }
      | SFBmodtype _ | SFBrules _ -> index)
    empty_field_index fields

let find_module fields label = Id.Map.find_opt label fields.modules
let find_constant fields label = Id.Map.find_opt label fields.constants
let find_mind fields label = Id.Map.find_opt label fields.minds

(** {6 Records of checked opaque bodies}

    Prototype C7 (measurement only, never merged). The process that checks
    an opaque body records the objects that the walk below adds for that body
    ([opaque_body_refs]), with the constant and the library and index of its
    stored proof; the report takes them instead of reading and walking the
    body again ([recorded_refs]). *)

(* Keyed by user name, as the environment is. *)
module ConstTbl = Hashtbl.Make (struct
    type t = Constant.t
    let equal = Constant.UserOrd.equal
    let hash = Constant.UserOrd.hash
  end)

(* Two objects equal here have both names equal: one can stand for the other
   anywhere. *)
module RefTbl = Hashtbl.Make (struct
    type t = GlobRef.t
    let equal a b = GlobRef.UserOrd.equal a b && GlobRef.CanOrd.equal a b
    let hash = GlobRef.UserOrd.hash
  end)

type opaque_records = {
  bodies : (DirPath.t * int * GlobRef.t list option) list ConstTbl.t;
  (* for each constant, the library and index of each stored proof that a
     check recorded under its name, with the objects its body references, or
     [None] when two records of that proof disagree *)
  shared : GlobRef.t RefTbl.t;
  (* one copy of each object the records name *)
  mutable count : int;
  mutable files : int;
  mutable bytes : int;
  mutable read_s : float;
  (* how many records were read, from how many files of how many bytes, in
     how many seconds *)
}

type state = {
  env : Environ.env;
  access : Opaqueproof.opaque -> Opaqueproof.opaque_proofterm;
  records : opaque_records option;
  (* the recorded objects of checked opaque bodies, for the report only *)
  mutable fields : field_index ModPath.Map.t;
  (* the indexed fields of the implementation of each module looked up so far *)
  mutable public_nodes : node GlobRef.Map_env.t;
  mutable implementation_nodes : node GlobRef.Map_env.t;
  (* each object reached so far, keyed by its constant or by the first
     inductive of its block, in the declaration view that typed its use *)
  mutable gen : int;
  keys : Constr.t array;
  gens : int array;
  (* the cache of [seen] *)
}

and node = {
  refs : vref list;
  (* the objects the selected declaration mentions, with the view that
     typed each reference *)
  axiom : bool;
  (* no body: a constant without one, an opaque constant whose body cannot be
     read, or an object neither the environment nor an implementation
     resolves, which is reported rather than left out *)
  flags : (string * GlobRef.t) list;
  (* the relaxed typing conditions the selected object relies on,
     (kind, object); an inductive block's object is its first inductive *)
}


let rec fields_of_functor f subs mp0 args = function
  | NoFunctor a -> f subs mp0 args a
  | MoreFunctor (mbid, _, e) ->
    match args with
    | [] -> raise Not_found (* an unapplied functor has no fields *)
    | mpa :: args ->
      let subs =
        Mod_subst.join (Mod_subst.map_mbid mbid mpa (Mod_subst.empty_delta_resolver mpa)) subs in
      fields_of_functor f subs mp0 args e

(* As in vernac/assumptions.ml (#22533): a module whose parent's
   implementation cannot be read is taken from the environment, which holds
   its signature. *)
let rec lookup_module_in_impl st mp = match mp with
  | MPfile _ | MPbound _ -> Environ.lookup_module mp st.env
  | MPdot (mp', lab) ->
    match fields_of_mp st mp' with
    | fields ->
      (match find_module fields lab with
       | Some mb -> mb
       | None -> Environ.lookup_module mp st.env)
    | exception Not_found -> Environ.lookup_module mp st.env

and fields_of_mp st mp =
  match ModPath.Map.find_opt mp st.fields with
  | Some fields -> fields
  | None ->
    let mb = lookup_module_in_impl st mp in
    let raw_fields, inner_mp, subs = fields_of_mb st Mod_subst.empty_subst mp mb [] in
    let fields =
      match mod_expr mb, ModPath.equal inner_mp mp with
      | (Algebraic _, false) ->
        let mp_from = inner_mp in
        let source = lookup_module_in_impl st mp_from in
        let alias = Modops.strengthen_and_subst_module_body mp_from source mp false in
        let fields, inner_mp, subs =
          fields_of_signature Mod_subst.empty_subst mp [] (mod_type alias) in
        let subs =
          if ModPath.equal inner_mp mp then subs
          else Mod_subst.add_mp inner_mp mp (Mod_subst.empty_delta_resolver mp) subs
        in
        Modops.subst_structure subs mp fields
      | _ ->
        let subs =
          if ModPath.equal inner_mp mp then subs
          else if Mod_subst.has_root_delta_resolver mp (mod_delta mb) then
            Mod_subst.add_mp inner_mp mp (mod_delta mb) subs
          else Mod_subst.add_mp inner_mp mp (Mod_subst.empty_delta_resolver mp) subs
        in
        Modops.subst_structure subs mp raw_fields
    in
    let fields = index_fields fields in
    st.fields <- ModPath.Map.add mp fields st.fields;
    fields

and fields_of_mb st subs mp mb args = match mod_expr mb with
  | Algebraic me ->
    fields_of_functor (fields_of_expr st) subs mp args
      (Modops.annotate_module_expression me (mod_type mb))
  | Struct (_, struc) ->
    fields_of_signature subs mp args (Modops.annotate_struct_body struc (mod_type mb))
  | Abstract | FullStruct -> fields_of_signature subs mp args (mod_type mb)

and fields_of_signature subs mp args sign =
  fields_of_functor (fun subs mp0 args struc ->
      if not (List.is_empty args) then raise Not_found;
      (struc, mp0, subs))
    subs mp args sign

and fields_of_expr st subs mp0 args = function
  | MEident mp ->
    let mp = Mod_subst.subst_mp subs mp in
    fields_of_mb st subs mp (lookup_module_in_impl st mp) args
  | MEapply (me, mp) -> fields_of_expr st subs mp0 (mp :: args) me
  | MEwith _ -> raise Not_found (* no 'with' in an implementation *)

let in_impl st get kn =
  let mp, lab = KerName.repr kn in
  match fields_of_mp st mp with
  | fields -> get fields lab
  | exception Not_found -> None

(* A public term uses its final-environment declaration. When that declaration
   has no body, its proof witness is the implementation. A term already
   reached from an implementation keeps that implementation view. The user
   name, not its canonical target, selects a transparent Include alias. *)
let lookup_constant st view kn =
  let impl () = in_impl st find_constant (Constant.user kn) in
  match view with
  | Public ->
    if Environ.mem_constant kn st.env then
      let cb = Environ.lookup_constant kn st.env in
      if Declareops.constant_has_body cb then Some (Public, cb)
      else match impl () with
        | Some cb -> Some (Implementation, cb)
        | None -> Some (Public, cb)
    else Option.map (fun cb -> (Implementation, cb)) (impl ())
  | Implementation ->
    match impl () with
    | Some cb -> Some (Implementation, cb)
    | None ->
      if Environ.mem_constant kn st.env then Some (Public, Environ.lookup_constant kn st.env)
      else None

let lookup_mind st view mind =
  let impl () = in_impl st find_mind (MutInd.user mind) in
  match view with
  | Public ->
    if Environ.mem_mind mind st.env then Some (Public, Environ.lookup_mind mind st.env)
    else Option.map (fun mib -> (Implementation, mib)) (impl ())
  | Implementation ->
    match impl () with
    | Some mib -> Some (Implementation, mib)
    | None ->
      if Environ.mem_mind mind st.env then Some (Public, Environ.lookup_mind mind st.env)
      else None

(** {6 The objects a declaration mentions} *)

(* A term is a graph with shared nodes: [seen] skips a node already walked in
   the same declaration, as vernac/assumptions.ml does, with a cache of the
   same size. The cache is lossy and direct-mapped: a miss only walks the node
   again. *)
(* Prototype (measurement only, never merged): ROCQCHK_REPORT_CACHE_BITS
   sets the cache to 2^bits entries; unset, 2^18 as at the base. *)
let cache_size =
  match Option.bind (Sys.getenv_opt "ROCQCHK_REPORT_CACHE_BITS") int_of_string_opt with
  | Some b when b >= 10 && b <= 26 -> 1 lsl b
  | Some _ | None -> 1 lsl 18

let fresh_gen st = st.gen <- st.gen + 1; st.gen

let seen st gen c =
  let i = Constr.hash_bounded c land (cache_size - 1) in
  if Int.equal st.gens.(i) gen && st.keys.(i) == c then true
  else begin
    st.gens.(i) <- gen;
    st.keys.(i) <- c;
    false
  end

let empty_refs = GlobRef.Set_env.empty, GlobRef.Set_env.empty

let add_ref view obj (public, implementation) = match view with
  | Public -> GlobRef.Set_env.add obj public, implementation
  | Implementation -> public, GlobRef.Set_env.add obj implementation

let add_mind view mind refs = add_ref view (GlobRef.IndRef (mind, 0)) refs

(* The primitive type a literal has, which the kernel looks up to type it. *)
let add_prim view prim refs = match prim with
  | Some c -> add_ref view (GlobRef.ConstRef c) refs
  | None -> refs

let refs_to_list (public, implementation) =
  List.map (fun obj -> Public, obj) (GlobRef.Set_env.elements public)
  @ List.map (fun obj -> Implementation, obj) (GlobRef.Set_env.elements implementation)

(* The walk keeps its own list of terms to visit, so its depth does not depend
   on the depth of the terms. A term retains the declaration view that typed
   it. The inductive of a [match] and of a projection, and the primitive type
   of a literal or an array, are objects the term relies on even though no
   subterm names them. *)
let rec walk st gen refs = function
  | [] -> refs
  | (view, c) :: todo ->
    let open Constr in
    let retro = Environ.retroknowledge st.env in
    match kind c with
    | Rel _ | Var _ | Sort _ | Meta _ | Evar _ -> walk st gen refs todo
    | Int _ -> walk st gen (add_prim view retro.Retroknowledge.retro_int63 refs) todo
    | Float _ -> walk st gen (add_prim view retro.Retroknowledge.retro_float64 refs) todo
    | String _ -> walk st gen (add_prim view retro.Retroknowledge.retro_string refs) todo
    | Const (kn, _) -> walk st gen (add_ref view (GlobRef.ConstRef kn) refs) todo
    | Ind ((mind, _), _) | Construct (((mind, _), _), _) ->
      walk st gen (add_mind view mind refs) todo
    | Cast _ | Prod _ | Lambda _ | LetIn _ | App _ | Proj _ | Case _ | Fix _ | CoFix _ | Array _ ->
      if seen st gen c then walk st gen refs todo
      else
        let refs = match kind c with
          | Case (ci, _, _, _, _, _, _) -> add_mind view (fst ci.ci_ind) refs
          | Proj (p, _, _) -> add_mind view (Projection.mind p) refs
          | Array _ -> add_prim view retro.Retroknowledge.retro_array refs
          | _ -> refs
        in
        walk st gen refs (fold (fun todo c -> (view, c) :: todo) todo c)

(* Prototype C7: the objects [walk] adds for the term [c] alone, in one view,
   with the primitive types that [env] registers. A walk that starts from a
   declaration's type and its body [c] adds the objects of the type and, in
   the declaration's view, exactly these: [seen] only skips a node already
   walked, whose objects are added already. The cache of these walks is the
   process's own, made at the first call; each call takes a new generation
   of it, before it walks, so that no call can see another's entries. *)
let body_walk_cache =
  lazy (Array.make cache_size Constr.mkProp, Array.make cache_size (-1), ref 0)

let opaque_body_refs env c =
  let keys, gens, gen = Lazy.force body_walk_cache in
  incr gen;
  let st = {
    env; access = (fun _ -> CErrors.anomaly (Pp.str "opaque_body_refs reads no body."));
    records = None; fields = ModPath.Map.empty;
    public_nodes = GlobRef.Map_env.empty; implementation_nodes = GlobRef.Map_env.empty;
    gen = !gen; keys; gens;
  } in
  let public, _ = walk st !gen empty_refs [Public, c] in
  GlobRef.Set_env.elements public

let push_context view ctx todo =
  List.fold_left (fun todo d ->
      Context.Rel.Declaration.fold_constr (fun c todo -> (view, c) :: todo) d todo)
    todo ctx

let typing_flags obj (tf : typing_flags) acc =
  let add ok kind acc = if ok then acc else (kind, obj) :: acc in
  acc
  |> add tf.check_universes "type-in-type"
  |> add tf.check_guarded "unsafe-fixpoint"
  |> add tf.check_eliminations "unchecked-eliminations"

(* The same test as vernac/assumptions.ml's [uses_uip]. *)
let uses_uip mib =
  Array.exists (fun mip ->
      Option.is_empty mip.mind_squashed
      && (match mip.mind_relevance with Sorts.Irrelevant -> true | _ -> false)
      && Int.equal (Array.length mip.mind_nf_lc) 1
      && Int.equal (List.length (fst mip.mind_nf_lc.(0))) (List.length mib.mind_params_ctxt))
    mib.mind_packets

let unresolved = { refs = []; axiom = true; flags = [] }

(* Test-only seam, beside [test_fault] below: a test sets this to make the
   opaque accessor fail for one constant, so the unreadable-body warning has a
   test without a damaged .vo. The real failures it stands for — a proof stored
   nowhere, and a lazy reader refusing a table whose bytes changed since intern
   — are not reachable from this test suite's own objects. *)
let test_unreadable_opaque kn =
  match Sys.getenv_opt "COQ_TEST_SUITE_STATEMENT_REPORT_UNREADABLE" with
  | Some c when String.equal c (Constant.to_string kn) ->
    CErrors.user_err Pp.(str "test unreadable opaque body")
  | None | Some _ -> ()

(* Prototype I (measurement only, never merged): with ROCQCHK_REPORT_STATS
   set, the time spent reading and walking each constant's body, by the root
   of its library, is written to that file when the report ends. *)
let report_stats : (string, float array) Hashtbl.t = Hashtbl.create 17

let stats_on = Option.has_some (Sys.getenv_opt "ROCQCHK_REPORT_STATS")

let rec file_of_mp = function
  | MPfile dp -> Some dp
  | MPdot (mp, _) -> file_of_mp mp
  | MPbound _ -> None

let root_of kn = match file_of_mp (Constant.modpath kn) with
  | Some dp -> (match List.rev (DirPath.repr dp) with id :: _ -> Id.to_string id | [] -> "")
  | None -> "<bound>"

(* n_opaque, t_access, t_walk_opaque, n_other, t_walk_other *)
let add_stats kn opaque t_access t_walk =
  let r = root_of kn in
  let a = match Hashtbl.find_opt report_stats r with
    | Some a -> a
    | None -> let a = Array.make 5 0. in Hashtbl.add report_stats r a; a in
  if opaque then begin
    a.(0) <- a.(0) +. 1.; a.(1) <- a.(1) +. t_access; a.(2) <- a.(2) +. t_walk end
  else begin a.(3) <- a.(3) +. 1.; a.(4) <- a.(4) +. t_walk end

(* Prototype C7: the opaque constants the report reached whose objects it
   took from a record, and those whose body it read. *)
let record_hits = ref 0
let record_misses = ref 0

let write_stats records =
  match Sys.getenv_opt "ROCQCHK_REPORT_STATS" with
  | None -> ()
  | Some f ->
    (try
       let oc = open_out f in
       Hashtbl.iter (fun r a ->
           Printf.fprintf oc "%s %.0f %.3f %.3f %.0f %.3f\n" r a.(0) a.(1) a.(2) a.(3) a.(4))
         report_stats;
       let files, bytes, n, read_s = match records with
         | Some r -> r.files, r.bytes, r.count, r.read_s
         | None -> 0, 0, 0, 0.
       in
       Printf.fprintf oc "RECORDS hits %d misses %d files %d bytes %d records %d read_s %.3f\n"
         !record_hits !record_misses files bytes n read_s;
       close_out oc
     with Sys_error _ -> ())

let opaque_records () = {
  bodies = ConstTbl.create 4096; shared = RefTbl.create 4096;
  count = 0; files = 0; bytes = 0; read_s = 0.;
}

(* A proof that one constant names twice, in a module's signature and in its
   implementation, is recorded twice; the records then name the same objects.
   If they do not, they are not two checks of one body, and neither is used:
   the report reads that body. Each object is kept once, so that the records
   of a large tree take one copy of each name they share. *)
let add_opaque_record r kn dp i objs =
  r.count <- r.count + 1;
  let share obj = match RefTbl.find_opt r.shared obj with
    | Some obj -> obj
    | None -> RefTbl.add r.shared obj obj; obj
  in
  let objs = List.map share objs in
  let same (dp', i', _) = Int.equal i i' && DirPath.equal dp dp' in
  let bodies = Option.default [] (ConstTbl.find_opt r.bodies kn) in
  let bodies = match List.find_opt same bodies with
    | None -> (dp, i, Some objs) :: bodies
    | Some (_, _, Some objs') when List.equal (==) objs objs' -> bodies
    | Some _ -> (dp, i, None) :: List.filter (fun b -> not (same b)) bodies
  in
  ConstTbl.replace r.bodies kn bodies

let note_opaque_records_read r ~files ~bytes ~seconds =
  r.files <- files;
  r.bytes <- bytes;
  r.read_s <- seconds

(* Prototype C7: the objects that a check recorded for the opaque body [o] of
   [kn], when the body it checked is the one [st.access o] would read. [o]
   has no substitution, so its body is its stored proof as its cooking
   information cooks it ([CheckLibrary.indirect_accessor]), and the record
   names the same stored proof, by library and index, under the same
   constant. The stored proof is the library's file as the main process
   hashed it, which every process that reads it checks. The cooking
   information is not compared: a stored proof gets its cooking information
   when its section closes, before any module can hold it, and a module that
   copies it substitutes it. Two records of one proof under one constant that
   disagree are not used ([add_opaque_record]). *)
let recorded_refs st kn o =
  match st.records with
  | None -> None
  | Some r ->
    let (sub, _, dp, i) = Opaqueproof.repr o in
    if not (List.is_empty sub) then None
    else
      let i = Opaqueproof.repr_handle i in
      match ConstTbl.find_opt r.bodies kn with
      | None -> None
      | Some bodies ->
        match List.find_opt (fun (dp', i', _) -> Int.equal i i' && DirPath.equal dp dp') bodies with
        | Some (_, _, objs) -> objs
        | None -> None

let constant_node st view kn =
  match lookup_constant st view kn with
  | None -> unresolved
  | Some (declaration_view, cb) ->
    (* An opaque body that cannot be read is reported as an axiom, as
       vernac/assumptions.ml's [get_constant_body] does: a constant whose body
       this process cannot see rests on something it cannot check. The read can
       fail for two unrelated reasons, though — the proof was not stored, which
       is what upstream means, or the table could not be READ (damaged bytes, or
       a lazy reader refusing a table whose bytes changed since intern) — and
       the verdict alone does not tell them apart. So the failure is named here.
       The exit status is deliberately unchanged: a stored-nowhere body is an
       ordinary answer, and failing the whole check on it would turn every
       delayed proof into a failed grade. A reader who needs certainty reads the
       warning, which names the constant. *)
    let t0 = if stats_on then Unix.gettimeofday () else 0. in
    let opaque = match cb.const_body with OpaqueDef _ -> true | _ -> false in
    let body, recorded, axiom = match cb.const_body with
      | Def c -> [declaration_view, c], None, false
      | OpaqueDef o ->
        (* Prototype C7: a body that a check recorded is not read; the walk
           of the type alone, and the recorded objects in the declaration's
           view, make the same references as the walk of the type and the
           body. *)
        let read () = match recorded_refs st kn o with
          | Some _ as recorded -> [], recorded
          | None -> let c, _ = st.access o in [declaration_view, c], None
        in
        (match (test_unreadable_opaque kn; read ()) with
         | body, recorded -> body, recorded, false
         | exception e when CErrors.noncritical e ->
           Feedback.msg_warning
             Pp.(str "Statement report: the opaque body of " ++ str (Constant.to_string kn)
                 ++ str " could not be read, so it is reported as an axiom: " ++ CErrors.print e);
           [], None, true)
      | Undef _ | Primitive _ | Symbol _ -> [], None, true
    in
    if opaque then incr (if Option.has_some recorded then record_hits else record_misses);
    let t1 = if stats_on then Unix.gettimeofday () else 0. in
    let refs = walk st (fresh_gen st) empty_refs ((declaration_view, cb.const_type) :: body) in
    let refs = match recorded with
      | None -> refs
      | Some objs -> List.fold_left (fun refs obj -> add_ref declaration_view obj refs) refs objs
    in
    if stats_on then add_stats kn opaque (t1 -. t0) (Unix.gettimeofday () -. t1);
    { refs = refs_to_list refs; axiom;
      flags = typing_flags (GlobRef.ConstRef kn) cb.const_typing_flags [] }

let mind_node st view mind =
  match lookup_mind st view mind with
  | None -> unresolved
  | Some (declaration_view, mib) ->
    let todo =
      Array.fold_left (fun todo mip ->
          push_context declaration_view mip.mind_arity_ctxt
            (Array.fold_left (fun todo c -> (declaration_view, c) :: todo) todo mip.mind_user_lc))
        (push_context declaration_view mib.mind_params_ctxt []) mib.mind_packets
    in
    let refs = walk st (fresh_gen st) empty_refs todo in
    Array.iter (fun mip ->
        if not (CheckNames.valid_id mip.mind_typename) then
          CErrors.user_err
            Pp.(str ("The statement report reached the inductive type name " ^
                     CheckNames.quote (Id.to_string mip.mind_typename) ^
                     ", which is not an identifier.")))
      mib.mind_packets;
    let name = GlobRef.IndRef (mind, 0) in
    let tf = mib.mind_typing_flags in
    let flags = typing_flags name tf [] in
    let add cond kind flags = if cond then (kind, name) :: flags else flags in
    let flags =
      flags
      |> add (not tf.check_positive) "assumed-positive"
      |> add (uses_uip mib) "uip"
      |> add (not tf.indices_matter
              && Array.exists (fun mip -> mip.mind_relies_on_indices_not_mattering) mib.mind_packets)
        "indices-not-mattering"
    in
    { refs = refs_to_list refs; axiom = false; flags }

let node st view obj =
  let nodes = match view with
    | Public -> st.public_nodes
    | Implementation -> st.implementation_nodes
  in
  match GlobRef.Map_env.find_opt obj nodes with
  | Some n -> n
  | None ->
    let n = match obj with
      | GlobRef.ConstRef kn -> constant_node st view kn
      | GlobRef.IndRef (mind, _) | GlobRef.ConstructRef ((mind, _), _) -> mind_node st view mind
      | GlobRef.VarRef _ -> { refs = []; axiom = false; flags = [] }
    in
    begin match view with
    | Public -> st.public_nodes <- GlobRef.Map_env.add obj n st.public_nodes
    | Implementation -> st.implementation_nodes <- GlobRef.Map_env.add obj n st.implementation_nodes
    end;
    n

let name_of = function
  | GlobRef.ConstRef kn -> Constant.to_string kn
  | GlobRef.IndRef (mind, _) | GlobRef.ConstructRef ((mind, _), _) -> MutInd.to_string mind
  | GlobRef.VarRef id -> Id.to_string id

(* Place 2 of the name check (checkNames.mli), for a name that the check at
   load cannot see: a constant or an inductive that a term of an admitted
   library names and that no library declares, which the report prints as an
   axiom. Each object whose name an [axiom] or [flag] line would print is
   tested when the closure reaches it, as are the type names of each inductive
   block it resolves ([mind_node]). This is before the type verdict, whose
   conversion can reach an anomaly that prints an unresolved inductive's name,
   and before the statement's line, so a refusal leaves no END STATEMENT
   REPORT line. *)
let check_printed_name obj =
  let valid = match obj with
    | GlobRef.ConstRef kn -> CheckNames.valid_kername (Constant.user kn)
    | GlobRef.IndRef (mind, _) | GlobRef.ConstructRef ((mind, _), _) ->
      CheckNames.valid_kername (MutInd.user mind)
    | GlobRef.VarRef id -> CheckNames.valid_id id
  in
  if not valid then
    CErrors.user_err
      Pp.(str ("The statement report would print the name " ^ CheckNames.quote (name_of obj) ^
               ", which is not made of identifiers."))

module FlagSet = Stdlib.Set.Make (struct
    type t = string * GlobRef.t
    let compare (k1, o1) (k2, o2) =
      let c = String.compare k1 k2 in
      if Int.equal c 0 then GlobRef.UserOrd.compare o1 o2 else c
  end)

(** The axioms and flags of every object reachable from [root]. The axioms
    are the objects themselves, not their printed names: two objects can
    print the same name (a constant [Q.g] of a module [Q] of the library
    [R.P] prints as the constant [g] of the library [R.P.Q]), and the
    comparator must tell them apart. A name the report must not print stops
    the walk ([check_printed_name]). *)
let closure st root =
  let rec loop public_seen implementation_seen axioms flags = function
    | [] -> axioms, flags
    | (view, obj) :: todo ->
      let seen = match view with
        | Public -> GlobRef.Set_env.mem obj public_seen
        | Implementation -> GlobRef.Set_env.mem obj implementation_seen
      in
      if seen then loop public_seen implementation_seen axioms flags todo
      else
        let n = node st view obj in
        if n.axiom || not (List.is_empty n.flags) then check_printed_name obj;
        let axioms = if n.axiom then GlobRef.Set_env.add obj axioms else axioms in
        let flags = List.fold_left (fun flags f -> FlagSet.add f flags) flags n.flags in
        let public_seen, implementation_seen = match view with
          | Public -> GlobRef.Set_env.add obj public_seen, implementation_seen
          | Implementation -> public_seen, GlobRef.Set_env.add obj implementation_seen
        in
        loop public_seen implementation_seen axioms flags (List.rev_append n.refs todo)
  in
  loop GlobRef.Set_env.empty GlobRef.Set_env.empty GlobRef.Set_env.empty FlagSet.empty [Public, root]

(* The printed names of the axioms and flags, for the report's lines. They
   are not identities: two objects can print the same name and then make
   one line, so no grader may check these lines against a permitted list by
   name ([Check_closure.print]'s documentation). *)
let axiom_names axioms =
  GlobRef.Set_env.fold (fun obj acc -> CString.Set.add (name_of obj) acc) axioms CString.Set.empty

let flag_names flags =
  FlagSet.fold (fun (kind, obj) acc -> CString.Set.add (kind ^ " " ^ name_of obj) acc)
    flags CString.Set.empty

(** {6 The type match} *)

(* The universe comparison that checking [Definition f := model] against a
   monomorphic [Parameter f : <type>] of a sealing module type makes
   (vernac/declaremods.ml's [RawModOps.Interp.end_module_core], which runs
   [Mod_typing.finalize_module] with [Reductionops.inferred_universes] and
   adds the constraints it collects to the global graph before
   [Global.end_module] checks the module again): a comparison that does not
   hold yet adds the constraints it needs, if they are consistent with the
   environment. The state is the universe graph with those constraints; the
   error marks a needed constraint that is inconsistent. *)
let infer_universes : (UGraph.t, unit) Conversion.universe_compare =
  let merge csts g =
    match UGraph.merge_constraints csts g with
    | g -> Result.Ok g
    | exception UGraph.UniverseInconsistency _ -> Result.Error (Some ())
  in
  let leq u v g =
    match UGraph.enforce_leq_alg u v g with
    | _, g -> Result.Ok g
    | exception UGraph.UniverseInconsistency _ -> Result.Error (Some ())
  in
  let compare_sorts pb s1 s2 g =
    let holds = match pb with
      | Conversion.CUMUL -> UGraph.check_leq_sort Sorts.Quality.equal g s1 s2
      | Conversion.CONV -> UGraph.check_eq_sort Sorts.Quality.equal g s1 s2
    in
    if holds then Result.Ok g
    (* As pretyping/reductionops.ml's [Infer]: the qualities must already
       compare, and only the universe constraint is inferred. The checked
       comparison above has decided every case with an impredicative sort. *)
    else match s1, s2 with
      | (Sorts.SProp | Sorts.Prop), _ | _, (Sorts.SProp | Sorts.Prop) -> Result.Error None
      | _ when not (Sorts.Quality.equal (Sorts.quality s1) (Sorts.quality s2)) -> Result.Error None
      | _ ->
        let u1 = Sorts.univ_of_sort s1 and u2 = Sorts.univ_of_sort s2 in
        match pb with
        | Conversion.CUMUL -> leq u1 u2 g
        | Conversion.CONV ->
          (* As engine/univSubst.ml's [enforce_eq]: only two levels can be made equal. *)
          match Univ.Universe.level u1, Univ.Universe.level u2 with
          | Some _, Some _ -> Result.bind (leq u1 u2 g) (leq u2 u1)
          | _ -> Result.Error (Some ())
  in
  let compare_instances ~flex u1 u2 g =
    if UGraph.check_eq_instances Sorts.Quality.equal g u1 u2 then Result.Ok g
    else if flex then Result.Error None
    else
      let qcsts, ucsts = UVars.enforce_eq_instances u1 u2 UVars.empty_unif_constraints in
      if UVars.QUnifConstraints.is_trivial qcsts then merge ucsts g else Result.Error None
  in
  let compare_cumul_instances pb variances u1 u2 g =
    let qcsts, ucsts = Conversion.get_cumulativity_constraints pb variances u1 u2 in
    if UVars.QUnifConstraints.is_trivial qcsts then merge ucsts g else Result.Error None
  in
  { Conversion.compare_sorts; compare_instances; compare_cumul_instances }

(* Whether the model constant can stand for the trusted constant in a module
   sealed by a signature that declares the trusted type T: whether [Definition
   f := model] ([Polymorphic] when T is) is accepted for the field [Parameter f
   : T] (kernel/subtyping.ml's [check_constant]). The model's type must be
   cumulative to T. Against a monomorphic T, a needed universe constraint is
   added when it is consistent with the environment; against a polymorphic T,
   the definition's universe context must be T's and adds no constraint.
   Elaborating the definition takes a polymorphic model at fresh universes,
   and can minimize them when the model's universe context has sort variables
   or constraints; this check does not replay that, so it answers
   [universes-differ] for such a model, which the sealing may still accept. *)
let type_verdict env model trusted =
  let cm = Environ.lookup_constant model env and ct = Environ.lookup_constant trusted env in
  let infer env =
    let state = Environ.universes env, infer_universes in
    match Conversion.generic_conv Conversion.CUMUL ~l2r:false TransparentState.full env state
            cm.const_type ct.const_type with
    | Result.Ok _ -> "match"
    | Result.Error None -> "mismatch"
    | Result.Error (Some ()) -> "universes-differ"
  in
  (* The definition's context [am] must be T's context [at]; the types are
     compared under [at]. A failure that ignoring universe levels removes needs a
     constraint that [at] does not give. *)
  let against_polymorphic am at =
    if Subtyping.check_polymorphic_universes env at am then
      let env = Environ.push_context ~strict:false (UVars.AbstractContext.repr at) env in
      match Conversion.default_conv_leq env cm.const_type ct.const_type with
      | Result.Ok () -> "match"
      | Result.Error () ->
        match Conversion.default_conv_leq (Environ.set_type_in_type true env)
                cm.const_type ct.const_type with
        | Result.Ok () -> "universes-differ"
        | Result.Error () -> "mismatch"
    else "universes-differ"
  in
  let minimizable am =
    fst (UVars.AbstractContext.size am) > 0
    || not (PConstraints.is_empty (UVars.UContext.constraints (UVars.AbstractContext.repr am)))
  in
  match cm.const_universes, ct.const_universes with
  | Monomorphic, Monomorphic -> infer env
  | Monomorphic, Polymorphic at -> against_polymorphic UVars.AbstractContext.empty at
  | Polymorphic am, _ when minimizable am -> "universes-differ"
  | Polymorphic am, Monomorphic ->
    (* The model's bound universes are fresh in [env]: they are its instance. The
       definition declares them as global universes, which [Global.push_context_set]
       does with [~strict:true], so each is above [Set] and cannot be taken as it. *)
    infer (Environ.push_context ~strict:true (UVars.AbstractContext.repr am) env)
  | Polymorphic am, Polymorphic at -> against_polymorphic am at

(** {6 The report} *)

(* One message per line, so that a long report never builds one [Pp.t]. *)
let line fmt = Printf.ksprintf (fun s -> Feedback.msg_notice (Pp.str s)) fmt

(* Test-only seam: a test sets this for one process to exercise the public
   incomplete-report contract. It has no effect unless the test variable is
   explicitly set. *)
let test_fault () =
  match Sys.getenv_opt "COQ_TEST_SUITE_STATEMENT_REPORT_FAILURE" with
  | Some "1" -> CErrors.user_err Pp.(str "test statement-report failure")
  | None | Some _ -> ()

let print ?records env access requests =
  let pt0 = Unix.gettimeofday () in
  let total () =
    let a = Array.make 5 0. in
    a.(1) <- Unix.gettimeofday () -. pt0;
    Hashtbl.replace report_stats "<TOTAL-wall-in-[1]>" a in
  let index =
    Environ.fold_constants (fun c _ acc -> CString.Map.add (Constant.to_string c) c acc)
      env CString.Map.empty
  in
  let st = {
    env; access; records; fields = ModPath.Map.empty;
    public_nodes = GlobRef.Map_env.empty; implementation_nodes = GlobRef.Map_env.empty; gen = 0;
    keys = Array.make cache_size Constr.mkProp; gens = Array.make cache_size (-1);
  } in
  line "STATEMENT REPORT";
  test_fault ();

  List.iter (fun r ->
      let trusted = Option.default "-" r.req_trusted in
      match CString.Map.find_opt r.req_model index with
      | None -> line "statement %s %s %s model-missing 0 0" r.req_name r.req_model trusted
      | Some model ->
        let axioms, flags = closure st (GlobRef.ConstRef model) in
        let axioms = axiom_names axioms and flags = flag_names flags in
        let verdict = match r.req_trusted with
          | None -> "not-requested"
          | Some t ->
            match CString.Map.find_opt t index with
            | None -> "trusted-missing"
            | Some t -> type_verdict env model t
        in
        line "statement %s %s %s %s %d %d" r.req_name r.req_model trusted verdict
          (CString.Set.cardinal axioms) (CString.Set.cardinal flags);
        CString.Set.iter (line "axiom %s %s" r.req_name) axioms;
        CString.Set.iter (line "flag %s %s" r.req_name) flags)
    requests;
  line "END STATEMENT REPORT";
  if stats_on then total ();
  write_stats records

(** {6 The closure, for [rocqchk -compare]} *)

(* The comparator needs the axioms and flags of a constant, not the report's
   text, and it asks for several constants in one run, so the walk's caches
   are built once and kept. *)

type closure_state = state

let closure_state env access = {
  env; access; records = None; fields = ModPath.Map.empty;
  public_nodes = GlobRef.Map_env.empty; implementation_nodes = GlobRef.Map_env.empty; gen = 0;
  keys = Array.make cache_size Constr.mkProp; gens = Array.make cache_size (-1);
}

let axioms_and_flags st kn =
  let axioms, flags = closure st (GlobRef.ConstRef kn) in
  let axioms = List.map (fun obj -> name_of obj, obj) (GlobRef.Set_env.elements axioms) in
  let flags =
    List.map (fun (kind, obj) -> kind, name_of obj, obj) (FlagSet.elements flags)
    |> List.stable_sort (fun (k1, n1, _) (k2, n2, _) ->
        let c = String.compare k1 k2 in if Int.equal c 0 then String.compare n1 n2 else c)
  in
  List.stable_sort (fun (a, _) (b, _) -> String.compare a b) axioms, flags
