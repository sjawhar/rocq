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

(** {6 The cache of the walk} *)

(* A term is a graph with shared nodes: [seen] skips a node already walked in
   the same declaration, as vernac/assumptions.ml does, with a cache of the
   same size. The cache is lossy and direct-mapped: a miss only walks the node
   again. *)
let cache_size = 1 lsl 18

(* The slots of [objects] below. *)
let object_slots = 4096

(* What a slot of [objects] holds before the walk builds an object there. *)
let no_object = GlobRef.VarRef (Id.of_string "dummy")

(* The slots of the stack below that a cache starts with. *)
let stack_start = 1024

(* What [walk] keeps from one node to the next, in three parts that last
   differently: the table of [seen] ([keys] to [touched_count]), which
   each walk takes in a new generation; the stack of the terms to visit
   ([terms] to [peak]), which lasts one walk; and [objects], which lasts as
   long as the cache. One walk at a time on a cache, since its stack is the
   current walk's: an [add] must not walk. A walk that an [add] started on
   the same cache would empty the stack as it ended ([end_walk]), and the
   walk that called that [add] would lose the terms it had still to visit,
   and their objects, with no error. *)
type walk_cache = {
  keys : Constr.t array;
  (* the node last walked at each slot of [seen]: kept until a later walk
     writes the slot or, where [noting], until the walk that wrote it ends
     ([end_walk]) *)
  gens : int array;
  (* the generation that wrote each slot of [keys], kept until a later
     generation writes the slot *)
  mutable gen : int;
  (* the generation of the current walk, or of the last one: each walk takes
     a new one ([fresh_gen]), so that it sees no slot another walk wrote *)
  noting : bool;
  (* whether the cache notes in [touched] the slots each walk writes, for
     its whole life: only the cache of [opaque_body_refs] does *)
  touched : int array;
  (* where [noting], the slots of [keys] that the current walk wrote, each
     once, the first [touched_count]: the next walk writes over them *)
  mutable touched_count : int;
  (* the slots of [touched] that the current walk filled, from its start
     ([fresh_gen]) to the start of the next walk; always 0 where not
     [noting] *)
  mutable terms : Constr.t array;
  (* the stack of the terms the current walk has still to visit: the first
     [size], the last one on top ([push]); the array is kept from one walk
     to the next, doubled when full and never shrunk, so that [push]
     allocates only where the stack outgrows it *)
  mutable views : view array;
  (* the view that typed each term of [terms], at the same slot, kept the
     same way *)
  mutable size : int;
  (* the terms on the stack: 0 between two walks ([end_walk]) *)
  mutable peak : int;
  (* the first slots of [terms] that the current walk wrote, the only ones
     that can hold a term: [end_walk] empties them, and sets [peak] to 0 *)
  objects : GlobRef.t array;
  (* the object the walks built last at each slot ([const_ref], [ind_ref]),
     kept as long as the cache: nothing empties it *)
}

let walk_cache ~noting = {
  keys = Array.make cache_size Constr.mkProp;
  gens = Array.make cache_size (-1);
  gen = 0;
  noting;
  touched = (if noting then Array.make cache_size 0 else [||]);
  touched_count = 0;
  terms = Array.make stack_start Constr.mkProp;
  views = Array.make stack_start Public;
  size = 0;
  peak = 0;
  objects = Array.make object_slots no_object;
}

let fresh_gen cache =
  cache.gen <- cache.gen + 1;
  cache.touched_count <- 0;
  cache.gen

(* A slot is noted when the generation first writes it, so a generation
   notes at most [cache_size] of them. *)
let seen cache gen c =
  let i = Constr.hash_bounded c land (cache_size - 1) in
  let g = cache.gens.(i) in
  if Int.equal g gen && cache.keys.(i) == c then true
  else begin
    if cache.noting && not (Int.equal g gen) then begin
      cache.touched.(cache.touched_count) <- i;
      cache.touched_count <- cache.touched_count + 1
    end;
    cache.gens.(i) <- gen;
    cache.keys.(i) <- c;
    false
  end

(* Pushes the term [c], in the view [view], on the stack of terms to visit. *)
let push cache view c =
  let n = cache.size in
  if Int.equal n (Array.length cache.terms) then begin
    let terms = Array.make (2 * n) Constr.mkProp and views = Array.make (2 * n) Public in
    Array.blit cache.terms 0 terms 0 n;
    Array.blit cache.views 0 views 0 n;
    cache.terms <- terms;
    cache.views <- views
  end;
  cache.terms.(n) <- c;
  cache.views.(n) <- view;
  cache.size <- n + 1;
  if n >= cache.peak then cache.peak <- n + 1

let push_array cache view a =
  for i = 0 to Array.length a - 1 do push cache view a.(i) done

(* Pushes the subterms of a node that [walk] enters, from the first to the
   last in the order of [Constr.fold]. For a fixpoint that has not as many
   bodies as types, it raises, before it pushes any, the exception that
   [Constr.fold] raises there: [Invalid_argument "Array.fold_left2"], with
   the message of [CArray.fold_left2], which [Constr.fold] calls, copied: a
   change of that message must be made here too. [Constr.fold] itself is
   not used: it needs a closure that captures [view], made at each node, and
   its [Case] and [Fix] arms make closures of their own.
   [Constr.iter] is not used either: it takes the subterms of a fixpoint in
   another order, and makes a closure for each [match]. *)
let push_subterms cache view c =
  let open Constr in
  match kind c with
  (* the nodes [walk] does not enter, which have no subterms but [Evar]:
     [Constr.fold] folds an [Evar]'s instance, which [walk] never reaches *)
  | Rel _ | Var _ | Meta _ | Evar _ | Sort _ | Const _ | Ind _ | Construct _
  | Int _ | Float _ | String _ -> ()
  | Cast (t, _, ty) -> push cache view t; push cache view ty
  | Prod (_, ty, t) | Lambda (_, ty, t) -> push cache view ty; push cache view t
  | LetIn (_, b, ty, t) -> push cache view b; push cache view ty; push cache view t
  | App (f, args) -> push cache view f; push_array cache view args
  | Proj (_, _, t) -> push cache view t
  | Case (_, _, pms, ((_, p), _), iv, t, bl) ->
    push_array cache view pms;
    push cache view p;
    (match iv with NoInvert -> () | CaseInvert { indices } -> push_array cache view indices);
    push cache view t;
    for i = 0 to Array.length bl - 1 do push cache view (snd bl.(i)) done
  | Fix (_, (_, tl, bl)) | CoFix (_, (_, tl, bl)) ->
    if not (Int.equal (Array.length tl) (Array.length bl)) then invalid_arg "Array.fold_left2";
    for i = 0 to Array.length tl - 1 do push cache view tl.(i); push cache view bl.(i) done
  | Array (_, elems, def, ty) ->
    push_array cache view elems; push cache view def; push cache view ty

(* Ends a walk: empties the stack, the slots of [terms] that the walk wrote
   and, where [noting], the slots of [keys] that it wrote, so that the cache
   keeps no term the walk visited alive, but in the slots of [keys] of a
   cache not [noting]. *)
let end_walk cache =
  for i = 0 to cache.peak - 1 do cache.terms.(i) <- Constr.mkProp done;
  cache.size <- 0;
  cache.peak <- 0;
  for j = 0 to cache.touched_count - 1 do
    cache.keys.(cache.touched.(j)) <- Constr.mkProp
  done

(* The object [GlobRef.ConstRef kn]: the one at the slot of [objects] that
   the hash [kn] carries picks, where it is made of that very name ([==]),
   which makes it the same object as a new one; else a new one, kept there.
   The occurrences of a constant in a term usually share its name, so the
   walk makes its object once instead of at each occurrence. The hash is
   read, not computed ([KerName.hash]), and the name is not compared, so
   nothing here walks a name before [add_finite] checks it. Nothing empties
   [objects]: it keeps alive at most [object_slots] objects, which hold
   names and no term. *)
let const_ref cache kn =
  let i = Constant.UserOrd.hash kn land (object_slots - 1) in
  match cache.objects.(i) with
  | GlobRef.ConstRef kn' as obj when kn' == kn -> obj
  | _ -> let obj = GlobRef.ConstRef kn in cache.objects.(i) <- obj; obj

(* The object [GlobRef.IndRef (mind, 0)], the same way. *)
let ind_ref cache mind =
  let i = MutInd.UserOrd.hash mind land (object_slots - 1) in
  match cache.objects.(i) with
  | GlobRef.IndRef (mind', 0) as obj when mind' == mind -> obj
  | _ -> let obj = GlobRef.IndRef (mind, 0) in cache.objects.(i) <- obj; obj

type state = {
  env : Environ.env;
  access : Opaqueproof.opaque -> Opaqueproof.opaque_proofterm;
  recorded : Constant.t -> Opaqueproof.opaque -> GlobRef.t list option;
  (* the objects that the check of the opaque body of a constant recorded
     for it, if any: for the report only, never for the closure of
     -compare *)
  mutable fields : field_index ModPath.Map.t;
  (* the indexed fields of the implementation of each module looked up so far *)
  mutable public_nodes : node GlobRef.Map_env.t;
  mutable implementation_nodes : node GlobRef.Map_env.t;
  (* each object reached so far, keyed by its constant or by the first
     inductive of its block, in the declaration view that typed its use *)
  cache : walk_cache;
  (* the cache of [seen], the stack and the objects of [walk] *)
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

let empty_refs = GlobRef.Set_env.empty, GlobRef.Set_env.empty

(* [GlobRef.Set_env.add] gives back the set itself for an object the set
   holds already, but allocates on its way there, where [mem] does not: so
   [add_ref] gives back [refs] itself, and allocates nothing, for an object
   that it added before. *)
let add_ref view obj ((public, implementation) as refs) = match view with
  | Public ->
    if GlobRef.Set_env.mem obj public then refs
    else GlobRef.Set_env.add obj public, implementation
  | Implementation ->
    if GlobRef.Set_env.mem obj implementation then refs
    else public, GlobRef.Set_env.add obj implementation

(* The primitive type a literal has, which the kernel looks up to type it. *)
let add_prim add cache view prim refs = match prim with
  | Some c -> add view (const_ref cache c) refs
  | None -> refs

let refs_to_list (public, implementation) =
  List.map (fun obj -> Public, obj) (GlobRef.Set_env.elements public)
  @ List.map (fun obj -> Implementation, obj) (GlobRef.Set_env.elements implementation)

(* The objects that the terms [todo] mention, each added with [add]:
   [add_ref], but for [opaque_body_refs], which checks the object's names
   first. The walk takes a new generation of [cache], and keeps the terms
   it has still to visit on the stack of [cache], so its depth does not
   depend on the depth of the terms. A term retains the declaration view
   that typed it. The inductive of a [match] and of a projection, and the
   primitive type of a literal or an array, are objects the term relies on
   even though no subterm names them.

   The walk pushes each term of [todo] in its order, when the stack is
   empty, and visits the term on the top of the stack, which it pops. A
   node it enters pushes its subterms in the order of [Constr.fold]
   ([push_subterms]), so the walk takes them from the last to the first,
   and is done with all that the last one leads to before it takes the one
   below it. The objects it adds do not depend on that order: [seen] only
   skips a node walked before in the same generation, whose subterms were
   pushed then, so every node that [todo] reaches is walked and adds its
   objects. The order only decides which of two objects that
   [GlobRef.UserOrd] does not tell apart (one user name, two canonical
   names) a set keeps: the first one added.

   The walk's own code allocates nothing to visit a node, except where a
   set gains an object ([add_ref]), where [objects] has not the one the
   node names ([const_ref], [ind_ref]), and where the stack outgrows its
   arrays ([push]). That claim leaves out [Constr.hash_bounded], which
   [seen] calls for each compound node the walk pops, and which may
   allocate. The walk ends with [end_walk], by an exception too. *)
let walk add env cache todo =
  let gen = fresh_gen cache in
  let retro = Environ.retroknowledge env in
  let rec go refs todo =
    let n = cache.size in
    if Int.equal n 0 then begin match todo with
      | [] -> refs
      | (view, c) :: todo -> push cache view c; go refs todo
    end else begin
      cache.size <- n - 1;
      let view = cache.views.(n - 1) and c = cache.terms.(n - 1) in
      let open Constr in
      match kind c with
      | Rel _ | Var _ | Sort _ | Meta _ | Evar _ -> go refs todo
      | Int _ -> go (add_prim add cache view retro.Retroknowledge.retro_int63 refs) todo
      | Float _ -> go (add_prim add cache view retro.Retroknowledge.retro_float64 refs) todo
      | String _ -> go (add_prim add cache view retro.Retroknowledge.retro_string refs) todo
      | Const (kn, _) -> go (add view (const_ref cache kn) refs) todo
      | Ind ((mind, _), _) | Construct (((mind, _), _), _) ->
        go (add view (ind_ref cache mind) refs) todo
      | Cast _ | Prod _ | Lambda _ | LetIn _ | App _ | Proj _ | Case _ | Fix _ | CoFix _ | Array _ ->
        if seen cache gen c then go refs todo
        else
          let refs = match kind c with
            | Case (ci, _, _, _, _, _, _) -> add view (ind_ref cache (fst ci.ci_ind)) refs
            | Proj (p, _, _) -> add view (ind_ref cache (Projection.mind p)) refs
            | Array _ -> add_prim add cache view retro.Retroknowledge.retro_array refs
            | _ -> refs
          in
          push_subterms cache view c;
          go refs todo
    end
  in
  match go empty_refs todo with
  | refs -> end_walk cache; refs
  | exception e ->
    let e = Exninfo.capture e in
    end_walk cache;
    Exninfo.iraise e

exception Name_not_finite

(* [add_ref] for an object whose names are finite
   ([CheckNames.finite_names]), checked before [add_ref] compares them
   ([GlobRef.Set_env.mem], then [GlobRef.Set_env.add]) with those of any
   other object. *)
let add_finite view obj refs =
  if CheckNames.finite_names obj then add_ref view obj refs else raise Name_not_finite

(* The objects [walk] adds for the term [c] alone, in one view: the walk
   itself, so that the two cannot drift apart. A walk that starts from a
   declaration's type and its body [c], both in the declaration's view, adds
   the objects of the type and exactly these: [seen] only skips a node
   already walked in the same generation, whose objects are added already,
   so the objects of the two terms are the union of the objects of each.

   The primitive types of literals and arrays are those that [env]
   registers, where the report's walk takes the final environment's. They
   are the same constants, by their user names: the check of [c] in [env]
   typed each literal and array of [c], which needs its primitive type
   registered there ([Typeops.type_of_int] and the like), and a registration
   once made is never changed ([Primred.add_retroknowledge] keeps the first,
   and refuses one of another name). The report looks objects up, and
   prints them, by their user names only ([GlobRef.Map_env],
   [Environ.lookup_constant], [Constant.to_string]).

   The first object whose names are not finite ends the walk, and the body
   has no objects to record, [None].

   The cache of these walks is made once: [prepare_opaque_body_refs] makes
   it in the main process before any worker is forked, so that the workers
   share it until they write to it. On a 64-bit machine it takes 6 MiB plus
   48 KiB, plus a stack that grows to fit the largest walk it has run, which
   it keeps. Each walk, as it ends ([end_walk]), empties its stack and the
   slots of [seen] that it wrote: a worker checks one body after another,
   and the cache would otherwise keep the last body it walked alive. The
   objects it keeps ([const_ref], [ind_ref]) hold names only. *)
let body_walk_cache = lazy (walk_cache ~noting:true)

let prepare_opaque_body_refs () = ignore (Lazy.force body_walk_cache)

let opaque_body_refs env c =
  match walk add_finite env (Lazy.force body_walk_cache) [Public, c] with
  | public, _ -> Some (GlobRef.Set_env.elements public)
  | exception Name_not_finite -> None

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

type opaque_body =
  | Read of Constr.t
  | Recorded of GlobRef.t list

(* The body of the opaque [o] of the constant [kn], read, or the objects
   that the check of [o] recorded for it. A recorded body is not read
   again: the process that checked it read it, from the table the main
   process hashed. Its table is then not read here either, which is the
   one way records can change the report: see the header of
   reportRecords.mli. *)
let opaque_body st kn o =
  match st.recorded kn o with
  | Some objs -> Recorded objs
  | None -> let c, _ = st.access o in Read c

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
       warning, which names the constant.

       The test seam comes before the records, so that it still makes the
       body unreadable. Then a body that a check recorded is not read: the
       walk of the type alone, with the recorded objects added in the
       declaration's view, makes the same references as the walk of the type
       and the body ([opaque_body_refs]). The main process checked the
       names of the recorded objects as it decoded them
       ([CheckNames.finite_names]), before any was compared. *)
    let body, recorded, axiom = match cb.const_body with
      | Def c -> [declaration_view, c], [], false
      | OpaqueDef o ->
        (match (test_unreadable_opaque kn; opaque_body st kn o) with
         | Read c -> [declaration_view, c], [], false
         | Recorded objs -> [], objs, false
         | exception e when CErrors.noncritical e ->
           Feedback.msg_warning
             Pp.(str "Statement report: the opaque body of " ++ str (Constant.to_string kn)
                 ++ str " could not be read, so it is reported as an axiom: " ++ CErrors.print e);
           [], [], true)
      | Undef _ | Primitive _ | Symbol _ -> [], [], true
    in
    let refs = walk add_ref st.env st.cache ((declaration_view, cb.const_type) :: body) in
    let refs = List.fold_left (fun refs obj -> add_ref declaration_view obj refs) refs recorded in
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
    let refs = walk add_ref st.env st.cache todo in
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

(* Each opaque body is read: none has a record. *)
let no_record _ _ = None

(* A state with nothing reached yet, and a walk cache of its own. *)
let new_state ?(recorded = no_record) env access = {
  env; access; recorded; fields = ModPath.Map.empty;
  public_nodes = GlobRef.Map_env.empty; implementation_nodes = GlobRef.Map_env.empty;
  cache = walk_cache ~noting:false;
}

let print ?recorded env access requests =
  let index =
    Environ.fold_constants (fun c _ acc -> CString.Map.add (Constant.to_string c) c acc)
      env CString.Map.empty
  in
  let st = new_state ?recorded env access in
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
  line "END STATEMENT REPORT"

(** {6 The closure, for [rocqchk -compare]} *)

(* The comparator needs the axioms and flags of a constant, not the report's
   text, and it asks for several constants in one run, so the walk's caches
   are built once and kept. It reads every opaque body it reaches: the
   records are the report's alone. *)

type closure_state = state

let closure_state env access = new_state env access

let axioms_and_flags st kn =
  let axioms, flags = closure st (GlobRef.ConstRef kn) in
  let axioms = List.map (fun obj -> name_of obj, obj) (GlobRef.Set_env.elements axioms) in
  let flags =
    List.map (fun (kind, obj) -> kind, name_of obj, obj) (FlagSet.elements flags)
    |> List.stable_sort (fun (k1, n1, _) (k2, n2, _) ->
        let c = String.compare k1 k2 in if Int.equal c 0 then String.compare n1 n2 else c)
  in
  List.stable_sort (fun (a, _) (b, _) -> String.compare a b) axioms, flags
