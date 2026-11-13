(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** What a module's implementation declares, where the environment holds an
    interface instead.

    [Module M : T := E] and [Module M : T. ... End M] put T in the
    environment, so a field T declares as a parameter has no body there even
    where E or the structure defines it. The summary's Axioms section reads
    "no body" as "assumed", and so reported a definition as an axiom
    (dispatch://BET-245): for [Module Asc : U := Plain] with
    [Definition q := Asc.p], [rocqchk -o] printed Seal2.Asc.p while
    [Print Assumptions] on a proof that uses it reads "Closed under the
    global context".

    [defines_constant] answers the one question that tells the two apart, the
    way [Print Assumptions] answers it ([lookup_constant_in_impl] in
    vernac/assumptions.ml): it resolves the constant's module path through
    the implementations the environment holds and reads whether the
    implementation gives that field a body.

    A functor application is read the same way: [Module R := F A] and
    [Module R : T := F A] are implemented by the body of F, with F's
    parameter standing for A, as [fields_of_expr] in vernac/assumptions.ml
    reads them. So a field T declares as a parameter and F defines has a
    body, and a field F leaves without one is an axiom of R, named R.x, the
    name Print Assumptions prints for it. [application_axioms] lists those
    fields. The substitution of an application, F's path to R's and each
    parameter to its argument, is applied to the module paths the walk
    follows inside F's body, and to nothing else: the terms of the body are
    never read, and no renaming changes whether a field has a body.

    Every answer it is unsure of is [false], which keeps the name its caller
    would print. It reads an implementation and never a type: a module type
    can carry [Module M : T := E] of its own, and a module declared with
    [Declare Module] carries nothing else, while neither says what an
    implementation of it binds. The type of [Module M. ... End M], and of a
    functor declared without an ascription, is its implementation, and is
    read as one. *)

open Names
open Declarations
open Mod_declarations

(* A functor application a structure is read inside of: the path the
   functor's body was declared at, and the arguments its parameters are
   bound to. *)
type instance = ModPath.t * ModPath.t list

let same_instance (raw, args) (raw', args') =
  ModPath.equal raw raw' && List.equal ModPath.equal args args'

(* Where a structure is read. It was declared at the path [raw]; [subst] maps
   the module paths it mentions to the ones they denote where it is read, for
   a functor's body read through an application the functor's path to the
   application's and each parameter to its argument; and [within] lists the
   applications it is read inside of, innermost first. *)
type context = {
  raw : ModPath.t;
  subst : Mod_subst.substitution;
  within : instance list;
}

let root_context mp = { raw = mp; subst = Mod_subst.empty_subst; within = [] }

(* What one module's implementation declares, read by label: the modules
   under it, which the walk goes through, and whether each constant has a
   body, which is the answer it is after. [struc] is that structure, in the
   order it declares its fields, and [ctx] where it is read. *)
type fields = {
  modules : module_body Id.Map.t;
  constants : bool Id.Map.t;
  struc : structure_body;
  ctx : context;
}

let no_fields = {
  modules = Id.Map.empty;
  constants = Id.Map.empty;
  struc = [];
  ctx = root_context ModPath.dummy;
}

let fields_of_structure ctx struc =
  let add fields (lab, field) = match field with
    | SFBconst cb ->
      { fields with
        constants = Id.Map.add lab (Declareops.constant_has_body cb) fields.constants }
    | SFBmodule msb -> { fields with modules = Id.Map.add lab msb fields.modules }
    | SFBmind _ | SFBrules _ | SFBmodtype _ -> fields
  in
  List.fold_left add { no_fields with struc; ctx } struc

(* The module [lab] of a structure, and the context it is read in. *)
let member fields lab =
  Option.map (fun mb -> mb, { fields.ctx with raw = MPdot (fields.ctx.raw, lab) })
    (Id.Map.find_opt lab fields.modules)

let lookup_module env mp =
  match Environ.lookup_module mp env with
  | mb -> Some mb
  | exception Not_found -> None

(* The functor at the head of an application, and its arguments in the order
   the functor's parameters take them. *)
let rec unapply args = function
  | MEident f -> Some (f, args)
  | MEapply (me, arg) -> unapply (arg :: args) me
  | MEwith _ -> None

(* [subst] extended with each parameter of the functor type [sign] bound to
   the argument at its place, if [args] are exactly as many. *)
let rec bind subst sign args = match sign, args with
  | NoFunctor _, [] -> Some subst
  | MoreFunctor (mbid, _, sign), arg :: args ->
    bind (Mod_subst.add_mbid mbid arg (Mod_subst.empty_delta_resolver arg) subst) sign args
  | NoFunctor _, _ :: _ | MoreFunctor _, [] -> None

let rec functor_result = function
  | NoFunctor struc -> struc
  | MoreFunctor (_, _, sign) -> functor_result sign

(* Each module path is read once for each environment that asks about it: the
   summary asks about every constant it would print and about every module on
   the way to one, and an alias chain asks for the same structure again at
   each of its links. The environment is compared by identity, as the memo of
   Print Assumptions is (sync_memo in vernac/assumptions.ml), since what a
   path resolves to depends on it. A path that cannot be read is kept as the
   empty record, which answers for every label as a structure without that
   label does. [instances] counts the applications read for the
   environment. *)
type memo = {
  env : Environ.env;
  read : fields ModPath.Map.t;
  instances : int;
}

let memo = ref None

let read_memo env =
  match !memo with
  | Some m when m.env == env -> m.read
  | Some _ | None -> ModPath.Map.empty

let instances_read env =
  match !memo with
  | Some m when m.env == env -> m.instances
  | Some _ | None -> 0

let count_instance env =
  memo := Some { env; read = read_memo env; instances = instances_read env + 1 }

(* The paths whose fields are being read and are not kept yet. A library
   rocqchk checks cannot make a module its own implementation, since
   [check_mexpr] needs an alias's target in the environment before the alias;
   an admitted library is not checked, and [Module A := A], or [A := B] with
   [B := A], would otherwise send the walk round the cycle for ever. Such a
   path is read as the empty record, which keeps every name under it. *)
let reading = ref ModPath.Set.empty

let start_reading mp = reading := ModPath.Set.add mp !reading

let keep_fields env paths fields =
  let read = List.fold_left (fun read mp -> ModPath.Map.add mp fields read)
      (read_memo env) paths
  in
  memo := Some { env; read; instances = instances_read env };
  reading := List.fold_left (fun s mp -> ModPath.Set.remove mp s) !reading paths;
  fields

(* The applications of a library coqc compiled have an end: a functor body
   names only parameters, the modules it declares itself and modules declared
   before the functor, so the bodies one path is read inside of can repeat
   only through functor parameters bound to partial applications, and each
   such repetition is bound to arguments the one around it was given. With
   HG := H G, the body of R := H HG A holds H's body again, bound to G and A
   where the outer one is bound to HG and A; both are read, and both must be,
   since an axiom of G's body is named R.M.M.g. An admitted library is not
   checked, and can make a functor's body apply that functor again with no
   end: to the same arguments, or to a module of the application, a path
   that grows at each level. Three stops end it, each where an application is
   read, so that the path reads as the empty record for both questions this
   file answers: no field under it has a body, so no name under it is
   dropped, and no axiom under it is listed. An application stops when it is
   read inside one with the same functor body and the same arguments, which
   only an admitted library can hold; when it is read inside [max_depth]
   applications; and when [max_instances] applications have been read for
   the environment, which bounds the work a library can make the summary do
   with many applications at each level. A library that reaches one of the
   last two keeps its names under the stop, the answer that fails closed;
   each level of nesting on one path is an application a library writes or a
   partial application it declares, so an honest library reaches [max_depth]
   only with a chain of 64 of them. *)
let max_depth = 64
let max_instances = 100_000

(* An alias is followed as a loop, over the paths read so far, and not as a
   call: a chain of them is as long as a library cares to make it, and each
   of its links is given the fields the chain ends at. A link whose target
   lies under a module that is itself read through another alias is the one
   case that keeps a frame, since that module is read first; the modules such
   a chain needs are nested as deeply as the chain is long, and both the
   import of a library and the check of one recurse once per level of
   nesting, so this walk runs out of stack no sooner than they do. Every path
   of [read] is in [reading]; a target that already is closes a cycle. [ctx]
   is where the structure that declares [mb] is read. *)
let rec read_module env read ctx mb =
  match mod_type mb, mod_expr mb with
  | MoreFunctor _, _ ->
    (* A functor: its fields are a functor body's, which no name of this
       walk reaches but through an application. *)
    keep_fields env read no_fields
  | NoFunctor _, Algebraic (MENoFunctor (MEident target)) ->
    (* [Module M := N] and [Module M : T := N]: N is the implementation. *)
    let target = Mod_subst.subst_mp ctx.subst target in
    if ModPath.Set.mem target !reading then keep_fields env read no_fields
    else
    (match ModPath.Map.find_opt target (read_memo env) with
     | Some fields -> keep_fields env read fields
     | None ->
       match module_at env target with
       | None -> keep_fields env read no_fields
       | Some (mb, ctx) ->
         start_reading target; read_module env (target :: read) ctx mb)
  | NoFunctor _, Algebraic (MENoFunctor (MEapply _ as me)) ->
    (* [Module R := F A] and [Module R : T := F A]: F's body, instantiated.
       [read] is never empty, and its first path is the module whose
       expression this is. *)
    keep_fields env read (applied env (List.hd read) ctx ctx ModPath.Set.empty me [])
  | NoFunctor _, Algebraic (MENoFunctor (MEwith _) | MEMoreFunctor _) ->
    (* Neither is in an implementation of a module that is not a functor. *)
    keep_fields env read no_fields
  | NoFunctor _, Struct (_, struc) ->
    keep_fields env read (fields_of_structure ctx struc)
  | NoFunctor struc, FullStruct ->
    (* [Module M. ... End M]: the type is the implementation. *)
    keep_fields env read (fields_of_structure ctx struc)
  | NoFunctor _, Abstract ->
    (* [Declare Module M : T]: no implementation at all. *)
    keep_fields env read no_fields

(* The fields of the module [app]: the body of the functor the expression
   [me] applies, to [me]'s arguments and then to [args], with the functor's
   path mapped to [app]'s and each of its parameters to its argument. [ctx]
   gives the paths [me] names, and [site] is where [app] is read. An alias
   of a functor, and a functor that is a partial application, are followed to
   the functor they name, [seen] stopping a cycle of them. A functor declared
   with [Declare Module], and one an expression defines over parameters of
   its own, have no body this walk reads. *)
and applied env app site ctx seen me args =
  match unapply [] me with
  | None -> no_fields
  | Some (f, args') ->
    let resolve = Mod_subst.subst_mp ctx.subst in
    let f = resolve f and args = List.map resolve args' @ args in
    if ModPath.Set.mem f seen then no_fields else
    match module_at env f with
    | None -> no_fields
    | Some (mb, ctx) ->
      match mod_expr mb with
      | Struct (_, struc) -> instantiate env app site ctx (mod_type mb) args struc
      | FullStruct ->
        instantiate env app site ctx (mod_type mb) args (functor_result (mod_type mb))
      | Abstract | Algebraic (MEMoreFunctor _) -> no_fields
      | Algebraic (MENoFunctor me) -> applied env app site ctx (ModPath.Set.add f seen) me args

(* The body [struc] of the functor of type [sign] declared where [ctx] says,
   bound to [args], read as [app]'s, inside the applications of [site]; or the
   empty record, at one of the stops above. *)
and instantiate env app site ctx sign args struc =
  let instance = (ctx.raw, args) in
  if List.exists (same_instance instance) site.within
  || List.length site.within >= max_depth
  || instances_read env >= max_instances
  then no_fields
  else
    match bind ctx.subst sign args with
    | None -> no_fields
    | Some subst ->
      count_instance env;
      let subst = Mod_subst.add_mp ctx.raw app (Mod_subst.empty_delta_resolver app) subst in
      fields_of_structure { raw = ctx.raw; subst; within = instance :: site.within } struc

(* A path's own root is the only module read from the environment. Under it,
   each module is the one its enclosing implementation declares, and a label
   that implementation does not declare is read no further: what the
   environment holds under such a name came from a type, which says nothing
   about what an implementation binds. The module comes with the context of
   the structure that declares it. *)
and module_at env mp =
  match mp with
  | MPfile _ | MPbound _ ->
    Option.map (fun mb -> mb, root_context mp) (lookup_module env mp)
  | MPdot (enclosing, lab) -> member (fields_in_implementation env enclosing) lab

(* The path is walked from its root down, so that its own depth costs no
   stack. *)
and fields_in_implementation env mp =
  match ModPath.Map.find_opt mp (read_memo env) with
  | Some fields -> fields
  | None ->
    let rec split mp labs = match mp with
      | MPfile _ | MPbound _ -> mp, labs
      | MPdot (enclosing, lab) -> split enclosing (lab :: labs)
    in
    let root, labs = split mp [] in
    let descend (mp, fields) lab =
      let mp = MPdot (mp, lab) in
      match ModPath.Map.find_opt mp (read_memo env) with
      | Some fields -> mp, fields
      | None when ModPath.Set.mem mp !reading -> mp, no_fields
      | None ->
        match member fields lab with
        | None -> mp, keep_fields env [mp] no_fields
        | Some (mb, ctx) -> start_reading mp; mp, read_module env [mp] ctx mb
    in
    let root_fields = match ModPath.Map.find_opt root (read_memo env) with
      | Some fields -> fields
      | None when ModPath.Set.mem root !reading -> no_fields
      | None ->
        match module_at env root with
        | None -> keep_fields env [root] no_fields
        | Some (mb, ctx) -> start_reading root; read_module env [root] ctx mb
    in
    snd (List.fold_left descend (root, root_fields) labs)

let defines_constant env kn =
  reading := ModPath.Set.empty;
  let mp, lab = KerName.repr (Constant.user kn) in
  match Id.Map.find_opt lab (fields_in_implementation env mp).constants with
  | Some has_body -> has_body
  | None -> false

(* Every constant without a body in the implementation of [mp], and in the
   modules under it, named under [mp], in the order the structures declare
   them: what the environment fold lists for a module it holds, for one
   whose implementation it does not hold. A module under it is read as it is
   implemented: a plain or sealed structure for what it declares, an
   application for its functor's body, a declared module for its type,
   whose parameters are what Print Assumptions names. An alias is not read:
   what it names is declared, and listed, where its target is. A functor is
   not read either: its fields are reached through its applications. The
   walk reads every module through [fields_in_implementation], so it stops
   exactly where [defines_constant] has no body to give: at an application
   read as the empty record, above. *)
let application_axioms env mp =
  reading := ModPath.Set.empty;
  let bodyless mp acc lab cb =
    if Declareops.constant_has_body cb then acc else Constant.make2 mp lab :: acc
  in
  let rec structure acc mp fields = List.fold_left (field mp) acc fields.struc
  and field mp acc (lab, sfb) = match sfb with
    | SFBconst cb -> bodyless mp acc lab cb
    | SFBmodule msb ->
      let mp = MPdot (mp, lab) in
      (match mod_type msb, mod_expr msb with
       | MoreFunctor _, _ | NoFunctor _, Algebraic (MENoFunctor (MEident _)) -> acc
       | NoFunctor struc, Abstract -> declared acc mp struc
       | NoFunctor _, (Algebraic _ | Struct _ | FullStruct) ->
         structure acc mp (fields_in_implementation env mp))
    | SFBmind _ | SFBrules _ | SFBmodtype _ -> acc
  and declared acc mp struc =
    List.fold_left (fun acc (lab, sfb) -> match sfb with
        | SFBconst cb -> bodyless mp acc lab cb
        | SFBmodule msb ->
          (match mod_type msb with
           | NoFunctor struc -> declared acc (MPdot (mp, lab)) struc
           | MoreFunctor _ -> acc)
        | SFBmind _ | SFBrules _ | SFBmodtype _ -> acc)
      acc struc
  in
  List.rev (structure [] mp (fields_in_implementation env mp))
