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

    [defines_constant] answers [false] wherever no implementation says,
    which keeps the name its caller would print. It reads an implementation
    and never a type: a module type can carry [Module M : T := E] of its
    own, and a module declared with [Declare Module] carries nothing else,
    while neither says what an implementation of it binds. The type of
    [Module M. ... End M], and of a functor declared without an ascription,
    is its implementation, and is read as one. [application_axioms] reads
    types as well: a declared module's, and those of an application of a
    functor that has no body. There it lists every constant those types
    declare without a body, which can be more names than Print Assumptions
    prints; its comment below says where.

    Where the walk stops before it has read an implementation that exists,
    at one of the stops below, both functions raise a user error, and
    rocqchk -o prints no summary: a summary that could leave out an axiom
    of the implementation not read is never printed. *)

open Names
open Declarations
open Mod_declarations

(* Where a structure is read. It was declared at the path [raw]; [subst] maps
   the module paths it mentions to the ones they denote where it is read, for
   a functor's body read through an application the functor's path to the
   application's and each parameter to its argument; and [depth] counts the
   applications it is read inside of. *)
type context = {
  raw : ModPath.t;
  subst : Mod_subst.substitution;
  depth : int;
}

let root_context mp = { raw = mp; subst = Mod_subst.empty_subst; depth = 0 }

(* What one module's implementation declares, read by label: the modules
   under it, which the walk goes through, and whether each constant has a
   body, which is the answer it is after. [struc] is that structure, in the
   order it declares its fields, and [ctx] where it is read. [implemented] is
   false for the empty record, which stands for a module whose fields the
   walk reads from no implementation: a functor, whose fields it reads
   through its applications, and a module no implementation leads to, such
   as a declared one. For an application of a functor that has no body,
   [types] then holds the result type of each functor the walk followed to
   it, the innermost first. *)
type fields = {
  modules : module_body Id.Map.t;
  constants : bool Id.Map.t;
  struc : structure_body;
  ctx : context;
  implemented : bool;
  types : structure_body list;
}

let no_fields = {
  modules = Id.Map.empty;
  constants = Id.Map.empty;
  struc = [];
  ctx = root_context ModPath.dummy;
  implemented = false;
  types = [];
}

let fields_of_structure ctx struc =
  let add fields (lab, field) = match field with
    | SFBconst cb ->
      { fields with
        constants = Id.Map.add lab (Declareops.constant_has_body cb) fields.constants }
    | SFBmodule msb -> { fields with modules = Id.Map.add lab msb fields.modules }
    | SFBmind _ | SFBrules _ | SFBmodtype _ -> fields
  in
  List.fold_left add { no_fields with struc; ctx; implemented = true } struc

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

(* [subst] with the parameter [mbid] bound to the argument [arg]. *)
let bind_param subst mbid arg =
  Mod_subst.add_mbid mbid arg (Mod_subst.empty_delta_resolver arg) subst

(* [subst] extended with each parameter of the functor type [sign] bound to
   the argument at its place, if [args] are exactly as many. *)
let rec bind subst sign args = match sign, args with
  | NoFunctor _, [] -> Some subst
  | MoreFunctor (mbid, _, sign), arg :: args -> bind (bind_param subst mbid arg) sign args
  | NoFunctor _, _ :: _ | MoreFunctor _, [] -> None

(* For [Module G (X : S) := E], whose type is the functor type [sign] and
   whose expression is [E] under one [MEMoreFunctor] for each parameter:
   [subst] with each parameter bound to the argument at its place, [E], and
   the arguments left for it, as [fields_of_expression] in
   vernac/assumptions.ml reads it. The parameters are the type's: the
   expression names them but does not hold them. *)
let rec bind_expression subst sign fe args = match sign, fe, args with
  | _, MENoFunctor me, args -> Some (subst, me, args)
  | MoreFunctor (mbid, _, sign), MEMoreFunctor fe, arg :: args ->
    bind_expression (bind_param subst mbid arg) sign fe args
  | (NoFunctor _ | MoreFunctor _), MEMoreFunctor _, _ -> None

let rec functor_result = function
  | NoFunctor struc -> struc
  | MoreFunctor (_, _, sign) -> functor_result sign

(* Each module path is read once for each environment that asks about it: the
   summary asks about every constant it would print and about every module on
   the way to one, and an alias chain asks for the same structure again at
   each of its links. The environment is compared by identity, as the memo of
   Print Assumptions is (sync_memo in vernac/assumptions.ml), since what a
   path resolves to depends on it. A path no implementation leads to is kept
   as the empty record, which answers for every label as a structure without
   that label does. [steps] counts the steps the walk has taken for the
   environment ([max_steps] below says what a step is). *)
type memo = {
  env : Environ.env;
  read : fields ModPath.Map.t;
  steps : int;
}

let memo = ref None

let current env =
  match !memo with
  | Some m when m.env == env -> m
  | Some _ | None -> { env; read = ModPath.Map.empty; steps = 0 }

let read_memo env = (current env).read

let steps_taken env = (current env).steps

let take_steps env n =
  let m = current env in
  memo := Some { m with steps = m.steps + n }

(* The paths whose fields are being read and are not kept yet. A library
   rocqchk checks cannot make a module its own implementation, since
   [check_mexpr] needs an alias's target in the environment before the alias;
   an admitted library is not checked, and [Module A := A], or [A := B] with
   [B := A], would otherwise send the walk round the cycle for ever. Such a
   cycle is one of the stops below. *)
let reading = ref ModPath.Set.empty

let start_reading mp = reading := ModPath.Set.add mp !reading

let keep_fields env paths fields =
  let read = List.fold_left (fun read mp -> ModPath.Map.add mp fields read)
      (read_memo env) paths
  in
  memo := Some { (current env) with read };
  reading := List.fold_left (fun s mp -> ModPath.Set.remove mp s) !reading paths;
  fields

(* The walk of a library coqc compiled has an end: a functor body names only
   parameters, the modules it declares itself and modules declared before
   the functor. One functor body can still be read inside itself, and both
   reads must be made. With HG := H G, the body of R := H HG A holds H's
   body again, bound to G and A where the outer one is bound to HG and A, and
   an axiom of G's body is named R.M.M.g. A functor K declared in the body of
   a functor G is declared at G.K in every application of G: with S1 := G A,
   S2 := G S1 and Z := S2.K B, where K's body holds Q := Y.K X, the body
   declared at G.K is read at Z, bound to B with Y standing for S1, and again
   at Z.Q, bound to B with Y standing for A. The functors followed to the one
   whose body is read can meet one functor twice as well: with
   Apply (X : FSIG) (Y : SIG) := X Y and AF := Apply F, the walk reads
   R := Apply AF Q through Apply, AF and Apply again, bound to F and Q, and
   then reads F's body.

   An admitted library is not checked, and can make the walk go on for ever:
   a functor's body can apply that functor again, to the same arguments or to
   a module of the application, a path that grows at each level, and the
   functors followed to a body can lead to one whose path grows at each
   step. Two bounds end it, and each refuses the summary ([refuse]):
   - [max_depth]: an application read inside 64 applications, since an
     application read in the body of another is read one level deeper;
   - [max_steps]: the steps of the walk for the environment, 100000. Each
     functor [applied] resolves, at the head of an application and at each
     alias, partial application or functor an expression defines that it
     follows from there, costs one step, and one more for each name in its
     path after the library or functor parameter it starts from ([labels]):
     Lib.F costs two steps, Lib.M.F three, since the walk reads each module
     on that path to reach it. A step that would go past the bound is not
     taken.
   Each level of nesting on one path is an application a library writes or a
   partial application it declares, so an honest library reaches [max_depth]
   only with 64 of them nested on one path, and [max_steps] only when the
   applications the summary reads, those of the functor bodies they apply
   included, cost more than 100000 steps. At a bound the walk has not read
   the body that declares the application's axioms, and the application's
   type need not name them. *)
let max_depth = 64
let max_steps = 100_000

(* Every stop of the walk, where it has not read an implementation the
   Axioms section needs, ends the summary with this error: [at] names where
   the walk stopped and [why] says why. Besides the two bounds above, each
   stop is a shape that coqc does not write, which only a crafted .vo holds:
   an alias whose target the walk is already reading; a module whose
   implementation it needs while it reads it; an application whose
   arguments do not fit the parameters of its functor, or those the
   expression that defines its functor binds; an application whose functor
   is a 'with' constraint; and a module that is not a functor but is
   implemented by a functor or a 'with' constraint. The tests
   misc/rocqchk_walk_stop_summary.sh and misc/rocqchk_functor_loop_summary.sh
   forge one library for each. *)
let refuse at why =
  CErrors.user_err
    Pp.(str "The Axioms summary could not be completed: the walk of the \
             module implementations stopped at " ++ at ++ str ", " ++ why
        ++ str ".")

(* An application, with its functor's whole path and the first 8 arguments:
   a crafted G := G A gives each step one argument more. *)
let pr_application mp f args =
  let rec first n = function
    | [] -> Pp.mt ()
    | arg :: args when n > 0 -> Pp.(str " " ++ ModPath.print arg ++ first (n - 1) args)
    | rest -> Pp.(str " ... (" ++ int (List.length rest) ++ str " more)")
  in
  Pp.(str "the application " ++ ModPath.print mp ++ str " := " ++ ModPath.print f ++ first 8 args)

let rec labels = function
  | MPfile _ | MPbound _ -> 0
  | MPdot (mp, _) -> 1 + labels mp

(* An alias is followed as a loop, over the paths read so far, and not as a
   call: a chain of them is as long as a library cares to make it, and each
   of its links is given the fields the chain ends at. A link whose target
   lies under a module that is itself read through another alias is the one
   case that keeps a frame, since that module is read first; the modules such
   a chain needs are nested as deeply as the chain is long, and both the
   import of a library and the check of one recurse once per level of
   nesting, so this walk runs out of stack no sooner than they do. Every path
   of [read] is in [reading]; a target that already is closes a cycle, a
   stop. [read] is never empty, and its first path is the module [mb] is.
   [ctx] is where the structure that declares [mb] is read. *)
let rec read_module env read ctx mb =
  match mod_type mb, mod_expr mb with
  | MoreFunctor _, _ ->
    (* A functor: its fields are a functor body's, which no name of this
       walk reaches but through an application. *)
    keep_fields env read no_fields
  | NoFunctor _, Algebraic (MENoFunctor (MEident target)) ->
    (* [Module M := N] and [Module M : T := N]: N is the implementation. *)
    let target = Mod_subst.subst_mp ctx.subst target in
    if ModPath.Set.mem target !reading then
      refuse Pp.(str "the alias " ++ ModPath.print (List.hd read) ++ str " := "
                 ++ ModPath.print target)
        (Pp.str "whose target it is already reading: the aliases form a cycle")
    else
    (match ModPath.Map.find_opt target (read_memo env) with
     | Some fields -> keep_fields env read fields
     | None ->
       match module_at env target with
       | None -> keep_fields env read no_fields
       | Some (mb, ctx) ->
         start_reading target; read_module env (target :: read) ctx mb)
  | NoFunctor _, Algebraic (MENoFunctor (MEapply _ as me)) ->
    (* [Module R := F A] and [Module R : T := F A]: F's body, instantiated. *)
    keep_fields env read (applied env (List.hd read) ctx ctx [] me [])
  | NoFunctor _, Algebraic (MENoFunctor (MEwith _) | MEMoreFunctor _) ->
    (* Neither is in an implementation of a module that is not a functor. *)
    refuse Pp.(str "the module " ++ ModPath.print (List.hd read))
      (Pp.str "which is not a functor but is implemented by a functor or by a \
               'with' constraint")
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
   of a functor, a functor that is a partial application, and a functor an
   expression defines over parameters of its own, [Module G (X : S) := E],
   are followed to the functor they name, as [fields_of_expr] and
   [fields_of_expression] in vernac/assumptions.ml follow them. Each functor
   resolved costs the steps [max_steps] says. A functor declared with
   [Declare Module] has no body to read, and neither has one no
   implementation leads to, such as a functor a declared module's type
   declares. [outer] holds the result type of each functor followed so far,
   the innermost first; for a functor with no body, the empty record carries
   them, for the listing. *)
and applied env app site ctx outer me args =
  let unread types = { no_fields with types } in
  match unapply [] me with
  | None ->
    refuse (Pp.seq [Pp.str "the application "; ModPath.print app])
      (Pp.str "whose functor is a 'with' constraint")
  | Some (f, args') ->
    let resolve = Mod_subst.subst_mp ctx.subst in
    let f = resolve f and args = List.map resolve args' @ args in
    let cost = 1 + labels f in
    if steps_taken env + cost > max_steps then
      refuse (pr_application app f args)
        Pp.(str "which would take it past " ++ int max_steps
            ++ str " steps, the most it takes for one summary")
    else
    let () = take_steps env cost in
    match module_at env f with
    | None -> unread outer
    | Some (mb, ctx) ->
      let sign = mod_type mb in
      match mod_expr mb with
      | Struct (_, struc) -> instantiate env app site ctx sign args struc
      | FullStruct -> instantiate env app site ctx sign args (functor_result sign)
      | Abstract -> unread (functor_result sign :: outer)
      | Algebraic fe ->
        (* [bind_expression] gives [MENoFunctor me] back as [me], with
           [ctx]'s substitution and [args] unchanged. *)
        match bind_expression ctx.subst sign fe args with
        | None ->
          refuse (pr_application app f args)
            (Pp.str "whose arguments do not fit the parameters that the \
                     expression defining its functor binds")
        | Some (subst, me, args) ->
          applied env app site { ctx with subst } (functor_result sign :: outer) me args

(* The body [struc] of the functor of type [sign] declared where [ctx] says,
   bound to [args], read as [app]'s, one level deeper than [site]. At the
   depth bound above, or where [args] do not fit [sign], the summary is
   refused. The error names the functor by the path it has where it is
   read. *)
and instantiate env app site ctx sign args struc =
  let stop why = refuse (pr_application app (Mod_subst.subst_mp ctx.subst ctx.raw) args) why in
  if site.depth >= max_depth then
    stop Pp.(str "which is read inside " ++ int max_depth
             ++ str " nested applications, the most it reads")
  else
    match bind ctx.subst sign args with
    | None -> stop (Pp.str "whose arguments do not fit the functor's parameters")
    | Some subst ->
      let subst = Mod_subst.add_mp ctx.raw app (Mod_subst.empty_delta_resolver app) subst in
      fields_of_structure { raw = ctx.raw; subst; depth = site.depth + 1 } struc

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
    (* The fields at [mp]: those kept for it; else, unless it is being read,
       which closes a cycle, a stop, those of the module [find] gives, read
       and kept. *)
    let read_at mp find =
      match ModPath.Map.find_opt mp (read_memo env) with
      | Some fields -> fields
      | None when ModPath.Set.mem mp !reading ->
        refuse Pp.(str "the module " ++ ModPath.print mp)
          (Pp.str "whose implementation it needs while it reads it: the \
                   implementations form a cycle")
      | None ->
        match find () with
        | None -> keep_fields env [mp] no_fields
        | Some (mb, ctx) -> start_reading mp; read_module env [mp] ctx mb
    in
    let descend (mp, fields) lab =
      let mp = MPdot (mp, lab) in
      mp, read_at mp (fun () -> member fields lab)
    in
    let root_fields = read_at root (fun () -> module_at env root) in
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
   whose implementation it does not hold. [mb] is the module the walk of
   [Mod_checking] recorded at [mp]. A module under it is read as it is
   implemented: a plain or sealed structure for what it declares, an
   application for its functor's body, a declared module for its type,
   whose parameters are what Print Assumptions names. An alias is not read:
   what it names is declared, and listed, where its target is. A functor is
   not read either: its fields are reached through its applications. The
   walk reads every module through [fields_in_implementation], so it reads a
   body exactly where [defines_constant] may drop a name for it.

   An application of a functor that has no body, declared with
   [Declare Module] or one no implementation leads to, such as a functor a
   declared module's type declares, and an application a module type
   declares, as under a [Declare Module], are listed by their types instead:
   the constants without a body in the type the application has, which is
   the functor's result type bound to its arguments, or the type an
   ascription gives it, and in the result type of each functor the walk
   followed to it. No body hides an axiom behind those types there, and
   they list every parameter they declare: more names than Print
   Assumptions prints, which fails closed. Where the walk stops before it
   reads a body that exists, the summary is refused instead ([refuse]),
   since those types need not name the axioms that body declares. *)
let application_axioms env mp mb =
  reading := ModPath.Set.empty;
  let bodyless mp acc lab cb =
    if Declareops.constant_has_body cb then acc else Constant.make2 mp lab :: acc
  in
  let rec structure acc mp fields = List.fold_left (field mp) acc fields.struc
  and field mp acc (lab, sfb) = match sfb with
    | SFBconst cb -> bodyless mp acc lab cb
    | SFBmodule msb -> module_ acc (MPdot (mp, lab)) msb
    | SFBmind _ | SFBrules _ | SFBmodtype _ -> acc
  and module_ acc mp mb =
    match mod_type mb, mod_expr mb with
    | MoreFunctor _, _ | NoFunctor _, Algebraic (MENoFunctor (MEident _)) -> acc
    | NoFunctor struc, Abstract -> declared acc mp struc
    | NoFunctor struc, Algebraic _ ->
      let fields = fields_in_implementation env mp in
      if fields.implemented then structure acc mp fields
      else List.fold_left (fun acc struc -> declared acc mp struc) acc (struc :: fields.types)
    | NoFunctor _, (Struct _ | FullStruct) -> structure acc mp (fields_in_implementation env mp)
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
  List.rev (module_ [] mp mb)

(* With [-d checker-summary], how many steps ([max_steps]) the summary's walk
   took for the environment. *)
let debug = CDebug.create ~name:"checker-summary" ()

let debug_counts env =
  debug (fun () ->
      let m = current env in
      Pp.(str "steps: " ++ int m.steps ++ str " of at most " ++ int max_steps))
