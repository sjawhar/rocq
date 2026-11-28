(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Constr
open Declarations
open Environ
open CheckDischargedKeys

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

(** {6 Checking an opaque body discharged from sections}

    Discharging a section turns each use of a section definition [c] into
    [c x1 .. xn], the discharged [c] applied to the section variables, which
    are Rels of the block of binders that cooking puts in front of the body.
    The lazy machine (kernel/cClosure.ml) keeps the value of a constant once
    per conversion, but [c xs] beta-reduces that value into a new closure at
    each occurrence, so the reduction of one occurrence is never shared with
    another. Inside the section, where coqc checks the body at Qed, the
    section variables are variables of the environment ([Var]), and [c] is
    a constant with no argument whose section hypotheses are those
    variables, reduced once. A chain of section definitions that each read
    the previous one twice makes the check of the discharged body
    exponential.

    So the body is checked here in that section form ([prepare]): each
    variable of the named block ([split]) becomes a variable of the
    environment, and each such [c xs] a fresh constant [c'] with no
    argument, whose section hypotheses are the variables of [xs] and whose
    value is [c]'s body at [xs]; each [c xs rest] of the body and of the
    statement becomes [c' rest]. The lazy machine keeps the value of [c']
    as it keeps any constant's, so [c'] is reduced once per conversion, as
    [c] is inside the section.

    The named block is the assumptions of the block before the first one
    whose type mentions a local definition of the block, a section [Let]
    ([split]). The local definitions, and the assumptions from that one on,
    stay binders of the rewritten body, in their order, so the stock check
    types them as it types the cooked body. The statement substitutes the
    [Let]s ([Cooking.abstract_as_type]) and the body keeps them as let-ins,
    whose typing substitutes their values in the type of what follows
    ([Typeops.execute] of LetIn), so the stock check compares a [Let]'s
    value with itself, or its Rel with itself, where it compares the
    statement with the type of the body, and the rewritten check does the
    same. A [Let] as a variable of the environment would meet its value
    there; so would an assumption named with the values substituted in its
    type, where the body uses it at a type that holds the [Let]'s Rel; and
    conversion reduces the value, by match and fixpoint reduction too,
    before it unfolds the variable or the Rel ([Conversion.eqappr]), which
    can take far longer than the whole stock check.

    Such a [c xs], a key, is a section constant applied first to as many
    variables of the named block as the cookings of this body apply it to
    ([CheckDischargedKeys.head]), and it is bound only if [c] occurs
    in no term that the check reads and that is not rewritten
    ([CheckDischargedKeys.find_keys]). Where conversion meets one constant
    on both sides, as in [c xs] against [c ts], it compares [xs] with [ts]
    first and stops there when they are convertible ([Conversion]:
    [conv_table_key], then [convert_stacks]). Against [c'] it unfolds one
    of the two instead, and then possibly a constant in its value, whose
    reduction the stock check never does and which can take far longer than
    the whole stock check. Cooking applies [c] to the same variables at
    each of its occurrences, so in the rewritten terms [c'] only meets
    [c']. Nothing here checks that: a body that applies [c] to other
    variables elsewhere gets one constant for each, which can make the
    check slower but changes no verdict
    ([CheckDischargedKeys.key_values]). A global constant can occur in
    other forms, as in [g n] against [g (0 + n)], so it is never a key; and
    the terms that are not rewritten, such as the named block or the type
    of a section lemma, hold [c xs] as it is.

    The binding pays where the value of a key holds keys: the stock check
    puts each of them in a new closure wherever it unfolds the key, so a
    chain of K section definitions, each holding the one before it twice,
    is reduced about 2^K times, and once each with the binding. Where no
    value holds keys twice, nothing doubles: the binding shares only the
    reduction of a key's value between the places where one conversion
    unfolds it, and that has cost more than it saved. On r188's release
    tree (BET-1599's tree-rel-2, a grade tree of dispatch://BET-1602), a
    version of this check that bound keys whether or not they formed a
    chain checked the 939 proofs with one key in 78.6 s, with their key
    search and rewritten checks, where the stock check took 66.1 s; those
    with 2 to 4 keys took 25.9 s against 23.6 s, and those with 5 to 19
    keys 4.6 s against 4.0 s. So the keys are bound only when they form a
    chain, the value of one of them holding keys at least twice, counted as
    [CheckDischargedKeys.chain_gate] counts them (the chain gate, decided
    before any key's value is unfolded); else the stock check runs.

    The steps, in order:
    - [check]: the early exits listed there;
    - [peel]: the block, the first binders of the body;
    - [split]: the named block, and the body under it;
    - [CheckDischargedKeys.has_key]: for a body with no key that can be
      bound, the stock check runs;
    - [Typeops.infer_type] types the named block in one pass, then
      [statement_in_block] compares each domain of the statement with its
      variable and gives the statement under the named block;
    - [CheckDischargedKeys.find_keys]: if they form a chain, the keys to
      bind, each with its value and type, within a budget of work;
    - [prepare]: the named block and the keys' constants, in the
      environment, and [subst] rewrites the body and the statement with
      them;
    - test only, [put_back_check]: [put_back] gives back, from what the
      rewritten check reads, the body and the statement under the named
      block, the types of the named block, and each key's value and type,
      and [unsplit] gives back the cooked body from the named block and
      the body under it;
    - [check]: [stock], the stock check that [Mod_checking] passes in, runs
      on the rewritten body and statement, in the environment that holds the
      named block and the constants.

    When that does not accept, [stock] runs on the cooked body instead, and
    its verdict and error stand: a shape that this check does not expect, a
    refusal of the rewritten body, and any exception but an interrupt or
    memory exhausted all fall back. So this check refuses nothing itself,
    but the test-only put-back assertion, and the verdicts are the stock
    check's as long as the stock check accepts the cooked body whenever it
    accepts the rewritten one ([prepare] says why it does). The comment of
    each function says why it keeps that. *)

(* An interrupt or memory exhausted ends this check as it would end the
   stock check. Any other exception here, Stack_overflow included, runs the
   stock check. *)
let falls_back = function
  | Sys.Break | Out_of_memory -> false
  | _ -> true

let attempt f = try Some (f ()) with e when falls_back e -> None

(* Test only, read as [CheckLibrary.cook_cross_check_on] reads it: with
   ROCQCHK_COOK_CROSS_CHECK set to a non-empty value, [put_back_check] runs
   on each body that this check rewrites. *)
let cross_check_on =
  match Sys.getenv_opt "ROCQCHK_COOK_CROSS_CHECK" with
  | None | Some "" -> false
  | Some _ -> true

(* [peel n body]: the block, the first [n] binders of the body, as cooking
   puts it there ([Cooking.abstract_as_body]: [it_mkLambda_or_LetIn]); [n]
   is the number of section names that the cookings abstract. Its
   declarations, the outermost first, and the body under it. A body with
   fewer binders is not of that shape. [Term.decompose_lambda_n_decls]
   would skip a [Cast] between the binders, which the stock check types;
   this check falls back on such a body. *)
let peel n body =
  let rec peel i acc c =
    if Int.equal i n then Array.of_list (List.rev acc), c
    else match kind c with
      | Lambda (na, t, c) -> peel (i + 1) (RelDecl.LocalAssum (na, t) :: acc) c
      | LetIn (na, v, t, c) -> peel (i + 1) (RelDecl.LocalDef (na, v, t) :: acc) c
      | _ -> raise Fallback
  in
  peel 0 [] body

(* The named block and the body under it. *)
type split = {
  ctx : rel_context; (* the named block, innermost first *)
  rest : constr; (* the body under it *)
  named : int array; (* the positions in the block of its variables *)
  kept : int array; (* the positions of the other binders *)
}

(* [split decls body rest]: for the block [decls] of [body], with [rest]
   under it (from [peel]), the named block: its assumptions before the
   first one whose type mentions a local definition of the block (the
   header says why), at least one. The body under it is the other binders
   of the block, in their order, around [rest]. When the named block is
   the first binders of the block, that is [body] under them; else its
   terms are re-indexed, in one pass over [rest]: the named block first,
   the other binders after it, which none of the named types mentions. A
   term at position [p] of the block (under its binders before [p])
   mentions the binder at position [i] as Rel [p - i] at depth 0; under
   [named] variables of the named block, then [kept] other binders, that
   is Rel [kept + named - j] for the [j]th variable and Rel [kept - j] for
   the [j]th other binder, from 0. *)
let split decls body rest =
  let n = Array.length decls in
  let is_let i = i >= 0 && RelDecl.is_local_def decls.(i) in
  let mentions_let i t =
    let exception Found in
    let memo = Memo.create ~size:16 () in
    let rec walk k c = match kind c with
      | Rel r -> if r > k && is_let (i - (r - k)) then raise Found
      | _ when is_leaf c -> ()
      | _ -> memoized memo k c (fun () -> Constr.iter_with_binders succ walk k c)
    in
    match walk 0 t with
    | () -> false
    | exception Found -> true
  in
  let rec cut i =
    if Int.equal i n then n
    else match decls.(i) with
      | RelDecl.LocalAssum (_, t) when mentions_let i t -> i
      | RelDecl.LocalAssum _ | RelDecl.LocalDef _ -> cut (i + 1)
  in
  let cut = cut 0 in
  let is_named i = i < cut && RelDecl.is_local_assum decls.(i) in
  let positions = List.init n Fun.id in
  let named = Array.of_list (List.filter is_named positions) in
  let kept = Array.of_list (List.filter (fun i -> not (is_named i)) positions) in
  let m = Array.length named in
  let () = if Int.equal m 0 then raise Fallback in
  if Int.equal named.(m - 1) (m - 1) then
    let rec under i c =
      if Int.equal i m then c
      else match kind c with
        | Lambda (_, _, c) | LetIn (_, _, _, c) -> under (i + 1) c
        | _ -> raise Fallback
    in
    let ctx = List.rev (Array.to_list (Array.sub decls 0 m)) in
    { ctx; rest = under 0 body; named; kept }
  else
    let index = Array.make n 0 in
    let () = Array.iteri (fun j i -> index.(i) <- j) named in
    let () = Array.iteri (fun j i -> index.(i) <- j) kept in
    let visit c = if not (canonical c) then raise Fallback in
    let reindex ~p ~named:nn ~kept:nk t =
      subst_rels ~visit (fun k r ->
          let i = p - r in
          let () = if i < 0 then raise Fallback in
          let s = if is_named i then nk + nn - index.(i) else nk - index.(i) in
          let () = if s <= 0 then raise Fallback in
          mkRel (k + s)) t
    in
    let ctx = List.rev (Array.to_list (Array.mapi (fun j i ->
        RelDecl.map_constr (reindex ~p:i ~named:j ~kept:0) decls.(i)) named)) in
    let kept_ctx = List.rev (Array.to_list (Array.mapi (fun j i ->
        RelDecl.map_constr (reindex ~p:i ~named:m ~kept:j) decls.(i)) kept)) in
    let rest = reindex ~p:n ~named:m ~kept:(Array.length kept) rest in
    { ctx; rest = Term.it_mkLambda_or_LetIn rest kept_ctx; named; kept }

(* [statement_in_block env ctx ty]: [ty] under the named block [ctx], [env]
   the environment before the block.

   The statement abstracts the section variables but substitutes the
   section [Let]s ([Cooking.abstract_as_type]: [it_mkProd_wo_LetIn]), so
   each assumption of the block takes one product of [ty], in order, and
   the named block takes its first ones. [ty] is closed
   ([check_constant_declaration] typed it in an empty context), so what is
   left is under the named block.

   The stock check compares the type of the whole body with [ty] by
   [conv_leq], which compares the domains of two products with CONV
   ([Conversion.ccnv]), in the binders before them, where the type of the
   body has the [Let]s substituted ([Typeops.execute] of LetIn). Each
   domain of the named block is compared here with CONV with the type of
   its variable, which mentions no [Let] ([split]), in the variables
   before it; the stock check compares the others itself, with the
   statement under the named block. [prepare] typed the named block
   before, and the domains are compared in order, so each is well typed in
   the variables before it. *)
let statement_in_block env ctx ty =
  let rec walk env ty = function
    | [] -> ty
    | d :: ctx ->
      match kind ty with
      | Prod (_, dom, ty) ->
        let () = match Conversion.conv env (RelDecl.get_type d) dom with
          | Result.Ok () -> ()
          | Result.Error () -> raise Fallback
        in
        walk (push_rel d env) ty ctx
      | _ -> raise Fallback
  in
  walk env ty (List.rev ctx)

(* [subst ids n key ~spend ~size t]: [t], a term under the first [n]
   variables of the named block, in the named form ([prepare]): the Rel of
   the variable at position [i] (from 0, the outermost), Rel [k + n - i] at
   binder depth [k] in [t], becomes [Var ids.(i)], and a Rel free beyond
   those variables skips them; and a node [c] at depth [k] for which
   [key k c] is [Some (c', p)], an occurrence [c xs rest] of a key with [p]
   arguments, becomes [c' rest]. The other nodes are rebuilt by
   [map_with_binders], which goes under the binders of case branches,
   return clauses and fixpoint bodies. [spend ()] runs at each node that it
   computes. The memo starts with [size] slots: [prepare] gives few to the
   named block and to the value and type of a key, which are mostly small,
   and many to the body and the statement. *)
let subst ids n key ~spend ~size =
  let memo = Memo.create ~size mkProp in
  let rec go k c = match kind c with
    | Rel r ->
      if r <= k then c
      else if r <= k + n then mkVar ids.(k + n - r)
      else mkRel (r - n)
    | _ when is_leaf c -> c
    | _ ->
      memoized memo k c (fun () ->
          spend ();
          match key k c with
          | Some (cst, p) ->
            let args = snd (destApp c) in
            let rest = Array.sub args p (Array.length args - p) in
            mkApp (mkConstU (cst, UVars.Instance.empty), Array.map (go k) rest)
          | None -> map_with_binders succ go k c)
  in
  go 0

(* Test only. [put_back index keys ~size n t]: [t], in the named form
   ([prepare]) under the first [n] variables of the named block, with each
   variable whose position in the named block [index] gives as [i < n] put
   back as the Rel of that variable, each constant of a key put back as the
   application of its key ([keys]), and its other free Rels moved past the
   [n] variables; its memo starts with [size] slots. It is written apart
   from [subst] on purpose, sharing none of its code but the memo,
   [memoized] and [is_leaf]: [put_back_check] uses it as the oracle that
   [subst]'s result is checked against. *)
let put_back index keys ~size n =
  let memo = Memo.create ~size mkProp in
  let rec go k c = match kind c with
    | Rel r -> if r <= k then c else mkRel (r + n)
    | Var id ->
      begin match Id.Map.find_opt id index with
      | Some i when i < n -> mkRel (k + n - i)
      | Some _ | None -> c
      end
    | Const (cst, _) ->
      begin match CstTbl.find_opt keys cst with
      | Some (cst, args) ->
        mkApp (mkConstU (cst, UVars.Instance.empty), Array.map (fun a -> mkRel (a + k)) args)
      | None -> c
      end
    | _ when is_leaf c -> c
    | _ -> memoized memo k c (fun () -> map_with_binders succ go k c)
  in
  go 0

(* Test only. [unsplit sp]: the cooked body from the named block and the
   body under it, by the positions of [sp] alone: a term at position [p]
   of the block mentions, as Rel [r] at depth 0 below [named] variables and
   [kept] other binders, the [kept - r]th other binder if [r <= kept], and
   else the [named - (r - kept)]th variable; it is written apart from the
   re-indexing of [split], as [put_back] is from [subst]. *)
let unsplit sp =
  let m = Array.length sp.named and h = Array.length sp.kept in
  let back ~p ~named ~kept t =
    subst_rels ~visit:ignore (fun k r ->
        let i = if r <= kept then sp.kept.(kept - r) else sp.named.(named - (r - kept)) in
        mkRel (k + p - i)) t
  in
  let decls = Array.make (m + h) (List.hd sp.ctx) in
  let () = List.iteri (fun j d ->
      let j = m - 1 - j in
      decls.(sp.named.(j)) <- RelDecl.map_constr (back ~p:sp.named.(j) ~named:j ~kept:0) d)
      sp.ctx
  in
  let rec peel_kept j c =
    if Int.equal j h then Some c
    else
      let i = sp.kept.(j) in
      let decl d c =
        decls.(i) <- RelDecl.map_constr (back ~p:i ~named:m ~kept:j) d;
        peel_kept (j + 1) c
      in
      match kind c with
      | Lambda (na, t, c) -> decl (RelDecl.LocalAssum (na, t)) c
      | LetIn (na, v, t, c) -> decl (RelDecl.LocalDef (na, v, t)) c
      | _ -> None
  in
  Option.map (fun rest ->
      Term.it_mkLambda_or_LetIn (back ~p:(m + h) ~named:m ~kept:h rest)
        (List.rev (Array.to_list decls)))
    (peel_kept 0 sp.rest)

(* The variable at position [i] (from 0, the outermost) of the named block,
   and the constant of the [j]th key. *)
let block_id i = Id.of_string ("rocqchk_block_" ^ string_of_int i)

let key_modpath = ModPath.MPfile (DirPath.make [Id.of_string "rocqchk_discharged_keys"])

let key_constant j =
  Constant.make1 (KerName.make key_modpath (Id.of_string ("key_" ^ string_of_int j)))

type prepared = {
  body : constr; (* the cooked body *)
  split : split;
  env' : env; (* the named block, then the keys' constants *)
  rest' : constr; (* [split.rest], named, with the keys bound *)
  concl : types; (* the statement under the named block *)
  concl' : types; (* the same, named, with the keys bound *)
  ids : Id.t array; (* the variables of the named block, the outermost first *)
  constants : Constant.t array; (* the constants of the keys *)
  bindings : binding array;
}

(* [prepare env ci n body ty]: the body and the statement under the named
   block, rewritten, and the environment in which [check] runs the stock
   check on them.

   The named block's variable at position [i] (from 0, the outermost)
   becomes the assumption [block_id i] of the environment, with its
   relevance and its type in the named form ([subst]). The [j]th binding
   becomes the constant [key_constant j]: its section hypotheses are the
   variables that its key applies [c] to, in the order of the named block,
   each the very declaration pushed; its value is the key's value and its
   type the key's type, both in the named form with the keys before it
   bound; its relevance is [c]'s; it has no universe, no code, and the
   typing flags of the body. The constants are added to the environment
   unchecked: their values are never typed ([find_keys]). They are outside
   every fixpoint of the body.

   That is the form in which coqc checks the body at Qed inside the
   section, where [c]'s section hypotheses are its own variables, and the
   stock check accepts the cooked body whenever it accepts it: [put_back],
   which puts back the named block's Rels for its variables and [c xs] for
   each [c'], and [unsplit] map each step of the rewritten check to a step
   of the stock check on the cooked body. Typing [c'] checks that the
   environment holds its hypotheses ([Typeops.check_hyps_inclusion]), which
   it does: each is a declaration of the named block, which the environment
   holds as it is, so the lookup finds it and its type is compared with
   itself. A key's value and type mention, of the named block, only the
   variables of the key ([unfold], [find_keys]), and, of the keys' constants,
   only those of keys before it, whose variables are among the key's, as
   inside the section a constant's body and type mention only its own
   variables and constants declared before it. Typing [c'] gives the type
   that typing [c xs] gives ([find_keys] typed it); unfolding [c']
   gives the term that unfolding [c] reaches at [xs] ([unfold]); a variable
   of the named block has the type and the relevance of its Rel, and no
   value; the other binders of the block are binders of the rewritten body,
   as they were of the cooked one; and the guard checker unfolds [c'] as it
   unfolds [c], and treats a variable of the named block as the Rel of an
   assumption ([Inductive]: the [Const], [Var] and [Rel] cases of
   [check_one_fix] and [check_one_cofix], and [whd_all] in
   [subterm_specif]).

   No term that the check reads but the rewritten ones names these
   variables or constants. [find_keys] gives up on a [Var] in a term that
   it reads, and on a constant or an inductive whose section hypotheses
   typing would check against the named block. A library that rocqchk
   checks holds no [Var] (typing one in an empty named context fails), and
   names no constant that the environment does not hold: rocqchk checks a
   constant whose canonical name is not its user name as an alias of the
   environment's constant of that name ([Subtyping.check_constant_alias]).
   So this gives up when the environment holds the name of a key's
   constant ([mem_constant]), and [check] gives up on an environment with
   a named variable. A library that rocqchk admits without checking is
   trusted here as everywhere.

   Each key's constant has the default level in the oracle (else this
   gives up). Conversion asks the oracle which of two heads to unfold when
   both have a value ([Conversion.eqwhnf], [Conv_oracle.oracle_order]): a
   constant at its level, and a Rel bound to a local definition as [None],
   which [oracle_order] treats as [Expand] (projections are no such heads
   there). The rewritten check changes these heads in one way only: [c] at
   the default level ([key_values]) is [c'] at the default level, which
   [oracle_order] and [dep_order] order as [c] against every head: against
   a Rel by the levels, and against a constant [g], another key's constant
   included, by [l2r] at equal levels. The local definitions of the block
   are Rels of let-ins in both checks, and a variable of the named block
   has no value, as its Rel, so every other pair of heads is the stock
   check's. The verdict does not depend on the order anyway
   ([key_values]). *)
let prepare env ci n body ty =
  let decls, rest = peel n body in
  let sp = split decls body rest in
  let m = Array.length sp.named in
  let ks = search env ci m in
  let () = if not (has_key ks sp.rest) then raise Fallback in
  (* The named block typed in one pass, as the product of its variables
     over Prop: [Typeops.infer_type] checks the universes of all their
     types at once, and its [execute] of Prod types each type in the
     variables before it with the [execute_is_type] and [check_assum_annot]
     that the stock check's [execute] of Lambda uses; the sort of a product
     ([sort_of_product]) and the type of Prop refuse nothing. That refuses
     what [Typeops.check_context] refuses, which types each variable apart,
     and whose [HConstr.of_constr] then enters every Rel before it, the
     square of the size of the block. *)
  let _ : unsafe_type_judgment = Typeops.infer_type env (Term.it_mkProd_or_LetIn mkProp sp.ctx) in
  let env_block = push_rel_context sp.ctx env in
  let concl = statement_in_block env sp.ctx ty in
  let keys, bindings, spend = find_keys ks env_block sp.ctx [sp.rest; concl] in
  (* With no key there is nothing to share, and the stock check runs. *)
  let () = if Array.is_empty bindings then raise Fallback in
  let ids = Array.init m block_id in
  let bind_none _ _ = None in
  let block = List.mapi (fun i d ->
      let na = Context.make_annot ids.(i) (RelDecl.get_relevance d) in
      NamedDecl.LocalAssum (na, subst ids i bind_none ~spend:ignore ~size:16 (RelDecl.get_type d)))
      (List.rev sp.ctx)
  in
  let env_named = List.fold_left (fun env d -> push_named d env) env block in
  let constants = Array.init (Array.length bindings) key_constant in
  let fresh c' =
    not (mem_constant c' env)
    && Conv_oracle.is_transparent (Conv_oracle.get_strategy (oracle env) (Conv_oracle.EvalConstRef c'))
  in
  let () = if not (Array.for_all fresh constants) then raise Fallback in
  (* [bound j]: the [key] of [subst] that binds the first [j] keys *)
  let bound j k c = match key_of ks k c with
    | Some key ->
      begin match KeyTbl.find_opt keys key with
      | Some i when i < j -> Some (constants.(i), Array.length (snd key))
      | Some _ | None -> None
      end
    | None -> None
  in
  let flags = typing_flags env in
  let env' = Array.fold_left_i (fun j env b ->
      let sub = subst ids m (bound j) ~spend ~size:16 in
      (* the declarations of the key's variables, the innermost first as in
         a named context: Rel [r] at depth 0 is the variable at position
         [m - r] *)
      let own = Array.make m false in
      let () = Array.iter (fun r -> own.(m - r) <- true) (snd b.key) in
      let hyps = List.fold_left_i (fun i hyps d -> if own.(i) then d :: hyps else hyps) 0 [] block in
      let cb = {
        const_hyps = hyps;
        const_univ_hyps = UVars.Instance.empty;
        const_body = Def (sub b.value);
        const_type = sub b.typ;
        const_relevance = b.relevance;
        const_body_code = None;
        const_universes = Monomorphic;
        const_inline_code = false;
        const_typing_flags = flags;
      } in
      add_constant constants.(j) cb env)
      env_named bindings
  in
  let subst_root = subst ids m (bound (Array.length bindings)) ~spend:ignore ~size:1024 in
  { body; split = sp; env'; rest' = subst_root sp.rest; concl; concl' = subst_root concl;
    ids; constants; bindings }

(* Test only: [put_back] gives back from what [stock] checks in [check],
   and from what the environment holds for it, the body and the statement
   under the named block, the named block itself, and each key's value and
   type; and [unsplit] gives back the cooked body from the named block and
   the body under it. *)
let put_back_check p =
  let keys = CstTbl.create (Array.length p.constants) in
  let () = Array.iteri (fun j c' -> CstTbl.add keys c' p.bindings.(j).key) p.constants in
  let index = Array.fold_left_i (fun i m id -> Id.Map.add id i m) Id.Map.empty p.ids in
  let put_back = put_back index keys in
  let back = put_back ~size:1024 (Array.length p.ids) in
  let differs what =
    CErrors.anomaly Pp.(str "discharged check: " ++ str what ++ str " differs from the cooked one.")
  in
  let () = if not (Constr.equal (back p.rest') p.split.rest) then differs "the rewritten body" in
  let () = if not (Constr.equal (back p.concl') p.concl) then differs "the rewritten statement" in
  let () = List.iteri (fun i d ->
      let back = put_back ~size:16 i in
      let t = NamedDecl.get_type (lookup_named p.ids.(i) p.env') in
      if not (Constr.equal (back t) (RelDecl.get_type d)) then differs "a variable of the named block")
      (List.rev p.split.ctx)
  in
  let () = Array.iteri (fun j c' ->
      let cb = lookup_constant c' p.env' in
      let b = p.bindings.(j) in
      match cb.const_body with
      | Def v when Constr.equal (back v) b.value && Constr.equal (back cb.const_type) b.typ -> ()
      | _ -> differs "the value or the type of a key")
      p.constants
  in
  match unsplit p.split with
  | Some body when Constr.equal body p.body -> ()
  | Some _ | None -> differs "the body under the named block"

let check env sub ci body ty ~stock =
  let n = List.fold_left (fun n info ->
      n + Id.Set.cardinal (Cooking.names_info info)) 0 ci
  in
  (* The early exits, for which the stock check runs on the cooked body at
     once:
     - without [share_reduction] the lazy machine keeps no value, a
       constant's no more than any other;
     - with rewrite rules allowed, the order of unfolding that a binding can
       change may change the verdict ([key_values], [prepare]);
     - a body with no block was not discharged;
     - a body under a module substitution, as one of a module that an
       [Include] copies, names its section constants otherwise than its
       cooking information does ([CheckLibrary.indirect_accessor]), so
       nothing would be bound;
     - an environment with a named variable is not one that the named block
       can extend ([prepare]).
     Otherwise the stock check runs on the cooked body once, unless it
     accepted the rewritten one. *)
  let shared () =
    (typing_flags env).share_reduction && not (rewrite_rules_allowed env) && n > 0
    && List.is_empty sub && List.is_empty (named_context env)
    && match attempt (fun () -> prepare env ci n body ty) with
    | None -> false
    | Some p ->
      let () = if cross_check_on then put_back_check p in
      (* The very same check as the stock check of the cooked body, run on
         the rewritten body and statement under the named block ([prepare]
         says why it accepts only what the stock check accepts). *)
      Option.has_some (attempt (fun () -> stock p.env' p.rest' p.concl'))
  in
  if not (shared ()) then stock env body ty
