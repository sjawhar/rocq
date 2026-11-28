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

module RelDecl = Context.Rel.Declaration

(* The key search of [CheckDischarged]: which applications of section
   constants the check of a discharged body binds, and their values and
   types. checkDischarged.ml says what a key is, in which form the body is
   checked, and why that keeps the verdict. Every term here is under the
   named block ([CheckDischarged.split]): its Rel [r] at binder depth [k],
   [k < r <= k + n], is the variable at position [k + n - r] (from 0, the
   outermost) of the [n] variables of that block. *)

exception Fallback

(* A memo from a compound term at a binder depth to a value, the terms
   compared physically. The cooked body is a shared graph whose tree
   unfolding can be exponential (cooking keeps the sharing of the stored
   proof, [Cooking.abstract_as_body_shared]), and so can be the body of a
   section constant, so each pass visits a node once per depth.

   The same code as [Cooking.ShareMemo] (kernel/cooking.ml, which does not
   export it), whose caller's depth [-1] entries are not used here; [create]
   also takes a starting size, and the values are of any type. Exporting
   [ShareMemo] would change kernel/cooking.mli, which this change leaves
   as it is (the kernel, and so what rocq compile links, is P's), so the
   copy stays. The memo is lossy: a lookup probes a fixed number of slots,
   and an entry whose slots are all taken overwrites the first of them, so
   terms that share a hash cost a recomputation, never a long scan.
   [Constr.hash_bounded] gives one hash to every cell of a long uniform
   chain and to every sibling of a wide node, which a table with buckets
   would scan whole at each lookup. Losing an entry is safe in each use:
   [subst_rels] and the substitutions of checkDischarged.ml compute the
   same term again, [holds_key], [cast_gate] and [type_heads] walk the
   node again, [value_heads] makes the node a second vertex, whose paths
   from the root and those of the first are the paths to the node, and
   [find_keys] only scans the node again, where it notes again what it has
   noted and [bind] does nothing for a key it has met already. A pass that
   counts against the budget ([budget_floor]) counts such a node again,
   which can only make it fall back sooner; the scan of the roots counts
   it again among the nodes of the roots ([incr root_nodes] in
   [find_keys]), which can raise the budget by [budget_factor] nodes, and
   so can only make it fall back later. Neither changes a verdict, and
   which entries are lost depends on the file only. *)
module Memo = struct
  type 'a t = {
    mutable keys : constr array;
    mutable depths : int array;
    mutable values : 'a array;
    mutable count : int;
    empty : 'a; (* the value of a free slot *)
  }

  (* never a key: only compound terms are entered *)
  let no_key = mkProp
  let probes = 8
  let max_size = 1 lsl 22

  let make size empty =
    { keys = Array.make size no_key; depths = Array.make size 0;
      values = Array.make size empty; count = 0; empty }

  (* [size], a power of two, is the number of slots to start with; [add]
     doubles it as the memo fills. [empty] is any value of the type. *)
  let create ?(size = 1024) empty = make size empty

  (* [h] is [Constr.hash_bounded c] *)
  let find m h c k =
    let mask = Array.length m.keys - 1 in
    let h = Hashset.Combine.combine h k in
    let rec probe i =
      if Int.equal i probes then None
      else
        let j = (h + i) land mask in
        let key = Array.unsafe_get m.keys j in
        if key == no_key then None
        else if key == c && Int.equal (Array.unsafe_get m.depths j) k then
          Some (Array.unsafe_get m.values j)
        else probe (i + 1)
    in
    probe 0

  let insert m h c k v =
    let mask = Array.length m.keys - 1 in
    let h = Hashset.Combine.combine h k in
    let rec probe i =
      if Int.equal i probes then h land mask (* all taken: overwrite the first *)
      else
        let j = (h + i) land mask in
        if Array.unsafe_get m.keys j == no_key then (m.count <- m.count + 1; j)
        else probe (i + 1)
    in
    let j = probe 0 in
    Array.unsafe_set m.keys j c;
    Array.unsafe_set m.depths j k;
    Array.unsafe_set m.values j v

  let add m h c k v =
    let size = Array.length m.keys in
    if 2 * m.count >= size && size < max_size then begin
      let keys = m.keys and depths = m.depths and values = m.values in
      let m' = make (2 * size) m.empty in
      m.keys <- m'.keys; m.depths <- m'.depths; m.values <- m'.values; m.count <- 0;
      Array.iteri (fun j key ->
          if key != no_key then
            insert m (Constr.hash_bounded key) key depths.(j) values.(j)) keys
    end;
    insert m h c k v
end

(* [memoized m k c f]: what [m] holds for the compound term [c] at depth
   [k], or else [f ()], which [m] then holds. Every pass looks its memo up
   through it, so each gives [Memo] the hash it expects, and enters a node
   once [f] has gone through the node's subterms, as
   [Cooking.expand_constr_shared] enters a term once expanded: the entry
   made last is never lost, so a node that two neighbouring subterms share,
   as in [f x x], is found again even when its own subterms share its
   hash. A term has no cycle, so [f] never meets [c] again. *)
let memoized m k c f =
  let h = Constr.hash_bounded c in
  match Memo.find m h c k with
  | Some v -> v
  | None ->
    let v = f () in
    Memo.add m h c k v;
    v

let is_leaf c = match kind c with
  | Rel _ | Var _ | Meta _ | Sort _ | Const _ | Ind _ | Construct _
  | Int _ | Float _ | String _ -> true
  | Evar _ | Cast _ | Prod _ | Lambda _ | LetIn _ | App _ | Case _ | Fix _
  | CoFix _ | Proj _ | Array _ -> false

(* [subst_rels ~visit f t]: [t] with each Rel [r] that is free at binder
   depth [k] in it ([r > k]) replaced by [f k (r - k)], a term at depth
   [k]. This is [Vars.substl] with a memo, so it keeps the sharing of [t].
   [visit c] runs at each compound node [c] of [t] that it computes. Its
   memo starts with [subst_memo_size] slots, as that of [value_heads],
   which so computes the same nodes. *)
let subst_memo_size = 16

let subst_rels ~visit f t =
  let memo = Memo.create ~size:subst_memo_size mkProp in
  let rec go k c = match kind c with
    | Rel r -> if r <= k then c else f k (r - k)
    | _ when is_leaf c -> c
    | _ -> memoized memo k c (fun () -> visit c; map_with_binders succ go k c)
  in
  go 0 t

(* A key: a section constant applied to variables of the named block, given
   by their Rels at depth 0 ([head]). Two occurrences have the same
   key when their constants have the same user name, by which the
   environment looks a constant up, and the same canonical name, which
   typing checks ([Typeops.check_constant]) and conversion compares, and
   the same variables. [Constr.equal] compares canonical names only, so it
   would merge occurrences that the stock check treats apart. *)
type key = Constant.t * int array

let same_constant c1 c2 =
  Constant.UserOrd.equal c1 c2 && Constant.CanOrd.equal c1 c2

module KeyTbl = Hashtbl.Make (struct
    type t = key
    let equal (c1, a1) (c2, a2) = same_constant c1 c2 && Array.equal Int.equal a1 a2
    let hash (c, a) =
      Array.fold_left Hashset.Combine.combine (Constant.UserOrd.hash c) a
  end)

(* Constants, compared as keys compare them. *)
module CstTbl = Hashtbl.Make (struct
    type t = Constant.t
    let equal = same_constant
    let hash = Constant.UserOrd.hash
  end)

(* [section ci]: how the cookings [ci] of the body apply an object, the
   number of arguments for a constant ([arity]), and whether any for an
   inductive ([inductive]). A cooking that expands an object of its section
   puts it applied to the section variables that the object was abstracted
   over, local definitions excluded ([Cooking.make_cooking_info]), as Rels
   of the block. Each cooking of the body, from the outermost, so adds
   arguments, and every occurrence of a section constant [c] in the cooked
   terms is [c] applied to all of them, then to what the section applied it
   to. A cooking adds as many as [Cooking.expand_subst] gives the object
   alone ([c] itself for none): none to an object of a section that was
   closed before, to one from outside these sections, or to a section
   constant that uses no section variable. A constant that no cooking
   applies to variables is called a global constant below. Each cache is
   made once per check, and each arity computed once. [Cooking.expand_subst]
   raises on cooking information that a forged file holds, which
   [CheckDischarged.check] meets inside [attempt]. *)
type section = {
  arity : Constant.t -> int;
  inductive : inductive -> bool;
}

let section ci =
  let caches = List.map Cooking.create_cache ci in
  let count t = List.fold_left (fun p cache ->
      match kind (Cooking.expand_subst cache t) with
      | App (_, args) -> p + Array.length args
      | _ -> p) 0 caches
  in
  let arities = CstTbl.create 64 in
  let arity cst = match CstTbl.find_opt arities cst with
    | Some p -> p
    | None ->
      let p = count (mkConstU (cst, UVars.Instance.empty)) in
      let () = CstTbl.add arities cst p in
      p
  in
  let inductive ind = count (mkIndU (ind, UVars.Instance.empty)) > 0 in
  { arity; inductive }

type binding = {
  key : key;
  value : constr; (* under the named block *)
  typ : types; (* under the named block *)
  relevance : Sorts.relevance;
}

let key_term (cst, args) = mkApp (mkConstU (cst, UVars.Instance.empty), Array.map mkRel args)

(* Whether the kernel's constructors build [c] as it is ([Constr.of_kind]
   flattens an application whose function is an application, drops one with
   no argument, and collapses two stacked casts of the same kind, VM or
   native). The substitutions rebuild the nodes they change with those
   constructors, and [CheckDischarged.put_back_check] compares the result
   with [Constr.equal]. Rebuilding a stacked cast of one kind drops the
   inner cast, whose check the stock check makes, so this guards the
   verdict too. The scans of [find_keys] check it on the terms they read,
   and [CheckDischarged.split] on those it re-indexes. coqc builds every
   term so, and a .vo file that holds another runs the stock check. *)
let canonical c = match kind c with
  | App (f, args) -> not (Array.is_empty args) && not (isApp f)
  | Cast (c, (VMcast | NATIVEcast as knd), _) ->
    (match kind c with Cast (_, knd', _) -> knd' != knd | _ -> true)
  | _ -> true

(* [head n k c]: when [c], at binder depth [k] below [n] binders, is a
   constant at the empty instance applied first to Rels of those binders,
   the constant and the number [l] of those Rels before its other
   arguments. Under the named block, [c] is a key ([search]: [is_key],
   [key_of]) when the cookings of the body apply its constant to [a]
   arguments, [0 < a <= l], and [key_values] binds it: the constant and the
   variables of its first [a] arguments, followed by more arguments or
   none. Each occurrence of a section constant in the cooked terms is so
   ([section]) when the variables that the cookings give it are named. The
   named block holds no local definition, and a key never takes one: the
   cookings apply a constant to section variables only, and a Rel of a
   local definition of the block is no variable of the named block. An
   application of a global constant is no key (checkDischarged.ml says
   why), nor is one of a constant at another instance: a key holds no
   instance, so binding one is outside the scope of this check. *)
type head = Constant.t * int

let head n k c = match kind c with
  | App (f, args) ->
    begin match kind f with
    | Const (cst, u) when UVars.Instance.is_empty u ->
      let bound a = match kind a with Rel r -> k < r && r <= k + n | _ -> false in
      let rec lead i = if i < Array.length args && bound args.(i) then lead (i + 1) else i in
      let l = lead 0 in
      if l > 0 then Some (cst, l) else None
    | _ -> None
    end
  | _ -> None

(* [key_values env sec]: for a section constant [c], [Some v] when a key
   [c xs] of it can be bound, [v] being what is left of [c]'s body after
   the Lambdas that [xs] take; [None] otherwise. It reads [c]'s declaration
   and those Lambdas only, once per constant, so [prepare] asks it before
   it types the block. A key can be bound when:
   - [c]'s body is [Def], with at least as many leading Lambdas as [xs]:
     an opaque body never unfolds;
   - [c]'s code, if it has some, marks no argument after [xs] unused (the
     VM meets [c'] only as an atom, [cast_gate], so only the mask of the
     code matters here). Typed conversion ([Conversion.default_conv], by
     which typing compares the type of an argument, of a let-in's value or
     of a cast with the type it expects there) compares [c xs rest] with
     [c xs rest'] without the arguments that the mask of [c]'s code marks
     [false]: the argument at position [i], counted from [c], is skipped
     when [i < Array.length mask] and [not mask.(i)]
     ([CClosure.get_ref_mask], then [Conversion.convert_stacks]). [c'] has
     no code, and a constant with none has no mask ([CClosure.drop_code]),
     so [c' rest] against [c' rest'] compares those arguments as well,
     which can take far longer than the whole stock check. The checker
     compiles every constant whether the VM is on or not
     ([Safe_checking.compile_vm_library]), so this holds with the VM off
     too. A mask that is not empty ends with [false] ([Vmbytegen.compile]
     drops the [true]s at its end), so it marks an argument after [xs]
     unused exactly when it is longer than [xs];
   - [v] is not a function (Lambda, Fix or CoFix). Such a value is in weak
     head normal form already, and each application reduces its body anew,
     so binding it shares no reduction;
   - [c] has the default Strategy level ([Conv_oracle.is_transparent]),
     which [c'] has too, so that conversion unfolds [c'] where the stock
     check unfolds [c] ([CheckDischarged.prepare]).
   The last three are for speed, not for the verdict: the verdict depends
   neither on the order in which conversion unfolds constants nor on the
   arguments that it compares before it unfolds both sides, as long as
   reduction is confluent, which rewrite rules need not be (nothing is
   bound when they are allowed). For the same reason, two keys of one
   constant, which conversion compares by unfolding where it compares the
   arguments of [c xs] and [c ys], change no verdict. *)
let key_values env sec =
  let values = CstTbl.create 64 in
  let value cst =
    let cb = lookup_constant cst env in
    let p = sec.arity cst in
    let transparent =
      Conv_oracle.is_transparent
        (Conv_oracle.get_strategy (oracle env) (Conv_oracle.EvalConstRef cst))
    in
    let mask_ok = match cb.const_body_code with
      | Some (Vmemitcodes.BCdefined (mask, _, _)) -> Array.length mask <= p
      | Some (Vmemitcodes.BCalias _ | Vmemitcodes.BCconstant) | None -> true
    in
    let rec strip i c =
      if Int.equal i p then
        match kind c with
        | Lambda _ | Fix _ | CoFix _ -> None
        | _ -> Some c
      else match kind c with
        | Lambda (_, _, c) -> strip (i + 1) c
        | _ -> None
    in
    match cb.const_body with
    | Def body when transparent && mask_ok -> strip 0 body
    | Def _ | Undef _ | OpaqueDef _ | Primitive _ | Symbol _ -> None
  in
  fun cst -> match CstTbl.find_opt values cst with
    | Some v -> v
    | None ->
      let v = value cst in
      let () = CstTbl.add values cst v in
      v

(* [unfold ~spend key v]: the value of [key], [v] from [key_values] with
   the key's variables put in place of the Lambdas: the term that the lazy
   machine reaches from each occurrence. Rel [i] of [v] is the [i]th of
   those Lambdas from the innermost, which takes the [i]th of [xs] from the
   last. Its free Rels are the key's variables only: [c]'s body is closed.
   So a value, and a type ([find_keys]), never mention a local definition
   of the block: a cooked body carries its own section [Let]s as let-ins
   inside it, and a cooked type substitutes them. *)
let unfold ~spend (_, args) v =
  let p = Array.length args in
  let at k i = mkRel (k + (if i <= p then args.(p - i) else i - p)) in
  subst_rels ~visit:(fun _ -> spend ()) at v

(* [holds_key key_of memo k t]: whether a key ([key_of]) occurs in [t] at
   depth [k]. [memo] holds the nodes found to hold none, as a node that
   holds one ends the walk; [has_key] and [cast_gate] share it ([search]),
   as both ask with the same [key_of]. *)
let holds_key key_of memo =
  let exception Found in
  let rec walk k c =
    if not (is_leaf c) then
      memoized memo k c (fun () ->
          if Option.has_some (key_of k c) then raise Found;
          Constr.iter_with_binders succ walk k c)
  in
  fun k t -> match walk k t with
    | () -> false
    | exception Found -> true

(* [cast_gate ~spend holds roots]: falls back when a VM or native cast in
   [roots] can reach a key ([holds]), with the VM or the native compiler on
   (native conversion runs the VM when the native compiler is off,
   [Nativeconv.native_conv_gen]). Typing a cast runs the compiled
   conversion on the type inferred for its term and on its type
   ([Typeops.check_cast]). That keeps a constant with no code, as [c'], as
   an atom ([Vmsymtable.slot_for_getglobal]), and a match on the atom is
   stuck; when both sides are stuck on it, [Vconv] compares every branch,
   and so runs code that the stock check, where [c xs] computes to one
   constructor, never runs: that can take far longer than the whole stock
   check. A cast reaches a key when its subterm holds one, or when one of
   its free Rels is bound in [roots] by a binder that reaches one: the
   value or the type of a let-in, which the VM evaluates for its Rel and
   typing gives as the Rel's type; the type of a Lambda or a product, which
   typing gives its Rel; the parameters of a match, from which typing gives
   the types, and the let-in values, of the binders of its return clause
   and branches; the types of a fixpoint, which typing gives its names. A
   binder reaches a key when its terms hold one or mention, in turn, a Rel
   of a binder that reaches one. The named block's variables have no value,
   and their types hold no bound key ([find_keys]), so they reach none.

   The walk is bottom-up, so that it enters each node in its memo once per
   depth whatever binders are above it: for a node, the Rels free in it
   (as indices at the node) that feed a compiled cast in it, which are
   those that the cast would reach a key through. A binder whose Rel feeds
   a cast falls back when its terms hold a key, and else adds the Rels free
   in its terms. A cast that holds no key and whose free Rels reach none
   holds no [c'] once rewritten, and the compiled conversion runs on it as
   on the cooked one, the named block's variables standing for its Rels;
   so a proof whose casts come from tactics like lia, whose let-ins
   [__ff] and [__wit] hold no section definition, keeps its bindings.

   A set can hold a Rel for each binder above a cast, and it is rebuilt at
   each of those binders, so the work on the sets can grow as the square
   of the size of [roots] (a cast under thousands of binders whose type
   mentions them all). So each Rel that [free] or [above] moves into a new
   set costs a node of the budget ([spend], [budget_floor]). *)
let cast_gate ~spend holds roots =
  let union = Int.Set.union in
  (* the Rels free in a node, as indices at the node *)
  let free_memo = Memo.create Int.Set.empty in
  let rec free c = match kind c with
    | Rel r -> Int.Set.singleton r
    | _ when is_leaf c -> Int.Set.empty
    | _ ->
      memoized free_memo 0 c (fun () ->
          let acc = ref Int.Set.empty in
          Constr.iter_with_binders succ (fun nb c ->
              Int.Set.iter (fun r ->
                  if r > nb then (spend (); acc := Int.Set.add (r - nb) !acc)) (free c))
            0 c;
          !acc)
  in
  (* the Rels of [d], at a node below [nb] binders, that are free above
     them *)
  let above nb d =
    Int.Set.fold (fun r acc ->
        if r > nb then (spend (); Int.Set.add (r - nb) acc) else acc) d Int.Set.empty
  in
  let memo = Memo.create Int.Set.empty in
  let rec feeds k c = match kind c with
    | _ when is_leaf c -> Int.Set.empty
    | Cast (_, (VMcast | NATIVEcast), _) ->
      if holds k c then raise Fallback;
      free c
    | _ ->
      memoized memo k c (fun () -> match kind c with
          | LetIn (_, v, t, b) -> binders k [|v; t|] [|1, feeds (k + 1) b|]
          | Lambda (_, t, b) | Prod (_, t, b) -> binders k [|t|] [|1, feeds (k + 1) b|]
          | Case (_, _, pms, (p, _), iv, c, brs) ->
            let under (nas, t) =
              let nb = Array.length nas in
              nb, feeds (k + nb) t
            in
            let d = binders k pms (Array.append [|under p|] (Array.map under brs)) in
            let d = union d (feeds k c) in
            begin match iv with
            | NoInvert -> d
            | CaseInvert { indices } ->
              Array.fold_left (fun d i -> union d (feeds k i)) d indices
            end
          | Fix (_, (nas, tys, bds)) | CoFix (_, (nas, tys, bds)) ->
            let nb = Array.length nas in
            binders k tys (Array.map (fun b -> nb, feeds (k + nb) b) bds)
          | _ -> Constr.fold (fun d c -> union d (feeds k c)) Int.Set.empty c)
  (* [bts], at depth [k], give the binders of each body their types and
     values; each body is below [nb] binders, and feeds [db] *)
  and binders k bts bodies =
    let d = Array.fold_left (fun d t -> union d (feeds k t)) Int.Set.empty bts in
    let d = Array.fold_left (fun d (nb, db) -> union d (above nb db)) d bodies in
    let bound (nb, db) = not (Int.Set.is_empty db) && Int.Set.min_elt db <= nb in
    if not (Array.exists bound bodies) then d
    else if Array.exists (holds k) bts then raise Fallback
    else Array.fold_left (fun d t -> union d (free t)) d bts
  in
  List.iter (fun root -> ignore (feeds 0 root)) roots

(* The key search of one body: its [section], [key_values] and the keys
   that these bind ([head]), under a named block of [n] variables. *)
type search = {
  sec : section;
  values : Constant.t -> constr option;
  is_key : head -> bool;
  key_of : int -> constr -> key option;
  holds : int -> constr -> bool;
}

let search env ci n =
  let sec = section ci in
  let values = key_values env sec in
  let is_key (cst, l) =
    let a = sec.arity cst in
    0 < a && a <= l && Option.has_some (values cst)
  in
  let key_of k c = match head n k c with
    | Some ((cst, _) as h) when is_key h ->
      let args = snd (destApp c) in
      Some (cst, Array.init (sec.arity cst) (fun i -> destRel args.(i) - k))
    | Some _ | None -> None
  in
  { sec; values; is_key; key_of; holds = holds_key key_of (Memo.create ()) }

let key_of s = s.key_of

(* A body with no key that can be bound has nothing to share; [prepare]
   asks this before it types the block and reads the statement. *)
let has_key s t = s.holds 0 t

(* The work of [find_keys] and [CheckDischarged.prepare] outside the
   roots, the body and the statement, is bounded by the roots: past
   [max budget_floor (budget_factor * r)] nodes, [r] being the number of
   nodes that the scan of the roots enters, it falls back. The stock check
   reads the environment only where conversion unfolds, so a value, a
   body or the data of an inductive that it never needs costs it nothing,
   while reading it here can cost far more than the whole stock check (a
   lemma whose proof is eq_refl on a long section list, say). The nodes
   counted are those that a pass computes, once per node and depth with
   the memos: [unfold]'s substitution, the scans of values and types, the
   reading of the terms that are not rewritten, and [prepare]'s
   substitutions in values and types; and so is each Rel that [cast_gate]
   moves into a new set. The count is of nodes, not of time, so whether
   this falls back depends on the file only. The chain gate
   ([chain_gate]) spends from a copy of the same budget, apart, on the
   values that it reads and the heads that it examines, so it is bounded
   by the roots too.

   The bound comes from the proofs that take the rewritten check in three
   grade trees of dispatch://BET-1602, counted without the budget: the
   curl attempt's libraries AgentChain and AgentChainL (7 proofs), r188's
   release tree (BET-1599's tree-rel-2, 112 proofs) and the golden
   submission of the curl task (C_E, 10 proofs). Where the floor decides,
   the most work outside the roots is 2114 nodes (r188), a margin of 23;
   past 1000 nodes of roots it is at most 0.547 times the roots, and past
   5000, where the factor decides, at most 0.355 times (r188), a margin of
   28. *)
let budget_floor = 50_000
let budget_factor = 10

(* [unfold_costs] keeps, for each constant whose value [unfold] or the
   chain gate ([value_heads]) has walked in this process, what that cost:
   its number of nodes, or, where the budget ran out first, one more than
   the budget had left then, which is at most that number. That number
   depends only on the constant's body: a value is the body under all its
   leading Lambdas ([key_values]), and both walks enter each of its nodes
   once per depth, the nodes that [unfold] computes, whatever the key's
   variables that it puts in place. So [recorded] falls back before a walk
   when the cost kept for the constant exceeds the budget left, which is
   only where the walk would run out of the budget anyway: a value larger
   than the budget spends a whole budget once per process, not once per
   body, and whether this falls back still depends on the file only. What
   the scan of a value costs is not kept, as it depends on what the scans
   of the body entered before it. *)
let unfold_costs : int CstTbl.t = CstTbl.create 64

(* [recorded ~left cst walk]: [walk ()], a walk of the value of [cst] that
   spends from [!left], the budget left. It falls back first when
   [unfold_costs] keeps for [cst] a cost larger than [!left], and keeps
   there what [walk] cost, unless [walk] stops otherwise. *)
let recorded ~left cst walk =
  let had = !left in
  let () = match CstTbl.find_opt unfold_costs cst with
    | Some cost when cost > had -> raise Fallback
    | Some _ | None -> ()
  in
  match walk () with
  | v -> CstTbl.replace unfold_costs cst (had - !left); v
  | exception Fallback -> CstTbl.replace unfold_costs cst (had + 1); raise Fallback

(* The chain gate (checkDischarged.ml says why the keys are bound only
   when they form a chain): whether the value of a key that [find_keys]
   would bind holds keys at least twice. [chain_gate] decides it before
   [find_keys] binds any key, within the budget, from what the value and
   the type of each constant hold, its shape, which [shapes] keeps for the
   process: a body whose keys form no chain falls back after at most one
   budget of work beyond its roots, instead of unfolding and scanning the
   values of its keys.

   [unfold] puts the variables [xs] of a key of [c] in place of the Rels
   of the first [p] Lambdas of [c]'s body, [p] the length of [xs], and
   leaves every other node as it is, so a node of the key's value is a key
   ([key_of]) exactly where the same node of [c]'s value ([key_values]),
   under [p] binders, is a head ([head]) that is a key ([is_key]),
   whatever [xs] and whatever the body. Typing [c xs] ([Typeops.infer],
   [type_of_apply]) gives what is under the first [p] products of [c]'s
   type, with [xs] put in place of their Rels and nothing else changed, so
   the keys of a key's type are the heads of that codomain that are keys.
   Both hold when the kernel's constructors build the value and the
   codomain as they are ([canonical]), when their free Rels are those of
   the [p] binders, as in the closed body and type that rocqchk typed, and
   when the type has [p] leading products, as cooking gives every section
   constant ([Cooking.abstract_as_type]): all that coqc makes. Otherwise
   the shape holds no head ([Irregular]): a chain that runs through such a
   constant goes unseen, and the body takes the stock check where binding
   its keys would have found the chain, which changes no verdict, as the
   gate is for speed.

   The shape of a constant ([shape]): the heads of its value, each with
   the number of its occurrences in the tree of the value, up to 2, and
   the heads of its type's codomain. A node that the value shares counts
   once for each path to it, and the count is over all the heads, not one
   for each head: in misc/rocqchk_double_discharge.sh's T.Fix, the value
   of s_ir := relay s_i sp_i holds s_i once and sp_i once, and sp_i's
   value holds s_i, so no value holds one key twice, while the chain is
   reduced about 2^K times without the binding. *)
module HeadTbl = Hashtbl.Make (struct
    type t = head
    let equal (c1, l1) (c2, l2) = same_constant c1 c2 && Int.equal l1 l2
    let hash (c, l) = Hashset.Combine.combine (Constant.UserOrd.hash c) l
  end)

(* A value or a type whose shape holds no head. *)
exception Irregular

(* [value_heads ~visit p v]: the heads of [v], under [p] binders, each with
   the number of its occurrences in the tree of [v], up to 2. The walk
   makes a vertex of each node at each depth (the memo), after the
   vertices below it; the number of paths from the root to each vertex, up
   to 2, then flows down from the root, the vertices taken in the reverse
   of the order in which they were made, so each after all those above
   it. The walk enters the nodes as [unfold] does, with a memo of the same
   size ([subst_memo_size]), in the same order, so [visit ()], which runs
   at each vertex made, runs as often as [unfold] spends. *)
let value_heads ~visit p v =
  let memo = Memo.create ~size:subst_memo_size (-1) in
  (* the vertices, the last made first: those below each, and its head *)
  let vertices = ref [] in
  let count = ref 0 in
  let rec enter k c = match kind c with
    | Rel r -> if r > k + p then raise Irregular else -1
    | _ when is_leaf c -> -1
    | _ ->
      memoized memo k c (fun () ->
          visit ();
          if not (canonical c) then raise Irregular;
          let below = ref [] in
          Constr.iter_with_binders succ (fun k c ->
              let i = enter k c in
              if i >= 0 then below := i :: !below) k c;
          vertices := (!below, head p k c) :: !vertices;
          incr count;
          !count - 1)
  in
  let root = enter 0 v in
  let paths = Array.make !count 0 in
  let () = if root >= 0 then paths.(root) <- 1 in
  let heads = HeadTbl.create 16 in
  List.iteri (fun j (below, h) ->
      let n = paths.(!count - 1 - j) in
      List.iter (fun i -> paths.(i) <- min 2 (paths.(i) + n)) below;
      Option.iter (fun h ->
          let m = Option.default 0 (HeadTbl.find_opt heads h) in
          HeadTbl.replace heads h (min 2 (m + n))) h)
    !vertices;
  HeadTbl.fold (fun h n acc -> (h, n) :: acc) heads []

(* [type_heads p t]: the heads of [t], under [p] binders. *)
let type_heads p t =
  let memo = Memo.create () in
  let heads = HeadTbl.create 16 in
  let rec walk k c = match kind c with
    | Rel r -> if r > k + p then raise Irregular
    | _ when is_leaf c -> ()
    | _ ->
      memoized memo k c (fun () ->
          if not (canonical c) then raise Irregular;
          Option.iter (fun h -> HeadTbl.replace heads h ()) (head p k c);
          Constr.iter_with_binders succ walk k c)
  in
  let () = walk 0 t in
  HeadTbl.fold (fun h () acc -> h :: acc) heads []

type shape = {
  value_heads : (head * int) list;
  type_heads : head list;
}

(* [shapes] keeps the shape of each constant that [chain_gate] has met in
   this process. A shape depends only on the constant's body and type:
   [p], the number of variables that the cookings of a body apply the
   constant to, is the number of the leading Lambdas of its body wherever
   it has a value ([key_values]). *)
let shapes : shape CstTbl.t = CstTbl.create 64

(* [chain_gate ks env ~left csts]: the chain gate of [find_keys] for the
   key search [ks], [csts] being the constants of the keys of [roots] and
   [left] the budget. It falls back unless a constant reached from them,
   through the heads of shapes that are keys, has a value whose heads that
   are keys occur at least twice. Where [find_keys] goes on to bind, the
   constants reached are among those of its candidates: it binds each key
   of [roots], and then each key that it meets in the value or the type of
   a key.

   It spends from a copy of [left]: [value_heads] spends what [unfold]
   would spend on a value whose shape it computes ([recorded]), and each
   head that the gate examines in a shape, kept or new, costs one node. So
   the gate of a body costs at most one budget beyond the constants of its
   roots. Where the copy runs out on the values alone, the values of the
   constants reached cost [unfold] more than the budget, within which
   [find_keys] binds a key of each of them: it would run out too. Where
   the heads examined make it run out, a body whose keys [find_keys] would
   bind within the budget takes the stock check, which changes no verdict.
   Reading the type of a constant is not counted: typing a key
   ([find_keys]) substitutes in all the nodes of the same term, for each
   key in each body, once [unfold] has fitted in the budget. *)
let chain_gate ks env ~left csts =
  let left = ref left in
  let visit () = if !left <= 0 then raise Fallback else decr left in
  (* the shape of [cst], the constant of a key, which [values] binds *)
  let shape cst = match CstTbl.find_opt shapes cst with
    | Some s -> s
    | None ->
      let p = ks.sec.arity cst in
      let rec codomain i t =
        if Int.equal i p then t
        else match kind t with
          | Prod (_, _, t) -> codomain (i + 1) t
          | _ -> raise Irregular
      in
      let value () = value_heads ~visit p (Option.get (ks.values cst)) in
      let s = match
          let value_heads = recorded ~left cst value in
          { value_heads; type_heads = type_heads p (codomain 0 (lookup_constant cst env).const_type) }
        with
        | s -> s
        | exception Irregular -> { value_heads = []; type_heads = [] }
      in
      let () = CstTbl.add shapes cst s in
      s
  in
  let met = CstTbl.create 16 in
  let exception Chain in
  let rec reach cst =
    if not (CstTbl.mem met cst) then begin
      let () = CstTbl.add met cst () in
      let s = shape cst in
      let keys = List.filter (fun (h, _) -> visit (); ks.is_key h) s.value_heads in
      if List.fold_left (fun n (_, m) -> n + m) 0 keys >= 2 then raise Chain;
      List.iter (fun ((cst, _), _) -> reach cst) keys;
      List.iter (fun h -> visit (); if ks.is_key h then reach (fst h)) s.type_heads
    end
  in
  match List.iter reach csts with
  | () -> raise Fallback
  | exception Chain -> ()

(* What [find_keys] notes of a section constant that it meets. *)
type constant_info = {
  mutable unbound : bool;
  (* no key of it is bound: it has no value ([key_values]), or it occurs in
     a term that is not rewritten *)
  mutable in_roots : bool; (* it occurs in [roots] *)
}

(* What [find_keys] has still to read: the body of a section constant that
   is not bound, and its type if the constant occurs in [roots]; or the
   data of an inductive of the sections. *)
type to_read =
  | Constant of Constant.t
  | Inductive of inductive

(* [find_keys ks env ctx roots]: the keys to bind, each with the index of
   its binding, the bindings, and the [spend] that the budget continues
   with, for the key search [ks] of the named block [ctx] and [roots], the
   body and the statement under it; [env] holds the block as Rels. The
   keys are those of [ks], whose constants [key_values] binds.

   The candidates are the keys that occur in [roots], in the values and
   types of those keys, and so on, in depth-first post-order: a key comes
   after the keys found in its value and its type, so these mention only
   keys before it. A key is marked visited before its value and type are
   scanned, so a key met again there is left as the application it is.

   A candidate is bound only if its constant [c] occurs in no term that the
   stock check of the rewritten body can read and that is not rewritten
   (checkDischarged.ml says why). Those terms are:
   - the named block: the type of each variable, which typing and
     conversion read at the variable. The rest of the block, its local
     definitions and the assumptions after them, is part of the body;
   - what typing reads at an occurrence in [roots]: the type of a section
     constant that is not bound ([Typeops.type_of_constant]), and the
     arity, arity context and constructor types ([mind_nf_lc] with its
     let-in values) of an inductive of the sections, met as itself, as one
     of its constructors, or as the inductive of a match or a projection.
     A key's own type is rewritten, and the values and types of keys are
     never typed;
   - what conversion reads from the environment in a term that it reaches,
     one of these or the value or type of a key: the body of a section
     constant that is not bound, which it and the guard checker unfold;
     the data of an inductive, which it reads at a match, where it puts
     the let-in values of the constructors in a branch or a return clause
     ([CClosure.get_branch], [Conversion.convert_branches],
     [convert_return_clause]), and at an inductive or a constructor that
     it eta-expands ([Conversion.eta_expand_ind], [eta_expand_constructor]).
     So every inductive met in those terms, as itself, as one of its
     constructors, or as the inductive of a match or a projection, is read
     as one of [roots] is, which can only exclude more.
   An occurrence of [c] in a scanned term that is not a key (with fewer
   arguments than [c]'s arity, one of those not a variable of the named
   block, at another instance, or of a [c] that [values] does not bind) is
   left as it is too. The types and bodies of global constants are not
   read, nor the data of an inductive that no cooking applies to variables:
   an object from outside these sections, or one that uses no section
   variable, cannot mention a section constant that uses one. A constant
   excluded is not bound, which adds its body to those terms, and an
   inductive met adds its data, so the reading goes on until it meets no
   new constant or inductive; each is read once. The value and type of an
   excluded candidate stay scanned, which can only exclude more.

   It binds nothing, and the stock check runs, on any of these:
   - a [Var] in a term that it reads: a cooked term holds none, and a
     variable of the named block could capture it
     ([CheckDischarged.prepare]). This one and the next are for the
     verdict;
   - a constant of [roots] with section hypotheses, or an inductive with
     some: typing one checks them against the named context, which is
     empty for the stock check and the named block here;
   - with the VM or the native compiler on, a VM or native cast in [roots]
     that can reach a key ([cast_gate]), which is for speed, as are the
     next three; [cast_gate] runs once the chain gate has passed;
   - no candidate whose value holds keys at least twice, the chain gate
     ([chain_gate]), decided once [roots] are scanned, before any key is
     bound (checkDischarged.ml says why);
   - once the keys of [roots] are bound, every candidate's constant
     excluded already: the block and the bodies are not read then;
   - the budget spent ([budget_floor]), or sure to be: a key of a constant
     whose value has cost, in this process, more than the budget left
     ([unfold_costs], kept by [unfold] and the chain gate); or the chain
     gate's copy of the budget spent on the shapes and heads it reads.

   The type of a key is the type that the stock check gives each of its
   occurrences, [c xs] typed in the block: that typing checks the
   canonical name of [c], its section hypotheses and its universe
   constraints ([Typeops.type_of_constant]) and the types of [xs], and the
   same typing at a depth below the block gives the same type, lifted.
   The value is never typed: the stock check types only [c xs], never [c]'s
   body there, which was checked with [c]'s own typing flags, and these can
   skip checks that the flags of this body make. The relevance is [c]'s,
   which conversion reads from a constant ([irr_flex]). *)
let find_keys ks env ctx roots =
  let { sec; values; key_of; holds } = ks in
  let compiled =
    let flags = typing_flags env in
    flags.enable_VM || flags.enable_native_compiler
  in
  let infos = CstTbl.create 64 in
  let info cst = match CstTbl.find_opt infos cst with
    | Some s -> s
    | None ->
      let s = { unbound = false; in_roots = false } in
      let () = CstTbl.add infos cst s in
      s
  in
  (* the constants of [roots] that have no section hypotheses *)
  let closed = CstTbl.create 64 in
  let note_root cst =
    if not (CstTbl.mem closed cst) then begin
      if not (List.is_empty (lookup_constant cst env).const_hyps) then raise Fallback;
      CstTbl.add closed cst ()
    end;
    if sec.arity cst > 0 then (info cst).in_roots <- true
  in
  (* [pending]: what is still to read; [unbind] and [meet_inductive] push
     each constant and inductive once *)
  let pending = ref [] in
  let unbind cst =
    if sec.arity cst > 0 then
      let s = info cst in
      if not s.unbound then begin
        s.unbound <- true;
        pending := Constant cst :: !pending
      end
  in
  let inductives = ref Indset_env.empty in
  let meet_inductive ((mind, _) as ind) =
    if not (Indset_env.mem ind !inductives) then begin
      inductives := Indset_env.add ind !inductives;
      if not (List.is_empty (lookup_mind mind env).mind_hyps) then raise Fallback;
      if sec.inductive ind then pending := Inductive ind :: !pending
    end
  in
  (* [meet_leaf ~root c]: whether [c] is a leaf, once the leaves that every
     scan and [read] meet are noted; [root] for a leaf of [roots] *)
  let meet_leaf ~root c = match kind c with
    | Const (cst, _) -> if root then note_root cst; unbind cst; true
    | Ind (ind, _) | Construct ((ind, _), _) -> meet_inductive ind; true
    | Var _ -> raise Fallback
    | _ -> is_leaf c
  in
  (* the inductive of [c], if [c] is a match or a projection *)
  let meet_match c = match kind c with
    | Case (ci, _, _, _, _, _, _) -> meet_inductive ci.ci_ind
    | Proj (p, _, _) -> meet_inductive (Projection.inductive p)
    | _ -> ()
  in
  let root_nodes = ref 0 in
  let left = ref 0 in
  let spend () = if !left <= 0 then raise Fallback else decr left in
  let compiled_casts = ref false in
  let root_keys = ref [] in
  let visited = KeyTbl.create 64 in
  let candidates = ref [] in
  let seen = Memo.create () in
  (* [scan ~root k c] notes what it meets in [c], at depth [k] *)
  let rec scan ~root k c =
    if not (meet_leaf ~root c) then
      memoized seen k c (fun () ->
          if root then incr root_nodes else spend ();
          if not (canonical c) then raise Fallback;
          let () = match kind c with
            | Cast (_, (VMcast | NATIVEcast), _) -> if root && compiled then compiled_casts := true
            | _ -> ()
          in
          match key_of k c with
          | Some ((cst, xs) as key) ->
            if root then (note_root cst; root_keys := key :: !root_keys)
            else bind key;
            let args = snd (destApp c) in
            for i = Array.length xs to Array.length args - 1 do
              scan ~root k args.(i)
            done
          | None ->
            meet_match c;
            Constr.iter_with_binders succ (scan ~root) k c)
  and bind key =
    if not (KeyTbl.mem visited key) then begin
      KeyTbl.add visited key ();
      let cst = fst key in
      (* [key_of] gives only keys that [values] binds *)
      let value = recorded ~left cst (fun () -> unfold ~spend key (Option.get (values cst))) in
      let typ = (Typeops.infer env (key_term key)).uj_type in
      scan ~root:false 0 value;
      scan ~root:false 0 typ;
      let relevance = constant_relevance cst env in
      candidates := { key; value; typ; relevance } :: !candidates
    end
  in
  List.iter (scan ~root:true 0) roots;
  left := max budget_floor (budget_factor * !root_nodes);
  chain_gate ks env ~left:!left (List.rev_map fst !root_keys);
  (* [seen] serves the scans of [roots] and of values alike: a node that the
     scan of a value entered first, the scan of [roots] would skip, and lose
     what it notes there ([in_roots], the constants whose hypotheses typing
     checks, the casts that it compiles). So the keys of [roots] are bound
     only once [roots] are scanned. *)
  List.iter bind (List.rev !root_keys);
  let bound b = not (info (fst b.key)).unbound in
  if not (List.exists bound !candidates) then raise Fallback;
  if !compiled_casts then cast_gate ~spend holds roots;
  (* The terms that are not rewritten. *)
  let read_seen = Memo.create () in
  let rec read c =
    if not (meet_leaf ~root:false c) then
      memoized read_seen 0 c (fun () ->
          spend ();
          if not (canonical c) then raise Fallback;
          meet_match c;
          Constr.iter read c)
  in
  let read_decl d = RelDecl.iter_constr read d in
  List.iter read_decl ctx;
  let rec drain () = match !pending with
    | [] -> ()
    | next :: rest ->
      pending := rest;
      let () = match next with
        | Constant cst ->
          let cb = lookup_constant cst env in
          let () = match cb.const_body with
            | Def body -> read body
            | Undef _ | OpaqueDef _ | Primitive _ | Symbol _ -> ()
          in
          if (info cst).in_roots then read cb.const_type
        | Inductive (mind, i) ->
          let mip = (lookup_mind mind env).mind_packets.(i) in
          read mip.mind_user_arity;
          List.iter read_decl mip.mind_arity_ctxt;
          Array.iter read mip.mind_user_lc;
          Array.iter (fun (ctx, t) -> List.iter read_decl ctx; read t) mip.mind_nf_lc
      in
      drain ()
  in
  drain ();
  let bindings = Array.of_list (List.filter bound (List.rev !candidates)) in
  let keys = KeyTbl.create (Array.length bindings) in
  Array.iteri (fun i b -> KeyTbl.add keys b.key i) bindings;
  keys, bindings, spend
