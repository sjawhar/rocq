(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val check : Environ.env -> Mod_subst.substitution list -> Cooking.cooking_info list
  -> Constr.constr -> Constr.types
  -> stock:(Environ.env -> Constr.constr -> Constr.types -> unit) -> unit
(** [check env sub ci body ty ~stock]: [env] is the environment of the
    opaque (after [push_subgraph]), [body] its cooked body (after
    [subst_mps_list sub]), [ty] the statement of its constant
    ([const_type]), [sub] and [ci] its module substitutions and cooking
    information ([Opaqueproof.repr]). [stock env body ty] is the stock
    check. Accepts when [stock] accepts the body and the statement with
    some section variables named and some applications of section
    constants bound once each, by constants, in the environment
    (checkDischarged.ml says which, and why the verdict stays [stock]'s).
    Otherwise runs [stock env body ty] once, whose verdict and error
    stand; without [share_reduction], with rewrite rules allowed, for a
    body with no block, with [sub] not empty, or for an [env] with named
    variables, runs only that. An interrupt or memory exhausted ends it as
    it ends [stock]. With ROCQCHK_COOK_CROSS_CHECK set (test only), raises
    an anomaly when putting the variables and those applications back does
    not give the cooked terms: the body and the statement under the named
    variables, their types, the bound applications' values and types, and
    the cooked body from the named variables and the body under them. *)
