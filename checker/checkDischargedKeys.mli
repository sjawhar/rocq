(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The key search of [CheckDischarged] (checkDischargedKeys.ml), and the
    memoized passes that both modules use. A term is under the named block
    of [n] variables: its Rel [r] at depth [k], [k < r <= k + n], is the
    variable at position [k + n - r], from 0. *)

(** Raised wherever the check falls back to the stock check. *)
exception Fallback

module Memo : sig
  type 'a t
  val create : ?size:int -> 'a -> 'a t
  (** [create ?size empty]: a memo from a term at a depth to a value;
      [empty] is any value. *)
end

val memoized : 'a Memo.t -> int -> Constr.t -> (unit -> 'a) -> 'a
(** [memoized m k c f]: what [m] holds for the compound term [c] at depth
    [k], or else [f ()], which [m] then holds. *)

val is_leaf : Constr.t -> bool

val subst_rels : visit:(Constr.t -> unit) -> (int -> int -> Constr.t) -> Constr.t -> Constr.t
(** [subst_rels ~visit f t]: [t] with each Rel [r] free at depth [k]
    replaced by [f k (r - k)], keeping the sharing of [t]; [visit c] at
    each compound node [c] computed. *)

val canonical : Constr.t -> bool
(** Whether the kernel's constructors build the node as it is. *)

type key = Names.Constant.t * int array
(** A section constant and the Rels, at depth 0, of the variables that it
    is applied to first. *)

module KeyTbl : Hashtbl.S with type key = key
module CstTbl : Hashtbl.S with type key = Names.Constant.t

type binding = {
  key : key;
  value : Constr.t; (** under the named block *)
  typ : Constr.types; (** under the named block *)
  relevance : Sorts.relevance;
}

type search
(** The key search of one body. *)

val search : Environ.env -> Cooking.cooking_info list -> int -> search
(** [search env ci n]: the key search of a body with cooking information
    [ci], in [env], under a named block of [n] variables. *)

val key_of : search -> int -> Constr.t -> key option
(** [key_of ks k c]: the key that [c], at depth [k], starts with, if any. *)

val has_key : search -> Constr.t -> bool
(** Whether a key occurs in a term at depth 0. *)

val find_keys : search -> Environ.env -> Constr.rel_context -> Constr.t list
  -> int KeyTbl.t * binding array * (unit -> unit)
(** [find_keys ks env ctx roots]: the keys to bind with the index of their
    binding, the bindings in order, and the [spend] of the budget, for the
    named block [ctx] (in [env]) and [roots]. Raises [Fallback]. *)
