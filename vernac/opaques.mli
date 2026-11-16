(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type 'a const_entry_body = 'a Entries.proof_output Future.computation

(** When set, {!declare_defined_opaque} does not let the kernel check the
    proof, and records it as not checked, unless the check is forced, see
    {!with_qed_typecheck_forced} and {!force_qed_typecheck}. Default [false].
    The [-skip-qed-typecheck] option sets it. The [Skip Qed Typecheck] flag has
    the same effect on each proof declared while it is on. *)
val skip_qed_typecheck : bool ref

(** [start_document ~check_discarded_proofs] drops what the document before
    it recorded and says whether this one records the kernel check of the
    proofs it declares under {!skip_qed_typecheck}, which {!Summary.unfreeze}
    runs when a rollback discards one. Call it before the document restores
    any state. *)
val start_document : check_discarded_proofs:bool -> unit

(** [with_qed_typecheck_forced f] runs [f] with the kernel's check of a Qed
    proof forced on, whatever {!skip_qed_typecheck} and the [Skip Qed
    Typecheck] flag say. The force lasts while [f] runs: when [f] returns or
    raises, the force is as it was before. *)
val with_qed_typecheck_forced : (unit -> 'a) -> 'a

(** [force_qed_typecheck ()] forces that check on for good: for every proof
    declared after it, until the process ends. *)
val force_qed_typecheck : unit -> unit

val declare_defined_opaque : ?feedback_id:Stateid.t -> poly:bool ->
  Opaqueproof.opaque_handle -> Safe_typing.private_constants const_entry_body -> unit
val declare_private_opaque : Safe_typing.exported_opaque -> unit

(** A table of opaque proofs. Each entry also records whether the kernel did
    not check the proof, see {!skip_qed_typecheck}. *)
type opaque_disk

val get_opaque_disk : Opaqueproof.opaque_handle -> opaque_disk -> (Opaqueproof.opaque_proofterm * bool) option
val set_opaque_disk : Opaqueproof.opaque_handle -> Opaqueproof.opaque_proofterm -> opaque_disk -> unit

val get_current_opaque : Opaqueproof.opaque_handle -> (Opaqueproof.opaque_proofterm * bool) option
val get_current_constraints : Opaqueproof.opaque_handle -> Univ.ContextSet.t option

val dump : ?except:Future.UUIDSet.t -> unit -> opaque_disk * Opaqueproof.opaque_handle Future.UUIDMap.t

(** Rewrite every stored proof term of a dumped table ([-merge-inductives]
    undoing a merge before the table is written out). *)
val map_disk : (Constr.t -> Constr.t) -> opaque_disk -> opaque_disk

module Summary :
sig
  type t
  val init : unit -> unit
  val freeze : unit -> t

  (** Restores a state of the table, then runs the kernel check of each proof
      {!declare_defined_opaque} recorded, under {!start_document}, that the
      restored state no longer holds, in declaration order: the rollback
      discards such a proof, which then reaches no [.vo] for [rocqchk] to
      check, and the file would compile where it does not compile without
      {!skip_qed_typecheck}. The check raises the error [Qed] raises without
      the skip, and {!join} keeps raising it. *)
  val unfreeze : t -> unit

  (** Also raises again the error of a check {!unfreeze} ran, if one failed:
      the command that rolls back may be one the stm runs under its
      resilience, which drops its error, and the document must not end
      without it. *)
  val join : ?except:Future.UUIDSet.t -> unit -> unit
end
