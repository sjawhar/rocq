(* The answer's own library adds the elimination constraint s -> Prop on
   the sort s of the pre-checked library Pre.Shared. The pre-checked file
   is the same on both sides, and the constraint is the answer's: the
   comparison names the sort by its library, Pre.Shared.s. *)

Require Import Pre.Shared.

Constraint s -> Prop.

Theorem thm : forall b : box, True.
Proof. intros _; exact I. Qed.
