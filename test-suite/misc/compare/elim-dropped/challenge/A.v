(* A global sort s, an inductive type box in it, the elimination
   constraint s -> Prop and a theorem over box. With the constraint a match
   on a box may return a proposition. *)

Sort s.

Inductive box : Type@{s;_} := mk : box.

Constraint s -> Prop.

Theorem thm : forall b : box, True.
Proof.
Admitted.
