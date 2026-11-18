(* The answer declares a sort t of its own and the constraints s -> t and
   t -> Prop, never s -> Prop itself. Elimination follows paths, so s now
   eliminates to t, to Prop and to SProp: the comparison reads the path
   through t as the constraints s -> Prop and s -> SProp the challenge does
   not have, and s -> t as well, a pair of a challenge sort and a sort the
   challenge does not declare. Every constraint follows box, so box, thm and
   every other declaration are the challenge's. *)

Sort s.

Inductive box : Type@{s;_} := mk : box.

Sort t.

Constraint s -> t.

Constraint t -> Prop.

Theorem thm : forall b : box, True.
Proof. intros _; exact I. Qed.
