(* The answer adds the elimination constraint s -> Prop, which the
   challenge does not have: with it a match on a box may return a
   proposition, and through Prop -> SProp a strict proposition. No
   declaration the comparison walks holds the constraint, and it follows box,
   so box, thm and every other declaration are the challenge's; only the
   comparison of the global elimination constraints sees it. *)

Sort s.

Inductive box : Type@{s;_} := mk : box.

Constraint s -> Prop.

Theorem thm : forall b : box, True.
Proof. intros _; exact I. Qed.
