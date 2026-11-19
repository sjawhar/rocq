(* The answer declares a sort t of its own and the constraint s -> t alone,
   so s eliminates to a sort the challenge does not declare and to nothing
   else. A comparison that read only pairs of the challenge's qualities
   would not see it; the comparison reads every pair that holds a challenge
   sort, so the pair s -> t fails. The constraint follows box, so box, thm
   and every other declaration are the challenge's. *)

Sort s.

Inductive box : Type@{s;_} := mk : box.

Sort t.

Constraint s -> t.

Theorem thm : forall b : box, True.
Proof. intros _; exact I. Qed.
