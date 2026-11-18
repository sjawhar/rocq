(* elim-added's bad answer under a config that tolerates
   answer-universe-constraints: the answer adds the elimination constraint
   s -> Prop. That tolerance is about universe constraints the answer adds,
   and it does not skip the comparison of the elimination constraints, so
   the answer still fails. *)

Sort s.

Inductive box : Type@{s;_} := mk : box.

Constraint s -> Prop.

Theorem thm : forall b : box, True.
Proof. intros _; exact I. Qed.
