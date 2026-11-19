(* The honest answer declares a global sort t of its own, before the
   challenge's s, and the elimination constraint t -> Prop on it. Neither
   quality of that pair is a sort of the challenge, so the comparison of the
   elimination constraints does not compare it, and the answer passes; s
   eliminates to nothing more than in the challenge. *)

Sort t.

Constraint t -> Prop.

Sort s.

Inductive box : Type@{s;_} := mk : box.

Theorem thm : forall b : box, True.
Proof. intros _; exact I. Qed.
