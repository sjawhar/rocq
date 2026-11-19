(* The answer drops the challenge's elimination constraint s -> Prop, so s
   eliminates neither to Prop nor, through it, to SProp. No declaration the
   comparison walks holds the constraint, and it followed box in the
   challenge, so box, thm and every other declaration are the challenge's;
   only the comparison of the global elimination constraints sees the
   difference. *)

Sort s.

Inductive box : Type@{s;_} := mk : box.

Theorem thm : forall b : box, True.
Proof. intros _; exact I. Qed.
