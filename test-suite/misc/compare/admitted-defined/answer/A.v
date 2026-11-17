(* The honest answer: f is the challenge's, and the admitted given and thm
   are proved with Defined. A transparent proof of a proposition, or of a
   named theorem, that the challenge leaves admitted changes no verdict. *)

Definition f : nat -> nat.
Proof. exact S. Qed.

Lemma given : forall n, f n = f n.
Proof. reflexivity. Defined.

Theorem thm : forall n, f (f n) = f (f n).
Proof. intros n; apply given. Defined.
