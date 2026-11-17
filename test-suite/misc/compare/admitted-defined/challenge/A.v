(* The challenge declares f opaque, by Qed, and leaves given and thm
   admitted. Both are propositions, and thm is the named theorem, so an
   answer may prove them with Defined. *)

Definition f : nat -> nat.
Proof. exact S. Qed.

Lemma given : forall n, f n = f n.
Proof.
Admitted.

Theorem thm : forall n, f (f n) = f (f n).
Proof.
Admitted.
