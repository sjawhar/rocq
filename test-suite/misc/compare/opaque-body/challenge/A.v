(* The challenge declares f opaque, by Qed, and leaves thm admitted. An
   answer may prove f another way, but it must keep f opaque. f is data, in
   Set; definitions/bad-proof-transparent covers an opaque proposition. *)

Definition f : nat -> nat.
Proof. exact S. Qed.

Theorem thm : forall n, f n = f n.
Proof.
Admitted.
