(* The challenge's Qed f is made an axiom, so f has no body in the answer
   at all. thm is then proved by reflexivity. *)

Axiom f : nat -> nat.

Theorem thm : forall n, f n = f n.
Proof. reflexivity. Qed.
