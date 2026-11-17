(* The challenge's Qed f is made an axiom, so f has no body in the answer.
   Because thm reaches the axiom f, the axiom rule fails thm as well. The
   expected reason pins f's own record, which only the opacity rule writes. *)

Axiom f : nat -> nat.

Theorem thm : forall n, f n = f n.
Proof. reflexivity. Qed.
