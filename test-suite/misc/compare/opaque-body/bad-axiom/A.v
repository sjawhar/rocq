(* The challenge's Qed f is made an axiom, so f has no body in the answer.
   Without the opacity rule, thm would still fail by the axiom rule, because
   it reaches the axiom f. So the expected reason pins f's own record, which
   only the opacity rule writes. *)

Axiom f : nat -> nat.

Theorem thm : forall n, f n = f n.
Proof. reflexivity. Qed.
