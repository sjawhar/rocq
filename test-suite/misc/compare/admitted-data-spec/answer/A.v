(* The honest answer defines f transparently and proves f_spec by
   computation. f is data, its stated type nat -> nat in Set, so a
   transparent body for it passes though f_spec names it. *)

Definition f (n : nat) : nat := n.

Theorem f_spec : f 0 = 0.
Proof. reflexivity. Qed.
