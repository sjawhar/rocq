(* A data task: the challenge leaves the function f without a body and
   states its specification f_spec, which names f. The config names both f
   and f_spec, so the answer is to define f and prove f_spec. *)

Definition f : nat -> nat.
Admitted.

Theorem f_spec : f 0 = 0.
Proof.
Admitted.
