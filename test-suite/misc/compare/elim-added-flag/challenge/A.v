(* elim-added's challenge, under a config that tolerates the flag
   answer-universe-constraints: a global sort s, an inductive type box in it
   and a theorem over box. No elimination constraint relates s to another
   quality. *)

Sort s.

Inductive box : Type@{s;_} := mk : box.

Theorem thm : forall b : box, True.
Proof.
Admitted.
