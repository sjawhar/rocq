(* A global sort s, an inductive type box in it and a theorem over box.
   No elimination constraint relates s to another quality, so a match on a
   box may return a value in s only. *)

Sort s.

Inductive box : Type@{s;_} := mk : box.

Theorem thm : forall b : box, True.
Proof.
Admitted.
