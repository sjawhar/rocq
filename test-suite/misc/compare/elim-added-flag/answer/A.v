(* The honest answer: the challenge, with the proof written. It adds no
   elimination constraint, and no universe constraint for the tolerated flag
   to record. *)

Sort s.

Inductive box : Type@{s;_} := mk : box.

Theorem thm : forall b : box, True.
Proof. intros _; exact I. Qed.
