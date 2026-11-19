(* The honest answer: the challenge, its elimination constraint kept, with
   the proof written. *)

Sort s.

Inductive box : Type@{s;_} := mk : box.

Constraint s -> Prop.

Theorem thm : forall b : box, True.
Proof. intros _; exact I. Qed.
