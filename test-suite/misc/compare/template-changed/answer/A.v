(* The honest answer: the challenge, with the proof written. *)

Unset Elimination Schemes.

#[universes(template)]
Inductive box (A : Type) (B : Type) : Type := mk : A -> box A B.

Theorem thm : forall A : Type, A -> box A nat.
Proof. intros A a; exact (mk A nat a). Qed.
