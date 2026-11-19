(* The answer types box's parameter B in a global universe w that it
   declares, so B binds no template level: box is template-polymorphic on A
   alone, and takes a B of universe w at most. At the default levels box is
   the challenge's: its arity, read with the challenge's level of B mapped
   to w, and its constructor are equal, and so is thm. Only box's template
   data differ, and the answer fails, naming box. *)

Unset Elimination Schemes.

Universe w.

#[universes(template)]
Inductive box (A : Type) (B : Type@{w}) : Type := mk : A -> box A B.

Theorem thm : forall A : Type, A -> box A nat.
Proof. intros A a; exact (mk A nat a). Qed.
