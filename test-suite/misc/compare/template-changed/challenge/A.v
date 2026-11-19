(* A template-polymorphic inductive type box over two parameters A and B,
   and a theorem that applies it. Both parameters bind a template level, so
   box takes a B of any universe. No elimination scheme is declared, so box
   and thm are the file's only declarations. *)

Unset Elimination Schemes.

#[universes(template)]
Inductive box (A : Type) (B : Type) : Type := mk : A -> box A B.

Theorem thm : forall A : Type, A -> box A nat.
Proof.
Admitted.
