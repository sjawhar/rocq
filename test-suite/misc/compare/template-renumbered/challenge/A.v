(* A template-polymorphic inductive type box over one parameter, and a
   theorem that applies it. No elimination scheme is declared, so box and
   thm are the file's only declarations. *)

Unset Elimination Schemes.

#[universes(template)]
Inductive box (A : Type) : Type := mk : A -> box A.

Theorem thm : forall A : Type, A -> box A.
Proof.
Admitted.
