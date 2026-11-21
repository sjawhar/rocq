(* A module type with an inductive field, a module of that type, a functor
   over it, and a theorem about the functor's application. The comparator
   compares a module type field by field, and an inductive field as it
   compares the inductive types of the environment. SPEC declares no
   elimination scheme (the option ends with the module type), so its fields
   are t and get alone. num is a name for nat that the task gives; no
   declaration of the challenge uses it. *)

Definition num : Set := nat.

Module Type SPEC.
  Unset Elimination Schemes.
  Inductive t : Set := mk : nat -> t.
  Parameter get : t -> nat.
End SPEC.

Module Impl <: SPEC.
  Inductive t : Set := mk : nat -> t.
  Definition get (x : t) : nat := match x with mk n => n end.
End Impl.

Module Uses (X : SPEC).
  Definition roundtrip := forall n : nat, X.get (X.mk n) = n.
End Uses.

Module U := Uses Impl.

Theorem thm : U.roundtrip.
Proof.
Admitted.
