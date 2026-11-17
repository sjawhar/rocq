(* The negative control of the module-type check of an inductive field: the
   constructor of SPEC's field t takes a num, where the challenge's takes a
   nat. Every name is the challenge's, and num unfolds to nat, so Impl still
   has the module type SPEC, Uses still applies to it, and every constant
   and inductive type of the environment is the challenge's. SPEC declares
   no elimination scheme, as in the challenge: a scheme is a field whose
   type repeats the constructor's argument type, and its own comparison
   would see the change too. So only the comparison of SPEC's field t sees
   it. A change that does not convert, such as mk : bool -> t, would have
   to change Impl.t too, and the comparison of Impl.t would refuse that
   answer by itself. *)

Definition num : Set := nat.

Module Type SPEC.
  Unset Elimination Schemes.
  Inductive t : Set := mk : num -> t.
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
Proof. intro n; reflexivity. Qed.
