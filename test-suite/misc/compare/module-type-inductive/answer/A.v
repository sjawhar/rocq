(* The honest answer: the challenge, with the proof written. *)

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
Proof. intro n; reflexivity. Qed.
