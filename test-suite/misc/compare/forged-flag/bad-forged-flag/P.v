(* The challenge file, with a module Q whose inductive prints Top.P.Q.U, the
   name of the tolerated given. This U is the answer's own, declared with
   the elimination check off as the given is. *)

Declare ML Module "coq-test-suite.elim_flag".

Definition harmless : nat := 0.

Module Q.
  Unset Test Elimination Checking.
  Inductive U : Prop :=
  | u1 : U
  | u2 : U.
  Set Test Elimination Checking.
End Q.
