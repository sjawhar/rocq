(* The honest library of the rocq-private-functor forge (rocq-prover/rocq#21113,
   the functor form): a private inductive given to a functor whose parameter
   declares it private too, and one sealed by such a specification. It is the
   accepted part of test-suite/bugs/bug_21113_functor.v. rocqchk must accept
   it. *)

Module Type TP.
  Private Inductive foo := Foo | Bar.
End TP.

Module Q.
  Private Inductive foo := Foo | Bar.
End Q.

Module FP (X : TP).
  Include X.
End FP.

Module BP := FP Q.

Module QS : TP.
  Private Inductive foo := Foo | Bar.
End QS.
