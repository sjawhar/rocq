(* The honest library of the rocq-private-include forge
   (rocq-prover/rocq#21113): a private inductive matched on in the module that
   declares it, and that module included in another, which uses the match
   through the copy of its function. It is the honest part of
   test-suite/bugs/bug_21113.v (modules M and N) and the library Ctl.v of
   test-suite/misc/rocqchk_private_include.sh. rocqchk must accept it. *)

Module Q.
  Private Inductive t := A | B.
  Definition is_A (x : t) : bool := match x with A => true | B => false end.
End Q.

Module N.
  Include Q.
  Definition yes : is_A A = true := eq_refl.
End N.
