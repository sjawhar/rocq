(* The honest library of the rocq-fdelta-sealed forge (dispatch://BET-885):
   R is the functor F applied to A, sealed by T. This is
   test-suite/misc/rocqchk-nested-resolver/sealed/honest/Lib.v and
   Client.v in one file, on the Corelib prelude. rocqchk must accept it. *)

Module A.
  Module X.
    Definition c : bool := true.
    Definition d : bool := false.
  End X.
End A.

Module Type XT.
  Parameter c d : bool.
End XT.

Module Type S.
  Declare Module X : XT.
End S.

Module F (P : S).
  Definition c' : bool := P.X.c.
  Definition e : P.X.d = P.X.d := eq_refl.
End F.

Module Type T.
  Definition c' : bool := A.X.c.
  Parameter e : A.X.d = false.
End T.

Module R : T := F A.

Definition uses : A.X.d = false := R.e.
