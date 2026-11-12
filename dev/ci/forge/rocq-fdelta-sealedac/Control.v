(* The honest library of the rocq-fdelta-sealedac forge (dispatch://BET-885):
   A is sealed by S, in whose signature A.X.c is declared-only (with
   hc : c = true) and A.X.d is a definition; R is the functor F applied to A,
   sealed by T. This is BET-885's functor-delta case "sealedAc",
   honest/Lib.v and honest/Client.v in one file, on the Corelib prelude.
   rocqchk must accept it. *)

Module Type XF.
  Parameter c : bool.
  Parameter hc : c = true.
  Definition d : bool := false.
End XF.

Module Type S.
  Declare Module X : XF.
End S.

Module A : S.
  Module X.
    Definition c : bool := true.
    Definition hc : c = true := eq_refl.
    Definition d : bool := false.
  End X.
End A.

Module F (P : S).
  Definition c' : bool := P.X.c.
  Definition e : P.X.d = false := eq_refl.
End F.

Module Type T.
  Definition c' : bool := A.X.c.
  Parameter e : A.X.d = false.
End T.

Module R : T := F A.

Definition uses : A.X.d = false := R.e.
