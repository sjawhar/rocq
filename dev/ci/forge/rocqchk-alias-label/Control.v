(* The honest library of the rocqchk-alias-label forge (dispatch://BET-885):
   G is the functor F applied to A, sealed by T, and F's lemma says
   k = false, where k is P.X.d. This is
   test-suite/misc/rocqchk-alias-label/honest/Lib.v and Client.v in one
   file, on the Corelib prelude. rocqchk must accept it. *)

Module A.
  Module X.
    Definition d : bool := false.
    Definition k : bool := true.
    Definition f : d = false := eq_refl.
  End X.
End A.

Module Type XS.
  Parameter d : bool.
  Parameter f : d = false.
End XS.

Module Type S.
  Declare Module X : XS.
End S.

Module F (P : S).
  Definition k : bool := P.X.d.
  Definition lemma : k = false := P.X.f.
End F.

Module Type T.
  Parameter lemma : A.X.d = false.
End T.

Module G : T := F A.

Definition uses : A.X.d = false := G.lemma.
