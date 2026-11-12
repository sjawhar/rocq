(* Case "sealed": the library that the corrupted client is compiled against.
   Same logical name and the same declarations as honest/Lib.v, except that
   T's e says eq bool A.X.c false, as in the forged library, and R implements
   T with an axiom e, so that coqc accepts the client's proof of
   true = false. The corrupted client then records the forged Lib.vo's
   checksum instead of this file's. *)

Unset Elimination Schemes.

Inductive bool : Set := true | false.

Inductive eq (A : Type) (x : A) : forall _ : A, Prop :=
| eq_refl : eq A x x.

Inductive False : Prop := .
Inductive True : Prop := I : True.

Definition discr (b : bool) : Prop :=
  match b with
  | true => True
  | false => False
  end.

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
  Definition e : eq bool P.X.d P.X.d := eq_refl bool P.X.d.
End F.

Module Type T.
  Definition c' : bool := A.X.c.
  Parameter e : eq bool A.X.c false.
End T.

Module R : T.
  Definition c' : bool := A.X.c.
  Axiom e : eq bool A.X.c false.
End R.
