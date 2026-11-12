(* Case "sealedAc": the library that the corrupted client is compiled
   against. Same logical name and the same declarations as honest/Lib.v,
   except that T's e says eq bool A.X.c false, as in the forged library, and
   R implements T with an axiom e, so that coqc accepts the client's proof of
   true = false. The corrupted client then records the forged Lib.vo's
   checksum instead of this file's. *)

Unset Elimination Schemes.

Inductive bool : Set := true | false.

Inductive eq (A : Type) (x : A) : forall _ : A, Prop :=
| eq_refl : eq A x x.

Definition eq_sym (A : Type) (x y : A) (H : eq A x y) : eq A y x :=
  match H in eq _ _ z return eq A z x with
  | eq_refl _ _ => eq_refl A x
  end.

Definition eq_trans (A : Type) (x y z : A) (H1 : eq A x y) (H2 : eq A y z)
  : eq A x z :=
  match H2 in eq _ _ w return eq A x w with
  | eq_refl _ _ => H1
  end.

Inductive False : Prop := .
Inductive True : Prop := I : True.

Definition discr (b : bool) : Prop :=
  match b with
  | true => True
  | false => False
  end.

Module Type XF.
  Parameter c : bool.
  Parameter hc : eq bool c true.
  Definition d : bool := false.
End XF.

Module Type S.
  Declare Module X : XF.
End S.

Module A : S.
  Module X.
    Definition c : bool := true.
    Definition hc : eq bool c true := eq_refl bool true.
    Definition d : bool := false.
  End X.
End A.

Module F (P : S).
  Definition c' : bool := P.X.c.
  Definition e : eq bool P.X.d false := eq_refl bool false.
End F.

Module Type T.
  Definition c' : bool := A.X.c.
  Parameter e : eq bool A.X.c false.
End T.

Module R : T.
  Definition c' : bool := A.X.c.
  Axiom e : eq bool A.X.c false.
End R.
