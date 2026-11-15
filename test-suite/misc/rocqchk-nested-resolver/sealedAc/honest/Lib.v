(* Case "sealedAc": the honest library. A is sealed by S; A.X.c is
   declared-only in A's signature, which states hc : c = true, and A.X.d is a
   definition there (d := false). R is sealed by T. The forged Lib.vo is this
   file's Lib.vo with the alias A.X.d -> A.X.c added to A's delta resolver
   (the signature's) only, and, in T and in R's stored signature, e's type
   eq bool A.X.d false changed to eq bool A.X.c false. *)

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
  Parameter e : eq bool A.X.d false.
End T.

Module R : T := F A.
