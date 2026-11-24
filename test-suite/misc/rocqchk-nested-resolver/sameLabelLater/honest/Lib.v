(* Case "sameLabelLater": the honest library. A is not sealed; R is sealed
   by T. The forged Lib.vo (forge.ml same-label) is this file's Lib.vo with
   the alias A.X.d -> A.Y.d, which keeps the label d, added to A's delta
   resolver only, and, in T and in R's stored signature, e's type
   eq bool A.X.d false changed to eq bool A.Y.d false. Y comes after X, so
   that A.Y.d is not in the environment when A.X is checked: rocqchk must
   refuse the alias with the module typing error of the other alias checks,
   not stop on the anomaly that says A.Y.d does not appear in the
   environment. c' names A.Y.d for forge.ml. *)

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
    Definition d : bool := false.
  End X.
  Module Y.
    Definition d : bool := true.
  End Y.
End A.

Module Type XT.
  Parameter d : bool.
End XT.

Module Type S.
  Declare Module X : XT.
End S.

Module F (P : S).
  Definition c' : bool := A.Y.d.
  Definition e : eq bool P.X.d P.X.d := eq_refl bool P.X.d.
End F.

Module Type T.
  Definition c' : bool := A.Y.d.
  Parameter e : eq bool A.X.d false.
End T.

Module R : T := F A.
