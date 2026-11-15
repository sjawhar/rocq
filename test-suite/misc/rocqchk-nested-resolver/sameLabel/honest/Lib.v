(* Case "sameLabel": the honest library. A is not sealed; R is sealed by T.
   The forged Lib.vo (forge.ml same-label) is this file's Lib.vo with the
   alias A.X.d -> A.Y.d, which keeps the label d, added to A's delta
   resolver only, and, in T and in R's stored signature, e's type
   eq bool A.X.d false changed to eq bool A.Y.d false. Y comes before X, so
   that A.Y.d is in the environment when A.X is checked. c' names A.Y.d for
   forge.ml. *)

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
  Module Y.
    Definition d : bool := true.
  End Y.
  Module X.
    Definition d : bool := false.
  End X.
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
