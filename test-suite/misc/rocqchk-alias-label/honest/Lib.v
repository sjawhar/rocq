(* The honest library of rocqchk_alias_label.sh. Its forged copy records, in
   F's body, that F.k is an alias of P.X.d, from label k to label d: F's
   delta resolver gets the entry, and lemma's type names F.k as (user F.k,
   canonical P.X.d). F.k := P.X.d converts with its target, so only the
   labels tell this alias from an honest one. *)

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
    Definition k : bool := true.
    Definition f : eq bool d false := eq_refl bool false.
  End X.
End A.

Module Type XS.
  Parameter d : bool.
  Parameter f : eq bool d false.
End XS.

Module Type S.
  Declare Module X : XS.
End S.

Module F (P : S).
  Definition k : bool := P.X.d.
  Definition lemma : eq bool k false := P.X.f.
End F.
