(* Case "sealed": the honest library. M is sealed by S. The forged Lib.vo is
   this file's Lib.vo with M's stored signature field lem taken from
   donor/Lib.vo (lem : forall b, eq bool b M.d), and M's implementation
   resolver given the inline hint M.d -> Inline (0, Some (Rel 1)). *)

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

Module Type S.
  Parameter d : bool.
  Parameter lem : forall b : bool, eq bool b b.
End S.

Module M : S.
  Definition d : bool := true.
  Definition lem : forall b : bool, eq bool b b := fun b => eq_refl bool b.
End M.
