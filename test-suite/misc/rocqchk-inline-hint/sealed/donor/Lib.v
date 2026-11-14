(* Case "sealed": the library that the corrupted client is compiled against,
   and the source of the forged signature field M.lem. Same logical name and
   the same declarations as honest/Lib.v, except that S's and M's lem say
   forall b, eq bool b d, and M implements lem with an axiom. The corrupted
   client then records the forged Lib.vo's checksum instead of this
   file's. *)

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
  Parameter lem : forall b : bool, eq bool b d.
End S.

Module M : S.
  Definition d : bool := true.
  Axiom lem : forall b : bool, eq bool b d.
End M.
