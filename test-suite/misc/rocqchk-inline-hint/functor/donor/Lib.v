(* Case "functor": the library that the corrupted client is compiled
   against. Same logical name and the same declarations as honest/Lib.v,
   except that F's lem is an axiom of the type that the forged hint of A
   would give F A's lem: (forall b, eq bool b b) -> eq bool true false. The
   corrupted client then records the forged Lib.vo's checksum instead of
   this file's. *)

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

Module Type XS.
  Parameter d : bool.
End XS.

Module A.
  Definition d : bool := true.
End A.

Definition use_d : bool := A.d.

Module F (P : XS).
  Axiom lem : forall _ : (forall b : bool, eq bool b b), eq bool true false.
End F.
