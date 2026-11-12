(* The honest library of rocqchk_sigalias.sh. Each case's forged copy of this
   file records, in a module signature, an alias between two declared-only
   fields whose implementations differ. *)

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

(* Case "sealed": in M's signature, M.d becomes an alias of M.c. *)
Module Type T.
  Parameter c d : bool.
  Parameter e : eq bool c true.
  Parameter f : eq bool d false.
End T.

Module M : T.
  Definition c : bool := true.
  Definition d : bool := false.
  Definition e : eq bool c true := eq_refl bool true.
  Definition f : eq bool d false := eq_refl bool false.
End M.

(* Case "cross": in M2's signature, M2.c becomes an alias of M1.c; the alias
   keeps its label, as the ones coqc writes do. *)
Module Type TT.
  Parameter c : bool.
  Parameter e : eq bool c true.
End TT.

Module M1 : TT.
  Definition c : bool := true.
  Definition e : eq bool c true := eq_refl bool true.
End M1.

Module Type TF.
  Parameter c : bool.
  Parameter f : eq bool c false.
End TF.

Module M2 : TF.
  Definition c : bool := false.
  Definition f : eq bool c false := eq_refl bool false.
End M2.

(* Case "functor": in the type of F's parameter, X.d becomes an alias of X.c.
   The forged library is donor/Lib.vo with this file's T and M. *)
Module F (X : T).
  Definition dd : eq bool X.d X.d := eq_refl bool X.d.
  Definition uses : eq bool X.c true := X.e.
End F.

Module Type TN.
  Parameter uses : eq bool M.c true.
End TN.

Module N : TN := F M.
