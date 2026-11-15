(* The library the forged clients are compiled against: honest/Lib.v, except
   that T's f and TF's f say c = false and M1.c = false (axioms of M and M2
   here), so that coqc accepts the clients' proofs of true = false, and that
   F also proves it, for the sealed N. Each forged client then records the
   forged Lib.vo's digest instead of this file's. The forged library of case
   "functor" is this file's Lib.vo with honest/Lib.v's T and M. *)

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

Module Type T.
  Parameter c d : bool.
  Parameter e : eq bool c true.
  Parameter f : eq bool c false.
End T.

Module M : T.
  Definition c : bool := true.
  Definition d : bool := false.
  Definition e : eq bool c true := eq_refl bool true.
  Parameter f : eq bool c false.
End M.

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
  Parameter f : eq bool M1.c false.
End TF.

Module M2 : TF.
  Definition c : bool := false.
  Parameter f : eq bool M1.c false.
End M2.

Module F (X : T).
  (* dd gives the forger X.d's kernel name. *)
  Definition dd : eq bool X.d X.d := eq_refl bool X.d.
  Definition uses : eq bool X.c true := X.e.
  Definition both : eq bool true false :=
    eq_trans bool true X.c false (eq_sym bool X.c true X.e) X.f.
End F.

Module Type TN.
  Parameter uses : eq bool M.c true.
  Parameter both : eq bool true false.
End TN.

Module N : TN := F M.
