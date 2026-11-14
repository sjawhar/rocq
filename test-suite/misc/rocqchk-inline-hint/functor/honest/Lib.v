(* Case "functor": the honest library. The forged Lib.vo is this file's
   Lib.vo with A's delta resolver given the inline hint
   A.d -> Inline (0, Some (Rel 1)). F proves, for any P.d,
   lem : (forall b, eq bool b P.d) -> eq bool true false; in F A, the hint
   would turn P.d under the binder b into b itself. use_d only names A.d, so
   that the forger can read A.d's kernel name from the file. *)

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
  (* (forall b, b = P.d) -> true = false, written without the -> notation (-noinit). *)
  Definition lem : forall _ : (forall b : bool, eq bool b P.d), eq bool true false :=
    fun H => eq_trans bool true P.d false (H true) (eq_sym bool false P.d (H false)).
End F.
