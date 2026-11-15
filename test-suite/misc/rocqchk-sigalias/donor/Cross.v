(* Against the forged Lib.vo of case "cross", M2.f's type reads M2.c = false
   and M2.c's canonical name is M1.c. *)

Require Import SigAlias.Lib.

Definition both : eq bool true false :=
  eq_trans bool true M1.c false (eq_sym bool M1.c true M1.e) M2.f.

Definition contradiction : False :=
  match both in eq _ _ y return discr y with
  | eq_refl _ _ => I
  end.
