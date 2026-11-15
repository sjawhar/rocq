(* Against the forged Lib.vo of case "sealed", M.f's type reads M.d = false
   and M.d's canonical name is M.c. *)

Require Import SigAlias.Lib.

Definition both : eq bool true false :=
  eq_trans bool true M.c false (eq_sym bool M.c true M.e) M.f.

Definition contradiction : False :=
  match both in eq _ _ y return discr y with
  | eq_refl _ _ => I
  end.
