(* Against the forged Lib.vo of case "functor", N.both comes from F's proof of
   true = false, which type-checks because X.d is an alias of X.c. *)

Require Import SigAlias.Lib.

Definition contradiction : False :=
  match N.both in eq _ _ y return discr y with
  | eq_refl _ _ => I
  end.
