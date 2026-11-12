(* Case "sealedAc": the source of the corrupted client, compiled against
   donor/Lib.v. A.X.c is declared-only, so it is not unfolded:
   A.X.hc : A.X.c = true and, in the forged library, R.e : A.X.c = false. *)

Require Import NestedResolver.Lib.

Definition boom : eq bool true false :=
  eq_trans bool true A.X.c false (eq_sym bool A.X.c true A.X.hc) R.e.

(* A closed proof of False. *)
Definition contradiction : False :=
  match boom in eq _ _ y return discr y with
  | eq_refl _ _ => I
  end.
