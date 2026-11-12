(* Case "sameLabel": the source of the corrupted client, compiled against
   donor/Lib.v. In the forged library R.e : eq bool A.Y.d false, and A.Y.d is
   true. *)

Require Import NestedResolver.Lib.

Definition boom : eq bool true false := R.e.

(* A closed proof of False. *)
Definition contradiction : False :=
  match boom in eq _ _ y return discr y with
  | eq_refl _ _ => I
  end.
