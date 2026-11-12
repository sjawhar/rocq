(* Case "sealed": the source of the corrupted client, compiled against
   donor/Lib.v. In the forged library M.lem : forall b, eq bool b M.d, with
   M.d a parameter of M's signature. *)

Require Import InlineHint.Lib.

Definition boom : eq bool true false :=
  eq_trans bool true M.d false (M.lem true) (eq_sym bool false M.d (M.lem false)).

(* A closed proof of False. *)
Definition contradiction : False :=
  match boom in eq _ _ y return discr y with
  | eq_refl _ _ => I
  end.
