(* Case "functor": the source of the corrupted client, compiled against
   donor/Lib.v. With the forged hint of A, F A would compute
   lem : (forall b, eq bool b b) -> eq bool true false, T's type. *)

Require Import InlineHint.Lib.

Module Type T.
  Parameter lem : forall _ : (forall b : bool, eq bool b b), eq bool true false.
End T.

Module G : T := F A.

Definition boom : eq bool true false := G.lem (fun b => eq_refl bool b).

(* A closed proof of False. *)
Definition contradiction : False :=
  match boom in eq _ _ y return discr y with
  | eq_refl _ _ => I
  end.
