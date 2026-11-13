(* An honest client of sealed/Lib.v. *)

Require Import RegType.Lib.

Definition uses : forall _ : M.int, False := M.int_empty.
