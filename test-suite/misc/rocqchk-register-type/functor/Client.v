(* An honest client of functor/Lib.v. *)

Require Import RegType.Lib.

Definition uses : forall _ : R.M.int, False := R.M.int_empty.
