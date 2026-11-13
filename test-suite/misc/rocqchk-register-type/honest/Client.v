(* The honest client: it uses the registered types and the operators of
   Lib.v. *)

Require Import RegType.Lib.

Definition max : int := max_length.

Definition float : Set := Float.float.

Definition string : Set := Str.string.

Definition ops : int := Mul.mul (sub (add max max) max) max.

Definition arr : array int := make int max max.
