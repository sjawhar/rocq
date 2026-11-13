(* The forged functor client's source: max_length is an int63 literal, of
   the registered type R.M.int. *)

Require Import RegType.Lib.

Primitive max_length := #array_max_length.

Definition boom : False := R.M.int_empty max_length.
