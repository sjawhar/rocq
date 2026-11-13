(* The forged sealed client's source: max_length is an int63 literal, of
   the registered type M.int. *)

Require Import RegType.Lib.

Primitive max_length := #array_max_length.

Definition boom : False := M.int_empty max_length.
