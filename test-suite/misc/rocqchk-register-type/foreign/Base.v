(* A library that registers nothing, compiled with -noinit: its definition
   int is the constant that the forged foreign and dual Lib.vo register as
   the int63 type, though their Lib.v does not declare it. *)

Unset Elimination Schemes.

Inductive False : Prop := .
Inductive Empty_set : Set := .

Definition int : Set := Empty_set.
