(* C, the library of rocqchk_register_ind_canonical.sh, compiled with
   -noinit, so that no other library registers bool or int. It registers B
   as the primitive bool: its only Register_ind is that of B, and the
   Register_type of int, which Primitive declares, is its other stored
   action. forge.ml ind-canonical and ind-repeat rewrite or repeat that
   Register_ind: the forged C' gives it the canonical name of U, whose
   second constructor takes a proof of False. The definition names names B
   and U, so that forge.ml takes their kernel names from the file. *)

Unset Elimination Schemes.

Inductive True : Prop := I.
Inductive False : Prop := .

Primitive int := #int63_type.
Primitive max_length := #array_max_length.

Inductive B : Set := true | false.
Inductive U : Set := u1 | u2 (_ : False).

Register B as kernel.ind_bool.

Definition names (_ : B) : U := u1.
