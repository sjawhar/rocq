(* A2, the library of the set honest-include of
   rocqchk_register_ind_canonical.sh, compiled with -noinit. It registers
   B as bool through M, which includes N, so that the stored registration
   has the user name RegInd.Lib.M.B; its canonical name is the one coqc
   gives it, which the test prints. A1 (../alias/Lib.v) and A2 are two
   libraries because one library cannot register bool under two user
   names. *)

Unset Elimination Schemes.

Inductive True : Prop := I.
Inductive False : Prop := .

Primitive int := #int63_type.
Primitive max_length := #array_max_length.

Module N.
  Inductive B : Set := true | false.
End N.

Module M.
  Include N.
End M.

Register M.B as kernel.ind_bool.
