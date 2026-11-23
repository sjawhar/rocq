(* A3, the library of the set honest-sealed of
   rocqchk_register_ind_canonical.sh, compiled with -noinit. It registers
   B as bool inside M, which S seals and which includes N, so that the
   stored registration has the user name RegInd.Lib.M.B; its canonical name
   is the one coqc gives B in the implementation of M, which the test
   prints. rocqchk checks the type of M, which gives M.B a canonical name of
   its own, before its implementation. *)

Unset Elimination Schemes.

Inductive True : Prop := I.
Inductive False : Prop := .

Primitive int := #int63_type.
Primitive max_length := #array_max_length.

Module Type S.
  Inductive B : Set := true | false.
End S.

Module N.
  Inductive B : Set := true | false.
End N.

Module M : S.
  Include N.
  Register B as kernel.ind_bool.
End M.
