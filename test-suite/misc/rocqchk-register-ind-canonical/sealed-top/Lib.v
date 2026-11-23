(* A4, the library of the set honest-sealed-top of
   rocqchk_register_ind_canonical.sh, compiled with -noinit. M, which S
   seals, includes N, and B is registered as bool after M, as M.B, so that
   the stored registration has the user name RegInd.Lib.M.B; its canonical
   name is the one coqc gives it, which the test prints. rocqchk checks the
   type of M, which gives M.B a canonical name of its own, before its
   implementation, which gives it that of N.B. *)

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
End M.

Register M.B as kernel.ind_bool.
