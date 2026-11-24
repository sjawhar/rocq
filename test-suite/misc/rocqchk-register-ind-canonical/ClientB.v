(* D_B, the client of C (Lib.v) in rocqchk_register_ind_canonical.sh,
   compiled with -noinit against C. Its primitive ltb returns B, the type C
   registers as bool, and t type-checks only with that registration in
   force: ltb max_length max_length computes false. The test relinks it to
   the control, to C'' and to the library of the set repeated-last. *)

Require Import RegInd.Lib.

Primitive ltb : forall (_ : int) (_ : int), B := #int63_lt.

Definition t : match ltb max_length max_length with true => False | false => True end := I.
