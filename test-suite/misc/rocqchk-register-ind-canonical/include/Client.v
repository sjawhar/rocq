(* The client of A2 (Lib.v here) in rocqchk_register_ind_canonical.sh,
   compiled with -noinit against it. Its primitive ltb returns M.B, the
   registered bool, and t type-checks only with that registration in
   force. *)

Require Import RegInd.Lib.

Primitive ltb : forall (_ : int) (_ : int), M.B := #int63_lt.

Definition t : match ltb max_length max_length with M.true => False | M.false => True end := I.
