(* The client of A1 (alias/Lib.v) and of A2 (include/Lib.v) in
   rocqchk_register_ind_canonical.sh, compiled with -noinit against each,
   in the scratch directory of its set. Its primitive ltb returns M.B, the
   registered bool, and t type-checks only with that registration in
   force. *)

Require Import RegInd.Lib.

Primitive ltb : forall (_ : int) (_ : int), M.B := #int63_lt.

Definition t : match ltb max_length max_length with M.true => False | M.false => True end := I.
