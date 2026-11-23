(* The client of A3 (sealed/Lib.v) in rocqchk_register_ind_canonical.sh,
   compiled with -noinit against it, in the scratch directory of its set.
   Its primitive ltb returns N.B: the registration of B in M has the
   canonical name of N.B, and M.B, which S seals, has one of its own. t
   type-checks only with that registration in force. *)

Require Import RegInd.Lib.

Primitive ltb : forall (_ : int) (_ : int), N.B := #int63_lt.

Definition t : match ltb max_length max_length with N.true => False | N.false => True end := I.
