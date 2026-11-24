(* The honest client of label/Lib.v in rocqchk_register_ind_label.sh,
   compiled with -noinit against the honest library. Its primitive ltb
   returns B, the type the library registers as bool. *)

Require Import RegInd.Lib.

Primitive ltb : forall (_ : int) (_ : int), B := #int63_lt.

Definition t : match ltb max_length max_length with true => False | false => True end := I.
