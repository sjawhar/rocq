(* The client of the forged label/Lib.vo in rocqchk_register_ind_label.sh,
   compiled with -noinit against the forged library, whose registration of
   B as bool has the canonical name of N.B. Its primitive ltb returns N.B,
   which converts with the registered bool once the forged library is in
   force, and boom is a closed proof of False. *)

Require Import RegInd.Lib.

Primitive ltb : forall (_ : int) (_ : int), N.B := #int63_lt.

Definition boom : False :=
  match ltb max_length max_length as y
        return match y with N.u1 => True | N.u2 _ => False end
  with N.u1 => I | N.u2 f => f end.
