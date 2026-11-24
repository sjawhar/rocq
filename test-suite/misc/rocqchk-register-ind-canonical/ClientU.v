(* D_U, the client of C' in rocqchk_register_ind_canonical.sh, compiled
   with -noinit against C' (C with its registration of B as bool given the
   canonical name of U), never against C. Its primitive ltb returns U,
   which converts with the registered bool once C' is in force, and
   ltb max_length max_length computes the second constructor of bool, which
   the match reads as u2 with no proof of False: boom is a closed proof of
   False. Relinked to C, the type of ltb is not the operator's. *)

Require Import RegInd.Lib.

Primitive ltb : forall (_ : int) (_ : int), U := #int63_lt.

Definition boom : False :=
  match ltb max_length max_length as y
        return match y with u1 => True | u2 _ => False end
  with u1 => I | u2 f => f end.
