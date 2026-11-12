(* The honest library of the rocq-sigalias-sealed forge (dispatch://BET-885):
   M is sealed by T, whose fields are all declared-only. This is BET-885's
   sigalias case "sealed", honest/Lib.v and honest/Client.v in one file, on
   the Corelib prelude. rocqchk must accept it. *)

Module Type T.
  Parameter c d : bool.
  Parameter e : c = true.
  Parameter f : d = false.
End T.

Module M : T.
  Definition c : bool := true.
  Definition d : bool := false.
  Definition e : c = true := eq_refl.
  Definition f : d = false := eq_refl.
End M.

Definition uses : M.c = true := M.e.
