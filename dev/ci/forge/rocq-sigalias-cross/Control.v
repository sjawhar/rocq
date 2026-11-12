(* The honest library of the rocq-sigalias-cross forge (dispatch://BET-885):
   M1 and M2 are sealed by TT and TF, whose fields are all declared-only.
   This is BET-885's sigalias case "cross", honest/Lib.v and honest/Client.v
   in one file, on the Corelib prelude. rocqchk must accept it. *)

Module Type TT.
  Parameter c : bool.
  Parameter e : c = true.
End TT.

Module M1 : TT.
  Definition c : bool := true.
  Definition e : c = true := eq_refl.
End M1.

Module Type TF.
  Parameter c : bool.
  Parameter f : c = false.
End TF.

Module M2 : TF.
  Definition c : bool := false.
  Definition f : c = false := eq_refl.
End M2.

Definition uses : M1.c = true := M1.e.
