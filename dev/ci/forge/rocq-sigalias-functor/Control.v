(* The honest library of the rocq-sigalias-functor forge (dispatch://BET-885):
   M is sealed by T, whose fields are all declared-only, F takes a parameter
   of type T, and N is F applied to M, sealed by TN. This is BET-885's
   sigalias case "functor", honest/Lib.v and honest/Client.v in one file, on
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

Module F (X : T).
  Definition dd : X.d = X.d := eq_refl.
  Definition uses : X.c = true := X.e.
End F.

Module Type TN.
  Parameter uses : M.c = true.
End TN.

Module N : TN := F M.

Definition uses : M.c = true := N.uses.
