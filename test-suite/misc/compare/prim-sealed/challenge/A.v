(* A module type S with a type field T, a module M sealed by S whose T is a
   parameter, and a theorem over M.T. The config permits M.T as an
   axiom. *)

Module Type S.
  Parameter T : Set.
End S.

Module M : S.
  Parameter T : Set.
End M.

Theorem thm : forall _ : M.T, True.
Proof.
Admitted.
