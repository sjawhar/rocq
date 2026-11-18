(* The honest answer: the challenge, with the proof written. *)

Module Type S.
  Parameter T : Set.
End S.

Module M : S.
  Parameter T : Set.
End M.

Theorem thm : forall _ : M.T, True.
Proof. exact (fun _ => I). Qed.
