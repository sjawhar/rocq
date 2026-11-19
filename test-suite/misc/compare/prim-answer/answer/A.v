(* The honest answer: the challenge, with thm proved from the permitted
   element t0. *)

Parameter T : Set.

Parameter t0 : T.

Theorem thm : exists x : T, True.
Proof. exact (ex_intro _ t0 I). Qed.
