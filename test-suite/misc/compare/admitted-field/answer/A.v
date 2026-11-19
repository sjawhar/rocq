(* The honest answer: the challenge, its field p left open, with the proof
   written. *)

Module Type MT.
  Parameter p : True.
End MT.

Theorem thm : True.
Proof. exact I. Qed.
