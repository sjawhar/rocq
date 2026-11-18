(* A module type MT whose field p, a proof of True, the challenge leaves
   open, and a theorem. A field of a module type is a declaration a module
   of that type must provide, not one the answer may fill. *)

Module Type MT.
  Parameter p : True.
End MT.

Theorem thm : True.
Proof.
Admitted.
