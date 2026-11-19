(* The answer's module type MT defines its field p, which the challenge's
   leaves open. A field of a module type is compared with no environment to
   type it in, so its stated sort is undetermined, though p is a proof:
   the challenge leaves p open and the answer defines it, and the answer
   fails, naming MT. *)

Module Type MT.
  Definition p : True := I.
End MT.

Theorem thm : True.
Proof. exact I. Qed.
