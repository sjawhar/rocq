(* The honest answer: the challenge, T registered as in the challenge, with
   the proof written. *)

Primitive T := #int63_type.

Theorem thm : forall _ : T, True.
Proof. exact (fun _ => I). Qed.
