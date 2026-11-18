(* The challenge leaves the lemma L, a proposition, without a body, and
   states thm about L itself: L is one particular proof. With L opaque, thm
   follows from proof irrelevance, which the task declares as an axiom and
   the config permits. An answer that gave L a transparent body could prove
   thm by computation instead. *)

Axiom proof_irrelevance : forall (P : Prop) (p q : P), p = q.

Lemma L : exists n, n = 0.
Admitted.

Theorem thm : L = ex_intro _ 0 eq_refl.
Proof.
Admitted.
