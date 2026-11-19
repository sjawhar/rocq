(* admitted-named's challenge, whose config names L as a theorem too: the
   lemma L, a proposition, left without a body, and thm about L itself,
   which follows from the permitted proof irrelevance while L is opaque. *)

Axiom proof_irrelevance : forall (P : Prop) (p q : P), p = q.

Lemma L : exists n, n = 0.
Admitted.

Theorem thm : L = ex_intro _ 0 eq_refl.
Proof.
Admitted.
