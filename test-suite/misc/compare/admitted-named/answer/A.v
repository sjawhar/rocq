(* The honest answer proves L with Qed, so L stays opaque, and thm from
   the permitted axiom. *)

Axiom proof_irrelevance : forall (P : Prop) (p q : P), p = q.

Lemma L : exists n, n = 0.
Proof. exists 0; reflexivity. Qed.

Theorem thm : L = ex_intro _ 0 eq_refl.
Proof. apply proof_irrelevance. Qed.
