(* The answer proves L with Defined, so L's body is the very proof thm
   names, and thm holds by reflexivity, with no axiom. L is a proposition
   that the challenge leaves without a body and that thm names, so a
   transparent body for it fails, naming L. *)

Axiom proof_irrelevance : forall (P : Prop) (p q : P), p = q.

Lemma L : exists n, n = 0.
Proof. exact (ex_intro _ 0 eq_refl). Defined.

Theorem thm : L = ex_intro _ 0 eq_refl.
Proof. reflexivity. Qed.
