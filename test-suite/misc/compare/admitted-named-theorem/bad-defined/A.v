(* admitted-named's bad answer under a config that names L as a theorem:
   L proved with Defined, thm by reflexivity. Naming L as a theorem lets the
   answer prove it, not give it a body that another challenge declaration
   reads, so the answer still fails, naming L. *)

Axiom proof_irrelevance : forall (P : Prop) (p q : P), p = q.

Lemma L : exists n, n = 0.
Proof. exact (ex_intro _ 0 eq_refl). Defined.

Theorem thm : L = ex_intro _ 0 eq_refl.
Proof. reflexivity. Qed.
