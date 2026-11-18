(* The honest answer proves L with Qed, so L stays opaque, and thm from
   the permitted axiom L_nat. *)

Polymorphic Lemma L@{s;u} (A : Type@{s;u}) (a : A) : A.
Proof. exact a. Qed.

Axiom L_nat : forall n : nat, L nat n = n.

Theorem thm : L nat 0 = 0.
Proof. apply L_nat. Qed.
