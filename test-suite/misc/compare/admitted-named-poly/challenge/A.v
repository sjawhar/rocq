(* The challenge leaves L without a body. L is sort-polymorphic: its stated
   type lives in the sort variable s, so it is neither a proposition nor
   data. The axiom L_nat, which the config permits, and thm both name L,
   and the config names L as a theorem as well as thm. With L opaque, thm
   follows from L_nat; an answer that gave L a transparent body could prove
   it by computation instead. *)

Polymorphic Lemma L@{s;u} (A : Type@{s;u}) (a : A) : A.
Admitted.

Axiom L_nat : forall n : nat, L nat n = n.

Theorem thm : L nat 0 = 0.
Proof.
Admitted.
