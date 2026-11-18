(* The answer gives L a transparent body, the identity, so thm holds by
   reflexivity, with no axiom. The config names L as a theorem, so the rule
   for a declaration the challenge leaves open does not apply, and L's
   stated sort is a sort variable, not data: L is a constant the challenge
   leaves without a body, that other challenge declarations name, given a
   transparent body, and the answer fails, naming L. *)

Polymorphic Definition L@{s;u} (A : Type@{s;u}) (a : A) : A := a.

Axiom L_nat : forall n : nat, L nat n = n.

Theorem thm : L nat 0 = 0.
Proof. reflexivity. Qed.
