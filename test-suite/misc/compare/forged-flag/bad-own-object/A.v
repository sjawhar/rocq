(* The answer declares an inductive of its own, Top.A.V, with the
   elimination check off, and proves thm through it rather than through the
   given U. The config tolerates unchecked-eliminations on Top.P.Q.U alone,
   so the flag on Top.A.V is not tolerated. *)

Require Top.P.
Require Top.P.Q.

Declare ML Module "coq-test-suite.elim_flag".

Unset Test Elimination Checking.

Inductive V : Prop :=
| v1 : V
| v2 : V.

Set Test Elimination Checking.

Theorem thm : ~ (forall (A : Prop) (x y : A), x = y).
Proof.
  intro irrelevance.
  exact (match irrelevance V v1 v2 in (_ = y)
               return (match y with v1 => True | v2 => False end)
         with eq_refl => I end).
Qed.
