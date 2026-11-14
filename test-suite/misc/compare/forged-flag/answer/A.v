(* The honest answer proves thm through the tolerated given U: proof
   irrelevance would make u1 and u2 equal, and a match on U that returns a
   Prop tells them apart. *)

Require Top.P.
Require Top.P.Q.

Theorem thm : ~ (forall (A : Prop) (x y : A), x = y).
Proof.
  intro irrelevance.
  exact (match irrelevance Top.P.Q.U Top.P.Q.u1 Top.P.Q.u2 in (_ = y)
               return (match y with Top.P.Q.u1 => True | Top.P.Q.u2 => False end)
         with eq_refl => I end).
Qed.
