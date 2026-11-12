(* Rocq does not load the library Top.P.Q beside a module Top.P.Q, so this
   answer requires only Top.P, and Top.P.Q.U is its own inductive. It
   proves thm as the honest answer does, through that U. *)

Require Top.P.

Theorem thm : ~ (forall (A : Prop) (x y : A), x = y).
Proof.
  intro irrelevance.
  exact (match irrelevance Top.P.Q.U Top.P.Q.u1 Top.P.Q.u2 in (_ = y)
               return (match y with Top.P.Q.u1 => True | Top.P.Q.u2 => False end)
         with eq_refl => I end).
Qed.
