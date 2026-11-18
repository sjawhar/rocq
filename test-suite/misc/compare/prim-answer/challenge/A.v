(* An abstract type T, an element t0 of it, and a theorem that T is
   inhabited. The config permits T and t0 as axioms, so an honest answer
   proves thm from t0. *)

Parameter T : Set.

Parameter t0 : T.

Theorem thm : exists x : T, True.
Proof.
Admitted.
