(* The honest answer declares one more universe before box, so the default
   level of box's template parameter, a global level, has another number
   than in the challenge; box is otherwise the challenge's. The template
   data are compared through the map of levels, a bound level by its
   position, so the answer passes. A comparison of the default levels as
   they are fails it. *)

Unset Elimination Schemes.

Universe extra.

#[universes(template)]
Inductive box (A : Type) : Type := mk : A -> box A.

Theorem thm : forall A : Type, A -> box A.
Proof. intros A a; exact (mk A a). Qed.
