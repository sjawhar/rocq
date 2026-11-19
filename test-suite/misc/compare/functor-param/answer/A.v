(* The honest answer adds an unrelated functor module type G before FT and
   leaves FT unchanged. G's parameter Z takes a count, so FT's parameters X
   and Y have other names than in the challenge. The comparison renames each
   challenge parameter to the answer's parameter of the same position, so
   FT's field q, which names X, is the challenge's and the answer passes. A
   comparison of the parameters' names as they are fails it. *)

Module Type SIG.
  Parameter P : Prop.
End SIG.

Module Type G (Z : SIG).
End G.

Module Type FT (X : SIG) (Y : SIG).
  Parameter q : X.P.
End FT.

Theorem thm : forall A : Prop, A -> A.
Proof. intros A a; exact a. Qed.
