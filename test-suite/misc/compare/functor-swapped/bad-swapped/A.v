(* functor-param's honest answer, an unrelated functor module type G before
   FT, with FT's field q naming the other parameter, Y, where the
   challenge's names X. The comparison renames the challenge's X to the
   answer's X and its Y to the answer's Y, by position, so q differs and the
   answer fails, naming the module type FT. A comparison that took every
   functor parameter for every other would pass it. *)

Module Type SIG.
  Parameter P : Prop.
End SIG.

Module Type G (Z : SIG).
End G.

Module Type FT (X : SIG) (Y : SIG).
  Parameter q : Y.P.
End FT.

Theorem thm : forall A : Prop, A -> A.
Proof. intros A a; exact a. Qed.
