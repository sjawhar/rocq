(* The honest answer to B.v, the other way round: FT declared first, its
   parameters renamed to V and X, its field naming the second one, then G.
   The inner parameter X of this FT has the name of the outer parameter X of
   the challenge's FT. The challenge's X stands for V and its Y for this X;
   renamed twice, Y would stand for V and the field would differ. *)

Module Type SIG.
  Parameter P : Prop.
End SIG.

Module Type FT (V : SIG) (X : SIG).
  Parameter q : X.P.
End FT.

Module Type G (Z : SIG).
End G.

Theorem thm : forall A : Prop, A -> A.
Proof. intros A a; exact a. Qed.
