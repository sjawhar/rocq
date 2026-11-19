(* The honest answer to A.v: G declared first, then FT with its parameters
   renamed to Y and W, its field naming the first one. G's parameter takes
   a count, so the outer parameter Y of this FT has the name of the inner
   parameter Y of the challenge's FT. The comparison renames each challenge
   parameter once, to the answer's parameter of the same position: the
   challenge's X stands for this Y, and its Y for W. Renamed twice, X would
   stand for W and the field would differ. *)

Module Type SIG.
  Parameter P : Prop.
End SIG.

Module Type G (Z : SIG).
End G.

Module Type FT (Y : SIG) (W : SIG).
  Parameter q : Y.P.
End FT.

Theorem thm : forall A : Prop, A -> A.
Proof. intros A a; exact a. Qed.
