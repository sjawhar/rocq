(* A functor module type FT over two parameters X and Y whose field q
   names the first one, X. The name of a functor parameter is a counter of
   the parameters the file declared before it, its identifier and its
   library, so a parameter of one side may have the name of a parameter of
   the other: the answer's A.v gives its outer parameter the name of this
   file's inner parameter Y. *)

Module Type SIG.
  Parameter P : Prop.
End SIG.

Module Type FT (X : SIG) (Y : SIG).
  Parameter q : X.P.
End FT.

Theorem thm : forall A : Prop, A -> A.
Proof.
Admitted.
