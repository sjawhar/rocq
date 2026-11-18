(* A module type SIG, a functor module type FT over two parameters X and Y
   of type SIG whose field q names the first one, X, and a theorem. The
   kernel name of a functor parameter holds a number from a counter that
   each functor parameter declared before it in the file advanced, so a
   parameter declared earlier changes the names of the ones after it. *)

Module Type SIG.
  Parameter P : Prop.
End SIG.

Module Type FT (X : SIG) (Y : SIG).
  Parameter q : X.P.
End FT.

Theorem thm : forall A : Prop, A -> A.
Proof.
Admitted.
