(* A module type SIG, a functor module type FT over two parameters X and Y
   of type SIG whose field q names the first one, X, and a theorem. *)

Module Type SIG.
  Parameter P : Prop.
End SIG.

Module Type FT (X : SIG) (Y : SIG).
  Parameter q : X.P.
End FT.

Theorem thm : forall A : Prop, A -> A.
Proof.
Admitted.
