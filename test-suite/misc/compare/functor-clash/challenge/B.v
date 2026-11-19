(* An unrelated functor module type G, then a functor module type FT over
   two parameters X and Y whose field q names the second one, Y. The
   answer's B.v gives its inner parameter the name of this file's outer
   parameter X. *)

Module Type SIG.
  Parameter P : Prop.
End SIG.

Module Type G (Z : SIG).
End G.

Module Type FT (X : SIG) (Y : SIG).
  Parameter q : Y.P.
End FT.

Theorem thm : forall A : Prop, A -> A.
Proof.
Admitted.
