(* Forge, dispatch://BET-885: a .vo in which only A's delta resolver says
   that A.X.d is A.X.c, while the resolver of A's submodule X does not, gives
   a closed proof of False through the sealed functor application
   R : T := F A. This is BET-885's functor-delta case "sealed": the variant
   library donor/Lib.v (T's e reads A.X.c = false, and R implements T with
   an axiom e), the client donor/Client.v compiled against it, and a module
   Forge_fdelta. Given Forge_fdelta, the reverted build's coqc (unfix.patch)
   writes R as the application F A, as Control.v has it, and adds
   A.X.d -> A.X.c to A's resolver only. Then R has no axiom, R.e reads
   A.X.c = false, A.X.c is true, and contradiction has type False. *)

Definition discr (b : bool) : Prop := if b then True else False.

Module A.
  Module X.
    Definition c : bool := true.
    Definition d : bool := false.
  End X.
End A.

Module Type XT.
  Parameter c d : bool.
End XT.

Module Type S.
  Declare Module X : XT.
End S.

Module F (P : S).
  Definition c' : bool := P.X.c.
  Definition e : P.X.d = P.X.d := eq_refl.
End F.

Module Type T.
  Definition c' : bool := A.X.c.
  Parameter e : A.X.c = false.
End T.

Module R : T.
  Definition c' : bool := A.X.c.
  Axiom e : A.X.c = false.
End R.

Definition boom : true = false := R.e.

Definition contradiction : False :=
  match boom in _ = y return discr y with eq_refl => I end.

Module Forge_fdelta.
End Forge_fdelta.
