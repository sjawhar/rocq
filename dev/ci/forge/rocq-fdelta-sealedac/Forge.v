(* Forge, dispatch://BET-885: a .vo in which only A's delta resolver (the
   resolver of A's signature) says that A.X.d is A.X.c, while the resolver of
   A's submodule X does not, gives a closed proof of False through the sealed
   functor application R : T := F A: A is sealed, A.X.c is declared-only in
   its signature and A.X.d is a definition there. Forge.v is, on the Corelib
   prelude and in one file,
   test-suite/misc/rocqchk-nested-resolver/sealedAc/donor/: the variant
   library Lib.v (T's e reads A.X.c = false, and R implements T with an
   axiom e), the client Client.v compiled against it, and a module
   Forge_fdelta. Given Forge_fdelta, the reverted build's coqc (unfix.patch)
   writes R as the application F A, as Control.v has it, and adds
   A.X.d -> A.X.c to A's resolver only. Then R has no axiom, R.e reads
   A.X.c = false, A.X.hc reads A.X.c = true, and contradiction has type
   False. *)

Definition discr (b : bool) : Prop := if b then True else False.

Module Type XF.
  Parameter c : bool.
  Parameter hc : c = true.
  Definition d : bool := false.
End XF.

Module Type S.
  Declare Module X : XF.
End S.

Module A : S.
  Module X.
    Definition c : bool := true.
    Definition hc : c = true := eq_refl.
    Definition d : bool := false.
  End X.
End A.

Module F (P : S).
  Definition c' : bool := P.X.c.
  Definition e : P.X.d = false := eq_refl.
End F.

Module Type T.
  Definition c' : bool := A.X.c.
  Parameter e : A.X.c = false.
End T.

Module R : T.
  Definition c' : bool := A.X.c.
  Axiom e : A.X.c = false.
End R.

Definition boom : true = false := eq_trans (eq_sym A.X.hc) R.e.

Definition contradiction : False :=
  match boom in _ = y return discr y with eq_refl => I end.

Module Forge_fdelta.
End Forge_fdelta.
