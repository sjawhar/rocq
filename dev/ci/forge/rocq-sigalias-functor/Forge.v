(* Forge, dispatch://BET-885: a .vo whose functor parameter's signature
   records that one declared-only field is an alias of another of the same
   type gives a closed proof of False. This is BET-885's sigalias case
   "functor": the variant library donor/Lib.v (T's f reads c = false, M's f is
   an axiom, F proves true = false from its parameter, and TN, which seals N,
   declares that proof), the client donor/Client.v compiled against it, and a
   module Forge_functor with Control.v's T and M. Given Forge_functor, the
   reverted build's coqc (unfix.patch) writes Forge_functor.M as M and
   Forge_functor.T as the type of F's parameter X, records in that type that
   X.d is an alias of X.c, and names X.d (canonical X.c) in that type and in
   F's body. Then M has no axiom, X's f reads X.c = false in F's body, N.both
   proves true = false, and contradiction has type False. *)

Definition discr (b : bool) : Prop := if b then True else False.

Module Type T.
  Parameter c d : bool.
  Parameter e : c = true.
  Parameter f : c = false.
End T.

Module M : T.
  Definition c : bool := true.
  Definition d : bool := false.
  Definition e : c = true := eq_refl.
  Parameter f : c = false.
End M.

Module F (X : T).
  Definition dd : X.d = X.d := eq_refl.
  Definition uses : X.c = true := X.e.
  Definition both : true = false := eq_trans (eq_sym X.e) X.f.
End F.

Module Type TN.
  Parameter uses : M.c = true.
  Parameter both : true = false.
End TN.

Module N : TN := F M.

Definition uses : M.c = true := N.uses.

Definition boom : true = false := N.both.

Definition contradiction : False :=
  match boom in _ = y return discr y with eq_refl => I end.

Module Forge_functor.
  Module Type T.
    Parameter c d : bool.
    Parameter e : c = true.
    Parameter f : d = false.
  End T.

  Module M : T.
    Definition c : bool := true.
    Definition d : bool := false.
    Definition e : c = true := eq_refl.
    Definition f : d = false := eq_refl.
  End M.
End Forge_functor.
