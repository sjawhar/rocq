(* Forge, dispatch://BET-885: a .vo whose sealed module's signature records
   that one declared-only field is an alias of another of the same type gives
   a closed proof of False. This is BET-885's sigalias case "sealed": the
   variant library donor/Lib.v (T's f reads c = false, and M's f is an axiom),
   the client donor/Client.v compiled against it, and a module Forge_sealed
   with Control.v's T and M. Given Forge_sealed, the reverted build's coqc
   (unfix.patch) writes Forge_sealed.M as M, records in M's signature that M.d
   is an alias of M.c, and names M.d (canonical M.c) in the signature's f.
   Then M has no axiom, its signature's f reads M.c = false, and
   contradiction has type False. *)

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

Definition uses : M.c = true := M.e.

Definition both : true = false := eq_trans (eq_sym M.e) M.f.

Definition contradiction : False :=
  match both in _ = y return discr y with eq_refl => I end.

Module Forge_sealed.
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
End Forge_sealed.
