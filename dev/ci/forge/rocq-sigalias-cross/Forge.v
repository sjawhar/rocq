(* Forge, dispatch://BET-885: a .vo whose sealed module's signature records
   that its declared-only field is an alias of another sealed module's field
   of the same type, with the same label as every alias coqc writes, gives a
   closed proof of False. This is BET-885's sigalias case "cross": the variant
   library donor/Lib.v (TF's f reads M1.c = false, and M2's f is an axiom),
   the client donor/Client.v compiled against it, and a module Forge_cross
   with Control.v's TF and M2. Given Forge_cross, the reverted build's coqc
   (unfix.patch) writes Forge_cross.M2 as M2, records in M2's signature that
   M2.c is an alias of M1.c, and names M2.c (canonical M1.c) in the
   signature's f. Then M2 has no axiom, its signature's f reads
   M1.c = false, and contradiction has type False. *)

Definition discr (b : bool) : Prop := if b then True else False.

Module Type TT.
  Parameter c : bool.
  Parameter e : c = true.
End TT.

Module M1 : TT.
  Definition c : bool := true.
  Definition e : c = true := eq_refl.
End M1.

Module Type TF.
  Parameter c : bool.
  Parameter f : M1.c = false.
End TF.

Module M2 : TF.
  Definition c : bool := false.
  Parameter f : M1.c = false.
End M2.

Definition uses : M1.c = true := M1.e.

Definition both : true = false := eq_trans (eq_sym M1.e) M2.f.

Definition contradiction : False :=
  match both in _ = y return discr y with eq_refl => I end.

Module Forge_cross.
  Module Type TF.
    Parameter c : bool.
    Parameter f : c = false.
  End TF.

  Module M2 : TF.
    Definition c : bool := false.
    Definition f : c = false := eq_refl.
  End M2.
End Forge_cross.
