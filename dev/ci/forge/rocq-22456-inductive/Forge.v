(* Forge, dispatch://BET-885: a .vo whose delta resolver aliases two
   incompatible inductives gives a closed proof of False
   (rocq-prover/rocq#22456). This is Control.v and a module Forge_donor.
   Given Forge_donor, the reverted build's coqc (unfix.patch) writes
   B.inhabited as Forge_donor.inhabited, which has no constructor, and keeps
   the alias of B.inhabited to A.inhabited: the .vo that upstream's
   test-suite/misc/rocqchk-delta-alias/forge.ml makes, in mode inductive, from
   a compiled file. In that .vo, inductive_transport inhabits an empty
   inductive. *)

Unset Elimination Schemes.

Module A.
  Definition x : bool := true.
  Inductive inhabited : Prop := witness : inhabited.
End A.

Module B.
  Include A.
End B.

Definition discr (b : bool) : Prop := if b then True else False.

Definition alias : A.x = B.x := eq_refl.

Definition transported : discr B.x :=
  match alias in _ = y return discr y with eq_refl => I end.

Definition inductive_transport : B.inhabited := A.witness.

Module Forge_donor.
  Inductive inhabited : Prop := .
End Forge_donor.
