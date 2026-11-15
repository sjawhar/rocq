Unset Elimination Schemes.

Inductive nat : Set := O : nat | succ : forall _ : nat, nat.

(* The same names as good/Alias.v, with a different rule: N's type here
   states f ?n => O, which donates that block to the forged alias. *)
Module S.
  Symbol f : forall _ : nat, nat.
  Rewrite Rule f_rew := f ?n => O.
End S.

Module N := S.
