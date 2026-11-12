Unset Elimination Schemes.

Inductive nat : Set := O : nat | succ : forall _ : nat, nat.

Module S.
  Symbol f : forall _ : nat, nat.
  Rewrite Rule f_rew := f ?n => ?n.
End S.

(* An honest alias: its type restates S's rule block. *)
Module N := S.
