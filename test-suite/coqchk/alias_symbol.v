(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)
(* Honest module aliases of a module that declares a rewrite-rule symbol:
   rocqchk must accept the aliases they make. include_symbol.v covers
   Include; this covers [Module N := S.], an alias of that alias, and the
   alias that a functor application makes of its argument. *)

Module S.
  Symbol f : nat -> nat.
  Rewrite Rule f_rew := f ?n => ?n.
End S.

Module N := S.
Module N2 := N.

Module Type HasF.
  Parameter f : nat -> nat.
End HasF.

Module F (X : HasF).
  Module M := X.
End F.

Module R := F S.

Definition f_id : N2.f 0 = 0 := eq_refl.
Definition same : S.f = N2.f := eq_refl.
Definition f_id_applied : R.M.f 0 = 0 := eq_refl.
Definition same_applied : S.f = R.M.f := eq_refl.
