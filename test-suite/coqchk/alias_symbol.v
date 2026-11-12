(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)
(* An honest module alias that a functor application makes of a module
   that declares a rewrite-rule symbol: rocqchk must accept it.
   include_symbol.v covers Include. A direct [Module N := S.] is not
   tested here: the base's own rocqchk already refuses a module alias of a
   module with a rewrite rule, a separate issue from the alias check. *)

Module S.
  Symbol f : nat -> nat.
  Rewrite Rule f_rew := f ?n => ?n.
End S.

Module Type HasF.
  Parameter f : nat -> nat.
End HasF.

Module F (X : HasF).
  Module M := X.
End F.

Module R := F S.

Definition f_id_applied : R.M.f 0 = 0 := eq_refl.
Definition same_applied : S.f = R.M.f := eq_refl.
