(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)
(* An honest Include of a module that declares a rewrite-rule symbol:
   rocqchk must accept the aliases it makes. *)

Module S.
  Symbol f : nat -> nat.
  Rewrite Rule f_rew := f ?n => ?n.
End S.

Module T.
  Include S.
End T.

Definition f_id : T.f 0 = 0 := eq_refl.
Definition same : S.f = T.f := eq_refl.
