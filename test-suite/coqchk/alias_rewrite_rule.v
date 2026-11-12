(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)

(* rocqchk checks a module alias by subtyping its expansion against its
   declared type, which restates the target's rewrite-rule block; it refused
   every such block (NoRewriteRulesSubtyping) although coqc accepts the
   alias. *)

Module S. Symbol f : nat -> nat. Rewrite Rule f_rew := f ?n => ?n. End S.
Module N := S.
Module N2 := N.

Definition f_id : N.f 0 = 0 := eq_refl.
Definition same : S.f = N2.f := eq_refl.
