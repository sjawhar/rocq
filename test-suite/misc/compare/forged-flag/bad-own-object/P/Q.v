(* A file of the task the answer leaves unchanged, so the config declares it
   pre-checked. Its given inductive Top.P.Q.U is declared with the
   elimination check off, so a match on U may return a Prop, and the config
   tolerates unchecked-eliminations on that object alone. Its given
   inductive Top.P.Q.T skips the positivity check; the case's config
   tolerates nothing on it, and refuse-exact-assumed-positive-task is the
   config that tries to. *)

Declare ML Module "coq-test-suite.elim_flag".

#[bypass_check(positivity)]
Inductive T : Type := mk : (T -> False) -> T.

Unset Test Elimination Checking.

Inductive U : Prop :=
| u1 : U
| u2 : U.

Set Test Elimination Checking.
