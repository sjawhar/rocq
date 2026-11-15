Require Import SigAlias.Lib.

Definition uses_sealed : eq bool M.c true := M.e.
Definition uses_cross : eq bool M1.c true := M1.e.
Definition uses_functor : eq bool M.c true := N.uses.
