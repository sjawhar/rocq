(* Case "functor": the honest client. *)

Require Import InlineHint.Lib.

Module Type T.
  Parameter lem : forall _ : (forall b : bool, eq bool b A.d), eq bool true false.
End T.

Module G : T := F A.

Definition uses : forall _ : (forall b : bool, eq bool b A.d), eq bool true false := G.lem.
