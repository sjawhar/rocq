(* Case "inductive": the source of the corrupted client, compiled against
   donor/Lib.v. In the forged library R.e : forall _ : A.Y.I, False, and
   A.Y.I has the constructor A.Y.i. *)

Require Import NestedResolver.Lib.

(* A closed proof of False. *)
Definition contradiction : False := R.e A.Y.i.
