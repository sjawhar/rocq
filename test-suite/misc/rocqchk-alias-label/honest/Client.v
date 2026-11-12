(* The honest client: G.k is A.X.d, so G.lemma says A.X.d = false. *)

Require Import LabelAlias.Lib.

Module Type T.
  Parameter lemma : eq bool A.X.d false.
End T.

Module G : T := F A.

Definition uses : eq bool A.X.d false := G.lemma.
