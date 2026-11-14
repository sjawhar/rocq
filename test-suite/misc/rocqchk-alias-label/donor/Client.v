(* The forged client's source. With the forged Lib.vo, F A computes
   lemma : eq bool (G.k, canonical A.X.k) false, which matches T's
   lemma : eq bool A.X.k false by canonical name, although A.X.k is true. *)

Require Import LabelAlias.Lib.

Module Type T.
  Parameter lemma : eq bool A.X.k false.
End T.

Module G : T := F A.

Definition boom : eq bool true false := G.lemma.

(* A closed proof of False. *)
Definition contradiction : False :=
  match boom in eq _ _ y return discr y with
  | eq_refl _ _ => I
  end.
