(* Forge, dispatch://BET-885: a .vo in which the resolver of a functor's body
   makes F.k an alias of P.X.d, a name with another label, gives a closed
   proof of False through the functor application G : T := F A. This is, on
   the Corelib prelude and in one file,
   test-suite/misc/rocqchk-alias-label/donor/: the variant library Lib.v
   (F's lemma is an axiom that says A.X.k = false), the client Client.v
   compiled against it, and a module Forge_label. Given Forge_label, the
   reverted build's coqc (unfix.patch) writes F as Control.v has it,
   k := P.X.d and lemma : k = false := P.X.f, and records in F's resolver
   that F.k is an alias of P.X.d: the F that
   test-suite/misc/rocqchk-alias-label/forge.ml writes for
   test-suite/misc/rocqchk_alias_label.sh. A functor application rebuilds
   the canonical part of a name with the user name's label, so in F A,
   lemma's statement reads (G.k, A.X.k) = false and matches T's
   lemma : A.X.k = false. Then F has no axiom, G.lemma proves
   A.X.k = false, A.X.k is true, and contradiction has type False. *)

Definition discr (b : bool) : Prop := if b then True else False.

Module A.
  Module X.
    Definition d : bool := false.
    Definition k : bool := true.
    Definition f : d = false := eq_refl.
  End X.
End A.

Module Type XS.
  Parameter d : bool.
  Parameter f : d = false.
End XS.

Module Type S.
  Declare Module X : XS.
End S.

Module F (P : S).
  Definition k : bool := P.X.d.
  Axiom lemma : A.X.k = false.
End F.

Module Type T.
  Parameter lemma : A.X.k = false.
End T.

Module G : T := F A.

Definition boom : true = false := G.lemma.

Definition contradiction : False :=
  match boom in _ = y return discr y with eq_refl => I end.

Module Forge_label.
End Forge_label.
