(* Forge, rocq-prover/rocq#21113, the functor form: a private inductive
   given to a functor whose parameter declares it non-private. The axiom AB
   holds only while Q.foo is private; F's match, written against T, tells
   Foo from Bar once B := F Q, and gives a proof of False from AB. The
   reverted build's coqc (unfix.patch) accepts the application; coqc and
   rocqchk with check_private refuse it. *)

Module Type T.
  Unset Elimination Schemes.
  Inductive foo := Foo | Bar.
End T.

Module Q.
  Private Inductive foo := Foo | Bar.
  Axiom AB : Foo = Bar.
End Q.

Module F (X : T).
  Include X.
  Definition to_bool (b : foo) := match b with Foo => true | Bar => false end.
End F.

Module B := F Q.

Definition proof : False :=
  match f_equal B.to_bool Q.AB in _ = y return if y then True else False with
  | eq_refl => I
  end.
