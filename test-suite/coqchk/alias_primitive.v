(* Honest module aliases of a module that declares primitives: rocqchk must
   accept the aliases they make. include_primitive.v covers Include; this
   covers [Module N := P.], an alias of that alias, and the alias that a
   functor application makes of its argument. *)

Module P.
  Primitive int := #int63_type.
  Primitive add := #int63_add.
End P.

Module N := P.
Module N2 := N.

Module Type HasAdd.
  Parameter add : P.int -> P.int -> P.int.
End HasAdd.

Module F (X : HasAdd).
  Module M := X.
End F.

Module R := F P.

Definition double (x : N2.int) : N2.int := N2.add x x.
Definition same : P.add = N2.add := eq_refl.
Definition same_applied : P.add = R.M.add := eq_refl.
