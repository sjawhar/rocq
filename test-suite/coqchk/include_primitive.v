(* An honest Include of a module that declares primitives: rocqchk must
   accept the aliases it makes. *)

Module P.
  Primitive int := #int63_type.
  Primitive add := #int63_add.
End P.

Module Q.
  Include P.
End Q.

Definition double (x : Q.int) : Q.int := Q.add x x.
Definition same : P.add = Q.add := eq_refl.
