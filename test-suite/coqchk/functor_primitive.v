(* An applied functor whose body declares a primitive operator: rocqchk
   must accept the modules that its applications make. rocqchk checks
   each application against its own signature, where the primitive field
   is implemented by the field's own declaration of the same primitive,
   through the alias of the field to itself that strengthening makes.
   coqc does not run that check. The cases: an application at top level,
   one nested in a module, one through a functor that returns the
   application, an alias of one, definitions that use them and a
   universe-polymorphic primitive. primitive_field.v covers primitive fields
   of module types that a module implements. *)

Primitive int := #int63_type.
Primitive array := #array_type.

Module Type T. End T.
Module X. End X.

Module F (Y : T).
  Primitive add := #int63_add.
End F.

Module M := F X.

Module Outer.
  Module M := F X.
End Outer.

Module G (Y : T) := F Y.
Module MG := G X.

Module M3 := M.

Definition double (x : int) : int := M.add x x.
Definition same : M.add = M3.add := eq_refl.

(* A universe-polymorphic primitive: the field and its alias carry
   universe instances. *)
Module FArr (Y : T).
  Primitive make : forall A, int -> A -> array A := #array_make.
End FArr.

Module MArr := FArr X.
