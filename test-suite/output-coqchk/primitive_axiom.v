(* rocqchk does not check a primitive's declared type against the type of
   its operator, so -o lists every primitive among the axioms: the operator
   myadd as well as the type int (a primitive type has no body). *)
Primitive int := #int63_type.
Primitive myadd := #int63_add.
