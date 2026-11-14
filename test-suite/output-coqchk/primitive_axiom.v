(* -o lists every primitive among the axioms: the operator myadd, whose
   type rocqchk checks against its operator's but whose computation is the
   kernel's code, as well as the type int (a primitive type has no body). *)
Primitive int := #int63_type.
Primitive myadd := #int63_add.
