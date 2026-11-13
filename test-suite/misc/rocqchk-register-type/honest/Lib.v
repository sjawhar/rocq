(* The honest library of rocqchk_register_type.sh, compiled with -noinit:
   each primitive type registered as coqc registers it, by Primitive, at the
   top of the library (int63 and array, which is universe polymorphic), in
   a module (float64) and in a module sealed by a signature (string);
   max_length, whose body is an int63 literal that rocqchk types with the
   registered int; and primitive operators with the operator's type: add,
   sub with that type written out, the universe polymorphic make, and mul
   in a module sealed by a signature that declares it as a parameter. *)

Primitive int := #int63_type.
Primitive array := #array_type.

Module Float.
  Primitive float := #float64_type.
End Float.

Module Type StringType.
  Parameter string : Set.
End StringType.

Module Str : StringType.
  Primitive string := #string_type.
End Str.

Primitive max_length := #array_max_length.

Primitive add := #int63_add.
Primitive sub : forall (_ : int) (_ : int), int := #int63_sub.
Primitive make := #array_make.

Module Type MulType.
  Parameter mul : forall (_ : int) (_ : int), int.
End MulType.

Module Mul : MulType.
  Primitive mul := #int63_mul.
End Mul.
