(* The honest library of rocqchk_register_type.sh, compiled with -noinit:
   each primitive type registered as coqc registers it, by Primitive, at the
   top of the library (int63 and array, which is universe polymorphic), in
   a module (float64) and in a module sealed by a signature (string); and
   max_length, whose body is an int63 literal that rocqchk types with the
   registered int. *)

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
