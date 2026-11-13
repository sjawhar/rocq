(* The honest library of the rocqchk-register-type forge (dispatch://BET-885):
   each primitive type registered as coqc registers it, by Primitive, and
   max_length, whose body is an int63 literal that rocqchk types with the
   registered int, and add, a primitive operator. This is most of
   test-suite/misc/rocqchk-register-type/honest/Lib.v and Client.v in one
   file, on the Corelib prelude, which registers no primitive type. rocqchk
   must accept it. *)

Primitive int := #int63_type.
Primitive float := #float64_type.
Primitive string := #string_type.
Primitive array := #array_type.

Primitive max_length := #array_max_length.
Primitive add := #int63_add.

Definition max : int := add max_length max_length.
