(* The honest library of the rocqchk-register-type forge (dispatch://BET-885):
   each primitive type registered as coqc registers it, by Primitive: int
   in the sealed module MI, whose implementation has an operator and an
   int63 literal, and the others at the top, with operators whose types
   need MI's int and Corelib's bool, which this file registers. This is
   test-suite/misc/rocqchk-register-type/honest/Lib.v on the Corelib
   prelude, which registers no primitive type, with Corelib's bool in place
   of the library's own. rocqchk must accept it. *)

Module Type IT.
  Parameter int : Set.
  Parameter add : int -> int -> int.
  Parameter max : int.
End IT.

Module MI : IT.
  Primitive int := #int63_type.
  Primitive add := #int63_add.
  Primitive max_length := #array_max_length.
  Definition max : int := add max_length max_length.
End MI.

Register bool as kernel.ind_bool.

Primitive eqb := #int63_eq.

Primitive float := #float64_type.
Primitive string := #string_type.
Primitive array := #array_type.
Primitive make := #array_make.

Primitive max_length := #array_max_length.
