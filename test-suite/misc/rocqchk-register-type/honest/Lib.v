(* The honest library of rocqchk_register_type.sh, compiled with -noinit.
   Each primitive type is registered as coqc registers it, by Primitive:
   int in the sealed module MI, whose implementation has an int63 literal,
   max_length, and an operator, add, and the others at the top. The
   declarations at the top, after MI, need the int that MI registered: the
   operator eqb, whose type also names the inductive type bool registered
   here, and the literal max_length. make is an operator with a universe.
   The forged copy twice registers MI.int a second time. *)

Module Type IT.
  Parameter int : Set.
  Parameter add : forall (_ : int) (_ : int), int.
  Parameter max : int.
End IT.

Module MI : IT.
  Primitive int := #int63_type.
  Primitive add := #int63_add.
  Primitive max_length := #array_max_length.
  Definition max : int := add max_length max_length.
End MI.

Inductive bool : Set := true | false.
Register bool as kernel.ind_bool.

Primitive eqb := #int63_eq.

Primitive float := #float64_type.
Primitive string := #string_type.
Primitive array := #array_type.
Primitive make := #array_make.

Primitive max_length := #array_max_length.
