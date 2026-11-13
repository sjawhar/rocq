(* The honest library of rocqchk_register_type.sh, compiled with -noinit.
   Each primitive type is registered as coqc registers it, by Primitive:
   int in the sealed module MI, whose implementation has an int63 literal,
   max_length, and the others at the top. The max_length at the top, after
   MI, is a literal whose type is the int that MI registered. The forged
   copy twice registers MI.int a second time. *)

Module Type IT.
  Parameter int : Set.
  Parameter max : int.
End IT.

Module MI : IT.
  Primitive int := #int63_type.
  Primitive max_length := #array_max_length.
  Definition max : int := max_length.
End MI.

Primitive float := #float64_type.
Primitive string := #string_type.
Primitive array := #array_type.

Primitive max_length := #array_max_length.
