(* The library of rocqchk_register_ind_label.sh, compiled with -noinit. It
   registers B as the primitive bool, and declares in a module N a second
   inductive type with the label B, N.B := u1 | u2 (_ : False), whose second
   constructor takes a proof of False. The test forges the registration of
   B with the canonical name of N.B: the same label, another type. The
   definition names names B and N.B, so that forge.ml takes their kernel
   names from the file. *)

Unset Elimination Schemes.

Inductive True : Prop := I.
Inductive False : Prop := .

Primitive int := #int63_type.
Primitive max_length := #array_max_length.

Inductive B : Set := true | false.

Module N.
  Inductive B : Set := u1 | u2 (_ : False).
End N.

Register B as kernel.ind_bool.

Definition names (_ : B) : N.B := N.u1.
