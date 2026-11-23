(* C'', the library of the set honest-repeated of
   rocqchk_register_ind_canonical.sh: C (../Lib.v) with a second
   registration of B as bool just after the first. coqc stores both
   entries, (B, B) then (B, B). *)

Unset Elimination Schemes.

Inductive True : Prop := I.
Inductive False : Prop := .

Primitive int := #int63_type.
Primitive max_length := #array_max_length.

Inductive B : Set := true | false.
Inductive U : Set := u1 | u2 (_ : False).

Register B as kernel.ind_bool.
Register B as kernel.ind_bool.

Definition names (_ : B) : U := u1.
