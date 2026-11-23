(* The library functor/Lib.vo of rocqchk_register_ind_canonical.sh,
   compiled with -noinit. It registers B as bool, and declares a functor F
   whose body declares an inductive type B of its own, which the definition
   f names, so that forge.ml takes the kernel name of F.B from the file.
   forge.ml ind-name gives the registration of B the user and canonical
   names of F.B: the forged library of the set forged-functor, whose
   registration names a type that only a functor's body declares. coqc
   never registers inside a functor. *)

Unset Elimination Schemes.

Inductive True : Prop := I.
Inductive False : Prop := .

Primitive int := #int63_type.
Primitive max_length := #array_max_length.

Inductive B : Set := true | false.

Register B as kernel.ind_bool.

Module Type T.
End T.

Module F (X : T).
  Inductive B : Set := true | false.
  Definition f (b : B) : B := b.
End F.
