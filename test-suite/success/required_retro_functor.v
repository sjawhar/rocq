(* After the end of a functor that requires a library, the kernel keeps the
   registrations of that library: here PrimInt63's [Primitive int :=
   #int63_type], which an int literal needs. *)

Module Type S.
End S.

Module F (X : S).
  Require Corelib.Numbers.Cyclic.Int63.PrimInt63.
End F.

Import Corelib.Numbers.Cyclic.Int63.PrimInt63.
Open Scope uint63_scope.

Definition two : int := 2.
Definition one_plus_one : add 1 1 = two := eq_refl.
