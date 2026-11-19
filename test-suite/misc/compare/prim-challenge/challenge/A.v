(* The challenge registers T as the primitive type of 63-bit integers and
   states a theorem over it. The config permits T as an axiom. *)

Primitive T := #int63_type.

Theorem thm : forall _ : T, True.
Proof.
Admitted.
