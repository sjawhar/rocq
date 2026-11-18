(* The challenge registers T as the primitive type of 63-bit integers and
   max_length as the primitive #array_max_length, a literal of T, and
   states that T is inhabited. The config permits T as an axiom. *)

Primitive T := #int63_type.

Primitive max_length := #array_max_length.

Theorem thm : exists x : T, True.
Proof.
Admitted.
