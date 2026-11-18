(* The answer registers T as the primitive type of 63-bit integers, so T
   has literals, and proves thm with one of them, max_length, which it
   declares as the primitive #array_max_length (Corelib.Array.PArray would
   register int63 first, and the registration of T would then fail). A
   primitive type has no body, as a parameter has none, and the config
   permits T as an axiom: only the comparison of the primitive types sees
   the difference, and the answer fails, naming T. *)

Primitive T := #int63_type.

Primitive max_length := #array_max_length.

Parameter t0 : T.

Theorem thm : exists x : T, True.
Proof. exact (ex_intro _ max_length I). Qed.
