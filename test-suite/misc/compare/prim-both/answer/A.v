(* The honest answer registers T as the same primitive type as the
   challenge does, and proves thm with the literal max_length. Both sides
   the same primitive type: the answer passes. *)

Primitive T := #int63_type.

Primitive max_length := #array_max_length.

Theorem thm : exists x : T, True.
Proof. exact (ex_intro _ max_length I). Qed.
