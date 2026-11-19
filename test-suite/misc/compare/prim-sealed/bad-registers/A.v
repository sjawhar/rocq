(* The answer's module M, sealed by S, registers its T as the primitive
   type of 63-bit integers, where the challenge's M declares it as a
   parameter. The seal hides nothing from the comparison: the constant M.T
   is compared inside the module, the primitive type it is registered as
   first, and the answer fails, naming M.T. *)

Module Type S.
  Parameter T : Set.
End S.

Module M : S.
  Primitive T := #int63_type.
End M.

Theorem thm : forall _ : M.T, True.
Proof. exact (fun _ => I). Qed.
