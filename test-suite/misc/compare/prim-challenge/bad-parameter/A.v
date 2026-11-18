(* The answer declares T as a parameter, no primitive type, where the
   challenge registers it as the primitive type of 63-bit integers. A
   primitive type has no body, as a parameter has none, and the config
   permits T as an axiom: only the comparison of the primitive types sees
   the difference, and the answer fails, naming T. *)

Parameter T : Set.

Theorem thm : forall _ : T, True.
Proof. exact (fun _ => I). Qed.
