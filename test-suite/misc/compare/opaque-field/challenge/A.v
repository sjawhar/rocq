(* The challenge declares a module type T whose field g is opaque, by Qed,
   and leaves thm admitted. An answer may prove g another way, but it must
   keep g opaque. *)

Module Type T.
  Definition g : nat -> nat.
  Proof. exact S. Qed.
End T.

Theorem thm : forall n : nat, n = n.
Proof.
Admitted.
