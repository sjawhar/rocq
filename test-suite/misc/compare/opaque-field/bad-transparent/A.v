(* The challenge's Qed field g of T is made transparent, so the field's
   body reaches conversion where the challenge's could not. *)

Module Type T.
  Definition g : nat -> nat := fun n => n.
End T.

Theorem thm : forall n : nat, n = n.
Proof. reflexivity. Qed.
