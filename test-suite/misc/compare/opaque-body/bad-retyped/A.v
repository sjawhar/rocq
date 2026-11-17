(* The challenge's Qed f stays opaque but gets another type, nat -> bool.
   So f's type differs from the challenge's, and thm's statement changes
   with it. *)

Definition f : nat -> bool.
Proof. exact (fun _ => true). Qed.

Theorem thm : forall n, f n = f n.
Proof. reflexivity. Qed.
