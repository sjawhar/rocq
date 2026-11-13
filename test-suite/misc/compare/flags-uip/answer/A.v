(* The honest answer declares seq as the task does and proves thm without
   reaching it. *)

Set Definitional UIP.

Inductive seq {A : Type} (a : A) : A -> SProp := srefl : seq a a.

Unset Definitional UIP.

Theorem thm : forall (P : nat -> Prop) (n : nat), P n -> P n.
Proof. intros P n x. exact x. Qed.
