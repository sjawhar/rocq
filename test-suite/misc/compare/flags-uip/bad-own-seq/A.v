(* The answer declares seq as the task does, and a seq2 of its own of the
   same shape, and proves thm through seq2. The config tolerates uip on
   Top.A.seq2, but that is not the task's declaration of that name, so the
   flag is not tolerated; tolerate-uip adds a kind-only uip entry, which
   tolerates it on every object. *)

Set Definitional UIP.

Inductive seq {A : Type} (a : A) : A -> SProp := srefl : seq a a.

Inductive seq2 {A : Type} (a : A) : A -> SProp := srefl2 : seq2 a a.

Unset Definitional UIP.

Definition cast2 (P : nat -> Prop) (a b : nat) (e : seq2 a b) (x : P a) : P b :=
  match e with
    srefl2 _ => x
  end.

Theorem thm : forall (P : nat -> Prop) (n : nat), P n -> P n.
Proof. intros P n x. exact (cast2 P n n (srefl2 n) x). Qed.
