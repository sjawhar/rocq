(* The answer proves thm through the task's seq: cast, a match on seq into
   Prop, which seq allows only because it is declared under definitional
   UIP, takes P a to P b. The config tolerates uip on Top.A.seq2 alone, so
   the flag on Top.A.seq is not tolerated; tolerate-uip names Top.A.seq,
   the task's declaration. *)

Set Definitional UIP.

Inductive seq {A : Type} (a : A) : A -> SProp := srefl : seq a a.

Unset Definitional UIP.

Definition cast (P : nat -> Prop) (a b : nat) (e : seq a b) (x : P a) : P b :=
  match e with
    srefl _ => x
  end.

Theorem thm : forall (P : nat -> Prop) (n : nat), P n -> P n.
Proof. intros P n x. exact (cast P n n (srefl n) x). Qed.
