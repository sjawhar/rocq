(* The honest answer: the challenge, with the proof written. *)

Module Type SIG.
  Parameter P : Prop.
End SIG.

Module Type FT (X : SIG) (Y : SIG).
  Parameter q : X.P.
End FT.

Theorem thm : forall A : Prop, A -> A.
Proof. intros A a; exact a. Qed.
