(* The honest answer: the challenge, with the proof written. It adds no
   elimination constraint. *)

Require Import Img.Base.

Theorem thm : forall b : box, True.
Proof. intros _; exact I. Qed.
