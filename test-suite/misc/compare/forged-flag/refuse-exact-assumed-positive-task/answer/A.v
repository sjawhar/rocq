(* What this case once tolerated: the config names the pre-checked given
   Top.P.Q.T for assumed-positive, and this answer proves thm through the
   proof of False that T gives. A comparator that accepts the pair passes
   it, with assumed-positive recorded on Top.P.Q.T. No config may tolerate
   assumed-positive, on any object, so the run is refused before any
   library loads. *)

Require Top.P.
Require Top.P.Q.

Theorem thm : ~ (forall (A : Prop) (x y : A), x = y).
Proof.
  intros _.
  pose (f := fun t : Top.P.Q.T => match t with Top.P.Q.mk g => g t end).
  exact (f (Top.P.Q.mk f)).
Qed.
