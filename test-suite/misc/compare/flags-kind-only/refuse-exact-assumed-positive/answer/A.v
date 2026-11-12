(* The shape of dispatch://BET-969: an exact pair on an object the answer
   writes itself. This answer declares Bad without the positivity check and
   proves thm through the proof of False that Bad gives, and the config
   tolerates assumed-positive on Top.A.Bad. No config may tolerate
   assumed-positive, on any object, so the run is refused before any
   library loads. *)

#[bypass_check(positivity)]
Inductive Bad : Type := mk : (Bad -> False) -> Bad.

Theorem thm : forall n : nat, n = n.
Proof.
  pose (f := fun b : Bad => match b with mk g => g b end).
  exact (False_ind _ (f (mk f))).
Qed.
