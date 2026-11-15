(* A tolerated flag names its object by the name it prints. A module Q of
   the library Top.P holding an inductive U prints Top.P.Q.U, the name of
   the given; only the object tells the forgery from the given.

   The given U of Top.P.Q has two constructors and a large elimination the
   elimination check would refuse, so a match on U tells u1 from u2, and
   thm, which says that proof irrelevance does not hold, has an honest
   proof through it. The statement names no object of Top.P.Q, so an answer
   that forges U states thm as the challenge does, and only the flag fails
   it.

   bad-own-object proves thm through an inductive of its own, which the
   config's pair does not name. fail-config names the task's T for
   unchecked-eliminations instead of U, and the honest answer fails under
   it. refuse-exact-assumed-positive-task names T for assumed-positive, a
   kind no config may tolerate. *)

Require Top.P.
Require Top.P.Q.

Theorem thm : ~ (forall (A : Prop) (x y : A), x = y).
Proof.
Admitted.
