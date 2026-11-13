(* A tolerated flag with no object: the kind wherever it appears.

   An honest proof of an equality reaches Corelib.Init.Logic.eq, an
   inductive of the image built without -indices-matter, so its closure
   carries indices-not-mattering on an object the task never wrote. The
   route the comparator replaces always allowed that kind, on any object
   (grading-tools _axiom_kinds._ALWAYS_ALLOWED_KINDS); naming every object
   of the image that carries it would be a list of the standard library.

   fail-config is the other half: a kind-only entry for ANOTHER kind
   tolerates nothing of this one, and the same honest answer fails under
   it.

   The refuse- configs are entries no config may write. assumed-positive,
   unsafe-fixpoint and type-in-type are refused with an object or without:
   each refuse-exact-<kind> names its kind on an object, and each
   refuse-kind-only-<kind> names it without one. refuse-exact-assumed-positive
   is the shape of dispatch://BET-969, on an answer of its own that declares
   the object it names. unchecked-eliminations is refused without an object
   alone (refuse-kind-only-unchecked-eliminations). *)

Theorem thm : forall n : nat, n = n.
Proof.
Admitted.
