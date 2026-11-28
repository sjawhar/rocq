(* Forge, rocq-prover/rocq#21113: Include copied a private inductive open to
   matching. The axiom AB holds only while t is private, since no match can
   then tell A from B. N's match on its copy of t, after the Include, tells
   them apart, and gives a proof of False from AB. The reverted build's coqc
   (unfix.patch) accepts the match; coqc and rocqchk with the fix refuse it,
   since the copy is entered locked. *)

Module Q.
  Private Inductive t := A | B.
  Axiom AB : A = B.
End Q.

Module N.
  Include Q.
  Definition is_A (x : t) : bool := match x with A => true | B => false end.
  Definition proof : False :=
    match f_equal is_A AB in _ = y return if y then True else False with
    | eq_refl => I
    end.
End N.
