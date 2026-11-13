(* The library that forge.ml forges for rocqchk_register_type.sh with the
   registration of a field that no own body declares, compiled with
   -noinit. N is sealed by T, as M is in sealed/Lib.v: its implementation
   defines int as Empty_set and proves int_empty. R is F applied to N, and
   F seals its argument by T again: R's type declares R.M.int as a
   parameter, and R, an algebraic module, has no own body. The forged
   Lib.vo adds to the library's retroknowledge the registration of R.M.int
   as the int63 type. Then an int63 literal has type R.M.int, and
   R.M.int_empty applied to it has type False: the client of
   functor-donor. *)

Unset Elimination Schemes.

Inductive False : Prop := .
Inductive Empty_set : Set := .

Module Type T.
  Parameter int : Set.
  Parameter int_empty : forall _ : int, False.
End T.

Module N : T.
  Definition int : Set := Empty_set.
  Definition int_empty : forall _ : int, False := fun x => match x return False with end.
End N.

Module F (P : T).
  Module M : T := P.
End F.

Module R := F N.
