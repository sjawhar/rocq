(* The library that forge.ml forges for rocqchk_register_type.sh with the
   registration of a field of a sealed module, compiled with -noinit. M is
   sealed by T: its signature declares int as a parameter, and its
   implementation, its own body, defines it as Empty_set, and so proves
   int_empty. The forged Lib.vo adds to the library's retroknowledge the
   registration of M.int as the int63 type. Then an int63 literal has type
   M.int, and M.int_empty applied to it has type False: the client of
   sealed-donor. M.int_empty is proved, so it is no axiom. *)

Unset Elimination Schemes.

Inductive False : Prop := .
Inductive Empty_set : Set := .

Module Type T.
  Parameter int : Set.
  Parameter int_empty : forall _ : int, False.
End T.

Module M : T.
  Definition int : Set := Empty_set.
  Definition int_empty : forall _ : int, False := fun x => match x return False with end.
End M.
