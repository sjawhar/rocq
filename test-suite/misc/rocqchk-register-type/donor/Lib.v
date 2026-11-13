(* The library of the forgery donor of rocqchk_register_type.sh, compiled
   with -noinit, so that no other library registers the int63 type. The
   forged Lib.vo gives zero the body Int 0, the int63 literal 0, and adds to
   the library's retroknowledge the registration of the definition int as
   the int63 type. Then Int 0 has type int, int unfolds to Empty_set, and
   boom is a closed proof of False with no axiom. *)

Unset Elimination Schemes.

Inductive False : Prop := .
Inductive Empty_set : Set := .

Definition int : Set := Empty_set.

Axiom zero : int.

Definition boom : False := match zero return False with end.
