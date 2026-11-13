(* The library that forge.ml forges for rocqchk_register_type.sh, compiled
   with -noinit, so that no other library registers the int63 type. The
   forged Lib.vo gives zero the body Int 0, the int63 literal 0, and adds to
   the library's retroknowledge the registration of int as the int63 type,
   which coqc never writes: it registers only a constant that Primitive
   declares. Then Int 0 has type int, int unfolds to Empty_set, and boom is
   a closed proof of False with no axiom. The forgery registered of
   rocqchk_repeated_label.sh starts from this library too. *)

Unset Elimination Schemes.

Inductive False : Prop := .
Inductive Empty_set : Set := .

Definition int : Set := Empty_set.

Axiom zero : int.

Definition boom : False := match zero return False with end.
