(* The library that forge.ml forges for rocqchk_register_type.sh with a
   registration of a constant it does not declare, compiled with -noinit.
   The forged Lib.vo gives zero the body Int 0, and adds to the library's
   retroknowledge the registration of Base.int as the int63 type. Then
   Int 0 has type Base.int, which unfolds to Empty_set, and boom is a
   closed proof of False with no axiom. *)

Require Import RegType.Base.

Axiom zero : int.

Definition boom : False := match zero return False with end.
