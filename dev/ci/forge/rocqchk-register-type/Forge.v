(* Forge, dispatch://BET-885: a .vo that registers a definition as the int63
   primitive type gives a closed proof of False. This is, on the Corelib
   prelude, which registers no primitive type,
   test-suite/misc/rocqchk-register-type/donor/Lib.v, plus a module
   Forge_regtype. Given Forge_regtype, the reverted build's coqc
   (unfix.patch) gives zero the body Int 0, the int63 literal 0, and adds to
   the library's retroknowledge the registration of int as the int63 type:
   the library that test-suite/misc/rocqchk-register-type/forge.ml writes
   for test-suite/misc/rocqchk_register_type.sh. coqc writes neither: it
   registers a primitive type only for the constant that Primitive declares.
   The typing of Int 0 uses the registered constant, so zero has type int,
   which unfolds to Empty_set. Then the file has no axiom, and boom has type
   False. *)

Definition int : Set := Empty_set.

Axiom zero : int.

Definition boom : False := match zero return False with end.

Module Forge_regtype.
End Forge_regtype.
