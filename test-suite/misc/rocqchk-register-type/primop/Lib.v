(* The library that forge.ml forges for rocqchk_register_type.sh with a
   primitive operator of another type than the operator's, compiled with
   -noinit. The forged Lib.vo gives the axiom add the body Primitive
   Int63add, the int63 addition, which coqc declares only with the type
   int -> int -> int. Then add is no axiom, and boom is a closed proof of
   False. *)

Unset Elimination Schemes.

Inductive False : Prop := .

Primitive int := #int63_type.

Primitive max_length := #array_max_length.

Axiom add : forall (_ : int) (_ : int), False.

Definition boom : False := add max_length max_length.
