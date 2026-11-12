(* The honest library that misc/rocqchk_primitive_type.sh compiles and then
   forges with forge.ml into what coqc refuses to write:
     Primitive bogus : False := #int63_head0.
     Definition oops : False := bogus. *)
Unset Elimination Schemes.

Inductive False : Prop := .

(* forge.ml takes the term False from this body. *)
Definition false_prop : Prop := False.

Primitive int := #int63_type.

(* No type is written: under -noinit the notation A -> B does not exist.
   Both constants get the type of #int63_head0, int -> int, which forge.ml
   checks is a product before it replaces it with False. *)
Primitive bogus := #int63_head0.

Definition oops := bogus.
