(* The honest library that misc/rocqchk_primitive_type.sh compiles and then
   forges with forge.ml into what coqc refuses to write:
     Primitive bogus : False := #int63_head0.
     Definition oops : False := bogus. *)
Unset Elimination Schemes.

Inductive False : Prop := .

(* forge.ml takes the term False from this body. *)
Definition false_prop : Prop := False.

Primitive int := #int63_type.

Primitive bogus : int -> int := #int63_head0.

Definition oops : int -> int := bogus.
