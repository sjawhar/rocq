(* The library that the client of the forged sealed library is compiled
   against, with -noinit: M declares int with Primitive, as the int63 type,
   and int_empty as an axiom. The forged Client.vo records the forged
   sealed/Lib.vo as its dependency. *)

Unset Elimination Schemes.

Inductive False : Prop := .
Inductive Empty_set : Set := .

Module M.
  Primitive int := #int63_type.
  Axiom int_empty : forall _ : int, False.
End M.
