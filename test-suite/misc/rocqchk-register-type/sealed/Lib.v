(* The library of the forgery sealed of rocqchk_register_type.sh, compiled
   with -noinit. In M : T, int is a parameter in T and Empty_set in M,
   which proves int_empty. The forged Lib.vo registers M.int as the int63
   type: T's parameter has the type of the int63 type, M's definition is
   not a parameter. *)

Unset Elimination Schemes.

Inductive False : Prop := .
Inductive Empty_set : Set := .

Module Type T.
  Parameter int : Set.
  Parameter int_empty : forall (_ : int), False.
End T.

Module M : T.
  Definition int : Set := Empty_set.
  Definition int_empty : forall (_ : int), False :=
    fun x => match x return False with end.
End M.
