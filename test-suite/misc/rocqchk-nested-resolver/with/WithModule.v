(* An honest file where the delta resolver of a structure and the resolver of
   one of its submodules give one name different canonical names. XT
   includes the module Q, so XT.c is an alias of Q.c, and S declares X : XT.
   In S with Module X := B, B.c is a definition of its own, convertible with
   Q.c: the resolver of the result keeps S's entry X.c -> Q.c, while X's own
   resolver maps X to B, so that X.c is B.c. rocqchk must accept the file,
   because X.c, B.c and Q.c are convertible. *)

Unset Elimination Schemes.

Inductive bool : Set := true | false.

Module Q.
  Definition c : bool := true.
End Q.

Module Type XT.
  Include Q.
End XT.

Module Type S.
  Declare Module X : XT.
End S.

Module B.
  Definition c : bool := Q.c.
End B.

(* As a module type, *)
Module Type S2 := S with Module X := B.

(* as the type of a sealed module, *)
Module M : S with Module X := B.
  Module X := B.
End M.

(* and as the type of a functor's parameter. coqc refuses a body that names
   P.X.c ("Ill-formed constant P.X.c: expected canonical name B.c but found
   Q.c"), so this one names nothing of P. *)
Module F (P : S with Module X := B).
End F.
