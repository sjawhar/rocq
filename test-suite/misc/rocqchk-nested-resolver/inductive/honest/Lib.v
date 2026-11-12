(* Case "inductive": the honest library, sameLabel's with an inductive I in
   A.Y and in A.X: A.Y.I has a constructor and A.X.I has none. The forged
   Lib.vo (forge.ml inductive) is this file's Lib.vo with the alias
   A.X.I -> A.Y.I added to A's delta resolver only, and, in T and in R's
   stored signature, e's type forall _ : A.X.I, False changed to
   forall _ : A.Y.I, False. c' names A.Y.I for forge.ml. Under -noinit there
   is no notation A -> B. *)

Unset Elimination Schemes.

Inductive False : Prop := .

Module A.
  Module Y.
    Inductive I : Prop := i : I.
  End Y.
  Module X.
    Inductive I : Prop := .
  End X.
End A.

Module Type XT.
  Inductive I : Prop := .
End XT.

Module Type S.
  Declare Module X : XT.
End S.

Module F (P : S).
  Definition c' : Prop := A.Y.I.
  Definition e : forall _ : P.X.I, False := fun x => match x return False with end.
End F.

Module Type T.
  Definition c' : Prop := A.Y.I.
  Parameter e : forall _ : A.X.I, False.
End T.

Module R : T := F A.
