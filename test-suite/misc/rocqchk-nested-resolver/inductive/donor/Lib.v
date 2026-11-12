(* Case "inductive": the library that the corrupted client is compiled
   against. Same logical name and the same declarations as honest/Lib.v,
   except that T's e says forall _ : A.Y.I, False, as in the forged library,
   and R implements T with an axiom e, so that coqc accepts the client's
   proof of False. The corrupted client then records the forged Lib.vo's
   checksum instead of this file's. *)

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
  Parameter e : forall _ : A.Y.I, False.
End T.

Module R : T.
  Definition c' : Prop := A.Y.I.
  Axiom e : forall _ : A.Y.I, False.
End R.
