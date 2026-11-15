Module Type T_template.

  Unset Elimination Schemes.

  #[universes(template)]
  Inductive option (A:Type) : Type := None | Some (_:A).

End T_template.

Module M_template.

  #[universes(template=no)]
  Inductive option (A:Type) : Type := None | Some (_:A).

End M_template.

Fail Module FAIL : T_template := M_template.

Module Type T_private.

  Unset Elimination Schemes.

  Inductive Box (A:Type) := box (_:A).

End T_private.

Module M_private.

  Private Inductive Box (A:Type) := box (_:A).

End M_private.

Fail Module FAIL : T_private := M_private.

(* A private implementation of a private signature is legal. coqc reads a
   closed module's inductive from the environment for algebraic sealing,
   "<:" and functor application, and the environment holds it with
   mind_private = Some true where the signature holds Some false. *)

Module Type T_private_both.

  Unset Elimination Schemes.

  Private Inductive Box := box (_:nat).

End T_private_both.

Module M_private_both.

  Private Inductive Box := box (_:nat).

End M_private_both.

Module DONTFAIL_private : T_private_both := M_private_both.

Module DONTFAIL_private2 <: T_private_both := M_private_both.

Module F_private (X : T_private_both).

  Definition b : X.Box := X.box 0.

End F_private.

Module DONTFAIL_private3 := F_private M_private_both.

(* A functor parameter as the argument, also held with Some true *)
Module DONTFAIL_private4 (Y : T_private_both) := F_private Y.

(* A non-private implementation of a private signature stays refused *)

Module M_not_private.

  Inductive Box := box (_:nat).

End M_not_private.

Fail Module FAIL : T_private_both := M_not_private.

(* and so does a private implementation of a non-private signature,
   through "<:" and functor application too *)

Fail Module FAIL <: T_private := M_private.

Module F_not_private (X : T_private).
End F_not_private.

Fail Module FAIL := F_not_private M_private.

Module Type T_primitive.

  Unset Elimination Schemes.

  Record Bla := bli {blo:nat}.

End T_primitive.

Module M_primitive.
  Set Primitive Projections.
  Record Bla := bli {blo:nat}.
End M_primitive.

Fail Module FAIL : T_primitive := M_primitive.

Module Type T_primitive2.

  Unset Elimination Schemes.
  Set Primitive Projections.
  Record Bla := bli {blo:nat}.

End T_primitive2.

Module M_primitive2.

  Record Bla := bli {blo:nat}.

End M_primitive2.

Fail Module FAIL : T_primitive2 := M_primitive2.

Module Type T_uniform.

  Unset Elimination Schemes.
  Parameter id : nat -> nat.
  Inductive Bla (n:nat) : Prop := blo (_ : Bla (id n)).

End T_uniform.

Module M_uniform.

  Unset Elimination Schemes.
  Definition id (n:nat) := n.
  Inductive Bla (n:nat) : Prop := blo (_ : Bla n).

End M_uniform.

(* This direction is legal *)
Module DONTFAIL : T_uniform := M_uniform.
