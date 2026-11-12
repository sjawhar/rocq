(* The honest library of the rocq-22456 forges (rocq-prover/rocq#22456): B
   includes A, so B.x and B.inhabited are true aliases of A.x and
   A.inhabited. This is upstream's
   test-suite/misc/rocqchk-delta-alias/good/Attack.v on the Corelib prelude.
   rocqchk must accept it. *)

Unset Elimination Schemes.

Module A.
  Definition x : bool := true.
  Inductive inhabited : Prop := witness : inhabited.
End A.

Module B.
  Include A.
End B.

Definition discr (b : bool) : Prop := if b then True else False.

Definition alias : A.x = B.x := eq_refl.

Definition transported : discr B.x :=
  match alias in _ = y return discr y with eq_refl => I end.

Definition inductive_transport : B.inhabited := A.witness.
