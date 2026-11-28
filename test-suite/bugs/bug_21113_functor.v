(* rocq-prover/rocq#21113, the functor form: a private inductive does not
   implement a non-private one, or a functor body could match on it through
   the specification. Subtyping refuses it (check_private, rocq-prover/rocq
   commit c7076161aa, which compares only whether each side is private). *)

Module Type T.
Unset Elimination Schemes.
Inductive foo := Foo | Bar.
End T.

Module Q.
Private Inductive foo := Foo | Bar.
End Q.

Module F (X : T).
Include X.
Definition to_bool (b : foo) := match b with Foo => true | Bar => false end.
End F.

Fail Module B := F Q.

(* A private implementation of a private specification is accepted, as a
   functor argument and under an opaque seal. *)
Module Type TP.
Private Inductive foo := Foo | Bar.
End TP.

Module FP (X : TP).
Include X.
End FP.

Module BP := FP Q.

Module QS : TP.
Private Inductive foo := Foo | Bar.
End QS.

(* A non-private implementation of a private specification is refused too
   (rocq-prover/rocq#15842). *)
Module QN.
Inductive foo := Foo | Bar.
End QN.

Fail Module BN := FP QN.
