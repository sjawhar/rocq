(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)

(* Module subtyping accepts a rewrite-rule block of a signature only when
   the implementation has the same block. *)

Module A.
  Symbol f : nat -> nat.
  Rewrite Rule r := f ?n => ?n.
End A.

(* A symbol of a signature cannot be implemented, even by a symbol: this
   is refused on f, before the rules are compared. *)
Module Type T.
  Symbol f : nat -> nat.
  Rewrite Rule r := f ?n => 0.
End T.
Fail Module M : T := A.

(* The signature shows A's own symbol, so its block is compared with A's,
   and it states a different rule. *)
Module Type TA.
  Definition f := A.f.
  Rewrite Rule r := A.f ?n => 0.
End TA.
Fail Module M : TA := A.

(* The same block as A's. *)
Module Type TA'.
  Definition f := A.f.
  Rewrite Rule r := A.f ?n => ?n.
End TA'.
Module M : TA' := A.
Check eq_refl : M.f 3 = 3.

(* An implementation without the block. *)
Module B.
  Definition f := A.f.
End B.
Fail Module M' : TA' := B.
