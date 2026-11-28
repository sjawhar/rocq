(* rocq-prover/rocq#21113: Include copied a private inductive open to
   matching, so a match on the copy reached the original. *)

Module Foo.
Private Inductive foo := Foo | Bar.
End Foo.

Import Foo.

Module Bar.
Include Foo.

(* The copy is locked: no match on it. *)
Fail Definition to_bool b := match b with Foo => true | Bar => false end.

(* The original stays locked too. *)
Fail Definition to_bool' (b : Foo.foo) :=
  match b with Foo.Foo => true | Foo.Bar => false end.

End Bar.

(* A private inductive is still matched on in its own module, and a module
   that includes it still uses the functions defined there. *)
Module M.
Private Inductive I := a | b.
Definition f (x : I) : bool := match x with a => true | b => false end.
End M.

Module N.
Include M.
Definition g := f a.
Fail Definition h (x : I) : bool := match x with a => false | b => true end.
End N.

Check (eq_refl : N.g = true).

(* A functor that includes its parameter keeps the parameter's functions
   that match on a private inductive of its module type. *)
Module Type T.
Private Inductive J := c | d.
Definition k (x : J) : bool := match x with c => true | d => false end.
End T.

Module F (X : T).
Include X.
Definition l := k c.
Fail Definition m (x : J) : bool := match x with c => false | d => true end.
End F.

(* A module nested in the one that declares a private inductive matches on
   it, and an Include or an alias of the declaring module keeps that. *)
Module M2.
Private Inductive I2 := c2 | d2.
Module Sub.
Definition f2 (x : I2) : bool := match x with c2 => true | d2 => false end.
End Sub.
End M2.

Module N2.
Include M2.
End N2.

Module A2 := M2.

Check (eq_refl : N2.Sub.f2 N2.c2 = true).
