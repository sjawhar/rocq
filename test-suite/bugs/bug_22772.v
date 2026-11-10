(* rocq#22772: the lazy machine dropped the shift when the argument of a
   primitive operator was found under a Zshift, so a primitive array built
   under a binder was read in the wrong context: [get [|x|x|] 0] reduced to
   the next variable in scope instead of [x].  Conversion uses the lazy
   machine, so the kernel accepted a false equation. *)

From Corelib Require Import PrimInt63 PrimArray.

Open Scope array_scope.

Ltac check_const_eq name constr :=
  let v := (eval cbv delta [name] in name) in
  tryif constr_eq v constr
  then idtac
  else fail 0 v "<>" constr.

Notation check_const_eq name constr := (ltac:(check_const_eq name constr; exact constr)) (only parsing).

(** The proof of False of the issue: the kernel must refuse it. *)

Definition T (a : array bool) : Prop := forall y : bool, get a 0 = y.

Lemma bad : forall x : bool, T [| x | x |].
Proof.
  exact_no_check (fun (x y : bool) => @eq_refl bool y).
Fail Qed.
Abort.

(** Honest control: the same shape, but true. *)

Definition T' (a : array bool) : Prop := forall y : bool, get a 0 = get a 0.

Lemma honest : forall x : bool, T' [| x | x |].
Proof. exact_no_check (fun (x y : bool) => @eq_refl bool (get [| x | x |] 0)). Qed.

(** [lazy] and [cbv] agree on the term of the issue and on variants. *)

Definition lazy1 := Eval lazy in
  fun x : bool => (fun (a : array bool) (y : bool) => get a 0) [| x | x |].
Definition cbv1 := Eval cbv in
  fun x : bool => (fun (a : array bool) (y : bool) => get a 0) [| x | x |].
Check check_const_eq lazy1 (fun x _ : bool => x).
Check check_const_eq cbv1 (fun x _ : bool => x).

(* nested binders *)
Definition lazy2 := Eval lazy in
  fun x : bool => (fun (a : array bool) (y z w : bool) => get a 0) [| x | x |].
Definition cbv2 := Eval cbv in
  fun x : bool => (fun (a : array bool) (y z w : bool) => get a 0) [| x | x |].
Check check_const_eq lazy2 (fun x _ _ _ : bool => x).
Check check_const_eq cbv2 (fun x _ _ _ : bool => x).

(* two arrays *)
Definition lazy3 := Eval lazy in
  fun x x' : bool =>
    (fun (a b : array bool) (y : bool) => (get a 0, get b 1))
      [| x | x |] [| x ; x' | x |].
Definition cbv3 := Eval cbv in
  fun x x' : bool =>
    (fun (a b : array bool) (y : bool) => (get a 0, get b 1))
      [| x | x |] [| x ; x' | x |].
Check check_const_eq lazy3 (fun x x' _ : bool => (x, x')).
Check check_const_eq cbv3 (fun x x' _ : bool => (x, x')).

(* set, copy, default, out of bounds *)
Definition lazy4 := Eval lazy in
  fun x x' : bool => (fun (a : array bool) (y : bool) => get (set a 0 x') 0) [| x | x |].
Definition cbv4 := Eval cbv in
  fun x x' : bool => (fun (a : array bool) (y : bool) => get (set a 0 x') 0) [| x | x |].
Check check_const_eq lazy4 (fun _ x' _ : bool => x').
Check check_const_eq cbv4 (fun _ x' _ : bool => x').

Definition lazy5 := Eval lazy in
  fun x : bool => (fun (a : array bool) (y : bool) => get (copy a) 0) [| x | x |].
Definition cbv5 := Eval cbv in
  fun x : bool => (fun (a : array bool) (y : bool) => get (copy a) 0) [| x | x |].
Check check_const_eq lazy5 (fun x _ : bool => x).
Check check_const_eq cbv5 (fun x _ : bool => x).

Definition lazy6 := Eval lazy in
  fun x : bool => (fun (a : array bool) (y : bool) => default a) [| x | x |].
Definition cbv6 := Eval cbv in
  fun x : bool => (fun (a : array bool) (y : bool) => default a) [| x | x |].
Check check_const_eq lazy6 (fun x _ : bool => x).
Check check_const_eq cbv6 (fun x _ : bool => x).

Definition lazy7 := Eval lazy in
  fun x : bool => (fun (a : array bool) (y : bool) => get a 17) [| x | x |].
Definition cbv7 := Eval cbv in
  fun x : bool => (fun (a : array bool) (y : bool) => get a 17) [| x | x |].
Check check_const_eq lazy7 (fun x _ : bool => x).
Check check_const_eq cbv7 (fun x _ : bool => x).

(* array read scrutinised by a match *)
Definition lazy8 := Eval lazy in
  fun x : bool =>
    (fun (a : array bool) (y : bool) =>
       match get a 0 with true => x | false => y end) [| x | x |].
Definition cbv8 := Eval cbv in
  fun x : bool =>
    (fun (a : array bool) (y : bool) =>
       match get a 0 with true => x | false => y end) [| x | x |].
Check check_const_eq lazy8 (fun x y : bool => if x then x else y).
Check check_const_eq cbv8 (fun x y : bool => if x then x else y).

(* under a fix *)
Fixpoint f (n : nat) (a : array bool) (y : bool) {struct n} : bool :=
  match n with O => get a 0 | S k => f k a y end.

Definition lazy9 := Eval lazy in
  fun x : bool => (fun (a : array bool) (y : bool) => f 3 a y) [| x | x |].
Definition cbv9 := Eval cbv in
  fun x : bool => (fun (a : array bool) (y : bool) => f 3 a y) [| x | x |].
Check check_const_eq lazy9 (fun x _ : bool => x).
Check check_const_eq cbv9 (fun x _ : bool => x).

(* let-bound array, two binders deep *)
Definition lazy10 := Eval lazy in
  fun x : bool => let a := [| x | x |] in fun y z : bool => get a 0.
Definition cbv10 := Eval cbv in
  fun x : bool => let a := [| x | x |] in fun y z : bool => get a 0.
Check check_const_eq lazy10 (fun x _ _ : bool => x).
Check check_const_eq cbv10 (fun x _ _ : bool => x).

(* array of arrays *)
Definition lazy11 := Eval lazy in
  fun x : bool =>
    (fun (a : array (array bool)) (y : bool) => get (get a 0) 0)
      [| [| x | x |] | [| x | x |] |].
Definition cbv11 := Eval cbv in
  fun x : bool =>
    (fun (a : array (array bool)) (y : bool) => get (get a 0) 0)
      [| [| x | x |] | [| x | x |] |].
Check check_const_eq lazy11 (fun x _ : bool => x).
Check check_const_eq cbv11 (fun x _ : bool => x).

(** Kernel conversion (which uses the lazy machine) agrees. *)

Definition conv1 : (fun (x y : bool) => (fun (a : array bool) (z : bool) => get a 0) [| x | x |] y)
                   = (fun x _ : bool => x)
  := eq_refl.
Definition conv2 : (fun (x y : bool) => let a := [| x | x |] in get a 0) = (fun x _ : bool => x)
  := eq_refl.
