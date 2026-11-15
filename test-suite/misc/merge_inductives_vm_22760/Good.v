Require Spec.
Require Agent.

(* The honest counterpart of Bad.v, over the same merged type: the same VM
   cast, of a true equation, and the proof of True that Bad.v's match builds
   from it. *)
Import Spec.

Definition f1 (x : Big) : nat -> nat :=
  match x with C250 n => fun m => n | _ => fun m => 0 end.

Definition f1' (x : Big) : nat -> nat :=
  match x with C250 n => fun m => n | _ => fun m => 0 end.

Definition yes_true : f1 = f1' := (eq_refl f1 <: f1 = f1').

Definition good : True :=
  match f_equal (fun f => f (C250 1) 2) yes_true in _ = z
        return match z with 1 => True | _ => False end with
  | eq_refl => I
  end.
