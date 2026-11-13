(* The client of dual/Lib.v. The forged Client.vo gives z the body Int 0,
   whose type converts with N.int once the registration names N.int as the
   canonical name of int, and records the forged Lib.vo as its dependency.
   Then boom is a closed proof of False, and the only axiom is int. *)

Require Import RegType.Lib.

Axiom z : N.int.

Definition boom : False := match z return False with end.
