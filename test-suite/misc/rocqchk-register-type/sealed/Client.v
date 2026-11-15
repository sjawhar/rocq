(* The client of sealed/Lib.v. The forged Client.vo gives z the body Int 0,
   of type M.int once M.int is registered as the int63 type, and records
   the forged Lib.vo as its dependency. Then boom is a closed proof of
   False: M.int_empty is proved in M, and z is defined. *)

Require Import RegType.Lib.

Axiom z : M.int.

Definition boom : False := M.int_empty z.
