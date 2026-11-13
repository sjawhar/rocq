(* The forged operator client's source. The forged Client.vo is this file's
   Client.vo recording the forged Lib.vo as its dependency. *)

Require Import RegType.Lib.

Definition contradiction : False := boom.
