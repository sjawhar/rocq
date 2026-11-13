(* The forged clients' source. Each forged Client.vo is this file's
   Client.vo recording a forged Lib.vo as its dependency. *)

Require Import RegType.Base RegType.Lib.

Definition contradiction : False := boom.
