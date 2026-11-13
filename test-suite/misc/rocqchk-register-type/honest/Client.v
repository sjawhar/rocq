(* The honest client: it uses the registered types of Lib.v. *)

Require Import RegType.Lib.

Definition max : int := max_length.

Definition float : Set := Float.float.

Definition string : Set := Str.string.
