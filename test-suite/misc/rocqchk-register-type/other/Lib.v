(* The library of the forgery other of rocqchk_register_type.sh, compiled
   with -noinit. The forged Lib.vo registers Base.int, a constant of the
   earlier library Base, as the int63 type. *)

Require Import RegType.Base.

(* A declaration that names Base.int, for forge.ml. *)
Definition uses : Set := int.
