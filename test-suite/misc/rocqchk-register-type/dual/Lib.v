(* foreign/Lib.v with a parameter carrier : Set, compiled with -noinit next
   to foreign/Base.v and foreign/Client.v. The forged Lib.vo gives zero the
   body Int 0, and adds to the library's retroknowledge, as the int63 type,
   a name whose user name is carrier's, a parameter of type Set that this
   library declares, and whose canonical name is Base.int's, which
   conversion compares. Then Int 0 has type Base.int, and boom is a closed
   proof of False from the axiom carrier. *)

Require Import RegType.Base.

Axiom carrier : Set.

(* forge.ml reads carrier's kernel name from this body. *)
Definition carrier_alias : Set := carrier.

Axiom zero : int.

Definition boom : False := match zero return False with end.
