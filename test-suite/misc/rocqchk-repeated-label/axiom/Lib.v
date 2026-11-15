(* The donor of the forgery axiom of rocqchk_repeated_label.sh, compiled
   with -noinit. The forged Lib.vo gives twin the label ax. Then the
   environment keeps ax := tt, the last field labelled ax, a definition of
   another type. proof := ax was checked against the axiom, so no constant
   is left without a body, and proof is a closed proof of False with no
   axiom. A second ax : False := proof would unfold to itself through
   proof, and rocqchk -o, without the check, would not end on the file. *)

Unset Elimination Schemes.

Inductive False : Prop := .

Inductive unit : Set := tt.

Axiom ax : False.

Definition proof : False := ax.

Definition twin : unit := tt.
