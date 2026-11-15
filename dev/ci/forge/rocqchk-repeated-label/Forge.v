(* Forge, dispatch://BET-885: a .vo that gives one label to two constants
   of a structure gives a closed proof of False. This is, on the Corelib
   prelude, test-suite/misc/rocqchk-repeated-label/axiom/Lib.v, plus a
   module Forge_replabel. Given Forge_replabel, the reverted build's coqc
   (unfix.patch) gives twin the label ax: the library that
   test-suite/misc/rocqchk-repeated-label/forge.ml writes for
   test-suite/misc/rocqchk_repeated_label.sh. coqc never writes it: it gives
   a label to one constant of a structure at most. The environment keeps
   the last constant labelled ax, ax := tt. proof := ax was checked against
   the axiom, so no constant is left without a body, and proof has type
   False. *)

Axiom ax : False.

Definition proof : False := ax.

Definition twin : unit := tt.

Module Forge_replabel.
End Forge_replabel.
