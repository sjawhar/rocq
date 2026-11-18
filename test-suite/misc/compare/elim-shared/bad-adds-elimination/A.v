(* The answer's own library adds the elimination constraint s -> Prop on
   the sort s of the image's library Img.Base. The image's file is the same
   on both sides, and the constraint is the answer's: the comparison names
   the sort by its library, Img.Base.s. *)

Require Import Img.Base.

Constraint s -> Prop.

Theorem thm : forall b : box, True.
Proof. intros _; exact I. Qed.
