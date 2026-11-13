(* The honest library that misc/rocqchk_functor_loop_summary.sh compiles,
   and that forge.ml then makes a functor whose body applies that functor
   again, which coqc refuses to write:
     Module Grow := F Loc.   (a module of each application: grows)
     Module Same := F X.     (the arguments of the application around it)
   R applies F, so the -o summary reads F's body as R's, and under it each
   application of the forged body. *)
Inductive unit : Set := tt.

Module Type S. End S.
Module A. End A.
Module G (X : S). End G.

Module F (X : S).
  Axiom ax : unit.
  Module Loc. End Loc.
  Module Grow := G Loc.
  Module Same := G X.
End F.

Module R := F A.
