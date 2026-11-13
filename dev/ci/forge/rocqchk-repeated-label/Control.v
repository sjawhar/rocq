(* The honest library of the rocqchk-repeated-label forge (dispatch://BET-885):
   Forge.v without its marker, so that ax, proof and twin keep their labels,
   and the labels that test-suite/misc/rocqchk-repeated-label/honest/Lib.v
   shares as coqc lets it, on the Corelib prelude. A constant and a module
   of one structure share a label, since they are in two namespaces, and so
   do fields of two structures. An Include adds the fields of another
   structure, a with constraint replaces a field of a module type, and a
   functor application copies the fields of the functor's body. rocqchk
   must accept it. *)

Axiom ax : False.

Definition proof : False := ax.

Definition twin : unit := tt.

Definition M : unit := tt.

Module M.
  Definition M : unit := tt.
  Module M.
    Definition M : unit := tt.
  End M.
End M.

Module Type T.
  Parameter t : Set.
  Parameter x : t.
End T.

Definition T : unit := tt.

Module Type U := T with Definition t := unit.

Module A : U.
  Definition t := unit.
  Definition x := tt.
End A.

Module F (X : T).
  Include X.
  Definition y : t := x.
End F.

Module B := F A.

Module C.
  Include F A.
  Definition z : t := y.
End C.

Inductive Even : Prop := even_odd : Odd -> Even
with Odd : Prop := odd_even : Even -> Odd | odd_tt : Odd.
