(* A primitive field of a module type is implemented by the field's own
   declaration of the same primitive, given directly (sealing with a
   functor type, which does not strengthen) or through the alias of the
   field to itself that strengthening makes. coqc and rocqchk must accept
   these, and a functor argument whose type has a primitive field. A
   parameter or a different primitive must be refused: if another
   operator could implement a primitive field, a functor over the module
   type would compute with one operator and the module with the other,
   which proves False (rocq-prover/rocq#18503, bugs/bug_18503.v). An alias
   to another module's field is refused too, even when that field is the
   same primitive: that is the limit of this rule, which upstream also
   refuses, not a need of soundness. *)

Primitive int := #int63_type.

Module Type T. End T.

Module Type S.
  Primitive a := #int63_add.
End S.

(* The field's own declaration, through the alias of the field to
   itself. *)
Module MA : S.
  Primitive a := #int63_add.
End MA.

Definition double (x : int) : int := MA.a x x.

(* A functor argument whose type has a primitive field. *)
Module FA (Y : S).
  Definition d (x : int) : int := Y.a x x.
End FA.

Module RA := FA MA.

(* The field's own declaration, given directly. *)
Module Type ST (Y : T).
  Primitive a := #int63_add.
End ST.

Module FAdd (Y : T).
  Primitive a := #int63_add.
End FAdd.

Module FAddS : ST := FAdd.

(* A different primitive is refused, given directly. *)
Module FSub (Y : T).
  Primitive a := #int63_sub.
End FSub.
Fail Module FSubS : ST := FSub.

(* The shape of rocq-prover/rocq#18503: another operator, through the
   alias of the field to itself. *)
Module Type S2.
  Primitive bar := #int63_sub.
End S2.

Module N2 : S2.
  Primitive bar := #int63_land.
Fail End N2.
Reset N2.

(* An alias to another module's field is refused, even when that field is
   the same primitive: the field of MAS is an alias of MA'.a, not of
   itself. Upstream refuses it too. *)
Module MA'.
  Primitive a := #int63_add.
End MA'.
Fail Module MAS : S := MA'.

(* For the same reason, an alias of a module that implements S is refused
   as an argument of FA. *)
Module MA3 := MA.
Fail Module RA3 := FA MA3.

(* A parameter is refused. *)
Module MPar : S.
  Parameter a : int -> int -> int.
Fail End MPar.
Reset MPar.
