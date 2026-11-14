(* Axioms behind a functor application. A field of [R := F A] or
   [R : T := F A] is what F's body makes it: an axiom F's body declares is
   R's, named R.x, which is the name Print Assumptions prints, and a field F
   defines is no axiom even where T declares it as a parameter. The summary
   must name each axiom below under the name Print Assumptions prints for
   the proof beside it, and name no field a functor defines.
   misc/rocqchk_application_axiom_summary.sh reads the two accounts against
   each other over this same file. *)

Module Type Empty. End Empty.
Module E. End E.
Module Type UseT. Parameter use : False. End UseT.

(* An axiom declared in a functor body, reached only through an application
   inside a seal, behind a definition with a body: Print Assumptions names
   S.App.in_f for boom. *)
Module F (X : Empty).
  Axiom in_f : False.
End F.
Module S : UseT.
  Module App := F E.
  Definition helper : False := App.in_f.
  Definition use : False := helper.
End S.
Definition boom : False := S.use.

(* The same, behind an opaque helper. *)
Module SOpaque : UseT.
  Module App := F E.
  Lemma helper : False. Proof. exact App.in_f. Qed.
  Definition use : False := helper.
End SOpaque.
Definition boom_opaque : False := SOpaque.use.

(* The application ascribed: its type declares use_f, which the functor
   defines from an axiom of its own body, SAscribed.App.in_g. *)
Module Type UseF. Parameter use_f : False. End UseF.
Module G (X : Empty).
  Axiom in_g : False.
  Definition use_f : False := in_g.
End G.
Module SAscribed : UseT.
  Module App : UseF := G E.
  Definition helper : False := App.use_f.
  Definition use : False := helper.
End SAscribed.
Definition boom_ascribed : False := SAscribed.use.

(* Nested: an application under a plain module inside the seal, and one
   under a seal inside the seal. *)
Module Type Use2. Parameter use : False. Parameter use2 : False. End Use2.
Module SNested : Use2.
  Module Inner.
    Module App := F E.
  End Inner.
  Module Sub : UseT.
    Module App := G E.
    Definition use : False := App.use_f.
  End Sub.
  Definition helper : False := Inner.App.in_f.
  Definition use : False := helper.
  Definition use2 : False := Sub.use.
End SNested.
Definition boom_inner : False := SNested.use.
Definition boom_sub : False := SNested.use2.

(* A functor the seal declares itself. *)
Module SLocal : UseT.
  Module H (X : Empty). Axiom in_h : False. End H.
  Module App := H E.
  Definition helper : False := App.in_h.
  Definition use : False := helper.
End SLocal.
Definition boom_local : False := SLocal.use.

(* A sealed functor applied inside the seal: its body's axiom is behind the
   field its interface declares. *)
Module K (X : Empty) : UseF.
  Axiom in_k : False.
  Definition use_f : False := in_k.
End K.
Module SSealedFunctor : UseT.
  Module App := K E.
  Definition helper : False := App.use_f.
  Definition use : False := helper.
End SSealedFunctor.
Definition boom_sealed_functor : False := SSealedFunctor.use.

(* A field T declares as a parameter and the functor defines, in the open:
   each proof below is closed. *)
Module Type T. Parameter e : nat. End T.
Module Defines (X : Empty). Definition e := 0. End Defines.
Module R : T := Defines E.
Definition uses_r := R.e.
Module SealedDefines (X : Empty) : T. Definition e := 0. End SealedDefines.
Module R2 := SealedDefines E.
Definition uses_r2 := R2.e.
(* Through an alias of the functor, and through a partial application. *)
Module DefinesAlias := Defines.
Module R3 : T := DefinesAlias E.
Definition uses_r3 := R3.e.
Module Defines2 (X : Empty) (Y : Empty). Definition e := 0. End Defines2.
Module P := Defines2 E.
Module R4 : T := P E.
Definition uses_r4 := R4.e.
(* Through the argument: Pass's Y is its parameter, which is R here. *)
Module Type HasY. Declare Module Y : T. End HasY.
Module Pass (X : T) : HasY. Module Y := X. End Pass.
Module R5 := Pass R.
Definition uses_r5 := R5.Y.e.

(* A field the functor defines from an axiom of its own body: the field is
   not named, the axiom is, under the application's name R6.hidden. *)
Module Rests (X : Empty). Axiom hidden : nat. Definition e := hidden. End Rests.
Module R6 : T := Rests E.
Definition uses_r6 := R6.e.

(* A field the functor leaves an axiom: named R7.e. *)
Module Assumes (X : Empty). Axiom e : nat. End Assumes.
Module R7 : T := Assumes E.
Definition uses_r7 := R7.e.

(* A higher-order application that holds the body it applies again: with
   HG := Hh Gh, the body of RH := Hh HG E holds Hh's body again, bound to Gh
   and E, and under it Gh's body, whose axiom is RH.M.M.g; RH.M.use, which
   the environment holds as a parameter, is defined there. The same inside a
   seal: SHigher.R.M.M.g. *)
Module Type FT (Y : Empty). Parameter use : False. End FT.
Module Gh (Y : Empty). Axiom g : False. Definition use : False := g. End Gh.
Module Hh (Fn : FT) (X : Empty).
  Module M := Fn X.
  Definition use : False := M.use.
End Hh.
Module HG := Hh Gh.
Module RH := Hh HG E.
Definition boom_higher : False := RH.use.
Module SHigher : UseT.
  Module R := Hh HG E.
  Definition use : False := R.use.
End SHigher.
Definition boom_higher_sealed : False := SHigher.use.

(* A functor an expression defines over a parameter of its own: Gexpr's
   body is F's, so the application's axiom is SExpr.App.in_f. *)
Module Gexpr (X : Empty) := F X.
Module SExpr : UseT.
  Module App := Gexpr E.
  Definition helper : False := App.in_f.
  Definition use : False := helper.
End SExpr.
Definition boom_expr : False := SExpr.use.

(* A functor declared with Declare Module has no body: its type's parameter
   is the application's axiom, SDecl.App.p. *)
Module Type DT. Parameter p : False. End DT.
Declare Module DF (X : Empty) : DT.
Module SDecl : UseT.
  Module App := DF E.
  Definition helper : False := App.p.
  Definition use : False := helper.
End SDecl.
Definition boom_decl : False := SDecl.use.

(* An application a module type declares, reached through a Declare Module
   inside the seal: no implementation leads to it, so the walk lists what
   its type declares without a body, here the axiom SDeclType.D.App.in_f. *)
Module Type WithApp. Module App := F E. End WithApp.
Module SDeclType : UseT.
  Declare Module D : WithApp.
  Definition helper : False := D.App.in_f.
  Definition use : False := helper.
End SDeclType.
Definition boom_decl_type : False := SDeclType.use.
