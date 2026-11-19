(* A global sort's kernel name is its library and its name, not its module
   (UnivGen.new_sort_global). So a second global sort of one name in another
   module of the same library must be refused with a user error before it
   reaches the kernel's assertions. Fail re-raises anomalies, so each Fail
   below passes only on a user error. The cases after them pass today and
   must keep passing. Universes carry a counter in their kernel name, so they
   are not affected. *)

(* Module, then top level. *)
Module Hide1.
  Sort s1.
End Hide1.
Fail Sort s1.
Fail Sort t1 s1.

(* Top level, then module. *)
Sort s2.
Module M2.
  Fail Sort s2.
End M2.

(* Two modules. *)
Module M3.
  Sort s3.
End M3.
Module N3.
  Fail Sort s3.
End N3.

(* Functor body, then top level. *)
Module Type T4. End T4.
Module F4 (X : T4).
  Sort s4.
End F4.
Fail Sort s4.

(* Module, then a polymorphic sort in a section. *)
Module Hide5.
  Sort s5.
End Hide5.
Section X5.
  Fail Polymorphic Sort s5.
End X5.

(* A section-bound sort leaves the environment at End. *)
Section A7.
  Polymorphic Sort s7.
End A7.
Section B7.
  Polymorphic Sort s7.
End B7.

Section A8.
  Polymorphic Sort s8.
End A8.
Sort s8.

(* Include and functor application. *)
Module Hide10.
  Sort s10.
End Hide10.
Include Hide10.

Module Type T11. End T11.
Module F11 (X : T11).
  Sort s11.
End F11.
Module E11. End E11.
Module A11 := F11 E11.
Module B11 := F11 E11.
