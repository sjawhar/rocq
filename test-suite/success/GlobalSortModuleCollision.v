(* A global sort's kernel name is its library and its name, not its module
   (UnivGen.new_sort_global). So a second global sort of one name in another
   module of the same library must be refused with a user error before it
   reaches the kernel's assertions. Fail re-raises anomalies, so each Fail
   below passes only on a user error. The cases after them must succeed.
   Universes carry a counter in their kernel name, so they are not
   affected. *)

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
Section A6.
  Polymorphic Sort s6.
End A6.
Section B6.
  Polymorphic Sort s6.
End B6.

Section A7.
  Polymorphic Sort s7.
End A7.
Sort s7.

(* Include and functor application. *)
Module Hide8.
  Sort s8.
End Hide8.
Include Hide8.

Module Type T9. End T9.
Module F9 (X : T9).
  Sort s9.
End F9.
Module E9. End E9.
Module A9 := F9 E9.
Module B9 := F9 E9.
