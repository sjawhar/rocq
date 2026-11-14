(* The honest library that misc/rocqchk_alias_cycle_summary.sh compiles,
   and that forge.ml then turns into alias cycles coqc refuses to write:
     Module Self : T := Self.
     Module Ping : T := Pong.   Module Pong : T := Ping.
     Module Up : HasC := Down.  Module Down : T := Up.C.
   Each module ascribes T (or HasC) to Defines, so the field p is a
   parameter in the environment and a definition in the implementation: the
   -o summary asks the implementation, and must not list p here. *)
Inductive unit : Set := tt.

Module Type T. Parameter p : unit. End T.
Module Type HasC. Declare Module C : T. End HasC.

Module Defines. Definition p := tt. End Defines.
Module Outer. Module C := Defines. End Outer.

Module Self : T := Defines.
Module Ping : T := Defines.
Module Pong : T := Defines.
Module Up : HasC := Outer.
Module Down : T := Outer.C.
