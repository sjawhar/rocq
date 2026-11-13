(* The donor of the forgery modtype of rocqchk_repeated_label.sh, compiled
   with -noinit. The forged Lib.vo gives the module type U the label T, a
   second use of a label among the modules and module types, which coqc
   never writes. The environment keeps the last module type labelled T,
   and what reads module types by name, such as rocqchk -compare, reads
   only that one. This forgery gives no proof of False: it shows the check
   of the namespace of modules and module types. A second module with a
   label, rather than a module type, fails earlier, on the assertion of
   Environ.shallow_add_module, when rocqchk compiles the library's
   bytecode. *)

Unset Elimination Schemes.

Inductive unit : Set := tt.

Module Type T.
  Parameter t : Set.
End T.

Module Type U.
  Parameter u : unit.
End U.
