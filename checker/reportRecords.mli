(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Records of the checked opaque bodies, for [rocqchk -j N
    -statement-report FILE].

    With workers, each process that checks an opaque body records the
    objects that the statement report's walk would find in that body
    ([Check_closure.opaque_body_refs]), in a file of its own in a private
    directory. Once every worker has finished, the main process reads the
    records, and the report takes the objects of a recorded body from them
    instead of reading that body from its library's table and walking it
    again ([Check_closure.print]). The report's lines, and every other byte
    of the output, are the ones the report prints without records, and so is
    the exit status. *)

val start : unit -> unit
(** In the main process, before any library is checked, with workers and a
    statement report: makes the private directory, under the temporary
    directory, and installs the recorder
    ([Mod_checking.set_opaque_check_hook]). It removes the directory at
    exit, on every exit through [exit] or an uncaught exception; a signal
    that kills the process leaves it. If the directory cannot be made, it
    does nothing, and the report reads every body, as it does at [-j 1]. *)

val collect : unit -> Check_closure.opaque_records option
(** In the main process, once every check has passed and every worker has
    finished: takes out the recorder, reads the records of every process,
    and removes their files and the directory. [None] when [start] made no
    directory; no record when the records cannot be read. *)

val print_counts : Check_closure.opaque_records -> unit
(** With [-d checker-workers], one debug line, for after the report: how
    many opaque bodies the report took from the records and how many it
    read ([Check_closure.opaque_record_counts]). *)
