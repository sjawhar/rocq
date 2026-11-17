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
    ([Check_closure.opaque_body_refs]). Once every worker has finished, the
    main process reads the records, and the report takes the objects of a
    recorded body from them instead of reading that body from its library's
    table and walking it again ([Check_closure.print]). A record is used
    only for the very opaque value whose check made it. So the report still
    reads the bodies of the libraries it did not check, and those it
    reaches through a copy it makes itself: its implementation view
    substitutes the structure of each module it looks into, and a copy
    made with a substitution is a new value, which no record names.

    The records are kept in unnamed temporary files, which exist only while
    rocqchk runs: nothing is left on disk, however the run ends, but for a
    kill in the instant between the creation of a file and its removal, as
    for the files of the workers' output ([CheckWorkers.open_capture]).
    They are bounded: a process records nothing more once its file would
    pass 64 MiB, and if the records of all processes would pass 256 MiB,
    or name more than 32 Mi objects in all (33,554,432, counted with
    repetitions, as the main process decodes them), none is used, and the
    report reads every body, as it does at [-j 1]. A write of the records
    past the limit on the size of a file ([ulimit -f]) fails, SIGXFSZ being
    ignored for that write alone, and costs the records, not the run.

    The report's lines, and every other byte of the output, are the ones
    the report prints without records, and so is the exit status, with one
    known difference: a body that a worker recorded is not read again by
    the report, so a library file that changes or vanishes on disk during
    the run does not make the report warn that this body could not be read,
    nor report it as an axiom. *)

type t
(** The records, once read. *)

val start : unit -> unit
(** In the main process, before any library is checked, with workers and a
    statement report: makes the files of the main process and installs the
    recorder ([Mod_checking.set_opaque_check_hook]) and the workers' files
    ([CheckWorkers.set_worker_file]). If the files cannot be made, or
    anything else fails, nothing is recorded, the files made are closed,
    and the report reads every body, as it does at [-j 1]. Raises nothing
    but [Sys.Break]. *)

val collect : unit -> t option
(** In the main process, once every check has passed and every worker has
    finished: takes out the recorder, reads the records of every process,
    and closes the files. [None] when [start] did not record; no record
    when the records cannot be read, when a write of them failed, or when
    they would have passed 256 MiB (for tests only, a number of bytes in
    [COQ_TEST_SUITE_STATEMENT_REPORT_RECORDS_CAP] lowers that cap) or
    32 Mi objects named. Raises nothing but [Sys.Break]. *)

val recorded : t -> Opaqueproof.opaque -> Names.GlobRef.t list option
(** [recorded r o]: the objects recorded for the body of the very opaque
    value [o], compared physically, if two records of it do not disagree,
    for [Check_closure.print]. Counts the answer, for [print_counts]. *)

val print_counts : t -> unit
(** After the report: with [-d checker-workers], one debug line saying how
    many opaque bodies the report took from the records and how many it
    read. For tests only, with [COQ_TEST_SUITE_STATEMENT_REPORT_COUNTS] set
    to a file, writes the two numbers to that file, as ["<hits> <reads>"]. *)
