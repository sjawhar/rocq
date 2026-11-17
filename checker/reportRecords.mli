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

    Nothing is recorded in a run that also compares ([-compare]): with
    [-compare] the report reads the proofs as before. The comparison, which
    comes after the report, reads opaque bodies through the same accessor
    ([CheckLibrary.indirect_accessor]), which keeps each table it reads in
    the main process; a body the report took from a record would leave its
    table unread there, so that the comparison could read the library file
    again where, without records, it uses the table the report read.

    The records are kept in unnamed temporary files, which exist only while
    rocqchk runs: nothing is left on disk, however the run ends, but for a
    kill in the instant between the creation of a file and its removal, as
    for the files of the workers' output ([CheckWorkers.open_capture]).
    They are bounded: a process records nothing more once its records
    would pass 64 MiB, and if the records of all processes would pass
    256 MiB, or name more than 32 Mi objects in all (33,554,432, counted
    with repetitions, as the main process decodes them), none is used, and
    the report reads every body, as it does at [-j 1]. A write of the
    records past the limit on the size of a file ([ulimit -f]) fails,
    SIGXFSZ being ignored for that write alone, and costs the records, not
    the run. The main process opens a file of the records only for the
    first records it keeps, after a worker has ended or when it records a
    check of its own, and holds one at most, besides the file of each
    worker that runs. Nothing is recorded where the soft limit on open
    files ([ulimit -n], read from /proc/self/limits) is below [4 * n + 64]
    at [-j n], nor where that limit cannot be read: this keeps the
    recorder from taking, at low limits, the descriptors rocqchk needs
    without records, and the report reads every body, as at [-j 1].

    The report's lines, and every other byte of the output, are the ones
    the report prints without records, and so is the exit status, with one
    known difference: a body that a worker recorded is not read again by
    the report, so a library file that changes or vanishes on disk during
    the run does not make the report warn that this body could not be read,
    nor report it as an axiom. *)

type t
(** The records, once read. *)

val start : unit -> unit
(** In the main process, before any library is checked, with workers, a
    statement report and no comparison: installs the recorder
    ([Mod_checking.set_opaque_check_hook]) and the workers' files
    ([CheckWorkers.set_worker_file]). Opens no file but /proc/self/limits,
    which it closes at once. Installs nothing where the soft limit on open
    files read there is below [4 * n + 64] at [-j n] ([CheckWorkers.jobs]),
    which keeps the recorder from taking, at low limits, the descriptors
    rocqchk needs without records, nor where that limit cannot be read. If
    anything fails, nothing is recorded, and the report reads every body,
    as it does at [-j 1]. Raises nothing but [Sys.Break]. *)

val collect : unit -> t option
(** In the main process, once every check has passed and every worker has
    finished: takes out the recorder, reads the records of every process,
    and closes the file it read them from. [None] when [start] did not
    record, or when even empty records cannot be made; no record when the
    records cannot be read, when a write or an opening of their file
    failed, or when they would have passed 256 MiB (for tests only, a
    number of bytes in [COQ_TEST_SUITE_STATEMENT_REPORT_RECORDS_CAP] lowers
    that cap) or 32 Mi objects named. Raises nothing but [Sys.Break]. *)

val recorded : t -> Opaqueproof.opaque -> Names.GlobRef.t list option
(** [recorded r o]: the objects recorded for the body of the very opaque
    value [o], compared physically, if two records of it do not disagree,
    for [Check_closure.print]. Counts the answer, for [test_counts]. *)

val test_counts : t -> unit
(** After the report, for tests only: with
    [COQ_TEST_SUITE_STATEMENT_REPORT_COUNTS] set to a file, writes to that
    file how many opaque bodies the report took from the records and how
    many it read, as ["<hits> <reads>"]. Prints nothing. *)
