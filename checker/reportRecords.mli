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
    only for the very opaque value whose check made it, and only as the
    body of a constant of the name that check had. So the report still
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

    The records are kept, while a worker runs, in an unnamed file in
    /dev/shm, a file system in memory, and once the worker has ended, in
    the memory of the main process, which copies that file and closes it at
    once: nothing is left in /dev/shm, however the run ends, but for a kill
    in the instant between the creation of a file and its removal, as for
    the files of the workers' output ([CheckWorkers.open_capture]). Nothing
    is recorded where /dev/shm is not a directory rocqchk may create files
    in, nor where it shares its file system with the temporary directory
    (TMPDIR), in which the files of the workers' output are made, or with a
    file rocqchk holds open as it starts, such as its standard output and
    error. Without records, rocqchk then writes nothing to the file system
    of the records, so the records cannot take the room that a write of
    rocqchk needs; a full /dev/shm only stops recording. The records are
    bounded: a process records nothing more once its records would pass
    64 MiB, and if the records of all processes would pass 256 MiB, or name
    more than 32 Mi objects in all (33,554,432, counted with repetitions,
    as the main process decodes them), none is used, and the report reads
    every body, as it does at [-j 1]. A write of the records past the limit
    on the size of a file ([ulimit -f]) fails, SIGXFSZ being ignored for
    that write alone, and costs the records, not the run. The main process
    opens a file for the records only for a worker, before forking it, and
    closes it once that worker has ended; it holds no other. Nothing is
    recorded where the soft limit on open files ([ulimit -n], read from
    /proc/self/limits), less the descriptors open as the recorder starts
    (listed in /proc/self/fd), is below [4 * n + 64] at [-j n], nor where
    that limit or those descriptors cannot be read: this keeps the recorder
    from taking, at low limits, the descriptors rocqchk needs without
    records, and the report reads every body, as at [-j 1].

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
    ([CheckWorkers.set_worker_file]). Opens no file but the directory
    /proc/self/fd and the file /proc/self/limits, each closed at once.
    Installs nothing where /dev/shm cannot hold the records, as said above,
    nor where the soft limit on open files read there, less the descriptors
    open now, is below [4 * n + 64] at [-j n] ([CheckWorkers.jobs]), which
    keeps the recorder from taking, at low limits, the descriptors rocqchk
    needs without records, nor where that limit or those descriptors cannot
    be read. If anything fails, nothing is recorded, and the report reads
    every body, as it does at [-j 1]. Raises nothing but [Sys.Break]. *)

val collect : unit -> t option
(** In the main process, once every check has passed and every worker has
    finished: takes out the recorder and reads the records of every
    process, which it then drops. [None] when [start] did not record, or
    when even empty records cannot be made; no record when the records
    cannot be read, when the copy of a worker's file failed, or when they
    would have passed 256 MiB (for tests only, a number of bytes in
    [COQ_TEST_SUITE_STATEMENT_REPORT_RECORDS_CAP] lowers that cap) or
    32 Mi objects named. Raises nothing but [Sys.Break]. *)

val recorded : t -> Names.Constant.t -> Opaqueproof.opaque -> Names.GlobRef.t list option
(** [recorded r kn o]: the objects recorded for the body of the very opaque
    value [o], compared physically, as the body of a constant of the name
    of [kn] ([Names.Constant.UserOrd]), if two records of it do not
    disagree, for [Check_closure.print]. Counts the answer, for
    [test_counts]. Costs a lookup in a map ordered by names, and a walk of
    the records of that name, whatever the library files hold. *)

val test_counts : t -> unit
(** After the report, for tests only: with
    [COQ_TEST_SUITE_STATEMENT_REPORT_COUNTS] set to a file, writes to that
    file how many opaque bodies the report took from the records and how
    many it read, as ["<hits> <reads>"]. Prints nothing. *)
