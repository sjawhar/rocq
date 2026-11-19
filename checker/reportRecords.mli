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
    -statement-report FILE]. The rules that a user sees (when rocqchk
    records, the caps of the records, the line that says they are off or
    given up, and the exception below) are those of
    doc/sphinx/practical-tools/coq-commands.rst, under [-statement-report];
    reportRecords.ml says why each holds.

    With workers, each worker that checks an opaque body records the objects
    that the statement report's walk would find in that body
    ([Check_closure.opaque_body_refs]). Once every worker has finished, the
    main process reads the records, and the report takes the objects of a
    recorded body from them instead of reading that body from its library's
    table and walking it again ([Check_closure.print]). A record is used
    only for the very opaque value whose check made it, and only as the
    body of a constant of the name that check had. So the report still
    reads the bodies of the libraries it did not check, the bodies the main
    process checked itself, which it does not record (it checks one only
    where it could not make a pipe or fork a worker), and those it reaches
    through a copy it makes itself: its implementation view substitutes the
    structure of each module it looks into, and a copy made with a
    substitution is a new value, which no record names. It reads too each
    body that names an object whose names are not finite
    ([CheckNames.finite_names]), which is never recorded.

    The caller's rules:
    - [start] is called once, in the main process, before any library is
      checked, and only with a statement report; [deferring] where the main
      process defers the check of an opaque body ([Mod_checking]);
      [collect] once every worker has ended ([CheckWorkers.finish]), then
      [status_line], both before the report; and [recorded] is given to the
      report alone, never to the closure of [-compare].
    - Nothing here prints anything, nor raises anything but [Sys.Break]:
      every failure only leaves the report to read the bodies, as it does
      at [-j 1].

    With the records, the report's lines, every other byte of the output
    but the line of [status_line], and the exit status are the ones without
    them, with one known exception. A library file that changes or vanishes
    on disk while rocqchk runs can change which opaque bodies the report
    says it could not read, and so reports as axioms, whether those bodies
    were recorded or not: the report does not read a recorded body, so it
    does not read that body's table, and does not keep it for the later
    bodies of that library that it reads, which then read the file as it is
    then. *)

type t
(** The records, once read. *)

val start : compare:bool -> unit
(** [start ~compare], where [compare] says whether the run has [-compare]:
    starts recording where the run has workers ([CheckWorkers.parallel])
    and the conditions of coq-commands.rst hold, and installs the files of
    the workers ([CheckWorkers.set_worker_file]); otherwise records nothing,
    and notes why for [status_line] where the run has workers. *)

val deferring : Names.Constant.t -> Opaqueproof.opaque -> (Environ.env -> Constr.t -> unit)
(** [deferring kn o], in the process that defers the check of the opaque
    body [o] of the constant [kn], the main process: numbers that check,
    and returns the second stage, which the process that runs the check
    calls once the check of the cooked body [c] has returned normally,
    with the environment [c] was checked in and [c], and which records the
    objects of [c] in a worker that has a file. Nothing calls the second
    stage for a check that raised. Where nothing is recorded, both stages
    do nothing. *)

val collect : unit -> t option
(** Ends the recording and returns the records of the workers that ended
    successfully: [None] where [start] did not start recording; records
    that hold none where the main process gave up, or where decoding them
    fails. *)

val status_line : unit -> string option
(** After [collect], where the run has workers and the records are off or
    were given up: the one line that says so, with its reason, which the
    caller prints before the report; [None] otherwise, also where the
    records hold no body, as where no worker could be started (no pipe or
    no fork, [CheckWorkers.spawn]) and the main process checked every body
    itself, or where every recording worker stopped on its own. So [None]
    does not say that the report took any body from the records. *)

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
