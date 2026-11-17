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
    records, the caps of the records, the conditions [start] checks, and the
    exception below) are those of doc/sphinx/practical-tools/coq-commands.rst,
    under [-statement-report]; reportRecords.ml says why each holds.

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
    body that names an object whose user or canonical name does not end
    within the bound of [Check_closure.finite_names], as a name whose
    module path loops, which a forged library can hold: such an object is
    never recorded. The worker checks each object of a body before it
    compares it with any other, and records no body that names such an
    object; the main process checks each object of a frame before it
    compares any, and a frame that names such an object ends the records
    of that worker.

    The caller's rules:
    - [start] is called once, in the main process, before any library is
      checked, and only with workers ([CheckWorkers.parallel]) and a
      statement report; [collect] once every worker has ended
      ([CheckWorkers.finish]), before the report; and [recorded] is given
      to the report alone, never to the closure of [-compare].
    - [start] is not called with [-compare]. The comparison, which comes
      after the report, reads opaque bodies through the same accessor
      ([CheckLibrary.indirect_accessor]), which keeps each table it reads
      in the main process; a body the report took from a record would leave
      its table unread there, so that the comparison could read the library
      file again where, without records, it uses the table the report read.
    - Nor with [-merge-inductives] or [-merge-inductives-verbose]
      ([Indmerge.enabled]): after a merge, the opaque values of the final
      environment are new values, so that no record would match one.
    - Nothing here prints anything, nor raises anything but [Sys.Break]:
      every failure only leaves the report to read the bodies, as it does
      at [-j 1].

    With the records, the report's lines, every other byte of the output,
    and the exit status are the ones without them, with one known
    exception. A library file that changes or vanishes on disk while
    rocqchk runs can change which opaque bodies the report says it could
    not read, and so reports as axioms, whether those bodies were recorded
    or not: the report does not read a recorded body, so it does not read
    that body's table, and does not keep it for the later bodies of that
    library that it reads, which then read the file as it is then. *)

type t
(** The records, once read. *)

val start : unit -> unit
(** Installs the recorder ([Mod_checking.set_opaque_check_hook] and
    [CheckWorkers.set_worker_file]) where the conditions of coq-commands.rst
    hold; does nothing otherwise. *)

val collect : unit -> t option
(** Takes the recorder out and returns the records of the workers that
    ended successfully: [None] where [start] installed nothing, or where
    even empty records cannot be made; records that hold none where the
    main process gave up recording, or where decoding them fails. *)

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
