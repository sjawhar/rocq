(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Measurement only: a profile of the main process of [rocqchk -j N].

    Off unless [ROCQCHK_MAIN_PROFILE] names a file when this module is
    initialised; then every function here calls its argument and does
    nothing else. When it is set, the process that initialised this module
    records, at each boundary of a span, the wall time (CLOCK_MONOTONIC),
    its minor page faults (getrusage) and the time its garbage collector
    has taken so far (measured by the runtime's GC timing hooks). At its
    exit it writes [path] as a profiler trace ([NewProfile]'s format, one
    "B" and one "E" event per span) and [path.totals], one line of
    [key=value] pairs. A worker forked by [CheckWorkers] records no span
    ([in_child]); it appends one line to [path.workers] when it exits
    ([worker_exit]). *)

type span =
| Load            (** reading a library or a table of opaque proofs *)
| Vm_compile      (** compiling and injecting a library's bytecode *)
| Cook            (** cooking opaque bodies *)
| Universes       (** a library's universes, and [Safe_typing.import] *)
| Wait            (** waiting for workers *)
| Check           (** the kernel check of a library, and of an inductive *)
| Deal            (** [CheckWorkers.deal] *)
| Output          (** printing what workers printed, or what was held *)
| Intern          (** the intern of the libraries *)
| Statement_report
| Summary         (** the summary of -o *)
| Validate        (** the validation of a marshalled value *)

val span : span -> (unit -> 'a) -> 'a
(** [span s f] is [f ()], recorded as the span [s] when profiling. *)

val fork : (unit -> int) -> int
(** [fork f] is [f ()], where [f] is [Unix.fork]: recorded as the span
    "fork" in the parent. In the child, which [f] returns [0] to, nothing
    is recorded; the child must call [in_child] first. *)

val in_child : unit -> unit
(** In a process just forked: record no span from now on, and count the
    garbage collector's time, and the wall time for [worker_exit], from
    here. *)

val worker_exit : size:int -> completed:int -> code:int -> unit
(** In a worker, just before it exits with [code], having completed
    [completed] of the [size] checks of its batch: appends one line to
    [path.workers]. Never raises. *)
