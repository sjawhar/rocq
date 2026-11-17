(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The names the checker prints must be made of identifiers.

    The checker prints names that it reads from the libraries it loads: in its
    progress lines, in the context summary of [-o] and in the report of
    [-statement-report]. A name that is not an identifier
    ([Names.Id.is_valid]), for instance one that holds a line break or a
    blank, could add a line of its own to that output. Rocq's own commands
    write no such name, but a plugin or a modified file can, so the checker
    refuses one rather than print it: [CheckLibrary] when it reads a library,
    and [Check_closure] for a name that only a term of an admitted library
    holds. [finite_names] checks another shape of the names read from the
    libraries: that they end, for the statement report's records. *)

open Names

val valid_id : Id.t -> bool

val valid_dirpath : DirPath.t -> bool
(** Every component of the path is an identifier. *)

val valid_mbid : MBId.t -> bool
(** The identifier of the functor parameter and every component of its path,
    which [MBId.to_string] prints. *)

val valid_kername : KerName.t -> bool
(** Every component of the name that [KerName.to_string] prints. *)

val finite_names : GlobRef.t -> bool
(** Whether the user name and the canonical name of the object each end
    within 4096 steps: each module of its module path ([MPdot]), the root of
    that path ([MPfile] or [MPbound]), and each identifier of the directory
    path at that root is a step. A name that coqc writes takes a few tens.

    A library file can hold a name that has no end: a module path whose
    parent is itself, or a directory path whose list loops, as the validator
    lets cyclic values through ([val_gen] in checker/validate.ml). Two
    copies of such a name, equal at every depth but not the same value,
    compare for ever: [ModPath.compare], [DirPath.compare] and their [equal]
    stop early only on the same value. A check that passes can leave such a
    name in a body, as a canonical name: the kernel reads both names of the
    first leaf of each user name it types, and takes the later leaves of that
    user name from its cache ([HConstr]), whose canonical names it never
    reads; nor does the statement report's walk, which compares objects by
    their user names. The records of that report ([ReportRecords]) copy
    names and compare them, canonical names included, so they check each
    object with this before they compare it with any other.

    Total: it walks each of the two names for at most 4096 steps and a few
    more, whatever the object holds, compares names only physically, and
    hashes and prints nothing. A name found finite is kept in a cache of the
    process, and found there again only as the very same value. *)

val quote : string -> string
(** A refused name in an error message: between double quotes, with
    [String.escaped]. *)
