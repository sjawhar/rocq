(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

let valid_id id = Id.is_valid (Id.to_string id)

let valid_dirpath dp = List.for_all valid_id (DirPath.repr dp)

let valid_mbid mbid =
  let _, id, dp = MBId.repr mbid in
  valid_id id && valid_dirpath dp

let rec valid_modpath = function
  | ModPath.MPfile dp -> valid_dirpath dp
  | ModPath.MPbound mbid -> valid_mbid mbid
  | ModPath.MPdot (mp, label) -> valid_modpath mp && valid_id label

let valid_kername kn =
  let mp, label = KerName.repr kn in
  valid_modpath mp && valid_id label

(* The steps that [finite_names] may take for each kernel name: a few tens
   for any name that coqc writes, one step for each module its declaration
   is nested in and for each identifier of its library's logical path, or
   of the directory path of the functor parameter it is declared under. A
   cycle, of modules or in the list of a directory path, goes on past any
   bound, and so does a chain longer than the bound: either fails. *)
let name_steps = 4096

(* Whether the module path [mp] ends within [n] steps. At most [n + 1]
   steps, whatever [mp] is: [List.compare_length_with l k] looks at most
   at [k + 1] cells of [l]. *)
let rec modpath_ends n mp =
  n > 0 &&
  (match mp with
   | ModPath.MPfile dp -> List.compare_length_with (DirPath.repr dp) (n - 1) <= 0
   | ModPath.MPbound mbid ->
     let _, _, dp = MBId.repr mbid in
     List.compare_length_with (DirPath.repr dp) (n - 1) <= 0
   | ModPath.MPdot (mp, _) -> modpath_ends (n - 1) mp)

(* The kernel names found finite so far in this process: at each slot, the
   last one found there, or [no_kernel_name]. A name's slot is picked by
   the hash it carries ([KerName.hash]), which is read, not computed, and
   the name is taken as finite without a walk only where the slot holds
   that very value ([==]): a name never changes, so it still ends where it
   was found to end. Names that share a hash, as a forged library can make
   them all do, only take each other's slot, and are walked again. The
   occurrences of a constant in a body usually share its name, which is
   then walked once instead of at each occurrence. Nothing empties the
   cache, and nothing needs to: it keeps alive at most [finite_slots]
   names. A worker inherits it with the memory of the main process, where
   the names in it are the same values. *)
let finite_slots = 4096

let no_kernel_name = KerName.make ModPath.dummy (Id.of_string "dummy")

let finite_kernel_names = Array.make finite_slots no_kernel_name

let finite_kernel_name kn =
  let i = KerName.hash kn land (finite_slots - 1) in
  finite_kernel_names.(i) == kn
  || (modpath_ends name_steps (KerName.modpath kn)
      && (finite_kernel_names.(i) <- kn; true))

let finite_names = function
  | GlobRef.VarRef _ -> true
  | GlobRef.ConstRef c ->
    finite_kernel_name (Constant.user c) && finite_kernel_name (Constant.canonical c)
  | GlobRef.IndRef (mind, _) | GlobRef.ConstructRef ((mind, _), _) ->
    finite_kernel_name (MutInd.user mind) && finite_kernel_name (MutInd.canonical mind)

let quote s = "\"" ^ String.escaped s ^ "\""
