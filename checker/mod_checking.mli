(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val set_indirect_accessor : (Opaqueproof.opaque -> Opaqueproof.opaque_proofterm) -> unit

val set_opaque_check_hook :
  (Opaqueproof.opaque -> (Environ.env -> Constr.t -> unit)) -> unit
(** [set_opaque_check_hook f]: the check of each opaque body [o] calls
    [f o] when it is deferred, in the process that defers it (the main
    process), and the function [f o] returned right after the check of the
    cooked body [c] returned normally, in the process that runs it, with
    the environment [c] was checked in and [c]. Nothing calls the second
    stage for a check that raised. [f] and what it returns must raise
    nothing but [Sys.Break]: the hook changes nothing that is checked.
    Default: does nothing. *)

val reset_opaque_check_hook : unit -> unit
(** Back to the default hook, which does nothing. *)

val compile_module_bytecode : Environ.env -> Vmlibrary.t -> Names.ModPath.t ->
  'a Mod_declarations.generic_module_body ->
  Vmlibrary.t * 'a Mod_declarations.generic_module_body
(** Recompile the VM bytecode of every constant of a module (type) body from its
    body, discarding whatever code the [.vo] file claims, and add it to the given
    table. *)

val check_module : Environ.env -> Names.Cset.t Names.Cmap.t -> Retroknowledge.action list -> Names.ModPath.t -> Mod_declarations.module_body -> Names.Cset.t Names.Cmap.t

exception BadConstant of Names.Constant.t * Pp.t

(** Record assumptions hidden by module signatures without type checking. *)
val collect_module_opaques : Environ.env -> Names.Cset.t Names.Cmap.t -> Names.ModPath.t -> Mod_declarations.module_body -> Names.Cset.t Names.Cmap.t
