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

val set_opaque_checked_hook :
  (Names.Constant.t -> Opaqueproof.opaque -> Environ.env -> Constr.t -> unit) -> unit
(** Prototype C7 (measurement only, never merged): [set_opaque_checked_hook f]
    makes the check of each opaque body call [f kn o env c] in the process that
    runs it, right after the check of [c] returned normally: [kn] is the
    constant, [o] its opaque, [env] the environment [c] was checked in and [c]
    the cooked body that was checked. Nothing calls it for a check that
    raised. [f] must raise nothing. Default: does nothing. *)

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
