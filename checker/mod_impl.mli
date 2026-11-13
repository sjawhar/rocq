(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** What a module's implementation declares, where the environment holds an
    interface instead. See mod_impl.ml. *)

val defines_constant : Environ.env -> Names.Constant.t -> bool
(** Does the implementation give this constant a body? [false] where it
    declares it as a parameter or an axiom, and where the walk cannot read
    the implementation, so that a caller that reports assumed constants keeps
    every name it is unsure of. A field of a functor application is read in
    the functor's body. *)

val application_axioms :
  Environ.env -> Names.ModPath.t -> Mod_declarations.module_body -> Names.Constant.t list
(** The constants of the implementation of the module at this path, whose
    body is the one given, and of the modules it implements under it, that
    have no body, named under the path: for [Module R := F A] or
    [Module R : T := F A], those F's body declares without one, which are R's
    axioms under the names Print Assumptions prints for them. Where the walk
    cannot read the body of an application, the constants without a body in
    the application's type and in the result type of each functor it
    followed to it, which can be more names than Print Assumptions prints. *)

val debug_counts : Environ.env -> unit
(** With [-d checker-summary], print how many applications were read for
    this environment, and how many were stopped. *)
