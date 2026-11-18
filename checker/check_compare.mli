(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The comparator of
    [rocqchk -compare CONFIG -challenge DIR -compare-out FILE].

    The challenge and the answer carry the same library names. [rocqchk]
    checks the answer with the kernel as it does without the option; this
    module loads the challenge into a second environment without a check,
    compares every declaration of the challenge files' closure, but those of
    the pre-checked libraries and of the shared libraries they rest on, with
    the answer declaration of the same canonical kernel name, computes each
    named theorem's axiom closure and writes a JSON verdict.

    The comparison is structural after a one-to-one renaming of universe
    levels and, inside the signature of a functor, of its parameters: no
    conversion, no reduction, and no constant is unfolded.

    {2 Where a shared library may come from}

    The answer's tree may Require more of the image than the challenge
    files do, so the challenge environment loads the same SHARED libraries
    the answer loaded -- those outside the roots the challenge stands in
    for and not pre-checked -- and a constraint one of them carries is then
    not read as one the answer invented. That rests on a shared library
    being something the answer cannot write, so a run takes a shared
    library only from the directories it trusts for the image's own
    libraries: the corelib directory, user-contrib and the directories of
    [ROCQPATH] and [COQPATH], as this run locates them ([-coqlib], the
    environment, the installation). The plugins directory and the XDG
    directories are not trusted, and a run with [-boot] trusts none.

    A graded run therefore binds exactly one root with [-Q], the answer's
    project root, starts in a working directory that holds no [.vo], and is
    launched so that the answer's side cannot write a trusted directory:
    [ROCQPATH], [COQPATH] and [-coqlib], when given at all, name the image's
    directories. The option refuses what it can see: a run that loaded,
    from a bound root the challenge does not stand in for, a library the
    config does not pre-check, any bound root that is empty or is one of
    the image's own top-level names, and, on either side, a shared library
    whose recorded file lies directly in the working directory or under a
    bound directory, or that was found in a directory under none of the
    trusted ones ([prepare]). It also refuses a challenge library under a
    root the challenge stands in for, not pre-checked, read from outside the
    challenge directory, a shared library both sides loaded that the
    challenge read from another file than the answer, and a pre-checked
    library the challenge read from another file than the answer unless
    that file has the pinned sha256 ([run]). A library that passes is shared
    by where its file is, not by who wrote it. What is left -- the
    environment the grader hands the process, and so who can write a
    trusted directory -- is the grader's to get right, and
    dispatch://BET-894's R5 and R1 are where it is written down.

    The test suite stands in for the image with [ROCQPATH], because a test
    must not write into the installation it runs against. *)

type config

val read_config : string -> config
(** The config is one JSON object with the keys [theorems] (each
    [{name, permitted_axioms?}]), [permitted_axioms], [tolerated_flags]
    (each [{kind, object?}]), [rewrite_rules], [prechecked]
    ([{library, sha256}]) and [challenge_files] ([{path, sha256}]). Any
    other key, a duplicate key, a byte after the top-level value, a byte
    sequence that is not UTF-8, a name that is not a string or a pre-checked
    library whose name is not identifiers joined by dots is an error.

    A permitted axiom is named by the name it prints, and is the task's
    declaration of that name: an axiom a theorem's proof reaches passes only
    when its name is in the theorem's permitted list AND the constant of
    that kernel name lives under a pre-checked library or a shared one (a
    library outside every root the challenge stands in for: the image's own),
    exported or a field of a sealed module it hides, or the challenge and
    the answer both export it. A module path and a library path print
    alike (the constant [g] of a module [Q] of the library [R.P] prints
    [R.P.Q.g]), so a constant that only prints a permitted name fails with
    the reason that it is not the task's declaration of that name, followed
    by where the reached object lives and why it is not the task's.

    A theorem the config names is read by the kernel name of the challenge's
    constant of that printed name (two challenge constants printing it is an
    error), and a theorem whose name two answer constants print fails.

    A tolerated flag with an [object] tolerates that kind on that object
    alone, matched by the name it prints AND, by the rule for permitted
    axioms, only when the flagged object is the task's declaration of that
    name, so a relaxed condition the standard library rests on does not
    tolerate the same condition in the agent's own declaration.
    [indices-not-mattering] and [uip] take both forms. Without an object,
    [indices-not-mattering] applies wherever it appears: every inductive of
    an image built without [-indices-matter] may carry it, and the replaced
    route always allows it. The config has no [allow_uip] input, so a
    kind-only [uip] entry is that switch: writing it is the task saying
    definitional UIP is allowed wherever its proof reaches. A [uip] entry
    with an object allows it on that object alone, when the object is the
    task's declaration, and leaving both out is the task saying it is not
    allowed.

    [rewrite_rules] (default [false]) is whether the answer may declare a
    rewrite rule. Without it, every theorem fails when a library the answer
    loaded declares one, whatever symbol it rewrites: each library except a
    pre-checked one and a shared one that is one file for both sides (outside
    every root the challenge stands in for, found in a trusted directory and
    in no place an answer's file is found in: [prepare]). A library a
    pre-checked one rests on counts unless it is one of those. A library
    only the answer has counts, and so does a rule inside a module whose
    signature hides it. A rule the challenge declares counts too, since the
    answer's copy of it declares it again: such a task needs the option. A
    [Symbol] declaration with no rule is not a rule: it is an assumption,
    and the closure reports it among the theorem's axioms like an [Axiom],
    so a theorem whose proof reaches a symbol fails unless the config
    permits that symbol by name, under the rule for permitted axioms (a
    symbol the answer itself declares is never the task's).

    [answer-universe-constraints] is a kind-only tolerance for the global
    universe comparison, and one that names an object is an error. It skips
    only the answer-to-challenge direction of the universe comparison; the
    challenge-to-answer direction, both directions of the comparison of
    elimination constraints ([run]), declaration comparison, axiom checks
    and kernel checking still run. If that skipped direction would have
    failed, the record of every theorem the answer holds carries the flag
    with an object that summarizes the first failing constraints and their
    remaining count. It is not recorded when the direction already passes.

    [assumed-positive], [unsafe-fixpoint] and [type-in-type] are an error
    with an object or without: each is how a proof of False is written, and
    the replaced route denies it whatever the object (grading-tools
    [_axiom_kinds.py], [_ALWAYS_ALLOWED_KINDS]). [unchecked-eliminations]
    without an object is an error: it is how a proof of False is written
    too, and the replaced route vouches for one name at a time, so it is
    tolerated on a named object alone. Any other kind without an object is
    an error as well.
    @raise CErrors.UserError on any of these errors. *)

val prechecked_libraries : config -> Names.DirPath.t list
(** The libraries the config declares pre-checked, in its order. They load
    through the existing [-admit] path: once [check_prechecked_files] has
    checked their pins, [rocqchk] adds each of them to the admit list it
    reads, after the libraries given with [-admit]; the config is the only
    place that names them.

    A pre-checked library is never a shared one: the admit list puts it in
    the ANSWER's environment whether the answer's tree Requires it or not,
    and the challenge environment takes it only through the closure of what
    it loads anyway: its own files and the shared libraries the answer
    loaded. A config pins bytes; it cannot add a library to the challenge's
    universe graph and so decide what the challenge stands on. *)

val check_prechecked_files : config -> unit
(** Before any library is read: each pre-checked library, resolved on the
    load path in place ([CheckLibrary.library_file]), must have the sha256
    the config pins for it, so that the file the load path gives a
    pre-checked library, which loads without a check, is not unmarshalled
    before its pin is checked. When the command line names another file of
    that library, the loader reads that one instead, and [run] hashes it
    after the read.
    @raise CErrors.UserError when a file's sha256 differs from its pin, when
    a file cannot be read, or when the load path does not resolve a
    pre-checked library. *)

type t

val prepare :
  config -> dir:string -> out:string -> add_challenge_load_path:(unit -> unit) ->
  path_below_root:(Names.DirPath.t -> string option) ->
  open_roots:(Names.DirPath.t * string) list -> bound_dirs:string list ->
  trusted:string list -> t
(** Resolve the challenge files under [dir] and check the sha256 of each.
    [add_challenge_load_path] binds [dir], on the load path, in front of the
    answer's directories under each root the challenge stands in for, which
    stay behind it; it is called once, inside the challenge load.
    [path_below_root] gives the path of a library's [.vo] file below the
    directory of the root the challenge stands in for that holds it
    ([Some "X/Y.vo"] for [<root>.X.Y]), and [None] for a library under no
    such root: [dir] holds the challenge's file of that library at that path.
    A library lives under one of those roots when its name is the root's
    followed by at least one more component, which is when
    [path_below_root] gives it a path: unless pre-checked, those are the
    answer's own libraries.
    Every other library the answer loaded, unless pre-checked, is a shared
    one, which the challenge loads too, and the run is refused unless the
    file the loader recorded for it, on either side, passes two tests.
    First, it lies outside every place an answer's file is found in:
    directly in the working directory, which the load path binds
    implicitly, or anywhere under one of [bound_dirs], the directories the
    command line binds (real paths, links resolved). Second, the directory
    the loader found it in lies, by its real path, under one of [trusted],
    the directories the run trusts for the image's own libraries: the
    corelib directory, user-contrib and the directories of [ROCQPATH] and
    [COQPATH] (none under [-boot]); only those whose real path exists count,
    and a directory whose real path cannot be found is under none of them.
    That is a statement about where the file is, not about who wrote it: a
    file there is the image's only as far as the launch keeps the answer
    from writing the trusted directories (above).
    [open_roots] are the bound roots the challenge does NOT stand in for,
    with the directory each is bound to; the run is refused when the answer
    loaded a library from under one of them, or named as one of them, that
    the config does not pre-check.
    @raise CErrors.UserError when a file is missing, cannot be read or its
    sha256 differs. *)

val run :
  t -> Environ.env ->
  (Opaqueproof.opaque -> Opaqueproof.opaque_proofterm) ->
  Safe_typing.safe_environment ->
  answer_deps:(Names.DirPath.t * (Names.DirPath.t * Safe_typing.vodigest) array) list ->
  admitted:Names.DirPath.t list ->
  unit
(** Load the challenge into an environment of its own on top of the given
    empty safe environment, compare, and write the verdict file. The
    environment is the answer's, as [rocqchk] checked it, and the accessor
    reads its opaque proofs. [answer_deps] are the dependency digests each
    library the answer loaded records ([CheckLibrary.interned_deps]), and
    [admitted] the libraries given with [-admit], each by its full logical
    name, once, in command-line order (not the pre-checked libraries the
    option adds to the admit list).

    A library the answer loaded is pinned by its sha256 as a challenge file
    when it is not pre-checked, it is under a root the challenge stands in
    for, the challenge file at its path below that root's directory (by
    [path_below_root], compared by real path) is one of [challenge_files],
    and the file the answer's loader read it from has the sha256 the config
    gives that file. A library is the image's own when it is under no such
    root, not pre-checked, and its file, as the answer's loader recorded it,
    passes the two tests of [prepare] above.

    The verdict is one JSON object with the keys [format], [theorems],
    [declarations] and [admitted], in that order. [declarations] holds a
    record [{name, reason}] for each challenge declaration the answer lacks
    or changes, then the record named [<universes>] when the global universe
    comparison fails, then the record named [<qualities>] when the global
    elimination constraints differ. The latter compares, by identity (a
    global sort is its library and its name), every pair of distinct
    qualities of which at least one is a global sort of the challenge's
    environment: a pair that eliminates in the challenge must eliminate in
    the answer ([the challenge has an elimination constraint the answer does
    not:]), checked first, and a pair that eliminates in the answer must
    eliminate in the challenge ([the answer has an elimination constraint
    the challenge does not:]), elimination following paths through any
    quality; its reason lists the failing pairs [a -> b], sorted, at most
    five, then [(and n more)]. A theorem whose own declaration and the
    others compare equal fails with the [<universes>] reason when the
    universe comparison fails, else with the [<qualities>] one when the
    elimination constraints differ, before any reason about rewrite rules,
    axioms or flags. [admitted] lists the libraries of [admitted], and is
    [[]] when no [-admit] is given.

    @raise CErrors.UserError, before the challenge is loaded, when the file
    the answer's loader read a pre-checked library from is another file than
    the one [check_prechecked_files] hashed and it cannot be read or its
    sha256 differs from the pin, or when the answer did not load a
    pre-checked library; when the answer breaks a rule of [prepare] (an open
    root, a shared library's file); when a pre-checked library rests,
    directly or not, on a library that is neither pre-checked, nor pinned by
    its sha256 as a challenge file, nor the image's own, whether the run
    checks that library or not; when the answer loaded a library under a
    root the challenge stands in for without a check
    ([CheckLibrary.unchecked]: a dependency of a library given with [-norec]
    or [-admit]) that is neither pre-checked, nor pinned by its sha256 as a
    challenge file, nor in [admitted], so a library an [admitted] one
    depends on is not exempt; when, for either of the last two rules, the
    file the answer's loader read a library from cannot be read where its
    sha256 decides whether the library is pinned.
    While the challenge is loaded, before any of it is imported: when the
    challenge read a library under a root it stands in for, not pre-checked,
    from a file whose real path is not under the real path of [dir]; when a
    shared library the challenge loaded breaks the rule of [prepare] for a
    shared library's file; when the two sides record different dependency
    digests for a library that is one file for both sides; when the
    challenge read a shared library the answer loaded too from another file
    than the answer (real paths), or a pre-checked library from another file
    than the answer that cannot be read or whose sha256 is not the one the
    config pins.
    After the challenge is loaded: when the config names a theorem the
    challenge does not hold, or one whose name two challenge constants
    print.
    A verdict is never an error: the file is written and the run exits 0. *)

val sha256_of_file : string -> string
(** The hex SHA-256 of a file. [rocqchk -sha256 FILE] prints it, which is how
    the test suite checks this implementation against the standard vectors
    and against [sha256sum].
    @raise CErrors.UserError, naming the file, when it does not open (it is
    opened without blocking, so a FIFO opens at once), when its open
    descriptor is not a regular file's, before any read, or when a read
    fails. *)
