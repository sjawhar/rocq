#!/usr/bin/env bash
# A control that observes the error or the result of the command it wraps and
# then discards its effect (Fail, Succeed) sees the same Qed as without the
# skip: the kernel checks the proof in full, so the file compiles with the
# same status and the same output with -skip-qed-typecheck, with
# -set "Skip Qed Typecheck" and after "Set Skip Qed Typecheck." as it does
# without them. A command that rolls the document back past a proof the
# kernel did not check runs that check too, so the file stops with the same
# status and with the error Qed raises without the skip. The skip still
# applies to a Qed no command discards, but rocq compile -vos, rocq compile
# -vok and a toplevel, which write no .vo, check every Qed they run.
set -euo pipefail

export PATH="$BIN:$PATH"
workdir=$(mktemp -d)
trap 'rm -rf "$workdir"' EXIT

fail() { echo "$*" >&2; exit 1; }

bad='Lemma discarded_bad : False.
Proof. exact_no_check I.'
good='Lemma kept_good : True.
Proof. exact I.'
kernel_error='The term "I" has type "True" while it is expected to have type "False".'
ignored_option='has no effect here'

# Options every arm of the next case takes, for a case that needs its own, and
# the command it runs: rocq compile by default, or one of the toplevels, which
# read the case through -l.
extra=()
tool=compile

# Every arm compiles the same path, so a message that names the file reads the
# same, and every arm's first line is one line, so a message that names a line
# reads the same too.
compile() { # case arm
  local arm=$2 dir="$workdir/$1" rc=0
  local -a args=()
  case $arm in
    plain) printf '(* no skip *)\n' > "$dir/case.v";;
    option) args=(-skip-qed-typecheck); printf '(* option *)\n' > "$dir/case.v";;
    set) args=(-set "Skip Qed Typecheck"); printf '(* set *)\n' > "$dir/case.v";;
    inline) printf 'Set Skip Qed Typecheck.\n' > "$dir/case.v";;
    *) fail "unknown arm $arm";;
  esac
  cat "$dir/body.v" >> "$dir/case.v"
  # -test-mode prints the message Fail caught, which rocq compile is quiet
  # about, so the comparison below reads it.
  case $tool in
    compile)
      rocq c -q -test-mode ${extra[@]+"${extra[@]}"} ${args[@]+"${args[@]}"} \
        -R "$dir" Top "$dir/case.v";;
    *)
      $tool -batch -q -test-mode ${extra[@]+"${extra[@]}"} \
        ${args[@]+"${args[@]}"} -l "$dir/case.v";;
  esac > "$dir/$arm.out" 2>&1 || rc=$?
  printf '%s\n' "$rc" > "$dir/$arm.rc"
  # A Redirect case writes here, and the next arm would overwrite it.
  if [ -e "$dir/redirected.out" ]; then mv "$dir/redirected.out" "$dir/$arm.redirected"; fi
}

build() { # case body...
  local case=$1 arm
  shift
  mkdir -p "$workdir/$case"
  printf '%s\n' "$@" > "$workdir/$case/body.v"
  for arm in plain option set inline; do compile "$case" "$arm"; done
}

# The three skip arms must agree with the arm that does not skip, in exit
# status and in output.
same() { # case expected-status body...
  local case=$1 expected=$2 arm
  shift 2
  build "$case" "$@"
  [ "$(cat "$workdir/$case/plain.rc")" = "$expected" ] ||
    { cat "$workdir/$case/plain.out" >&2
      fail "$case: exit status $(cat "$workdir/$case/plain.rc") without the skip, expected $expected"; }
  for arm in option set inline; do
    [ "$(cat "$workdir/$case/$arm.rc")" = "$expected" ] ||
      { cat "$workdir/$case/$arm.out" >&2
        fail "$case/$arm: exit status $(cat "$workdir/$case/$arm.rc") with the skip, $expected without it"; }
    diff -u "$workdir/$case/plain.out" "$workdir/$case/$arm.out" >&2 ||
      fail "$case/$arm: the output with the skip differs from the output without it"
  done
}

says() { # case text [arm...], the arm that does not skip by default
  local case=$1 text=$2 arm
  shift 2
  [ $# -gt 0 ] || set -- plain
  for arm in "$@"; do
    grep -qF "$text" "$workdir/$case/$arm.out" ||
      { cat "$workdir/$case/$arm.out" >&2
        fail "$case/$arm: the output does not say \"$text\""; }
  done
}

# (a) Fail Qed on an ill-typed proof: the error is caught, Abort drops the
# proof, and the file compiles.
same fail_bad 0 "$bad" 'Fail Qed.' 'Abort.' "$good" 'Qed.'
says fail_bad 'The command has indeed failed with message:'

# (b) Succeed Qed on an ill-typed proof: the error is not caught, so the file
# does not compile.
same succeed_bad 1 "$bad" 'Succeed Qed.' 'Abort.'
says succeed_bad "$kernel_error"

# Save closes a proof the same way, so the two controls read its verdict too.
same fail_save_bad 0 "$bad" 'Fail Save other_name.' 'Abort.'
says fail_save_bad 'The command has indeed failed with message:'
same succeed_save_bad 1 "$bad" 'Succeed Save other_name.' 'Abort.'

# (c) the controls on a well-typed proof.
same fail_good 1 "$good" 'Fail Qed.' 'Abort.'
says fail_good 'The command has not failed!'
same succeed_good 0 "$good" 'Succeed Qed.' 'Qed.'

# (d) the other controls, which keep the effect of the command they wrap, and
# the two that discard it nested in each other.
same fail_succeed_bad 0 "$bad" 'Fail Succeed Qed.' 'Abort.'
says fail_succeed_bad 'The command has indeed failed with message:'
same succeed_fail_bad 0 "$bad" 'Succeed Fail Qed.' 'Abort.'
says succeed_fail_bad 'The command has indeed failed with message:'
# The inner Fail catches the error of Qed, so the outer one has nothing to
# catch and the file does not compile.
same fail_fail_bad 1 "$bad" 'Fail Fail Qed.' 'Abort.'
says fail_fail_bad 'The command has not failed!'
same timeout_fail_bad 0 "$bad" 'Timeout 600 Fail Qed.' 'Abort.'
says timeout_fail_bad 'The command has indeed failed with message:'
same redirect_fail_bad 0 "$bad" \
  "Redirect \"$workdir/redirect_fail_bad/redirected\" Fail Qed." 'Abort.'
# Redirect sends the caught message to the file, so compare the file too.
# The file is absent when the arm wrote none, so read it only if it is there.
grep -qF 'The command has indeed failed with message:' "$workdir/redirect_fail_bad/plain.redirected" ||
  { cat "$workdir/redirect_fail_bad/plain.redirected" >&2 || true
    fail "redirect_fail_bad: the redirected output does not report the caught error"; }
for arm in option set inline; do
  diff -u "$workdir/redirect_fail_bad/plain.redirected" "$workdir/redirect_fail_bad/$arm.redirected" >&2 ||
    fail "redirect_fail_bad/$arm: the redirected output with the skip differs from the one without it"
done

# (e) the skip still applies to a Qed no control discards: the file compiles
# with the skip and not without it.
skips() { # case body...
  local case=$1 arm
  shift
  build "$case" "$@"
  [ "$(cat "$workdir/$case/plain.rc")" = 1 ] ||
    { cat "$workdir/$case/plain.out" >&2
      fail "$case: the ill-typed proof compiled without the skip"; }
  for arm in option set inline; do
    [ "$(cat "$workdir/$case/$arm.rc")" = 0 ] ||
      { cat "$workdir/$case/$arm.out" >&2
        fail "$case/$arm: the skip did not apply"; }
  done
}

# The force ends with the control that raised through it.
skips scoped "$bad" 'Fail Qed.' 'Abort.' \
  'Lemma bad : False.' 'Proof. exact_no_check I. Qed.' 'Print Assumptions bad.'
says scoped 'bad has an opaque proof not checked by the kernel.' option set inline

# It ends with the control that returned through it too.
skips after_succeed "$good" 'Succeed Qed.' 'Qed.' \
  'Lemma bad : False.' 'Proof. exact_no_check I. Qed.'

# Time, Instructions, Profile, Timeout and Redirect keep the effect of the
# command and never set the force, so the skip still applies under them.
# Time, Instructions and Profile print a measure and Redirect takes the
# output away, so these read the status alone.
skips time_bad "$bad" 'Time Qed.'
skips instructions_bad "$bad" 'Instructions Qed.'
skips profile_bad "$bad" 'Profile Qed.'
skips timeout_bad "$bad" 'Timeout 600 Qed.'
skips redirect_bad "$bad" "Redirect \"$workdir/redirect_bad/redirected\" Qed."

# (f) a rollback discards a proof the kernel did not check: the check runs
# there, so the file stops with the status it has without the skip, and with
# the kernel's error. The error is raised at the command that rolls back
# rather than at the Qed, so these read the status of every arm and the
# message, not the whole output.
same_status() { # case expected-status body...
  local case=$1 expected=$2 arm
  shift 2
  build "$case" "$@"
  for arm in plain option set inline; do
    [ "$(cat "$workdir/$case/$arm.rc")" = "$expected" ] ||
      { cat "$workdir/$case/$arm.out" >&2
        fail "$case/$arm: exit status $(cat "$workdir/$case/$arm.rc"), expected $expected"; }
  done
}

# Every arm stops with status 1 and with the kernel's error.
stops_with_kernel_error() { # case body...
  local case=$1
  shift
  same_status "$case" 1 "$@"
  says "$case" "$kernel_error" plain option set inline
}

# Reset by name, Reset Initial, and Reset of the module that holds the proof.
stops_with_kernel_error reset_bad "$bad" 'Qed.' 'Reset discarded_bad.'
stops_with_kernel_error reset_initial_bad "$bad" 'Qed.' 'Reset Initial.'
stops_with_kernel_error reset_module_bad 'Module M.' "$bad" 'Qed.' 'End M.' \
  'Reset M.'

# One rollback discards three proofs: the well-typed one passes its check, and
# of the two that do not, the error is the earlier one's, as it is without the
# skip, which is what stops_with_kernel_error reads.
bad2='Lemma discarded_bad2 : True.
Proof. exact_no_check 0.'
stops_with_kernel_error reset_three "$good" 'Qed.' "$bad" 'Qed.' \
  "$bad2" 'Qed.' 'Reset kept_good.'

# Reset kept_good gives discarded_bad the handle of kept_good, and Reset m1
# brings kept_good back under it: the check of discarded_bad must still run.
stops_with_kernel_error reset_reused_handle_bad 'Definition m0 := 0.' \
  "$good" 'Qed.' 'Definition m1 := 0.' 'Reset kept_good.' \
  "$bad" 'Qed.' 'Reset m1.'

# The stm closes a proof nested in another by discarding its declaration and
# declaring it again, so the check of such a proof runs at its Qed, even here
# where the file keeps the proof.
stops_with_kernel_error nested_bad 'Set Nested Proofs Allowed.' \
  'Lemma outer : True.' "$bad" 'Qed.' 'exact I.' 'Qed.'

# The stm reads a navigation command without its control, so Fail catches
# nothing here.
stops_with_kernel_error fail_reset_bad "$bad" 'Qed.' \
  'Fail Reset discarded_bad.'

# (g) a navigation command that cannot roll back after a Qed is rejected
# before it discards anything, with or without the skip, and the file stops
# either way.
same_status undo_bad 1 "$bad" 'Qed.' 'Undo.'
says undo_bad 'Cannot undo.' option set inline
same_status undo_to_bad 1 "$bad" 'Qed.' 'Undo To 1.'
says undo_to_bad 'No focused proof' option set inline
same_status restart_bad 1 "$bad" 'Qed.' 'Restart.'
says restart_bad 'No focused proof' option set inline
same_status back_bad 1 "$bad" 'Qed.' 'Back.'
says back_bad 'Navigation commands forbidden in files.' option set inline

# (h) a rollback that discards a well-typed proof the kernel did not check:
# its check passes, so the file compiles with the same output as without the
# skip. A section variable, a universe-polymorphic proof and an abstract
# subproof are what the stored proof has to be prepared for.
same reset_good 0 "$good" 'Qed.' 'Reset kept_good.'
same reset_module_good 0 'Module M.' "$good" 'Qed.' 'End M.' 'Reset M.'
same reset_section_good 0 'Section S.' 'Variable n : nat.' 'Lemma good_s : n = n.' \
  'Proof. reflexivity. Qed.' 'End S.' 'Reset Initial.'
same reset_poly_good 0 'Polymorphic Lemma good_p : forall (A : Type) (x : A), x = x.' \
  'Proof. intros. reflexivity. Qed.' 'Definition use_p := good_p nat 0.' 'Reset Initial.'
same reset_abstract_good 0 'Lemma good_a : forall n : nat, n + 0 = n.' \
  'Proof. intro n. abstract (induction n; simpl; auto). Qed.' 'Reset Initial.'

# (i) a command that discards no proof leaves the skip alone: the proof
# reaches the .vo, where rocqchk checks it, and Print Assumptions reports it
# as not checked. Abort All with no proof open rolls nothing back, End keeps
# what the module holds, and Load keeps what it read.
unchecked_proof='discarded_bad has an opaque proof not checked by the kernel.'
skips abort_all_kept "$bad" 'Qed.' 'Abort All.' 'Print Assumptions discarded_bad.'
says abort_all_kept "$unchecked_proof" option set inline
skips module_kept 'Module M.' "$bad" 'Qed.' 'End M.' 'Print Assumptions M.discarded_bad.'
says module_kept "M.$unchecked_proof" option set inline
printf '%s\n' "$bad" 'Qed.' > "$workdir/loaded_bad.v"
skips load_kept "Load \"$workdir/loaded_bad\"." 'Print Assumptions discarded_bad.'
says load_kept "$unchecked_proof" option set inline

# A rollback that discards a well-typed proof keeps the ill-typed one the
# restored state holds: its check must not run, and the skip still applies.
skips reset_keeps_bad "$bad" 'Qed.' "$good" 'Qed.' 'Reset kept_good.' 'Print Assumptions discarded_bad.'
says reset_keeps_bad "$unchecked_proof" option set inline

# (j) neither a proof worker nor an interactive session is a document rocq
# compile builds, and only such a document checks what it discards. With
# -async-proofs on the Qed is delegated, and the worker restores the state it
# froze before it, which is no rollback: the skip must still apply.
# -stm-debug makes each process print its steps to stderr, each message led by
# "<pid>:<name>:<thread>] ", where a proof worker's name is proof:<n>:<m>.
# A worker prints some lines as it starts, before any task; it prints
# "reaching:" only while it builds a proof. ran_in_worker fails a case
# unless every arm has such a line, so it fails if the stm keeps the proof.
ran_in_worker() { # case
  local case=$1 arm
  for arm in plain option set inline; do
    grep -qE '[0-9]+:proof:[0-9]+:[0-9]+:[0-9]+\] reaching: ' \
      "$workdir/$case/$arm.out" ||
      { cat "$workdir/$case/$arm.out" >&2
        fail "$case/$arm: no proof worker built the proof"; }
  done
}
async_proofs=(-async-proofs on -async-proofs-j 1)
extra=("${async_proofs[@]}" -stm-debug)
skips async_bad "$bad" 'Qed.'
ran_in_worker async_bad
# A block that a proof worker runs takes its Fail Qed or Succeed Qed with it.
# The worker's document is not one rocq compile builds, so it checks nothing
# it discards, and the force of the control is the only check there.
# Without it, the ill-typed proof would pass Succeed: a Qed after it would
# keep the proof unchecked in the .vo, an Admitted after it in no file.
stops_with_kernel_error succeed_async_bad "$bad" 'Succeed Qed.' 'Qed.'
ran_in_worker succeed_async_bad
stops_with_kernel_error succeed_admitted_async_bad "$bad" 'Succeed Qed.' \
  'Admitted.'
ran_in_worker succeed_admitted_async_bad
same_status fail_admitted_async_bad 0 "$bad" 'Fail Qed.' 'Admitted.'
ran_in_worker fail_admitted_async_bad
says fail_admitted_async_bad 'The command has indeed failed with message:' \
  plain option set inline
says fail_admitted_async_bad "$kernel_error" plain option set inline
# -stm-debug prints process ids, so a case that compares outputs runs
# without it.
extra=("${async_proofs[@]}")
same succeed_async_good 0 "$good" 'Succeed Qed.' 'Qed.'
# The stm runs some commands under a resilience that drops their error, so the
# error of a check a rollback ran is raised again before the document ends.
# The stm applies that resilience only when -async-proofs is not off, so this
# case needs it, and sets it itself: without it, Reset stops the file, and the
# case never reaches the raise in Opaques.Summary.join. Without the skip this
# file stops at End S, with "Open proofs remain", so only the status is the
# same in every arm.
extra=("${async_proofs[@]}")
same_status resilient_reset_bad 1 'Section S.' 'Variable n : nat.' "$bad" 'Qed.' \
  'Reset discarded_bad.' 'Definition x := 0.' 'End S.'
says resilient_reset_bad "$kernel_error" option set inline
# Whether a rollback checks depends on the kind of document, not on whether
# the process calls itself a worker, so a compile that names a worker id
# still checks.
extra=(-worker-id qed_rollback)
stops_with_kernel_error worker_id_reset_bad "$bad" 'Qed.' \
  'Reset discarded_bad.'

# A command that writes no .vo forces the check; the option only warns.
forced_stops() { # case body...
  local case=$1
  stops_with_kernel_error "$@"
  says "$case" "$ignored_option" option
}

# (k) -vos and -vok write no .vo, so nothing they process reaches rocqchk and
# their exit status is the whole verdict: they typecheck every Qed proof they
# run. As in a toplevel, the check is forced on for the whole process, the
# files they load first included, whatever the flag says, and the option only
# warns. So no arm compiles an ill-typed proof they run, with the proof
# delegated to a worker or not, and every arm compiles a well-typed one.
extra=(-vok)
forced_stops vok_bad "$bad" 'Qed.'
same_status vok_good 0 "$good" 'Qed.'
says vok_good "$ignored_option" option
extra=(-vok "${async_proofs[@]}" -stm-debug)
same_status vok_async_bad 1 "$bad" 'Qed.'
ran_in_worker vok_async_bad
says vok_async_bad "$ignored_option" option
# -l loads its file before the first line of the case, so the arm that sets
# the flag there reaches it with the skip off: only the option arm and the
# -set arm would skip.
extra=(-vok -l "$workdir/loaded_bad.v")
same_status vok_load_bad 1 'Definition after_load := 0.'
says vok_load_bad "$kernel_error" plain option set
says vok_load_bad "$ignored_option" option
# -vos does not run most proofs, but it runs some in the main process, for
# instance one that uses a command that can read an opaque proof, such as
# Print, and every proof closed under Set Universe Polymorphism.
extra=(-vos)
forced_stops vos_print_bad "$bad" 'Print nat.' 'Qed.'
forced_stops vos_poly_bad 'Set Universe Polymorphism.' "$bad" 'Qed.'
same_status vos_good 0 "$good" 'Print nat.' 'Qed.'
extra=()

# (l) a toplevel writes no .vo either, and under -batch its exit status
# says whether the files it was given go through, so it typechecks every Qed
# proof too: the check is forced on before the session reads anything, the
# files -l loads included, and the option only warns, since a project passes
# it to every command through its _CoqProject, an editor among them. These
# cases read the body through -l, with and without -async-proofs on: either
# way a toplevel runs each sentence of a -l file as it reads it, so the Qed
# finds its proof already run and checks it in the main process. The
# -async-proofs on cases pin that: a proof a toplevel sent to a worker would
# leave its check to a join that -batch never runs.
for tool in "rocq repl" coqidetop; do
  # coqidetop belongs to a package a build can leave out.
  [ -x "$BIN/${tool%% *}" ] || { echo "skipping $tool: not built"; continue; }
  name=${tool##* }
  forced_stops "${name}_bad" "$bad" 'Qed.'
  extra=("${async_proofs[@]}")
  forced_stops "${name}_async_bad" "$bad" 'Qed.'
  # The message is one of the command line's injections, so -w silences it,
  # and the check stays on.
  extra=(-w -skip-qed-typecheck-ignored)
  stops_with_kernel_error "${name}_quiet_bad" "$bad" 'Qed.'
  ! grep -qF "$ignored_option" "$workdir/${name}_quiet_bad/option.out" ||
    { cat "$workdir/${name}_quiet_bad/option.out" >&2
      fail "${name}_quiet_bad: -w did not silence the message"; }
  extra=()
done
