#!/usr/bin/env bash
# rocqchk -j N counts a batch as checked only when the worker that held it
# exits with code 0 and reports the checks it completed
# (CheckWorkers.completed_count). A worker killed by SIGKILL does neither,
# so the main process stops the other workers and fails the run
# (CheckWorkers.WorkerFailed): it prints "Worker process PID was killed by
# SIGKILL while checking ..." and exits with code 1
# (Coqchk_main.exit_code). Nothing that a process did not finish checking
# is accepted.
#
# The kill comes at a known point, with no timing:
# ROCQCHK_OPAQUE_AT=before:WKill.Lib:dir makes each process that reads the
# table of opaque proofs of WKill.Lib create dir/before-PID and wait, for at
# most a minute, for dir/go (CheckLibrary.test_at). At -j 4 only workers
# read that table before a failure: the worker of
# CheckWorkers.validate_tables, and each worker whose batch holds a check
# of the library. The main process reads no table when it has workers, and
# Lib.v has no sealed module whose bodies -o would make it read. So the
# test waits for the first marker, checks that its PID is a process below
# rocqchk and not rocqchk itself, and kills it with SIGKILL while it waits.
# A worker stopped at the hook is alive for that minute, so a failed kill
# fails the test.
#
# After the failure, the main process reads that table itself, to report a
# malformed table first if there is one (CheckLibrary.recheck_library,
# raise_first_table_error), so it stops at the hook too, as noted in
# misc/rocqchk_reorder.sh. dir/go is created only once its own marker is
# there: by then every worker has been killed and reaped
# (CheckWorkers.fail and abort), so the go releases no worker, and the run
# does not wait out the minute.
#
# rocqchk must then exit with code 1 and name the killed worker's PID in
# that line. If no marker appears within 30 s, if the first marker is the
# main process's or that of a process not below it, or if rocqchk does not
# end within 30 s of the kill and 30 s more after the go, the test fails.
#
# The kill is made twice, the second time with -statement-report and a
# request file of one line, with which each worker that checks a proof
# also records its objects to a file of its own, where the conditions of
# ReportRecords.start hold (checker/reportRecords.ml): the same lines and
# the same exit code are asked of both runs, and the second must print no
# report.
set -eu
: "${BIN:=$(dirname "$(command -v rocq)")/}"
export PATH="$BIN:$PATH"
unset ROCQCHK_WORKER_RELEASE_AT ROCQCHK_OPAQUE_AT ROCQCHK_INTERN_AT ROCQCHK_CHECK_AT

fail() { >&2 echo "FAILURE: $*"; exit 1; }

# children PID: the child processes of PID, one per line. pgrep -P, or the
# parent field of /proc/*/stat where pgrep is not installed.
children() {
  if command -v pgrep > /dev/null 2>&1; then
    pgrep -P "$1" || true
  else
    local s line st pp
    for s in /proc/[0-9]*/stat; do
      { read -r line < "$s"; } 2> /dev/null || continue
      read -r st pp _ <<< "${line##*) }"
      if [ "$pp" = "$1" ]; then s=${s#/proc/}; echo "${s%/stat}"; fi
    done
  fi
}

# parent PID: the parent of PID, from /proc, or from ps without /proc.
# Nothing if PID does not exist.
parent() {
  local line st pp
  if { read -r line < "/proc/$1/stat"; } 2> /dev/null; then
    read -r st pp _ <<< "${line##*) }"
    echo "$pp"
  else
    ps -o ppid= -p "$1" 2> /dev/null | tr -d ' '
  fi
}

# below ANCESTOR PID: PID is a descendant of ANCESTOR, and not ANCESTOR.
below() {
  local p=$2
  if [ "$p" = "$1" ]; then return 1; fi
  for _ in $(seq 1 64); do
    p=$(parent "$p")
    case $p in ''|*[!0-9]*) return 1 ;; esac
    if [ "$p" = "$1" ]; then return 0; fi
    [ "$p" -gt 1 ] || return 1
  done
  return 1
}

# alive PID: PID has not exited. kill -0 succeeds on a process that has
# exited but has not been reaped yet (a zombie), so where /proc is mounted
# the state of the process must not be Z.
alive() {
  local line
  kill -0 "$1" 2> /dev/null || return 1
  [ -d /proc/self ] || return 0
  { read -r line < "/proc/$1/stat"; } 2> /dev/null || return 1
  line=${line##*) }
  [ "${line%% *}" != Z ]
}

# ends PID SECONDS: wait up to SECONDS for PID to exit, polling every 0.1 s.
ends() {
  for _ in $(seq 1 $(( $2 * 10 ))); do
    alive "$1" || return 0
    sleep 0.1
  done
  ! alive "$1"
}

d=$(mktemp -d)
main=
# On any exit: rocqchk and its workers, if they still run, then the scratch
# directory.
cleanup() {
  local p
  if [ -n "$main" ]; then
    for p in $(children "$main"); do kill -KILL "$p" 2> /dev/null || true; done
    kill -KILL "$main" 2> /dev/null || true
    wait "$main" 2> /dev/null || true
  fi
  rm -rf "$d"
}
trap cleanup EXIT

# The hook splits its value at each ':'.
case $d in *:*) fail "the scratch directory $d holds a ':', which ROCQCHK_OPAQUE_AT cannot carry" ;; esac

cat > "$d/Lib.v" <<'EOF'
Lemma l1 : True. Proof. exact I. Qed.
Lemma l2 : 0 = 0. Proof. reflexivity. Qed.
Lemma l3 : 1 + 1 = 2. Proof. reflexivity. Qed.
Lemma l4 : forall n : nat, n = n. Proof. reflexivity. Qed.
Lemma l5 : forall b : bool, b = b. Proof. intro b. reflexivity. Qed.
EOF

rocq c -native-compiler no -Q "$d" WKill "$d/Lib.v"

# kill_case NAME ARGS...: the kill described above, of rocqchk run with
# ARGS besides its own, its output in $d/NAME.log and its markers in
# $d/NAME-marks, a directory of its own, so that no marker or go of an
# earlier case is seen.
kill_case() {
  local name=$1 m log target why released f R
  shift
  m="$d/$name-marks"
  mkdir "$m"
  log="$d/$name.log"
  ( ROCQCHK_OPAQUE_AT="before:WKill.Lib:$m" \
      exec rocqchk -o -bytecode-compiler yes -j 4 -worker-budget 20 "$@" -Q "$d" WKill -norec WKill.Lib \
      > "$log" 2>&1 ) &
  main=$!

  # The first marker, polled every 0.1 s for up to 30 s.
  target=
  for _ in $(seq 1 300); do
    for f in "$m"/before-*; do
      [ -e "$f" ] || continue
      [ "$f" != "$m/before-$main" ] \
        || { cat "$log" >&2; fail "$name: the hook stopped the main process $main before any worker failed"; }
      if [ -z "$target" ]; then target=${f##*/before-}; fi
    done
    if [ -n "$target" ]; then break; fi
    alive "$main" || break
    sleep 0.1
  done

  if [ -z "$target" ]; then
    if alive "$main"; then
      why="no process read the table of WKill.Lib within 30 s"
    else
      R=0
      wait "$main" || R=$?
      main=
      why="rocqchk ended, with exit code $R, before any process read the table of WKill.Lib"
    fi
    cat "$log" >&2
    fail "$name: $why"
  fi

  case $target in ''|*[!0-9]*) fail "$name: the marker before-$target names no process id" ;; esac
  below "$main" "$target" \
    || { cat "$log" >&2; fail "$name: process $target, stopped at the hook, is not a worker of rocqchk ($main)"; }
  kill -KILL "$target" \
    || { cat "$log" >&2; fail "$name: kill -KILL $target failed: the worker was not waiting at the hook"; }

  # The main process stops at the hook once it has failed (see the header):
  # let it go on only then.
  released=no
  for _ in $(seq 1 300); do
    alive "$main" || break
    if [ -e "$m/before-$main" ]; then touch "$m/go"; released=yes; break; fi
    sleep 0.1
  done
  if [ "$released" = no ] && alive "$main"; then
    cat "$log" >&2
    fail "$name: rocqchk did not end within 30 s after worker $target was killed"
  fi
  ends "$main" 30 \
    || { cat "$log" >&2; fail "$name: rocqchk did not end within 30 s after $m/go was created"; }

  R=0
  wait "$main" || R=$?
  main=

  if [ "$R" != 1 ]; then
    cat "$log" >&2
    fail "$name: rocqchk exited with code $R after worker $target was killed; expected 1"
  fi
  # The line is wrapped where it is long, so whitespace is collapsed first.
  tr -s ' \n\t' ' ' < "$log" | grep -Fq "Worker process $target was killed by SIGKILL while checking" \
    || { cat "$log" >&2; fail "$name: rocqchk did not say that worker process $target was killed by SIGKILL while checking"; }
}

kill_case kill

# The same kill with a statement report: each worker that checks a proof of
# WKill.Lib then also records its objects, to a file of its own that the
# main process opened for it (ReportRecords). The killed worker's file is
# closed with no copy, and the run fails as above, with no report.
echo 'l1 WKill.Lib.l1 -' > "$d/kill.req"
kill_case kill-report -statement-report "$d/kill.req"
if grep -q 'STATEMENT REPORT' "$d/kill-report.log"; then
  cat "$d/kill-report.log" >&2; fail "kill-report: rocqchk printed a report after a worker was killed"
fi

exit 0
