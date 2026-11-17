#!/usr/bin/env bash
# rocqchk -j N -statement-report: each worker that checks an opaque body
# records the objects of that body, and the report takes them instead of
# reading the body again (checker/reportRecords.ml). The run at -j 3 must
# print what the run at -j 1 prints: the same report, line for line, the
# same context summary (-o), the same standard output and the same
# libraries checked and admitted, with the same exit code. The records are
# kept in unnamed files in /dev/shm, and the files of the workers' output
# in unnamed files in TMPDIR, so no run may leave anything in TMPDIR, nor a
# file of rocqchk's in /dev/shm.
#
# The -j 3 runs take the default path, where the walk starts while the
# libraries are read; COQ_TEST_SUITE_STATEMENT_REPORT_COUNTS makes rocqchk
# write "H M" there, H the opaque bodies the report took from the records
# and M those it read, and H > 0 shows the records were used. At -j 1
# nothing is recorded, and nothing is written. rocqchk records only where
# the conditions of ReportRecords.start hold (coq-commands.rst): where
# this test can see that one of them does not, it says which, checks only
# that -j 3 prints what -j 1 prints on (a), and ends there with success.
#
#  (a) A.v, a plain library: an axiom that opaque proofs use through other
#      opaque proofs. With -d checker-workers too, which prints what -j 1
#      prints, with no line of its own about the records.
#  (b) B.v: opaque proofs in a section. Their cooking information abstracts
#      a hypothesis whose type names an opaque proof of A, and a Let whose
#      body is an axiom, which only the cooked body names. A is loaded
#      without being checked, so the bodies of A are read: M > 0.
#  (c) C.v: opaque proofs reached through a functor application and an
#      Include, whose bodies are the substituted copies that C stores in the
#      types of those modules, which are checked, and so recorded, as any
#      other; and through a signature that hides a proof in its module's
#      implementation. A is loaded without being checked: M > 0.
#  (d) D.v with A, B and C, all checked in one run: every opaque body the
#      report reaches is one this run checked, and is taken from the
#      records: M = 0.
#  (e) Bad.v, a library whose first opaque proof is ill-typed, made by
#      misc/vo_segments.py: rocqchk refuses it at -j 1 and at -j 3 with the
#      same exit code, and prints no report.
#  (f) Prims.v: opaque proofs whose bodies hold an int, a float, a string
#      and an array literal, each of a type that reaches its primitive type
#      only through a rewrite rule (as misc/statement_report_primitives.sh,
#      whose literals are in transparent definitions): the primitive types
#      come from the bodies, so at -j 3 from the records.
#  (g) (a) with COQ_TEST_SUITE_STATEMENT_REPORT_UNREADABLE naming an opaque
#      proof that a worker checks: the seam comes before the records, so
#      -j 3 warns that the body could not be read and reports it as an
#      axiom, as -j 1 does.
#  (h) (d) with -worker-budget 0: every worker stops once it has completed
#      its first check, and the other checks of its batch are queued again,
#      so most bodies are checked, and recorded, by workers that stopped
#      early, each in a file of its own. The report of -j 1, and M = 0.
#  (i) (d) with ROCQCHK_WORKER_RELEASE_AT=check:1 (see misc/rocqchk_release.sh):
#      a worker asks itself to release as it starts the second check of its
#      batch, so a worker with more than two checks completes two and gives
#      the others back while it runs. The report of -j 1, and M = 0.
#  (j) (d) and (c) at -j 3, started together, with the same TMPDIR: each
#      prints the report of its run at -j 1, (d) with M = 0, and TMPDIR is
#      empty once both have ended, and nothing of theirs is left in
#      /dev/shm. The two runs number their checks differently, so a record
#      that crossed from one run to the other would name the objects of
#      another body than the check of that number there: (d) would read
#      bodies, or print another report.
#  (k) K.v, a library of opaque proofs whose bodies each name 200
#      constants, so that the first record a worker writes takes more than
#      1024 bytes. Without a limit, -j 3 prints what -j 1 prints, and takes
#      every body from the records: M = 0. Then with the size of the files
#      rocqchk writes limited to 1024 bytes (ulimit -f 1). Its standard
#      output and error go through pipes, which the limit does not apply
#      to, and its workers print nothing to the files of their output, so
#      the files that meet it are those of the records, in /dev/shm, which
#      the limit applies to as to any file: a write past it fails, instead
#      of killing the worker with SIGXFSZ, and costs records only. -j 1
#      under the limit prints what K prints at -j 1 without it, and -j 3
#      prints that too, with M > 0: the limit cost records.
#  (l) (d) at -j 3 with COQ_TEST_SUITE_STATEMENT_REPORT_RECORDS_CAP=1, which
#      lowers the cap of the records the main process copies to 1 byte: the
#      main process gives up at the first segment it would keep, and the
#      report reads every body. The report of -j 1, with H = 0 and M > 0.
#  (m) (a) with -compare, whose comparison reads opaque bodies through the
#      accessor that keeps, in the main process, each table the report
#      read: nothing is recorded, so the counts are not written, and -j 3
#      prints the report and the verdict of -j 1. The challenge is a copy
#      of A.vo, and the config pins it and the prelude, as the norec case
#      of misc/compare.sh does.
#  (n) (d) under a limit on open files of 60 (ulimit -n 60), which, less
#      the descriptors open as rocqchk starts, is below the 5 * 3 + 65 = 80
#      that -j 3 needs for the recorder to start
#      (CheckWorkers.descriptors_for_workers): nothing is recorded, so the
#      counts are not written, and -j 3 prints what -j 1 prints under the
#      same limit, which is what (d) prints at -j 1.
#  (o) (d) with TMPDIR naming a directory that does not exist, so that no
#      file of the workers' output can be made: the walk does not start
#      while the libraries are read, and the workers print to the standard
#      output and error they inherit. The records need no TMPDIR: -j 3
#      prints what (d) prints at -j 1, with H > 0 and M = 0, and the
#      directory still does not exist.
#  (p) (d) under a limit on open files of 120, which leaves room for the
#      recorder at -j 3 beside the few descriptors rocqchk starts with: the
#      records are used, H > 0 and M = 0. Then the same with 60 descriptors
#      more open as rocqchk starts: 120 is above 80, but 120 less the
#      descriptors open is not, so nothing is recorded, the counts are not
#      written, and -j 3 prints what (d) prints at -j 1.
#  (q) (d) with TMPDIR a directory in /dev/shm: the files of the workers'
#      output would share their file system with the records, so nothing
#      is recorded, the counts are not written, and -j 3 prints what (d)
#      prints at -j 1, leaving that directory empty.
#  (r) (d) with -merge-inductives, at -j 1 and at -j 3: after a merge the
#      opaque values of the final environment are new values, which no
#      record would match, so nothing is recorded (rocqchk does not start
#      the recorder), the counts are not written, and -j 3 prints what
#      -j 1 prints.
#
# A case where /dev/shm is missing, not writable, or writable by other
# users without its sticky bit needs another mount of /dev/shm than the
# one of the machine, which this test cannot make; on such a machine the
# test ends after (a) without records, as said above.
set -eu
: "${BIN:=$(dirname "$(command -v rocq)")/}"
export PATH="$BIN:$PATH"
unset ROCQCHK_WORKER_RELEASE_AT ROCQCHK_OPAQUE_AT ROCQCHK_INTERN_AT ROCQCHK_CHECK_AT
unset COQ_TEST_SUITE_STATEMENT_REPORT_FAILURE COQ_TEST_SUITE_STATEMENT_REPORT_RECORDS_CAP

d=$(mktemp -d)
t=$(mktemp -d)
# The TMPDIR made in /dev/shm for (q), once it is made.
s=
trap 'rm -rf "$d" "$t"; [ -z "$s" ] || rm -rf "$s"' EXIT
mkdir "$d/lib" "$d/prims" "$d/big" "$d/good" "$d/bad" "$d/spliced"

{
  cat <<'EOF'
Axiom ax : 0 = 0.
Lemma uses_ax : 0 = 0. Proof. exact ax. Qed.
Lemma via : 0 = 0. Proof. exact uses_ax. Qed.
Lemma clean : 1 = 1. Proof. reflexivity. Qed.
Definition model_a := via.
EOF
  # More checks, so that the workers have work.
  for i in $(seq 1 20); do
    echo "Lemma f$i : $i = $i. Proof. reflexivity. Qed."
  done
} > "$d/lib/A.v"

cat > "$d/lib/B.v" <<'EOF'
From SRPar Require A.
Axiom bax : True.
Section S.
  Variable n : nat.
  Hypothesis h : A.uses_ax = A.uses_ax.
  Let k := S n.
  Let hb : True := bax.
  Lemma sec_k : k = S n. Proof using n. reflexivity. Qed.
  Lemma sec_h : A.uses_ax = A.uses_ax. Proof using h. exact h. Qed.
  Lemma sec_let : True. Proof. exact hb. Qed.
End S.
Lemma use_sec : True. Proof. exact sec_let. Qed.
EOF

cat > "$d/lib/C.v" <<'EOF'
From SRPar Require A.
Axiom cax : 0 = 0.
Axiom mp_ax : 3 = 3.

Module Type T.
  Parameter m : nat.
  Axiom p : m = m.
End T.

Module F (X : T).
  Lemma fl : X.m = X.m. Proof. exact X.p. Qed.
  Lemma fl2 : 0 = 0. Proof. exact cax. Qed.
End F.

Module M.
  Definition m := 3.
  Lemma p : m = m. Proof. exact mp_ax. Qed.
End M.

(* The opaque bodies of FM and of H's included fields are F's, substituted. *)
Module FM := F M.
Module H.
  Include F M.
  Lemma h_own : 0 = 0. Proof. exact A.via. Qed.
End H.

(* N.q is a Parameter of S: the report follows N's implementation. *)
Module Type S.
  Parameter q : 0 = 0.
End S.
Module N : S.
  Lemma q : 0 = 0. Proof. exact cax. Qed.
End N.

Lemma plain_c : 0 = 0. Proof. exact H.h_own. Qed.
EOF

cat > "$d/lib/D.v" <<'EOF'
From SRPar Require A B C.
Lemma d1 : 0 = 0. Proof. exact C.plain_c. Qed.
Lemma d2 : True. Proof. exact B.sec_let. Qed.
Definition model_d := conj d1 d2.
EOF

for lib in A B C D; do
  rocq c -native-compiler no -Q "$d/lib" SRPar "$d/lib/$lib.v"
done

cat > "$d/prims/Prims.v" <<'EOF'
From Corelib Require Import PrimInt63 PrimFloat PrimString PrimArray.
Open Scope array_scope.

Symbol TI : Set.
Rewrite Rule TI_int := TI => int.
Lemma i : TI. Proof. exact 0%uint63. Qed.

Symbol TF : Set.
Rewrite Rule TF_float := TF => float.
Lemma f : TF. Proof. exact 0x1p-1%float. Qed.

Symbol TS : Set.
Rewrite Rule TS_string := TS => string.
Lemma s : TS. Proof. exact "a"%pstring. Qed.

Symbol TA : Type.
Rewrite Rule TA_array := TA => array nat.
Lemma a : TA. Proof. exact [| O | O |]. Qed.
EOF
rocq c -native-compiler no -allow-rewrite-rules -Q "$d/prims" SRPrim "$d/prims/Prims.v"

# K.v, for (k): the body of each opaque proof names the 200 constants
# filler_<i>, so that the first record of each worker, which gives each of
# them with its name, takes more than 1024 bytes.
sum=filler_1
for i in $(seq 2 200); do sum="$sum + filler_$i"; done
{
  for i in $(seq 1 200); do echo "Definition filler_$i : nat := 0."; done
  for j in $(seq 1 12); do
    echo "Lemma big_$j : $sum = $sum. Proof. exact (eq_refl ($sum)). Qed."
  done
} > "$d/big/K.v"
rocq c -native-compiler no -Q "$d/big" SRBig "$d/big/K.v"

cat > "$d/a.req" <<'EOF'
via SRPar.A.via -
model_a SRPar.A.model_a -
clean SRPar.A.clean SRPar.A.clean
typed SRPar.A.uses_ax SRPar.A.via
EOF
cat > "$d/b.req" <<'EOF'
sec_k SRPar.B.sec_k -
sec_h SRPar.B.sec_h -
sec_let SRPar.B.sec_let -
use_sec SRPar.B.use_sec -
EOF
cat > "$d/c.req" <<'EOF'
fm SRPar.C.FM.fl -
fm2 SRPar.C.FM.fl2 -
h SRPar.C.H.fl2 -
n SRPar.C.N.q -
plain_c SRPar.C.plain_c -
EOF
{
  cat "$d/a.req" "$d/b.req" "$d/c.req"
  echo 'model_d SRPar.D.model_d -'
} > "$d/d.req"
cat > "$d/f.req" <<'EOF'
int SRPrim.Prims.i -
float SRPrim.Prims.f -
string SRPrim.Prims.s -
array SRPrim.Prims.a -
EOF
for j in $(seq 1 12); do echo "big_$j SRBig.K.big_$j -"; done > "$d/k.req"

fail() { >&2 echo "FAILURE: $*"; exit 1; }

# The opaque proof whose body the test seam makes unreadable, for (g).
unreadable=

# The limit on the size of the files rocqchk writes, in blocks of 1024
# bytes (ulimit -f), for (k); none if empty.
fsize=

# The limit on the files rocqchk holds open (ulimit -n), for (n) and (p);
# none if empty. Under it, rocqchk starts with $extra descriptors more open,
# on /dev/null, for (p).
nofile=
extra=0

# The TMPDIR of the runs: $t, but in (o) and (q).
tmp=$t

# capture NAME J ARGS...: rocqchk -o -j J ARGS with TMPDIR set to $tmp. Its
# standard output is in $d/NAME.out and its standard error in $d/NAME.err;
# from that, the report's lines are in $d/NAME.report, the context summary
# in $d/NAME.summary, and the "Checking library:" and "Admitting library:"
# lines, sorted, in $d/NAME.libs. The counts of the records, if the run
# wrote them, are in $d/NAME.counts. Exit code in $R. With $fsize, rocqchk
# runs under that limit, and its standard output and error are pipes, to
# readers started outside the limit, so that it meets the limit only in
# the files it writes itself. With $nofile, rocqchk runs under that limit,
# with $extra descriptors more open. Each descriptor that bash opens with
# {fd}< is inherited by the commands it runs.
R=0
capture() {
  local name=$1 j=$2 po pe
  shift 2
  # call_rocqchk ARGS...: the run itself, which each branch below makes
  # under its own limits and with its own standard output and error.
  call_rocqchk() {
    TMPDIR="$tmp" COQ_TEST_SUITE_STATEMENT_REPORT_COUNTS="$d/$name.counts" \
      COQ_TEST_SUITE_STATEMENT_REPORT_UNREADABLE="$unreadable" \
      rocqchk -o -j "$j" "$@"
  }
  R=0
  rm -f "$d/$name.counts"
  if [ -n "$nofile" ]; then
    ( ulimit -n "$nofile" || exit
      for _ in $(seq 1 "$extra"); do exec {fd}</dev/null || exit; done
      call_rocqchk "$@" ) > "$d/$name.out" 2> "$d/$name.err" || R=$?
  elif [ -z "$fsize" ]; then
    call_rocqchk "$@" > "$d/$name.out" 2> "$d/$name.err" || R=$?
  else
    rm -f "$d/$name.o" "$d/$name.e"
    mkfifo "$d/$name.o" "$d/$name.e"
    cat "$d/$name.o" > "$d/$name.out" &
    po=$!
    cat "$d/$name.e" > "$d/$name.err" &
    pe=$!
    ( ulimit -f "$fsize" || exit
      call_rocqchk "$@" ) > "$d/$name.o" 2> "$d/$name.e" || R=$?
    wait "$po"
    wait "$pe"
    rm -f "$d/$name.o" "$d/$name.e"
  fi
  sed -n '/^STATEMENT REPORT$/,/^END STATEMENT REPORT$/p' "$d/$name.err" > "$d/$name.report"
  sed -n '/CONTEXT SUMMARY/,$p' "$d/$name.err" > "$d/$name.summary"
  { grep -E '(Checking|Admitting) library: ' "$d/$name.err" || true; } | sort > "$d/$name.libs"
}

# shm_files: the files in /dev/shm named as rocqchk names its files there,
# sorted; shm0: those there when this test started, which are not its own.
shm_files() { find /dev/shm -maxdepth 1 -name 'rocqchk*' 2>/dev/null | sort; }
shm0=$(shm_files)

# shm_new: the files of shm_files that were not there when this test
# started.
shm_new() { comm -13 <(printf '%s\n' "$shm0") <(shm_files); }

# empty WHAT: nothing is left in $tmp after WHAT, if it is a directory, nor
# in /dev/shm a file of rocqchk's that was not there when this test
# started. A file that a rocqchk of another test holds there, for the
# instant between its creation and its removal, is not left: what is found
# is looked for again a second later.
empty() {
  local left
  if [ -d "$tmp" ]; then
    left=$(find "$tmp" -mindepth 1 -maxdepth 1)
    [ -z "$left" ] || fail "$1 left in TMPDIR: $left"
  fi
  left=$(shm_new)
  if [ -n "$left" ]; then
    sleep 1
    left=$(shm_new)
  fi
  [ -z "$left" ] || fail "$1 left in /dev/shm: $left"
}

# run NAME J ARGS...: capture, then the run must leave nothing in $tmp, nor
# in /dev/shm. Runs that share $tmp at the same time, as in (j), are
# captured, and $tmp and /dev/shm are looked at once all of them have
# ended.
run() {
  capture "$@"
  empty "$1"
}

# counts NAME: $hits and $reads, from the counts the run NAME wrote.
counts() {
  [ -s "$d/$1.counts" ] || { cat "$d/$1.err" >&2; fail "$1: no counts of the records"; }
  read -r hits reads < "$d/$1.counts"
}

# not_recorded NAME WHAT: the run NAME, which WHAT names, wrote no counts,
# so it recorded nothing; the counts seam is set for every run.
not_recorded() {
  [ ! -e "$d/$1.counts" ] || { cat "$d/$1.counts" >&2; fail "$2 recorded opaque bodies"; }
}

# has NAME LINE: the report of the run NAME has the line LINE.
has() {
  grep -qxF "$2" "$d/$1.report" || { cat "$d/$1.err" >&2; fail "$1: no line \"$2\""; }
}

# same NAME1 NAME2 R1 WHAT: the run NAME2, whose exit code is $R, printed
# what the run NAME1 printed, and has its exit code R1.
same() {
  local part
  for part in report summary out libs; do
    diff -u "$d/$1.$part" "$d/$2.$part" > "$d/$2.diff" \
      || { cat "$d/$2.diff" >&2; fail "$4: its $part differs from -j 1"; }
  done
  [ "$R" = "$3" ] || { cat "$d/$2.err" >&2; fail "$4: exit code $R, -j 1 gave $3"; }
}

# baseline F ARGS...: the fixture F at -j 1, which ends with code 0, prints
# a whole report, a context summary and the libraries, and records
# nothing.
baseline() {
  local f=$1
  shift
  run "$f-j1" 1 -statement-report "$d/$f.req" "$@"
  [ "$R" = 0 ] || { cat "$d/$f-j1.err" >&2; fail "($f) -j 1: exit code $R"; }
  grep -qx 'END STATEMENT REPORT' "$d/$f-j1.report" \
    || { cat "$d/$f-j1.err" >&2; fail "($f) -j 1 printed no whole report"; }
  [ -s "$d/$f-j1.summary" ] || { cat "$d/$f-j1.err" >&2; fail "($f) -j 1 printed no context summary"; }
  [ -s "$d/$f-j1.libs" ] || { cat "$d/$f-j1.err" >&2; fail "($f) -j 1 named no library"; }
  not_recorded "$f-j1" "($f) -j 1"
}

# report F ARGS...: the fixture F at -j 1 (baseline), then at -j 3, which
# prints the same and takes bodies from the records. Sets $hits and $reads
# from the run at -j 3.
report() {
  local f=$1
  shift
  baseline "$f" "$@"
  run "$f-j3" 3 -statement-report "$d/$f.req" "$@"
  same "$f-j1" "$f-j3" 0 "($f) -j 3"
  counts "$f-j3"
  [ "$hits" -gt 0 ] || { cat "$d/$f-j3.err" >&2; fail "($f) -j 3: no body taken from the records"; }
}

# no_records_here: why rocqchk records nothing on this machine, by the
# conditions of ReportRecords.start (coq-commands.rst) that this test can
# see, or nothing where none of them holds. A run at -j 3 needs 80
# descriptors free for the recorder to start: the count of
# CheckWorkers.descriptors_for_workers ~extra_per_worker:1, whose formula
# in checkWorkers.ml is (4 + extra_per_worker) * jobs () + 1 + 64, with
# jobs () = 3 at -j 3, so (4 + 1) * 3 + 1 + 64 = 80. They must be free
# below the soft limit on open files (ulimit -n) less the descriptors open,
# which rocqchk counts in /proc/self/fd less the one of that listing
# (ReportRecords.open_descriptors), as this test counts those of its
# shell, which the runs below inherit; and in the system's table of open
# files, by /proc/sys/fs/file-nr, without which rocqchk records nothing.
# Cases (n) and (p) check the limit of a run less the descriptors open.
no_records_here() {
  local perm shm dir limit fds held allocated max
  if [ ! -d /dev/shm ] || [ ! -w /dev/shm ] || [ ! -x /dev/shm ]; then
    echo "/dev/shm is not a directory that rocqchk may create files in"; return
  fi
  perm=$(stat -L -c %a /dev/shm) || { echo "the mode of /dev/shm cannot be read"; return; }
  if (( (8#$perm & 8#022) != 0 && (8#$perm & 8#1000) == 0 )); then
    echo "other users may write to /dev/shm, which has no sticky bit"; return
  fi
  shm=$(stat -L -c %d /dev/shm) || { echo "the file system of /dev/shm cannot be read"; return; }
  for dir in "${TMPDIR:-/tmp}" "$d" "$t"; do
    if [ "$(stat -L -c %d "$dir")" = "$shm" ]; then
      echo "$dir is on the file system of /dev/shm"; return
    fi
  done
  if ! { read -r _ < /proc/self/limits; } 2> /dev/null || ! ls /proc/self/fd > /dev/null 2>&1; then
    echo "/proc/self/limits or /proc/self/fd cannot be read"; return
  fi
  limit=$(ulimit -Sn)
  fds=(/proc/self/fd/*)
  held=$(( ${#fds[@]} - 1 ))
  case $limit in
    unlimited) ;;
    ''|*[!0-9]*) echo "the limit on open files cannot be read"; return ;;
    *)
      if (( limit - held < 80 )); then
        echo "the limit on open files, $limit, less the $held open, leaves fewer than 80"; return
      fi ;;
  esac
  if [ ! -e /proc/sys/fs/file-nr ]; then
    echo "/proc/sys/fs/file-nr does not exist"; return
  fi
  if ! { read -r allocated _ max < /proc/sys/fs/file-nr; } 2> /dev/null; then
    echo "/proc/sys/fs/file-nr cannot be read"; return
  fi
  case $allocated$max in
    ''|*[!0-9]*) echo "/proc/sys/fs/file-nr holds no numbers"; return ;;
  esac
  if (( max - allocated < 80 )); then
    echo "the system's table of open files has fewer than 80 places left"; return
  fi
}

# Where rocqchk rightly records nothing, every case below that needs
# records would fail: then only (a) is run, which must print at -j 3 what
# it prints at -j 1.
why=$(no_records_here) || true
if [ -n "$why" ]; then
  echo "rocqchk records nothing here: $why; only (a) is checked, without records."
  baseline a -Q "$d/lib" SRPar -norec SRPar.A
  run a-j3 3 -statement-report "$d/a.req" -Q "$d/lib" SRPar -norec SRPar.A
  same a-j1 a-j3 0 "(a) -j 3 without records"
  exit 0
fi

# (a)
report a -Q "$d/lib" SRPar -norec SRPar.A
has a-j1 'axiom via SRPar.A.ax'
has a-j1 'statement typed SRPar.A.uses_ax SRPar.A.via match 1 1'
# -d checker-workers also turns the default path off. The run prints the
# report, the summary, the output and the exit code of -j 1, and among its
# debug lines none about the records, which the counts alone give.
run a-d3 3 -d checker-workers -statement-report "$d/a.req" -Q "$d/lib" SRPar -norec SRPar.A
same a-j1 a-d3 0 "(a) -j 3 -d checker-workers"
counts a-d3
[ "$hits" -gt 0 ] || { cat "$d/a-d3.err" >&2; fail "(a) -j 3 -d checker-workers: no body taken from the records"; }
if tr -s ' \n\t' ' ' < "$d/a-d3.err" | grep -qF '[checker-workers] statement report'; then
  cat "$d/a-d3.err" >&2; fail "(a) -j 3 -d checker-workers: a debug line about the records"
fi

# (b)
report b -Q "$d/lib" SRPar -norec SRPar.B
has b-j1 'axiom sec_h SRPar.A.ax'
has b-j1 'axiom sec_let SRPar.B.bax'
has b-j1 'axiom use_sec SRPar.B.bax'
[ "$reads" -gt 0 ] || { cat "$d/b-j3.err" >&2; fail "(b) -j 3: no body of A read"; }

# (c)
report c -Q "$d/lib" SRPar -norec SRPar.C
has c-j1 'axiom fm SRPar.C.mp_ax'
has c-j1 'axiom fm2 SRPar.C.cax'
has c-j1 'axiom h SRPar.C.cax'
has c-j1 'axiom n SRPar.C.cax'
has c-j1 'axiom plain_c SRPar.A.ax'
[ "$reads" -gt 0 ] || { cat "$d/c-j3.err" >&2; fail "(c) -j 3: no body of A read"; }

# (d)
dargs=(-Q "$d/lib" SRPar -norec SRPar.A -norec SRPar.B -norec SRPar.C -norec SRPar.D)
report d "${dargs[@]}"
has d-j1 'axiom model_d SRPar.A.ax'
has d-j1 'axiom model_d SRPar.B.bax'
[ "$reads" = 0 ] || { cat "$d/d-j3.err" >&2; fail "(d) -j 3: $reads bodies read, all were checked"; }

# (e) Two builds that differ in one proof have opaque tables of the same
# layout: the library segment of the good one with the opaques segment of
# the bad one makes a .vo whose l1, of type U, has a proof of type U -> U.
gen() {
  echo 'Inductive T : Prop := I.'
  echo 'Definition U := T.'
  for i in $(seq 1 20); do
    if [ "$i" = 1 ] && [ "$1" = bad ]; then
      echo "Lemma l$i : forall x : U, U. Proof. exact (fun x => x). Qed."
    else
      echo "Lemma l$i : U. Proof. exact I. Qed."
    fi
  done
  echo 'Definition model := l2.'
}
gen good > "$d/good/Bad.v"
gen bad > "$d/bad/Bad.v"
rocq c -native-compiler no -Q "$d/good" SRBad "$d/good/Bad.v"
rocq c -native-compiler no -Q "$d/bad" SRBad "$d/bad/Bad.v"
python3 misc/vo_segments.py splice-opaques "$d/good/Bad.vo" "$d/bad/Bad.vo" "$d/spliced/Bad.vo"

echo 'bad SRBad.Bad.model -' > "$d/e.req"
run e-j1 1 -statement-report "$d/e.req" -Q "$d/spliced" SRBad -norec SRBad.Bad
r1=$R
[ "$r1" != 0 ] || { cat "$d/e-j1.err" >&2; fail "(e) -j 1 accepted the ill-typed proof"; }
run e-j3 3 -statement-report "$d/e.req" -Q "$d/spliced" SRBad -norec SRBad.Bad
[ "$R" = "$r1" ] || { cat "$d/e-j3.err" >&2; fail "(e) -j 3: exit code $R, -j 1 gave $r1"; }
for name in e-j1 e-j3; do
  if grep -q 'STATEMENT REPORT' "$d/$name.out" "$d/$name.err"; then
    cat "$d/$name.err" >&2
    fail "($name) printed a report for a refused library"
  fi
done

# (f)
report f -Q "$d/prims" SRPrim -norec SRPrim.Prims
has f-j1 'axiom int Corelib.Numbers.Cyclic.Int63.PrimInt63.int'
has f-j1 'axiom float Corelib.Floats.PrimFloat.float'
has f-j1 'axiom string Corelib.Strings.PrimString.string'
has f-j1 'axiom array Corelib.Array.PrimArray.array'

# (g)
# warned NAME: the warnings of the run NAME about the unreadable body.
warned() {
  tr -s ' \n\t' ' ' < "$d/$1.err" |
    { grep -o 'Statement report: the opaque body of SRPar\.A\.uses_ax could not be read, so it is reported as an axiom: test unreadable opaque body' || true; }
}
unreadable=SRPar.A.uses_ax
run g-j1 1 -statement-report "$d/a.req" -Q "$d/lib" SRPar -norec SRPar.A
[ "$R" = 0 ] || { cat "$d/g-j1.err" >&2; fail "(g) -j 1: exit code $R"; }
has g-j1 'axiom via SRPar.A.uses_ax'
run g-j3 3 -statement-report "$d/a.req" -Q "$d/lib" SRPar -norec SRPar.A
same g-j1 g-j3 0 "(g) -j 3"
w1=$(warned g-j1)
[ -n "$w1" ] || { cat "$d/g-j1.err" >&2; fail "(g) -j 1: no warning"; }
[ "$(warned g-j3)" = "$w1" ] || { cat "$d/g-j3.err" >&2; fail "(g) -j 3: not the warning of -j 1"; }
unreadable=

# like_d NAME WHAT: the run NAME of the fixture (d) at -j 3, whose exit code
# is $R, printed what (d) at -j 1 printed, and took every opaque body the
# report reached from the records, as (d) at -j 3 does: M = 0. Every check
# is recorded by the process that ran it, whatever the schedule, so a
# worker that stopped early or gave checks back must have its records used
# too.
like_d() {
  same d-j1 "$1" 0 "$2"
  counts "$1"
  [ "$hits" -gt 0 ] || { cat "$d/$1.err" >&2; fail "$2: no body taken from the records"; }
  [ "$reads" = 0 ] || { cat "$d/$1.err" >&2; fail "$2: $reads bodies read, all were checked"; }
}

# (h) -worker-budget takes any number of seconds from 0 up (coqchk_main.ml,
# set_worker_budget). At 0, a worker's budget has passed as soon as it has
# completed its first check, which it always completes, so it stops there
# and the main process queues the rest of its batch again
# (CheckWorkers.run_worker). The checks of (d) are many enough that the
# first batches dealt hold several each.
run h-j3 3 -worker-budget 0 -statement-report "$d/d.req" "${dargs[@]}"
like_d h-j3 "(h) -j 3 -worker-budget 0"

# (i) At "check:1" the request comes after the second check of the batch is
# started, so the worker completes that check and releases the ones after
# it (CheckWorkers.release_test_at); the main process queues them again
# when it reads the release message. A batch of one or two checks has
# nothing to give back, but the first batches dealt hold more.
ROCQCHK_WORKER_RELEASE_AT=check:1 run i-j3 3 -statement-report "$d/d.req" "${dargs[@]}"
like_d i-j3 "(i) -j 3 ROCQCHK_WORKER_RELEASE_AT=check:1"

# (j) Each run's exit code is the one of its subshell; both are waited for
# before anything is looked at.
( capture j-d 3 -statement-report "$d/d.req" "${dargs[@]}"; exit "$R" ) &
pd=$!
( capture j-c 3 -statement-report "$d/c.req" -Q "$d/lib" SRPar -norec SRPar.C; exit "$R" ) &
pc=$!
rd=0
rc=0
wait "$pd" || rd=$?
wait "$pc" || rc=$?
empty "(j) j-d and j-c"
R=$rd
like_d j-d "(j) -j 3 of (d), beside -j 3 of (c)"
R=$rc
same c-j1 j-c 0 "(j) -j 3 of (c), beside -j 3 of (d)"
counts j-c
[ "$hits" -gt 0 ] || { cat "$d/j-c.err" >&2; fail "(j) -j 3 of (c), beside -j 3 of (d): no body taken from the records"; }

# (k) Each record of K names its 200 constants by number, and the first
# record of a file gives each of them with its name, of 8 to 10 characters
# (Definition filler_<i>), so that the first record of each worker takes
# more than 1024 bytes: every worker that checks a proof of K meets the
# limit as it writes its first record, which M > 0 shows, where K at -j 3
# without the limit reads no body. Were SIGXFSZ not ignored for the writes
# of the records, it would kill the worker that wrote past the limit, and
# the run would fail where -j 1 succeeds.
kargs=(-Q "$d/big" SRBig -norec SRBig.K)
report k "${kargs[@]}"
[ "$reads" = 0 ] || { cat "$d/k-j3.err" >&2; fail "(k) -j 3: $reads bodies read, all were checked"; }
fsize=1
run kf-j1 1 -statement-report "$d/k.req" "${kargs[@]}"
same k-j1 kf-j1 0 "(k) -j 1 under ulimit -f 1"
run kf-j3 3 -statement-report "$d/k.req" "${kargs[@]}"
same kf-j1 kf-j3 0 "(k) -j 3 under ulimit -f 1"
counts kf-j3
[ "$reads" -gt 0 ] || { cat "$d/kf-j3.err" >&2; fail "(k) -j 3 under ulimit -f 1: no body read, so the records did not meet the limit"; }
fsize=

# (l) Only the main process reads the cap; every worker records as usual,
# and the main process gives up when it would keep the first segment.
COQ_TEST_SUITE_STATEMENT_REPORT_RECORDS_CAP=1 run l-j3 3 -statement-report "$d/d.req" "${dargs[@]}"
same d-j1 l-j3 0 "(l) -j 3 with the records capped at 1 byte"
counts l-j3
[ "$hits" = 0 ] || { cat "$d/l-j3.err" >&2; fail "(l) -j 3 with the records capped at 1 byte: $hits bodies taken from the records"; }
[ "$reads" -gt 0 ] || { cat "$d/l-j3.err" >&2; fail "(l) -j 3 with the records capped at 1 byte: no body read"; }

# (m) The answer and the challenge are the same A.vo, so the verdicts are
# those of A's own proofs: what they are matters less than that -j 3 gives
# the ones -j 1 gives. With the counts seam set, a run that recorded writes
# the counts; one that did not writes nothing.
mkdir "$d/chal"
cp "$d/lib/A.vo" "$d/chal/A.vo"
where=$(rocq -where)
prelude=
for p in "$where/theories/Corelib/Init/Prelude.vo" "$where/theories/Init/Prelude.vo"; do
  if [ -f "$p" ]; then prelude=$p; break; fi
done
[ -n "$prelude" ] || fail "(m): no Prelude.vo under $where"
prelude_sha=$(rocqchk -sha256 "$prelude")
chal_sha=$(rocqchk -sha256 "$d/chal/A.vo")
printf '%s\n' \
  "{\"theorems\": [{\"name\": \"SRPar.A.clean\"}, {\"name\": \"SRPar.A.via\"}]," \
  " \"tolerated_flags\": [{\"kind\": \"indices-not-mattering\", \"object\": \"Corelib.Init.Logic.eq\"}]," \
  " \"prechecked\": [{\"library\": \"Corelib.Init.Prelude\", \"sha256\": \"$prelude_sha\"}]," \
  " \"challenge_files\": [{\"path\": \"A.vo\", \"sha256\": \"$chal_sha\"}]}" > "$d/m.config"
# compared NAME J: (a) at -j J with -compare, its verdict in $d/NAME.json.
compared() {
  run "$1" "$2" -statement-report "$d/a.req" -compare "$d/m.config" -challenge "$d/chal" \
    -compare-out "$d/$1.json" -Q "$d/lib" SRPar -norec SRPar.A
}
compared m-j1 1
[ "$R" = 0 ] || { cat "$d/m-j1.err" >&2; fail "(m) -j 1: exit code $R"; }
grep -qx 'END STATEMENT REPORT' "$d/m-j1.report" \
  || { cat "$d/m-j1.err" >&2; fail "(m) -j 1 printed no whole report"; }
[ -s "$d/m-j1.json" ] || { cat "$d/m-j1.err" >&2; fail "(m) -j 1 wrote no verdict"; }
compared m-j3 3
same m-j1 m-j3 0 "(m) -j 3 with -compare"
diff -u "$d/m-j1.json" "$d/m-j3.json" > "$d/m-j3.diff" \
  || { cat "$d/m-j3.diff" >&2; fail "(m) -j 3 with -compare: its verdict differs from -j 1"; }
not_recorded m-j3 "(m) -j 3 with -compare"

# (n) Without records, -j 3 holds in the main process, besides its own
# few, at most four descriptors for each of its at most three workers,
# which 60 leaves room for; with them, one more for each, which
# ReportRecords.start counts (CheckWorkers.descriptors_for_workers). The
# counts seam is set, so a run that recorded would write the counts.
nofile=60
run n-j1 1 -statement-report "$d/d.req" "${dargs[@]}"
same d-j1 n-j1 0 "(n) -j 1 under ulimit -n 60"
run n-j3 3 -statement-report "$d/d.req" "${dargs[@]}"
same n-j1 n-j3 0 "(n) -j 3 under ulimit -n 60"
not_recorded n-j3 "(n) -j 3 under ulimit -n 60"
nofile=

# (o) No file can be made in a TMPDIR that does not exist
# (CheckWorkers.open_capture), so the workers have no files of output
# (CheckLibrary: the walk waits for the libraries to be read), and the
# records, in /dev/shm, are used as in (d).
tmp=$t/none
run o-j1 1 -statement-report "$d/d.req" "${dargs[@]}"
same d-j1 o-j1 0 "(o) -j 1 with a TMPDIR that does not exist"
run o-j3 3 -statement-report "$d/d.req" "${dargs[@]}"
like_d o-j3 "(o) -j 3 with a TMPDIR that does not exist"
[ ! -e "$tmp" ] || fail "(o) -j 3 made its TMPDIR"
tmp=$t
empty "(o)"

# (p) -j 3 records where the limit on open files less the descriptors
# open is at least 80 (CheckWorkers.descriptors_for_workers). Under a limit
# of 120 that holds where rocqchk starts with at most 40 open, as with its
# standard input, output and error and the few that the test's runner may
# leave open; with 60 more, on /dev/null, it does not, though 120 is above
# 80. Without records, 120 less those 60 still leaves room for all that
# -j 3 opens, as 60 does in (n).
nofile=120
run p-j3 3 -statement-report "$d/d.req" "${dargs[@]}"
like_d p-j3 "(p) -j 3 under ulimit -n 120"
extra=60
run pe-j3 3 -statement-report "$d/d.req" "${dargs[@]}"
same d-j1 pe-j3 0 "(p) -j 3 under ulimit -n 120 with 60 descriptors open"
not_recorded pe-j3 "(p) -j 3 under ulimit -n 120 with 60 descriptors open"
extra=0
nofile=

# (q) The files of the workers' output go to $s, on the file system of
# /dev/shm, which the records would then share with them
# (ReportRecords.start).
s=$(mktemp -d /dev/shm/srpar.XXXXXX)
tmp=$s
run q-j3 3 -statement-report "$d/d.req" "${dargs[@]}"
same d-j1 q-j3 0 "(q) -j 3 with its TMPDIR in /dev/shm"
not_recorded q-j3 "(q) -j 3 with its TMPDIR in /dev/shm"
tmp=$t

# (r) coqchk_main.ml does not start the recorder with -merge-inductives
# (Indmerge.enabled), as it does not with -compare. The counts seam is set,
# so a run that recorded would write the counts.
cp "$d/d.req" "$d/r.req"
baseline r -merge-inductives "${dargs[@]}"
run r-j3 3 -statement-report "$d/r.req" -merge-inductives "${dargs[@]}"
same r-j1 r-j3 0 "(r) -j 3 with -merge-inductives"
not_recorded r-j3 "(r) -j 3 with -merge-inductives"

exit 0
