#!/usr/bin/env bash
# rocqchk -j N -statement-report: each process that checks an opaque body
# records the objects of that body, and the report takes them instead of
# reading the body again (checker/reportRecords.ml). The report must be the
# one of -j 1, line for line, with the same exit code, and the directory of
# the records must be gone after every run, whatever its end.
#
#  (a) A.v, a plain library: an axiom that opaque proofs use through other
#      opaque proofs;
#  (b) B.v: opaque proofs in a section. Their cooking information abstracts
#      a hypothesis whose type names an opaque proof of A, and a Let whose
#      body is an axiom, which only the cooked body names;
#  (c) C.v: opaque proofs reached through a functor application and an
#      Include, which are substituted copies that the report reads as it
#      does without records, and through a signature that hides a proof in
#      its module's implementation;
#  (d) D.v with A, B and C, all checked in one run.
#
# For each, the report of -j 3, where two workers check the opaque bodies,
# and its exit code are those of -j 1; and with -d checker-workers the
# debug line "statement report: H opaque bodies from records, M read" has
# H > 0, so the records were used. In (d), where every library is checked,
# M > 0 too: the substituted copies of (c) are read. Every run has TMPDIR
# set to a directory of its own, which must hold no rocqchk_refs_*
# directory afterwards.
#
#  (e) Bad.v, a library whose first opaque proof is ill-typed, made by the
#      splice of misc/rocqchk_parallel.sh: rocqchk refuses it at -j 1 and at
#      -j 3 with the same exit code, prints no report, and leaves no
#      directory.
set -eu
: "${BIN:=$(dirname "$(command -v rocq)")/}"
export PATH="$BIN:$PATH"
unset ROCQCHK_WORKER_RELEASE_AT ROCQCHK_OPAQUE_AT ROCQCHK_INTERN_AT ROCQCHK_CHECK_AT
unset COQ_TEST_SUITE_STATEMENT_REPORT_UNREADABLE COQ_TEST_SUITE_STATEMENT_REPORT_FAILURE

d=$(mktemp -d)
t=$(mktemp -d)
trap 'rm -rf "$d" "$t"' EXIT
mkdir "$d/lib" "$d/good" "$d/bad" "$d/spliced"

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

fail() { >&2 echo "FAILURE: $*"; exit 1; }

# run NAME J ARGS...: rocqchk -silent -j J ARGS with TMPDIR set to $t, its
# standard output in $d/NAME.out, its standard error, where the report is,
# in $d/NAME.err, and the report's lines in $d/NAME.report. Exit code in $R.
# No rocqchk_refs_* directory may be left in $t.
R=0
run() {
  local name=$1 j=$2 left
  shift 2
  R=0
  TMPDIR="$t" rocqchk -silent -j "$j" "$@" > "$d/$name.out" 2> "$d/$name.err" || R=$?
  sed -n '/^STATEMENT REPORT$/,/^END STATEMENT REPORT$/p' "$d/$name.err" > "$d/$name.report"
  left=$(find "$t" -mindepth 1 -maxdepth 1 -name 'rocqchk_refs_*')
  [ -z "$left" ] || fail "$name left $left"
}

# counts NAME: "H M" from the last debug line "statement report: H opaque
# bodies from records, M read" of the run NAME, which can be wrapped over
# several lines; nothing if there is none.
counts() {
  tr -s ' \n\t' ' ' < "$d/$1.err" |
    grep -o 'statement report: [0-9]* opaque bodies from records, [0-9]* read' |
    tail -n 1 | awk '{ print $3, $8 }'
}

# has NAME LINE: the report of the run NAME has the line LINE.
has() {
  grep -qxF "$2" "$d/$1.report" || { cat "$d/$1.err" >&2; fail "$1: no line \"$2\""; }
}

# same NAME1 NAME2 R1 WHAT: the run NAME2, whose exit code is $R, has the
# report of the run NAME1, and its exit code R1.
same() {
  local r1=$3
  diff -u "$d/$1.report" "$d/$2.report" > "$d/$2.diff" \
    || { cat "$d/$2.diff" >&2; fail "$4: the report differs from -j 1"; }
  [ "$R" = "$r1" ] || { cat "$d/$2.err" >&2; fail "$4: exit code $R, -j 1 gave $r1"; }
}

# report F ARGS...: the fixture F, at -j 1, at -j 3, and at -j 3 with the
# debug line. Sets $hits and $reads from the debug line.
report() {
  local f=$1 r1 c
  shift
  run "$f-j1" 1 -statement-report "$d/$f.req" -Q "$d/lib" SRPar "$@"
  r1=$R
  [ "$r1" = 0 ] || { cat "$d/$f-j1.err" >&2; fail "($f) -j 1: exit code $r1"; }
  grep -qx 'END STATEMENT REPORT' "$d/$f-j1.report" \
    || { cat "$d/$f-j1.err" >&2; fail "($f) -j 1 printed no whole report"; }
  run "$f-j3" 3 -statement-report "$d/$f.req" -Q "$d/lib" SRPar "$@"
  same "$f-j1" "$f-j3" "$r1" "($f) -j 3"
  run "$f-d3" 3 -d checker-workers -statement-report "$d/$f.req" -Q "$d/lib" SRPar "$@"
  same "$f-j1" "$f-d3" "$r1" "($f) -j 3 -d checker-workers"
  c=$(counts "$f-d3")
  [ -n "$c" ] || { cat "$d/$f-d3.err" >&2; fail "($f) -j 3: no debug line of the report"; }
  read -r hits reads <<< "$c"
  [ "$hits" -gt 0 ] || { cat "$d/$f-d3.err" >&2; fail "($f) -j 3: no body taken from the records"; }
}

# (a)
report a -norec SRPar.A
has a-j1 'axiom via SRPar.A.ax'
has a-j1 'statement typed SRPar.A.uses_ax SRPar.A.via match 1 1'

# (b): A is loaded without being checked, so its bodies are read.
report b -norec SRPar.B
has b-j1 'axiom sec_h SRPar.A.ax'
has b-j1 'axiom sec_let SRPar.B.bax'
has b-j1 'axiom use_sec SRPar.B.bax'

# (c)
report c -norec SRPar.C
has c-j1 'axiom fm SRPar.C.mp_ax'
has c-j1 'axiom fm2 SRPar.C.cax'
has c-j1 'axiom h SRPar.C.cax'
has c-j1 'axiom n SRPar.C.cax'
has c-j1 'axiom plain_c SRPar.A.ax'

# (d)
report d -norec SRPar.A -norec SRPar.B -norec SRPar.C -norec SRPar.D
has d-j1 'axiom model_d SRPar.A.ax'
has d-j1 'axiom model_d SRPar.B.bax'
[ "$reads" -gt 0 ] || { cat "$d/d-d3.err" >&2; fail "(d) -j 3: no body read"; }

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

# Same splice as misc/rocqchk_parallel.sh.
python3 - "$d" <<'PY'
import sys, hashlib, struct
d = sys.argv[1]
MAGIC = 0x436F7121  # "Coq!"; all ints big-endian, layout per lib/objFile.ml
def parse(p):
    b = open(p, "rb").read()
    magic, ver = struct.unpack_from(">II", b, 0)
    assert magic == MAGIC, "bad magic"
    (sp,) = struct.unpack_from(">Q", b, 8)
    off = sp
    (n,) = struct.unpack_from(">I", b, off); off += 4
    segs = {}
    for _ in range(n):
        (nl,) = struct.unpack_from(">I", b, off); off += 4
        name = b[off:off+nl].decode(); off += nl
        pos, ln = struct.unpack_from(">QQ", b, off); off += 16
        h = b[off:off+16]; off += 16
        data = b[pos:pos+ln]
        assert hashlib.md5(data).digest() == h, name + ": bad segment MD5"
        segs[name] = data
    return ver, segs
def write(p, ver, by):
    out = bytearray()
    out += struct.pack(">II", MAGIC, ver)
    out += struct.pack(">Q", 0)
    summ = []
    for name in sorted(by):
        data = by[name]; pos = len(out); out += data
        h = hashlib.md5(data).digest(); out += h
        summ.append((name, pos, len(data), h))
    sp = len(out)
    out += struct.pack(">I", len(summ))
    for name, pos, ln, h in summ:
        nb = name.encode()
        out += struct.pack(">I", len(nb)); out += nb
        out += struct.pack(">QQ", pos, ln); out += h
    struct.pack_into(">Q", out, 8, sp)
    open(p, "wb").write(out)
vg, sg = parse(d + "/good/Bad.vo")
vb, sb = parse(d + "/bad/Bad.vo")
assert vg == vb, "vo_version mismatch"
assert sg["opaques"] != sb["opaques"], "opaques should differ"
spliced = dict(sg)
spliced["opaques"] = sb["opaques"]
write(d + "/spliced/Bad.vo", vg, spliced)
PY

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

exit 0
