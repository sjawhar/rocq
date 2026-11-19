#!/usr/bin/env bash
# rocqchk -bytecode-compiler yes runs the VM casts of a proof again, with
# bytecode it compiles itself (misc/rocqchk_vm_bytecode.sh), in the
# environment of the libraries it loads, not of those the proof was
# compiled against. L proves f 100 = 10000 with a VM cast, compiled against
# an F whose f is n * n. F is then compiled again with f n = n * n + 1, and
# L is forged to record the digest of that F as its dependency's (the
# client command of misc/rocqchk_forge_lib.ml, which writes the digest in
# L's summary and in its compiled library), so that rocqchk loads L with the
# new F, where the cast is false. At -j 16 the check of L's opaque proof
# runs in a worker process, and the worker must refuse it as -j 1 does, and
# say which proof it was checking.
#
#  (a) The honest F and L, at -j 16, as a grader runs rocqchk (-o
#      -bytecode-compiler yes, each library named with -norec): accepted,
#      exit code 0, with a summary.
#  (b) The new F and the forged L, at -j 16: refused with exit code 129, the
#      code of a kernel error, which rocqchk has no handler for
#      (CErrors.exit_code). The first error printed is the worker's: "Type
#      error: ActualType" (the failed cast, Typeops.check_cast), then the
#      line "while checking the opaque proof of VMForge.L.f100."
#      (Coqchk_main.explain_exn of CheckWorkers.CheckError). A second error
#      follows, from the main process: "Worker process PID exited with code
#      129 while checking ...". It names the worker's batch, so it is not
#      compared, as in misc/rocqchk_cook.sh (d).
#  (c) The same at -j 1: exit code 129, and the first error of (b) without
#      the worker's line.
set -eu
: "${BIN:=$(dirname "$(command -v rocq)")/}"
export PATH="$BIN:$PATH"
unset ROCQCHK_WORKER_RELEASE_AT

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
mkdir "$d/honest" "$d/forged"

cat > "$d/honest/F.v" <<'EOF'
Definition f (n : nat) : nat := n * n.
EOF

# The cast is not run by the tactic, only by the kernel: at Qed, and in
# rocqchk.
cat > "$d/honest/L.v" <<'EOF'
From VMForge Require Import F.
Lemma f100 : f 100 = 10000.
Proof. vm_cast_no_check (@eq_refl nat 10000). Qed.
EOF

cat > "$d/forged/F.v" <<'EOF'
Definition f (n : nat) : nat := n * n + 1.
EOF

rocq c -native-compiler no -Q "$d/honest" VMForge "$d/honest/F.v"
rocq c -native-compiler no -Q "$d/honest" VMForge "$d/honest/L.v"
rocq c -native-compiler no -Q "$d/forged" VMForge "$d/forged/F.v"

fail() { >&2 echo "FAILURE: $*"; exit 1; }

# The forger: the client command of misc/rocqchk_forge_lib.ml, loaded as
# the forge.ml files of the other forge tests load it. ocaml runs from
# test-suite/, where the ./ path is found.
cat > "$d/forge.ml" <<'EOF'
#use "./misc/rocqchk_forge_lib.ml";;

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [ "client"; src; lib; lib_dp; dst ] -> client ~src ~lib ~lib_dp ~dst
  | _ ->
    prerr_endline "usage: ocaml forge.ml client CLIENT.vo LIB.vo LIB_DIRPATH OUT.vo";
    exit 2
EOF
# L as compiled against the honest F, recording the new F's digest.
ocaml "$d/forge.ml" client "$d/honest/L.vo" "$d/forged/F.vo" VMForge.F "$d/forged/L.vo" \
  > "$d/forge.log" 2>&1 || { cat "$d/forge.log" >&2; fail "the forger failed"; }

# check NAME ARGS...: rocqchk as a grader runs it, with its standard output
# and error in $d/NAME.log. Exit code in $R.
R=0
check() {
  local name=$1; shift
  R=0
  rocqchk -o -bytecode-compiler yes "$@" > "$d/$name.log" 2>&1 || R=$?
}

# The first error block of a log: from its first "Fatal Error" line to the
# next one.
errblock() {
  awk '/^Fatal Error/ { n++ } n == 1' "$d/$1.log"
}

HONEST=(-Q "$d/honest" VMForge -norec VMForge.F -norec VMForge.L)
FORGED=(-Q "$d/forged" VMForge -norec VMForge.F -norec VMForge.L)

# (a) The honest pair.
check honest-j16 -j 16 -worker-budget 20 "${HONEST[@]}"
if [ "$R" != 0 ] || ! grep -q 'CONTEXT SUMMARY' "$d/honest-j16.log"; then
  cat "$d/honest-j16.log" >&2
  fail "(a) the honest F and L at -j 16: exit code $R; expected 0 and a summary"
fi

# (b) The forgery at -j 16, checked by a worker.
check forged-j16 -j 16 -worker-budget 20 "${FORGED[@]}"
errblock forged-j16 > "$d/err16"
if [ "$R" != 129 ] || ! grep -q 'Type error: ActualType' "$d/err16" \
   || ! grep -qx ' *while checking the opaque proof of VMForge\.L\.f100\.' "$d/err16"; then
  cat "$d/forged-j16.log" >&2
  fail "(b) the forged L at -j 16: exit code $R; expected 129, with a first error" \
    "\"Type error: ActualType\" while checking the opaque proof of VMForge.L.f100"
fi

# (c) The forgery at -j 1.
check forged-j1 -j 1 "${FORGED[@]}"
errblock forged-j1 > "$d/err1"
if [ "$R" != 129 ] || ! grep -q 'Type error: ActualType' "$d/err1" \
   || grep -q 'while checking' "$d/forged-j1.log"; then
  cat "$d/forged-j1.log" >&2
  fail "(c) the forged L at -j 1: exit code $R; expected 129, with a first error" \
    "\"Type error: ActualType\" and no worker line"
fi
grep -v 'while checking the opaque proof of' "$d/err16" > "$d/err16.1"
diff -u "$d/err1" "$d/err16.1" > "$d/err.diff" \
  || { cat "$d/err.diff" >&2; fail "(c) the first error of -j 16 is not the one of -j 1 with the worker's line"; }

exit 0
