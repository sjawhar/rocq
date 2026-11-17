#!/usr/bin/env bash
# rocqchk must refuse libraries whose universe constraints are inconsistent
# only when taken together. Base declares two universes, u and v. X1 says
# u < v and X2 says v < u. No file requires both X1 and X2, so each file
# compiles, and each of X1 and X2 is consistent with everything it requires.
# Only the universe graph of a run that loads both holds both constraints.
# rocqchk keeps one graph for the whole run: the main process adds the
# constraints of each library to it when it loads that library
# (Safe_checking.env_of_library, push_context_set ~strict:true), so the
# second of X1 and X2 makes the run fail, at any -j. A checker that
# divided the libraries among processes, each with a graph of its own
# share only ({Base, S, X1} in one, {Base, T, X2} in the other), would
# accept each share, and so the run. S and T give the shares more than
# universes: S declares a module M sealed by a signature, with a field x
# and an opaque proof that uses x; T requires S and uses M.x.
#
#  (a) The five libraries, each named with -norec, as a grader runs
#      rocqchk (-o -bytecode-compiler yes), at -j 1 and at -j 16 (with
#      -worker-budget 20): rocqchk refuses them with "Universe
#      inconsistency" and exit code 129, the code of a kernel error, which
#      rocqchk has no handler for (CErrors.exit_code), and prints no
#      summary.
#  (b) As controls, {Base, S, X1} and {Base, T, X2} (T loads S, which it
#      requires), checked the same way at -j 1 and at -j 16: each is
#      accepted, with exit code 0 and a summary. So the refusal in (a)
#      comes from X1 and X2 meeting in one run, and from nothing else.
set -eu
: "${BIN:=$(dirname "$(command -v rocq)")/}"
export PATH="$BIN:$PATH"
unset ROCQCHK_WORKER_RELEASE_AT

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT

cat > "$d/Base.v" <<'EOF'
(* Two global universes, with no constraint between them. *)
Universes u v.
EOF

cat > "$d/X1.v" <<'EOF'
From USplit Require Base.
Constraint Base.u < Base.v.
EOF

cat > "$d/X2.v" <<'EOF'
From USplit Require Base.
Constraint Base.v < Base.u.
EOF

cat > "$d/S.v" <<'EOF'
Module Type ST.
  Parameter x : nat.
  Axiom x_add_0 : x + 0 = x.
End ST.

(* x_add_0 is declared without a body and proved with Qed. *)
Module M : ST.
  Definition x : nat := 7.
  Lemma x_add_0 : x + 0 = x. Proof. reflexivity. Qed.
End M.
EOF

cat > "$d/T.v" <<'EOF'
From USplit Require Import S.
Definition y : nat := M.x + 1.
Lemma y_eq : y = M.x + 1. Proof. reflexivity. Qed.
EOF

# One file at a time, so X1 and X2 never meet in a compile.
for lib in Base X1 X2 S T; do
  rocq c -native-compiler no -Q "$d" USplit "$d/$lib.v"
done

fail() { >&2 echo "FAILURE: $*"; exit 1; }

# check NAME ARGS...: rocqchk as a grader runs it, on the libraries of $d,
# with its standard output and error in $d/NAME.log. Exit code in $R.
R=0
check() {
  local name=$1; shift
  R=0
  rocqchk -o -bytecode-compiler yes -Q "$d" USplit "$@" > "$d/$name.log" 2>&1 || R=$?
}

# refused NAME WHAT: the run NAME exited with 129, printed "Universe
# inconsistency", and printed no summary.
refused() {
  if [ "$R" != 129 ] || ! grep -q 'Universe inconsistency' "$d/$1.log" \
     || grep -q 'CONTEXT SUMMARY' "$d/$1.log"; then
    cat "$d/$1.log" >&2
    fail "$2: exit code $R; expected 129, \"Universe inconsistency\" and no summary"
  fi
}

# accepted NAME WHAT: the run NAME exited with 0 and printed its summary.
accepted() {
  if [ "$R" != 0 ] || ! grep -q 'CONTEXT SUMMARY' "$d/$1.log"; then
    cat "$d/$1.log" >&2
    fail "$2: exit code $R; expected 0 and a summary"
  fi
}

ALL=(-norec USplit.Base -norec USplit.X1 -norec USplit.X2 -norec USplit.S -norec USplit.T)
LEFT=(-norec USplit.Base -norec USplit.S -norec USplit.X1)
RIGHT=(-norec USplit.Base -norec USplit.T -norec USplit.X2)

for j in 1 16; do
  if [ "$j" = 1 ]; then par=(-j 1); else par=(-j 16 -worker-budget 20); fi
  check "all-j$j" "${par[@]}" "${ALL[@]}"
  refused "all-j$j" "(a) -j $j, Base X1 X2 S T"
  check "left-j$j" "${par[@]}" "${LEFT[@]}"
  accepted "left-j$j" "(b) -j $j, Base S X1"
  check "right-j$j" "${par[@]}" "${RIGHT[@]}"
  accepted "right-j$j" "(b) -j $j, Base T X2"
done

exit 0
