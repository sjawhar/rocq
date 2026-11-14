#!/usr/bin/env bash

# The -o summary reads a functor application through its functor's body
# (checker/mod_impl.ml), and stops at an application read inside 64 nested
# applications, or after 100000 applications. At a stop it has not read the
# body that declares the application's axioms, and the application's type
# need not name them, so rocqchk -o must refuse to print a summary, while
# rocqchk without -o accepts the library. The four libraries below are
# honest: coqc writes them from their source. Each is checked as the BET
# grader checks a library, with -o -bytecode-compiler yes, and with
# rocqchk's default options, neither flag: the refusal comes from -o alone.
#
# Deep.v: F0's body declares the axiom hidden, each Fi (i = 1..64) applies
# F(i-1) to its parameter in its module N, and R := F64 A, so R.N...N with
# 64 times N is F0's body. The walk stops there, inside 64 applications.
# Each result type is the empty E, so no type names hidden. The control,
# Short.v, is the same chain one shorter, F0..F63 and R := F63 A: it is read
# to its end and lists R.N...N.hidden, with 63 times N.
#
# Wide.v: each Fi (i = 1..5) applies F(i-1) in ten modules N0..N9, and
# R := F5 A holds 111111 applications.
#
# Inner.v, a control: the functor K declared in G's body is declared at G.K
# in every application of G. Z := S2.K B is K's body with Y standing for
# S1, Z.Q := S1.K B is K's body again, bound to B, with Y standing for A,
# and Z.Q.Q := A.K B holds the axiom a. The walk reads all three, and lists
# Z.Q.Q.a.
set -eu

. misc/rocqchk_summary_common.bash

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT

prelude() {
  echo 'Inductive False : Prop := .'
  echo 'Module Type E. End E.'
  echo 'Module A : E. End A.'
  echo 'Module F0 (X : E) : E. Axiom hidden : False. End F0.'
}

# chain <n>: F0 .. F<n>, each applying the one before, and R := F<n> A.
chain() {
  prelude
  for i in $(seq 1 "$1"); do
    echo "Module F$i (X : E) : E. Module N := F$((i - 1)) X. End F$i."
  done
  echo "Module R := F$1 A."
}

chain 64 > "$d/Deep.v"
chain 63 > "$d/Short.v"
{
  prelude
  for i in 1 2 3 4 5; do
    printf 'Module F%d (X : E) : E.' "$i"
    for j in 0 1 2 3 4 5 6 7 8 9; do printf ' Module N%d := F%d X.' "$j" "$((i - 1))"; done
    printf ' End F%d.\n' "$i"
  done
  echo 'Module R := F5 A.'
} > "$d/Wide.v"
cat > "$d/Inner.v" <<'EOF'
Inductive False : Prop := .
Module Type E0. End E0.
Module B. End B.
Module Type E. Declare Module K (X : E0) : E0. End E.
Module A. Module K (X : E0). Axiom a : False. End K. End A.
Module G (Y : E). Module K (X : E0). Module Q := Y.K X. End K. End G.
Module S1 := G A.
Module S2 := G S1.
Module Z := S2.K B.
EOF

for lib in Deep Short Wide Inner; do
  $coqc -noinit -Q "$d" Bound "$d/$lib.v"
  R=0
  timeout 120 "$BIN"rocqchk -silent -Q "$d" Bound -norec "Bound.$lib" > "$d/$lib-check.log" 2>&1 || R=$?
  if [ "$R" != 0 ]; then
    echo "rocqchk without -o exited with $R on $lib"
    cat "$d/$lib-check.log"
    exit 1
  fi
done

# lists <library> <name>: rocqchk -o accepts the library and its Axioms
# section names exactly <name>.
lists() {
  local R=0 listed
  timeout 120 "$BIN"rocqchk -silent -o -bytecode-compiler yes -Q "$d" Bound -norec "Bound.$1" \
    > "$d/$1.log" 2>&1 || R=$?
  listed=$(section 'Axioms' "$d/$1.log" | sed -n 's/^    //p')
  if [ "$R" != 0 ] || [ "$listed" != "$2" ]; then
    echo "rocqchk -o exited with $R on $1, or did not list exactly $2"
    cat "$d/$1.log"
    exit 1
  fi
}

n64=$(printf '.N%.0s' $(seq 64))
expected="the walk of the module implementations stopped at the application Bound.Deep.R$n64 := Bound.Deep.F0 Bound.Deep.A, which is read inside 64 nested applications, the most it reads."
got=$(refusal "$d/deep.log" -bytecode-compiler yes -Q "$d" Bound -norec Bound.Deep)
if [ "$got" != "$expected" ]; then
  echo "rocqchk -o refused Deep with another error"
  cat "$d/deep.log"
  exit 1
fi

lists Short "Bound.Short.R$(printf '.N%.0s' $(seq 63)).hidden"

got=$(refusal "$d/wide.log" -bytecode-compiler yes -Q "$d" Bound -norec Bound.Wide)
if ! printf '%s\n' "$got" | grep -q -x -E 'the walk of the module implementations stopped at the application Bound\.Wide\.R(\.N[0-9])+ := Bound\.Wide\.F[0-4] Bound\.Wide\.A, after 100000 applications, the most it reads for one summary\.'; then
  echo "rocqchk -o refused Wide with another error"
  cat "$d/wide.log"
  exit 1
fi

lists Inner "Bound.Inner.Z.Q.Q.a"
