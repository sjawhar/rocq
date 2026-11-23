#!/usr/bin/env bash

# A mutual fixpoint of 4200 functions has a vector of types of 4200 words,
# more than the minor heap that OCAMLRUNPARAM=s=1 gives (4096 words on OCaml
# 4.14, less on OCaml 5). `Eval vm_compute in f` reads the fixpoint back, which
# copies that vector in rocq_tcode_array (kernel/byterun/rocq_values.c). One
# constant holds the block (a `Fixpoint` command would make 4200 constants that
# each hold it). Each function recurses on itself alone, and the functions
# have two types, nat -> nat and nat -> bool, so a wrong vector of types gives
# an ill-typed read-back. The read-back must be f itself, and VM conversion
# must refuse a fixpoint that differs from f only in its last function.
# A first run defines the two fixpoints with the default minor heap, where
# that costs less; only the read-back and the checks run with s=1.

set -e

export PATH=$BIN:$PATH

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT

N=4200

# fixdef NAME LAST: the fixpoint NAME of N functions; f_i has type nat -> nat
# for odd i and nat -> bool for even i, and the last function (even) returns
# LAST on O.
fixdef() {
  printf 'Definition %s := fix f1 (n : nat) : nat := match n with O => O | S m => f1 m end\n' "$1"
  for i in $(seq 2 $N); do
    if [ $(( i % 2 )) -eq 0 ]; then
      if [ "$i" -eq "$N" ]; then z=$2; else z=true; fi
      printf 'with f%d (n : nat) : bool := match n with O => %s | S m => f%d m end\n' "$i" "$z" "$i"
    else
      printf 'with f%d (n : nat) : nat := match n with O => O | S m => f%d m end\n' "$i" "$i"
    fi
  done
  printf 'for f1.\n'
}

{
  fixdef f true
  fixdef f\' false
} > "$d/defs.v"

{
  echo "Require Import T.defs."
  echo "Definition t := Eval vm_compute in f."
  echo "Example t_ok : t = f := eq_refl."
  echo "Fail Check (eq_refl f <: f = f')."
} > "$d/bug_22775_typevec_fix.v"

# A CPU-time limit bounds each run. Without the fix the read-back in the second
# run loops, and the limit makes that a failure.
(ulimit -t 900; unset OCAMLRUNPARAM
 ${coqc#"$BIN"} -native-compiler no -R "$d" T "$d/defs.v")
(ulimit -t 900; export OCAMLRUNPARAM=s=1
 ${coqc#"$BIN"} -native-compiler no -R "$d" T "$d/bug_22775_typevec_fix.v")
