#!/usr/bin/env bash

# A mutual fixpoint of 4200 functions has a vector of types of 4200 words,
# more than the minor heap that OCAMLRUNPARAM=s=1 gives (4096 words on OCaml
# 4.14, less on OCaml 5). `Eval vm_compute in f` reads the fixpoint back, which
# copies that vector in rocq_tcode_array (kernel/byterun/rocq_values.c). One
# constant holds the block (a `Fixpoint` command would make 4200 constants that
# each hold it).

set -e

export PATH=$BIN:$PATH
export OCAMLRUNPARAM=s=1

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT

N=4200

{
  printf 'Definition f := fix f1 (n : nat) : nat := match n with O => O | S m => f2 m end\n'
  for i in $(seq 2 $N); do
    j=$(( i % N + 1 ))
    printf 'with f%d (n : nat) : nat := match n with O => O | S m => f%d m end\n' "$i" "$j"
  done
  printf 'for f1.\n'
  echo "Definition t := Eval vm_compute in f."
} > "$d/bug_22775_typevec_fix.v"

# Without the fix the allocation loops; a CPU-time limit makes that a failure.
(ulimit -t 900; ${coqc#"$BIN"} "$d/bug_22775_typevec_fix.v")
