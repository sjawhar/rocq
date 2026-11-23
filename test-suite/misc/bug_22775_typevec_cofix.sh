#!/usr/bin/env bash

# A mutual cofixpoint of 4200 functions has a vector of types of 4200 words,
# more than the minor heap that OCAMLRUNPARAM=s=1 gives (4096 words on OCaml
# 4.14, less on OCaml 5). `Eval vm_compute in c` reads the cofixpoint back,
# which copies that vector in rocq_tcode_array (kernel/byterun/rocq_values.c).
# One constant holds the block (a `CoFixpoint` command would make 4200
# constants that each hold it).

set -e

export PATH=$BIN:$PATH
export OCAMLRUNPARAM=s=1

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT

N=4200

{
  echo "CoInductive stream := Cons : nat -> stream -> stream."
  printf 'Definition c := cofix c1 : stream := Cons O c2\n'
  for i in $(seq 2 $N); do
    j=$(( i % N + 1 ))
    printf 'with c%d : stream := Cons O c%d\n' "$i" "$j"
  done
  printf 'for c1.\n'
  echo "Definition t := Eval vm_compute in c."
} > "$d/bug_22775_typevec_cofix.v"

# Without the fix the allocation loops; a CPU-time limit makes that a failure.
(ulimit -t 900; ${coqc#"$BIN"} "$d/bug_22775_typevec_cofix.v")
