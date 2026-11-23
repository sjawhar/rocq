#!/usr/bin/env bash

# A mutual cofixpoint of 4200 functions has a vector of types of 4200 words,
# more than the minor heap that OCAMLRUNPARAM=s=1 gives (4096 words on OCaml
# 4.14, less on OCaml 5). `Eval vm_compute in c` reads the cofixpoint back,
# which copies that vector in rocq_tcode_array (kernel/byterun/rocq_values.c).
# One constant holds the block (a `CoFixpoint` command would make 4200
# constants that each hold it). The functions have two types, s true and
# s false, so a wrong vector of types gives an ill-typed read-back. The
# read-back must be c itself, and VM conversion must refuse a cofixpoint that
# differs from c only in its last function.
# A first run defines the two cofixpoints with the default minor heap, where
# that costs less; only the read-back and the checks run with s=1.

set -e

export PATH=$BIN:$PATH

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT

N=4200

# cofixdef NAME LAST: the cofixpoint NAME of N functions; c_i has type s true
# for odd i and s false for even i, and the last function (even) holds LAST.
cofixdef() {
  printf 'Definition %s := cofix c1 : s true := C true O c2\n' "$1"
  for i in $(seq 2 $N); do
    j=$(( i % N + 1 ))
    if [ "$i" -eq "$N" ]; then z=$2; else z=O; fi
    if [ $(( i % 2 )) -eq 0 ]; then b=false; else b=true; fi
    printf 'with c%d : s %s := C %s %s c%d\n' "$i" "$b" "$b" "$z" "$j"
  done
  printf 'for c1.\n'
}

{
  echo "CoInductive s : bool -> Type := C : forall b, nat -> s (negb b) -> s b."
  cofixdef c O
  cofixdef c\' '(S O)'
} > "$d/defs.v"

{
  echo "Require Import T.defs."
  echo "Definition t := Eval vm_compute in c."
  echo "Example t_ok : t = c := eq_refl."
  echo "Fail Check (eq_refl c <: c = c')."
} > "$d/bug_22775_typevec_cofix.v"

# A CPU-time limit bounds each run. Without the fix the read-back in the second
# run loops, and the limit makes that a failure.
(ulimit -t 900; unset OCAMLRUNPARAM
 ${coqc#"$BIN"} -native-compiler no -R "$d" T "$d/defs.v")
(ulimit -t 900; export OCAMLRUNPARAM=s=1
 ${coqc#"$BIN"} -native-compiler no -R "$d" T "$d/bug_22775_typevec_cofix.v")
