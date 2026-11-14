#!/usr/bin/env bash

# rocq#22760 over a merged type.
#
# For a constructor with an extended tag (the 245th non-constant constructor
# of its type and later with OCaml 4.14, the 243rd and later with OCaml 5),
# the VM's symbolic branches give the constructor's arguments the levels just
# below the branch's own binders (Vmvalues.branch_arg;
# test-suite/bugs/bug_22760.v). One level too high, the
# last argument would be the first variable bound in the branch's body, the
# VM's conversion would accept f1 = f2 in Bad.v for two functions that
# differ, and its bad : False would compile.
#
# merge_inductives_vm_agree shows VM-on and VM-off giving the same verdict
# on every test of this family. This file adds a type whose constructors take
# that extended-tag path, merged from two libraries.
#
# What is asserted: the option neither hides a VM verdict nor widens one.
# With the option, after the merge of the two copies of Big, and without it,
# coqc refuses Bad.v at its VM cast of f1 = f2. Good.v, the same VM cast of a
# true equation over the same merged type and the proof of True that Bad.v's
# match builds from it, compiles with the option, and a check with the VM on
# and one with the VM off accept it, with the option and without it -- the
# same four verdicts.
#
# So coqc writes no Bad.vo here. That rocqchk refuses a Bad.vo written by a
# coqc that accepts the cast is the job of the forge row
# dev/ci/forge/rocq-22760.
set -eu

. misc/merge_inductives_common.bash

mi_setup misc/merge_inductives_vm_22760

# -native-compiler no is not optional here: OCaml refuses more than 246
# non-constant constructors, so an install with the native compiler on by
# default cannot compile a 250-constructor inductive at all. Upstream's own
# copy of this reproducer is named d760_issue22760_nonative.v for the same
# reason. Without the flag this test passes only where native happens to be
# off, which is how it reached the branch.
mi_coqc Spec -native-compiler no -merge-inductives
mi_coqc Agent -native-compiler no -merge-inductives

# refused_at_cast: the refusal in $d/last.log is the one of Bad.v's VM cast,
# the definition of yes.
refused_at_cast () {
  mi_says '"f1 = f1" while it is expected to have type' "the VM cast of f1 = f2"
}
mi_coqc_fails Bad -native-compiler no -merge-inductives-verbose
# Without this the file could stop being about a merged type and nothing
# here would notice.
mi_says 'Merged inductive' "a merge of the two Big copies"
refused_at_cast
mi_coqc_fails Bad -native-compiler no
refused_at_cast

mi_coqc Good -native-compiler no -merge-inductives-verbose
mi_says 'Merged inductive' "a merge of the two Big copies"

verdict () {
  local want=$1; shift
  set +e
  "$BIN"rocqchk -silent -R "$d" $mi_root "$@" > "$d/last.log" 2>&1
  local got=$?
  set -e
  [ "$got" = "$want" ] || mi_fail "rocqchk $* gave $got, expected $want"
  mi_no_anomaly "rocqchk $*"
}

for opt in "" "-merge-inductives"; do
  verdict 0 $opt -bytecode-compiler yes "$mi_root.Good"
  verdict 0 $opt -bytecode-compiler no  "$mi_root.Good"
done
