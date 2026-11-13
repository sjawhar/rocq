#!/usr/bin/env bash

# rocqchk must refuse a structure that gives one label to two fields in one
# of the two namespaces of coqc: the constants, the rewrite rule blocks and
# the types and constructors of inductive blocks; and the modules and
# module types. The environment keeps the last field with a label, so the
# second field replaces the first, which the fields between them were
# checked against. In each case of repeated-label/, forge.ml forges the
# library, and relinks the client to the forged library:
# - axiom: Axiom ax : False, proof : False := ax and twin : unit := tt,
#   with twin labelled ax. No constant is left without a body, and the
#   client proves False with proof;
# - registered: int : Set := Empty_set, zero : int and
#   boom : False := match zero return False with end, with zero := Int 0,
#   int registered as the int63 type, and a parameter int : Set inserted
#   before the definition int. The registration is checked on the
#   parameter, the definition replaces it, and the client proves False
#   with boom;
# - modtype: two module types T and U, with U labelled T.
# The files that coqc compiles must be accepted, and so must shared/Lib.v,
# whose labels repeat as coqc lets them. Each run of rocqchk has 300 s of
# CPU time: when the second ax is ax : False := proof, a rocqchk that lets
# a label repeat does not end within 1200 s.

set -e

D=misc/rocqchk-delta-alias
L=$D/repeated-label

forge() { ocaml "$D/forge.ml" "$@"; }

# compile <case> <file>...: compile $L/<case>/<file>.v, in that order.
compile() {
  local c=$L/$1 f
  shift
  rm -rf "$c/forged"
  rm -f "$c"/*.vo "$c"/*.vok "$c"/*.vos "$c"/*.glob
  for f in "$@"; do
    $coqc -noinit -R "$c" RepeatedLabel "$c/$f.v"
  done
  mkdir "$c/forged"
}

xcpu=$((128 + $(kill -l XCPU)))

# chk <dir> <library>...: rocqchk on RepeatedLabel.<library>... in <dir>,
# with 300 s of CPU time.
chk() {
  local dir=$1 libs=() l rc=0
  shift
  for l in "$@"; do libs+=("RepeatedLabel.$l"); done
  ( ulimit -S -t 300; exec "$BIN"rocqchk -R "$dir" RepeatedLabel "${libs[@]}" ) \
    > "$L/out.log" 2>&1 || rc=$?
  if [ "$rc" = "$xcpu" ]; then
    echo "rocqchk did not end within 300 s of CPU time on $dir"
  fi
  return $rc
}

fail=0

# accept <case> <library>...: rocqchk must accept the libraries of case
# <case> as coqc compiles them.
accept() {
  local c=$1
  shift
  if ! chk "$L/$c" "$@"; then
    echo "rocqchk refused the files of case $c"
    cat "$L/out.log"
    fail=1
  fi
}

# relink <case>: the forged Client.vo of case <case>, with the forged Lib.vo
# as its dependency.
relink() {
  local c=$L/$1
  forge client "$c/Client.vo" "$c/forged/Lib.vo" RepeatedLabel.Lib "$c/forged/Client.vo"
}

# refuse <case> <error>: rocqchk must refuse the forged files of case
# <case> with an error that the extended regular expression <error>
# matches.
refuse() {
  if chk "$L/$1/forged" Lib Client; then
    echo "rocqchk accepted the forged library of case $1"
    cat "$L/out.log"
    fail=1
  elif ! grep -Eq "$2" "$L/out.log"; then
    echo "unexpected rocqchk failure for the forged library of case $1"
    cat "$L/out.log"
    fail=1
  fi
}

objects="twice among its constants, inductive types, constructors and rewrite rules"

compile shared Lib
accept shared Lib

compile axiom Lib Client
accept axiom Lib Client
C=$L/axiom
forge relabel "$C/Lib.vo" "$C/forged/Lib.vo" twin ax
relink axiom
refuse axiom "RepeatedLabel\.Lib declares the label ax $objects"

compile registered Lib Client
accept registered Lib Client
C=$L/registered
forge int0 "$C/Lib.vo" "$C/forged/Lib.vo" zero
forge register "$C/forged/Lib.vo" "$C/forged/Lib.vo" RepeatedLabel.Lib.int
forge repeat-parameter "$C/forged/Lib.vo" "$C/forged/Lib.vo" int
relink registered
refuse registered "RepeatedLabel\.Lib declares the label int $objects"

compile modtype Lib Client
accept modtype Lib Client
C=$L/modtype
forge relabel "$C/Lib.vo" "$C/forged/Lib.vo" U T
relink modtype
refuse modtype "RepeatedLabel\.Lib declares the label T twice among its modules and module types"

exit $fail
