#!/usr/bin/env bash

# rocqchk must refuse a structure that gives one label to two fields in one
# of coqc's two namespaces: the objects (constants, rewrite rule blocks, and
# the types and constructors of inductive blocks) and the modules (modules
# and module types). The environment keeps the last field with a label, so
# the second field replaces the first, which the fields between them were
# checked against. forge.ml, with the regtype command of
# misc/rocqchk-register-type/forge.ml, writes the forgeries:
# - registered: misc/rocqchk-register-type/donor/Lib.v with zero := Int 0,
#   int registered as the int63 type, and a parameter int : Set before
#   int := Empty_set. The parameter passes the registration's check. On
#   this line that check also refuses the definition, since it checks each
#   declaration of a registered name, but the label check refuses the file
#   first;
# - axiom: Axiom ax : False, proof := ax and twin : unit := tt, with twin
#   renamed ax. No constant is left without a body, and proof is a closed
#   proof of False;
# - modtype: two module types T and U, with U renamed T.
# The clients of registered and axiom prove False with the library's
# proof; each client is relinked to the forged library. rocqchk must accept
# each pair as coqc compiles it, and the honest library, which shares
# labels as coqc lets it. It must refuse each forged pair with the error of
# the repeated label. Each is checked as a grader runs rocqchk and with the
# default options, and each run of rocqchk has 300 s to end.

set -e

D=misc/rocqchk-repeated-label
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT

# need <file>...: each file must exist and not be empty.
need() {
  local f
  for f in "$@"; do
    if [ ! -s "$f" ]; then
      echo "missing or empty: $f"
      exit 1
    fi
  done
}

# compile <case> <source>...: compile the sources in that order, bound to
# RepLabel, in $d/<case>.
compile() {
  local c=$1 f v
  shift
  mkdir "$d/$c"
  for f in "$@"; do
    cp "$f" "$d/$c/"
    v=$d/$c/$(basename "$f")
    $coqc -noinit -R "$d/$c" RepLabel "$v"
    need "${v%.v}.vo"
  done
}

compile honest $D/honest/Lib.v
compile registered misc/rocqchk-register-type/donor/Lib.v $D/registered/Client.v
compile axiom $D/axiom/Lib.v $D/axiom/Client.v
compile modtype $D/modtype/Lib.v $D/modtype/Client.v

# mode_args <mode> <dir> [<client>]: set the array mode_argv to the rocqchk
# arguments that check RepLabel.Lib, and RepLabel.<client> if it is given,
# in <dir>, as a grader runs rocqchk (mode grader) or with the default
# options (mode default).
mode_args() {
  local libs=(RepLabel.Lib)
  if [ -n "${3-}" ]; then libs+=("RepLabel.$3"); fi
  case $1 in
    grader) mode_argv=(-o -bytecode-compiler yes -R "$2" RepLabel -norec "${libs[@]}") ;;
    default) mode_argv=(-R "$2" RepLabel "${libs[@]}") ;;
  esac
}

# chk <what> <rocqchk argument>...: run rocqchk, with its output in
# $d/out.log, and set rc to its exit status. A run that does not end within
# 300 s is a failure of its own.
chk() {
  local what=$1
  shift
  rc=0
  timeout 300 "$BIN"rocqchk "$@" > "$d/out.log" 2>&1 || rc=$?
  if [ "$rc" = 124 ]; then
    echo "rocqchk did not end within 300 s on $what: rocqchk $*"
    cat "$d/out.log"
    exit 1
  fi
}

checks=0

# accept_case <dir> [<client>] and refuse_case <dir> <error> <forgery>:
# rocqchk must accept RepLabel.Lib and RepLabel.<client> in $d/<dir>, and
# report them checked, or refuse RepLabel.Lib and RepLabel.Client with an
# error that the extended regular expression <error> matches. Each runs
# rocqchk as a grader runs it and with the default options, and prints
# what it checked.
accept_case() {
  local mode
  for mode in grader default; do
    mode_args $mode "$d/$1" ${2-}
    chk "$1 ($mode)" "${mode_argv[@]}"
    if [ "$rc" != 0 ] || ! grep -q "Modules were successfully checked" "$d/out.log"; then
      echo "rocqchk ($mode) refused the files of $1, or did not report them checked"
      cat "$d/out.log"
      exit 1
    fi
    echo "checked $1 ($mode): accepted"
    checks=$((checks + 1))
  done
}

refuse_case() {
  local mode
  for mode in grader default; do
    mode_args $mode "$d/$1" Client
    chk "$1 ($mode)" "${mode_argv[@]}"
    if [ "$rc" = 0 ]; then
      echo "rocqchk ($mode) accepted $3"
      cat "$d/out.log"
      exit 1
    fi
    if ! grep -Eq "$2" "$d/out.log"; then
      echo "unexpected rocqchk ($mode) failure for $3"
      cat "$d/out.log"
      exit 1
    fi
    echo "checked $1 ($mode): refused: $(grep -m1 -E -o "$2" "$d/out.log")"
    checks=$((checks + 1))
  done
}

accept_case honest
accept_case registered Client
accept_case axiom Client
accept_case modtype Client

forge() { ocaml "$D/forge.ml" "$@"; }
regtype() { ocaml misc/rocqchk-register-type/forge.ml "$@"; }

# relink <case>: the client of <case>, recording the forged Lib.vo of
# f-<case> as its dependency.
relink() {
  forge client "$d/$1/Client.vo" "$d/f-$1/Lib.vo" RepLabel.Lib "$d/f-$1/Client.vo"
  need "$d/f-$1/Lib.vo" "$d/f-$1/Client.vo"
}

objects="twice among its constants, inductive types, constructors and rewrite rules"

mkdir "$d/f-registered"
regtype regtype "$d/registered/Lib.vo" "$d/registered-reg.vo"
forge param "$d/registered-reg.vo" "$d/f-registered/Lib.vo" int
relink registered
refuse_case f-registered "RepLabel\.Lib declares the label int $objects" \
  "a parameter int registered as the int63 type and followed by int := Empty_set"

mkdir "$d/f-axiom"
forge rename "$d/axiom/Lib.vo" "$d/f-axiom/Lib.vo" twin ax
relink axiom
refuse_case f-axiom "RepLabel\.Lib declares the label ax $objects" \
  "an axiom ax replaced by ax : unit := tt, and a closed proof of False"

mkdir "$d/f-modtype"
forge rename "$d/modtype/Lib.vo" "$d/f-modtype/Lib.vo" U T
relink modtype
refuse_case f-modtype "RepLabel\.Lib declares the label T twice among its modules and module types" \
  "two module types labelled T"

if [ "$checks" -ne 14 ]; then
  echo "ran $checks checks, not 14"
  exit 1
fi
echo "ran $checks checks"
