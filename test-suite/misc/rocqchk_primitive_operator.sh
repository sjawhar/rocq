#!/usr/bin/env bash

# rocqchk must refuse a constant whose body is a primitive operator and
# whose type is not the operator's. Conversion and the VM compute with the
# operator whatever type the constant declares, so bogus : False with the
# body #int63_head0 is a closed proof of False. coqc gives such a constant
# the type of its operator, int -> int for head0, and does not declare it
# while that type names a primitive type that is not registered. In each
# case of primitive-operator/, forge.ml gives the axiom bogus : False the
# body #int63_head0:
# - registered: the library registers int, and declares operators as coqc
#   does;
# - unregistered: the library registers no primitive type.
# The libraries that coqc compiles must be accepted.

set -e

D=misc/rocqchk-delta-alias
P=$D/primitive-operator

chk() {
  "$BIN"rocqchk -R "$1" PrimitiveOperator PrimitiveOperator.Lib > "$P/out.log" 2>&1
}

fail=0

# check <case> <error>: rocqchk must accept the library of case <case>, and
# refuse its forged copy with an error that the extended regular expression
# <error> matches.
check() {
  local c=$P/$1
  rm -rf "$c/forged"
  rm -f "$c"/*.vo "$c"/*.vok "$c"/*.vos "$c"/*.glob
  $coqc -noinit -R "$c" PrimitiveOperator "$c/Lib.v"
  if ! chk "$c"; then
    echo "rocqchk refused the library of case $1"
    cat "$P/out.log"
    fail=1
  fi
  mkdir "$c/forged"
  ocaml "$D/forge.ml" head0 "$c/Lib.vo" "$c/forged/Lib.vo" bogus
  if chk "$c/forged"; then
    echo "rocqchk accepted bogus : False := #int63_head0 (case $1)"
    cat "$P/out.log"
    fail=1
  elif ! grep -Eq "$2" "$P/out.log"; then
    echo "unexpected rocqchk failure for bogus : False := #int63_head0 (case $1)"
    cat "$P/out.log"
    fail=1
  fi
}

check registered "is the primitive operator head0, but its type is not the operator's"
check unregistered "The type int must be registered before this construction can be typechecked"

exit $fail
