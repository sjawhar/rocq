#!/usr/bin/env bash

# rocqchk must refuse a library that registers as a primitive type a
# constant that coqc does not register. The typing of a primitive literal
# uses the registered constant: with int : Set := Empty_set registered as
# the int63 type, the literal Int 0 has the type int, which unfolds to
# Empty_set, and a match on it is a closed proof of False. coqc registers
# only the parameter that Primitive declares, in the library or in one of
# its modules that is not a functor, under the parameter's own name.
# forge.ml registers another constant as the int63 type in each case of
# register-type/, and gives z (zero in donor) the body Int 0:
# - donor: the definition int;
# - sealed: M.int, where M : T, T declares int as a parameter and M defines
#   it;
# - functor: R.M.int, where R := F N; R's type, with the parameter int of
#   F's M : T := P, is the only declaration of R.M.int, and N defines int;
# - dual: the parameter int, with the canonical name of N.int, which is
#   defined;
# - other: int of the earlier library Base;
# - twice: MI.int of honest/Lib.v, which registers it already.
# The libraries that coqc compiles, among them honest/Lib.v, which registers
# each primitive type as coqc does, must be accepted.

set -e

D=misc/rocqchk-delta-alias
R=$D/register-type

forge() { ocaml "$D/forge.ml" "$@"; }

# compile <case> <file>...: compile $R/<case>/<file>.v, in that order.
compile() {
  local c=$R/$1 f
  shift
  rm -rf "$c/forged"
  rm -f "$c"/*.vo "$c"/*.vok "$c"/*.vos "$c"/*.glob "$c/out.log"
  for f in "$@"; do
    $coqc -noinit -R "$c" RegisterType "$c/$f.v"
  done
  mkdir "$c/forged"
}

# chk <dir> <library>: rocqchk on RegisterType.<library> in <dir>.
chk() {
  "$BIN"rocqchk -R "$1" RegisterType "RegisterType.$2" > "$R/out.log" 2>&1
}

fail=0

# accept <case> <library>: rocqchk must accept the library of case <case>.
accept() {
  if ! chk "$R/$1" $2; then
    echo "rocqchk refused the files of case $1"
    cat "$R/out.log"
    fail=1
  fi
}

# refuse <case> <dir> <library> <error>: rocqchk must refuse the forged
# library of case <case>, in $R/<dir>/forged, with an error that the
# extended regular expression <error> matches.
refuse() {
  if chk "$R/$2/forged" $3; then
    echo "rocqchk accepted the forged registration of case $1"
    cat "$R/out.log"
    fail=1
  elif ! grep -Eq "$4" "$R/out.log"; then
    echo "unexpected rocqchk failure for the forged registration of case $1"
    cat "$R/out.log"
    fail=1
  fi
}

not_a_parameter="is registered as the primitive type int63_type, but it is not a parameter"

compile donor Lib
accept donor Lib
C=$R/donor
forge int0 "$C/Lib.vo" "$C/forged/Lib.vo" zero
forge register "$C/forged/Lib.vo" "$C/forged/Lib.vo" RegisterType.Lib.int
refuse donor donor Lib "$not_a_parameter"

# client_case <case> <error> <name> [<canonical>]: the forged Lib.vo of
# <case> registers <name>, with the canonical name <canonical> if it is
# given, and its forged Client.vo gives z the body Int 0. rocqchk must
# accept the files that coqc compiles, and refuse the forged ones with an
# error that the extended regular expression <error> matches.
client_case() {
  local name=$1 c=$R/$1 error=$2
  shift 2
  compile $name Lib Client
  accept $name Client
  forge register "$c/Lib.vo" "$c/forged/Lib.vo" "$@"
  forge int0 "$c/Client.vo" "$c/forged/Client.vo" z
  forge client "$c/forged/Client.vo" "$c/forged/Lib.vo" RegisterType.Lib "$c/forged/Client.vo"
  refuse $name $name Client "$error"
}

client_case sealed "$not_a_parameter" RegisterType.Lib.M.int
client_case functor \
  "Retroknowledge registration for unknown constant RegisterType\.Lib\.R\.M\.int" \
  RegisterType.Lib.R.M.int
client_case dual \
  "is registered as the primitive type int63_type, but the registration gives it another canonical name, RegisterType\.Lib\.N\.int" \
  RegisterType.Lib.int RegisterType.Lib.N.int

compile other Base Lib
accept other Lib
C=$R/other
cp "$C/Base.vo" "$C/forged/"
forge register "$C/Lib.vo" "$C/forged/Lib.vo" RegisterType.Base.int
refuse other other Lib "is registered as the primitive type int63_type, but an earlier library declares it"

# The forged library of case twice is made from the honest one.
compile honest Lib
accept honest Lib
C=$R/honest
forge register "$C/Lib.vo" "$C/forged/Lib.vo" RegisterType.Lib.MI.int
refuse twice honest Lib "is registered twice as a primitive type"

exit $fail
