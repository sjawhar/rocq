#!/usr/bin/env bash

# rocqchk must refuse a library that registers as a primitive type a
# constant that coqc does not register. The typing of a primitive literal
# uses the registered constant: with int : Set := Empty_set registered as
# the int63 type, the literal Int 0 has type int, which unfolds to
# Empty_set, and a match on it is a closed proof of False. coqc registers a
# primitive type only for a parameter that Primitive declares, in a library
# or in a module nested in it with no functor parameter, and names it as
# declared. forge.ml writes the forgeries:
# - donor: the definition int registered, and zero := Int 0;
# - sealed: in Module M : T, M.int is T's parameter and M's definition of
#   Empty_set; M.int registered, and the client's z := Int 0;
# - functor: R := F N, with Module M : T := P in F; R.M.int, declared only
#   by T's parameter in R's type, registered, and the client's z := Int 0;
# - dual: the parameter int registered with the canonical name of
#   N.int := Empty_set, and the client's z : N.int := Int 0;
# - other: a constant of an earlier library registered;
# - twice: the honest library's MI.int registered a second time.
# Each of the sources, and the honest library, must be accepted.

set -e

. misc/rocqchk_forge_common.bash

D=misc/rocqchk-register-type
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT

# compile <case> <file>...: compile <case>/<file>.v in that order, bound to
# RegType, in a copy of the case under $d.
compile() {
  local c=$1 f
  shift
  mkdir "$d/$c"
  for f in "$@"; do
    cp "$D/$c/$f.v" "$d/$c/"
    $coqc -noinit -R "$d/$c" RegType "$d/$c/$f.v"
  done
}

compile honest Lib
compile donor Lib
compile sealed Lib Client
compile functor Lib Client
compile dual Lib Client
compile other Base Lib

# accept_case <dir> [<client>] and refuse_case <dir> <client or ""> <error>
# <forgery>: rocqchk must accept RegType.Lib and RegType.<client> in $d/<dir>,
# or refuse them with an error that the extended regular expression <error>
# matches, as a grader runs it and with the default options. The error is
# matched without the constant's name, which rocqchk may print on the line
# before.
accept_case() {
  local mode
  for mode in grader default; do
    mode_args $mode "$d/$1" RegType ${2-}
    must_accept "$d/out.log" "rocqchk ($mode) refused the files of $1" "${mode_argv[@]}"
  done
}

refuse_case() {
  local mode
  for mode in grader default; do
    mode_args $mode "$d/$1" RegType $2
    must_refuse "$d/out.log" "$3" "rocqchk ($mode) accepted $4" \
      "unexpected rocqchk ($mode) failure for $4" "${mode_argv[@]}"
  done
}

accept_case honest
accept_case donor
accept_case sealed Client
accept_case functor Client
accept_case dual Client
accept_case other Base

forge() { ocaml "$D/forge.ml" "$@"; }

# forge_client <case>: the client of <case> with z := Int 0, recording the
# forged Lib.vo of f-<case> as its dependency.
forge_client() {
  forge int0 "$d/$1/Client.vo" "$d/$1-int0.vo" z
  forge client "$d/$1-int0.vo" "$d/f-$1/Lib.vo" RegType.Lib "$d/f-$1/Client.vo"
}

not_a_parameter="is registered as the primitive type int63_type, but it is not a parameter"

mkdir "$d/f-donor"
forge int0 "$d/donor/Lib.vo" "$d/donor-int0.vo" zero
forge register "$d/donor-int0.vo" "$d/f-donor/Lib.vo" RegType.Lib.int
refuse_case f-donor "" "$not_a_parameter" \
  "the definition int registered as the int63 type and a closed proof of False"

mkdir "$d/f-sealed"
forge register "$d/sealed/Lib.vo" "$d/f-sealed/Lib.vo" RegType.Lib.M.int
forge_client sealed
refuse_case f-sealed Client "$not_a_parameter" \
  "the sealed definition M.int registered as the int63 type and a closed proof of False"

mkdir "$d/f-functor"
forge register "$d/functor/Lib.vo" "$d/f-functor/Lib.vo" RegType.Lib.R.M.int
forge_client functor
refuse_case f-functor Client \
  "Retroknowledge registration for unknown constant RegType\.Lib\.R\.M\.int" \
  "R.M.int, a parameter of a functor application, registered as the int63 type and a closed proof of False"

mkdir "$d/f-dual"
forge register "$d/dual/Lib.vo" "$d/f-dual/Lib.vo" RegType.Lib.int RegType.Lib.N.int
forge_client dual
refuse_case f-dual Client \
  "is registered as the primitive type int63_type, but the registration gives it another canonical name, RegType\.Lib\.N\.int" \
  "int registered as the int63 type with the canonical name of N.int and a closed proof of False"

mkdir "$d/f-other"
cp "$d/other/Base.vo" "$d/f-other/"
forge register "$d/other/Lib.vo" "$d/f-other/Lib.vo" RegType.Base.int
refuse_case f-other Base \
  "is registered as the primitive type int63_type, but an earlier library declares it" \
  "the registration of a constant of an earlier library"

mkdir "$d/f-twice"
forge register "$d/honest/Lib.vo" "$d/f-twice/Lib.vo" RegType.Lib.MI.int
refuse_case f-twice "" "is registered twice as a primitive type" \
  "a constant registered twice as a primitive type"
