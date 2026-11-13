#!/usr/bin/env bash

# rocqchk must refuse a library that registers as a primitive type a
# constant that is not a parameter of the primitive type's type, or that the
# own body of the library does not declare. The typing of a primitive
# literal uses the registered constant: with int : Set := Empty_set
# registered as the int63 type, the literal Int 0 has type int, which
# unfolds to Empty_set, and a match on it is a closed proof of False. coqc
# registers a primitive type only for the constant that Primitive declares,
# so forge.ml writes the forged libraries, each in forged-<case>:
#  - own: donor/Lib.vo registers its own definition int;
#  - foreign: foreign/Lib.vo registers Base.int, a definition of another
#    library, which Lib.v does not declare;
#  - dual: dual/Lib.vo registers a name whose user name is its own
#    parameter carrier : Set and whose canonical name is Base.int;
#  - sealed: sealed/Lib.vo registers M.int, which the signature of the
#    sealed module M declares as a parameter and its implementation defines
#    as Empty_set;
#  - functor: functor/Lib.vo registers R.M.int, which the type of R, an
#    application of a functor, declares as a parameter, and which no own
#    body of the library declares.
# own, foreign and dual give zero : int the body Int 0, and their Client.vo,
# as coqc compiled it, records the forged Lib.vo as its dependency. The
# Client.vo of sealed and functor is compiled against sealed-donor/Lib.v and
# functor-donor/Lib.v, where M.int and R.M.int are declared by Primitive,
# and applies int_empty to an int63 literal.
#
# rocqchk must also refuse a primitive operator whose type is not the
# operator's: in forged-primop, primop/Lib.vo's axiom
# add : int -> int -> False becomes the int63 addition, and its Client.vo
# records it. rocqchk must accept the honest and donor libraries and refuse
# each forged pair, as a grader runs it (-o -bytecode-compiler yes) and with
# the default options. Every case runs, and the script fails if one of them
# does not hold.

set -e

D=misc/rocqchk-register-type
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
status=0

for dir in honest donor foreign sealed functor sealed-donor functor-donor primop; do
  cp -r "$D/$dir" "$d/$dir"
done
# The dual libraries are the foreign ones with dual/Lib.v.
cp -r "$D/foreign" "$d/dual"
cp "$D/dual/Lib.v" "$d/dual/Lib.v"
for dir in honest donor sealed functor sealed-donor functor-donor primop; do
  for f in Lib Client; do
    $coqc -noinit -R "$d/$dir" RegType "$d/$dir/$f.v"
  done
done
for dir in foreign dual; do
  for f in Base Lib Client; do
    $coqc -noinit -R "$d/$dir" RegType "$d/$dir/$f.v"
  done
done

# mode_args <mode> <dir>: set the array mode_argv to the rocqchk arguments
# that check RegType.Lib and RegType.Client in <dir>, as a grader runs
# rocqchk (mode grader) or with the default options (mode default).
mode_args() {
  case $1 in
    grader) mode_argv=(-o -bytecode-compiler yes -R "$2" RegType -norec RegType.Lib RegType.Client) ;;
    default) mode_argv=(-R "$2" RegType RegType.Lib RegType.Client) ;;
  esac
}

# accepts <dir> <mode>: rocqchk must accept the libraries of $d/<dir>.
accepts() {
  local log="$d/$1-$2.log"
  mode_args "$2" "$d/$1"
  if ! "$BIN"rocqchk "${mode_argv[@]}" > "$log" 2>&1; then
    echo "FAILURE: rocqchk ($2) refused the $1 libraries: rocqchk ${mode_argv[*]}"
    cat "$log"
    status=1
  fi
}

# refuses <case> <mode> <error>...: rocqchk must refuse the libraries of
# $d/forged-<case> with an error that contains each <error>.
refuses() {
  local name=$1 mode=$2 log="$d/forged-$1-$2.log" e
  shift 2
  mode_args "$mode" "$d/forged-$name"
  if "$BIN"rocqchk "${mode_argv[@]}" > "$log" 2>&1; then
    echo "FAILURE: rocqchk ($mode) accepted the forged $name libraries and a closed proof of False: rocqchk ${mode_argv[*]}"
    cat "$log"
    status=1
    return
  fi
  for e in "$@"; do
    if ! grep -Fq -- "$e" "$log"; then
      echo "FAILURE: rocqchk ($mode) refused the forged $name libraries without \"$e\": rocqchk ${mode_argv[*]}"
      cat "$log"
      status=1
      return
    fi
  done
}

# The honest libraries register each primitive type as coqc does. The
# donor, foreign, dual, sealed and functor libraries register nothing, and
# the sealed-donor and functor-donor libraries declare int with Primitive.
# In primop, add is an axiom.
for dir in honest donor foreign dual sealed functor sealed-donor functor-donor primop; do
  for mode in grader default; do
    accepts "$dir" "$mode"
  done
done

# forge <case> <lib dir> <client dir> <command> <argument>...: the forged
# pair of <case> in $d/forged-<case>: forge.ml <command> on the Lib.vo of
# $d/<lib dir>, and the Client.vo of $d/<client dir> recording it.
forge() {
  local f="$d/forged-$1" lib=$2 client=$3
  shift 3
  mkdir "$f"
  if [ -f "$d/$lib/Base.vo" ]; then cp "$d/$lib/Base.vo" "$f/"; fi
  ocaml "$D/forge.ml" "$1" "$d/$lib/Lib.vo" "$f/Lib.vo" "${@:2}"
  ocaml "$D/forge.ml" client "$d/$client/Client.vo" "$f/Lib.vo" RegType.Lib "$f/Client.vo"
}

forge own donor donor regtype
forge foreign foreign foreign regtype
forge dual dual dual dual
forge sealed sealed sealed-donor register M
forge functor functor functor-donor register R.M
forge primop primop primop primop

for mode in grader default; do
  refuses own "$mode" \
    "is registered as the primitive type int63_type, but it is not a parameter."
  refuses foreign "$mode" \
    "is registered as the primitive type int63_type in RegType.Lib, which does not declare it."
  refuses dual "$mode" \
    "(canonical name RegType.Base.int)" \
    "is registered as the primitive type int63_type in RegType.Lib, which does not declare it."
  refuses sealed "$mode" \
    "is registered as the primitive type int63_type, but it is not a parameter."
  refuses functor "$mode" \
    "is registered as the primitive type int63_type in RegType.Lib, which does not declare it."
  refuses primop "$mode" \
    "is the primitive operator add, but its type is not the operator's."
done

exit $status
