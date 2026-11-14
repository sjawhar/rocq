#!/usr/bin/env bash

# The -o summary reads an admitted library's implementations to tell a
# parameter from a definition (checker/mod_impl.ml). rocqchk does not check
# an admitted library, so its modules can be alias cycles that coqc never
# writes: forge.ml turns the honest Cycle.v into
#   Self := Self,  Ping := Pong,  Pong := Ping,  Up := Down,  Down := Up.C.
# Reading such a module ends only at a stop, where the walk has not read
# the implementation it needs: rocqchk -o must end, and refuse to print a
# summary, with an error that names a module of a cycle. Which cycle it
# meets first depends on the order in which the summary asks about the five
# parameters these modules' types declare, so any of them will do. The
# honest library is the control: each module there is Defines, which
# defines p, so nothing is listed.
set -eu

. misc/rocqchk_summary_common.bash

D=misc/rocqchk-alias-cycle
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
mkdir "$d/honest" "$d/forged"
cp "$D/Cycle.v" "$d/honest/"

$coqc -noinit -Q "$d/honest" AliasCycle "$d/honest/Cycle.v"
cp "$d/honest/Cycle.vo" "$d/forged/"
ocaml "$D/forge.ml" "$d/forged/Cycle.vo"

axioms "$d/honest" "$d/honest.log" AliasCycle Cycle > "$d/honest-axioms"
if [ -s "$d/honest-axioms" ]; then
  echo "the honest library has axioms"
  cat "$d/honest.log"
  exit 1
fi

got=$(refusal "$d/forged.log" -Q "$d/forged" AliasCycle -admit AliasCycle.Cycle)
path='AliasCycle\.Cycle\.[A-Za-z.]+'
if ! printf '%s\n' "$got" | grep -q -x -E "the walk of the module implementations stopped at (the alias $path := $path, whose target it is already reading: the aliases form a cycle|the module $path, whose implementation it needs while it reads it: the implementations form a cycle)\."; then
  echo "rocqchk -o refused the forged cycles with another error"
  cat "$d/forged.log"
  exit 1
fi
