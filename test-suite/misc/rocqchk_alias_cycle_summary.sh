#!/usr/bin/env bash

# The -o summary reads an admitted library's implementations to tell a
# parameter from a definition (checker/mod_impl.ml). rocqchk does not check
# an admitted library, so its modules can be alias cycles that coqc never
# writes: forge.ml turns the honest Cycle.v into
#   Self := Self,  Ping := Pong,  Pong := Ping,  Up := Down,  Down := Up.C.
# Reading such a module must stop and keep the name, as for any
# implementation it cannot read: rocqchk must end, and list the five
# parameters these modules' types declare. The honest library is the
# control: each module there is Defines, which defines p, so nothing is
# listed.
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

cat > "$d/expected" <<'EOF'
AliasCycle.Cycle.Down.p
AliasCycle.Cycle.Ping.p
AliasCycle.Cycle.Pong.p
AliasCycle.Cycle.Self.p
AliasCycle.Cycle.Up.C.p
EOF
axioms "$d/forged" "$d/forged.log" AliasCycle Cycle > "$d/axioms"
if ! diff -u "$d/expected" "$d/axioms"; then
  echo "rocqchk -o does not keep the names under the forged cycles"
  cat "$d/forged.log"
  exit 1
fi
