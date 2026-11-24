#!/usr/bin/env bash

# rocqchk must compare the whole canonical name of a stored registration of
# a primitive inductive type with the declared one, not only its label. An
# honest registration through a module alias or an Include keeps the label
# and changes the module path (Subtyping.check_inductive_alias requires
# equal labels), so a check that compares labels passes every honest set of
# rocqchk_register_ind_canonical.sh, and every forged set there whose
# canonical name the check compares, since their forged canonical names
# have the label U (forged-functor is refused as an unknown inductive
# whatever the comparison). Here the library
# rocqchk-register-ind-canonical/label/Lib.v declares B := true | false,
# registered as bool, and N.B := u1 | u2 (_ : False), which has the label B
# too. The forged library stores the registration of B with the canonical
# name of N.B, and the client ClientU.v, compiled against it, proves
# boom : False. rocqchk must refuse the forged library, alone and with the
# client, as a grader runs it and with the default options, with the error
# that names the registration, N.B and B. The honest library with its
# honest client must be accepted in both modes.

set -e

. misc/rocqchk_forge_common.bash

: "${coqc:?the misc rule of test-suite/Makefile exports coqc}"

D=misc/rocqchk-register-ind-canonical/label
FORGE=misc/rocqchk-register-type/forge.ml
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT

mkdir "$d/honest" "$d/forged"
cp "$D/Lib.v" "$D/ClientB.v" "$d/honest/"
$coqc -noinit -R "$d/honest" RegInd "$d/honest/Lib.v"
$coqc -noinit -R "$d/honest" RegInd "$d/honest/ClientB.v"
# forge.ml names the scratch directory in its output: keep it in a log,
# printed only if forge.ml fails, so that two runs print the same bytes.
ocaml "$FORGE" ind-canonical "$d/honest/Lib.vo" "$d/forged/Lib.vo" RegInd.Lib.B RegInd.Lib.N.B \
  > "$d/forge.log" 2>&1 || { sed "s|$d|<scratch>|g" "$d/forge.log"; exit 1; }
ocaml "$FORGE" retro "$d/forged/Lib.vo"
cp "$D/ClientU.v" "$d/forged/"
$coqc -noinit -R "$d/forged" RegInd "$d/forged/ClientU.v"

set +e

expected='Fatal Error: User error: RegInd.Lib.B is registered as the primitive inductive type bool, but the registration gives it the canonical name RegInd.Lib.N.B, not RegInd.Lib.B.'
fails=0
for mode in grader default; do
  mode_args "$mode" "$d/honest" RegInd ClientB
  if "$BIN"rocqchk "${mode_argv[@]}" > "$d/out.log" 2>&1; then
    echo "honest ($mode): accepted"
  else
    echo "honest ($mode): refused, not as expected:"
    sed "s|$d|<scratch>|g" "$d/out.log"
    fails=$((fails + 1))
  fi
  for client in "" ClientU; do
    shown="library alone"
    if [ -n "$client" ]; then shown="with client"; fi
    mode_args "$mode" "$d/forged" RegInd "$client"
    if "$BIN"rocqchk "${mode_argv[@]}" > "$d/out.log" 2>&1; then
      echo "forged ($mode, $shown): accepted, not as expected: the registration of B with N.B's canonical name"
      fails=$((fails + 1))
    elif grep -qF "$expected" "$d/out.log"; then
      echo "forged ($mode, $shown): refused: $expected"
    else
      echo "forged ($mode, $shown): refused with another error, not as expected:"
      sed "s|$d|<scratch>|g" "$d/out.log"
      fails=$((fails + 1))
    fi
  done
done
echo "not as expected: $fails of 6 runs"
[ "$fails" = 0 ]
