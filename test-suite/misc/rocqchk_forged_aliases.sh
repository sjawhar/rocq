#!/usr/bin/env bash

# rocqchk must refuse a delta resolver alias that coqc never writes. For each
# case, forge.ml records one in a library compiled by coqc, and a client
# compiled against <case>/donor/Lib.v proves False from it:
# - parameter: M2.c becomes an alias of M1.c in the type of M2, where both
#   are declared-only, M1.c := true and M2.c := false.
# See misc/rocqchk_delta_alias.sh for forged aliases between definitions.

set -e

D=misc/rocqchk-delta-alias

# chk <honest|forged>: rocqchk on the library and the client of case $C.
chk() {
  "$BIN"rocqchk -R "$C/$1" ForgedAliases ForgedAliases.Lib ForgedAliases.Client > "$C/out.log" 2>&1
}

fail=0
for case in parameter; do
  C=$D/$case
  rm -rf "$C/forged"
  rm -f "$C"/*/*.vo "$C"/*/*.vok "$C"/*/*.vos "$C"/*/*.glob "$C/out.log"
  for v in honest donor; do
    $coqc -noinit -R "$C/$v" ForgedAliases "$C/$v/Lib.v"
    $coqc -noinit -R "$C/$v" ForgedAliases "$C/$v/Client.v"
  done
  mkdir "$C/forged"
  ocaml "$D/forge.ml" $case "$C/honest/Lib.vo" "$C/forged/Lib.vo"
  ocaml "$D/forge.ml" client "$C/donor/Client.vo" "$C/forged/Lib.vo" \
    ForgedAliases.Lib "$C/forged/Client.vo"

  if ! chk honest; then
    echo "rocqchk refused the honest files of case $case"
    cat "$C/out.log"
    fail=1
  fi
  if chk forged; then
    echo "rocqchk accepted a forged $case alias and a closed proof of False"
    cat "$C/out.log"
    fail=1
  elif ! grep -q "Module typing error" "$C/out.log"; then
    echo "unexpected rocqchk failure for a forged $case alias"
    cat "$C/out.log"
    fail=1
  fi
done
exit $fail
