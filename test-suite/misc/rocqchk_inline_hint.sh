#!/usr/bin/env bash

# rocqchk must not let the term of an inline hint, Inline (lev, Some t), that a
# delta resolver of a .vo carries change what a substitution through that
# resolver gives: the substitution puts t in place of the constant without
# lifting it, and no check reads t. The forged Lib.vo of case sealed gives the
# implementation resolver of the sealed M the hint M.d -> Inline (0, Some
# (Rel 1)), and M's stored signature says lem : forall b, eq bool b M.d where
# M implements lem : forall b, eq bool b b: through the hint, the expected
# type becomes the implementation's, the binder b capturing Rel 1, and the
# client proves False. In case functor, the hint is in the resolver of A, and
# F A gives lem the type (forall b, eq bool b b) -> eq bool true false that
# the client's T asks for. A corrupted pair may be refused with any error;
# the script prints which.

set -e

D=misc/rocqchk-inline-hint

# chk <dir> <rocqchk arguments>: rocqchk's output goes to <dir>/out.log.
chk() {
  local d=$1
  shift
  "$BIN"rocqchk "$@" > "$D/$d/out.log" 2>&1
}

accepts() {
  local d=$1
  shift
  if ! chk "$d" "$@"; then
    echo "rocqchk refused honest files ($d): rocqchk $*"
    cat "$D/$d/out.log"
    exit 1
  fi
}

refuses() {
  local d=$1
  shift
  if chk "$d" "$@"; then
    echo "rocqchk accepted a forged inline hint and a closed proof of False ($d): rocqchk $*"
    cat "$D/$d/out.log"
    exit 1
  fi
  echo "refused ($d): rocqchk $*: $(grep -m1 -E 'Error|Anomaly' "$D/$d/out.log")"
}

for c in sealed functor; do
  C=$D/$c
  rm -rf "$C/forged"
  rm -f "$C"/honest/*.vo "$C"/honest/*.vok "$C"/honest/*.vos "$C"/honest/*.glob \
        "$C"/donor/*.vo "$C"/donor/*.vok "$C"/donor/*.vos "$C"/donor/*.glob \
        "$C/out.log"
  mkdir "$C/forged"

  for v in honest donor; do
    $coqc -noinit -R "$C/$v" InlineHint "$C/$v/Lib.v"
    $coqc -noinit -R "$C/$v" InlineHint "$C/$v/Client.v"
  done

  # The forged library, from honest/Lib.vo, and the corrupted client:
  # donor/Client.vo, recording the forged library's checksum.
  if [ "$c" = sealed ]; then
    ocaml "$D/forge.ml" sealed "$C/donor/Lib.vo" "$C/honest/Lib.vo" "$C/forged/Lib.vo"
  else
    ocaml "$D/forge.ml" functor "$C/honest/Lib.vo" "$C/forged/Lib.vo"
  fi
  ocaml "$D/forge.ml" client "$C/donor/Client.vo" "$C/forged/Lib.vo" \
    InlineHint.Lib "$C/forged/Client.vo"

  for v in honest forged; do
    if [ "$v" = honest ]; then check=accepts; else check=refuses; fi
    # As a grader runs it, and with the default options.
    $check "$c" -o -bytecode-compiler yes -R "$C/$v" InlineHint \
      -norec InlineHint.Lib InlineHint.Client
    $check "$c" -R "$C/$v" InlineHint InlineHint.Lib InlineHint.Client
  done
done

# The forged library of case sealed holds the unsound sealing by itself. That
# of case functor does not: only the client applies F to A.
refuses sealed -R "$D/sealed/forged" InlineHint -norec InlineHint.Lib
