#!/usr/bin/env bash

# rocqchk must not accept a serialized module signature whose delta resolver
# makes a declared-only field (a Parameter) an alias of another one. With c
# and d declared in the type of a sealed module M, an alias of M.d to M.c
# proves False, although M's implementation has c := true and d := false. The
# same holds for an alias that keeps its label (M2.c to M1.c) and for an alias
# in the type of a functor's parameter. See misc/rocqchk_delta_alias.sh for
# forged aliases of definitions.

set -e

D=misc/rocqchk-sigalias

rm -f "$D"/*/*.vo "$D"/*/*.vok "$D"/*/*.vos "$D"/*/*.glob "$D"/out.log
rm -rf "$D"/forged-sealed "$D"/forged-cross "$D"/forged-functor

for f in Lib Client; do
  $coqc -noinit -R "$D/honest" SigAlias "$D/honest/$f.v"
done
for f in Lib Sealed Cross Functor; do
  $coqc -noinit -R "$D/donor" SigAlias "$D/donor/$f.v"
done

# chk <dir> <client> <mode>: rocqchk on SigAlias.Lib and SigAlias.<client> in
# <dir>, as a grader runs it or with the default options.
chk() {
  case $3 in
    grader) "$BIN"rocqchk -o -bytecode-compiler yes -R "$1" SigAlias -norec SigAlias.Lib "SigAlias.$2" ;;
    default) "$BIN"rocqchk -R "$1" SigAlias SigAlias.Lib "SigAlias.$2" ;;
  esac > "$D/out.log" 2>&1
}

for mode in grader default; do
  if ! chk "$D/honest" Client $mode; then
    echo "rocqchk ($mode) refused the honest libraries"
    cat "$D/out.log"
    exit 1
  fi
done

for kind in sealed cross functor; do
  F="$D/forged-$kind"
  client=${kind^}
  mkdir "$F"
  if [ $kind = functor ]; then
    ocaml "$D/forge.ml" functor "$D/donor/Lib.vo" "$D/honest/Lib.vo" "$F/Lib.vo"
  else
    ocaml "$D/forge.ml" $kind "$D/honest/Lib.vo" "$F/Lib.vo"
  fi
  # The client as coqc compiled it against donor/Lib.v, recording the forged
  # Lib.vo as its dependency.
  ocaml "$D/forge.ml" client "$D/donor/$client.vo" "$F/Lib.vo" SigAlias.Lib "$F/$client.vo"

  for mode in grader default; do
    if chk "$F" $client $mode; then
      echo "rocqchk ($mode) accepted a forged $kind alias between declared-only fields and a closed proof of False"
      cat "$D/out.log"
      exit 1
    fi
    # 9.2's rocqchk has no printer for a module typing error and reports the
    # exception itself (see misc/rocqchk_delta_alias.sh).
    if ! grep -Eq "Module typing error|ModuleTypingError" "$D/out.log"; then
      echo "unexpected rocqchk ($mode) failure for a forged $kind alias"
      cat "$D/out.log"
      exit 1
    fi
  done
done
