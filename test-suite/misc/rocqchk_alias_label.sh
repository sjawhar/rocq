#!/usr/bin/env bash

# rocqchk must not accept a serialized delta resolver entry that makes a
# constant an alias of a constant with another label. A functor application
# rebuilds a substituted name's canonical part with the user name's label
# (Mod_subst.subst_con0_flat). So in F (P : S), an alias of F.k to P.X.d,
# with F.k := P.X.d, names A.X.k in G := F A, and F's lemma : k = false,
# proved from P.X.f, becomes a proof of A.X.k = false, although A.X.k is
# true. See misc/rocqchk_sigalias.sh for aliases between declared-only
# fields.

set -e

D=misc/rocqchk-alias-label

rm -f "$D"/*/*.vo "$D"/*/*.vok "$D"/*/*.vos "$D"/*/*.glob "$D"/out.log
rm -rf "$D"/forged

for dir in honest donor; do
  for f in Lib Client; do
    $coqc -noinit -R "$D/$dir" LabelAlias "$D/$dir/$f.v"
  done
done

# chk <dir> <mode>: rocqchk on LabelAlias.Lib and LabelAlias.Client in <dir>,
# as a grader runs it or with the default options.
chk() {
  case $2 in
    grader) "$BIN"rocqchk -o -bytecode-compiler yes -R "$1" LabelAlias -norec LabelAlias.Lib LabelAlias.Client ;;
    default) "$BIN"rocqchk -R "$1" LabelAlias LabelAlias.Lib LabelAlias.Client ;;
  esac > "$D/out.log" 2>&1
}

for mode in grader default; do
  if ! chk "$D/honest" $mode; then
    echo "rocqchk ($mode) refused the honest libraries"
    cat "$D/out.log"
    exit 1
  fi
done

F="$D/forged"
mkdir "$F"
ocaml "$D/forge.ml" label "$D/honest/Lib.vo" "$F/Lib.vo"
# The client as coqc compiled it against donor/Lib.v, recording the forged
# Lib.vo as its dependency.
ocaml "$D/forge.ml" client "$D/donor/Client.vo" "$F/Lib.vo" LabelAlias.Lib "$F/Client.vo"

for mode in grader default; do
  if chk "$F" $mode; then
    echo "rocqchk ($mode) accepted a forged alias that changes its label and a closed proof of False"
    cat "$D/out.log"
    exit 1
  fi
  # 9.2's rocqchk has no printer for a module typing error and reports the
  # exception itself (see misc/rocqchk_delta_alias.sh).
  if ! grep -Eq "Module typing error|ModuleTypingError" "$D/out.log"; then
    echo "unexpected rocqchk ($mode) failure for a forged alias that changes its label"
    cat "$D/out.log"
    exit 1
  fi
done
