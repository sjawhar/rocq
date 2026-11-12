#!/usr/bin/env bash

# rocqchk must check, as an alias, a canonical name that a module's delta
# resolver gives a declaration of one of its submodules when the submodule's
# own resolver gives another. In each case, the forged Lib.vo adds an alias
# of a declaration of A.X to the resolver of A only, where X's own resolver,
# under which X's declarations are checked, keeps the declaration as it is.
# Applying a functor to A (R : T := F A) substitutes F's body with A's whole
# resolver, so that R.e's type names the alias's target instead, and the
# client proves False:
# - sealed, and sealedAc where A is sealed too: A.X.d -> A.X.c, with A.X.c
#   true, so that R.e : eq bool A.X.d false becomes eq bool A.X.c false. The
#   alias changes label, so the label test of check_constant_alias refuses
#   it;
# - sameLabel: A.X.d -> A.Y.d, with A.Y.d := true declared before A.X. The
#   alias keeps its label, so check_constant_alias refuses it when it
#   compares A.X.d := false with A.Y.d;
# - inductive: A.X.I -> A.Y.I, where A.X.I has no constructor and A.Y.I has
#   one, so that R.e : forall _ : A.X.I, False becomes
#   forall _ : A.Y.I, False; check_inductive_alias refuses it when it
#   compares the two.
# WithModule.v is an honest file where the two resolvers differ and the
# alias is sound.

set -e

D=misc/rocqchk-nested-resolver

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

# Upstream's rocqchk prints a module typing error as "Module typing error"
# (rocq-prover/rocq#22373). 9.2's rocqchk has no printer for it and reports
# the exception itself, "Modops.ModuleTypingError".
refuses() {
  local d=$1
  shift
  if chk "$d" "$@"; then
    echo "rocqchk accepted a forged delta resolver and a closed proof of False ($d): rocqchk $*"
    cat "$D/$d/out.log"
    exit 1
  fi
  if ! grep -Eq "Module typing error|ModuleTypingError" "$D/$d/out.log"; then
    echo "unexpected rocqchk failure for a forged delta resolver ($d): rocqchk $*"
    cat "$D/$d/out.log"
    exit 1
  fi
}

rm -f "$D"/with/*.vo "$D"/with/*.vok "$D"/with/*.vos "$D"/with/*.glob "$D/with/out.log"
$coqc -noinit -R "$D/with" NestedResolver "$D/with/WithModule.v"
accepts with -o -bytecode-compiler yes -R "$D/with" NestedResolver -norec NestedResolver.WithModule
accepts with -R "$D/with" NestedResolver NestedResolver.WithModule

for c in sealed sealedAc sameLabel inductive; do
  case $c in
    sealed|sealedAc) forge=sealed ;;
    sameLabel) forge=same-label ;;
    inductive) forge=inductive ;;
  esac
  C=$D/$c
  rm -rf "$C/forged"
  rm -f "$C"/honest/*.vo "$C"/honest/*.vok "$C"/honest/*.vos "$C"/honest/*.glob \
        "$C"/donor/*.vo "$C"/donor/*.vok "$C"/donor/*.vos "$C"/donor/*.glob \
        "$C/out.log"
  mkdir "$C/forged"

  for v in honest donor; do
    $coqc -noinit -R "$C/$v" NestedResolver "$C/$v/Lib.v"
    $coqc -noinit -R "$C/$v" NestedResolver "$C/$v/Client.v"
  done

  # The forged library, from honest/Lib.vo, and the corrupted client:
  # donor/Client.vo, recording the forged library's checksum.
  ocaml "$D/forge.ml" $forge "$C/honest/Lib.vo" "$C/forged/Lib.vo"
  ocaml "$D/forge.ml" client "$C/donor/Client.vo" "$C/forged/Lib.vo" \
    NestedResolver.Lib "$C/forged/Client.vo"

  for v in honest forged; do
    if [ "$v" = honest ]; then check=accepts; else check=refuses; fi
    # As a grader runs it, and with the default options.
    $check "$c" -o -bytecode-compiler yes -R "$C/$v" NestedResolver \
      -norec NestedResolver.Lib NestedResolver.Client
    $check "$c" -R "$C/$v" NestedResolver NestedResolver.Lib NestedResolver.Client
  done
  refuses "$c" -R "$C/forged" NestedResolver -norec NestedResolver.Lib
done
