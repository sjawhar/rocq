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
# the client's T asks for. With the term of the hint dropped, these checks
# compare M.d or A.d, which is true, with the bound b: rocqchk must refuse
# each corrupted pair with a module typing error.

set -e

. misc/rocqchk_forge_common.bash

D=misc/rocqchk-inline-hint
forgery="a forged inline hint"

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
    for mode in grader default; do
      mode_args $mode "$C/$v" InlineHint Client
      $check "$c" "${mode_argv[@]}"
    done
  done
done

# The forged library of case sealed holds the unsound sealing by itself. That
# of case functor does not: only the client applies F to A.
refuses sealed -R "$D/sealed/forged" InlineHint -norec InlineHint.Lib
