#!/usr/bin/env bash

# rocqchk must not accept a serialized module signature whose delta resolver
# makes a declared-only field (a Parameter) an alias of another one. With c
# and d declared in the type of a sealed module M, an alias of M.d to M.c
# proves False, although M's implementation has c := true and d := false. The
# same holds for an alias that keeps its label (M2.c to M1.c) and for an alias
# in the type of a functor's parameter. The aliases of cases sealed (M.d to
# M.c) and functor (X.d to X.c) change label, so the label test of
# Subtyping.check_constant_alias refuses them first; only case cross reaches
# its refusal of an alias whose body is not a definition. See
# misc/rocqchk_delta_alias.sh for forged aliases of definitions.

set -e

. misc/rocqchk_forge_common.bash

D=misc/rocqchk-sigalias

rm -f "$D"/*/*.vo "$D"/*/*.vok "$D"/*/*.vos "$D"/*/*.glob "$D"/out.log
rm -rf "$D"/forged-sealed "$D"/forged-cross "$D"/forged-functor

for f in Lib Client; do
  $coqc -noinit -R "$D/honest" SigAlias "$D/honest/$f.v"
done
for f in Lib Sealed Cross Functor; do
  $coqc -noinit -R "$D/donor" SigAlias "$D/donor/$f.v"
done

# SigAlias.Lib and SigAlias.<client>, as a grader runs rocqchk and with the
# default options.
for mode in grader default; do
  mode_args $mode "$D/honest" SigAlias Client
  must_accept "$D/out.log" "rocqchk ($mode) refused the honest libraries" "${mode_argv[@]}"
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
    mode_args $mode "$F" SigAlias $client
    must_refuse "$D/out.log" "$typing_error" \
      "rocqchk ($mode) accepted a forged $kind alias between declared-only fields and a closed proof of False" \
      "unexpected rocqchk ($mode) failure for a forged $kind alias" "${mode_argv[@]}"
  done
done
