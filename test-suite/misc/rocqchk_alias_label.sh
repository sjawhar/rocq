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

. misc/rocqchk_forge_common.bash

D=misc/rocqchk-alias-label

rm -f "$D"/*/*.vo "$D"/*/*.vok "$D"/*/*.vos "$D"/*/*.glob "$D"/out.log
rm -rf "$D"/forged

for dir in honest donor; do
  for f in Lib Client; do
    $coqc -noinit -R "$D/$dir" LabelAlias "$D/$dir/$f.v"
  done
done

# LabelAlias.Lib and LabelAlias.Client, as a grader runs rocqchk and with the
# default options.
for mode in grader default; do
  mode_args $mode "$D/honest" LabelAlias Client
  must_accept "$D/out.log" "rocqchk ($mode) refused the honest libraries" "${mode_argv[@]}"
done

F="$D/forged"
mkdir "$F"
ocaml "$D/forge.ml" label "$D/honest/Lib.vo" "$F/Lib.vo"
# The client as coqc compiled it against donor/Lib.v, recording the forged
# Lib.vo as its dependency.
ocaml "$D/forge.ml" client "$D/donor/Client.vo" "$F/Lib.vo" LabelAlias.Lib "$F/Client.vo"

for mode in grader default; do
  mode_args $mode "$F" LabelAlias Client
  must_refuse "$D/out.log" "$typing_error" \
    "rocqchk ($mode) accepted a forged alias that changes its label and a closed proof of False" \
    "unexpected rocqchk ($mode) failure for a forged alias that changes its label" "${mode_argv[@]}"
done
