#!/usr/bin/env bash

# rocqchk accepts an honest alias of a module that declares a rewrite rule,
# and refuses an alias whose declared type states a rule its target does not
# have: adding that type to the environment would add the rule.

set -e

. misc/rocqchk_forge_common.bash

D=misc/rocqchk-alias-rewrite-rule

rm -f "$D"/good/*.vo "$D"/good/*.vok "$D"/good/*.vos "$D"/good/*.glob \
      "$D"/bad/*.vo "$D"/bad/*.vok "$D"/bad/*.vos "$D"/bad/*.glob \
      "$D"/out.log

$coqc -noinit -allow-rewrite-rules -R "$D/good" AliasRR "$D/good/Alias.v"
$coqc -noinit -allow-rewrite-rules -R "$D/bad" AliasRR "$D/bad/Alias.v"

must_accept "$D/out.log" "rocqchk refused an honest alias of a module with a rewrite rule" \
  -R "$D/good" AliasRR AliasRR.Alias

ocaml "$D/forge.ml" "$D/good/Alias.vo" "$D/bad/Alias.vo"

must_refuse "$D/out.log" "$typing_error" \
  "rocqchk accepted an alias whose type states a rule its target does not have" \
  "unexpected rocqchk failure for the forged alias" \
  -R "$D/good" AliasRR AliasRR.Alias
