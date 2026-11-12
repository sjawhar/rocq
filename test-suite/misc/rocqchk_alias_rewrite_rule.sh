#!/usr/bin/env bash

# rocqchk accepts an honest alias of a module that declares a rewrite rule,
# and refuses an alias whose declared type states a rule its target does not
# have: adding that type to the environment would add the rule.

set -e

D=misc/rocqchk-alias-rewrite-rule

rm -f "$D"/good/*.vo "$D"/good/*.vok "$D"/good/*.vos "$D"/good/*.glob \
      "$D"/bad/*.vo "$D"/bad/*.vok "$D"/bad/*.vos "$D"/bad/*.glob \
      "$D"/out.log

$coqc -noinit -allow-rewrite-rules -R "$D/good" AliasRR "$D/good/Alias.v"
$coqc -noinit -allow-rewrite-rules -R "$D/bad" AliasRR "$D/bad/Alias.v"

if ! "$BIN"rocqchk -R "$D/good" AliasRR AliasRR.Alias > "$D/out.log" 2>&1; then
  echo "rocqchk refused an honest alias of a module with a rewrite rule"
  cat "$D/out.log"
  exit 1
fi

ocaml "$D/forge.ml" "$D/good/Alias.vo" "$D/bad/Alias.vo"

if "$BIN"rocqchk -R "$D/good" AliasRR AliasRR.Alias > "$D/out.log" 2>&1; then
  echo "rocqchk accepted an alias whose type states a rule its target does not have"
  cat "$D/out.log"
  exit 1
fi

# 9.2's rocqchk has no printer for a module typing error and reports the
# exception itself, "Modops.ModuleTypingError".
if ! grep -Eq "Module typing error|ModuleTypingError" "$D/out.log"; then
  echo "unexpected rocqchk failure for the forged alias"
  cat "$D/out.log"
  exit 1
fi
