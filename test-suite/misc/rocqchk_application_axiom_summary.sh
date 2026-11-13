#!/usr/bin/env bash
# The Axioms section of rocqchk -o and Print Assumptions must name the same
# constants for a proof that goes through a functor application: an axiom of
# the functor's body under the application's name, wherever the application
# is, and no field the body defines, even where the application's type
# declares it as a parameter. A name only one of the two accounts prints
# fails the BET grader's join by name.
#
# The shapes are the ones output-coqchk/application_axiom_summary.v
# declares, read here through the other account: that file pins the whole
# summary under -norec, and this test runs Print Assumptions over each of its
# proofs and then checks each name of two lists in both accounts, the axioms
# both must name and the fields neither may, under a recursive check as well,
# where the library is read as a dependency. The functors' own names, F.in_f
# and the like, must appear in neither.
set -eu
export PATH="$BIN:$PATH"

src=output-coqchk/application_axiom_summary.v
lib=application_axiom_summary

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
cp "$src" "$d/"

proofs="boom boom_opaque boom_ascribed boom_inner boom_sub boom_local
        boom_sealed_functor uses_r uses_r2 uses_r3 uses_r4 uses_r5 uses_r6
        uses_r7"
{
  echo "Require $lib."
  for p in $proofs; do echo "Print Assumptions $lib.$p."; done
} > "$d/Use.v"
rocq c -native-compiler no -R "$d" "" "$d/$lib.v"
rocq c -native-compiler no -R "$d" "" "$d/Use.v" > "$d/pa.log" 2>&1

# Print one summary section: its "* <title>" line and the lines under it, up to
# the next "* " bullet. awk's index() takes the title literally.
section() { awk -v h="* $1" 'index($0, h) == 1 { p = 1; print; next } p && /^\* / { exit } p { print }' "$2"; }

# Each axiom both accounts must name.
assumed="$lib.S.App.in_f $lib.SOpaque.App.in_f $lib.SAscribed.App.in_g
         $lib.SNested.Inner.App.in_f $lib.SNested.Sub.App.in_g
         $lib.SLocal.App.in_h $lib.SSealedFunctor.App.in_k $lib.R6.hidden
         $lib.R7.e"
# Each field a functor defines, and each functor's own name for an axiom of
# its body: neither account names them.
defined="$lib.R.e $lib.R2.e $lib.R3.e $lib.R4.e $lib.R5.Y.e $lib.R6.e
         $lib.SAscribed.App.use_f $lib.SNested.Sub.App.use_f
         $lib.SSealedFunctor.App.use_f $lib.F.in_f $lib.G.in_g $lib.K.in_k
         $lib.SLocal.H.in_h"

for name in $assumed; do
  if ! grep -q "^$name : " "$d/pa.log"; then
    echo "Print Assumptions did not name $name"; cat "$d/pa.log"; exit 1
  fi
done
for name in $defined; do
  if grep -q "^$name : " "$d/pa.log"; then
    echo "Print Assumptions named $name"; exit 1
  fi
done

for args in "Use" "-norec $lib"; do
  # shellcheck disable=SC2086
  rocqchk -o -silent -R "$d" "" $args > "$d/chk.log" 2>&1
  axioms=$(section 'Axioms' "$d/chk.log")
  for name in $assumed; do
    if ! printf '%s\n' "$axioms" | grep -qx "    $name"; then
      echo "the summary did not name $name ($args)"; cat "$d/chk.log"; exit 1
    fi
  done
  for name in $defined; do
    if printf '%s\n' "$axioms" | grep -qx "    $name"; then
      echo "the summary named $name, which Print Assumptions does not ($args)"
      exit 1
    fi
  done
done
