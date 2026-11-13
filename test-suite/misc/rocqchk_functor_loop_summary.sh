#!/usr/bin/env bash

# The -o summary reads a functor application through its functor's body
# (checker/mod_impl.ml), and the applications in that body in turn. rocqchk
# does not check an admitted library, so its functor's body can apply that
# functor again, which coqc never writes: forge.ml makes F's body in the
# honest Loop.v hold Grow := F Loc, whose argument is a module of each
# application, a path that grows at each level, and Same := F X, whose
# arguments are those of the application around it. Reading R := F A must
# still end, keep R.ax, and list a bounded number of names, each R.ax under
# some Grows, or under Same, where the walk stops and lists the parameters of
# F's type instead of its body. The honest library is the control: it lists
# R.ax alone.
set -eu

. misc/rocqchk_summary_common.bash

D=misc/rocqchk-functor-loop
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
mkdir "$d/honest" "$d/forged"
cp "$D/Loop.v" "$d/honest/"

$coqc -noinit -Q "$d/honest" FunctorLoop "$d/honest/Loop.v"
cp "$d/honest/Loop.vo" "$d/forged/"
ocaml "$D/forge.ml" "$d/forged/Loop.vo"

axioms "$d/honest" "$d/honest.log" FunctorLoop Loop > "$d/honest-axioms"
if [ "$(cat "$d/honest-axioms")" != "FunctorLoop.Loop.R.ax" ]; then
  echo "the honest library does not list exactly FunctorLoop.Loop.R.ax"
  cat "$d/honest.log"
  exit 1
fi

axioms "$d/forged" "$d/forged.log" FunctorLoop Loop > "$d/axioms"
if ! grep -qx 'FunctorLoop.Loop.R.ax' "$d/axioms"; then
  echo "the forged library does not list FunctorLoop.Loop.R.ax"
  cat "$d/forged.log"
  exit 1
fi
if grep -v -x 'FunctorLoop\.Loop\.R\(\.Grow\)*\(\.Same\)\?\.ax' "$d/axioms"; then
  echo "the forged library lists a name other than R[.Grow...][.Same].ax"
  exit 1
fi
n=$(wc -l < "$d/axioms")
if [ "$n" -gt 200 ]; then
  echo "the forged library lists $n names"
  exit 1
fi
