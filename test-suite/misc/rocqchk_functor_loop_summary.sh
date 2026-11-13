#!/usr/bin/env bash

# The -o summary reads a functor application through its functor's body
# (checker/mod_impl.ml), and the applications in that body in turn. rocqchk
# does not check an admitted library, so its functor's body can apply that
# functor again, which coqc never writes: forge.ml makes F's body in the
# honest Loop.v hold Grow := F Loc, whose argument is a module of each
# application, a path that grows at each level, and Same := F X, whose
# arguments are those of the application around it. Reading R := F A must
# still end, keep R.ax, name nothing under Same, and list a bounded number
# of the names under Grow. The honest library is the control: it lists R.ax
# alone.
set -eu

D=misc/rocqchk-functor-loop
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
mkdir "$d/honest" "$d/forged"
cp "$D/Loop.v" "$d/honest/"

$coqc -noinit -Q "$d/honest" FunctorLoop "$d/honest/Loop.v"
cp "$d/honest/Loop.vo" "$d/forged/"
ocaml "$D/forge.ml" "$d/forged/Loop.vo"

# axioms <dir> <log>: rocqchk -o with the library admitted, within a time
# limit, then the sorted Axioms section. The caller keeps the standard output,
# so a failure is said on the standard error.
axioms () {
  local R=0
  timeout 120 "$BIN"rocqchk -silent -o -Q "$1" FunctorLoop -admit FunctorLoop.Loop > "$2" 2>&1 || R=$?
  if [ "$R" = 124 ]; then
    echo "rocqchk -o did not end within 120 s on $1" >&2
    exit 1
  elif [ "$R" != 0 ]; then
    echo "rocqchk -o exited with $R on $1" >&2
    cat "$2" >&2
    exit 1
  fi
  sed -n '/^\* Axioms/,/^\* Constants/p' "$2" | sed -n 's/^    //p' | LC_ALL=C sort
}

axioms "$d/honest" "$d/honest.log" > "$d/honest-axioms"
if [ "$(cat "$d/honest-axioms")" != "FunctorLoop.Loop.R.ax" ]; then
  echo "the honest library does not list exactly FunctorLoop.Loop.R.ax"
  cat "$d/honest.log"
  exit 1
fi

axioms "$d/forged" "$d/forged.log" > "$d/axioms"
if ! grep -qx 'FunctorLoop.Loop.R.ax' "$d/axioms"; then
  echo "the forged library does not list FunctorLoop.Loop.R.ax"
  cat "$d/forged.log"
  exit 1
fi
if grep -v -x 'FunctorLoop\.Loop\.R\(\.Grow\)*\.ax' "$d/axioms"; then
  echo "the forged library lists a name other than R.ax and R.Grow...Grow.ax"
  exit 1
fi
n=$(wc -l < "$d/axioms")
if [ "$n" -gt 100 ]; then
  echo "the forged library lists $n names"
  exit 1
fi
