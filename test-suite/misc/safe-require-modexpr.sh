#!/usr/bin/env bash
# A module expression over a module or module type of a library loaded with
# Require (safe) is refused with an error, not an anomaly. Such a library
# replays none of its objects, so nothing in it has the substitutive objects
# that a module expression copies. Shapes that need none of them compile, and
# every shape compiles after a plain Require.

export PATH=$BIN:$PATH

cd misc/safe-require-modexpr || exit 1
rm -rf _test
mkdir _test
cp ./*.v _test
cd _test || exit 1

fail=0

# compile EXPECT FILE [PATH]: compile FILE with a time limit and print its
# output. EXPECT is ok (exit 0) or refused (exit 1 and the Require (safe)
# error naming PATH). A line with "Anomaly" fails either way.
compile() {
  local rc=0
  timeout 60 rocq c -R . SafeModExpr "$2" > "$2.log" 2>&1 || rc=$?
  echo "== $2: exit $rc"
  cat "$2.log"
  if grep -q Anomaly "$2.log"; then
    echo "FAIL $2: anomaly"; fail=1
  elif [ "$1" = ok ] && [ "$rc" != 0 ]; then
    echo "FAIL $2: expected exit 0"; fail=1
  elif [ "$1" = refused ] && { [ "$rc" != 1 ] \
      || ! grep -q -F "Cannot use $3 in a module expression" "$2.log" \
      || ! grep -q -F "because library SafeModExpr.M was loaded with Require (safe)." "$2.log"; }; then
    echo "FAIL $2: expected exit 1 and the Require (safe) error for $3"; fail=1
  fi
}

compile ok M.v
compile ok MF.v

# The minimal case, then the same over an Import, a module, a "with"
# constraint, an Include, the library itself, a declared module, a sealed
# module and a functor parameter.
compile refused C.v SafeModExpr.M.N.T
compile refused CImport.v SafeModExpr.M.N.T
compile refused CModule.v SafeModExpr.M.N
compile refused CWith.v SafeModExpr.M.N.T
compile refused CInclude.v SafeModExpr.M.N.T
compile refused CLib.v SafeModExpr.M
compile refused CDeclare.v SafeModExpr.M.N.T
compile refused CSeal.v SafeModExpr.M.N.T
compile refused CFunctor.v SafeModExpr.M.N.T

# A functor applied to a module of the library, a subtyping check against a
# module type of the library, and the printing of a functor of the library.
compile ok SafeOk.v

# Every shape above with a plain Require.
compile ok Plain.v

exit $fail
