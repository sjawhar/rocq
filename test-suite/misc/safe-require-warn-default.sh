#!/usr/bin/env bash
# The cats of a warn attribute may name a category that CWarnings makes
# itself or treats as special ("default", "none", "all"), list several, give
# the warning name of another list ("a,b" and "a b"), give a warning name that
# a category has, or name a category or a warning that a later deprecation
# makes ("deprecated-since-..." and "deprecated-reference-since-...").
# Compiling such a library or definition, loading the library with Require
# (safe) or Require, and using the definition or the deprecated object must
# exit 0, give the warning and print no anomaly. A category that is the name
# of a plain warning is refused with an error. Every case runs, and each
# failure is named.

export PATH=$BIN:$PATH

rm -rf misc/safe-require-warn-default
mkdir misc/safe-require-warn-default
cd misc/safe-require-warn-default || exit 1

failed=0
fail() { echo "FAILURE: $*"; failed=1; }

# compile <file> [<flags>...]: compile <file> within 120 s into <file>.real,
# print its output, set [rc] and fail on any anomaly.
compile() {
  local f=$1
  shift
  rc=0
  timeout 120 rocq c -R . Top "$@" "$f" > "$f.real" 2>&1 || rc=$?
  cat "$f.real"
  if grep -q Anomaly "$f.real"; then fail "$f${*:+ $*} raised an anomaly"; fi
}

# run <file> <warning categories, or ""> [<flags>...]: <file> must compile,
# and its output must hold the given categories of the warning, when they are
# not empty.
run() {
  local f=$1 cats=$2
  shift 2
  compile "$f" "$@"
  if [ "$rc" != 0 ]; then fail "$f${*:+ $*} exited with $rc"
  elif [ -n "$cats" ] && ! grep -q -F "[$cats]" "$f.real"; then
    fail "$f${*:+ $*} did not give the warning [$cats]"
  fi
}

# library <name> <warning categories> <line>...: a library of these lines,
# required with Require (safe) and with Require, which give the warning.
library() {
  local name=$1 cats=$2
  shift 2
  printf '%s\n' "$@" > "$name.v"
  echo "Require (safe) $name." > "Safe$name.v"
  echo "Require $name." > "Plain$name.v"
  run "$name.v" ""
  run "Safe$name.v" "$cats"
  run "Plain$name.v" "$cats"
  # The grader's flags.
  run "Safe$name.v" "" -w none
}

# definition <name> <cats> <warning categories>: a definition with this warn
# attribute, used in its own file and by clients that require its library
# with Require (safe) and with Require. A safe load gives no warning of a
# definition.
definition() {
  local name=$1 cats=$3
  printf '%s\n' "#[warn(note=\"n\", cats=\"$2\")] Definition d := 0." 'Check d.' > "$name.v"
  printf '%s\n' "Require (safe) $name." "Check Top.$name.d." > "Safe$name.v"
  printf '%s\n' "Require $name." "Check Top.$name.d." > "Plain$name.v"
  run "$name.v" "$cats"
  run "Safe$name.v" ""
  run "Plain$name.v" "$cats"
}

library LDefault warn-library-file-default,warn-library-file,user-warn,default \
  'Attributes warn(note="n", cats="default").'
library LNone warn-library-file-none,warn-library-file,user-warn,default \
  'Attributes warn(note="n", cats="none").'
library LAll warn-library-file-all,warn-library-file,user-warn,default \
  'Attributes warn(note="n", cats="all").'
library LMix warn-library-file-all-default-foo-none,foo,warn-library-file,user-warn,default \
  'Attributes warn(note="n", cats="default, none, all, foo").'
# Two lists that give one warning name share the first one's warning.
library LSameName warn-library-file-a-b,b,a,warn-library-file,user-warn,default \
  'Attributes warn(note="n1", cats="a,b").' 'Attributes warn(note="n2", cats="a b").'
# The second warning's name is a category made by the first one: it is
# given without its categories.
library LCatName warn-library-file,user-warn,default \
  'Attributes warn(note="n1", cats="warn-library-file-x").' 'Attributes warn(note="n2", cats="x").'

definition DDefault default warn-reference-default,warn-reference,user-warn,default
definition DNone none warn-reference-none,warn-reference,user-warn,default
definition DAll all warn-reference-all,warn-reference,user-warn,default

# A library category with the name a later deprecation gives its own
# category: the deprecation uses it.
library LDepSince warn-library-file-deprecated-since-bet,deprecated-since-bet,warn-library-file,user-warn,default \
  'Attributes warn(note="n", cats="deprecated-since-bet").'
deprecated=deprecated-reference-since-bet,deprecated-since-bet,user-warn,deprecated-reference,deprecated,default
printf '%s\n' 'Require (safe) LDepSince.' '#[deprecated(since="bet", note="x")] Definition e := 0.' 'Check e.' > SafeDepSince.v
printf '%s\n' 'Require LDepSince.' '#[deprecated(since="bet", note="x")] Definition e := 0.' 'Check e.' > PlainDepSince.v
run SafeDepSince.v "$deprecated"
run PlainDepSince.v "$deprecated"

# A library category with the name a later deprecation gives its warning:
# the deprecation is given under the name with no since.
library LDepRef warn-library-file-deprecated-reference-since-bet,deprecated-reference-since-bet,warn-library-file,user-warn,default \
  'Attributes warn(note="n", cats="deprecated-reference-since-bet").'
printf '%s\n' 'Require (safe) LDepRef.' '#[deprecated(since="bet", note="x")] Definition e := 0.' 'Check e.' > SafeDepRef.v
printf '%s\n' 'Require LDepRef.' '#[deprecated(since="bet", note="x")] Definition e := 0.' 'Check e.' > PlainDepRef.v
run SafeDepRef.v deprecated-reference,deprecated,default
run PlainDepRef.v deprecated-reference,deprecated,default

# A plain warning is not a category: requiring the library is refused.
echo 'Attributes warn(note="n", cats="require-in-module").' > LWarning.v
echo 'Require (safe) LWarning.' > SafeLWarning.v
echo 'Require LWarning.' > PlainLWarning.v
run LWarning.v ""
for f in SafeLWarning.v PlainLWarning.v; do
  compile "$f"
  if [ "$rc" = 0 ] || [ "$rc" -ge 124 ]; then fail "$f exited with $rc, not an error"
  elif ! grep -q -F 'Cannot use require-in-module as a category name.' "$f.real"; then
    fail "$f did not give the error"
  fi
done

exit "$failed"
