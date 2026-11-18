#!/usr/bin/env bash
# The checks of rocqchk -compare (dispatch://BET-894, dispatch://BET-901).
#
# Each case is a directory under misc/compare/<case>/:
#
#   challenge/*.v     the task as the agent receives it, proofs Admitted
#   answer/*.v        an honest answer; it must pass
#   bad-<name>/*.v    an answer that must fail: at least one theorem's
#                     verdict is fail, or, with a file `refuse` in bad-<name>/,
#                     the run itself must exit non-zero
#   pre/*.v           optional, libraries bound with -Q under the root Pre,
#                     in pre-order or alphabetically. Shared.vo, when there
#                     is one, is declared pre-checked; Pin.vo is pinned only
#                     by a config that writes @PRECHECKED_PIN@
#   pre-order         optional, the order to compile pre/*.v in
#   shared/*.v        optional, libraries under the root Img, reached
#                     through ROCQPATH and bound by no -Q: they stand for
#                     the IMAGE's own installed libraries, which a test must
#                     neither compile nor write into
#   shared-order      optional, the order to compile shared/*.v in
#   bad-<name>/vendor/*.v
#                     optional, a tree the bad answer binds under a second
#                     root, Vendor, that no challenge file lives under
#   bad-<name>/vendor-root
#                     optional, the root that tree is bound to (default
#                     Vendor)
#   bad-<name>/cwd/*.v
#                     optional, libraries the bad answer leaves in the
#                     directory the comparator runs in, which the load path
#                     binds implicitly under no root
#   config.tmpl       the config, with @SHA256:<file>@ for a challenge
#                     file's digest, @PRECHECKED@ for the pre-checked
#                     array and @PRECHECKED_TOP:<dir>/<file>@ for a further
#                     pre-checked entry, the library Top.<dir>.<file> at the
#                     digest of the challenge's <dir>/<file>.vo (an
#                     unchanged file of the task, which the answer's tree
#                     holds at the same bytes)
#   expected.json     the verdict the honest answer must give; only the
#                     (name, verdict) pairs are compared, because a reason
#                     is prose
#   expected-flags    optional, one flag kind per line that the honest
#                     answer's passing verdict must record
#   expected-flag-object
#                     optional, a regular expression the recorded flag object
#                     of the honest answer must match
#   order             optional, the order to compile the .v files in
#                     (default: alphabetical); an entry <dir>/<file>.v is
#                     copied from each tree's <dir>/ and compiled as the
#                     library Top.<dir>.<file>
#   coqc-flags        optional, in a tree (challenge/, answer/, bad-<name>/,
#                     refuse-<name>/answer/), one line of further coqc flags
#                     for that tree, for example -allow-rewrite-rules;
#                     @ELIM_PLUGIN_DIR@ in it becomes the directory of the
#                     plugin that needs-elim-plugin builds
#   needs-elim-plugin optional, a marker: the case builds the plugin of
#                     misc/unchecked-eliminations, src/elim_flag_plugin.cmxs,
#                     in its own work directory, never in the source
#                     directory, which misc/unchecked-eliminations.sh cleans
#                     while other tests run. A plugin that does not build
#                     fails the case. A tree whose coqc-flags holds
#                     -I @ELIM_PLUGIN_DIR@ loads it with
#                       Declare ML Module "coq-test-suite.elim_flag".
#                     and turns the elimination check off and on with
#                       Unset Test Elimination Checking.
#                       Set Test Elimination Checking.
#   refuse-<name>/    optional, a config the run must refuse with a non-zero
#                     exit and no verdict file: config.json, used as it is,
#                     or config.tmpl, filled like the case's config.tmpl
#   refuse-<name>/expected-reason
#                     optional, extended regular expressions, one per line
#                     and at least one, that the refused run's output must
#                     match
#   refuse-<name>/answer/*.v
#                     optional, the answer the config is refused on, laid
#                     out like answer/ and compiled as answer/ is (its own
#                     coqc-flags, the case's order and pre-checked
#                     libraries), with no vendor or cwd tree; without it,
#                     the honest answer
#   fail-config/expected-reason
#                     optional, a regular expression the failed reason must
#                     match
#   utf8-refusal      optional, a marker: the run must refuse a config whose
#                     bytes are not UTF-8
#   bad-<name>/tolerate-<flag>.tmpl
#                     optional, a config that tolerates <flag>: that bad
#                     answer must pass under it with the flag recorded
#   bad-<name>/expected-reason
#                     optional, regular expressions, one per line, that the
#                     failed verdict must match, or, for a bad answer with
#                     `refuse`, the refused run's output
#
# The runner takes a case name, or runs every case when given none. Each
# `ok` line it prints is one run: a case's honest answer, one of its
# sub-runs (a bad answer, a tolerance, a refused config, fail-config,
# utf8-refusal), a named case (sha256, vos, digest, sibling, norec,
# pre-dep-forged, pre-dep-norec, challenge-missing-dep, challenge-dir-link,
# unchecked-helper, unchecked-admit-closure, shared-xdg, shared-nohome,
# shared-coqpath, shared-user-contrib, same-file-shared,
# same-file-prechecked, prechecked-read-file, prechecked-garbage,
# forgeries), a sub-run of a named case that has several, a form of norec
# or a forgery. A run in which every case passed ends with
#
#   compare.sh: <run> ok, <skipped> skipped, <held> held
#
# where <held> counts the runs the fixture tree holds (of the named case
# alone, when the runner is given one), and fails when <run> and <skipped>
# do not add up to <held>. Only the forgeries are skipped, where their
# trees are not mounted. `compare.sh --count` prints the whole tree's
# <held> and runs nothing.
#
# COMPARE_STRICT=1 also fails a run that skipped anything, or that leaves a
# check out for want of python3 (the parse of a verdict file) or of
# sha256sum (the cross-check of every digest).
#
# COMPARE_KEEP_VERDICTS=<dir> keeps the verdict file of each rocqchk run
# that writes one, as <dir>/<case>/<sub-run>.json, copied before the run's
# checks. <sub-run> is honest, bad-<name>, bad-<name>.tolerate-<flag>,
# bad-<name>.tolerate-<flag>.honest (the honest answer under that
# tolerance), refuse-<name>, fail-config or refuse-invalid-utf8; for the
# named cases, answer (vos, digest), honest (sibling), <form>.honest and
# <form>.bad (norec), forged, prechecked and pinned (pre-dep-forged),
# forged (pre-dep-norec), missing and prechecked (challenge-missing-dep),
# linked-dir and linked-challenge (challenge-dir-link), forged, honest and
# checked-forged (unchecked-helper), closure and split
# (unchecked-admit-closure), answer (shared-xdg, shared-nohome,
# shared-coqpath, shared-user-contrib), linked and unlinked
# (same-file-shared, same-file-prechecked), read-file and honest
# (prechecked-read-file), garbage, directory and honest
# (prechecked-garbage) and <forgery> (forgeries).
#
# The challenge and the answer are compiled from the SAME source layout, at
# the same paths and under the same logical root (Top), which is what the
# grader does: nothing is renamed.

set -eu

: "${BIN:=$(dirname "$(command -v rocq)")/}"
export PATH="$BIN:$PATH"

here=$(cd "$(dirname "$0")" && pwd)
cases_dir="$here/compare"

fail() { >&2 echo "FAILURE: $*"; exit 1; }

# The count (see above): the runs that printed an ok line, and the runs
# skipped.
ran=0
skipped=0
passed() { # <ok line>
  echo "$1"
  ran=$((ran + 1))
}

# A tool that a check needs. Without it the check is left out, unless
# COMPARE_STRICT=1, where leaving a check out fails the run.
have() { # <command>
  command -v "$1" > /dev/null && return
  [ "${COMPARE_STRICT:-}" != 1 ] || fail "no $1, and COMPARE_STRICT=1 leaves no check out"
  return 1
}

# Every rocqchk run is bounded, so a hang fails the suite rather than
# stalling it. COMPARE_TIMEOUT sets the bound.
bounded() { timeout "${COMPARE_TIMEOUT:-120s}" "$@"; }

# A run that timed out (124), could not start (125-127) or died on a signal
# (128 and above) gave no verdict, whatever the case expects of it.
completed() { # <exit code> <log>
  [ "$1" -lt 124 ] && return
  cat "$2" >&2
  fail "rocqchk could not complete (exit $1)"
}

# The (name, verdict) pairs of a verdict file, sorted. A reason is prose and
# is not compared; its presence is.
verdicts() {
  grep -o '"name":"[^"]*","verdict":"[^"]*"' "$1" | sort
}

prelude_vo() {
  local w p
  w=$(rocq -where)
  for p in "$w/theories/Corelib/Init/Prelude.vo" "$w/theories/Init/Prelude.vo"; do
    [ -f "$p" ] && { echo "$p"; return; }
  done
  fail "cannot find Prelude.vo under $w"
}

# The verdict file parses, when a JSON reader is at hand. A reader that is
# not there leaves the check out rather than passing it silently; the suite
# prints which, and COMPARE_STRICT=1 fails instead.
json_valid() {
  if have python3; then
    python3 -c 'import json,sys; json.load(open(sys.argv[1]))' "$1"
  else
    echo "  (no python3: the verdict file is not parsed)" >&2
  fi
}

# A verdict file an earlier run left, which says pass: a run that stops
# before its verdict must remove it, wherever it stops, or a reader takes
# that old verdict for this run's (dispatch://BET-895, P2-1).
seed_stale_verdict() {
  printf '%s\n' '{"format":1,"theorems":[{"name":"Top.A.thm","verdict":"pass","reason":"","axioms":[],"flags":[]}],"declarations":[]}' > "$1"
}

# ---------------------------------------------------------------- sha256
#
# The comparator carries its own SHA-256, because the checker links no
# digest library. It is trusted code, so it is checked against FIPS 180-4's
# vectors and against sha256sum here, and compare.sh compares it with
# sha256sum on every challenge file it builds (see run_case).
case_sha256() {
  local d
  d=$(mktemp -d)
  local n=0
  check_vector() { # <content-producer> <expected>
    n=$((n + 1))
    "$1" > "$d/v$n"
    local got
    got=$(bounded rocqchk -sha256 "$d/v$n")
    [ "$got" = "$2" ] || fail "sha256 vector $n is $got, expected $2"
    if have sha256sum; then
      local ref
      ref=$(sha256sum "$d/v$n" | cut -d' ' -f1)
      [ "$got" = "$ref" ] || fail "sha256 vector $n is $got, sha256sum says $ref"
    fi
  }
  v_empty() { printf ''; }
  v_abc() { printf 'abc'; }
  v_448() { printf 'abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq'; }
  v_896() { printf '%s' 'abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu'; }
  v_million() { for _ in $(seq 1 1000); do printf '%01000d' 0 | tr '0' 'a'; done; }
  check_vector v_empty e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
  check_vector v_abc ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad
  check_vector v_448 248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1
  check_vector v_896 cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1
  check_vector v_million cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0
  # a file of 1 MiB of random bytes, against sha256sum
  if have sha256sum; then
    head -c 1048576 /dev/urandom > "$d/rand"
    local got ref
    got=$(bounded rocqchk -sha256 "$d/rand")
    ref=$(sha256sum "$d/rand" | cut -d' ' -f1)
    [ "$got" = "$ref" ] || fail "sha256 of a random file is $got, sha256sum says $ref"
  fi
  rm -rf "$d"
  passed "ok sha256"
}

# ---------------------------------------------------------------- a case

# The image stand-in: when a case ships shared/, every coqc and rocqchk of
# that case runs with ROCQPATH pointing at a directory holding those
# libraries under the root Img. A -Q would make them the answer's side; the
# image's own libraries are bound by no -Q, and a test must not write into
# the installation it runs against.
rocq_env=()

# The directory of the case's elimination-flag plugin, when the case has
# one (needs-elim-plugin); a tree's coqc-flags reaches it as
# @ELIM_PLUGIN_DIR@.
elim_plugin=""

# Compile every .v of <src> into <dst>, under the logical root Top, with the
# pre-checked library of <pre> on the load path when there is one.
build_tree() {
  local src=$1 dst=$2 pre=$3 order=$4 vendor=${5:-} vroot=${6:-Vendor}
  mkdir -p "$dst"
  cp "$src"/*.v "$dst"/
  local args=(-R "$dst" Top)
  [ -n "$pre" ] && args+=(-R "$pre" Pre)
  [ -n "$vendor" ] && args+=(-R "$vendor" "$vroot")
  # A tree may need a flag of its own, for example -allow-rewrite-rules.
  if [ -f "$src/coqc-flags" ]; then
    local extra
    read -r extra < "$src/coqc-flags"
    if [[ $extra == *"@ELIM_PLUGIN_DIR@"* ]]; then
      [ -n "$elim_plugin" ] \
        || fail "$src/coqc-flags names @ELIM_PLUGIN_DIR@, and the case has no needs-elim-plugin"
      extra=${extra//"@ELIM_PLUGIN_DIR@"/$elim_plugin}
    fi
    args+=($extra)
  fi
  local f
  # A file the order names under a subdirectory is copied from the same
  # subdirectory of the tree.
  for f in $order; do
    case $f in
      */*) mkdir -p "$dst/$(dirname "$f")"; cp "$src/$f" "$dst/$f" ;;
    esac
  done
  for f in $order; do
    (cd "$dst" && "${rocq_env[@]}" coqc "${args[@]}" "$f") || fail "$src/$f does not compile"
  done
}

# The order to compile the .v files of <src> in: the order file of <dir>
# (default: the directory above <src>, the case), else alphabetical.
file_order() {
  local src=$1 dir=${2:-$1/..}
  if [ -f "$dir/order" ]; then
    cat "$dir/order"
  else
    (cd "$src" && ls *.v | sort)
  fi
}

# The config: @SHA256:<file>@ becomes that challenge file's digest,
# @PRECHECKED@ the pre-checked array, @PRECHECKED_PIN@ the entry for
# pre/Pin.vo, which only a config that asks for it pins, and
# @PRECHECKED_TOP:<dir>/<file>@ the entry for the library Top.<dir>.<file>
# at the digest of the challenge's <dir>/<file>.vo.
make_config() {
  local tmpl=$1 chdir=$2 out=$3 pre=$4
  local pre_json=""
  if [ -n "$pre" ] && [ -f "$pre/Shared.vo" ]; then
    local sha
    sha=$(bounded rocqchk -sha256 "$pre/Shared.vo")
    pre_json="{\"library\":\"Pre.Shared\",\"sha256\":\"$sha\"}"
  fi
  local pin_json=""
  if [ -n "$pre" ] && [ -f "$pre/Pin.vo" ]; then
    local pin_sha
    pin_sha=$(bounded rocqchk -sha256 "$pre/Pin.vo")
    pin_json=",{\"library\":\"Pre.Pin\",\"sha256\":\"$pin_sha\"}"
  fi
  local prelude
  prelude=$(prelude_vo)
  local prelude_sha
  prelude_sha=$(bounded rocqchk -sha256 "$prelude")
  local all="{\"library\":\"Corelib.Init.Prelude\",\"sha256\":\"$prelude_sha\"}"
  [ -n "$pre_json" ] && all="$all,$pre_json"
  local text
  text=$(cat "$tmpl")
  local f
  for f in "$chdir"/*.vo; do
    local base sha
    base=$(basename "$f")
    sha=$(bounded rocqchk -sha256 "$f")
    # Every digest the comparator writes into a config is also checked
    # against sha256sum, so a defect in the comparator's SHA-256 cannot hide
    # behind its own agreement with itself.
    if have sha256sum; then
      local ref
      ref=$(sha256sum "$f" | cut -d' ' -f1)
      [ "$sha" = "$ref" ] || fail "rocqchk -sha256 $f is $sha, sha256sum says $ref"
    fi
    text=${text//"@SHA256:$base@"/$sha}
  done
  local zero=0000000000000000000000000000000000000000000000000000000000000000
  text=${text//"@PRECHECKED_BAD@"/"{\"library\":\"Corelib.Init.Prelude\",\"sha256\":\"$zero\"}"}
  text=${text//"@PRECHECKED@"/$all}
  text=${text//"@PRECHECKED_PIN@"/$pin_json}
  local top_path top_sha
  while [[ $text =~ @PRECHECKED_TOP:([A-Za-z0-9_/]+)@ ]]; do
    top_path=${BASH_REMATCH[1]}
    [ -f "$chdir/$top_path.vo" ] || fail "no challenge file $top_path.vo to pre-check"
    top_sha=$(bounded rocqchk -sha256 "$chdir/$top_path.vo")
    if have sha256sum; then
      local top_ref
      top_ref=$(sha256sum "$chdir/$top_path.vo" | cut -d' ' -f1)
      [ "$top_sha" = "$top_ref" ] || fail "rocqchk -sha256 $top_path.vo is $top_sha, sha256sum says $top_ref"
    fi
    local top_lib=${top_path//\//.}
    local top_json=",{\"library\":\"Top.$top_lib\",\"sha256\":\"$top_sha\"}"
    text=${text//"@PRECHECKED_TOP:$top_path@"/$top_json}
  done
  # The standard library's eq is built without -indices-matter, so every
  # honest answer reaches that flag on that object. A tolerated flag names
  # its object, so tolerating it here tolerates nothing of the agent's own.
  text=${text//"@TOLERATED@"/'{"kind": "indices-not-mattering", "object": "Corelib.Init.Logic.eq"}'}
  printf '%s\n' "$text" > "$out"
}

# Run the comparator on one answer tree. Prints the exit code; the verdict
# file is $work/out.json. With a seventh argument, the comparator runs in
# that directory, whose libraries the load path binds implicitly.
run_compare() {
  local work=$1 answer=$2 config=$3 pre=$4 vendor=${5:-} vroot=${6:-Vendor} cwd=${7:-.}
  local args=(-silent -Q "$answer" Top)
  [ -n "$pre" ] && args+=(-Q "$pre" Pre)
  [ -n "$vendor" ] && args+=(-Q "$vendor" "$vroot")
  local libs=()
  local f
  for f in "$answer"/*.vo; do libs+=("Top.$(basename "$f" .vo)"); done
  set +e
  (cd "$cwd" && bounded "${rocq_env[@]}" rocqchk "${args[@]}" -compare "$config" -challenge "$work/challenge" \
    -compare-out "$work/out.json" "${libs[@]}") > "$work/log" 2>&1
  local code=$?
  set -e
  completed "$code" "$work/log"
  echo "$code"
}

# The elimination-flag plugin of misc/unchecked-eliminations, built in
# <dir> from the files its _CoqProject names and nothing else:
# misc/unchecked-eliminations.sh builds and cleans in the source directory
# while other tests run, so a build product found there may be half
# written.
build_elim_plugin() { # <dir> <case name>
  local from="$here/unchecked-eliminations" to=$1 f
  mkdir -p "$to"
  cp "$from/_CoqProject" "$to"/
  while read -r f || [ -n "$f" ]; do
    case $f in ''|-*) continue ;; esac
    mkdir -p "$to/$(dirname "$f")"
    cp "$from/$f" "$to/$f"
  done < "$from/_CoqProject"
  (cd "$to" && export COQBIN="$BIN" && rocq makefile -f _CoqProject -o Makefile \
      && make src/elim_flag_plugin.cmxs) > "$to/build.log" 2>&1 \
    || { cat "$to/build.log" >&2; fail "$2: the elimination-flag plugin does not build"; }
}

# With COMPARE_KEEP_VERDICTS=<dir>, the verdict file a run just wrote is
# kept as <dir>/<case>/<sub-run>.json.
keep_verdict() { # <verdict file> <case> <sub-run>
  [ -n "${COMPARE_KEEP_VERDICTS:-}" ] || return 0
  [ -f "$1" ] || return 0
  mkdir -p "$COMPARE_KEEP_VERDICTS/$2"
  cp "$1" "$COMPARE_KEEP_VERDICTS/$2/$3.json"
}

# Each extended regular expression of <patterns>, one per line, must match
# <file>. A patterns file that holds none fails: it would check nothing.
match_reasons() { # <patterns> <file> <run> <what is matched>
  local reason reason_count=0
  while IFS= read -r reason || [ -n "$reason" ]; do
    [[ $reason =~ [^[:space:]] ]] || continue
    reason_count=$((reason_count + 1))
    grep -Eq -- "$reason" "$2" \
      || { cat "$2"; fail "$3: $4 does not match $reason"; }
  done < "$1"
  [ "$reason_count" -gt 0 ] || fail "$3: expected-reason has no patterns"
}

run_case() {
  local name=$1
  local c="$cases_dir/$name"
  [ -d "$c" ] || fail "no case $name"
  local work
  work=$(mktemp -d)

  # The elimination-flag plugin, when the case's trees load it.
  elim_plugin=""
  if [ -f "$c/needs-elim-plugin" ]; then
    build_elim_plugin "$work/elim-plugin" "$name"
    elim_plugin="$work/elim-plugin/src"
  fi

  # The image stand-in, reached through ROCQPATH and bound by no -Q.
  rocq_env=()
  if [ -d "$c/shared" ]; then
    mkdir -p "$work/rocqpath/Img"
    cp "$c/shared"/*.v "$work/rocqpath/Img"/
    local sorder
    if [ -f "$c/shared-order" ]; then sorder=$(cat "$c/shared-order")
    else sorder=$(cd "$work/rocqpath/Img" && ls *.v | sort); fi
    local sf
    for sf in $sorder; do
      (cd "$work/rocqpath/Img" && ROCQPATH="$work/rocqpath" coqc -Q . Img "$sf") \
        || fail "$name: the image library $sf does not compile"
    done
    rocq_env=(env "ROCQPATH=$work/rocqpath")
  fi

  local pre=""
  if [ -d "$c/pre" ]; then
    pre="$work/pre"
    mkdir -p "$pre"
    cp "$c/pre"/*.v "$pre"/
    local porder
    if [ -f "$c/pre-order" ]; then porder=$(cat "$c/pre-order")
    else porder=$(cd "$pre" && ls *.v | sort); fi
    local pf
    for pf in $porder; do
      (cd "$pre" && "${rocq_env[@]}" coqc -Q . Pre "$pf") \
        || fail "$name: the library $pf does not compile"
    done
  fi

  local order
  order=$(file_order "$c/challenge")
  build_tree "$c/challenge" "$work/challenge" "$pre" "$order"
  make_config "$c/config.tmpl" "$work/challenge" "$work/config.json" "$pre"

  # the honest answer
  local order_a code
  order_a=$(file_order "$c/answer")
  build_tree "$c/answer" "$work/answer" "$pre" "$order_a"
  code=$(run_compare "$work" "$work/answer" "$work/config.json" "$pre")
  keep_verdict "$work/out.json" "$name" honest
  [ "$code" = "0" ] || { cat "$work/log"; fail "$name: the honest answer exits $code"; }
  [ -f "$work/out.json" ] || fail "$name: no verdict file"
  json_valid "$work/out.json" || fail "$name: the verdict file is not valid JSON"
  diff <(verdicts "$work/out.json") <(verdicts "$c/expected.json") \
    || { cat "$work/out.json"; fail "$name: the honest answer's verdicts differ"; }
  if [ -f "$c/expected-flags" ]; then
    local flag
    while IFS= read -r flag; do
      [ -z "$flag" ] && continue
      grep -q "\"kind\":\"$flag\"" "$work/out.json" \
        || { cat "$work/out.json"; fail "$name: the passing verdict does not record $flag"; }
    done < "$c/expected-flags"
  fi
  if [ -f "$c/expected-flag-object" ]; then
    local object
    while IFS= read -r object; do
      [ -z "$object" ] && continue
      grep -Eq -- "$object" "$work/out.json" \
        || { cat "$work/out.json"; fail "$name: the recorded flag object does not match $object"; }
    done < "$c/expected-flag-object"
  fi

  # the answers that must fail
  local bad
  for bad in "$c"/bad-*; do
    [ -d "$bad" ] || continue
    local b
    b=$(basename "$bad")
    local bdir="$work/$b"
    local border
    border=$(file_order "$bad")
    # A bad answer may ship a tree of its own under a SECOND root, bound
    # with -Q and holding no challenge counterpart: a library the answer
    # wrote that the comparator must not take for one of the image's. The
    # root is Vendor, or the name in vendor-root, which a case uses to bind
    # a name the image itself serves.
    local bvendor="" vroot="Vendor"
    if [ -f "$bad/vendor-root" ]; then read -r vroot < "$bad/vendor-root"; fi
    if [ -d "$bad/vendor" ]; then
      bvendor="$work/$b-vendor"
      mkdir -p "$bvendor"
      cp "$bad/vendor"/*.v "$bvendor"/
      local vf
      for vf in $(cd "$bvendor" && ls *.v | sort); do
        (cd "$bvendor" && "${rocq_env[@]}" coqc -R . "$vroot" ${pre:+-R "$pre" Pre} "$vf") \
          || fail "$name/$b: the vendor library $vf does not compile"
      done
    fi
    # A bad answer may also leave libraries in the directory the comparator
    # runs in (bad-<name>/cwd/*.v). The load path binds the working
    # directory implicitly, under no root, so each is found by its bare
    # name; the answer's own build finds them the same way, through
    # ROCQPATH, in front of the image stand-in.
    local bcwd="." saved_env=("${rocq_env[@]}")
    if [ -d "$bad/cwd" ]; then
      bcwd="$work/$b-cwd"
      mkdir -p "$bcwd"
      cp "$bad/cwd"/*.v "$bcwd"/
      local cf
      for cf in $(cd "$bcwd" && ls *.v | sort); do
        (cd "$bcwd" && "${rocq_env[@]}" coqc "$cf") \
          || fail "$name/$b: the working-directory library $cf does not compile"
      done
      if [ -d "$work/rocqpath" ]; then rocq_env=(env "ROCQPATH=$bcwd:$work/rocqpath")
      else rocq_env=(env "ROCQPATH=$bcwd"); fi
    fi
    build_tree "$bad" "$bdir" "$pre" "$border" "$bvendor" "$vroot"
    rocq_env=("${saved_env[@]}")
    # A run that does not complete must leave no verdict behind, whatever
    # file was there before it: here, the honest answer's passing one.
    seed_stale_verdict "$work/out.json"
    code=$(run_compare "$work" "$bdir" "$work/config.json" "$pre" "$bvendor" "$vroot" "$bcwd")
    keep_verdict "$work/out.json" "$name" "$b"
    if [ -f "$bad/refuse" ]; then
      [ "$code" != "0" ] || fail "$name/$b: the run should not have completed"
      [ ! -f "$work/out.json" ] || fail "$name/$b: an earlier verdict file survived the refusal"
      # A refusal that must be a specific one names it, so that the run
      # cannot pass this check by failing for another reason.
      if [ -f "$bad/expected-reason" ]; then
        match_reasons "$bad/expected-reason" "$work/log" "$name/$b" "the refusal"
      fi
    else
      [ "$code" = "0" ] || { cat "$work/log"; fail "$name/$b: the run exits $code"; }
      grep -q '"verdict":"fail"' "$work/out.json" \
        || { cat "$work/out.json"; fail "$name/$b: no theorem failed"; }
      if [ -f "$bad/expected-reason" ]; then
        match_reasons "$bad/expected-reason" "$work/out.json" "$name/$b" "the failure"
      fi
    fi
    passed "  ok $name/$b"
    # A named tolerance is a documented cost: it must turn this exact bad
    # answer into a pass and the verdict must say that it did.
    local tolerate
    for tolerate in "$bad"/tolerate-*.tmpl; do
      [ -f "$tolerate" ] || continue
      local flag
      flag=$(basename "$tolerate" .tmpl)
      flag=${flag#tolerate-}
      make_config "$tolerate" "$work/challenge" "$work/tolerated-config.json" "$pre"
      code=$(run_compare "$work" "$bdir" "$work/tolerated-config.json" "$pre" "$bvendor" "$vroot")
      keep_verdict "$work/out.json" "$name" "$b.tolerate-$flag"
      [ "$code" = "0" ] || { cat "$work/log"; fail "$name/$b/$flag: the run exits $code"; }
      grep -q '"verdict":"pass"' "$work/out.json" \
        && ! grep -q '"verdict":"fail"' "$work/out.json" \
        || { cat "$work/out.json"; fail "$name/$b/$flag: the tolerated answer did not pass"; }
      grep -q "\"kind\":\"$flag\"" "$work/out.json" \
        || { cat "$work/out.json"; fail "$name/$b/$flag: the passing verdict does not record $flag"; }
      passed "  ok $name/$b/$flag"
      code=$(run_compare "$work" "$work/answer" "$work/tolerated-config.json" "$pre")
      keep_verdict "$work/out.json" "$name" "$b.tolerate-$flag.honest"
      [ "$code" = "0" ] || { cat "$work/log"; fail "$name/$b/$flag: the unchanged answer exits $code"; }
      grep -q '"verdict":"pass"' "$work/out.json" \
        && ! grep -q "\"kind\":\"$flag\"" "$work/out.json" \
        || { cat "$work/out.json"; fail "$name/$b/$flag: an unused tolerance was recorded"; }
    done
  done

  # configs that must be refused, on the honest answer or on an answer of
  # their own, laid out like answer/ and compiled as answer/ is (its own
  # coqc-flags, the case's order and pre-checked libraries), with no vendor
  # or cwd tree
  local ref
  for ref in "$c"/refuse-*; do
    [ -d "$ref" ] || continue
    local r rtree="$work/answer"
    r=$(basename "$ref")
    if [ -d "$ref/answer" ]; then
      local rorder
      rorder=$(file_order "$ref/answer" "$c")
      rtree="$work/$r"
      build_tree "$ref/answer" "$rtree" "$pre" "$rorder"
    fi
    seed_stale_verdict "$work/out.json"
    if [ -f "$ref/config.tmpl" ]; then
      make_config "$ref/config.tmpl" "$work/challenge" "$work/bad-config.json" "$pre"
    else
      cp "$ref/config.json" "$work/bad-config.json"
    fi
    code=$(run_compare "$work" "$rtree" "$work/bad-config.json" "$pre")
    keep_verdict "$work/out.json" "$name" "$r"
    [ "$code" != "0" ] || fail "$name/$r: the run should not have completed"
    [ ! -f "$work/out.json" ] || fail "$name/$r: an earlier verdict file survived the refusal"
    # A refusal that must be a specific one names it, so that the run
    # cannot pass this check by failing for another reason.
    if [ -f "$ref/expected-reason" ]; then
      match_reasons "$ref/expected-reason" "$work/log" "$name/$r" "the refusal"
    fi
    passed "  ok $name/$r"
  done

  # A config under which the honest answer must fail, rather than one the
  # comparator refuses.
  local fc
  for fc in "$c"/fail-config; do
    [ -d "$fc" ] || continue
    make_config "$fc/config.tmpl" "$work/challenge" "$work/fail-config.json" "$pre"
    code=$(run_compare "$work" "$work/answer" "$work/fail-config.json" "$pre")
    keep_verdict "$work/out.json" "$name" fail-config
    [ "$code" = "0" ] || { cat "$work/log"; fail "$name/fail-config: the run exits $code"; }
    grep -q '"verdict":"fail"' "$work/out.json" \
      || { cat "$work/out.json"; fail "$name/fail-config: the honest answer passed"; }
    if [ -f "$fc/expected-reason" ]; then
      match_reasons "$fc/expected-reason" "$work/out.json" "$name/fail-config" "the failure"
    fi
    passed "  ok $name/fail-config"
  done

  # A config whose bytes are not UTF-8. It is written here rather than kept
  # as a file, because a repository's text files are UTF-8.
  if [ -f "$c/utf8-refusal" ]; then
    seed_stale_verdict "$work/out.json"
    printf '{"theorems": [{"name": "Top.A.\xff"}], "challenge_files": [{"path": "A.vo", "sha256": "%s"}]}\n' \
      "$(bounded rocqchk -sha256 "$work/challenge/A.vo")" > "$work/bad-config.json"
    code=$(run_compare "$work" "$work/answer" "$work/bad-config.json" "$pre")
    keep_verdict "$work/out.json" "$name" refuse-invalid-utf8
    [ "$code" != "0" ] || fail "$name: a config that is not UTF-8 was accepted"
    [ ! -f "$work/out.json" ] || fail "$name: an earlier verdict file survived the refusal"
    passed "  ok $name/refuse-invalid-utf8"
  fi

  rm -rf "$work"
  passed "ok $name"
}

# ------------------------------------------------- an answer without proofs
#
# A library built with -vos holds no opaque proof. The kernel reaches for a
# body that is not there and the run fails, so such an answer can never be
# graded. The sources are written here: a case directory would hold a tree
# that no other check uses.
case_vos() {
  local work
  work=$(mktemp -d)
  mkdir -p "$work/challenge" "$work/answer"
  printf '%s\n' 'Definition two := 2.' 'Theorem thm : two = 2.' 'Proof.' 'Admitted.' \
    > "$work/challenge/A.v"
  printf '%s\n' 'Definition two := 2.' 'Theorem thm : two = 2.' 'Proof. reflexivity. Qed.' \
    > "$work/answer/A.v"
  (cd "$work/challenge" && coqc -R . Top A.v)
  (cd "$work/answer" && coqc -R . Top -vos A.v)
  # The grader receives .vo files; a -vos build renamed to .vo is the shape
  # an answer without its proofs takes.
  mv "$work/answer/A.vos" "$work/answer/A.vo"
  local sha prelude_sha
  sha=$(bounded rocqchk -sha256 "$work/challenge/A.vo")
  prelude_sha=$(bounded rocqchk -sha256 "$(prelude_vo)")
  printf '%s\n' \
    "{\"theorems\": [{\"name\": \"Top.A.thm\"}], \"tolerated_flags\": [{\"kind\": \"indices-not-mattering\"}]," \
    " \"prechecked\": [{\"library\": \"Corelib.Init.Prelude\", \"sha256\": \"$prelude_sha\"}]," \
    " \"challenge_files\": [{\"path\": \"A.vo\", \"sha256\": \"$sha\"}]}" > "$work/config.json"
  local code
  # The answer's own check stops this run, before any comparison.
  seed_stale_verdict "$work/out.json"
  code=$(run_compare "$work" "$work/answer" "$work/config.json" "")
  keep_verdict "$work/out.json" vos answer
  [ "$code" != "0" ] || { cat "$work/log"; fail "vos: an answer without its proofs was graded"; }
  [ ! -f "$work/out.json" ] || fail "vos: an earlier verdict file survived the refusal"
  rm -rf "$work"
  passed "ok vos"
}

# ------------------------------- the two sides on different shared libraries
#
# The challenge and the answer must record the same digest for a pre-checked
# library. Here the answer is built against another copy of the shared
# library, so the digests differ and the run stops before the challenge
# reaches an environment.
case_digest() {
  local work
  work=$(mktemp -d)
  mkdir -p "$work/pre" "$work/pre2" "$work/challenge" "$work/answer"
  printf '%s\n' 'Definition shared_two : nat := 2.' > "$work/pre/Shared.v"
  printf '%s\n' 'Definition shared_two : nat := 2.' 'Definition extra : nat := 3.' \
    > "$work/pre2/Shared.v"
  (cd "$work/pre" && coqc -R . Pre Shared.v)
  (cd "$work/pre2" && coqc -R . Pre Shared.v)
  printf '%s\n' 'Require Import Pre.Shared.' 'Definition two := shared_two.' \
    'Theorem thm : two = 2.' 'Proof.' 'Admitted.' > "$work/challenge/A.v"
  printf '%s\n' 'Require Import Pre.Shared.' 'Definition two := shared_two.' \
    'Theorem thm : two = 2.' 'Proof. reflexivity. Qed.' > "$work/answer/A.v"
  (cd "$work/challenge" && coqc -R . Top -R "$work/pre" Pre A.v)
  (cd "$work/answer" && coqc -R . Top -R "$work/pre2" Pre A.v)
  local sha pre_sha prelude_sha
  sha=$(bounded rocqchk -sha256 "$work/challenge/A.vo")
  pre_sha=$(bounded rocqchk -sha256 "$work/pre2/Shared.vo")
  prelude_sha=$(bounded rocqchk -sha256 "$(prelude_vo)")
  printf '%s\n' \
    "{\"theorems\": [{\"name\": \"Top.A.thm\"}], \"tolerated_flags\": [{\"kind\": \"indices-not-mattering\"}]," \
    " \"prechecked\": [{\"library\": \"Corelib.Init.Prelude\", \"sha256\": \"$prelude_sha\"}," \
    "   {\"library\": \"Pre.Shared\", \"sha256\": \"$pre_sha\"}]," \
    " \"challenge_files\": [{\"path\": \"A.vo\", \"sha256\": \"$sha\"}]}" > "$work/config.json"
  local code
  seed_stale_verdict "$work/out.json"
  code=$(run_compare "$work" "$work/answer" "$work/config.json" "$work/pre2")
  keep_verdict "$work/out.json" digest answer
  [ "$code" != "0" ] \
    || { cat "$work/log"; fail "digest: the two sides' shared libraries differ and the run passed"; }
  [ ! -f "$work/out.json" ] || fail "digest: an earlier verdict file survived the refusal"
  rm -rf "$work"
  passed "ok digest"
}

# ------------------- a pre-checked library under the answer's own root
#
# The challenge directory stands in for the answer's directory under each
# -R root. A pre-checked library may sit under that same root, in a
# directory of its own; the challenge directory must still stand in, or an
# honest answer cannot be graded at all.
case_sibling() {
  local work
  work=$(mktemp -d)
  mkdir -p "$work/shared" "$work/challenge" "$work/answer"
  printf '%s\n' 'Definition shared_two : nat := 2.' > "$work/shared/Lib.v"
  (cd "$work/shared" && coqc -R . Top Lib.v)
  printf '%s\n' 'Require Import Top.Lib.' 'Definition two := shared_two.' \
    'Theorem thm : two = 2.' 'Proof.' 'Admitted.' > "$work/challenge/A.v"
  printf '%s\n' 'Require Import Top.Lib.' 'Definition two := shared_two.' \
    'Theorem thm : two = 2.' 'Proof. reflexivity. Qed.' > "$work/answer/A.v"
  (cd "$work/challenge" && coqc -R . Top -R "$work/shared" Top A.v)
  (cd "$work/answer" && coqc -R . Top -R "$work/shared" Top A.v)
  local sha lib_sha prelude_sha
  sha=$(bounded rocqchk -sha256 "$work/challenge/A.vo")
  lib_sha=$(bounded rocqchk -sha256 "$work/shared/Lib.vo")
  prelude_sha=$(bounded rocqchk -sha256 "$(prelude_vo)")
  printf '%s\n' \
    "{\"theorems\": [{\"name\": \"Top.A.thm\"}]," \
    " \"tolerated_flags\": [{\"kind\": \"indices-not-mattering\", \"object\": \"Corelib.Init.Logic.eq\"}]," \
    " \"prechecked\": [{\"library\": \"Corelib.Init.Prelude\", \"sha256\": \"$prelude_sha\"}," \
    "   {\"library\": \"Top.Lib\", \"sha256\": \"$lib_sha\"}]," \
    " \"challenge_files\": [{\"path\": \"A.vo\", \"sha256\": \"$sha\"}]}" > "$work/config.json"
  set +e
  bounded rocqchk -silent -R "$work/answer" Top -R "$work/shared" Top \
    -compare "$work/config.json" -challenge "$work/challenge" \
    -compare-out "$work/out.json" Top.A > "$work/log" 2>&1
  local code=$?
  set -e
  completed "$code" "$work/log"
  keep_verdict "$work/out.json" sibling honest
  [ "$code" = "0" ] || { cat "$work/log"; fail "sibling: an honest answer exits $code"; }
  grep -q '"verdict":"pass"' "$work/out.json" \
    || { cat "$work/out.json"; fail "sibling: the honest answer did not pass"; }
  rm -rf "$work"
  passed "ok sibling"
}

# ------------------------- the answer libraries named only by -norec
#
# The grading side names each answer library with -norec and nothing
# positionally: check exactly these, load the rest. That selection must
# reach the same verdict as the positional one, so the case runs both
# forms over the same trees -- an honest answer, which must pass, and a
# wrong one, which must not. Before the fix of dispatch://BET-901 the
# -norec arm named no root for the challenge directory to stand in for,
# so the first challenge file failed to intern and no verdict was
# written at all.
#
# The libraries sit under a root with a dotted prefix and in
# subdirectories, the shape a task tree takes (-Q tree Top, Sub/B.v).
#
# The forms, which the count reads too.
norec_forms=(norec positional)

case_norec() {
  local work
  work=$(mktemp -d)
  local side
  for side in challenge answer bad; do
    mkdir -p "$work/$side/SubA" "$work/$side/SubB"
    printf '%s\n' 'Definition two : nat := 2.' > "$work/$side/SubA/Defs.v"
  done
  printf '%s\n' 'Require Import Top.SubA.Defs.' \
    'Theorem thm : two = 2.' 'Proof.' 'Admitted.' > "$work/challenge/SubB/Proof.v"
  printf '%s\n' 'Require Import Top.SubA.Defs.' \
    'Theorem thm : two = 2.' 'Proof. reflexivity. Qed.' > "$work/answer/SubB/Proof.v"
  # A wrong answer: the theorem is there under the right name, with another
  # statement. The comparator must not pass it.
  printf '%s\n' 'Require Import Top.SubA.Defs.' \
    'Theorem thm : two = two.' 'Proof. reflexivity. Qed.' > "$work/bad/SubB/Proof.v"
  for side in challenge answer bad; do
    (cd "$work/$side" && coqc -R . Top SubA/Defs.v) \
      || fail "norec: $side/Defs.v does not compile"
    (cd "$work/$side" && coqc -R . Top SubB/Proof.v) \
      || fail "norec: $side/Proof.v does not compile"
  done
  local spec_sha proof_sha prelude_sha
  spec_sha=$(bounded rocqchk -sha256 "$work/challenge/SubA/Defs.vo")
  proof_sha=$(bounded rocqchk -sha256 "$work/challenge/SubB/Proof.vo")
  prelude_sha=$(bounded rocqchk -sha256 "$(prelude_vo)")
  printf '%s\n' \
    "{\"theorems\": [{\"name\": \"Top.SubB.Proof.thm\"}]," \
    " \"tolerated_flags\": [{\"kind\": \"indices-not-mattering\", \"object\": \"Corelib.Init.Logic.eq\"}]," \
    " \"prechecked\": [{\"library\": \"Corelib.Init.Prelude\", \"sha256\": \"$prelude_sha\"}]," \
    " \"challenge_files\": [{\"path\": \"SubA/Defs.vo\", \"sha256\": \"$spec_sha\"}," \
    "   {\"path\": \"SubB/Proof.vo\", \"sha256\": \"$proof_sha\"}]}" > "$work/config.json"

  # <selection-form> <answer tree> -> prints the exit code, verdict in out.json
  norec_run() {
    local form=$1 tree=$2
    local sel=()
    case "$form" in
      norec) sel=(-norec Top.SubA.Defs -norec Top.SubB.Proof) ;;
      positional) sel=(Top.SubA.Defs Top.SubB.Proof) ;;
    esac
    seed_stale_verdict "$work/out.json"
    set +e
    bounded rocqchk -silent -Q "$tree" Top -compare "$work/config.json" \
      -challenge "$work/challenge" -compare-out "$work/out.json" "${sel[@]}" \
      > "$work/log" 2>&1
    local code=$?
    set -e
    completed "$code" "$work/log"
    echo "$code"
  }

  local form code
  for form in "${norec_forms[@]}"; do
    code=$(norec_run "$form" "$work/answer")
    keep_verdict "$work/out.json" norec "$form.honest"
    [ "$code" = "0" ] || { cat "$work/log"; fail "norec/$form: the honest answer exits $code"; }
    [ -f "$work/out.json" ] || fail "norec/$form: no verdict file"
    grep -q '"verdict":"pass"' "$work/out.json" \
      || { cat "$work/out.json"; fail "norec/$form: the honest answer did not pass"; }
    code=$(norec_run "$form" "$work/bad")
    keep_verdict "$work/out.json" norec "$form.bad"
    if [ "$code" = "0" ]; then
      grep -q '"verdict":"fail"' "$work/out.json" \
        || { cat "$work/out.json"; fail "norec/$form: the wrong answer did not fail"; }
    else
      [ ! -f "$work/out.json" ] || fail "norec/$form: a verdict file was written anyway"
    fi
    passed "  ok norec/$form"
  done
  rm -rf "$work"
  passed "ok norec"
}

# ------------------------------------------------ the libraries a run reads
#
# The named cases below test which library files a -compare run reads, and
# how: what a pre-checked library rests on (pre-dep-*), where the
# challenge's libraries are read from (challenge-*), the answer's libraries
# loaded without a check (unchecked-*), the directories a shared library may
# come from (shared-*), the same file on both sides (same-file-*) and the
# file a pre-checked library is read from (prechecked-*). Each needs -norec,
# -admit, a link, an environment variable or a patched file, so each runs
# rocqchk itself (named_compare). A case runs first its one run whose
# outcome these rules decide, so that the case run with a rocqchk that
# lacks them stops on that run; its other runs, which pass or which the
# kernel refuses, follow. Each case keeps its files under one directory of
# its own and removes it at the end. Every link a case makes points inside
# that directory, so none leaves a file system, but one: the theories link
# of shared-user-contrib points to the corelib of the installation in use.
#
# The cases, which the count and the runner read too.
library_cases=(pre-dep-forged pre-dep-norec challenge-missing-dep challenge-dir-link
  unchecked-helper unchecked-admit-closure shared-xdg shared-nohome shared-coqpath
  shared-user-contrib same-file-shared same-file-prechecked prechecked-read-file
  prechecked-garbage)

# Whether <name> is one of library_cases.
is_library_case() { # <name>
  local c
  for c in "${library_cases[@]}"; do
    [ "$c" = "$1" ] && return 0
  done
  return 1
}

# <command>... run in <dir>; a command that fails fails <run>.
in_dir() { # <run> <dir> <command>...
  local run=$1 dir=$2
  shift 2
  (cd "$dir" && "$@") || fail "$run: $* fails in $dir"
}

# A JSON object that pins <file> by its sha256, with <key> (path or library)
# set to <name>.
pin_entry() { # <key> <name> <file>
  local sha
  sha=$(bounded rocqchk -sha256 "$3")
  printf '{"%s": "%s", "sha256": "%s"}' "$1" "$2" "$sha"
}

# The config of a named case: the theorem <theorem>, the challenge files
# <files>, the pre-checked libraries <pre> after the Prelude, which every
# such config pre-checks, and the permitted axioms <axioms>; each list is
# the members of a JSON array. eq's indices-not-mattering is tolerated, as
# in the cases above.
named_config() { # <out> <theorem> <files> [<pre>] [<axioms>]
  local prelude_sha
  prelude_sha=$(bounded rocqchk -sha256 "$(prelude_vo)")
  printf '%s\n' \
    "{\"theorems\": [{\"name\": \"$2\"}], \"permitted_axioms\": [${5:-}]," \
    " \"tolerated_flags\": [{\"kind\": \"indices-not-mattering\", \"object\": \"Corelib.Init.Logic.eq\"}]," \
    " \"prechecked\": [{\"library\": \"Corelib.Init.Prelude\", \"sha256\": \"$prelude_sha\"}${4:+, $4}]," \
    " \"challenge_files\": [$3]}" > "$1"
}

# rocqchk -compare <config> -challenge <challenge>, run in <dir>, with
# <argument>..., which bind the answer and name its libraries. Its output is
# <w>/log and its verdict <w>/out.json. Prints the exit code.
named_compare() { # <w> <dir> <config> <challenge> <argument>...
  local w=$1 dir=$2 config=$3 challenge=$4
  shift 4
  set +e
  (cd "$dir" && bounded rocqchk -silent -compare "$config" -challenge "$challenge" \
    -compare-out "$w/out.json" "$@") > "$w/log" 2>&1
  local code=$?
  set -e
  completed "$code" "$w/log"
  echo "$code"
}

# The run <run> was refused: it exits non-zero, the verdict file seeded
# before it (seed_stale_verdict) is gone, and its output matches each
# extended regular expression <pattern>, which ties the library refused to
# the rule's text. A run that completed fails with its verdicts.
expect_refused() { # <run> <code> <w> <pattern>...
  local run=$1 code=$2 w=$3
  shift 3
  if [ "$code" = 0 ]; then
    cat "$w/out.json" 2> /dev/null
    fail "$run: the run completed (exit 0, $(verdicts "$w/out.json" 2> /dev/null | paste -sd ' ' -)), where it must be refused"
  fi
  [ ! -f "$w/out.json" ] || fail "$run: an earlier verdict file survived the refusal"
  printf '%s\n' "$@" > "$w/expected-reason"
  match_reasons "$w/expected-reason" "$w/log" "$run" "the refusal"
}

# The run <run> passed: it exits 0 and writes a verdict file that parses, in
# which every theorem passes; with <admitted>, the file ends with the member
# "admitted":<admitted>, exactly.
expect_pass() { # <run> <code> <w> [<admitted>]
  local run=$1 code=$2 w=$3
  [ "$code" = 0 ] || { cat "$w/log"; fail "$run: the run exits $code"; }
  [ -f "$w/out.json" ] || fail "$run: no verdict file"
  json_valid "$w/out.json" || fail "$run: the verdict file is not valid JSON"
  grep -q '"verdict":"pass"' "$w/out.json" && ! grep -q '"verdict":"fail"' "$w/out.json" \
    || { cat "$w/out.json"; fail "$run: the answer did not pass"; }
  if [ $# -gt 3 ]; then
    local verdict
    verdict=$(cat "$w/out.json")
    [[ $verdict == *"\"admitted\":$4}" ]] \
      || { cat "$w/out.json"; fail "$run: the verdict does not end with \"admitted\":$4}"; }
  fi
}

# The bytes of a .vo file. It starts with 16 bytes: its magic number, its
# version and the position of its table of segments. That table holds the
# number of segments (4 bytes), then for each the length of its name (4
# bytes), the name, the segment's position (8 bytes), its length (8 bytes)
# and the MD5 of its data, which also follows the data. The MD5 of the
# segment named library is the library's digest, the one each library that
# depends on it records. od may end its output with an empty line (BSD od
# does), so awk folds every byte it reads into one number.
number_at() { # <file> <offset> <count>: the big-endian number of <count> bytes at <offset>
  od -An -tu1 -j"$2" -N"$3" "$1" | awk '{ for (i = 1; i <= NF; i++) n = n * 256 + $i } END { print n }'
}

# Sets summary_md5 and data_md5 to the offsets of the two copies of the MD5
# of the segment <segment> of <file>: in the table of segments, and after
# the segment's data.
segment_md5() { # <file> <segment>
  local f=$1 at n nlen pos len
  at=$(number_at "$f" 8 8)
  n=$(number_at "$f" "$at" 4)
  at=$((at + 4))
  while [ "$n" -gt 0 ]; do
    nlen=$(number_at "$f" "$at" 4)
    if [ "$(dd if="$f" bs=1 skip=$((at + 4)) count="$nlen" 2> /dev/null)" = "$2" ]; then
      pos=$(number_at "$f" $((at + 4 + nlen)) 8)
      len=$(number_at "$f" $((at + 12 + nlen)) 8)
      summary_md5=$((at + 20 + nlen))
      data_md5=$((pos + len))
      return
    fi
    at=$((at + 36 + nlen))
    n=$((n - 1))
  done
  fail "$f has no segment $2"
}

copy_md5() { # <from> <offset> <to> <offset>: 16 bytes
  dd if="$1" bs=1 skip="$2" count=16 2> /dev/null | dd of="$3" bs=1 seek="$4" conv=notrunc 2> /dev/null
}

# <forged>, a library compiled from another source, made to state the
# digest of <honest>: both copies of the MD5 of its library segment become
# <honest>'s. A read compares the two copies with each other, and the
# digest a library records for its dependency with the first, so every
# library compiled against <honest> takes <forged> for it. Only the sha256
# of the whole file tells the two apart.
forge_digest() { # <honest .vo> <forged .vo>
  local from
  segment_md5 "$1" library
  from=$summary_md5
  segment_md5 "$2" library
  copy_md5 "$1" "$from" "$2" "$summary_md5"
  copy_md5 "$1" "$from" "$2" "$data_md5"
}

# ------------------------------ what a pre-checked library rests on
#
# The challenge (ch) holds Top.D, which defines d := 0; Top.P, which
# Requires it and proves d_zero : Top.D.d = 0; and Top.A, whose thm states
# Top.D.d = 0. The config pre-checks Top.P at the challenge's P.vo. The
# answer (answer) holds the challenge's D.vo and P.vo and an A that proves
# thm by Top.P.d_zero. The forged answer (forged) is the answer with another
# D.vo, compiled from d := 1 and made to state the digest of the
# challenge's (forge_digest), the one P records. Against that D, d_zero and
# thm both say 1 = 0, and the kernel check of A accepts its proof all the
# same: P was typed against the challenge's D, and no run checks P.
predep_trees() { # <w> <run>
  local w=$1 run=$2 f
  mkdir -p "$w/ch" "$w/answer" "$w/other" "$w/forged"
  printf '%s\n' 'Definition d : nat := 0.' > "$w/ch/D.v"
  printf '%s\n' 'Require Top.D.' 'Lemma d_zero : Top.D.d = 0.' 'Proof. reflexivity. Qed.' \
    > "$w/ch/P.v"
  printf '%s\n' 'Require Top.D Top.P.' 'Theorem thm : Top.D.d = 0.' 'Proof.' 'Admitted.' \
    > "$w/ch/A.v"
  for f in D.v P.v A.v; do in_dir "$run" "$w/ch" coqc -R . Top "$f"; done
  cp "$w/ch/D.vo" "$w/ch/P.vo" "$w/answer/"
  printf '%s\n' 'Require Top.D Top.P.' 'Theorem thm : Top.D.d = 0.' \
    'Proof. exact Top.P.d_zero. Qed.' > "$w/answer/A.v"
  in_dir "$run" "$w/answer" coqc -R . Top A.v
  printf '%s\n' 'Definition d : nat := 1.' > "$w/other/D.v"
  in_dir "$run" "$w/other" coqc -R . Top D.v
  cp "$w/answer/A.vo" "$w/answer/P.vo" "$w/other/D.vo" "$w/forged/"
  forge_digest "$w/ch/D.vo" "$w/forged/D.vo"
}

# The refusal of the forged D, which both cases expect.
predep_reason="The pre-checked library Top\.P depends on the library Top\.D, which is neither pre-checked by the config, nor pinned by its sha256 as a challenge file, nor the image's own\."

# pre-dep-forged: Top.A named alone, so the forged D loads without a check,
# through P's closure: refused, naming P and D. Then the answer, with the
# challenge's D pre-checked as well (the verdict's admitted is empty,
# though the config pre-checks D and P besides the Prelude), and with that
# D pinned by its sha256 as a challenge file instead: both pass.
case_pre_dep_forged() {
  local w c=pre-dep-forged code a p d
  w=$(mktemp -d)
  predep_trees "$w" "$c"
  a=$(pin_entry path A.vo "$w/ch/A.vo")
  p=$(pin_entry library Top.P "$w/ch/P.vo")
  named_config "$w/config.json" Top.A.thm "$a" "$p"
  seed_stale_verdict "$w/out.json"
  code=$(named_compare "$w" "$w" "$w/config.json" "$w/ch" -Q "$w/forged" Top Top.A)
  keep_verdict "$w/out.json" "$c" forged
  expect_refused "$c/forged" "$code" "$w" "$predep_reason"
  passed "  ok $c/forged"
  d=$(pin_entry library Top.D "$w/ch/D.vo")
  named_config "$w/config.json" Top.A.thm "$a" "$p, $d"
  rm -f "$w/out.json"
  code=$(named_compare "$w" "$w" "$w/config.json" "$w/ch" -Q "$w/answer" Top Top.A)
  keep_verdict "$w/out.json" "$c" prechecked
  expect_pass "$c/prechecked" "$code" "$w" '[]'
  passed "  ok $c/prechecked"
  d=$(pin_entry path D.vo "$w/ch/D.vo")
  named_config "$w/config.json" Top.A.thm "$a, $d" "$p"
  rm -f "$w/out.json"
  code=$(named_compare "$w" "$w" "$w/config.json" "$w/ch" -Q "$w/answer" Top Top.A)
  keep_verdict "$w/out.json" "$c" pinned
  expect_pass "$c/pinned" "$code" "$w"
  passed "  ok $c/pinned"
  rm -rf "$w"
  passed "ok $c"
}

# pre-dep-norec: the forged D named with -norec, and A with it, so the run
# checks D: it is sound by itself, but P holds a term typed against the
# challenge's D, and the run is refused all the same, naming P and D.
case_pre_dep_norec() {
  local w c=pre-dep-norec code a p
  w=$(mktemp -d)
  predep_trees "$w" "$c"
  a=$(pin_entry path A.vo "$w/ch/A.vo")
  p=$(pin_entry library Top.P "$w/ch/P.vo")
  named_config "$w/config.json" Top.A.thm "$a" "$p"
  seed_stale_verdict "$w/out.json"
  code=$(named_compare "$w" "$w" "$w/config.json" "$w/ch" -Q "$w/forged" Top \
    -norec Top.D -norec Top.A)
  keep_verdict "$w/out.json" "$c" forged
  expect_refused "$c" "$code" "$w" "$predep_reason"
  rm -rf "$w"
  passed "ok $c"
}

# --------------------- the challenge's libraries from the challenge directory
#
# challenge-missing-dep: the challenge directory holds A.vo alone, whose thm
# states Top.D.d = 1 of the D it was compiled against, which defines
# d := 0. The answer's D.vo is compiled from d := 1 and made to state that
# D's digest (forge_digest), and the answer's A, compiled against the
# challenge's D, proves thm by eq_refl 1 under Skip Qed Typecheck: a proof
# the kernel accepts against the answer's D alone. The challenge load finds
# no D.vo in the challenge directory and reads the answer's, which the run
# would then compare with itself: refused, naming D. Then the same, with D
# pre-checked at the sha256 of the answer's D.vo: the config vouches for
# those bytes, both sides read them, and the run passes.
case_challenge_missing_dep() {
  local w c=challenge-missing-dep code a d
  w=$(mktemp -d)
  mkdir -p "$w/src" "$w/ch" "$w/answer" "$w/other"
  printf '%s\n' 'Definition d : nat := 0.' > "$w/src/D.v"
  printf '%s\n' 'Require Top.D.' 'Theorem thm : Top.D.d = 1.' 'Proof.' 'Admitted.' > "$w/src/A.v"
  in_dir "$c" "$w/src" coqc -R . Top D.v
  in_dir "$c" "$w/src" coqc -R . Top A.v
  cp "$w/src/A.vo" "$w/ch/"
  cp "$w/src/D.vo" "$w/answer/"
  printf '%s\n' 'Require Top.D.' 'Set Skip Qed Typecheck.' 'Theorem thm : Top.D.d = 1.' \
    'Proof. exact_no_check (eq_refl 1). Qed.' > "$w/answer/A.v"
  in_dir "$c" "$w/answer" coqc -R . Top A.v
  printf '%s\n' 'Definition d : nat := 1.' > "$w/other/D.v"
  in_dir "$c" "$w/other" coqc -R . Top D.v
  cp "$w/other/D.vo" "$w/answer/D.vo"
  forge_digest "$w/src/D.vo" "$w/answer/D.vo"
  a=$(pin_entry path A.vo "$w/ch/A.vo")
  named_config "$w/config.json" Top.A.thm "$a"
  seed_stale_verdict "$w/out.json"
  code=$(named_compare "$w" "$w" "$w/config.json" "$w/ch" -Q "$w/answer" Top Top.A)
  keep_verdict "$w/out.json" "$c" missing
  expect_refused "$c/missing" "$code" "$w" \
    "The challenge loaded the library Top\.D from [^ ]*/answer/D\.vo, which is not under the challenge directory\."
  passed "  ok $c/missing"
  d=$(pin_entry library Top.D "$w/answer/D.vo")
  named_config "$w/config.json" Top.A.thm "$a" "$d"
  rm -f "$w/out.json"
  code=$(named_compare "$w" "$w" "$w/config.json" "$w/ch" -Q "$w/answer" Top Top.A)
  keep_verdict "$w/out.json" "$c" prechecked
  expect_pass "$c/prechecked" "$code" "$w"
  passed "  ok $c/prechecked"
  rm -rf "$w"
  passed "ok $c"
}

# challenge-dir-link: the challenge directory ch-link holds A.vo and a link
# Sub to the answer's own Sub, outside it, so the challenge reads the
# answer's file of Top.Sub.L, whose sha256 the config pins, and would
# compare it with itself: refused, naming Top.Sub.L. Then -challenge names
# ch-alias, a link to the directory ch-real, which holds every challenge
# file: by its real path each file the challenge reads lies under it, and
# the run passes.
case_challenge_dir_link() {
  local w c=challenge-dir-link code a l
  w=$(mktemp -d)
  mkdir -p "$w/src/Sub" "$w/answer/Sub" "$w/ch-link" "$w/ch-real/Sub"
  printf '%s\n' 'Definition two : nat := 2.' > "$w/src/Sub/L.v"
  printf '%s\n' 'Require Import Top.Sub.L.' 'Theorem thm : two = 2.' 'Proof.' 'Admitted.' \
    > "$w/src/A.v"
  in_dir "$c" "$w/src" coqc -R . Top Sub/L.v
  in_dir "$c" "$w/src" coqc -R . Top A.v
  cp "$w/src/Sub/L.vo" "$w/answer/Sub/"
  printf '%s\n' 'Require Import Top.Sub.L.' 'Theorem thm : two = 2.' 'Proof. reflexivity. Qed.' \
    > "$w/answer/A.v"
  in_dir "$c" "$w/answer" coqc -R . Top A.v
  cp "$w/src/A.vo" "$w/ch-link/"
  ln -s "$w/answer/Sub" "$w/ch-link/Sub"
  cp "$w/src/A.vo" "$w/ch-real/"
  cp "$w/src/Sub/L.vo" "$w/ch-real/Sub/"
  ln -s "$w/ch-real" "$w/ch-alias"
  a=$(pin_entry path A.vo "$w/src/A.vo")
  l=$(pin_entry path Sub/L.vo "$w/src/Sub/L.vo")
  named_config "$w/config.json" Top.A.thm "$a, $l"
  seed_stale_verdict "$w/out.json"
  code=$(named_compare "$w" "$w" "$w/config.json" "$w/ch-link" -Q "$w/answer" Top Top.A)
  keep_verdict "$w/out.json" "$c" linked-dir
  expect_refused "$c/linked-dir" "$code" "$w" \
    "The challenge loaded the library Top\.Sub\.L from [^ ]*/Sub/L\.vo, which is not under the challenge directory\."
  passed "  ok $c/linked-dir"
  rm -f "$w/out.json"
  code=$(named_compare "$w" "$w" "$w/config.json" "$w/ch-alias" -Q "$w/answer" Top Top.A)
  keep_verdict "$w/out.json" "$c" linked-challenge
  expect_pass "$c/linked-challenge" "$code" "$w"
  passed "  ok $c/linked-challenge"
  rm -rf "$w"
  passed "ok $c"
}

# ---------------------------- the answer's libraries loaded without a check
#
# unchecked-helper: the challenge's thm states forall n, n + 0 = n. The
# forged answer's Top.Helper proves bad : False by exact_no_check I under
# Skip Qed Typecheck, a proof the kernel never typed, and its Top.A proves
# thm from bad. With -norec Top.A alone, Helper loads without a check:
# refused, naming Helper. Then an honest Helper, whose add_0_r proves the
# statement, named with -norec too: the run passes, and admitted is empty.
# Last, the forged Helper named with -norec: the kernel check of bad
# refuses it, before the comparator runs. That run is not -silent, so its
# output names the constant being checked when the type error stops it,
# and rocqchk exits 129 there, as on every error it does not handle, which
# completed would take for a signal: the case reads the code itself.
case_unchecked_helper() {
  local w c=unchecked-helper code a t
  w=$(mktemp -d)
  mkdir -p "$w/ch" "$w/forged" "$w/honest"
  printf '%s\n' 'Theorem thm : forall n : nat, n + 0 = n.' 'Proof.' 'Admitted.' > "$w/ch/A.v"
  in_dir "$c" "$w/ch" coqc -R . Top A.v
  printf '%s\n' 'Set Skip Qed Typecheck.' 'Lemma bad : False.' 'Proof. exact_no_check I. Qed.' \
    > "$w/forged/Helper.v"
  printf '%s\n' 'Require Top.Helper.' 'Theorem thm : forall n : nat, n + 0 = n.' \
    'Proof. exact (False_ind _ Top.Helper.bad). Qed.' > "$w/forged/A.v"
  printf '%s\n' 'Lemma add_0_r : forall n : nat, n + 0 = n.' \
    'Proof. induction n as [|n IH]; [reflexivity | simpl; rewrite IH; reflexivity]. Qed.' \
    > "$w/honest/Helper.v"
  printf '%s\n' 'Require Top.Helper.' 'Theorem thm : forall n : nat, n + 0 = n.' \
    'Proof. exact Top.Helper.add_0_r. Qed.' > "$w/honest/A.v"
  for t in forged honest; do
    in_dir "$c" "$w/$t" coqc -R . Top Helper.v
    in_dir "$c" "$w/$t" coqc -R . Top A.v
  done
  a=$(pin_entry path A.vo "$w/ch/A.vo")
  named_config "$w/config.json" Top.A.thm "$a"
  seed_stale_verdict "$w/out.json"
  code=$(named_compare "$w" "$w" "$w/config.json" "$w/ch" -Q "$w/forged" Top -norec Top.A)
  keep_verdict "$w/out.json" "$c" forged
  expect_refused "$c/forged" "$code" "$w" \
    "The answer library Top\.Helper was loaded without a check, as a dependency of a library given with -norec or -admit, and it is neither pre-checked by the config, nor pinned by its sha256 as a challenge file, nor given with -admit itself\."
  passed "  ok $c/forged"
  rm -f "$w/out.json"
  code=$(named_compare "$w" "$w" "$w/config.json" "$w/ch" -Q "$w/honest" Top \
    -norec Top.Helper -norec Top.A)
  keep_verdict "$w/out.json" "$c" honest
  expect_pass "$c/honest" "$code" "$w" '[]'
  passed "  ok $c/honest"
  seed_stale_verdict "$w/out.json"
  set +e
  (cd "$w" && bounded rocqchk -compare "$w/config.json" -challenge "$w/ch" \
    -compare-out "$w/out.json" -Q "$w/forged" Top -norec Top.Helper -norec Top.A) \
    > "$w/log" 2>&1
  code=$?
  set -e
  keep_verdict "$w/out.json" "$c" checked-forged
  [ "$code" = 129 ] || { cat "$w/log"; fail "$c/checked-forged: the run exits $code, not 129"; }
  [ ! -f "$w/out.json" ] || fail "$c/checked-forged: an earlier verdict file survived the refusal"
  [ "$(tail -n 2 "$w/log")" = "$(printf '%s\n' '  checking cst:Top.Helper.bad' \
    'Fatal Error: Type error: ActualType')" ] \
    || { cat "$w/log"; fail "$c/checked-forged: the kernel did not refuse Top.Helper.bad"; }
  passed "  ok $c/checked-forged"
  rm -rf "$w"
  passed "ok $c"
}

# unchecked-admit-closure: the answer's Top.B proves thm by Top.A's
# add_0_r, which A takes from Top.Helper. -norec Top.B -admit Top.A loads A
# without a check, as -admit asks, and Helper with it: refused, naming
# Helper, which -admit does not name. Then each library named with -norec
# or -admit, -admit Top.Helper twice: the run passes, and admitted names
# the -admit libraries once each, in command-line order, which is not the
# sorted one.
case_unchecked_admit_closure() {
  local w c=unchecked-admit-closure code b f
  w=$(mktemp -d)
  mkdir -p "$w/ch" "$w/answer"
  printf '%s\n' 'Theorem thm : forall n : nat, n + 0 = n.' 'Proof.' 'Admitted.' > "$w/ch/B.v"
  in_dir "$c" "$w/ch" coqc -R . Top B.v
  printf '%s\n' 'Lemma add_0_r : forall n : nat, n + 0 = n.' \
    'Proof. induction n as [|n IH]; [reflexivity | simpl; rewrite IH; reflexivity]. Qed.' \
    > "$w/answer/Helper.v"
  printf '%s\n' 'Require Top.Helper.' 'Definition add_0_r := Top.Helper.add_0_r.' \
    > "$w/answer/A.v"
  printf '%s\n' 'Require Top.A.' 'Theorem thm : forall n : nat, n + 0 = n.' \
    'Proof. exact Top.A.add_0_r. Qed.' > "$w/answer/B.v"
  for f in Helper.v A.v B.v; do in_dir "$c" "$w/answer" coqc -R . Top "$f"; done
  b=$(pin_entry path B.vo "$w/ch/B.vo")
  named_config "$w/config.json" Top.B.thm "$b"
  seed_stale_verdict "$w/out.json"
  code=$(named_compare "$w" "$w" "$w/config.json" "$w/ch" -Q "$w/answer" Top \
    -norec Top.B -admit Top.A)
  keep_verdict "$w/out.json" "$c" closure
  expect_refused "$c/closure" "$code" "$w" \
    "The answer library Top\.Helper was loaded without a check, as a dependency of a library given with -norec or -admit, and it is neither pre-checked by the config, nor pinned by its sha256 as a challenge file, nor given with -admit itself\."
  passed "  ok $c/closure"
  rm -f "$w/out.json"
  code=$(named_compare "$w" "$w" "$w/config.json" "$w/ch" -Q "$w/answer" Top \
    -admit Top.Helper -norec Top.B -admit Top.A -admit Top.Helper)
  keep_verdict "$w/out.json" "$c" split
  expect_pass "$c/split" "$code" "$w" '["Top.Helper","Top.A"]'
  passed "  ok $c/split"
  rm -rf "$w"
  passed "ok $c"
}

# -------------------------- the directories a shared library may come from
#
# A library at the path of a standard library file that the test build
# does not serve, Stdlib.Logic.FunctionalExtensionality, under <dir>, which
# declares functional_extensionality_dep : False. The challenge (ch) states
# thm : False, the answer (answer) proves it by that axiom, and the config
# permits the axiom by its name. The answer is compiled with the library
# bound by -Q; the run binds no such root, and finds it only where the load
# path's own directories reach it.
funext_trees() { # <w> <dir> <run>
  local w=$1 dir=$2 run=$3 a
  mkdir -p "$dir/Stdlib/Logic" "$w/ch" "$w/answer"
  printf '%s\n' 'Axiom functional_extensionality_dep : False.' \
    > "$dir/Stdlib/Logic/FunctionalExtensionality.v"
  in_dir "$run" "$dir" coqc -Q Stdlib Stdlib Stdlib/Logic/FunctionalExtensionality.v
  printf '%s\n' 'Theorem thm : False.' 'Proof.' 'Admitted.' > "$w/ch/A.v"
  in_dir "$run" "$w/ch" coqc -R . Top A.v
  printf '%s\n' 'Require Stdlib.Logic.FunctionalExtensionality.' 'Theorem thm : False.' \
    'Proof. exact Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep. Qed.' \
    > "$w/answer/A.v"
  in_dir "$run" "$w/answer" coqc -Q "$dir/Stdlib" Stdlib -R . Top A.v
  a=$(pin_entry path A.vo "$w/ch/A.vo")
  named_config "$w/config.json" Top.A.thm "$a" "" \
    '"Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep"'
}

# shared-xdg: the library under XDG_DATA_HOME, which the load path binds and
# the run does not trust for the image's own libraries: refused, naming it.
case_shared_xdg() {
  local w c=shared-xdg code
  w=$(mktemp -d)
  funext_trees "$w" "$w/xdg/coq" "$c"
  seed_stale_verdict "$w/out.json"
  code=$(export XDG_DATA_HOME="$w/xdg"
    named_compare "$w" "$w" "$w/config.json" "$w/ch" -Q "$w/answer" Top Top.A)
  keep_verdict "$w/out.json" "$c" answer
  expect_refused "$c" "$code" "$w" \
    "The answer loaded the library Stdlib\.Logic\.FunctionalExtensionality from [^ ]*/xdg/coq/Stdlib/Logic/FunctionalExtensionality\.vo, which is under none of the directories a -compare run trusts for the image's own libraries"
  rm -rf "$w"
  passed "ok $c"
}

# shared-nohome: the library under ./.local/share/coq of the directory the
# run is in, nohome, where the load path finds the XDG data directory when
# no home directory is set (lib/envars.ml): refused, naming it.
case_shared_nohome() {
  local w c=shared-nohome code
  w=$(mktemp -d)
  funext_trees "$w" "$w/nohome/.local/share/coq" "$c"
  seed_stale_verdict "$w/out.json"
  code=$(unset HOME XDG_DATA_HOME HOMEDRIVE HOMEPATH USERPROFILE
    named_compare "$w" "$w/nohome" "$w/config.json" "$w/ch" -Q "$w/answer" Top Top.A)
  keep_verdict "$w/out.json" "$c" answer
  expect_refused "$c" "$code" "$w" \
    "The answer loaded the library Stdlib\.Logic\.FunctionalExtensionality from [^ ]*\.local/share/coq/Stdlib/Logic/FunctionalExtensionality\.vo, which is under none of the directories a -compare run trusts for the image's own libraries"
  rm -rf "$w"
  passed "ok $c"
}

# A library <root>.L at <parent>/<root>/L.vo, in a directory the run trusts
# for the image's own libraries; the challenge (ch) states thm : two = 2;
# and the answer (answer) Requires <root>.L and proves thm with it.
trusted_trees() { # <w> <parent> <root> <run>
  local w=$1 parent=$2 root=$3 run=$4 a
  mkdir -p "$parent/$root" "$w/ch" "$w/answer"
  printf '%s\n' 'Definition lib_two : nat := 2.' > "$parent/$root/L.v"
  in_dir "$run" "$parent" coqc -Q "$root" "$root" "$root/L.v"
  printf '%s\n' 'Definition two := 2.' 'Theorem thm : two = 2.' 'Proof.' 'Admitted.' > "$w/ch/A.v"
  in_dir "$run" "$w/ch" coqc -R . Top A.v
  printf '%s\n' "Require $root.L." 'Definition two := 2.' 'Theorem thm : two = 2.' \
    "Proof. exact (eq_refl $root.L.lib_two). Qed." > "$w/answer/A.v"
  in_dir "$run" "$w/answer" coqc -Q "$parent/$root" "$root" -R . Top A.v
  a=$(pin_entry path A.vo "$w/ch/A.vo")
  named_config "$w/config.json" Top.A.thm "$a"
}

# shared-coqpath, a guard: the library Cp.L under COQPATH passes.
case_shared_coqpath() {
  local w c=shared-coqpath code
  w=$(mktemp -d)
  trusted_trees "$w" "$w/cp" Cp "$c"
  rm -f "$w/out.json"
  code=$(unset ROCQPATH
    export COQPATH="$w/cp"
    named_compare "$w" "$w" "$w/config.json" "$w/ch" -Q "$w/answer" Top Top.A)
  keep_verdict "$w/out.json" "$c" answer
  expect_pass "$c" "$code" "$w"
  rm -rf "$w"
  passed "ok $c"
}

# shared-user-contrib, a guard: the library Uc.L under the user-contrib of
# coqlib, which the run is given with -coqlib: its theories is a link to the
# corelib of the installation in use, and its plugins an empty directory,
# which an installation must have. The run passes.
case_shared_user_contrib() {
  local w c=shared-user-contrib code
  w=$(mktemp -d)
  mkdir -p "$w/coqlib/plugins" "$w/coqlib/user-contrib"
  ln -s "$(cd "$(rocq -where)" && pwd)/theories" "$w/coqlib/theories"
  trusted_trees "$w" "$w/coqlib/user-contrib" Uc "$c"
  rm -f "$w/out.json"
  code=$(named_compare "$w" "$w" "$w/config.json" "$w/ch" -coqlib "$w/coqlib" \
    -Q "$w/answer" Top Top.A)
  keep_verdict "$w/out.json" "$c" answer
  expect_pass "$c" "$code" "$w"
  rm -rf "$w"
  passed "ok $c"
}

# ------------------------------------------- the same file on both sides
#
# Lib.X, a library that ROCQPATH reaches, declares the universes ux and vx.
# rp's file leaves them apart; rp2's is compiled from a source that also
# states vx < ux, and made to state the digest of rp's (forge_digest), so
# that each library compiled against rp's file takes rp2's for it. The runs
# list rp2 behind rp in ROCQPATH, so the answer reads rp's. The challenge
# (ch) declares u <= Lib.X.vx and states thm over Type@{u}; the honest
# answer (answer) proves thm. The forged answer (forged) also adds
# u < Lib.X.ux, which on the challenge side only rp2's levels make hold,
# and vx < ux, which the challenge-to-answer direction of the constraint
# check then asks of it (the other direction passes over a constraint
# between two levels that are not the answer's own). The challenge
# directory ch-link holds the challenge's A.vo and a link Lib to rp's Lib,
# which the challenge load binds under Top, so that on the challenge side
# the name Lib.X resolves to rp2's file.
samefile_trees() { # <w> <run>
  local w=$1 run=$2 t
  mkdir -p "$w/rp/Lib" "$w/rp2/Lib" "$w/other/Lib" "$w/ch" "$w/ch-link" "$w/answer" "$w/forged"
  printf '%s\n' 'Universe ux vx.' > "$w/rp/Lib/X.v"
  in_dir "$run" "$w/rp" coqc -Q Lib Lib Lib/X.v
  printf '%s\n' 'Universe ux vx.' 'Constraint vx < ux.' > "$w/other/Lib/X.v"
  in_dir "$run" "$w/other" coqc -Q Lib Lib Lib/X.v
  cp "$w/other/Lib/X.vo" "$w/rp2/Lib/"
  forge_digest "$w/rp/Lib/X.vo" "$w/rp2/Lib/X.vo"
  printf '%s\n' 'Require Lib.X.' 'Universe u.' 'Constraint u <= Lib.X.vx.' \
    'Definition U := Type@{u}.' 'Theorem thm : forall A : U, A -> A.' 'Proof.' 'Admitted.' \
    > "$w/ch/A.v"
  printf '%s\n' 'Require Lib.X.' 'Universe u.' 'Constraint u <= Lib.X.vx.' \
    'Definition U := Type@{u}.' 'Theorem thm : forall A : U, A -> A.' \
    'Proof. exact (fun A a => a). Qed.' > "$w/answer/A.v"
  printf '%s\n' 'Require Lib.X.' 'Universe u.' 'Constraint u <= Lib.X.vx.' \
    'Constraint u < Lib.X.ux.' 'Constraint Lib.X.vx < Lib.X.ux.' \
    'Definition U := Type@{u}.' 'Theorem thm : forall A : U, A -> A.' \
    'Proof. exact (fun A a => a). Qed.' > "$w/forged/A.v"
  for t in ch answer forged; do
    in_dir "$run" "$w/$t" env ROCQPATH="$w/rp" coqc -R . Top A.v
  done
  cp "$w/ch/A.vo" "$w/ch-link/"
  ln -s "$w/rp/Lib" "$w/ch-link/Lib"
}

# The same-file case <c>, Lib.X pre-checked at rp's file when <prechecked>
# is yes. With the link, the forged answer, which passes against rp2's
# levels and fails against rp's: refused with <pattern>, naming Lib.X and
# rp2's file. Without it, both sides read rp's file, and the honest answer
# passes.
samefile_case() { # <c> <prechecked> <pattern>
  local c=$1 w code a x=""
  w=$(mktemp -d)
  samefile_trees "$w" "$c"
  a=$(pin_entry path A.vo "$w/ch/A.vo")
  if [ "$2" = yes ]; then x=$(pin_entry library Lib.X "$w/rp/Lib/X.vo"); fi
  named_config "$w/config.json" Top.A.thm "$a" "$x"
  seed_stale_verdict "$w/out.json"
  code=$(export ROCQPATH="$w/rp:$w/rp2"
    named_compare "$w" "$w" "$w/config.json" "$w/ch-link" -Q "$w/forged" Top Top.A)
  keep_verdict "$w/out.json" "$c" linked
  expect_refused "$c/linked" "$code" "$w" "$3"
  passed "  ok $c/linked"
  rm -f "$w/out.json"
  code=$(export ROCQPATH="$w/rp:$w/rp2"
    named_compare "$w" "$w" "$w/config.json" "$w/ch" -Q "$w/answer" Top Top.A)
  keep_verdict "$w/out.json" "$c" unlinked
  expect_pass "$c/unlinked" "$code" "$w"
  passed "  ok $c/unlinked"
  rm -rf "$w"
  passed "ok $c"
}

# same-file-shared: Lib.X shared, which the challenge must read from the
# answer's file.
case_same_file_shared() {
  samefile_case same-file-shared no \
    "The challenge loaded the shared library Lib\.X from [^ ]*/rp2/Lib/X\.vo, and the answer loaded it from [^ ]*/rp/Lib/X\.vo: the two sides would read different files under one library name\."
}

# same-file-prechecked: Lib.X pre-checked, which the challenge must read
# from the answer's file or from a file of the pinned sha256.
case_same_file_prechecked() {
  samefile_case same-file-prechecked yes \
    "The challenge loaded the pre-checked library Lib\.X from [^ ]*/rp2/Lib/X\.vo, which is not the file the answer loaded it from, and whose sha256 is [0-9a-f]{64}, not the one the config pins\."
}

# ------------------------------- the file a pre-checked library is read from
#
# The challenge (ch) holds A.vo, whose thm states two = 2; the config
# pre-checks Top.P.Q at src's P/Q.vo, which no A Requires; the honest
# answer (answer) holds that file, so the run loads it through the
# pre-checked list alone, and an A that proves thm.
prebad_trees() { # <w> <run>
  local w=$1 run=$2 a q
  mkdir -p "$w/src/P" "$w/ch" "$w/answer/P"
  printf '%s\n' 'Definition q : nat := 2.' > "$w/src/P/Q.v"
  in_dir "$run" "$w/src" coqc -R . Top P/Q.v
  printf '%s\n' 'Definition two := 2.' 'Theorem thm : two = 2.' 'Proof.' 'Admitted.' > "$w/ch/A.v"
  in_dir "$run" "$w/ch" coqc -R . Top A.v
  cp "$w/src/P/Q.vo" "$w/answer/P/"
  printf '%s\n' 'Definition two := 2.' 'Theorem thm : two = 2.' 'Proof. reflexivity. Qed.' \
    > "$w/answer/A.v"
  in_dir "$run" "$w/answer" coqc -R . Top A.v
  a=$(pin_entry path A.vo "$w/ch/A.vo")
  q=$(pin_entry library Top.P.Q "$w/src/P/Q.vo")
  named_config "$w/config.json" Top.A.thm "$a" "$q"
}

# prechecked-read-file: two and pin are both bound to Top, and the load path
# searches pin first, so Top.P.Q resolves to pin's copy of the pinned file,
# whose sha256 is checked before any library is read. The command line
# names two's P/Q.vo, another library of that name, which the loader then
# reads instead: refused by its sha256, naming that file. Then the honest
# answer passes.
case_prechecked_read_file() {
  local w c=prechecked-read-file code got pin
  w=$(mktemp -d)
  prebad_trees "$w" "$c"
  mkdir -p "$w/two/P" "$w/pin/P"
  cp "$w/answer/A.vo" "$w/two/"
  printf '%s\n' 'Definition q : nat := 3.' > "$w/two/P/Q.v"
  in_dir "$c" "$w/two" coqc -R . Top P/Q.v
  cp "$w/src/P/Q.vo" "$w/pin/P/"
  got=$(bounded rocqchk -sha256 "$w/two/P/Q.vo")
  pin=$(bounded rocqchk -sha256 "$w/src/P/Q.vo")
  seed_stale_verdict "$w/out.json"
  code=$(named_compare "$w" "$w" "$w/config.json" "$w/ch" -Q "$w/two" Top -Q "$w/pin" Top \
    "$w/two/P/Q.vo" Top.A)
  keep_verdict "$w/out.json" "$c" read-file
  expect_refused "$c/read-file" "$code" "$w" \
    "The pre-checked library Top\.P\.Q is [^ ]*/two/P/Q\.vo, whose sha256 is $got, and the config pins $pin\."
  passed "  ok $c/read-file"
  rm -f "$w/out.json"
  code=$(named_compare "$w" "$w" "$w/config.json" "$w/ch" -Q "$w/answer" Top Top.A)
  keep_verdict "$w/out.json" "$c" honest
  expect_pass "$c/honest" "$code" "$w"
  passed "  ok $c/honest"
  rm -rf "$w"
  passed "ok $c"
}

# prechecked-garbage: the answer's P/Q.vo is the pinned file with the 16
# bytes at offset 16, where its first segment starts, overwritten: the
# marshal header there is no longer one, so the segment does not
# unmarshal. Its sha256 is checked before any library is read: refused by
# the pin's text, naming the file, and the loader never reads it (no
# "Corrupted file", no anomaly). Then that P/Q.vo is a directory: refused
# before the file is opened, naming it, as one that is not a regular file.
# Then the honest answer passes.
case_prechecked_garbage() {
  local w c=prechecked-garbage code got pin
  w=$(mktemp -d)
  prebad_trees "$w" "$c"
  mkdir -p "$w/garbage/P"
  cp "$w/answer/A.vo" "$w/garbage/"
  cp "$w/src/P/Q.vo" "$w/garbage/P/"
  printf '\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377' \
    | dd of="$w/garbage/P/Q.vo" bs=1 seek=16 conv=notrunc 2> /dev/null
  got=$(bounded rocqchk -sha256 "$w/garbage/P/Q.vo")
  pin=$(bounded rocqchk -sha256 "$w/src/P/Q.vo")
  seed_stale_verdict "$w/out.json"
  code=$(named_compare "$w" "$w" "$w/config.json" "$w/ch" -Q "$w/garbage" Top Top.A)
  keep_verdict "$w/out.json" "$c" garbage
  expect_refused "$c/garbage" "$code" "$w" \
    "The pre-checked library Top\.P\.Q is [^ ]*/garbage/P/Q\.vo, whose sha256 is $got, and the config pins $pin\."
  ! grep -Eq 'Corrupted file|Try to rebuild it|[Aa]nomaly' "$w/log" \
    || { cat "$w/log"; fail "$c/garbage: the loader read the file before its sha256 was checked"; }
  passed "  ok $c/garbage"
  rm -f "$w/out.json"
  rm -f "$w/garbage/P/Q.vo"
  mkdir "$w/garbage/P/Q.vo"
  seed_stale_verdict "$w/out.json"
  code=$(named_compare "$w" "$w" "$w/config.json" "$w/ch" -Q "$w/garbage" Top Top.A)
  keep_verdict "$w/out.json" "$c" directory
  expect_refused "$c/directory" "$code" "$w" \
    "The pre-checked library Top\.P\.Q is [^ ]*/P/Q\.vo, which cannot be read: Is a directory, not a regular file\."
  passed "  ok $c/directory"
  rm -f "$w/out.json"
  code=$(named_compare "$w" "$w" "$w/config.json" "$w/ch" -Q "$w/answer" Top Top.A)
  keep_verdict "$w/out.json" "$c" honest
  expect_pass "$c/honest" "$code" "$w"
  passed "  ok $c/honest"
  rm -rf "$w"
  passed "ok $c"
}

# ---------------------------------------------------- the recorded forgeries
#
# Six proofs of False that a kernel defect once accepted (rocq#22378,
# #22383, #22391, #22675, the VM forgery of dispatch://BET-357 and the
# array forgery of dispatch://BET-630). The cut this branch sits on carries
# the fix for each, so none of them may reach a passing verdict. Three
# outcomes count as not-pass, and the case prints which one each takes:
# the forgery does not compile, rocqchk refuses it, or the verdict is fail.
# The answer's Main.v proves False by "exact bottom" when the tree's
# Forge.v declares bottom, and by "exact contradiction" otherwise.
#
# The trees are read-only recordings; COMPARE_FORGERIES points at them and
# the case is skipped where they are not mounted.
: "${COMPARE_FORGERIES:=/mnt/durable/sami/eval-driven-development/round4/verified-grading/wrong-answers-e2e/trees}"
# The forgeries, which the count reads too.
forgery_names=(os-22378 os-22383 os-22391 os-22675 os-vm357 os-parray630)

case_forgeries() {
  if [ ! -d "$COMPARE_FORGERIES" ]; then
    echo "skip forgeries (no $COMPARE_FORGERIES)"
    skipped=$((skipped + $(held_of forgeries)))
    return
  fi
  # <log> -> its first error line and the next one, joined: Rocq prints
  # "Error:" alone and the message on the line after it.
  first_error() {
    grep -m1 -i -A1 error "$1" | paste -sd ' ' | cut -c1-110
  }
  local f
  for f in "${forgery_names[@]}"; do
    local src="$COMPARE_FORGERIES/$f/plain/Lib"
    [ -d "$src" ] || fail "forgeries: no $src"
    local work
    work=$(mktemp -d)
    mkdir -p "$work/challenge" "$work/answer"
    local side
    for side in challenge answer; do
      cp "$src/Forge.v" "$work/$side/Forge.v"
      [ -f "$src/hurkens.v" ] && cp "$src/hurkens.v" "$work/$side/hurkens.v"
    done
    printf '%s\n' 'Require Import Forge.' 'Theorem forged : False.' 'Proof.' 'Admitted.' \
      > "$work/challenge/Main.v"
    local proof=contradiction
    grep -Eq '^(Definition|Lemma|Theorem) bottom ' "$src/Forge.v" && proof=bottom
    printf '%s\n' 'Require Import Forge.' 'Theorem forged : False.' \
      "Proof. exact $proof. Qed." > "$work/answer/Main.v"
    local order="Forge.v Main.v"
    [ -f "$src/hurkens.v" ] && order="hurkens.v Forge.v Main.v"
    local ok="" v
    for v in $order; do
      (cd "$work/challenge" && coqc -R . Top "$v") > "$work/cc" 2>&1 \
        || { ok="the challenge does not compile: $(first_error "$work/cc")"; break; }
    done
    if [ -z "$ok" ]; then
      for v in $order; do
        (cd "$work/answer" && coqc -R . Top "$v") > "$work/ac" 2>&1 \
          || { ok="the answer does not compile: $(first_error "$work/ac")"; break; }
      done
    fi
    if [ -z "$ok" ]; then
      local sha prelude_sha
      sha=$(bounded rocqchk -sha256 "$work/challenge/Main.vo")
      prelude_sha=$(bounded rocqchk -sha256 "$(prelude_vo)")
      printf '%s\n' \
        "{\"theorems\": [{\"name\": \"Top.Main.forged\"}]," \
        " \"tolerated_flags\": [{\"kind\": \"indices-not-mattering\", \"object\": \"Corelib.Init.Logic.eq\"}]," \
        " \"prechecked\": [{\"library\": \"Corelib.Init.Prelude\", \"sha256\": \"$prelude_sha\"}]," \
        " \"challenge_files\": [{\"path\": \"Main.vo\", \"sha256\": \"$sha\"}]}" > "$work/config.json"
      local libs=() g
      for g in "$work/answer"/*.vo; do libs+=("Top.$(basename "$g" .vo)"); done
      set +e
      bounded rocqchk -silent -R "$work/answer" Top -compare "$work/config.json" \
        -challenge "$work/challenge" -compare-out "$work/out.json" "${libs[@]}" \
        > "$work/log" 2>&1
      local code=$?
      set -e
      completed "$code" "$work/log"
      keep_verdict "$work/out.json" forgeries "$f"
      if [ "$code" != "0" ]; then
        ok="rocqchk refuses it: $(first_error "$work/log")"
      elif grep -q '"verdict":"fail"' "$work/out.json"; then
        ok="the verdict is fail"
      else
        cat "$work/out.json"
        fail "forgeries/$f: the forgery PASSES"
      fi
    fi
    passed "  ok forgeries/$f: $ok"
    rm -rf "$work"
  done
  passed "ok forgeries"
}

compare_provenance() {
  local root rev
  root=$(cd "$here/../.." && pwd)
  if rev=$(git -C "$root" rev-parse HEAD 2>/dev/null); then
    printf 'compare suite revision: %s\n' "$rev"
  else
    echo "compare suite revision: unavailable"
  fi
  printf 'compare rocqchk: %s\n' "$(command -v rocqchk)"
  bounded rocqchk --version
}

# ---------------------------------------------------------------- the count
#
# The runs the fixture tree holds: one per ok line that a run in which
# every case passed prints.

# A case directory: its honest answer, each bad answer and each tolerance
# of one, each refused config, fail-config and utf8-refusal, found as
# run_case finds them.
held_case() { # <case directory>
  local c=$1 n=1 d t
  for d in "$c"/bad-*; do
    [ -d "$d" ] || continue
    n=$((n + 1))
    for t in "$d"/tolerate-*.tmpl; do
      [ -f "$t" ] || continue
      n=$((n + 1))
    done
  done
  for d in "$c"/refuse-*; do
    [ -d "$d" ] || continue
    n=$((n + 1))
  done
  if [ -d "$c/fail-config" ]; then n=$((n + 1)); fi
  if [ -f "$c/utf8-refusal" ]; then n=$((n + 1)); fi
  echo "$n"
}

# A case as the runner is given it. A named case holds its ok line, and one
# for each of its sub-runs when it has more than one.
held_of() { # <case>
  case "$1" in
    sha256|vos|digest|sibling) echo 1 ;;
    pre-dep-norec|shared-xdg|shared-nohome|shared-coqpath|shared-user-contrib) echo 1 ;;
    challenge-missing-dep|challenge-dir-link|unchecked-admit-closure) echo 3 ;;
    same-file-shared|same-file-prechecked|prechecked-read-file) echo 3 ;;
    pre-dep-forged|unchecked-helper|prechecked-garbage) echo 4 ;;
    norec) echo $((1 + ${#norec_forms[@]})) ;;
    forgeries) echo $((1 + ${#forgery_names[@]})) ;;
    *) held_case "$cases_dir/$1" ;;
  esac
}

# Every case, as the runner runs them when it is given none.
held_total() {
  local n c
  n=$(held_of sha256)
  for c in "$cases_dir"/*/; do
    n=$((n + $(held_case "$c")))
  done
  for c in vos digest sibling norec "${library_cases[@]}" forgeries; do
    n=$((n + $(held_of "$c")))
  done
  echo "$n"
}

main() {
  # The count reads the fixture tree alone, so it needs no rocq.
  if [ "${1:-}" = --count ]; then
    [ $# = 1 ] || fail "--count takes no case"
    held_total
    return
  fi
  compare_provenance
  local held
  if [ $# -gt 0 ]; then
    held=$(held_of "$1")
    case "$1" in
      sha256) case_sha256 ;;
      vos) case_vos ;;
      digest) case_digest ;;
      sibling) case_sibling ;;
      norec) case_norec ;;
      forgeries) case_forgeries ;;
      *)
        if is_library_case "$1"; then "case_${1//-/_}"; else run_case "$1"; fi ;;
    esac
  else
    held=$(held_total)
    case_sha256
    local c
    for c in "$cases_dir"/*/; do
      run_case "$(basename "$c")"
    done
    case_vos
    case_digest
    case_sibling
    case_norec
    for c in "${library_cases[@]}"; do
      "case_${c//-/_}"
    done
    case_forgeries
  fi
  echo "compare.sh: $ran ok, $skipped skipped, $held held"
  [ $((ran + skipped)) = "$held" ] \
    || fail "$ran ran and $skipped were skipped, but the fixture tree holds $held runs"
  [ "${COMPARE_STRICT:-}" != 1 ] || [ "$skipped" = 0 ] \
    || fail "$skipped runs were skipped under COMPARE_STRICT=1"
}

main "$@"
