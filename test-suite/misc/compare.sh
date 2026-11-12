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
#                     out like answer/ and built like a bad answer; without
#                     it, the honest answer
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
# forgeries), a form of norec or a forgery. A run in which every case
# passed ends with
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
# <form>.bad (norec) and <forgery> (forgeries).
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
  # their own, built as a bad answer is
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
# The two forms, which the count reads too.
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

# ---------------------------------------------------- the recorded forgeries
#
# Six proofs of False that a kernel defect once accepted (rocq#22378,
# #22383, #22391, #22675, the VM forgery of dispatch://BET-357 and the
# array forgery of dispatch://BET-630). The cut this branch sits on carries
# the fix for each, so none of them may reach a passing verdict. Three
# outcomes count as not-pass, and the case prints which one each takes:
# the forgery does not compile, rocqchk refuses it, or the verdict is fail.
#
# The trees are read-only recordings; COMPARE_FORGERIES points at them and
# the case is skipped where they are not mounted.
: "${COMPARE_FORGERIES:=/mnt/durable/sami/eval-driven-development/round4/verified-grading/wrong-answers-e2e/trees}"
# The six forgeries, which the count reads too.
forgery_names=(os-22378 os-22383 os-22391 os-22675 os-vm357 os-parray630)

case_forgeries() {
  if [ ! -d "$COMPARE_FORGERIES" ]; then
    echo "skip forgeries (no $COMPARE_FORGERIES)"
    skipped=$((skipped + $(held_of forgeries)))
    return
  fi
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
    printf '%s\n' 'Require Import Forge.' 'Theorem forged : False.' \
      'Proof. exact contradiction. Qed.' > "$work/answer/Main.v"
    local order="Forge.v Main.v"
    [ -f "$src/hurkens.v" ] && order="hurkens.v Forge.v Main.v"
    local ok="" v
    for v in $order; do
      (cd "$work/challenge" && coqc -R . Top "$v") > "$work/cc" 2>&1 \
        || { ok="the challenge does not compile: $(grep -m1 -i error "$work/cc" | cut -c1-110)"; break; }
    done
    if [ -z "$ok" ]; then
      for v in $order; do
        (cd "$work/answer" && coqc -R . Top "$v") > "$work/ac" 2>&1 \
          || { ok="the answer does not compile: $(grep -m1 -i error "$work/ac" | cut -c1-110)"; break; }
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
        ok="rocqchk refuses it: $(grep -m1 -i error "$work/log" | cut -c1-110)"
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

# A case as the runner is given it.
held_of() { # <case>
  case "$1" in
    sha256|vos|digest|sibling) echo 1 ;;
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
  for c in vos digest sibling norec forgeries; do
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
      *) run_case "$1" ;;
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
    case_forgeries
  fi
  echo "compare.sh: $ran ok, $skipped skipped, $held held"
  [ $((ran + skipped)) = "$held" ] \
    || fail "$ran ran and $skipped were skipped, but the fixture tree holds $held runs"
  [ "${COMPARE_STRICT:-}" != 1 ] || [ "$skipped" = 0 ] \
    || fail "$skipped runs were skipped under COMPARE_STRICT=1"
}

main "$@"
