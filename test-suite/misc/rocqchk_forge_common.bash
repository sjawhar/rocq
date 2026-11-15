# Shared helpers of the misc tests that run rocqchk on forged .vo files:
# rocqchk_sigalias.sh, rocqchk_alias_label.sh, rocqchk_nested_resolver.sh,
# rocqchk_inline_hint.sh, rocqchk_alias_rewrite_rule.sh,
# rocqchk_primitive_type.sh, rocqchk_register_type.sh and
# rocqchk_repeated_label.sh. Each sources it with
#
#   . misc/rocqchk_forge_common.bash
#
# This file is deliberately not named *.sh: the misc target runs every
# misc/*.sh as a test of its own (see the "misc:" rule in test-suite/Makefile).
# That rule exports $coqc and $BIN and runs the script from the test-suite
# directory; it does not export a rocqchk command, so rocqchk is spelled
# "$BIN"rocqchk. The forgers share misc/rocqchk_forge_lib.ml the same way.

# The refusal the forgeries expect. Upstream's rocqchk prints a module typing
# error as "Module typing error" (rocq-prover/rocq#22373). 9.2's rocqchk has
# no printer for it and reports the exception itself,
# "Modops.ModuleTypingError".
typing_error="Module typing error|ModuleTypingError"

# must_accept <log> <message> <rocqchk argument>...: rocqchk, with its output
# in <log>, must accept the files. If it refuses them, print <message> and
# <log>, and exit 1.
must_accept() {
  local log=$1 message=$2
  shift 2
  if ! "$BIN"rocqchk "$@" > "$log" 2>&1; then
    echo "$message"
    cat "$log"
    exit 1
  fi
}

# must_refuse <log> <error> <accepted> <unexpected> <rocqchk argument>...:
# rocqchk, with its output in <log>, must refuse the files with an error
# that the extended regular expression <error> matches. If it accepts them,
# print <accepted>; if it refuses them with another error, print
# <unexpected>; then print <log>, and exit 1.
must_refuse() {
  local log=$1 error=$2 accepted=$3 unexpected=$4
  shift 4
  if "$BIN"rocqchk "$@" > "$log" 2>&1; then
    echo "$accepted"
    cat "$log"
    exit 1
  fi
  if ! grep -Eq "$error" "$log"; then
    echo "$unexpected"
    cat "$log"
    exit 1
  fi
}

# mode_args <mode> <dir> <root> [<client>]: set the array mode_argv to the
# rocqchk arguments that check <root>.Lib, and <root>.<client> if it is
# given, in <dir>, bound to <root>, as a grader runs rocqchk (mode grader)
# or with the default options (mode default).
mode_args() {
  local libs=("$3.Lib")
  if [ -n "${4-}" ]; then libs+=("$3.$4"); fi
  case $1 in
    grader) mode_argv=(-o -bytecode-compiler yes -R "$2" "$3" -norec "${libs[@]}") ;;
    default) mode_argv=(-R "$2" "$3" "${libs[@]}") ;;
  esac
}

# accepts <case> <rocqchk argument>... and refuses <case> <rocqchk
# argument>...: must_accept, and must_refuse with a module typing error, with
# the output in $D/<case>/out.log. The messages name the case and the
# arguments, and those of refuses the forgery, as the script sets $forgery
# ("a forged delta resolver").
accepts() {
  local d=$1
  shift
  must_accept "$D/$d/out.log" "rocqchk refused honest files ($d): rocqchk $*" "$@"
}

refuses() {
  local d=$1
  shift
  must_refuse "$D/$d/out.log" "$typing_error" \
    "rocqchk accepted $forgery and a closed proof of False ($d): rocqchk $*" \
    "unexpected rocqchk failure for $forgery ($d): rocqchk $*" "$@"
}
