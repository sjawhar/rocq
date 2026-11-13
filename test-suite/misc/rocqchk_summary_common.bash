# Shared helpers of the fork's misc tests that read the summary of
# rocqchk -o: rocqchk_admitted_summary.sh, rocqchk_sealed_axiom_summary.sh,
# rocqchk_ascribed_axiom_summary.sh, rocqchk_application_axiom_summary.sh,
# rocqchk_alias_cycle_summary.sh, rocqchk_functor_loop_summary.sh,
# rocqchk_cook.sh and rocqchk_primitive_type.sh. Each sources it with
#
#   . misc/rocqchk_summary_common.bash
#
# so that a change of the summary's format is made here for them. Upstream's
# assumptions-norec.sh keeps its own reader, as upstream wrote it.
#
# This file is deliberately not named *.sh: the misc target runs every
# misc/*.sh as a test of its own (see the "misc:" rule in test-suite/Makefile).
# That rule exports $BIN and runs the script from the test-suite directory;
# it does not export a rocqchk command, so rocqchk is spelled "$BIN"rocqchk.

# section <title> <log>: print one summary section of <log>: its
# "* <title>" line and the lines under it, up to the next "* " bullet. awk's
# index() takes the title literally, slashes and parentheses included.
section() { awk -v h="* $1" 'index($0, h) == 1 { p = 1; print; next } p && /^\* / { exit } p { print }' "$2"; }

# axioms <dir> <log> <root> <library>: rocqchk -o on <dir>, bound to <root>,
# with <root>.<library> admitted, within a time limit, and its output in
# <log>. Then print the names of the Axioms section, sorted. The caller keeps
# the standard output, so a failure is said on the standard error.
axioms () {
  local R=0
  timeout 120 "$BIN"rocqchk -silent -o -Q "$1" "$3" -admit "$3.$4" > "$2" 2>&1 || R=$?
  if [ "$R" = 124 ]; then
    echo "rocqchk -o did not end within 120 s on $1" >&2
    exit 1
  elif [ "$R" != 0 ]; then
    echo "rocqchk -o exited with $R on $1" >&2
    cat "$2" >&2
    exit 1
  fi
  section 'Axioms' "$2" | sed -n 's/^    //p' | LC_ALL=C sort
}
