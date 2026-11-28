# Shared helpers of the misc tests that time rocqchk under a CPU limit:
# rocqchk_discharged_global_key.sh and rocqchk_double_discharge.sh. Each
# sets T, the limit in seconds, and sources it with
#
#   . misc/rocqchk_cpu_limit.bash
#
# This file is deliberately not named *.sh: the misc target runs every
# misc/*.sh as a test of its own (see the "misc:" rule in test-suite/Makefile).
# That rule runs the script from the test-suite directory with $BIN set, so
# rocqchk is spelled "$BIN"rocqchk.

# The time keyword reports the CPU time of what it times, also when the limit
# kills rocqchk. It times a group that this shell runs, around the subshell
# that sets the limits: timed directly, that subshell printed no times when
# the limit killed rocqchk.
TIMEFORMAT='%3U %3S'

# timed_rocqchk <log> <times> [<ulimit argument>...] -- <rocqchk argument>...:
# runs rocqchk with its output in <log>, with no core file, the CPU limit of
# T s (ulimit -t) and, if any are given, ulimit <ulimit argument>..., and
# sets rc to its exit code and cpu to the CPU time (user + sys, in seconds)
# that bash wrote to <times>. If bash wrote none, prints the failure with
# <times> and <log>, and returns 1.
timed_rocqchk() {
  local log=$1 times=$2 usage
  shift 2
  local limits=()
  while [ "$1" != -- ]; do limits+=("$1"); shift; done
  shift
  rc=0
  { time { (
      ulimit -c 0
      if [ ${#limits[@]} -gt 0 ]; then ulimit "${limits[@]}"; fi
      ulimit -t "$T"
      exec "$BIN"rocqchk "$@" > "$log" 2>&1
    ) ; } ; } 2> "$times" || rc=$?
  # bash may report the signal before the times: the times are the last line.
  usage=$(grep -E '^[0-9]+\.[0-9]+ [0-9]+\.[0-9]+$' "$times" | tail -n 1)
  if [ -z "$usage" ]; then
    echo "FAILURE: no CPU time for rocqchk $* (exit code $rc):"
    cat "$times" "$log"
    return 1
  fi
  cpu=$(awk -v t="$usage" 'BEGIN { split(t, a, " "); printf "%.2f", a[1] + a[2] }')
}

# cpu_limit_or_refusal <name> <log>: after timed_rocqchk <log> ... exited
# with a non-zero code, prints which case it is for rocqchk on <name>: it
# reached the CPU limit (killed by SIGXCPU, exit 152, or SIGKILL, exit 137,
# after at least T - 1 s of CPU), or it refused (any other exit code, or
# exit 152 or 137 after less than T - 1 s of CPU; <log> is printed).
cpu_limit_or_refusal() {
  local name=$1 log=$2
  if { [ "$rc" = 152 ] || [ "$rc" = 137 ]; } \
     && awk -v c="$cpu" -v t="$T" 'BEGIN { exit !(c >= t - 1) }'; then
    echo "FAILURE (CPU limit): rocqchk reached the CPU limit of $T s on $name: $cpu s of CPU, exit code $rc."
  else
    echo "FAILURE (refusal): rocqchk exited with code $rc after $cpu s of CPU on $name:"
    cat "$log"
  fi
}
