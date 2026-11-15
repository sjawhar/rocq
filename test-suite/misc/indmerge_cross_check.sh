#!/usr/bin/env bash

# The test suite runs every rocqchk with ROCQCHK_INDMERGE_CROSS_CHECK set
# (test-suite/Makefile): each inductive block pair that the comparator of
# rocqchk -compare compares, and each pair that Indmerge.merge compares under
# -merge-inductives, is compared by both comparisons, and a disagreement stops
# the run with an anomaly (checker/check_compare.ml). A check that is never
# reached proves nothing, so this test counts the checks. With the check's log
# on, it runs the definitions case of misc/compare.sh and
# misc/merge_inductives_demo.sh, whose rocqchk -merge-inductives run merges
# the two copies of color and tree, and it fails unless the log holds at least
# one check of each side.
set -eu

log_dir=$(mktemp -d)
trap 'rm -rf "$log_dir"' EXIT

export ROCQCHK_INDMERGE_CROSS_CHECK=1
export ROCQCHK_INDMERGE_CROSS_CHECK_LOG="$log_dir/checks"
: > "$ROCQCHK_INDMERGE_CROSS_CHECK_LOG"

bash misc/compare.sh definitions \
  || { echo "FAILED: misc/compare.sh definitions"; exit 1; }
bash misc/merge_inductives_demo.sh \
  || { echo "FAILED: misc/merge_inductives_demo.sh"; exit 1; }

compare_checks=$(grep -c '^compare ' "$ROCQCHK_INDMERGE_CROSS_CHECK_LOG" || true)
merge_checks=$(grep -c '^merge ' "$ROCQCHK_INDMERGE_CROSS_CHECK_LOG" || true)
echo "indmerge_cross_check: $compare_checks compare checks, $merge_checks merge checks"
[ "$compare_checks" -gt 0 ] || { echo "FAILED: no compare check was made"; exit 1; }
[ "$merge_checks" -gt 0 ] || { echo "FAILED: no merge check was made"; exit 1; }
