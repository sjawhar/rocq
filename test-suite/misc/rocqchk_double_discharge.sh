#!/usr/bin/env bash
# rocqchk checks an opaque proof made inside sections in its discharged
# form, where each use of a section definition c is the cooked constant
# applied to the section variables, c x1 .. xn. The kernel's lazy machine
# keeps one value per constant per conversion, but each c x1 .. xn
# beta-reduces that value into a new closure, so no reduction of one use
# serves another. rocq compile checks the same proof at Qed inside the
# section, where c's value is reduced once. The checker therefore checks the
# discharged body with each c x1 .. xn bound once in the environment
# (checker/checkDischarged.ml).
#
# The fixture: two nested sections (Variable a : bool in G, Variable b : bool
# in P); run, FUEL steps of a machine on a bool; at each of K levels
# s_i := run FUEL s_(i-1)r, sp_i := spec s_i and s_ir := relay s_i sp_i,
# which reads s_i twice; and the opaque
#   Lemma relay_same : forall c, s18 = c -> s18r = c
# whose body converts s18 with s18r inside an application
# (eq_sym (@eq_sym bool s18r c H)). Each level reads the one under it
# twice, so without the binding the discharged check reduces the chain about
# 2^K times; with it, each c x1 .. xn is reduced once. K = 18, FUEL = 20000.
#
# rocqchk -j 1 runs with the harness of misc/rocqchk_cpu_limit.bash, under a
# CPU limit of T = 60 s (ulimit -t) and an explicit 64 MiB stack (ulimit -S
# -s 65536), so that a stack crash ends with rocqchk's own "Stack overflow"
# error and not with the CPU limit. The test passes only if rocqchk accepts
# the file in less than T/10 = 6 s of CPU (user + sys). Otherwise it prints
# which case it is: it accepted the file too slowly, or one of the cases of
# misc/rocqchk_cpu_limit.bash: cpu_limit_or_refusal.
#
# Measured on 07e45e36 (release profile, OCaml 4.14.2), on this fixture
# with FUEL = 20000: rocq compile takes 0.2 to 0.3 s at every K (0.23 to
# 0.24 s at K = 14 to 18). rocqchk -j 1 without the binding takes 0.8 s at
# K = 8, 3.1 s at K = 10, 12.4 s at K = 12, 49.3 s at K = 14 and 195.1 s
# at K = 16 of user CPU, four times as long for every two levels, at a
# peak RSS of 36 to 38 MB at every K; so about 780 s at K = 18, 13 times
# the limit. Here, on 07e45e36, rocqchk reaches the limit: 60.00 s of CPU,
# exit code 137. With the binding, K = 18 takes 0.11 s of CPU (release
# profile) and 0.16 s (dev profile, as make world builds).
set -eu

. misc/rocqchk_cpu_limit.bash

K=18
FUEL=20000
T=60

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT

# gen <K> <FUEL> prints the fixture.
gen() {
  local k=$1 fuel=$2 i
  cat <<HEAD
Fixpoint run (fuel : nat) (s : bool) : bool :=
  match fuel with O => s | S f => match s with true => run f false | false => run f true end end.
Definition spec (s : bool) : bool := negb (negb s).
Definition relay (s sp : bool) : bool := if sp then s else s.
Definition FUEL : nat := $fuel.
Section G.
Variable a : bool.
Section P.
Variable b : bool.
Definition s0r : bool := orb true (andb a b).
HEAD
  for ((i = 1; i <= k; i++)); do
    echo "Definition s$i : bool := run FUEL s$((i - 1))r."
    echo "Definition sp$i : bool := spec s$i."
    echo "Definition s${i}r : bool := relay s$i sp$i."
  done
  cat <<TAIL
Lemma relay_same : forall c, s$k = c -> s${k}r = c.
Proof. intros c H. exact (eq_sym (@eq_sym bool s${k}r c H)). Qed.
End P.
End G.
TAIL
}

gen "$K" "$FUEL" > "$d/Fix.v"

if ! "$BIN"rocq c -native-compiler no -R "$d" T "$d/Fix.v" > "$d/compile.log" 2>&1; then
  echo "FAILURE: compile failed:"
  cat "$d/compile.log"
  exit 1
fi

name="T.Fix (K = $K, FUEL = $FUEL)"
timed_rocqchk "$d/check.log" "$d/time" -S -s 65536 -- -silent -j 1 -R "$d" T -norec T.Fix || exit 1
if [ "$rc" = 0 ]; then
  if awk -v c="$cpu" -v t="$T" 'BEGIN { exit !(c < t / 10) }'; then
    echo "rocqchk -j 1 accepted $name in $cpu s of CPU."
    exit 0
  fi
  echo "FAILURE (too slow): rocqchk accepted $name in $cpu s of CPU, not less than T/10 = $((T / 10)) s."
  exit 1
fi
cpu_limit_or_refusal "$name" "$d/check.log"
exit 1
