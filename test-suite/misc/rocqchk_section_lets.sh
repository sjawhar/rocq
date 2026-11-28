#!/usr/bin/env bash
# rocqchk checks an opaque proof made inside sections in its discharged
# form, where each use of a transparent section definition c is the cooked
# constant applied to the section variables, c x1 .. xn. Before that check,
# the checker binds some of these applications, the keys, once each in the
# environment, and checks the body with the bindings in place of the
# applications (checker/checkDischarged.ml: prepare, and
# checker/checkDischargedKeys.ml: unfold, find_keys). When the check with
# the bindings does not accept, or on any mismatch, it runs the check
# without them. The binding must not change a verdict. A review of the
# design (dispatch://BET-1602/artifact/fix-soundness-review-md) lists 11
# conditions, each with a pair: A, an honest file that rocqchk accepts, and
# R, a forged file that it refuses. This test holds those pairs, so it
# passes on the checker without the binding and must pass on the checker
# with it.
#
# An R fails here if the check with the bindings accepts it. An A cannot
# fail by a refusal of that check, since the check without the bindings
# then runs and accepts it: it fails only by the anomaly of the put-back
# check that ROCQCHK_COOK_CROSS_CHECK runs, by a crash, or by a hang. Below,
# a lemma that "binds" a key makes the check with the bindings run on it.
# The checker binds nothing in a body that holds no key, so such a lemma
# writes the key in its proof: eq_refl c, where reflexivity can give
# eq_refl of the other side of the equation. The checker also binds nothing
# unless the value of one of the keys holds keys at least twice (the chain
# gate, checker/checkDischarged.ml). So each section below in which a lemma
# binds a key has, after its first variable n, k0 := n and k2 := k0 + k0,
# whose value holds k0 n twice, and each lemma that binds a key holds
# let _ : k2 = k2 := eq_refl in its proof, and binds k2 n and k0 n beside
# the keys that its case is about. C6 is the exception: its L and L2 bind
# nothing, and L3, whose proof must not use n, binds e k with a chain of
# its own, e2 := e + e, and holds let _ : e2 = e2 := eq_refl in its proof.
#
# Each family below is one file, compiled as <family>.Lib in a directory of
# its own: good/ holds Good, and bad*/ hold the Bad files, which differ
# only in the proof of one lemma, L, and in what makes that proof type-check
# there. In each family Good and Bad have the same sections, the same
# statements, and the same opaque proofs in the same order (a Bad lemma named
# pad* stands in for an opaque lemma that Bad makes transparent). Good and
# every Bad are honest files: each is an A. Each R is Good with one forged
# part, made by misc/rocqchk-section-lets/forge.ml:
# - splice: Good's library with Bad's table of opaque proofs, so that Good's
#   L gets Bad's proof (as misc/rocqchk_cook.sh does in Python, plus checks
#   that both tables hold the same lemmas in the same order);
# - handle: Good with the opaque handle of a lemma, its cooking information
#   included, taken from Bad (the forgery lives in the library segment);
# - user: Good with one constant of a stored proof given the user name of
#   another constant, its canonical name kept;
# - flags: a file with the typing flags of one constant taken from another
#   (used for one A, see (1)).
# Every A is accepted, and every R refused with the error that rocqchk
# without the binding prints, in modes of mode_args
# (misc/rocqchk_forge_common.bash): as a grader runs rocqchk and with the
# default options, with ROCQCHK_COOK_CROSS_CHECK set. The cases, by
# condition of the review:
#  (1) C1: rocq refuses typing flags that change inside a section ("Changing
#      typing flags inside sections is not allowed"), so a section
#      definition with guard checking off, used by a lemma that checks
#      guards, exists only in a forged file. A1: C1 compiled under Unset
#      Guard Checking, c := (fix f m := f m) n and A1 : c = c, with A1
#      given the flags of donor, defined before Unset Guard Checking
#      ("flags"). rocqchk checks c's body under c's flags and A1's body under
#      A1's, so it accepts the file. A1 binds c n, whose value is that
#      unguarded fix. R1: Bad, compiled under Unset Guard Checking, proves
#      L : True with c and that fix; Good's L, which binds c n, checks
#      guards: IllFormedRecBody.
#  (2) C2: c : Type@{u} := (fun _ => nat) n with Set < u, and A2 (x : c) :
#      x = x. R: Bad declares c : Set, and L applies (fun _ : Set => I) to c:
#      CantApplyBadType. A2 and R2's L bind c n. A binding typed by its value
#      (Set) would accept R2.
#  (3) C3, a polymorphic section: c@{k} : Type@{k+1}, d := n, and
#      A3@{k l} : c@{k} -> c@{l} -> d = d -> True. A3 binds d n; c, at the
#      non-empty instances k and l, is no key and stays as it is. R3: Bad's
#      L@{k l | k <= l} uses d and converts c@{k} to c@{l} through
#      Type@{k}; Good's L has no constraint: CantApplyBadType. R3's L binds
#      d n. A binding of c@{k} and c@{l} by one constant would
#      accept R3. R3b ("user"): in the proof of A3, the c@{k} of the first
#      binder is named d by its user name: IllFormedConstant. A3 binds d n,
#      and the forged constant, at a non-empty instance, is no key: the
#      check with the bindings meets it as it is. C3m, a monomorphic copy:
#      c := n, d := n and A3m : c = c /\ d = d, proved by
#      conj (@eq_refl nat c) (@eq_refl nat d). R3c ("user", constant 2): in
#      the proof of A3m, the second c of c = c, which the binding meets
#      after the first c n, is named d by its user name:
#      IllFormedConstant. A binding keyed by the canonical name would bind
#      it with the first c n, and the body it checks would no longer hold
#      it. The forged c comes before every d: rocqchk's typing shares a
#      constant with an earlier one of the same user name (kernel/hConstr.ml,
#      eq_leaf), so a forged c after a d is typed as that d, whose value is
#      c's, and 07e45e36 accepts such a file.
#  (4, 7, 10) AB: SProp variables P, p, q with c : P := p, a := n,
#      b := S n (Good) or n (Bad), f k := k + n. A4 : sbox P c = sbox P q,
#      proved by eq_refl (sbox P c), binds c P p, a key of an irrelevant
#      constant. A7 unfolds a fix whose match branches use f, a and b,
#      under binders; it binds a n and b n, and f's value is a function,
#      which is never bound. R4: L holds let _ : a = b := eq_refl, which
#      marking a and b irrelevant would make type-check: ActualType. R7: the
#      same under a fun, a match branch and a fix: ActualType. Condition 10:
#      Bad10's L holds (@eq_refl nat a <: a = b), a VM cast; it is the A,
#      and R10 is Good with it (ActualType), each with the VM on and off in
#      both modes. The L of R4, R7 and R10 binds a n and b n; R10's only
#      with the VM off, as with it on the checker binds nothing in a body
#      whose VM cast holds a key.
#  (5) C5: two is opaque (Lemma two : nat ... Qed), c := n + 0, and
#      A5 : c + two = c + two, which binds c n; two n has no value to bind.
#      R: Bad makes two a Definition (pad keeps the table's order) and L
#      uses c and holds let _ : two = n + 2 := eq_refl: ActualType. R5's L
#      binds c n. A binding of two n to its opaque proof would accept R5.
#  (6) C6: Let m := S n, c := m + m, L : c = m + m (the A: the body keeps
#      the Let as a let-in, the type substitutes it) and L2 : True using
#      every variable, both proved with no key in the body (L by
#      reflexivity, which gives eq_refl (m + m)), so the checker binds
#      nothing in them. Bad declares Variable n : bool. R6 and R6b
#      ("handle"): L's, and L2's, opaque handle comes from Bad, whose
#      cooking information abstracts n : bool: ActualType for both. L2's
#      proof, I, is well typed under
#      either handle, and its type forall n : bool, True differs from
#      forall n : nat, True only in the product's domain; with no section
#      constant in it, nothing is bound.
#      L3 : e = e, after Variable k : nat and e := k, has a proof that uses
#      e. R6c ("handle"): L3's handle comes from Bad. e does not use n, so
#      the body type-checks under Bad's block, and only the block's
#      n : bool against the statement's n : nat refuses it: ActualType. A
#      check that did not compare the block with the statement would bind
#      e k and accept R6c. C6d: g : nat := 0 before the section,
#      Let m : nat := g, c := n + 0, and L : True, whose proof uses c and
#      whose block holds m (Proof using All). Bad6d declares g : bool and
#      Let m : bool := g. R6d ("handle"): L's handle comes from Bad6d, so
#      L's block holds m : bool := g, with g : nat: ActualType. The block's
#      domains are those of the statement, so only the typing of the block
#      refuses it; a check that did not type the block would bind c n and
#      accept R6d.
#  (7) C7: Variables n m : nat and e := n + m (Good) or m + n (Bad), whose
#      key e n m has two arguments. R7b: Bad's L holds
#      let _ : e = m + n := eq_refl, and binds e n m: ActualType. A value
#      that put n and m in the other order in e's body would accept it.
#  (9) C9: ap := id (fun g k => g k + n), whose value is not a function as
#      it stands, and A9 := fix F m := match m with S j => ap F j | 0 => 0
#      end. A9 binds ap n, which the guard unfolds to see F j. R: Bad,
#      compiled under Unset Guard Checking, holds the same fix with ap F m
#      in L; Good's L, which binds ap n, checks guards: IllFormedRecBody.
#  (11) C11: an unused section definition, a polymorphic section lemma
#      with a private universe, a section inside a functor applied as
#      Module M := F N, and a section inside a sealed module whose lemma
#      implements a Parameter and uses an axiom, which -o reads from the
#      cooked proof. A11a, F.A11c and Sealed.sv bind a key (M.A11c, under
#      the substitution of the functor application, binds nothing). Its -o
#      summary is the one rocqchk without the binding prints, at -j 1 and at
#      -j 2 (where the check runs in a worker).
# Not here:
#  (8) memoized traversal: the review sketches no pair. An A for it needs a
#      cooked body whose tree expansion is exponential while its sharing
#      keeps it small. The stock cook that ROCQCHK_COOK_CROSS_CHECK runs
#      (Cooking.expand_constr, through Constr.map_with_binders) walks every
#      path of such a term, and the test suite sets that variable for every
#      rocqchk run, so rocqchk without the binding would not end on it here.
#  The VM fallback of condition 10 (a section constant whose bytecode does
#  not compile): the review found no honest file that has one.
#
# The refusal texts are those that rocqchk prints on 07e45e36 (release
# profile, OCaml 4.14.2). With the binding (release profile), the whole
# test, 83 rocqchk runs, takes 19.3 s (15.2 s user, 3.2 s sys).
set -eu

. misc/rocqchk_forge_common.bash

# So that a run by hand, outside make, also runs the cross-checks.
export ROCQCHK_COOK_CROSS_CHECK=1

D=misc/rocqchk-section-lets
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT

# chain: k0 := n and k2 := k0 + k0, whose value holds k0 n twice. A lemma
# that binds keys holds let _ : k2 = k2 := eq_refl in its proof (the header
# says why).
chain() {
  printf 'Definition k0 : nat := n.\nDefinition k2 : nat := k0 + k0.\n'
}

# The families. gen_<family> <variant> prints the file.

# C1: good; bad, under Unset Guard Checking, with an unguarded fix in L;
# off, under Unset Guard Checking, with an unguarded fix in c.
gen_C1() {
  local U='' F='match m with 0 => 0 | S k => f k end' X='I'
  case $1 in
    bad) U='Unset Guard Checking.'
      X='let _ : k2 = k2 := eq_refl in let _ := c in let _ := (fix f (m : nat) : nat := f m) n in I' ;;
    off) U='Unset Guard Checking.' F='f m' ;;
  esac
  cat <<EOF
Definition donor : nat := 0.
$U
Section S.
Variable n : nat.
$(chain)
Definition c : nat := (fix f (m : nat) : nat := $F) n.
Lemma A1 : c = c. Proof. exact (let _ : k2 = k2 := eq_refl in @eq_refl nat c). Qed.
Lemma L : True. Proof using All. exact ($X). Qed.
End S.
EOF
}

gen_C2() {
  local T='Type@{u}' X='I'
  if [ "$1" = bad ]; then T='Set' X='let _ : k2 = k2 := eq_refl in let _ := (fun _ : Set => I) c in I'; fi
  cat <<EOF
Universe u.
Constraint Set < u.
Section S.
Variable n : nat.
$(chain)
Definition c : $T := (fun _ : nat => nat) n.
Lemma A2 (x : c) : x = x. Proof. exact (let _ : k2 = k2 := eq_refl in eq_refl). Qed.
Lemma L : True. Proof using All. exact ($X). Qed.
End S.
EOF
}

gen_C3() {
  local C='' X='I'
  if [ "$1" = bad ]; then
    C=' | k <= l'
    X='let _ : k2 = k2 := eq_refl in let _ := d in
      let _ := (fun x : c@{k} => (fun y : Type@{k} => (fun _ : c@{l} => I) y) x) in I'
  fi
  cat <<EOF
Set Universe Polymorphism.
Section S.
Variable n : nat.
$(chain)
Definition c@{k} : Type@{k+1} := (fun _ : nat => Type@{k}) n.
Definition d : nat := n.
Lemma A3@{k l} : c@{k} -> c@{l} -> d = d -> True.
Proof. intros _ _ _. exact (let _ : k2 = k2 := eq_refl in I). Qed.
Lemma L@{k l$C} : True. Proof using All. exact ($X). Qed.
End S.
EOF
}

# C3m: good only; R3c is a forgery of it.
gen_C3m() {
  cat <<EOF
Section S.
Variable n : nat.
$(chain)
Definition c : nat := n.
Definition d : nat := n.
Lemma A3m : c = c /\ d = d.
Proof. exact (let _ : k2 = k2 := eq_refl in conj (@eq_refl nat c) (@eq_refl nat d)). Qed.
End S.
EOF
}

gen_AB() {
  local B='n' X
  case $1 in
    good) B='S n' X='I' ;;
    bad4) X='let _ : k2 = k2 := eq_refl in let _ : a = b := eq_refl in I' ;;
    bad7) X='let _ : k2 = k2 := eq_refl in let _ := (fun k : nat => match k with 0 => I | S j =>
    (fix g (m : nat) : True :=
       match m with 0 => (let _ : a = b := eq_refl in I) | S i => g i end) j end) in I' ;;
    bad10) X='let _ : k2 = k2 := eq_refl in let _ := (@eq_refl nat a <: a = b) in I' ;;
  esac
  cat <<EOF
Inductive sBox (A : SProp) : Prop := sbox : A -> sBox A.
Section S.
Variable n : nat.
$(chain)
Variable P : SProp.
Variables p q : P.
Definition c : P := p.
Definition a : nat := n.
Definition b : nat := $B.
Definition f (k : nat) : nat := k + n.
Lemma A4 : sbox P c = sbox P q.
Proof. exact (let _ : k2 = k2 := eq_refl in @eq_refl (sBox P) (sbox P c)). Qed.
Lemma A7 : forall k : nat,
  (fix g (m : nat) : nat := match m with 0 => f a | S j => f (g j) + (b - b) end) (S k)
  = f ((fix g (m : nat) : nat := match m with 0 => f a | S j => f (g j) + (b - b) end) k)
    + (b - b).
Proof. intro k. refine (let _ : k2 = k2 := eq_refl in _). reflexivity. Qed.
Lemma L : True. Proof using All. exact ($X). Qed.
End S.
EOF
}

gen_C7() {
  local E='n + m' X='I'
  if [ "$1" = bad ]; then E='m + n' X='let _ : k2 = k2 := eq_refl in let _ : e = m + n := eq_refl in I'; fi
  cat <<EOF
Section S.
Variables n m : nat.
$(chain)
Definition e : nat := $E.
Lemma L : True. Proof using All. exact ($X). Qed.
End S.
EOF
}

gen_C5() {
  local TWO='Lemma two : nat. Proof using n. exact (n + 2). Qed.' X='I'
  if [ "$1" = bad ]; then
    TWO='Definition two : nat := n + 2.
Lemma pad : nat. Proof using n. exact (n + 2). Qed.'
    X='let _ : k2 = k2 := eq_refl in let _ := c in let _ : two = n + 2 := eq_refl in I'
  fi
  cat <<EOF
Section S.
Variable n : nat.
$(chain)
Definition c : nat := n + 0.
$TWO
Lemma A5 : c + two = c + two. Proof. exact (let _ : k2 = k2 := eq_refl in eq_refl). Qed.
Lemma L : True. Proof using All. exact ($X). Qed.
End S.
EOF
}

gen_C6() {
  local N='nat' M='S n'
  if [ "$1" = bad ]; then N='bool' M='S (if n then 0 else 0)'; fi
  cat <<EOF
Section S.
Variable n : $N.
Let m := $M.
Definition c := m + m.
Lemma L : c = m + m. Proof. reflexivity. Qed.
Lemma L2 : True. Proof using All. exact I. Qed.
Variable k : nat.
Definition e : nat := k.
Definition e2 : nat := e + e.
Lemma L3 : e = e. Proof using All. exact (let _ : e2 = e2 := eq_refl in @eq_refl nat e). Qed.
End S.
EOF
}

# C6d: good; bad, where g, and so the Let m, is a bool. R6d is Good with
# Bad's handle of L.
gen_C6d() {
  local T='nat' G='0'
  if [ "$1" = bad ]; then T='bool' G='true'; fi
  cat <<EOF
Definition g : $T := $G.
Section S.
Variable n : nat.
$(chain)
Let m : $T := g.
Definition c : nat := n + 0.
Lemma L : True.
Proof using All. exact (let _ : k2 = k2 := eq_refl in let _ : c = c := eq_refl in I). Qed.
End S.
EOF
}

# C9: good; bad, under Unset Guard Checking, with an unguarded fix in L.
gen_C9() {
  local U='' X='I'
  if [ "$1" = bad ]; then
    U='Unset Guard Checking.'
    X='let _ : k2 = k2 := eq_refl in
      let _ := (fix F (m : nat) : nat := match m with S j => ap F m | 0 => 0 end) in I'
  fi
  cat <<EOF
$U
Section S.
Variable n : nat.
$(chain)
Definition ap : (nat -> nat) -> nat -> nat := id (fun g k => g k + n).
Lemma A9 : nat -> nat.
Proof using All.
  exact (let _ : k2 = k2 := eq_refl in fix F (m : nat) : nat := match m with S j => ap F j | 0 => 0 end).
Qed.
Lemma L : True. Proof using All. exact ($X). Qed.
End S.
EOF
}

gen_C11() {
  cat <<EOF
Axiom used_ax : True.

Section S.
Variable n : nat.
$(chain)
Definition used : nat := S n.
Definition unused : nat := n + 1.
Lemma A11a : used = S n. Proof. exact (let _ : k2 = k2 := eq_refl in @eq_refl nat used). Qed.
End S.

Set Universe Polymorphism.
Section P.
Universe w.
Variable B : Type@{w}.
Variable b0 : B.
Definition pc : B := b0.
Lemma A11b : pc = b0. Proof. pose (T := Type). reflexivity. Qed.
End P.
Unset Universe Polymorphism.

Module Type NT. Parameter v : nat. End NT.
Module F (X : NT).
Section FS.
Variable n : nat.
$(chain)
Definition fc : nat := n + X.v.
Lemma A11c : fc = n + X.v. Proof. exact (let _ : k2 = k2 := eq_refl in @eq_refl nat fc). Qed.
End FS.
End F.
Module N. Definition v : nat := 3. End N.
Module M := F N.
Lemma A11d : forall k, M.fc k = k + 3. Proof. intro k. reflexivity. Qed.

Module Type SIG. Parameter sv : forall n : nat, n = n. End SIG.
Module Sealed : SIG.
Section SS.
Variable n : nat.
$(chain)
Definition sc : nat := n.
Lemma sv : sc = n.
Proof. pose proof used_ax as H. exact (let _ : k2 = k2 := eq_refl in @eq_refl nat sc). Qed.
End SS.
End Sealed.
EOF
}

# build <family> <variant>: write $d/<family>/<variant>/Lib.v and compile
# it as <family>.Lib.
build() {
  local dir=$d/$1/$2
  mkdir -p "$dir"
  "gen_$1" "$2" > "$dir/Lib.v"
  if ! "$BIN"rocq c -native-compiler no -R "$dir" "$1" "$dir/Lib.v" > "$dir/compile.log" 2>&1; then
    echo "FAILURE: compile failed: $1 ($2):"
    cat "$dir/compile.log"
    exit 1
  fi
}

# forge <command> <argument>... <out>: run $D/forge.ml, which writes <out>.
forge() {
  mkdir -p "$(dirname "${@: -1}")"
  if ! ocaml "$D/forge.ml" "$@" > "$d/forge.log" 2>&1; then
    echo "FAILURE: forge.ml $* failed:"
    cat "$d/forge.log"
    exit 1
  fi
}

# check_a <what> <family> <variant> <mode>...: rocqchk accepts
# $d/<family>/<variant>/Lib.vo in each mode of mode_args.
check_a() {
  local what=$1 fam=$2 var=$3 mode
  shift 3
  for mode in "$@"; do
    mode_args "$mode" "$d/$fam/$var" "$fam"
    must_accept "$d/out.log" \
      "FAILURE: rocqchk ($mode) refused an honest file, $what: rocqchk ${mode_argv[*]}" "${mode_argv[@]}"
  done
  echo "  A $fam/$var accepted ($*): $what"
}

# check_r <what> <error> <family> <variant> <mode>...: rocqchk refuses
# $d/<family>/<variant>/Lib.vo in each mode of mode_args, with an error that
# the extended regular expression <error> matches.
check_r() {
  local what=$1 error=$2 fam=$3 var=$4 mode
  shift 4
  for mode in "$@"; do
    mode_args "$mode" "$d/$fam/$var" "$fam"
    must_refuse "$d/out.log" "$error" \
      "FAILURE: rocqchk ($mode) accepted a forgery, $what: rocqchk ${mode_argv[*]}" \
      "FAILURE: rocqchk ($mode) refused a forgery, $what, without /$error/: rocqchk ${mode_argv[*]}" \
      "${mode_argv[@]}"
  done
  echo "  R $fam/$var refused ($*): $what"
}

both=(grader default)
vm=(grader grader-novm default default-vm)

case_1() {
  build C1 good
  build C1 bad
  build C1 off
  forge splice "$d/C1/good/Lib.vo" "$d/C1/bad/Lib.vo" L "$d/C1/r1/Lib.vo"
  forge flags "$d/C1/off/Lib.vo" A1 donor "$d/C1/a1/Lib.vo"
  check_a "c with guard checking off, used in A1, which checks guards (forged flags)" C1 a1 "${both[@]}"
  check_a "Good" C1 good "${both[@]}"
  check_a "Bad, under Unset Guard Checking" C1 bad "${both[@]}"
  check_a "c with an unguarded fix, under Unset Guard Checking" C1 off "${both[@]}"
  check_r "an unguarded fix in L, which checks guards" 'Type error: IllFormedRecBody' C1 r1 "${both[@]}"
}

case_2() {
  build C2 good
  build C2 bad
  forge splice "$d/C2/good/Lib.vo" "$d/C2/bad/Lib.vo" L "$d/C2/r2/Lib.vo"
  check_a "c : Type@{u} with Set < u, used in A2" C2 good "${both[@]}"
  check_a "Bad, c : Set" C2 bad "${both[@]}"
  check_r "c : Type@{u} given to a function on Set" 'Type error: CantApplyBadType' C2 r2 "${both[@]}"
}

case_3() {
  build C3 good
  build C3 bad
  build C3m good
  forge splice "$d/C3/good/Lib.vo" "$d/C3/bad/Lib.vo" L "$d/C3/r3/Lib.vo"
  forge user "$d/C3/good/Lib.vo" A3 1 c d "$d/C3/r3b/Lib.vo"
  forge user "$d/C3m/good/Lib.vo" A3m 2 c d "$d/C3m/r3c/Lib.vo"
  check_a "c@{k} and c@{l} in A3" C3 good "${both[@]}"
  check_a "Bad, L@{k l | k <= l}" C3 bad "${both[@]}"
  check_r "c@{k} converted to c@{l} without k <= l" 'Type error: CantApplyBadType' C3 r3 "${both[@]}"
  check_r "a c of A3's proof named d by its user name" 'Type error: IllFormedConstant' C3 r3b "${both[@]}"
  check_a "c n twice and d n in A3m" C3m good "${both[@]}"
  check_r "the second c n of A3m's proof, after the first, named d by its user name" \
    'Type error: IllFormedConstant' C3m r3c "${both[@]}"
}

case_4_7_10() {
  local v
  build AB good
  for v in bad4 bad7 bad10; do
    build AB $v
    forge splice "$d/AB/good/Lib.vo" "$d/AB/$v/Lib.vo" L "$d/AB/r${v#bad}/Lib.vo"
  done
  build C7 good
  build C7 bad
  forge splice "$d/C7/good/Lib.vo" "$d/C7/bad/Lib.vo" L "$d/C7/r7b/Lib.vo"
  check_a "A4 (c irrelevant) and A7 (constants under binders)" AB good "${both[@]}"
  check_a "Bad4, a = b" AB bad4 "${both[@]}"
  check_a "Bad7, a = b under binders" AB bad7 "${both[@]}"
  check_a "Bad10, a = b by a VM cast" AB bad10 "${vm[@]}"
  check_r "(4) a = b by eq_refl, with b := S n" 'Type error: ActualType' AB r4 "${both[@]}"
  check_r "(7) a = b by eq_refl under a fun, a match and a fix" 'Type error: ActualType' AB r7 "${both[@]}"
  check_r "(10) a = b by a VM cast" 'Type error: ActualType' AB r10 "${vm[@]}"
  check_a "Good, e := n + m" C7 good "${both[@]}"
  check_a "Bad, e := m + n" C7 bad "${both[@]}"
  check_r "(7) e = m + n by eq_refl, with e := n + m" 'Type error: ActualType' C7 r7b "${both[@]}"
}

case_5() {
  build C5 good
  build C5 bad
  forge splice "$d/C5/good/Lib.vo" "$d/C5/bad/Lib.vo" L "$d/C5/r5/Lib.vo"
  check_a "two opaque, used in A5 beside c" C5 good "${both[@]}"
  check_a "Bad, two transparent" C5 bad "${both[@]}"
  check_r "two unfolded although opaque" 'Type error: ActualType' C5 r5 "${both[@]}"
}

case_6() {
  build C6 good
  build C6 bad
  build C6d good
  build C6d bad
  forge handle "$d/C6/good/Lib.vo" "$d/C6/bad/Lib.vo" L "$d/C6/r6/Lib.vo"
  forge handle "$d/C6/good/Lib.vo" "$d/C6/bad/Lib.vo" L2 "$d/C6/r6b/Lib.vo"
  forge handle "$d/C6/good/Lib.vo" "$d/C6/bad/Lib.vo" L3 "$d/C6/r6c/Lib.vo"
  forge handle "$d/C6d/good/Lib.vo" "$d/C6d/bad/Lib.vo" L "$d/C6d/r6d/Lib.vo"
  check_a "a Let in the section, in L's statement" C6 good "${both[@]}"
  check_a "Bad, n : bool" C6 bad "${both[@]}"
  check_r "L's handle cooks n : bool" 'Type error: ActualType' C6 r6 "${both[@]}"
  check_r "L2's handle cooks n : bool" 'Type error: ActualType' C6 r6b "${both[@]}"
  check_r "L3's handle cooks n : bool, which e k does not use" 'Type error: ActualType' C6 r6c "${both[@]}"
  check_a "Let m : nat := g in L's block" C6d good "${both[@]}"
  check_a "Bad6d, g : bool and Let m : bool := g" C6d bad "${both[@]}"
  check_r "L's handle cooks Let m : bool := g, with g : nat" 'Type error: ActualType' C6d r6d "${both[@]}"
}

case_9() {
  build C9 good
  build C9 bad
  forge splice "$d/C9/good/Lib.vo" "$d/C9/bad/Lib.vo" L "$d/C9/r9/Lib.vo"
  check_a "a fix whose guard unfolds ap n" C9 good "${both[@]}"
  check_a "Bad, under Unset Guard Checking" C9 bad "${both[@]}"
  check_r "ap F m in a fix, in L, which checks guards" 'Type error: IllFormedRecBody' C9 r9 "${both[@]}"
}

# The -o summary of C11, as rocqchk without the binding prints it on
# 07e45e36, up to the libraries admitted without checking (Corelib's, under
# -norec), trailing blanks removed. Sealed.sv's proof uses C11.Lib.used_ax;
# under -o the main process cooks that proof for the summary
# (Mod_checking.register_opacified_constant).
want_11() {
  cat <<'EOF'
CONTEXT SUMMARY
===============

* Theory: Set is predicative

* Theory: Rewrite rules are not allowed

* Axioms:
    C11.Lib.used_ax

* Constants/Inductives relying on type-in-type: <none>

* Constants/Inductives relying on unsafe (co)fixpoints: <none>

* Inductives whose positivity is assumed: <none>

* Inductives relying on indices not mattering:
    Corelib.Init.Datatypes.eq_true
    Corelib.Init.Logic.eq

EOF
}

summary() {
  awk '/^CONTEXT SUMMARY/ { p = 1 } /^\* Libraries admitted/ { p = 0 } p' "$1" | sed 's/[[:space:]]*$//'
}

case_11() {
  local j
  build C11 good
  check_a "an unused section definition, a private polymorphic universe, sections in a functor and a sealed module" \
    C11 good default
  want_11 > "$d/want11"
  for j in 1 2; do
    mode_args grader "$d/C11/good" C11
    must_accept "$d/out.log" "FAILURE: rocqchk -j $j refused C11: rocqchk -j $j ${mode_argv[*]}" -j $j "${mode_argv[@]}"
    summary "$d/out.log" > "$d/got11"
    if ! diff -u "$d/want11" "$d/got11"; then
      echo "FAILURE: the -o summary of C11 at -j $j is not the expected one"
      exit 1
    fi
  done
  echo "  A C11/good: -o summary as expected at -j 1 and -j 2"
}

status=0
for c in 1 2 3 4_7_10 5 6 9 11; do
  echo "case $c:"
  if ! ( "case_$c" ); then
    echo "case $c FAILED"
    status=1
  fi
done
exit $status
