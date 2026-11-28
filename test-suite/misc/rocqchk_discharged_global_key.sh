#!/usr/bin/env bash
# rocqchk checks an opaque proof made inside a section in its discharged
# form, where each use of a section definition c is c applied to the
# section variables, c x1 .. xn. It checks that body with some of these
# applications bound once each, by a fresh constant c' with no argument
# (checker/checkDischarged.ml). Conversion decides c xs against c ts by
# comparing xs with ts, and stops there when they are convertible; it
# decides c' against c ts by unfolding one of them, and then it may reduce
# c's value. So a binding must never meet, in the check, its own constant
# in a term that is not rewritten. Nor may it make conversion compare
# arguments that it skips between two uses of c: typed conversion skips the
# arguments that c's bytecode marks unused, and c' has no bytecode. Nor may
# it make conversion unfold first a side that rocqchk without the binding
# unfolds later, or make the VM run what rocqchk without it does not.
#
# rocqchk binds keys only when they form a chain, the value of one of them
# holding keys at least twice (checker/checkDischarged.ml: the chain gate).
# So each file below up to VMLetKey has, after Variable n, k0 := n and
# k2 := k0 + k0, whose value holds k0 n twice, and the proof term of its
# lemma L (L2 in LetArg and LemmaType) holds let _ : k2 = k2 := eq_refl in
# around the term that the file is about, or, in Mask, LetPair and
# VMLetKey, under the let-ins that the proof makes first (H, or y and y')
# and around the rest: rocqchk binds k2 n and k0 n beside the keys of that
# term, which the descriptions below leave out.
#
# Each file below has a global constant heavy, a match on rec2 forty true,
# which reduces about 2^40 steps (rec2 reads its value twice at each of
# forty levels), and one opaque proof whose check compares heavy, or the
# section definition hc := heavy n, applied to convertible arguments, or
# (Mask) a section definition applied to arguments that differ only where
# its bytecode marks them unused. Each match has a return clause: without
# one, rocq compile does not finish elaborating the match of heavy. rocq
# compile and rocqchk without the binding decide each comparison by
# comparing the arguments, or by skipping them:
# - LetArg: Variable n, Let m := n + 0, L1 : heavy m = heavy m, and L2,
#   whose proof uses L1 at the type heavy m = heavy m. Discharging
#   substitutes m in L1's statement, so the check of L2 compares heavy m
#   with heavy (n + 0).
# - PlusArg: Variable n, and L, whose proof holds
#   let _ : heavy (0 + n) = heavy n := eq_refl in I. (With the sides the
#   other way, a binding of heavy n is unfolded on the left, and conversion
#   then unfolds heavy (0 + n) on the right and compares the two matches on
#   rec2 forty true by their parts, without reducing them.)
# - LemmaType: Variable n, hc := heavy n, L1 : hc = hc, and L2 : hc = hc,
#   proved by L1. The check of L2 compares its statement with the type of
#   L1 n, which comes from L1's statement in the environment.
# - HypType: Variable n, hc := heavy n, Hypothesis H : hc = true, and
#   L : hc = true, proved by H. The check of L compares its statement with
#   the type of H, which is in the block of binders before the body.
# - BodyRead: Variable n, hc := heavy n, g (b : bool) := Some hc, and
#   L : g true = Some hc, proved by eq_refl (g true). The check of L
#   unfolds g true to the body of g, Some hc, and compares it with Some hc.
# - IndData: Variable n, hc := heavy n, the inductive I : bool -> Type
#   with one constructor C : I hc, and L : I hc, proved by C. The check of
#   L compares the type of C, from the data of I, with its statement.
# The next four have Variable n, hc := heavy n and the inductive box with
# one constructor mk (u : unit) (b := hc), whose let-in value is hc. Their
# checks reduce the match m := match mk tt return bool with mk _ b => b end
# to that value, which only the data of box holds:
# - LetInBlock: Hypothesis H : m = true, and L : hc = true, proved by H.
#   The check of L compares its statement with the type of H, in the block.
# - LetInValue: hv := Some m, and L : hv = Some hc, proved by eq_refl hv.
#   The check of L unfolds hv, a definition that has a value.
# - LetInBody: g (u : unit) := Some m (with mk u for mk tt), and
#   L : g tt = Some hc, proved by eq_refl (g tt). The check of L unfolds
#   g tt to the body of g.
# - LetInIndData: the inductive I : bool -> Type with one constructor
#   C : I m, and L : I hc, proved by C. The check of L compares the type of
#   C, from the data of I, with its statement.
# - Mask: Variable n, c : bool -> nat := let k := n in fun m => k, whose
#   bytecode marks its argument m unused, and L : c true = n, whose proof
#   term is let H : c true = n := eq_refl (c (heavy n)) in H. The proof
#   makes it with change_no_check, so that rocq compile does not compare
#   heavy n with true. Typing the let-in compares c (heavy n) with c true
#   by typed conversion, which skips m.
#
# The next seven files use rec2_forty_true: rec2 forty true written out, a
# fix applied to the numeral 40 and to true, with no constant in it.
# Conversion reduces each side without unfolding constants before it
# compares them (Conversion.eqappr), and that reduces rec2_forty_true in
# about 2^40 steps, where heavy stops at rec2. In each file a section
# definition holds a match on rec2_forty_true, and the check of L meets it
# in a comparison that rocq compile and rocqchk without the binding decide
# without reducing it: by comparing arguments, or by unfolding the other
# side first, which gives the same application. A binding that conversion
# unfolded before the other side, as it does a local definition
# (Conv_oracle.oracle_order: a Rel is Expand), would reduce the match. Each
# proof uses change_no_check, so that rocq compile does not compare the two
# sides before Qed.
# - LetPair: Variable n, Let l1 := true, Let l2 := true,
#   c (m : bool) := the match, with m and n in its branches, and L : True,
#   whose proof term is let H : c l1 = c l2 := eq_refl (c l1) in I. Typing
#   the let-in compares c n l1 with c n l2, and so l1 with l2. The key of
#   both is c n, a function, which is not bound; bindings of c n l1 and of
#   c n l2 would be compared by their values.
# - StrategyLevel: Variable n, c := the match, Strategy 1000 [c], and
#   L : G c = c, with G (b : bool) := b before the section, proved by
#   eq_refl (G c). Conversion unfolds G first, as the more transparent
#   constant, and meets c against c. Without the Strategy command it would
#   unfold c first, the right side at the same level. c n is not bound: its
#   level is not the default one.
# - FunValue: Variable n, f (x : bool) := the match, with x in it, and
#   L : f true = G2 f true, with G2 (h : bool -> bool) (x : bool) := h x
#   before the section, proved by eq_refl (f true). Conversion unfolds G2
#   first, the right side at the same level, and meets f true against
#   f true. f n is a function, which is not bound.
# - PolyBody: under Set Universe Polymorphism, Variable n, d := the match,
#   c@{k} (T : Type@{k}) := d, and L : d = c@{Set} nat, proved by
#   eq_refl d. Conversion unfolds c first, the right side at the same
#   level, and meets d against d. c, at the non-empty instance Set, is no
#   key, so the check reads its body, which holds d: d n is not bound.
# - RewriteRules, compiled with -allow-rewrite-rules: Variable n, c := the
#   match, and L : c = G c, proved by eq_refl c. Conversion unfolds G
#   first, the right side at the same level, and meets c against c. With
#   rewrite rules allowed, rocqchk binds nothing.
# - Order: the file of RewriteRules, compiled without that option. c n is
#   a value that is not a function, at the default level, and only the
#   statement and the proof hold it: it is bound, and its constant c' is
#   at the level of c, so conversion unfolds G first there too.
# - FunValueLet: FunValue with f := let k := n in fun x => the match, with
#   k and x in it. f n is a let-in whose body is a function: it is bound,
#   and conversion unfolds G2 first, as in Order.
#
# The next three have Variable n, Let m : bool := rec2_forty_true and
# c := n, whose key c n rocqchk binds. Cooking substitutes m's value in
# the statement and keeps m as a let-in of the body, whose typing
# substitutes the same value in the type of the body: rocq compile and
# rocqchk without the binding compare that value with itself, or m's Rel
# with itself, and never reduce it. A check that met the value against
# m's Rel, or against a variable that stands for m, would reduce
# rec2_forty_true, as conversion reduces both sides before it unfolds a
# local definition (Conversion.eqappr):
# - LetHyp: Hypothesis H : m = true, and L : c = c, proved by eq_refl with
#   every variable used. The type of H in the block mentions m, and the
#   statement's domain for H holds its value.
# - LetStmt: L : m = m /\ c = c, proved by conj eq_refl eq_refl. The type
#   of the body mentions m where the statement holds its value.
# - LetHypBody: LetHyp, with the proof let _ : m = true := H in eq_refl.
#   Typing that let-in compares the type of H with m = true, both with m's
#   Rel in the body: a check that put the value in place of m in the type
#   of H, and kept m's Rel in the body, would meet the two.
#
# VMDeadBranch, compiled with -bytecode-compiler no: spin k, which makes
# 2^k calls, before the section, Variable n, big := spin 36 + n, and
# L : (if true then 0 else big) = 0, proved by eq_refl 0 cast to it by a VM
# cast. With the VM on, typing the cast compiles its two types and runs
# only the branch that true selects. The file guards that the VM never
# runs a key's value: linking a constant with bytecode runs its code, which
# for a constant with the value of big n would run spin 36. rocqchk binds
# nothing here with the VM on, as the VM cast holds the key big n
# (checker/checkDischargedKeys.ml: cast_gate), and a key's constant c' has
# no bytecode anyway, so the VM would keep it as an atom. rocq compile,
# without the VM, checks the cast by reducing the if.
#
# VMLetKey, checked with the VM on only: Variable n, b0 := orb true (n =? n),
# and L : True, whose proof binds y and y' to b0 and holds a VM cast of
# eq_refl (if y then true else rec2_forty_true) to
# (if y then true else rec2_forty_true) = (if y' then true else
# rec2_forty_true). rocq compile and rocqchk without the binding evaluate
# b0 n to true, so the VM runs one branch of each if. Both b0 n are the key
# of one binding, which the VM keeps as an atom: each if would be stuck on
# it, and the VM would compare both branches of the two, rec2_forty_true
# included. The cast holds no key, only y and y', whose let-in values do:
# rocqchk binds nothing in a body where a VM cast reaches a key through the
# binders above it, with the VM on. The file is checked with the VM on
# only, as the review that found this case ran it.
#
# Big: path, tree and grow x k p, a tree of 2^k leaves leaf x p' with
# distinct p', before the section; then Variable n, NB = 12 definitions
# big1 .. big12, each grow n D p, for a distinct p, computed by Eval cbv
# (a tree of 2^D = 8192 leaves leaf n p'); and BL = 800 lemmas
# (big1, .., big12) = (big1, .., big12), each proved by eq_refl. rocqchk
# without the binding checks each in microseconds, without reading the
# values of the bigs. Binding their keys would read those values, once per
# lemma, to substitute them and to scan them. Big has no chain, and
# rocqchk gives up on each lemma at the chain gate, before it unfolds any
# key (checker/checkDischargedKeys.ml: chain_gate): within the budget of
# work of a lemma, the gate reads what the values of the bigs hold, keeps
# it for the file, and reads each value about once for the file, plus once
# in part where the budget of a lemma runs out in it. It checks each lemma
# without the binding. (Fewer and larger trees would make rocq compile,
# and rocqchk without the binding, slow: their time grows faster than the
# size of a tree.)
#
# The next six files are about the cost of the binding itself. Each has
# enough lemmas that a checker that misses what the file guards runs past
# the CPU limit, where rocqchk without the binding takes a fraction of it.
# An earlier version of this change missed four of them: it gave the
# constant c' of a key the whole block as section hypotheses (Hyps), bound
# keys that form no chain (OneKey), kept no record of what reading a value
# cost (ValueCost), and did not count the work of cast_gate against the
# budget (CastSets). A later one decided the chain gate only once it had
# unfolded and scanned the values of the keys of a proof (ValueCost12),
# and the next one did not count against the budget what the gate reads
# of the values that it has kept (ShapeHeads).
# Hyps, OneKey, ValueCost and ValueCost12 use the trees of Big.
# - Hyps: HV = 3000 variables x1 .. x3000 : nat, c := x1, d := c + c, and
#   HL = 16 lemmas exists t : tree, True, each using every variable and
#   proved with grow d HD top (HD = 14), computed by cbv: 16384 leaves
#   leaf d p. Its keys are d x1 and c x1. Typing the constant of d x1
#   checks its section hypotheses against the environment at each of the
#   16384 places that hold it: they are x1 alone, as d's are in the
#   section, and not the 3000 variables of the block
#   (checker/checkDischarged.ml: prepare).
# - OneKey: Hyps with leaf c p, so that c x1, whose value holds no key, is
#   its one key: rocqchk checks it without the binding (the chain gate).
# - ValueCost: Variable n, big := grow n CD top (CD = 14), computed by Eval
#   cbv, about 65,500 nodes, and CL = 24000 lemmas big = big, each proved
#   by eq_refl. Putting n in big's value for the key big n would run out
#   of the budget, 50,000 nodes for so small a proof. The chain gate of
#   the first lemma reads that value within the budget and runs out of it;
#   rocqchk keeps what that cost, and from the second lemma on gives up at
#   the gate before it reads anything (checker/checkDischargedKeys.ml:
#   unfold_costs, which the gate and unfold share).
# - ValueCost12: ValueCost with a tree of depth CD12 = 12, about 16,400
#   nodes, and CL12 = 24000 lemmas. Putting n in big's value fits in the
#   budget, so a checker that decides the chain gate only once it has
#   bound the keys of a proof puts n in that value and scans it, up to the
#   whole budget, for every lemma; rocqchk finds that big n forms no chain
#   from what big's value holds, which it reads once for the file
#   (checker/checkDischargedKeys.ml: chain_gate).
# - ShapeHeads: GM = 1000 globals g1 .. g1000 (x : nat) := x before the
#   section, then Variable n, d0 := n, GK = 250 definitions
#   di := d(i-1) + g1 n + .. + g1000 n, and GL = 12000 lemmas
#   d250 = d250, each proved by eq_refl. The value of each di holds one
#   key, d(i-1) n, and 1000 applications of globals to n, so there is no
#   chain. The chain gate keeps what each value holds, its heads, for the
#   file; a checker that reads the heads that it has kept without counting
#   them against the budget reads all those of the 250 values twice for
#   every lemma, about 500,000 reads. rocqchk counts each head that the
#   gate reads, and gives up on each lemma within the budget
#   (checker/checkDischargedKeys.ml: chain_gate).
# - CastSets, checked with the VM on only: P (x1 .. xv : bool) := True
#   before the section, then Variable n, the chain, SV = 6000 variables
#   x1 .. xv : bool with v = SV, and SL = 24 lemmas
#   k2 = k2 -> bool -> .. -> bool -> P x1 .. xv, with SB = 1000 bools,
#   each proved by fun _ _ .. _ => (I <: P x1 .. xv), with SB + 1 binders:
#   a VM cast under SB + 1 binders whose type mentions every variable of
#   the block. The VM gate moves the set of the Rels that feed the cast
#   past each binder above it, SB + 1 times SV moves for each proof; that
#   work counts against the budget, which runs out
#   (checker/checkDischargedKeys.ml: cast_gate).
#   (A cast whose type mentions SB binders above it instead, as in the
#   review that found this, would make rocq compile slower than rocqchk:
#   it elaborates such binders in a time that grows as their square too.)
#
# Measured (release profile, OCaml 4.14.2, with ROCQCHK_COOK_CROSS_CHECK=1
# as the test suite sets it; both checkers built and run in one pod, the
# mean of two runs): with this change Hyps takes 10.5 s of CPU, OneKey
# 9.9 s, ValueCost 2.6 s, ValueCost12 2.0 s, ShapeHeads 11.7 s and
# CastSets 2.9 s, where rocqchk without the binding (07e45e36) takes 9.6 s,
# 9.6 s, 2.1 s, 1.5 s, 1.9 s and 2.6 s; the earlier versions above reached
# the CPU limit on each file that they missed. Big takes 2.7 s, and 2.6 s
# without the binding.
#
# Each file is checked by rocqchk -j 1 -norec under a CPU limit of
# T = 60 s (ulimit -t), with the harness of misc/rocqchk_cpu_limit.bash;
# Mask and VMDeadBranch are checked again with the VM on
# (-bytecode-compiler yes), and VMLetKey and CastSets with it only. The test
# passes only if rocqchk accepts every file within the limit. For each
# check it prints which case it is (misc/rocqchk_cpu_limit.bash:
# cpu_limit_or_refusal).
set -eu

. misc/rocqchk_cpu_limit.bash

T=60
files=(LetArg PlusArg LemmaType HypType BodyRead IndData
       LetInBlock LetInValue LetInBody LetInIndData Mask
       LetPair StrategyLevel FunValue PolyBody RewriteRules Order FunValueLet
       LetHyp LetStmt LetHypBody VMDeadBranch VMLetKey Big
       Hyps OneKey ValueCost ValueCost12 ShapeHeads CastSets)
# Big's number of trees, their depth, and the number of lemmas
NB=12
D=13
BL=800
# Hyps' and OneKey's number of variables, depth of the trees, and number of
# lemmas; ValueCost's and ValueCost12's depth of the tree and number of
# lemmas; ShapeHeads' number of globals, of definitions, and of lemmas;
# CastSets' number of variables, of binders, and of lemmas
HV=3000
HD=14
HL=16
CD=14
CL=24000
CD12=12
CL12=24000
GM=1000
GK=250
GL=12000
SV=6000
SB=1000
SL=24

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT

heavy() {
  cat <<'EOF'
Definition forty : nat := 40.
Definition rec2 : nat -> bool -> bool :=
  fix r (k : nat) (b : bool) {struct k} : bool :=
    match k with 0 => b | S k => if r k b then r k b else r k b end.
Definition heavy (x : nat) : bool :=
  match rec2 forty true return bool with true => Nat.eqb x 0 | false => true end.
EOF
}

# rec2 forty true written out, with no constant in it.
iheavy() {
  cat <<'EOF'
Notation rec2_forty_true :=
  ((fix r (k : nat) (b : bool) {struct k} : bool :=
      match k with 0 => b | S k => if r k b then r k b else r k b end) 40 true).
EOF
}

# sec: the start of the section of most files, Variable n and the chain
# k0 := n, k2 := k0 + k0, whose value holds k0 n twice. A proof that is to
# be checked with the binding holds let _ : k2 = k2 := eq_refl in.
sec() {
  cat <<'EOF'
Section S.
Variable n : nat.
Definition k0 : nat := n.
Definition k2 : nat := k0 + k0.
EOF
}

# The section of the files that use box.
box() {
  sec; cat <<'EOF'
Definition hc : bool := heavy n.
Inductive box : Type := mk (u : unit) (b := hc).
EOF
}

# The trees of Big, Hyps, OneKey, ValueCost and ValueCost12, outside any
# section: grow x k p is a tree of 2^k leaves leaf x p', with distinct p'.
trees() {
  cat <<'EOF'
Inductive path : Type := top | l (p : path) | r (p : path).
Inductive tree : Type := leaf (x : nat) (p : path) | node (a b : tree).
Fixpoint grow (x : nat) (k : nat) (p : path) : tree :=
  match k with 0 => leaf x p | S k => node (grow x k (l p)) (grow x k (r p)) end.
EOF
}

# gen <file> prints the file.
gen() {
  heavy
  case $1 in
    LetArg) sec; cat <<'EOF'
Let m := n + 0.
Lemma L1 : heavy m = heavy m. Proof. reflexivity. Qed.
Lemma L2 : True.
Proof using All. exact (let _ : k2 = k2 := eq_refl in let H : heavy m = heavy m := L1 in I). Qed.
End S.
EOF
    ;;
    PlusArg) sec; cat <<'EOF'
Lemma L : True.
Proof using All. exact (let _ : k2 = k2 := eq_refl in let _ : heavy (0 + n) = heavy n := eq_refl in I). Qed.
End S.
EOF
    ;;
    LemmaType) sec; cat <<'EOF'
Definition hc : bool := heavy n.
Lemma L1 : hc = hc. Proof. reflexivity. Qed.
Lemma L2 : hc = hc. Proof. exact (let _ : k2 = k2 := eq_refl in L1). Qed.
End S.
EOF
    ;;
    HypType) sec; cat <<'EOF'
Definition hc : bool := heavy n.
Hypothesis H : hc = true.
Lemma L : hc = true. Proof. exact (let _ : k2 = k2 := eq_refl in H). Qed.
End S.
EOF
    ;;
    BodyRead) sec; cat <<'EOF'
Definition hc : bool := heavy n.
Definition g (b : bool) : option bool := Some hc.
Lemma L : g true = Some hc.
Proof. exact (let _ : k2 = k2 := eq_refl in @eq_refl (option bool) (g true)). Qed.
End S.
EOF
    ;;
    IndData) sec; cat <<'EOF'
Definition hc : bool := heavy n.
Inductive I : bool -> Type := C : I hc.
Lemma L : I hc. Proof. exact (let _ : k2 = k2 := eq_refl in C). Qed.
End S.
EOF
    ;;
    LetInBlock) box; cat <<'EOF'
Hypothesis H : match mk tt return bool with mk _ b => b end = true.
Lemma L : hc = true. Proof. exact (let _ : k2 = k2 := eq_refl in H). Qed.
End S.
EOF
    ;;
    LetInValue) box; cat <<'EOF'
Definition hv : option bool := Some (match mk tt return bool with mk _ b => b end).
Lemma L : hv = Some hc. Proof. exact (let _ : k2 = k2 := eq_refl in @eq_refl (option bool) hv). Qed.
End S.
EOF
    ;;
    LetInBody) box; cat <<'EOF'
Definition g (u : unit) : option bool := Some (match mk u return bool with mk _ b => b end).
Lemma L : g tt = Some hc.
Proof. exact (let _ : k2 = k2 := eq_refl in @eq_refl (option bool) (g tt)). Qed.
End S.
EOF
    ;;
    LetInIndData) box; cat <<'EOF'
Inductive I : bool -> Type := C : I (match mk tt return bool with mk _ b => b end).
Lemma L : I hc. Proof. exact (let _ : k2 = k2 := eq_refl in C). Qed.
End S.
EOF
    ;;
    Mask) sec; cat <<'EOF'
Definition c : bool -> nat := let k := n in fun (m : bool) => k.
Lemma L : c true = n.
Proof.
  assert (H : c true = n).
  { change_no_check (c (heavy n) = n). exact (@eq_refl nat (c (heavy n))). }
  exact (let _ : k2 = k2 := eq_refl in H).
Qed.
End S.
EOF
    ;;
    LetPair) iheavy; sec; cat <<'EOF'
Let l1 : bool := true.
Let l2 : bool := true.
Definition c (m : bool) : bool :=
  match rec2_forty_true return bool with true => andb m (Nat.eqb n 0) | false => m end.
Lemma L : True.
Proof using All.
  assert (H : c l1 = c l2).
  { change_no_check (c l1 = c l1). exact (@eq_refl bool (c l1)). }
  exact (let _ : k2 = k2 := eq_refl in I).
Qed.
End S.
EOF
    ;;
    StrategyLevel) iheavy; echo 'Definition G (b : bool) : bool := b.'; sec; cat <<'EOF'
Definition c : bool :=
  match rec2_forty_true return bool with true => Nat.eqb n 0 | false => true end.
Strategy 1000 [c].
Lemma L : G c = c.
Proof. change_no_check (G c = G c). exact (let _ : k2 = k2 := eq_refl in @eq_refl bool (G c)). Qed.
End S.
EOF
    ;;
    FunValue) iheavy; echo 'Definition G2 (h : bool -> bool) (x : bool) : bool := h x.'; sec; cat <<'EOF'
Definition f (x : bool) : bool :=
  match rec2_forty_true return bool with true => andb x (Nat.eqb n 0) | false => x end.
Lemma L : f true = G2 f true.
Proof. change_no_check (f true = f true). exact (let _ : k2 = k2 := eq_refl in @eq_refl bool (f true)). Qed.
End S.
EOF
    ;;
    PolyBody) iheavy; echo 'Set Universe Polymorphism.'; sec; cat <<'EOF'
Definition d : bool :=
  match rec2_forty_true return bool with true => Nat.eqb n 0 | false => true end.
Definition c@{k} (T : Type@{k}) : bool := d.
Lemma L : d = c@{Set} nat.
Proof. change_no_check (d = d). exact (let _ : k2 = k2 := eq_refl in @eq_refl bool d). Qed.
End S.
EOF
    ;;
    RewriteRules | Order) iheavy; echo 'Definition G (b : bool) : bool := b.'; sec; cat <<'EOF'
Definition c : bool :=
  match rec2_forty_true return bool with true => Nat.eqb n 0 | false => true end.
Lemma L : c = G c.
Proof. change_no_check (c = c). exact (let _ : k2 = k2 := eq_refl in @eq_refl bool c). Qed.
End S.
EOF
    ;;
    FunValueLet) iheavy; echo 'Definition G2 (h : bool -> bool) (x : bool) : bool := h x.'; sec; cat <<'EOF'
Definition f : bool -> bool :=
  let k := n in
  fun (x : bool) =>
    match rec2_forty_true return bool with true => andb x (Nat.eqb k 0) | false => x end.
Lemma L : f true = G2 f true.
Proof. change_no_check (f true = f true). exact (let _ : k2 = k2 := eq_refl in @eq_refl bool (f true)). Qed.
End S.
EOF
    ;;
    LetHyp | LetStmt | LetHypBody)
      local hyp='Hypothesis H : m = true.' stmt='c = c' proof='eq_refl'
      case $1 in
        LetStmt) hyp='' stmt='m = m /\ c = c' proof='conj eq_refl eq_refl' ;;
        LetHypBody) proof='let _ : m = true := H in eq_refl' ;;
      esac
      iheavy; sec; cat <<EOF
Let m : bool := rec2_forty_true.
$hyp
Definition c : nat := n.
Lemma L : $stmt. Proof using All. exact (let _ : k2 = k2 := eq_refl in $proof). Qed.
End S.
EOF
    ;;
    VMDeadBranch) echo 'Fixpoint spin (k : nat) : nat := match k with 0 => 0 | S k => spin k + spin k end.'
      sec; cat <<'EOF'
Definition big : nat := spin 36 + n.
Lemma L : (if true then 0 else big) = 0.
Proof. exact (let _ : k2 = k2 := eq_refl in (@eq_refl nat 0 <: (if true then 0 else big) = 0)). Qed.
End S.
EOF
    ;;
    VMLetKey) iheavy; sec; cat <<'EOF'
Definition b0 : bool := orb true (Nat.eqb n n).
Lemma L : True.
Proof using All.
  pose (y := b0). pose (y' := b0).
  exact (let _ : k2 = k2 := eq_refl in
         let _ := (@eq_refl bool (if y then true else rec2_forty_true)
          <: (if y then true else rec2_forty_true) = (if y' then true else rec2_forty_true)) in I).
Qed.
End S.
EOF
    ;;
    Big)
      local i seed=top tuple=
      trees
      printf 'Section S.\nVariable n : nat.\n'
      for i in $(seq 1 "$NB"); do
        seed="r ($seed)"
        echo "Definition big$i : tree := Eval cbv in grow n $D ($seed)."
        tuple="${tuple:+$tuple, }big$i"
      done
      for i in $(seq 1 "$BL"); do
        echo "Lemma L$i : ($tuple) = ($tuple). Proof. exact eq_refl. Qed."
      done
      echo "End S."
    ;;
    Hyps | OneKey)
      local i x=d
      if [ "$1" = OneKey ]; then x=c; fi
      trees
      echo 'Section S.'
      echo "Variables $(seq -f 'x%g' 1 "$HV" | tr '\n' ' '): nat."
      echo 'Definition c : nat := x1.'
      echo 'Definition d : nat := c + c.'
      for i in $(seq 1 "$HL"); do
        echo "Lemma L$i : exists t : tree, True."
        echo "Proof using All."
        echo "  let t := eval cbv delta [grow] beta iota zeta in (grow $x $HD top) in"
        echo "  exact (ex_intro (fun _ : tree => True) t I)."
        echo "Qed."
      done
      echo 'End S.'
    ;;
    ValueCost | ValueCost12)
      local i depth=$CD count=$CL
      if [ "$1" = ValueCost12 ]; then depth=$CD12 count=$CL12; fi
      trees
      printf 'Section S.\nVariable n : nat.\n'
      echo "Definition big : tree := Eval cbv in grow n $depth top."
      for i in $(seq 1 "$count"); do echo "Lemma L$i : big = big. Proof. exact eq_refl. Qed."; done
      echo 'End S.'
    ;;
    ShapeHeads)
      local i sum
      sum=$(seq -f ' + g%g n' 1 "$GM" | tr -d '\n')
      for i in $(seq 1 "$GM"); do echo "Definition g$i (x : nat) : nat := x."; done
      printf 'Section S.\nVariable n : nat.\nDefinition d0 : nat := n.\n'
      for i in $(seq 1 "$GK"); do echo "Definition d$i : nat := d$((i - 1))$sum."; done
      for i in $(seq 1 "$GL"); do echo "Lemma L$i : d$GK = d$GK. Proof. exact eq_refl. Qed."; done
      echo 'End S.'
    ;;
    CastSets)
      local i xs arr un
      xs=$(seq -f 'x%g' 1 "$SV" | tr '\n' ' ')
      arr=$(printf 'bool -> %.0s' $(seq 1 "$SB"))
      un=$(printf '_ %.0s' $(seq 1 "$SB"))
      echo "Definition P ($xs: bool) : Prop := True."
      sec
      echo "Variables $xs: bool."
      echo "Notation A := ($arr P $xs)."
      echo "Notation F := (fun $un=> (I <: P $xs))."
      for i in $(seq 1 "$SL"); do echo "Lemma L$i : k2 = k2 -> A. Proof. exact (fun _ => F). Qed."; done
      echo 'End S.'
    ;;
  esac
}

# rocq compile runs under the same CPU limit, so that a file that it cannot
# compile within it fails the test instead of stopping it.
for f in "${files[@]}"; do
  gen "$f" > "$d/$f.v"
  opts=(-native-compiler no)
  case $f in
    RewriteRules) opts+=(-allow-rewrite-rules) ;;
    VMDeadBranch) opts+=(-bytecode-compiler no) ;;
  esac
  if ! ( ulimit -c 0; ulimit -t "$T"
         exec "$BIN"rocq c "${opts[@]}" -R "$d" T "$d/$f.v" > "$d/$f.compile.log" 2>&1 ); then
    echo "FAILURE: compile failed: $f:"
    cat "$d/$f.compile.log"
    exit 1
  fi
done

# check <file> [<rocqchk option>...]: rocqchk -j 1 checks T.<file> under the
# CPU limit, with the options given; the nth check writes its output to
# $d/<file>.<n>.log. Prints the case, and fails unless rocqchk accepted the
# file.
n=0
check() {
  local f=$1
  shift
  n=$((n + 1))
  local name="T.$f${1:+ ($*)}" log="$d/$f.$n.log"
  timed_rocqchk "$log" "$d/$f.$n.time" -- -silent -j 1 "$@" -R "$d" T -norec "T.$f" || return 1
  if [ "$rc" = 0 ]; then
    echo "rocqchk -j 1 accepted $name in $cpu s of CPU."
    return 0
  fi
  cpu_limit_or_refusal "$name" "$log"
  return 1
}

status=0
for f in "${files[@]}"; do
  case $f in
    VMLetKey | CastSets) ;;
    *) if ! check "$f"; then status=1; fi ;;
  esac
done
if ! check Mask -bytecode-compiler yes; then status=1; fi
if ! check VMDeadBranch -bytecode-compiler yes; then status=1; fi
if ! check VMLetKey -bytecode-compiler yes; then status=1; fi
if ! check CastSets -bytecode-compiler yes; then status=1; fi
exit $status
