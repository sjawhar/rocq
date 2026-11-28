#!/usr/bin/env bash
# rocq-prover/rocq#21113, through rocqchk. Include copies the fields of a
# module. A copied private inductive was entered open to matching, so a match
# on the copy, written after the Include, reached the original inductive, and
# with an axiom that only holds while the inductive is private it proves
# False. rocqchk accepted such a library.
#
# The compiler now refuses that match, so each library below is forged: it is
# compiled honestly with a non-private inductive I, and forge.ml then makes I
# private and open to matching (mind_private Some false) in every structure
# of the .vo, as a compiler without the fix writes it, and may change one
# constant of one module.
#
# The copy of I is entered locked. A copy of a function that matches on I in
# I's own module is typed with the copies of that module's inductives opened
# again, when it is the same declaration as the constant it copies
# (checker/mod_checking.ml, typing_env); every constant is typed in full. The
# cases check that a forged file cannot use that opening: each copy that is
# not the same declaration, or whose constant is gone, is typed with the
# copies locked, and refused; a same declaration that typing refuses is
# refused; and the opening does not outlast the copy's check.
#
# case       library  edit                   rocqchk must
# ctl        Ctl.v    none                   accept: the match is in I's module
# native     Lib.v    none                   refuse: N matches on its copy of I
# stay       Stay.v   none                   refuse: N matches on its copy of I right
#                                            after a copy whose check opened it
# body       Ctl.v    swap N f               refuse: N.f has another body than M.f
# type       Ctl.v    type N f M h           refuse: N.f has another type than M.f
# gone       Ctl.v    rename M f f0          refuse: N.f copies a constant that is not there
# guard      Ctl.v    noguard N f            refuse: N.f has other typing flags
# relev      Ctl.v    irrelevant N f         refuse: N.f has another relevance
# univs      Univ.v   univs N f M p          refuse: N.f has other universes
# univs2     Univ.v   univs N fp M p         refuse: N.fp has other polymorphic universes
# opaque     Opq.v    body N p1 M p2         refuse: N.p1 has M.p2's opaque proof, of type bool
# opqcopy    OpqC.v   body N l M l           refuse: N.l, a copy whose body is M.l's opaque
#                                            proof, which matches on I, is typed (opaque
#                                            bodies are never opened) and the match refused
# annot      Ctl.v    annot N f              refuse: N.f's binder is marked irrelevant
# kerpair    KP.v     kerpair N f N useg     refuse: N.f names N.g as the copy of Q.h
# bound      Bound.v  none                   accept: F includes its parameter X : T, and the
#                                            match is in T, which rocqchk checks before X
# boundbody  Bound.v  swap F f               refuse: F.f has another body than X.f
set -u
export PATH="$BIN:$PATH"

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT

cat > "$d/Ctl.v" <<'V'
Module M.
Inductive I := a | b.
Definition f (x : I) : bool := match x with a => true | b => false end.
Definition h (x : I) : I := x.
End M.
Module N.
Include M.
Definition g := f a.
End N.
V

cat > "$d/Lib.v" <<'V'
Module M.
Inductive I := a | b.
End M.
Module N.
Include M.
Definition to_bool (x : I) : bool := match x with a => true | b => false end.
End N.
V

cat > "$d/Univ.v" <<'V'
Module M.
Inductive I := a | b.
Definition f (x : I) : bool := match x with a => true | b => false end.
#[universes(polymorphic)] Definition fp@{u v} (x : I) : bool := match x with a => true | b => false end.
#[universes(polymorphic)] Definition p@{u} : Type@{u+1} := Type@{u}.
End M.
Module N.
Include M.
End N.
V

cat > "$d/Stay.v" <<'V'
Module M.
Inductive I := a | b.
Definition f (x : I) : bool := match x with a => true | b => false end.
End M.
Module N.
Include M.
Definition to_bool (x : I) : bool := match x with a => false | b => true end.
End N.
V

cat > "$d/KP.v" <<'V'
Module Q.
Inductive I := a | b.
Definition h (x : I) := true.
Definition g (x : I) := false.
Definition f (x : I) := h x.
End Q.
Module N.
Include Q.
Definition useg := g.
End N.
V

cat > "$d/Opq.v" <<'V'
Module M.
Inductive I := a | b.
Lemma p1 : nat. Proof. exact 0. Qed.
Lemma p2 : bool. Proof. exact true. Qed.
End M.
Module N.
Include M.
End N.
V

cat > "$d/OpqC.v" <<'V'
Module M.
Inductive I := a | b.
Definition l (x : I) : bool.
Proof. exact (match x with a => true | b => false end). Qed.
End M.
Module N.
Include M.
End N.
V

cat > "$d/Bound.v" <<'V'
Module Type T.
Inductive I := a | b.
Definition f (x : I) : bool := match x with a => true | b => false end.
End T.
Module F (X : T).
Include X.
End F.
V

for m in Ctl Lib Stay Univ Opq OpqC KP Bound; do
  rocq c -R "$d" PI "$d/$m.v" || { echo "rocq c refused the honest $m.v"; exit 1; }
  if ! rocqchk -o -bytecode-compiler yes -R "$d" PI -norec "PI.$m" > "$d/$m.honest.log" 2>&1; then
    echo "rocqchk refused the honest $m.vo"
    cat "$d/$m.honest.log"
    exit 1
  fi
done

failed=0
# check <case> <library> <accept|regex> [edit...]
check() {
  local c=$1 m=$2 want=$3
  shift 3
  mkdir "$d/$c"
  if ! ocaml misc/rocqchk-private-include/forge.ml "$d/$m.vo" "$d/$c/$m.vo" I "$@" > "$d/$c/forge.log" 2>&1; then
    echo "case $c: the forge failed"; cat "$d/$c/forge.log"; failed=1; return
  fi
  if rocqchk -o -bytecode-compiler yes -R "$d/$c" PI -norec "PI.$m" > "$d/$c/out.log" 2>&1; then
    if [ "$want" != accept ]; then
      echo "case $c: rocqchk accepted the forged $m.vo ($*)"; cat "$d/$c/out.log"; failed=1
    else
      echo "case $c: accepted"
    fi
  elif [ "$want" = accept ]; then
    echo "case $c: rocqchk refused the forged $m.vo, which matches only in I's module"; cat "$d/$c/out.log"; failed=1
  elif ! grep -Eq "$want" "$d/$c/out.log"; then
    echo "case $c: rocqchk refused the forged $m.vo with another error than /$want/"; cat "$d/$c/out.log"; failed=1
  else
    echo "case $c: refused: $(grep -E -m1 "$want" "$d/$c/out.log")"
  fi
}

private="CaseOnPrivateInd"
check ctl Ctl accept
check native Lib "$private"
check stay Stay "$private"
check body Ctl "$private" swap N f
check type Ctl "$private" type N f M h
check gone Ctl "$private" rename M f f0
check guard Ctl "$private" noguard N f
check relev Ctl "const_relevance" irrelevant N f
check univs Univ "$private" univs N f M p
check univs2 Univ "$private" univs N fp M p
check opaque Opq "ActualType" body N p1 M p2
check opqcopy OpqC "$private" body N l M l
check annot Ctl "BadBinderRelevance" annot N f
check kerpair KP "IllFormedConstant" kerpair N f N useg
check bound Bound accept
check boundbody Bound "$private" swap F f
exit "$failed"
