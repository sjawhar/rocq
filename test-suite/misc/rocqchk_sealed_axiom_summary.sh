#!/usr/bin/env bash
# The Axioms section of rocqchk -o must name an axiom that lives only inside an
# opaquely sealed implementation, whether the proof reaches it through an
# opaque or a transparent helper, under a full recursive check as well as under
# -norec. The library is output-coqchk/sealed_axiom_summary.v. That file's
# own test covers -norec alone, because the output-coqchk harness always
# passes it.
#
# The second half pins the NAME. An axiom declared in a functor is reported
# after the applied module (App.in_f), which is also what Print Assumptions
# prints for it; the functor's own name (F.in_f) must not appear. A reader that
# joins the two accounts by name, as the BET grader does, fails closed on any
# name that only one of them prints. An application inside a seal is read
# through its functor's body, so both accounts name its axiom Seal.Inner.in_f,
# and that is checked here too.
set -eu
export PATH="$BIN:$PATH"

. misc/rocqchk_summary_common.bash

src=output-coqchk/sealed_axiom_summary.v
lib=sealed_axiom_summary

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
cp "$src" "$d/"

echo "Require $lib. Definition use : 1 = 2 := $lib.OpaqueHelper.tgt." > "$d/Use.v"
rocq c -native-compiler no -R "$d" "" "$d/$lib.v"
rocq c -native-compiler no -R "$d" "" "$d/Use.v"

# Recursive check: the library is checked as a dependency of Use.
rocqchk -o -silent -R "$d" "" Use > "$d/rec.log" 2>&1
section 'Axioms' "$d/rec.log" | grep -qx "    $lib.OpaqueHelper.ax"
section 'Axioms' "$d/rec.log" | grep -qx "    $lib.TransparentHelper.ax"

# -norec on the sealing library itself.
rocqchk -o -silent -R "$d" "" -norec "$lib" > "$d/norec.log" 2>&1
section 'Axioms' "$d/norec.log" | grep -qx "    $lib.OpaqueHelper.ax"
section 'Axioms' "$d/norec.log" | grep -qx "    $lib.TransparentHelper.ax"

cat > "$d/Fun.v" <<'EOF'
Module Type S. Parameter n : nat. End S.
Module Arg. Definition n := 0. End Arg.
Module F (X : S).
  Axiom in_f : False.
  Definition use : False := in_f.
End F.
Module App := F Arg.
Definition reached : False := App.use.
Module Type T. Parameter tgt : 1 = 2. End T.
Module Seal : T.
  Module Inner := F Arg.
  Lemma tgt : 1 = 2. Proof. destruct Inner.use. Qed.
End Seal.
EOF
echo 'Require Fun. Print Assumptions Fun.reached. Print Assumptions Fun.Seal.tgt.' > "$d/Pa.v"
rocq c -native-compiler no -R "$d" "" "$d/Fun.v"
rocq c -native-compiler no -R "$d" "" "$d/Pa.v" > "$d/pa.log" 2>&1
grep -q 'Fun.App.in_f : False' "$d/pa.log"
grep -q 'Fun.Seal.Inner.in_f : False' "$d/pa.log"
if grep -q 'Fun.F.in_f' "$d/pa.log"; then
  echo "Print Assumptions named the functor, not the application"; exit 1
fi

rocqchk -o -silent -R "$d" "" Fun > "$d/fun.log" 2>&1
section 'Axioms' "$d/fun.log" | grep -qx '    Fun.App.in_f'
if section 'Axioms' "$d/fun.log" | grep -q 'Fun.F.in_f'; then
  echo "the summary named the functor, which Print Assumptions never prints"; exit 1
fi
# The application inside the seal: named as Print Assumptions named it above,
# and under no other name.
section 'Axioms' "$d/fun.log" | grep -qx '    Fun.Seal.Inner.in_f'
if section 'Axioms' "$d/fun.log" | grep 'Fun.Seal' | grep -qvx '    Fun.Seal.Inner.in_f'; then
  echo "the summary named something under Seal that Print Assumptions does not"; exit 1
fi
