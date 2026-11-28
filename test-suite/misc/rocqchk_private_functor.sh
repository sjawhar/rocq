#!/usr/bin/env bash
# rocq-prover/rocq#21113, the functor form, through rocqchk. Lib.v gives a
# module Q to a functor whose parameter declares Q's inductive non-private.
# It is compiled honestly with Q.foo non-private;
# misc/rocqchk-private-functor/forge.ml then makes Q.foo alone private and
# open to matching, as a compiler without check_private writes it. rocqchk
# must accept the honest file and refuse the forged one with a module typing
# error (check_private, PrivateStatusExpected).
set -eu
export PATH="$BIN:$PATH"

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT

cat > "$d/Lib.v" <<'V'
Module Type T.
Unset Elimination Schemes.
Inductive foo := Foo | Bar.
End T.
Module Q.
Unset Elimination Schemes.
Inductive foo := Foo | Bar.
End Q.
Module F (X : T).
Include X.
Definition to_bool (b : foo) := match b with Foo => true | Bar => false end.
End F.
Module B := F Q.
V

rocq c -R "$d" PF "$d/Lib.v"
if ! rocqchk -o -bytecode-compiler yes -R "$d" PF -norec PF.Lib > "$d/honest.log" 2>&1; then
  echo "rocqchk refused the honest Lib.vo"; cat "$d/honest.log"; exit 1
fi
mv "$d/Lib.vo" "$d/Lib.honest.vo"
ocaml misc/rocqchk-private-functor/forge.ml "$d/Lib.honest.vo" "$d/Lib.vo" Q foo
if rocqchk -o -bytecode-compiler yes -R "$d" PF -norec PF.Lib > "$d/forged.log" 2>&1; then
  echo "rocqchk accepted a private inductive for a non-private parameter"; cat "$d/forged.log"; exit 1
fi
if ! grep -Eq "Module typing error|ModuleTypingError" "$d/forged.log"; then
  echo "rocqchk refused the forged Lib.vo with another error"; cat "$d/forged.log"; exit 1
fi
echo "refused: $(grep -m1 -E "Module typing error|ModuleTypingError" "$d/forged.log")"
