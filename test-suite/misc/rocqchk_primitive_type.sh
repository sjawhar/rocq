#!/usr/bin/env bash

# rocqchk does not check a primitive's declared type against the type of its
# operator, so a forged .vo can hold [Primitive bogus : False :=
# #int63_head0.] and [Definition oops : False := bogus.], a closed proof of
# False, and rocqchk accepts it. coqc refuses to write those declarations:
# forge.ml retypes the compiled constants of the honest Bogus.v. What rocqchk
# must do is list bogus among the axioms of -o, as it did before rocq#22623
# was ported; the port listed only int, a primitive type, which has no body.
set -eu

D=misc/rocqchk-primitive-type
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
mkdir "$d/honest" "$d/primitive" "$d/both"
cp "$D/Bogus.v" "$d/honest/"

$coqc -noinit -Q "$d/honest" PrimitiveType "$d/honest/Bogus.v"

for mode in primitive both; do
  cp "$d/honest/Bogus.vo" "$d/$mode/"
  ocaml "$D/forge.ml" "$d/$mode/Bogus.vo" "$mode"
done

# With bogus retyped alone, oops : int -> int := bogus is ill-typed: rocqchk
# refusing it shows that it reads the forged type.
if "$BIN"rocqchk -silent -Q "$d/primitive" PrimitiveType \
     -norec PrimitiveType.Bogus > "$d/primitive.log" 2>&1; then
  echo "rocqchk accepted oops : int -> int := bogus with bogus : False"
  cat "$d/primitive.log"
  exit 1
fi
if ! grep -q "Type error: ActualType" "$d/primitive.log"; then
  echo "unexpected rocqchk failure with bogus retyped alone"
  cat "$d/primitive.log"
  exit 1
fi

cat > "$d/expected" <<'EOF'
PrimitiveType.Bogus.bogus
PrimitiveType.Bogus.int
EOF

for vm in yes no; do
  if ! "$BIN"rocqchk -silent -o -bytecode-compiler $vm -Q "$d/both" PrimitiveType \
       -norec PrimitiveType.Bogus > "$d/both-$vm.log" 2>&1; then
    echo "rocqchk -bytecode-compiler $vm refused the forged Bogus.vo"
    cat "$d/both-$vm.log"
    exit 1
  fi
  sed -n '/^\* Axioms:/,/^\* Constants/ s/^    //p' "$d/both-$vm.log" |
    LC_ALL=C sort > "$d/axioms-$vm"
  if ! diff -u "$d/expected" "$d/axioms-$vm"; then
    echo "rocqchk -o -bytecode-compiler $vm does not list the primitive bogus among the axioms"
    cat "$d/both-$vm.log"
    exit 1
  fi
done
