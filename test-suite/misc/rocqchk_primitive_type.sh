#!/usr/bin/env bash

# rocqchk must refuse a constant whose body is a primitive operator and
# whose type is not the operator's. Conversion and the VM compute with the
# operator whatever its declared type, so a forged .vo that holds
# [Primitive bogus : False := #int63_head0.] and
# [Definition oops : False := bogus.] holds a closed proof of False. coqc
# refuses to write those declarations: forge.ml retypes the compiled
# constants of the honest Bogus.v, bogus alone (mode primitive) or bogus
# and oops (mode both). rocqchk must accept Bogus.vo itself, and -o must
# list bogus among the axioms, with int, a primitive type, which has no
# body: what a primitive operator computes is the kernel's code.
set -eu

. misc/rocqchk_forge_common.bash

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

cat > "$d/expected" <<'EOF'
PrimitiveType.Bogus.bogus
PrimitiveType.Bogus.int
EOF

for vm in yes no; do
  must_accept "$d/honest-$vm.log" "rocqchk -bytecode-compiler $vm refused the honest Bogus.vo" \
    -silent -o -bytecode-compiler $vm -Q "$d/honest" PrimitiveType -norec PrimitiveType.Bogus
  sed -n '/^\* Axioms:/,/^\* Constants/ s/^    //p' "$d/honest-$vm.log" |
    LC_ALL=C sort > "$d/axioms-$vm"
  if ! diff -u "$d/expected" "$d/axioms-$vm"; then
    echo "rocqchk -o -bytecode-compiler $vm does not list the primitive bogus among the axioms"
    cat "$d/honest-$vm.log"
    exit 1
  fi
  for mode in primitive both; do
    must_refuse "$d/$mode-$vm.log" "is the primitive operator head0, but its type is not the operator's" \
      "rocqchk -bytecode-compiler $vm accepted bogus : False := #int63_head0 (mode $mode)" \
      "unexpected rocqchk -bytecode-compiler $vm failure for bogus : False := #int63_head0 (mode $mode)" \
      -silent -o -bytecode-compiler $vm -Q "$d/$mode" PrimitiveType -norec PrimitiveType.Bogus
  done
done
