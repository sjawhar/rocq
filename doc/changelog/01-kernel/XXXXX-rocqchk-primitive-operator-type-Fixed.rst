- **Fixed:**
  ``rocqchk`` refuses a crafted ``.vo`` in which a constant whose body is
  a primitive operator has a type other than the operator's. Conversion
  and the VM compute with the operator whatever its declared type, so
  ``add : int -> int -> False`` with the body of ``#int63_add`` gave a
  closed proof of ``False``; files written by coqc pass, since coqc gives
  such a constant the operator's type. ``rocqchk -o`` still lists a
  primitive operator among the axioms
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
