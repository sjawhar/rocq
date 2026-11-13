- **Fixed:**
  ``rocqchk`` refuses a crafted ``.vo`` in which a structure gives one
  label to two constants, rewrite rule blocks or inductive names, or to two
  modules or module types. The environment kept the last field with the
  label, so ``Axiom ax : False``, then ``proof : False := ax``, then a
  second ``ax : unit := tt`` left no constant without a body and gave a
  closed proof of ``False``. Files written by coqc pass, since coqc gives a
  label to one field of a structure at most in each of these two
  namespaces
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
