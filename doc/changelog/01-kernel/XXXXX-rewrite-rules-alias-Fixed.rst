- **Fixed:**
  Module subtyping accepts a rewrite-rule block of a signature when the
  implementation has the same block, and still refuses any other. rocqchk
  checks a module alias by subtyping, so it stopped with an uncaught
  ``Modops.ModuleTypingError`` on every alias of a module that declares a
  rewrite rule, although coqc accepts the alias
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
