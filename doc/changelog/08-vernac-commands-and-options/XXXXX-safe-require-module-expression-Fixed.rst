- **Fixed:**
  a module expression over a module or a module type of a library loaded
  with :cmd:`Require` :n:`(safe)`, such as ``Module Type A := M.N.T``, an
  ``Include``, a sealed module or a functor parameter, failed with an
  anomaly. It is now refused with an error that names the path. Such a
  library replays none of its objects, and the module expression would
  need them. A functor applied to a module of such a library and a
  subtyping check against one of its module types still work, and
  :cmd:`Print Module` of one of its functors now works
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
