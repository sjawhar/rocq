- **Fixed:**
  A :attr:`warn` attribute no longer causes an anomaly when its ``cats``
  names ``default`` or ``none``, when its warning name is already taken
  (by the warning of another list, as ``a,b`` for ``a b``, or by a
  category), or when it names a category or a warning that a later
  deprecation makes (``deprecated-since-X``,
  ``deprecated-reference-since-X``). coqc accepted such an attribute,
  but then every :cmd:`Require` or :cmd:`Require` :n:`(safe)` of a
  library holding it, a use of a definition holding it, or a later use of
  an object deprecated since ``X``, failed with an anomaly. The warning
  is now given
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
