- **Fixed:**
  ``rocqchk -o`` reads the axioms of a functor application in the
  functor's body, and lists them under the application's name, ``R.x``
  for ``Module R := F A``, whether or not a proof uses them. It listed
  only the constants without a body that the final environment holds, so
  an axiom of a functor's body that the application's type does not
  declare was not listed. Where that walk stops, at an application read
  inside 64 nested applications, after 100000 applications, or at a cycle
  or another shape that only a crafted ``.vo`` holds, ``rocqchk -o``
  prints no summary and ends with an error that names the application or
  module where the walk stopped and says why. With ``F0`` declaring
  ``Axiom hidden : False``, each of ``F1`` to ``F64`` applying the one
  before it, every result type empty, and ``Module R := F64 A``, no axiom
  was listed; ``rocqchk -o`` now ends with that error, and lists
  ``R.N.N...N.hidden`` for the same chain one shorter
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
