- **Fixed:**
  ``rocqchk -o`` reads the axioms of a functor application in the
  functor's body, and lists them under the application's name, ``R.x``
  for ``Module R := F A``, whether or not a proof uses them. It listed
  only the constants without a body that the final environment holds, so
  an axiom of a functor's body that the application's type does not
  declare was not listed. The walk stops at an application read inside
  64 nested applications, and where it would take more than 100000
  steps: each functor it resolves costs one step, and one more for each
  name in its path after the library or functor parameter it starts from
  (``Lib.F`` costs two steps, ``Lib.M.F`` three). A library can reach
  these two bounds, and every other stop needs a crafted ``.vo``, such as
  one that holds an alias cycle. Where the walk stops, ``rocqchk -o``
  prints no summary and ends with an error that names the application or
  module where it stopped and says why. With ``F0`` declaring
  ``Axiom hidden : False``, each of ``F1`` to ``F64`` applying the one
  before it, every result type empty, and ``Module R := F64 A``, no axiom
  was listed; ``rocqchk -o`` now ends with that error, and lists
  ``R.N.N...N.hidden`` for the same chain one shorter
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
