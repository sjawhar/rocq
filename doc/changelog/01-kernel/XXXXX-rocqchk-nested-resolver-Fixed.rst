- **Fixed:**
  ``rocqchk`` refuses a crafted ``.vo`` in which the delta resolver of a
  module records, for a field of a nested module, a canonical name that the
  nested module's own resolver does not give, unless that name passes the
  alias check every other alias gets. A functor application or a module alias
  substitutes through the whole resolver of the module it names, so such an
  entry could make two unrelated declarations convertible and give a closed
  proof of ``False``; files written by coqc pass
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
