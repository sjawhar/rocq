- **Fixed:**
  ``rocqchk`` accepted closed proofs of ``False`` from crafted ``.vo`` files
  whose delta resolvers record aliases that ``rocq compile`` never writes:
  an alias between declared-only fields of module types, an alias that a
  module records for a field of one of its submodules and the submodule
  does not, and an alias whose label differs from its target's
  (`#PRNUM <https://github.com/rocq-prover/rocq/pull/PRNUM>`_,
  by Sami Jawhar).
