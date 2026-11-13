- **Fixed:**
  ``rocqchk`` accepted closed proofs of ``False`` from crafted ``.vo`` files
  whose delta resolvers record aliases that ``rocq compile`` never writes:
  an alias between declared-only fields of module types, an alias that a
  module records for a field of one of its submodules and the submodule
  does not, and an alias whose label differs from its target's; and from
  crafted ``.vo`` files that register as a primitive type a constant that
  :cmd:`Primitive` does not declare there, or give a primitive operator a
  type other than the operator's
  (`#PRNUM <https://github.com/rocq-prover/rocq/pull/PRNUM>`_,
  fixes `#12439 <https://github.com/rocq-prover/rocq/issues/12439>`_,
  by Sami Jawhar).
