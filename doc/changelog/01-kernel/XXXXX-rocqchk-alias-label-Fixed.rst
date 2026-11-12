- **Fixed:**
  ``rocqchk`` refuses a crafted ``.vo`` in which a delta resolver records a
  constant or an inductive type as an alias of one with another label. A
  functor application rebuilds the target of an alias from the target's
  module and the alias's own label, so such an alias, even one whose body
  converts with its target, could make a field of the functor's body stand
  for a field of the argument that the functor never named, and give a
  closed proof of ``False``; files written by coqc pass, since coqc records
  an alias only between names with the same label
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
