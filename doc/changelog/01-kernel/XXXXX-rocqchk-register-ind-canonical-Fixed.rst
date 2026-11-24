- **Fixed:**
  ``rocqchk`` refuses a crafted ``.vo`` whose stored registration of a
  primitive inductive type gives the inductive type that the library
  declares another canonical name, in any of its entries. It checked the
  registration only against the inductive type of the same user name, and
  then put it in force for later libraries with the stored canonical name,
  which conversion compares: ``B`` registered as the primitive ``bool``
  under the canonical name of another inductive type ``U`` let a later
  primitive operator return ``U`` and give a closed proof of ``False`` with
  no axiom but the primitive declarations. It also refuses a registration
  of an inductive type that only the body of a functor declares, which
  coqc never writes. Files written by coqc pass, including an identical
  registration stored twice, a registration through a module alias or an
  ``Include``, and one made inside a module sealed by a module type
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
