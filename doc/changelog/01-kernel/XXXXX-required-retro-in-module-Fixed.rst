- **Fixed:**
  after the end of a module, a module type or a functor that requires a
  library registering a primitive type (such as
  ``Corelib.Numbers.Cyclic.Int63.PrimInt63``), the environment keeps that
  library's registrations, so a primitive literal that needs them is accepted
  again; since the registrations of a library are stored with the library
  and not with its module body, they were dropped at the end of the module
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
