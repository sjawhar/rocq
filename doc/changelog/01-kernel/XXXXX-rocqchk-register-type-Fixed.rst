- **Fixed:**
  ``rocqchk`` refuses a crafted ``.vo`` that registers as a primitive type
  a constant that is not a parameter of the primitive type's type, as it
  is declared in the body of its module: the type of a sealed module or of
  a functor application no longer stands for it. The typing of a primitive
  literal uses the registered constant, so a definition such as
  ``int : Set := Empty_set`` registered as the int63 type, in a library or
  behind a module type, gave the literal ``0`` the type ``Empty_set`` and a
  closed proof of ``False`` with no axiom. It also refuses, with an error
  in place of an assert failure, a constant registered twice or declared
  by an earlier library, and a registration that gives its constant
  another canonical name. Files written by coqc pass, since coqc registers
  a primitive type only for the parameter that ``Primitive`` declares; a
  registration made in a module is now in force after the module, as in
  coqc
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
