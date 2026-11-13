- **Fixed:**
  In a match that the virtual machine cannot reduce, the arguments of the
  245th and later non-constant constructors of an inductive type, which have
  an extended tag, had de Bruijn levels one too high, so that the last
  argument and the first variable bound in the branch's body were the same
  variable. VM conversion then found two different functions convertible, so
  that a ``vm_compute`` cast could prove :g:`False`, and ``vm_compute``
  returned wrong normal forms
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  fixes `#22760 <https://github.com/rocq-prover/rocq/issues/22760>`_,
  by Sami Jawhar).
