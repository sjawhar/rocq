- **Fixed:**
  ``rocqchk`` no longer inlines the term that an inline hint of a crafted
  ``.vo``'s delta resolver carries. A substitution through the resolver put
  that term in place of the constant without lifting it, and nothing checked
  the term, so a hint whose term has a free variable could make a sealed
  module match a signature it does not match, or give a functor application a
  signature it does not have, and give a closed proof of ``False``. Each
  resolver of a library now loses those terms when the library is loaded, and
  the constant stays where the term would have been; files written by coqc
  pass, as their terms are the bodies of the constants that conversion
  unfolds
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
