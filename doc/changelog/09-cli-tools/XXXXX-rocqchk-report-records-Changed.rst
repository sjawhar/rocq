- **Changed:**
  With ``-j n``, ``rocqchk -statement-report`` takes the references of
  each opaque proof that a worker checked from that worker, which records
  them as it checks the proof, instead of reading and walking each of
  those proofs again in the main process once all of them are checked.
  The proofs that the report reaches through a copy it makes itself, by
  substituting the structure of a module it looks into, are still read
  again. The records are kept in temporary files that exist only while
  ``rocqchk`` runs: no directory is made, and nothing is left behind.
  The report is the same, but for one case: a proof that a worker
  checked is not read again, so a library file that changes or vanishes
  on disk during the run no longer makes the report warn that this
  proof could not be read
  (see :ref:`rocqchk`)
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
