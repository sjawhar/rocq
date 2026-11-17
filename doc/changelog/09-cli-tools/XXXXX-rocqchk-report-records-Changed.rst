- **Changed:**
  With ``-j n``, ``rocqchk -statement-report`` takes the references of
  each opaque proof that a worker checked from that worker, which records
  them as it checks the proof, instead of reading and walking each of
  those proofs again in the main process once all of them are checked.
  The report is the same. The records are kept in a directory that
  ``rocqchk`` makes for them in the temporary directory (``TMPDIR``) and
  removes once it has read them, and when it exits
  (see :ref:`rocqchk`)
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
