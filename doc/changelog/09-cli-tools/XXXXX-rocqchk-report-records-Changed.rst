- **Changed:**
  With ``-j n``, ``rocqchk -statement-report`` takes the references of
  each opaque proof that a worker checked from that worker, which records
  them as it checks the proof, instead of reading and walking each of
  those proofs again in the main process. The records take bounded
  memory, whatever the libraries hold: at most 512 MiB for their bytes, in
  ``/dev/shm`` and then in the main process, and about 1.5 GiB more in the
  main process as it keeps track of them and decodes them (on a 64-bit
  machine, besides a copy of each object they name); libraries within
  those bounds can make ``rocqchk`` use more memory than before. Nothing
  is recorded with ``-compare`` or ``-merge-inductives``, nor where the
  records would share a file system with a file ``rocqchk`` writes, or
  take open files it may need.
  The report is the same, but where a library file changes or vanishes
  while ``rocqchk`` runs, which can change the proofs it says it could not
  read (see :ref:`rocqchk`)
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
