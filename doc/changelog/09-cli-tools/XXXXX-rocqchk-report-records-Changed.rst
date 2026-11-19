- **Changed:**
  With ``-j n``, ``rocqchk -statement-report`` takes the references of
  each opaque proof that a worker checked from that worker, which records
  them as it checks the proof, instead of reading and walking each of
  those proofs again in the main process. The records take bounded
  memory, whatever the libraries hold: at most 512 MiB for their bytes, in
  ``/dev/shm`` and then in the main process, and about 1.1 GiB more in the
  main process as it keeps track of them and decodes them (on a 64-bit
  machine, besides a copy of each object they name, up to about 3.3 GiB
  more). Each worker that records also keeps a number for each object its
  records name, which takes up to about 0.5 GiB in a worker and 2 GiB in
  all the workers that run at once, on a 64-bit machine. Libraries within
  those bounds can make ``rocqchk`` use more memory than before. Nothing
  is recorded with ``-compare`` or ``-merge-inductives``, nor where the
  records would share a file system with a file ``rocqchk`` writes, or
  take open files it may need. With ``-j``, where the records are off or
  given up, ``rocqchk`` prints one line on its standard error before the
  report, ``rocqchk: statement report: records off: REASON`` or
  ``rocqchk: statement report: records given up: REASON``.
  The report is the same, but where a library file changes or vanishes
  while ``rocqchk`` runs, which can change the proofs it says it could not
  read (see :ref:`rocqchk`)
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
