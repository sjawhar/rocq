- **Changed:**
  With ``-j n``, ``rocqchk -statement-report`` takes the references of
  each opaque proof that a worker checked from that worker, which records
  them as it checks the proof, instead of reading and walking each of
  those proofs again in the main process once all of them are checked.
  The proofs that the report reaches through a copy it makes itself, by
  substituting the structure of a module it looks into, are still read
  again. While a worker runs, its records are kept in a temporary file in
  ``/dev/shm``, a file system in memory, and once it has ended, in the
  memory of the main process, which copies that file and closes it at
  once: no directory is made, and nothing is left behind, unless
  ``rocqchk`` is killed in the instant between the creation of such a
  file and its removal, as with the files that hold the output of the
  workers. Nothing is recorded where ``/dev/shm`` is not a directory
  ``rocqchk`` can write to, nor where it is on the file system of
  ``TMPDIR``, or of a file that ``rocqchk`` holds open as it starts, such
  as its standard output: so the records take no room that ``rocqchk``
  needs without them, and a full ``/dev/shm`` only stops recording. The
  records take at most 64 MiB per process; if those of all the processes
  would pass 256 MiB, or name more than 32 Mi objects in all, none is
  used, and the report reads the proofs as before. A limit on the size of
  files (``ulimit -f``) that the records meet costs only records, not the
  run. With ``-compare``, nothing is recorded, and the report reads the
  proofs as before. Where the limit on open files (``ulimit -n``), less
  the files already open, is below ``4 n + 64`` with ``-j n``, or where
  ``rocqchk`` cannot read that limit from ``/proc/self/limits`` or those
  files from ``/proc/self/fd``, nothing is recorded, and the report reads
  the proofs as before.
  The report is the same, but for one case: a proof that a worker
  checked is not read again, so a library file that changes or vanishes
  on disk during the run no longer makes the report warn that this
  proof could not be read, nor report it as an axiom
  (see :ref:`rocqchk`)
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
