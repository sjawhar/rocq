(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** With workers, the statement report would otherwise read each opaque
    body it reaches from its library's table, cook it and walk it, in the
    main process, one body after the other, once the workers had checked
    them all. Instead, the worker that checked a body records the objects
    the report's walk finds in it, and the report takes them from the
    record: those walks are made by the workers, side by side. What a caller
    must do, and the one way the report can differ, are in the header of
    reportRecords.mli; the rules a user sees, in coq-commands.rst.

    The recorder is the hook of [Mod_checking], in two stages. When the main
    process defers the check of the opaque body of a constant, it gives the
    check a number, the index of that constant and that opaque value in
    [deferred]. When the check has passed in a worker, the worker writes
    the record of that number ([record]): the objects
    [Check_closure.opaque_body_refs] finds in the body it checked. After the
    run, the main process maps each number back to its constant and its
    opaque value, and the report uses a record only for that very value,
    as the body of a constant of that name. A record that is missing,
    because a worker could not write it or the main process could not
    read it, only makes the report read that body. The main process
    records nothing: it checks a body itself only where it could not make a
    pipe or fork a worker ([CheckWorkers.spawn]), and the report then reads
    that body, as it does without records.

    Nothing here prints anything, and nothing here can fail a check or the
    run: the hook and the entry points raise nothing but an interrupt, and
    every failure falls back to reading the body. The records take bounded
    room ([worker_file_cap], [buffer_cap], [id_cap], [deferred_cap]), a
    write of a record past the limit on the size of a file fails instead of
    killing the process ([write_all]), a write that fails gives back the
    room its file took ([empty_file]), and nothing is recorded where the
    files of the records would share a file system with a file rocqchk
    writes without them, or where the descriptors they take could be ones
    rocqchk needs without them ([start]). Whatever the library files hold,
    finding the records of a body costs a lookup in a map ordered by names
    and a walk of the records of that name ([t]), and finding an object
    among those the records name, a lookup in such a map ([RefMap]).

    One switch turns the recording off, the buffer of the main process
    ([buffer] and its [whole]): [deferring], [open_file] and [done_ok] look
    at it before anything else, and do nothing once it is gone or the main
    process gave up ([give_up]). The hook of [Mod_checking] stays. *)

open Names

(** {6 The records}

    A record is keyed by the opaque value itself, the one whose check the
    main process deferred and still holds, and by the name of the constant
    whose body that value is, and the report uses it only for that very
    value, as the body of a constant of that name. The body of an opaque
    value, the one the report reads, is a function of the value and of its
    library's table ([CheckLibrary.indirect_accessor]: the stored proof,
    cooked by the value's cooking information, then substituted by its
    substitutions), and the table is the library's file as the main process
    hashed it, which every process that reads it checks. So a record names
    the objects of the body the report would read.

    A key made of the constant's name and the stored proof's library and
    index would not be enough. The cooking information is part of the body:
    it abstracts the section variables the proof uses, and their types and
    the bodies of the [Let]s among them become binders of the body
    (kernel/cooking.ml, [abstract_as_body]), with the objects they name. In
    a file coqc wrote, a stored proof has one cooking information, which it
    gets as its sections close, before any module can hold it (a module is
    never inside a section), and a module that copies a declaration
    substitutes it. But a forged library can give the declaration of a
    constant in a signature and the one in its implementation the same
    stored proof with two cooking informations, both well-typed, so that
    the two bodies name different objects; had the check of one of them
    recorded nothing, the record of the other would stand for it.

    The name of the constant is in the key so that finding the records of
    a value costs little, whatever the library files hold. Opaque values
    have no order, and nothing but their address tells apart those that
    share one stored proof: [n] constants whose declarations hold [n] such
    values, which a forged library can give, would put [n] records under
    one hash of the stored proof, each found among the others. The records
    are kept by the name of their constant instead, in a map ordered by
    names ([Cmap_env]). Nor does a hash table keyed by names do: a kernel
    name carries its hash, which the library file gives and nothing checks
    ([KerName.hash]), so that a forged library can give all its constants
    one hash; in [Cmap_env] the hash only picks a bucket, which is itself a
    map ordered by names ([HMap]). The values of one name are few, a
    constant's declaration in a signature and the one in its
    implementation, but a forged library can repeat a label in a
    structure: they are kept in a list, which only [recorded] reads, and
    the report asks [recorded] at most twice for each constant it reaches,
    once in each of its views ([Check_closure], whose cache of the objects
    it reached orders them as [Cmap_env] does). Reading those lists costs
    then at most twice their length, in all. *)

(* Two objects equal here have both their names equal, and each the hash
   its names carry: they are the same object, and one can stand for the
   other anywhere. As above, the hash only picks a bucket, which is a map
   ordered by names ([HMap]), so that objects that a forged library gives
   one hash are each found among the others in logarithmic time. *)
module RefMap = HMap.Make (struct
    type t = GlobRef.t
    let hash = GlobRef.UserOrd.hash
    let compare a b =
      let c = Int.compare (hash a) (hash b) in
      if c <> 0 then c else
        let c = GlobRef.UserOrd.compare a b in
        if c <> 0 then c else
          let c = Int.compare (GlobRef.CanOrd.hash a) (GlobRef.CanOrd.hash b) in
          if c <> 0 then c else GlobRef.CanOrd.compare a b
  end)

type t = {
  mutable bodies : (Opaqueproof.opaque * GlobRef.t list) list Cmap_env.t;
  (* for each constant, by its name, the opaque value of each record of a
     body of that name, and the objects that record names *)
  mutable shared : GlobRef.t RefMap.t;
  (* one copy of each object the records name *)
  mutable hits : int;
  mutable reads : int;
  (* the opaque constants the report reached whose objects it took from a
     record, and those whose body it read or tried to read *)
}

(* No record, the report reads every body it reaches; or the records,
   before any is added. Allocates one block, so that a failure of
   [collect], which falls back to this, allocates little. *)
let no_records () =
  { bodies = Cmap_env.empty; shared = RefMap.empty; hits = 0; reads = 0 }

(* Each object is kept once, so that the records of a large tree take one
   copy of each name they share: [share r obj] is the copy of [obj] that
   [r] keeps. *)
let share r obj = match RefMap.find_opt obj r.shared with
  | Some obj -> obj
  | None -> r.shared <- RefMap.add obj obj r.shared; obj

(* The record of the body [o] of the constant [kn], which names [objs].
   Adding it looks at no other record. *)
let add_record r kn o objs =
  r.bodies <- Cmap_env.update kn (fun l -> Some ((o, objs) :: Option.default [] l)) r.bodies

(* The objects of the records of the body [o] of a constant of the name of
   [kn]. A value can be checked twice: a declaration that a module's
   signature and its implementation share is checked with each. Its
   records then name the same objects. Records of one value that do not
   are not used, and the report reads that body. The objects of the
   records are the copies [share] keeps, so that two records of one value
   compare physically. *)
let find_record r kn o =
  match Cmap_env.find_opt kn r.bodies with
  | None -> None
  | Some l ->
    let rec scan found = function
      | [] -> found
      | (o', objs) :: l when o' == o ->
        (match found with
         | None -> scan (Some objs) l
         | Some objs' -> if List.equal (==) objs objs' then scan found l else None)
      | _ :: l -> scan found l
    in
    scan None l

let recorded r kn o =
  match find_record r kn o with
  | Some objs -> r.hits <- r.hits + 1; Some objs
  | None -> r.reads <- r.reads + 1; None

(** {6 The checks the main process deferred} *)

(* The constant and the opaque value of each deferred check whose record
   is asked for, the latest first, and their count: the check numbered [n]
   is the one numbered after [n] others. Only the main process defers
   checks, and so fills these, while it checks the libraries. A worker's
   checks were deferred before it was forked, so their numbers are below
   the count it inherited, and they name in the main process the constants
   and values they name in the worker. The main process drops the list
   once it gives up ([give_up]), as no record is used then. *)
let deferred : (Constant.t * Opaqueproof.opaque) list ref = ref []
let deferred_count = ref 0

(* The entries that [deferred] may hold. Each takes a cell and a pair,
   three words each, 48 bytes on a 64-bit machine, and is kept until
   [collect] or [give_up], whether a record of its check is made or not:
   without a cap, a long run of cheap checks whose records are never made
   would keep an entry for every one of them. Past [deferred_cap], 4 Mi
   entries, about 192 MiB of list, the main process gives up
   ([deferring]), so that what the list keeps is bounded whatever the
   input. The constants and opaque values it names are the environment's,
   which holds them anyway. A tree of 4,190 libraries deferred 132,828
   checks, about 6 MiB. *)
let deferred_cap = 4 * 1024 * 1024

(** {6 The files and the buffer}

    Each worker that checks opaque bodies records to a file of its own,
    which the main process opens for it before the fork ([open_file],
    through [CheckWorkers.set_worker_file]): an unnamed file in /dev/shm
    ([records_dir]), created, opened and removed at once, as
    [CheckWorkers.open_capture] makes the files of the workers' output in
    the temporary directory. It lives while a process holds it open, and
    the system frees it with its last descriptor, at the latest when the
    last process that holds it exits: so nothing is left in /dev/shm,
    however the run ends (but for a kill in the instant between the
    creation of a file and its removal). No other user can replace the
    file between its creation and its opening, as [start] records only in
    a /dev/shm that no other user may write to, or that has the sticky bit.
    A process of the same user can open it while it lives, through
    /proc/<pid>/fd, as it can write the files of the workers' output,
    which rocqchk has without records too; such a process is not one a
    grade has to fear, as the grade's step runs alone, in a pid namespace
    of its own. /dev/shm is a file system in memory: its files take
    memory, which [worker_file_cap] bounds, and [start] records nothing
    where rocqchk writes anything else to its file system, so that the
    records cannot take the room that a write of rocqchk needs without
    them, and a full /dev/shm only stops recording.

    A file is a sequence of frames, each one marshalled [record], whose own
    header gives its size ([Marshal.total_size]). The worker writes its
    file, from its start, and records nothing more after its first failure,
    nor once a frame would take the file past its cap, so only the last
    frame of a file can be cut short. A write that fails empties the file
    first ([empty_file]).

    When a worker has ended successfully, the main process copies its file
    into its own memory, as one segment of the buffer, and closes it at
    once ([done_ok]); the file of a worker that failed, or that was killed,
    is closed with no copy. So /dev/shm holds only the files of the workers
    that run, until the main process sees each one end, and the records of
    a worker that failed, whose checks do not count, never reach the
    buffer. Once a file for a worker cannot be made, a segment would take
    the buffer past its cap, or a copy fails, the main process gives up:
    no record is used, nothing more is recorded, and the buffer is dropped
    ([give_up]).

    The main process opens no file for the records but the file of each
    worker, before that worker is forked, and holds it until that worker
    has ended: one descriptor per worker that runs, which [start] counts
    ([room_for_files]). *)

(* The room the records take, in /dev/shm while the workers run, and in
   the memory of the main process once they have ended, and so the bytes
   the main process decodes. What the report reads does not bound it: [n]
   opaque constants can share one stored proof that names [k] objects, and
   the check of each of them records the [k] objects, so that the records
   hold [n * k] numbers, while the report walks only the bodies it
   reaches. So a worker stops recording once its file would pass its cap
   ([worker_file_cap]), and the main process gives up once the buffer would
   pass its cap ([buffer_cap]): the report then reads every body, as it
   does without records. A worker's cap is [max_file_cap], or [files_cap]
   divided by the number of workers that may be alive at once
   ([CheckWorkers.jobs]) where that is less, so that the files of the
   workers alive hold at most [files_cap] in all, whatever [-j]: /dev/shm
   is memory. The segment that the main process copies from a file is that
   file, and the buffer holds at most [default_buffer_cap]. So the records
   take at most 512 MiB in all, in /dev/shm and in the main process. On a
   tree of 4,190 libraries they took 48 MB in all, so these leave a wide
   margin above it. What the decoding keeps in memory is bounded apart
   ([id_cap]), and so is the cache of the walk that makes the records
   ([Check_closure.opaque_body_refs]), 6 MiB in each worker that records,
   on a 64-bit machine. *)
let max_file_cap = 64 * 1024 * 1024
let files_cap = 256 * 1024 * 1024
let default_buffer_cap = 256 * 1024 * 1024

let worker_file_cap () = min max_file_cap (files_cap / CheckWorkers.jobs ())

(* Test-only seam, in the style of [Check_closure]'s: a number of bytes in
   COQ_TEST_SUITE_STATEMENT_REPORT_RECORDS_CAP lowers the cap of the
   buffer, so that a test can make the main process give up. *)
let buffer_cap () =
  match Option.bind (Sys.getenv_opt "COQ_TEST_SUITE_STATEMENT_REPORT_RECORDS_CAP")
          int_of_string_opt with
  | Some n when n >= 0 -> min n default_buffer_cap
  | Some _ | None -> default_buffer_cap

(* The numbers of objects that the main process decodes, in all the
   segments, may be at most [id_cap] ([read_segment]). Each becomes a cell
   of a list that the records keep, three words, and the cap of the buffer
   bounds them poorly: a number below 64 takes one byte in a frame, so a
   buffer of 256 MiB can hold 256 Mi numbers, 6 GiB of cells. The objects
   themselves are kept once each ([share]), so the objects that exist
   bound them. Past [id_cap], 32 Mi numbers, about 768 MiB of cells on a
   64-bit machine, the main process gives up, and the report reads every
   body. The 48 MB of records of the tree of 4,190 libraries held far
   fewer, by an estimate from the frame format, not a count: a frame takes
   about 30 bytes besides its numbers (the marshal header of 20 bytes, the
   number of the check, the headers of its arrays) and the objects it
   names first, tens of bytes each; a number takes 1 byte below 64, 2
   below 128, 3 below 32,768, and a worker numbers thousands of objects.
   If half of those records are numbers, at about 2 bytes each, they hold
   some 12 million; they would pass the cap only if some 70% of them were
   numbers of 1 byte. *)
let id_cap = 32 * 1024 * 1024

(* What a worker holds while it makes one record has no cap of its own,
   and needs none: it is linear in the size of the body the worker has
   just checked, which the check held. The record has at most one entry
   per distinct object of the body ([Check_closure.opaque_body_refs] gives
   a set), the walk that finds them is linear in the size of the body, its
   cache has a fixed size, and the frame of the record grows with its
   entries; a worker's numbering keeps besides the objects its file names,
   which the cap of its file bounds. The caps above bound what the records
   keep from one check to the next, in /dev/shm and in memory. Each record
   that the main process decodes adds to [bodies] a cell and a pair, and
   to the map at most one entry; each check makes one record at most, so
   that the deferred checks bound these too. *)

(* A record. [index] is the number of its check. Each file numbers the
   objects its records name, 0, 1, ... in the order they are first
   recorded: [defs] are the objects this record names first, which take
   the next numbers in order, and [ids] are the objects of the body, by
   number, in the order [Check_closure.opaque_body_refs] gives them. *)
type record = {
  index : int;
  defs : GlobRef.t array;
  ids : int array;
}

(* A numbering of the objects that records name. *)
type numbering = {
  mutable numbers : int RefMap.t;
  (* the number of each object numbered so far *)
  mutable next : int;
  (* the number the next new object takes *)
}

let numbering () = { numbers = RefMap.empty; next = 0 }

(* A worker's file, with its numbering of objects. A raw descriptor, to
   which each record goes whole as soon as it is made, so that nothing
   waits in a buffer: a worker leaves through [Unix._exit], which flushes
   nothing. *)
type output = {
  fd : Unix.file_descr;
  numbering : numbering;
  max_size : int;
  (* the bytes [fd] may hold: the [file_cap] of the buffer the worker was
     forked with *)
  mutable size : int;
  (* the bytes written to [fd] so far *)
}

(* The main process's buffer, from [start] to [collect]. *)
type buffer = {
  cap : int;
  (* the bytes the buffer may take: [buffer_cap ()] *)
  file_cap : int;
  (* the bytes the file of each worker may take: [worker_file_cap ()] *)
  mutable segments : Bytes.t list;
  (* the segments kept so far, the latest first *)
  mutable size : int;
  (* the bytes of [segments] *)
  mutable whole : bool;
  (* false once the main process gave up ([give_up]): no record is used,
     and nothing more is recorded *)
}

let buffer : buffer option ref = ref None

(* The file this process records to, in a worker that has one, until a
   write failed or a frame would have taken the file past its cap; [None]
   anywhere else, the main process included. *)
let current : output option ref = ref None

(* Every write of the records, and only those, is made with SIGXFSZ
   ignored, and the action it had is restored after. A write past the
   limit on the size of a file (RLIMIT_FSIZE, [ulimit -f]), which the files
   in /dev/shm meet as any other, then fails with EFBIG, which the caller
   takes as a failure of the recording, instead of raising that signal,
   whose default action kills the process: without records, rocqchk writes
   none of these files, and a limit that they meet must not end a run it
   would finish. If the action cannot be set, nothing is written, and that
   is a failure of the recording too. Every other write, such as the
   output of a worker, keeps the action it has. *)
let write_all fd b ofs len =
  let rec write ofs len =
    if len > 0 then
      match Unix.single_write fd b ofs len with
      | 0 -> failwith "ReportRecords.write_all"
      | n -> write (ofs + n) (len - n)
      | exception Unix.Unix_error (Unix.EINTR, _, _) -> write ofs len
  in
  let previous = Sys.signal Sys.sigxfsz Sys.Signal_ignore in
  match write ofs len with
  | () -> Sys.set_signal Sys.sigxfsz previous
  | exception e -> Sys.set_signal Sys.sigxfsz previous; raise e

(* Empties the file [fd], ignoring any failure but an interrupt. A write of
   the records may fail for want of room in /dev/shm (ENOSPC), which is
   memory, and which the files of the other workers share; the records of
   that file are then given up. Emptying the file gives back that room at
   once, instead of when the main process closes the file, once the worker
   has ended. Allocates nothing but on a failure. *)
let empty_file fd =
  try Unix.ftruncate fd 0 with
  | Sys.Break as e -> raise e
  | _ -> ()

let rec read_all fd b ofs len =
  if len > 0 then
    match Unix.read fd b ofs len with
    | 0 -> failwith "ReportRecords.read_all"
    | n -> read_all fd b (ofs + n) (len - n)
    | exception Unix.Unix_error (Unix.EINTR, _, _) -> read_all fd b ofs len

(* Copies the file [fd] of a worker, whole, into [b] as one segment. An
   empty file adds nothing. Fails, keeping nothing, if the file would take
   [b] past its cap, which is checked before the copy is allocated. *)
let copy_file b fd =
  let size = Unix.lseek fd 0 Unix.SEEK_END in
  if size > 0 then begin
    if b.size + size > b.cap then failwith "ReportRecords.copy_file";
    ignore (Unix.lseek fd 0 Unix.SEEK_SET);
    let seg = Bytes.create size in
    read_all fd seg 0 size;
    b.segments <- seg :: b.segments;
    b.size <- b.size + size
  end

(** {6 Recording} *)

(* In the main process: no record is used, and nothing more is recorded,
   so that the report reads every body it reaches: [deferring] numbers no
   more checks, [open_file] makes no more files, and [done_ok] copies none
   ([whole]). The constants and opaque values of the deferred checks, which
   no record will be matched to, are dropped, and so is the buffer. It
   allocates nothing, so that it can follow any failure. *)
let give_up () =
  deferred := [];
  match !buffer with
  | Some b -> b.whole <- false; b.segments <- []; b.size <- 0
  | None -> ()

(* The frame of the record of check [index], whose body names the objects
   [objs], in the numbering [n]: the objects [n] has no number for yet
   take the next ones. *)
let make_frame n index objs =
  let defs = ref [] in
  let number obj = match RefMap.find_opt obj n.numbers with
    | Some k -> k
    | None ->
      let k = n.next in
      n.next <- k + 1;
      n.numbers <- RefMap.add obj k n.numbers;
      defs := obj :: !defs;
      k
  in
  let ids = Array.of_list (List.map number objs) in
  Marshal.to_bytes { index; defs = Array.of_list (List.rev !defs); ids } []

(* The second stage of the hook, in whichever process checked the body [c]
   of check [index], in [env]: a worker with a file records it there, and
   any other process, the main one included, has none ([current]) and does
   nothing. It raises nothing but an interrupt, which is the user's. Any
   failure stops the recording in that worker only, and so does a frame
   that would take its file past its cap; a write that fails empties the
   file first ([empty_file]), and the report then reads the bodies that
   worker checked. *)
let record index env c =
  match !current with
  | None -> ()
  | Some o ->
    try
      let frame = make_frame o.numbering index (Check_closure.opaque_body_refs env c) in
      let size = Bytes.length frame in
      if o.size + size > o.max_size then current := None
      else begin
        (try write_all o.fd frame 0 size with
         | Sys.Break as e -> raise e
         | e -> empty_file o.fd; raise e);
        o.size <- o.size + size
      end
    with
    | Sys.Break as e -> raise e
    | _ -> current := None

(* The second stage of a check that is not recorded. *)
let no_record _ _ = ()

(* The first stage of the hook, in the process that defers the check of
   the opaque [o] of the constant [kn], the main process: it numbers the
   check, and the second stage carries the number. Every opaque is
   recorded, with substitutions or without: the key alone, the name of the
   constant and the very value, decides which record the report uses. The
   copies that the report makes itself are read: its implementation view
   substitutes the structure of each module it looks into ([Check_closure]'s
   [fields_of_mp], through [Modops.subst_structure]), and a copy made there
   with a substitution is a new value, which no record matches. It runs
   while the main process checks, and raises nothing but an interrupt: if
   anything fails here, or once [deferred] would pass [deferred_cap], the
   main process gives up, and the check runs with no second stage. Once
   the main process gave up, it adds nothing to [deferred]. *)
let deferring kn o =
  match !buffer with
  | Some b when b.whole ->
    let n = !deferred_count in
    if n >= deferred_cap then (give_up (); no_record)
    else
      (try
         deferred := (kn, o) :: !deferred;
         deferred_count := n + 1;
         record n
       with
       | Sys.Break as e -> raise e
       | _ -> give_up (); no_record)
  | Some _ | None -> no_record

(** {6 The files of the workers}

    None of these raises anything but an interrupt, as
    [CheckWorkers.set_worker_file] asks. *)

(* The directory of the workers' files: a file system in memory, which
   rocqchk writes nothing else to where it records ([start]). *)
let records_dir = "/dev/shm"

(* In the main process, before each fork: a file for the worker, or none
   once the main process gave up. A file that cannot be made gives up for
   the whole run, as the other failures do: had the main process gone on
   without it, nothing else would end the recording where no file can be
   made at all, as in a /dev/shm whose room or inodes are used up, and
   [deferred] would grow with every check while no record is made. *)
let open_file () =
  match !buffer with
  | Some b when b.whole ->
    (match CheckWorkers.open_capture ~temp_dir:records_dir () with
     | Some _ as file -> file
     | None -> give_up (); None
     | exception (Sys.Break as e) -> give_up (); raise e
     | exception _ -> give_up (); None)
  | Some _ | None -> None

(* In a worker, right after the fork. The buffer is not its to fill: it
   drops its copy, and records to its own file, if it has one, with a
   numbering of its own, up to the cap of a worker's file that the main
   process set. *)
let in_child fd =
  let max_size = match !buffer with Some b -> b.file_cap | None -> 0 in
  current := None;
  buffer := None;
  Option.iter (fun fd ->
      current := Some { fd; numbering = numbering (); max_size; size = 0 }) fd

(* In the main process, once the worker whose file is [fd] has ended
   successfully: the file is copied into the buffer ([copy_file]), and
   closed at once, whatever happens. Any failure but an interrupt gives
   up; nothing is allocated outside the handler. *)
let done_ok fd =
  match !buffer with
  | Some b when b.whole ->
    (match copy_file b fd with
     | () -> CheckWorkers.close_fd fd
     | exception (Sys.Break as e) -> give_up (); CheckWorkers.close_fd fd; raise e
     | exception _ -> give_up (); CheckWorkers.close_fd fd)
  | Some _ | None -> CheckWorkers.close_fd fd

(** {6 The main process, around the run} *)

(* The soft limit on the descriptors of this process (RLIMIT_NOFILE,
   [ulimit -n]): the first number of the line "Max open files" of
   /proc/self/limits, [max_int] where it says "unlimited". Fails if the
   file cannot be read, or holds no such line, or no number there. *)
let open_files_limit () =
  let prefix = "Max open files" in
  let ch = open_in "/proc/self/limits" in
  let line =
    Fun.protect ~finally:(fun () -> close_in_noerr ch) (fun () ->
        let rec find () =
          let line = input_line ch in
          if String.starts_with ~prefix line then line else find ()
        in
        find ())
  in
  let rest = String.sub line (String.length prefix) (String.length line - String.length prefix) in
  match List.filter (fun s -> s <> "") (String.split_on_char ' ' rest) with
  | "unlimited" :: _ -> max_int
  | n :: _ ->
    (match int_of_string_opt n with
     | Some n -> n
     | None -> failwith "ReportRecords.open_files_limit")
  | [] -> failwith "ReportRecords.open_files_limit"

(* The descriptors this process holds, as /proc/self/fd lists them, and
   whether one of them is open on a file of the file system [dev]. The
   listing ([Sys.readdir]) holds one descriptor itself, the directory's,
   which it lists too and closes before it returns: it is not counted, and
   [Unix.LargeFile.stat], which looks at a file of any size, finds it
   closed (ENOENT), which it is the only one to be. Fails if the directory
   cannot be read, or if a descriptor it lists cannot be looked at but for
   that. *)
let open_descriptors dev =
  let dir = "/proc/self/fd" in
  let fds = Sys.readdir dir in
  let on_dev fd =
    match Unix.LargeFile.stat (Filename.concat dir fd) with
    | st -> st.Unix.LargeFile.st_dev = dev
    | exception Unix.Unix_error (Unix.ENOENT, _, _) -> false
  in
  Array.length fds - 1, Array.exists on_dev fds

(* The file system of [records_dir], which must be a directory that this
   process may create files in: fails if it is not, or if it cannot be
   looked at, as where there is no /dev/shm. It fails too where users other
   than its owner may write to it and it has no sticky bit: such a user
   could remove and replace a file of the records between its creation and
   its opening ([CheckWorkers.open_capture]), and then see or change what a
   worker records. *)
let records_device () =
  let st = Unix.stat records_dir in
  let perm = st.Unix.st_perm in
  if st.Unix.st_kind <> Unix.S_DIR
  || (perm land 0o022 <> 0 && perm land 0o1000 = 0)
  then failwith "ReportRecords.records_device";
  Unix.access records_dir [Unix.W_OK; Unix.X_OK];
  st.Unix.st_dev

(* Whether the temporary directory (TMPDIR), in which the files of the
   workers' output are made ([CheckWorkers.open_capture]), is on the file
   system [dev]. A directory that cannot be looked at is one in which no
   file can be made either, and so on none. *)
let temp_dir_on dev =
  match Unix.stat (Filename.get_temp_dir_name ()) with
  | st -> st.Unix.st_dev = dev
  | exception Unix.Unix_error _ -> false

(* Whether the system's table of open files has room for [need] more, by
   /proc/sys/fs/file-nr ("allocated unused max"): its size less the files
   open in it, read unsigned, as the size may be LONG_MAX, which is past
   [max_int]. The limit of this process ([room_for_files]) does not count
   the files of other processes: in a system whose table is nearly full,
   the files of the records could take the last places, and a later open
   that rocqchk needs, of a library say, would fail where it succeeds
   without records. Where the file does not exist (ENOENT), the system
   shows no such table, as under gVisor, and there is nothing to check;
   any other failure to read or parse it fails, and then nothing is
   recorded. Other processes that fill the table while rocqchk runs make
   the outcome of a run without records depend on them too, which no check
   at the start can cover. *)
let system_room need =
  match Unix.openfile "/proc/sys/fs/file-nr" [Unix.O_RDONLY; Unix.O_CLOEXEC] 0 with
  | exception Unix.Unix_error (Unix.ENOENT, _, _) -> true
  | fd ->
    let ch = try Unix.in_channel_of_descr fd with e -> CheckWorkers.close_fd fd; raise e in
    let line = Fun.protect ~finally:(fun () -> close_in_noerr ch) (fun () -> input_line ch) in
    let number s =
      if String.equal s "" || not (String.for_all (fun c -> '0' <= c && c <= '9') s)
      then failwith "ReportRecords.system_room";
      Int64.of_string ("0u" ^ s)
    in
    let words = String.split_on_char ' ' (String.map (fun c -> if Char.equal c '\t' then ' ' else c) line) in
    match List.filter (fun s -> not (String.equal s "")) words with
    | [allocated; _; size] ->
      let allocated = number allocated and size = number size in
      Int64.unsigned_compare allocated size <= 0
      && Int64.unsigned_compare (Int64.sub size allocated) (Int64.of_int need) >= 0
    | _ -> failwith "ReportRecords.system_room"

(* Whether the descriptors the workers may need with their files of
   records ([CheckWorkers.descriptors_for_workers], one file each) fit
   below the soft limit on open files less the [held] descriptors this
   process already holds, and in the system's table of open files. The
   descriptors held already, those inherited and those rocqchk opened
   before the libraries are loaded, are not free for any of these: so the
   room is the limit less them, not the limit. Under less room, a
   descriptor the recorder took could be the one a later pipe, file of
   output or library load needs, which would then fail where it succeeds
   without records. Fails if the limit or the table cannot be read. *)
let room_for_files held =
  let need = CheckWorkers.descriptors_for_workers ~extra_per_worker:1 in
  open_files_limit () - held >= need && system_room need

(* The conditions of coq-commands.rst that [start] checks itself (its
   caller checks the others: see reportRecords.mli). [records_dir] is a
   directory this process may create files in, in which no other user can
   replace one ([records_device]), on another file system than every file
   rocqchk writes without records, so that the records cannot take the
   room one of those writes needs: that of the temporary directory, in
   which the files of the workers' output are made, and that of each
   descriptor this process holds, such as its standard output and error
   (those are all the files rocqchk writes, but for those of the test
   seams and of -compare, with which nothing is recorded); and the
   descriptors of the records fit ([room_for_files]). Opens nothing but
   the directory /proc/self/fd and the files /proc/self/limits and
   /proc/sys/fs/file-nr, each closed at once. If anything fails but an
   interrupt, nothing is recorded. [buffer] is set last: until then, and
   if anything fails, [deferring], [open_file] and [done_ok] do nothing. *)
let start () =
  try
    let dev = records_device () in
    let held, held_on_dev = open_descriptors dev in
    if not held_on_dev && not (temp_dir_on dev) && room_for_files held then begin
      let b = { cap = buffer_cap (); file_cap = worker_file_cap (); segments = [];
                size = 0; whole = true } in
      CheckWorkers.set_worker_file { CheckWorkers.open_file; in_child; done_ok };
      Mod_checking.set_opaque_check_hook deferring;
      buffer := Some b
    end
  with
  | Sys.Break as e -> raise e
  | _ -> buffer := None

(* The records of one segment, in order, for the constants and opaque
   values [values] of the checks, by number. A frame cut short, or one
   whose record or numbers are wrong, ends the segment: what follows it
   cannot be told apart from what it holds. The records read before it are
   whole, and kept. [decoded] counts the numbers of objects decoded so far,
   in all the segments: one that would take it past [id_cap] raises, and
   then no record is used. *)
let read_segment records values decoded b =
  let objects = ref [||] and known = ref 0 in
  let add (r : record) =
    let n = Array.length r.defs in
    if n > 0 then begin
      if !known + n > Array.length !objects then begin
        let a = Array.make (max 1024 (2 * (!known + n))) r.defs.(0) in
        Array.blit !objects 0 a 0 !known;
        objects := a
      end;
      Array.iteri (fun j obj -> (!objects).(!known + j) <- share records obj) r.defs;
      known := !known + n
    end;
    if r.index < 0 || r.index >= Array.length values
       || Array.exists (fun k -> k < 0 || k >= !known) r.ids
    then false
    else begin
      let count = !decoded + Array.length r.ids in
      if count > id_cap then failwith "ReportRecords.read_segment";
      decoded := count;
      let objs = Array.fold_right (fun k objs -> (!objects).(k) :: objs) r.ids [] in
      let kn, o = values.(r.index) in
      add_record records kn o objs;
      true
    end
  in
  let rec frames ofs =
    let left = Bytes.length b - ofs in
    if left >= Marshal.header_size then
      match Marshal.total_size b ofs with
      | exception (Failure _ | Invalid_argument _) -> ()
      | size when size > left -> ()
      | size ->
        match (Marshal.from_bytes b ofs : record) with
        | exception (Failure _ | Invalid_argument _) -> ()
        | r -> if add r then frames (ofs + size)
  in
  frames 0

(* The records of the segments of [b], in order, for the checks [checks],
   latest first: none if the main process gave up, or if no worker left
   any. The segments are taken out of the buffer before they are
   decoded. *)
let read_records b checks =
  let records = no_records () in
  if b.whole && not (CList.is_empty b.segments) then begin
    let values = Array.of_list (List.rev checks) and decoded = ref 0 in
    let segments = List.rev b.segments in
    b.segments <- [];
    List.iter (read_segment records values decoded) segments
  end;
  records

(* Everything after the run that allocates is inside the handlers: any
   failure but an interrupt leaves no record, and if even the empty
   records cannot be made, [None], with which the report reads every body
   as well. The buffer is dropped whatever happens. *)
let collect () =
  match !buffer with
  | None -> None
  | Some b ->
    buffer := None;
    let checks = !deferred in
    deferred := [];
    deferred_count := 0;
    try Some (read_records b checks) with
    | Sys.Break as e -> raise e
    | _ ->
      try Some (no_records ()) with
      | Sys.Break as e -> raise e
      | _ -> None

(* Test-only seam, in the style of [Check_closure]'s: a test sets this to a
   file, to which the main process writes "<hits> <reads>" after the
   report, so that a test sees the records used on the path that streams
   the libraries, which [-d checker-workers] turns off. *)
let test_counts r =
  match Sys.getenv_opt "COQ_TEST_SUITE_STATEMENT_REPORT_COUNTS" with
  | None | Some "" -> ()
  | Some file ->
    try
      let oc = open_out file in
      Fun.protect ~finally:(fun () -> close_out_noerr oc) (fun () ->
          Printf.fprintf oc "%d %d\n" r.hits r.reads)
    with Sys_error _ -> ()
