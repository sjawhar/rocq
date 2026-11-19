(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The recorder works in two stages. When the main process defers the
    check of the opaque body of a constant ([deferring]), it numbers the
    check: the index of that constant and that opaque value in its list of
    deferred checks. When the check has passed in a worker, the worker
    writes the record of that number, the objects
    [Check_closure.opaque_body_refs] finds in the body, to a file of its own
    ([record]). After the run, the main process maps each number back to its
    constant and its opaque value ([collect]). Its whole state is [mode].

    Nothing here can fail a check or the run: every entry point raises
    nothing but an interrupt, and every failure only leaves the report to
    read the bodies it would have taken from the records. *)

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
   its names carry: one can stand for the other anywhere. As above, the
   hash only picks a bucket, a map ordered by names ([HMap]) whose keys all
   have the same user hash, so that objects that a forged library gives one
   hash are each found among the others in logarithmic time. The order
   walks both names, so every object this map holds or looks up is checked
   first ([CheckNames.finite_names]): in the worker, by the walk that finds
   it ([Check_closure.opaque_body_refs]), and in the main process, as its
   frame is decoded ([read_segment]). *)
module RefMap = HMap.Make (struct
    type t = GlobRef.t
    let hash = GlobRef.UserOrd.hash
    let compare a b =
      let c = GlobRef.UserOrd.compare a b in
      if c <> 0 then c else
        let c = Int.compare (GlobRef.CanOrd.hash a) (GlobRef.CanOrd.hash b) in
        if c <> 0 then c else GlobRef.CanOrd.compare a b
  end)

(* A decoded record: the opaque value of its check, and the objects of the
   body, by number ([ids]), in the objects its segment numbered
   ([objects]), an array that decoding only replaces by a longer copy of
   itself, so that its last value holds every number of the segment. *)
type body = {
  value : Opaqueproof.opaque;
  objects : GlobRef.t array ref;
  ids : int array;
}

type t = {
  mutable bodies : body list Cmap_env.t;
  (* the records of the bodies of each constant, by its name *)
  mutable hits : int;
  mutable reads : int;
  (* the opaque constants the report reached whose objects it took from a
     record, and those whose body it read or tried to read *)
}

(* No record: the report reads every body it reaches. *)
let no_records () = { bodies = Cmap_env.empty; hits = 0; reads = 0 }

(* Adds the record [b] of a body of the constant [kn], looking at no other
   record. *)
let add_record r kn b =
  r.bodies <- Cmap_env.update kn (fun l -> Some (b :: Option.default [] l)) r.bodies

(* Whether the records [a] and [b] name the same objects, in the same
   order. Their objects are the copies that [share] keeps, so this compares
   them physically. *)
let same_objects a b =
  let oa = !(a.objects) and ob = !(b.objects) in
  Int.equal (Array.length a.ids) (Array.length b.ids)
  && Array.for_all2 (fun i j -> oa.(i) == ob.(j)) a.ids b.ids

(* The record of the body [o] of a constant of the name of [kn]. A value
   can be checked twice: a declaration that a module's signature and its
   implementation share is checked with each, and its records then name the
   same objects. Records of one value that do not are not used, and the
   report reads that body. *)
let find_record r kn o =
  match Cmap_env.find_opt kn r.bodies with
  | None -> None
  | Some l ->
    let rec scan found = function
      | [] -> found
      | b :: l when b.value == o ->
        (match found with
         | None -> scan (Some b) l
         | Some b' -> if same_objects b b' then scan found l else None)
      | _ :: l -> scan found l
    in
    scan None l

let recorded r kn o =
  match find_record r kn o with
  | Some b ->
    r.hits <- r.hits + 1;
    let objects = !(b.objects) in
    Some (CArray.map_to_list (fun k -> objects.(k)) b.ids)
  | None -> r.reads <- r.reads + 1; None

(** {6 The caps}

    What the report reads does not bound the records: [n] opaque constants
    can share one stored proof that names [k] objects, and the check of
    each of them records the [k] objects, while the report walks only the
    bodies it reaches. So past a cap, a worker records no more, or the main
    process gives up and the report reads every body, as it does without
    records. What a worker holds while it makes one record needs no cap:
    it is linear in the size of the body it has just checked. Its
    numbering of the objects its records name ([numbering]) lasts from
    one record to the next, until it ends or stops recording, and the
    cap of its file bounds it: each object it numbers is in the [defs]
    of a frame of that file, in some bytes there. The one exception is
    the body whose frame would pass the cap: [make_frame] numbers its
    objects before [record] finds that the frame does not fit. The sums
    at the caps are in coq-commands.rst. *)

(* The checks the main process defers before it gives up ([deferring]):
   4 Mi, each kept until [collect] as a cell and a pair, 48 bytes on a
   64-bit machine, 192 MiB. *)
let deferred_cap = 4 * 1024 * 1024

(* The bytes of a worker's file: [max_file_cap], or [files_cap] divided by
   the workers alive at once ([CheckWorkers.jobs]) where that is less, so
   that the files of the workers alive hold at most 256 MiB of /dev/shm,
   which is memory. *)
let max_file_cap = 64 * 1024 * 1024
let files_cap = 256 * 1024 * 1024

let worker_file_cap () = min max_file_cap (files_cap / CheckWorkers.jobs ())

(* The bytes the main process copies from the files of the workers before
   it gives up ([done_ok]): 256 MiB. *)
let default_buffer_cap = 256 * 1024 * 1024

(* Test-only seam, in the style of [Check_closure]'s: a number of bytes in
   COQ_TEST_SUITE_STATEMENT_REPORT_RECORDS_CAP lowers the cap of the
   buffer, so that a test can make the main process give up. *)
let buffer_cap () =
  match Option.bind (Sys.getenv_opt "COQ_TEST_SUITE_STATEMENT_REPORT_RECORDS_CAP")
          int_of_string_opt with
  | Some n when n >= 0 -> min n default_buffer_cap
  | Some _ | None -> default_buffer_cap

(* The numbers of objects the main process decodes, in all the segments,
   before it gives up ([read_segment]): 32 Mi, each a word of the array of
   numbers that its record keeps, 256 MiB on a 64-bit machine. A number
   below 64 takes one byte in a frame, so the cap of the buffer bounds
   them poorly. *)
let id_cap = 32 * 1024 * 1024

(** {6 The files}

    Each worker that checks opaque bodies records to a file of its own,
    which the main process opens for it before the fork ([open_file],
    through [CheckWorkers.set_worker_file]) and holds until that worker has
    ended: a file in /dev/shm ([records_dir]), created, opened and removed
    at once ([CheckWorkers.open_unnamed]). The system frees it with its last
    descriptor, at the latest when the last process that holds it exits, so
    nothing is left in /dev/shm however the run ends, but for a kill in the
    instant between the creation of a file and its removal, or a file that
    cannot be removed, as in a sandbox that forbids removing files in
    /dev/shm: such a file is closed at once, unused, and the main process
    gives up, so that no other is made. A named file of the records would
    outlive the run with what it holds. No other user can replace the file
    between its creation and its opening, as [start] records only in a
    /dev/shm that no other user may write to, or that has the sticky bit. A
    process of the same user can open it while it lives, through
    /proc/<pid>/fd, as it can the files of the workers' output, which
    rocqchk has without records too; such a process is not one a grade has
    to fear, as the grade's step runs alone, in a pid namespace of its own.

    A file is a sequence of frames, each one marshalled [frame], whose own
    header gives its size ([Marshal.total_size]). The worker writes its
    file from its start, and records nothing more after its first failure,
    nor once a frame would take the file past its cap, so only the last
    frame of a file can be cut short. A write that fails empties the file
    first ([empty_file]).

    When a worker has ended successfully, the main process copies its file,
    whole, as one segment, and closes it at once ([done_ok]); the file of a
    worker that failed, or that was killed, is closed with no copy, so the
    records of a worker whose checks do not count never reach the main
    process. *)

(* A record, as a worker writes it. [index] is the number of its check.
   Each file numbers the objects its records name, 0, 1, ... in the order
   they are first recorded: [defs] are the objects this record names first,
   which take the next numbers in order, and [ids] are the objects of the
   body, by number, in the order [Check_closure.opaque_body_refs] gives
   them. *)
type frame = {
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
  (* the bytes [fd] may hold: [worker_file_cap ()] *)
  mutable size : int;
  (* the bytes written to [fd] so far *)
}

(* The main process, from [start] to [collect]. *)
type main = {
  cap : int;
  (* the bytes [segments] may take: [buffer_cap ()] *)
  mutable segments : Bytes.t list;
  (* the copies of the files of the workers, the latest first *)
  mutable size : int;
  (* the bytes of [segments] *)
  mutable deferred : (Constant.t * Opaqueproof.opaque) list;
  (* the constant and the opaque value of each deferred check, the latest
     first: the check numbered [n] is the one deferred after [n] others *)
  mutable count : int;
  (* the length of [deferred] *)
}

(* What this process does with the records:
   - [Off]: nothing, in a process where [start] did not run or found no
     workers, in a worker that has no file or stopped recording, and once
     [collect] decoded the records ([None]); or since [start] stepped
     aside, for the reason given;
   - [Recording]: the main process, from [start] to [collect];
   - [Gave_up]: the main process, once it gave up, for the reason given:
     no record is used, nothing more is recorded, and what it kept is
     dropped;
   - [Worker]: a worker that records to its file.
   A worker's checks were deferred before it was forked, so their numbers
   name in the main process the constants and values they name in the
   worker. The reasons are the tokens of [status_line], which
   coq-commands.rst lists. Each [Gave_up] is a constant, so that giving up
   allocates nothing, and can follow any failure. *)
type mode =
  | Off of string option
  | Recording of main
  | Gave_up of string
  | Worker of output

let mode = ref (Off None)

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

exception Buffer_full

(* Copies the file [fd] of a worker, whole, into [m] as one segment. An
   empty file adds nothing. Raises [Buffer_full], keeping nothing, if the
   file would take [m] past its cap, which is checked before the copy is
   allocated. *)
let copy_file m fd =
  let size = Unix.lseek fd 0 Unix.SEEK_END in
  if size > 0 then begin
    if m.size + size > m.cap then raise Buffer_full;
    ignore (Unix.lseek fd 0 Unix.SEEK_SET);
    let seg = Bytes.create size in
    read_all fd seg 0 size;
    m.segments <- seg :: m.segments;
    m.size <- m.size + size
  end

(** {6 Recording} *)

(* The frame of the record of check [index], whose body names the objects
   [objs], in the numbering [n]: the objects [n] has no number for yet
   take the next ones, in the order of [objs]. *)
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
  let ids = CArray.map_of_list number objs in
  Marshal.to_bytes { index; defs = CArray.rev_of_list !defs; ids } []

(* The second stage, in whichever process checked the body [c] of check
   [index], in [env]: a worker with a file records it there, and any other
   process, the main one included, does nothing. Any failure stops the
   recording in that worker only, and so does a frame that would take its
   file past its cap; a write that fails empties the file first
   ([empty_file]), and the report then reads the bodies that worker
   checked. A body that names an object whose names are not finite
   ([Check_closure.opaque_body_refs] gives [None]) is not recorded, and
   none of its objects is numbered: the report reads that body, and the
   worker goes on recording the next ones. *)
let record index env c =
  match !mode with
  | Worker o ->
    (try
       match Check_closure.opaque_body_refs env c with
       | None -> ()
       | Some objs ->
         let frame = make_frame o.numbering index objs in
         let size = Bytes.length frame in
         if o.size + size > o.max_size then mode := Off None
         else begin
           (try write_all o.fd frame 0 size with
            | Sys.Break as e -> raise e
            | e -> empty_file o.fd; raise e);
           o.size <- o.size + size
         end
     with
     | Sys.Break as e -> raise e
     | _ -> mode := Off None)
  | Off _ | Recording _ | Gave_up _ -> ()

(* The second stage of a check that is not recorded. *)
let unrecorded _ _ = ()

(* The first stage, in the main process. Every opaque is recorded, with
   substitutions or without: the key alone, the name of the constant and
   the very value, decides which record the report uses. If anything fails
   here, or once the deferred checks would pass [deferred_cap], the main
   process gives up, and the check runs with no second stage. *)
let deferring kn o =
  match !mode with
  | Recording m ->
    let n = m.count in
    if n >= deferred_cap then (mode := Gave_up "deferred cap"; unrecorded)
    else
      (try
         m.deferred <- (kn, o) :: m.deferred;
         m.count <- n + 1;
         record n
       with
       | Sys.Break as e -> raise e
       | _ -> mode := Gave_up "defer failure"; unrecorded)
  | Off _ | Gave_up _ | Worker _ -> unrecorded

(** {6 The files of the workers}

    None of these raises anything but an interrupt, as
    [CheckWorkers.set_worker_file] asks. *)

(* The directory of the workers' files: a file system in memory, on which
   [start] records only where rocqchk writes nothing else there. *)
let records_dir = "/dev/shm"

(* In the main process, before each fork: a file for the worker, or none
   once the main process gave up. A file that cannot be made gives up for
   the whole run, as the other failures do: had the main process gone on
   without it, nothing else would end the recording where no file can be
   made at all, as in a /dev/shm whose room or inodes are used up, and the
   deferred checks would grow while no record is made. So does a file that
   can be made but not removed, which [CheckWorkers.open_unnamed] closes
   and does not give: going on would leave a named file in /dev/shm for
   each worker. *)
let open_file () =
  match !mode with
  | Recording _ ->
    (match CheckWorkers.open_unnamed ~temp_dir:records_dir with
     | Some _ as file -> file
     | None -> mode := Gave_up "file failure"; None
     | exception (Sys.Break as e) -> mode := Gave_up "file failure"; raise e
     | exception _ -> mode := Gave_up "file failure"; None)
  | Off _ | Gave_up _ | Worker _ -> None

(* In a worker, right after the fork: what the main process keeps is not
   its own, and it records to its own file, if it has one, with a numbering
   of its own. *)
let in_child fd =
  mode :=
    (match fd with
     | Some fd ->
       Worker { fd; numbering = numbering (); max_size = worker_file_cap (); size = 0 }
     | None -> Off None)

(* In the main process, once the worker whose file is [fd] has ended
   successfully: the file is copied ([copy_file]), and closed at once,
   whatever happens. Any failure but an interrupt gives up. *)
let done_ok fd =
  match !mode with
  | Recording m ->
    (match copy_file m fd with
     | () -> CheckWorkers.close_fd fd
     | exception Buffer_full ->
       mode :=
         (if m.cap < default_buffer_cap then Gave_up "buffer cap (test)"
          else Gave_up "buffer cap");
       CheckWorkers.close_fd fd
     | exception (Sys.Break as e) ->
       mode := Gave_up "copy failure"; CheckWorkers.close_fd fd; raise e
     | exception _ -> mode := Gave_up "copy failure"; CheckWorkers.close_fd fd)
  | Off _ | Gave_up _ | Worker _ -> CheckWorkers.close_fd fd

(** {6 Starting} *)

(* Raised where [start] steps aside, with the reason. *)
exception Step_aside of string

(* [f ()], or a step aside for [reason] where it fails but for an
   interrupt, or for want of memory or stack, which [start] takes as a
   failure of its own. *)
let or_step_aside reason f =
  try f () with
  | (Sys.Break | Out_of_memory | Stack_overflow) as e -> raise e
  | _ -> raise (Step_aside reason)

(* The words of the first line of [file] that starts with [prefix], after
   that prefix, split at spaces and tabs. Fails if the file cannot be read,
   or holds no such line. *)
let proc_words file ~prefix =
  let ch = open_in file in
  let line =
    Fun.protect ~finally:(fun () -> close_in_noerr ch) (fun () ->
        let rec find () =
          let line = input_line ch in
          if String.starts_with ~prefix line then line else find ()
        in
        find ())
  in
  let rest = String.sub line (String.length prefix) (String.length line - String.length prefix) in
  let words = String.split_on_char ' ' (String.map (fun c -> if Char.equal c '\t' then ' ' else c) rest) in
  List.filter (fun s -> not (String.equal s "")) words

(* The soft limit on the descriptors of this process (RLIMIT_NOFILE,
   [ulimit -n]): the first number of the line "Max open files" of
   /proc/self/limits, [max_int] where it says "unlimited". *)
let open_files_limit () =
  match proc_words "/proc/self/limits" ~prefix:"Max open files" with
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
   process may create files in, and in which no other user can remove and
   replace a file of the records between its creation and its opening
   ([CheckWorkers.open_unnamed]), and then see or change what a worker
   records: one that users other than its owner may write to must have the
   sticky bit. *)
let records_device () =
  let st = or_step_aside "no /dev/shm" (fun () -> Unix.stat records_dir) in
  if st.Unix.st_kind <> Unix.S_DIR then raise (Step_aside "no /dev/shm");
  let perm = st.Unix.st_perm in
  if perm land 0o022 <> 0 && perm land 0o1000 = 0 then
    raise (Step_aside "/dev/shm writable by others");
  or_step_aside "/dev/shm not writable" (fun () ->
      Unix.access records_dir [Unix.W_OK; Unix.X_OK]);
  st.Unix.st_dev

(* Whether the directory in which the files of the workers' output are made
   ([CheckWorkers.capture_dir]) is on the file system [dev]. A directory
   that cannot be looked at is one in which no file can be made either, and
   so on none. *)
let temp_dir_on dev =
  match Unix.stat (CheckWorkers.capture_dir ()) with
  | st -> st.Unix.st_dev = dev
  | exception Unix.Unix_error _ -> false

(* Whether the system's table of open files has room for [need] more, by
   /proc/sys/fs/file-nr ("allocated unused max"): its size less the files
   open in it, read unsigned, as the size may be LONG_MAX, which is past
   [max_int]. The limit of this process does not count the files of other
   processes: in a system whose table is nearly full, the files of the
   records could take the last places, and a later open that rocqchk needs,
   of a library say, would fail where it succeeds without records. Fails
   where the file cannot be read or parsed: without it, as where a sandbox
   hides it, the room cannot be known. *)
let file_table_room need =
  let number s =
    if String.equal s "" || not (String.for_all (fun c -> '0' <= c && c <= '9') s)
    then failwith "ReportRecords.file_table_room";
    Int64.of_string ("0u" ^ s)
  in
  match proc_words "/proc/sys/fs/file-nr" ~prefix:"" with
  | [allocated; _; size] ->
    let allocated = number allocated and size = number size in
    Int64.unsigned_compare allocated size <= 0
    && Int64.unsigned_compare (Int64.sub size allocated) (Int64.of_int need) >= 0
  | _ -> failwith "ReportRecords.file_table_room"

(* FD_SETSIZE on Linux: [Unix.select] refuses a descriptor numbered at or
   above it, and [CheckWorkers.wait_for_messages] selects on the report
   pipes of the workers, which then waits worse. The descriptor that the
   records add for each worker must not take a report pipe there where,
   without records, the pipes stay below it. *)
let fd_setsize = 1024

(* Steps aside unless the files that the workers may need with their files
   of records fit: the descriptors of this process
   ([CheckWorkers.descriptors_for_workers]) below the soft limit on open
   files less the [held] descriptors this process already holds, and all of
   them numbered below [fd_setsize], as descriptors take the lowest free
   numbers; and the open files of this process and of its workers
   ([CheckWorkers.open_files_for_workers]) in the system's table of open
   files ([file_table_room]). The two counts differ: a file that a worker
   opens itself, as a library's while it reads its table, takes a place in
   the system's table and no descriptor of this process. The descriptors
   held already, those inherited and those rocqchk opened before the
   libraries are loaded, are not free for any of these. Under less room, a
   descriptor or an open file the records took could be the one a later
   pipe, file of output or library load needs, in this process or in a
   worker, which would then fail where it succeeds without records. *)
let room_for_files held =
  let need = CheckWorkers.descriptors_for_workers () in
  let limit = or_step_aside "no /proc/self/limits" open_files_limit in
  if limit - held < need then raise (Step_aside "no room for descriptors");
  if held + need > fd_setsize then raise (Step_aside "FD_SETSIZE");
  let room = or_step_aside "no file-nr" (fun () ->
      file_table_room (CheckWorkers.open_files_for_workers ()))
  in
  if not room then raise (Step_aside "no room in file table")

(* The recorder, where each condition that [start] checks holds, or a step
   aside for the first that does not. [records_dir] must be on another file
   system than every file rocqchk writes without records, so that the
   records cannot take the room one of those writes needs, and a full
   /dev/shm only stops recording: that of the directory of the workers'
   output, and that of each descriptor this process holds, such as its
   standard output and error (those are all the files rocqchk writes, but
   for those of the test seams and of -compare, with which nothing is
   recorded). Opens nothing but the directory /proc/self/fd and the files
   /proc/self/limits and /proc/sys/fs/file-nr, each closed at once. *)
let recording () =
  let dev = records_device () in
  let held, held_on_dev = or_step_aside "no /proc/self/fd" (fun () -> open_descriptors dev) in
  if held_on_dev then raise (Step_aside "descriptor on /dev/shm");
  if temp_dir_on dev then raise (Step_aside "TMPDIR on /dev/shm");
  room_for_files held;
  Check_closure.prepare_opaque_body_refs ();
  CheckWorkers.set_worker_file { CheckWorkers.open_file; in_child; done_ok };
  Recording { cap = buffer_cap (); segments = []; size = 0; deferred = []; count = 0 }

(* Nothing is recorded without workers. Nor with -compare: the comparison,
   which comes after the report, reads opaque bodies through the same
   accessor ([CheckLibrary.indirect_accessor]), which keeps each table it
   reads in the main process; a body the report took from a record would
   leave its table unread there, so that the comparison could read the
   library file again where, without records, it uses the table the report
   read. Nor with -merge-inductives or -merge-inductives-verbose
   ([Indmerge.enabled]): after a merge, the opaque values of the final
   environment are new values, which no record would match. *)
let start ~compare =
  if CheckWorkers.parallel () then begin
    let m =
      if compare then Off (Some "compare")
      else if Indmerge.enabled () then Off (Some "merge-inductives")
      else
        try recording () with
        | Sys.Break as e -> raise e
        | Step_aside reason -> Off (Some reason)
        | _ -> Off (Some "start failed")
    in
    mode := m
  end

(** {6 After the run} *)

(* The one copy of [obj] that [shared] keeps, so that the records keep one
   copy of each object they name, and two records of one value compare
   physically ([same_objects]). *)
let share shared obj =
  match RefMap.find_opt obj !shared with
  | Some obj -> obj
  | None -> shared := RefMap.add obj obj !shared; obj

exception Too_many_ids

(* The frame at [ofs] in the segment [seg], and its size, where a whole one
   is there. *)
let next_frame seg ofs =
  let left = Bytes.length seg - ofs in
  if left < Marshal.header_size then None
  else
    match Marshal.total_size seg ofs with
    | exception (Failure _ | Invalid_argument _) -> None
    | size when size > left -> None
    | size ->
      match (Marshal.from_bytes seg ofs : frame) with
      | exception (Failure _ | Invalid_argument _) -> None
      | r -> Some (r, size)

(* The records of the segment [seg], in order, for the constants and opaque
   values [values] of the checks, by number. A frame cut short, or one
   whose record or numbers are wrong, ends the segment: what follows it
   cannot be told apart from what it holds. So does a frame that names
   first an object whose names are not finite ([CheckNames.finite_names]),
   which is checked for each such object before any of them is kept or
   compared ([share]); the objects it names by number were checked with
   the frame that named them first. The records read before it are whole,
   and kept. [decoded] counts the numbers of objects decoded so far, in all
   the segments: one that would take it past [id_cap] raises
   [Too_many_ids]. *)
let read_segment records values shared decoded seg =
  let objects = ref [||] and known = ref 0 in
  let add (r : frame) =
    let n = Array.length r.defs in
    if n > 0 then begin
      if !known + n > Array.length !objects then begin
        let a = Array.make (max 1024 (2 * (!known + n))) r.defs.(0) in
        Array.blit !objects 0 a 0 !known;
        objects := a
      end;
      Array.iteri (fun j obj -> (!objects).(!known + j) <- share shared obj) r.defs;
      known := !known + n
    end;
    if r.index < 0 || r.index >= Array.length values
       || Array.exists (fun k -> k < 0 || k >= !known) r.ids
    then false
    else begin
      let count = !decoded + Array.length r.ids in
      if count > id_cap then raise Too_many_ids;
      decoded := count;
      let kn, value = values.(r.index) in
      add_record records kn { value; objects; ids = r.ids };
      true
    end
  in
  let rec frames ofs =
    match next_frame seg ofs with
    | Some (r, size) when Array.for_all CheckNames.finite_names r.defs && add r ->
      frames (ofs + size)
    | Some _ | None -> ()
  in
  frames 0

(* The records of the segments of [m], in order: none if no worker left
   any. *)
let read_records m =
  let records = no_records () in
  if not (CList.is_empty m.segments) then begin
    let values = CArray.rev_of_list m.deferred
    and shared = ref RefMap.empty and decoded = ref 0 in
    List.iter (read_segment records values shared decoded) (List.rev m.segments)
  end;
  records

let collect () =
  match !mode with
  | Off _ | Worker _ -> None
  | Gave_up _ -> Some (no_records ())
  | Recording m ->
    mode := Off None;
    try Some (read_records m) with
    | Sys.Break as e -> raise e
    | Too_many_ids -> mode := Gave_up "id cap"; Some (no_records ())
    | _ -> mode := Gave_up "read failure"; Some (no_records ())

let status_line () =
  match !mode with
  | Off (Some reason) -> Some ("rocqchk: statement report: records off: " ^ reason)
  | Gave_up reason -> Some ("rocqchk: statement report: records given up: " ^ reason)
  | Off None | Recording _ | Worker _ -> None

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
