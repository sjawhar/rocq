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
    them all. Instead, the process that checked a body records the objects
    the report's walk finds in it, and the report takes them from the
    record: those walks are made by the workers, side by side.

    The recorder is the hook of [Mod_checking], in two stages. When the main
    process defers the check of an opaque body, it gives the check a number,
    the index of the opaque value in [deferred]. When the check has passed,
    the process that ran it writes the record of that number to its file:
    the objects [Check_closure.opaque_body_refs] finds in the body it
    checked. After the run, the main process maps each number back to its
    opaque value, and the report uses a record only for that very value. A
    record that is missing, because a process could not write it or the
    main process could not read it, only makes the report read that body.

    Nothing here prints anything, except the debug line of [print_counts],
    and nothing here can fail a check or the run: the hook raises nothing
    but an interrupt, and every failure falls back to reading the body. The
    records take bounded room ([file_cap], [spool_cap], [id_cap]), and a
    write of a record past the limit on the size of a file fails instead
    of killing the process ([write_all]). *)

open Names

(** {6 The records}

    A record is keyed by the opaque value itself, the one whose check the
    main process deferred and still holds, and the report uses it only for
    that very value. The body of an opaque value, the one the report reads,
    is a function of the value and of its library's table
    ([CheckLibrary.indirect_accessor]: the stored proof, cooked by the
    value's cooking information, then substituted by its substitutions), and
    the table is the library's file as the main process hashed it, which
    every process that reads it checks. So a record names the objects of
    the body the report would read.

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
    recorded nothing, the record of the other would stand for it. *)

(* Keyed by physical identity, as said above. The hash is the stored
   proof's, which every value of one proof shares. *)
module OpaqueTbl = Hashtbl.Make (struct
    type t = Opaqueproof.opaque
    let equal = (==)
    let hash o =
      let (_, _, dp, i) = Opaqueproof.repr o in
      Hashset.Combine.combine (DirPath.hash dp) (Opaqueproof.repr_handle i)
  end)

(* Two objects equal here have both their names equal: they are the same
   object, and one can stand for the other anywhere. *)
module RefTbl = Hashtbl.Make (struct
    type t = GlobRef.t
    let equal a b = GlobRef.UserOrd.equal a b && GlobRef.CanOrd.equal a b
    let hash = GlobRef.UserOrd.hash
  end)

type t = {
  bodies : GlobRef.t list option OpaqueTbl.t;
  (* the recorded objects of each opaque value, or [None] when two records
     of it disagree *)
  shared : GlobRef.t RefTbl.t;
  (* one copy of each object the records name *)
  mutable hits : int;
  mutable reads : int;
  (* the opaque constants the report reached whose objects it took from a
     record, and those whose body it read or tried to read *)
}

(* Records that hold nothing yet, with tables made for about [size]
   entries. *)
let make_records size = {
  bodies = OpaqueTbl.create size; shared = RefTbl.create size; hits = 0; reads = 0;
}

(* No record: the report reads every body it reaches. The tables are small,
   so that a failure of [collect], which falls back to this, allocates
   little. *)
let no_records () = make_records 16

(* Each object is kept once, so that the records of a large tree take one
   copy of each name they share: [share r obj] is the copy of [obj] that
   [r] keeps. *)
let share r obj = match RefTbl.find_opt r.shared obj with
  | Some obj -> obj
  | None -> RefTbl.add r.shared obj obj; obj

(* A value can be checked twice: a declaration that a module's signature
   and its implementation share is checked with each. Its records then name
   the same objects. Records of one value that do not are not used, and the
   report reads that body. The objects of [objs] are the copies [share]
   keeps, so that two records of one value compare physically. *)
let add_record r o objs =
  match OpaqueTbl.find_opt r.bodies o with
  | None -> OpaqueTbl.add r.bodies o (Some objs)
  | Some (Some objs') when List.equal (==) objs objs' -> ()
  | Some _ -> OpaqueTbl.replace r.bodies o None

let recorded r o =
  match OpaqueTbl.find_opt r.bodies o with
  | Some (Some objs) -> r.hits <- r.hits + 1; Some objs
  | Some None | None -> r.reads <- r.reads + 1; None

(** {6 The checks the main process deferred} *)

(* The opaque value of each deferred check whose record is asked for, the
   latest first, and their count: the check numbered [n] is the one
   numbered after [n] others. Only the main process defers checks, and so
   fills these, while it checks the libraries. A worker's checks were
   deferred before it was forked, so their numbers are below the count it
   inherited, and they name in the main process the values they name in
   the worker. *)
let deferred : Opaqueproof.opaque list ref = ref []
let deferred_count = ref 0

(** {6 The files}

    Every file here is unnamed ([CheckWorkers.open_capture]: created in the
    temporary directory, opened, and removed at once, as the files of the
    workers' output are). It lives while a process holds it open, and the
    system frees it with its last descriptor, at the latest when the last
    process that holds it exits: so nothing is left on disk, however the
    run ends (but for a kill in the instant between the creation of a file
    and its removal), and no other process can open it.

    Each process records to a file of its own: the main process to [own],
    for the checks it runs itself (those of a batch it could not fork), and
    each worker that checks opaque bodies to the file [CheckWorkers] opened
    for it before the fork ([CheckWorkers.set_worker_file]). A file is a
    sequence of frames, each one marshalled [record], whose own header
    gives its size ([Marshal.total_size]). One process writes the file,
    from its start, and records nothing more after its first failure, nor
    once a frame would take the file past [file_cap], so only the last
    frame of a file can be cut short.

    When a worker has ended successfully, the main process copies its file
    to [spool] as one segment, and closes it: the length of the file on 8
    bytes, big-endian, then its bytes. So the main process holds two files
    whatever the number of workers, and the records of a worker that
    failed, whose checks do not count, never reach the spool. Once a
    segment would take the spool past [spool_cap], or a write to it fails,
    the main process gives up: no record is used. *)

(* The room the records take on disk, and so the bytes the main process
   reads and decodes. What the report reads does not bound it: [n] opaque
   constants can share one stored proof that names [k] objects, and the
   check of each of them records the [k] objects, so that the records hold
   [n * k] numbers, while the report walks only the bodies it reaches. So
   a process stops recording once its file would pass [file_cap], and the
   main process gives up once the spool would pass [spool_cap]: the report
   then reads every body, as it does without records. [file_cap] bounds a
   worker's file while the worker runs, before the main process sees it,
   and the one segment the main process reads into memory at a time. On a
   tree of 4,190 libraries the whole spool took 48 MB, so 256 MiB in all
   and 64 MiB per file leave a wide margin above it. What the decoding
   keeps in memory is bounded apart ([id_cap]). *)
let file_cap = 64 * 1024 * 1024
let default_spool_cap = 256 * 1024 * 1024

(* Test-only seam, in the style of [Check_closure]'s: a number of bytes in
   COQ_TEST_SUITE_STATEMENT_REPORT_RECORDS_CAP lowers the cap of the spool,
   so that a test can make the main process give up. *)
let spool_cap () =
  match Option.bind (Sys.getenv_opt "COQ_TEST_SUITE_STATEMENT_REPORT_RECORDS_CAP")
          int_of_string_opt with
  | Some n when n >= 0 -> min n default_spool_cap
  | Some _ | None -> default_spool_cap

(* The numbers of objects that the main process decodes, in all the
   segments, may be at most [id_cap] ([read_segment]). Each becomes a cell
   of a list that the records keep, three words, and [spool_cap] bounds
   them poorly: a number below 64 takes one byte in a frame, so a spool of
   256 MiB can hold 256 Mi numbers, 6 GiB of cells. The objects themselves
   are kept once each ([share]), so the objects that exist bound them.
   Past [id_cap], 32 Mi numbers, about 768 MiB of cells on a 64-bit
   machine, the main process gives up, and the report reads every body.
   The 48 MB spool of the tree of 4,190 libraries held far fewer, by an
   estimate from the frame format, not a count: a frame takes about 30
   bytes besides its numbers (the marshal header of 20 bytes, the number
   of the check, the headers of its arrays) and the objects it names
   first, tens of bytes each; a number takes 1 byte below 64, 2 below 128,
   3 below 32,768, and a worker numbers thousands of objects. If half of
   that spool is numbers, at about 2 bytes each, it holds some 12 million;
   it would pass the cap only if some 70% of it were numbers of 1 byte. *)
let id_cap = 32 * 1024 * 1024

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

(* The file this process records to, with its numbering of objects. A raw
   descriptor, to which each record goes whole as soon as it is made, so
   that nothing waits in a buffer: a worker leaves through [Unix._exit],
   which flushes nothing. *)
type output = {
  fd : Unix.file_descr;
  numbers : int RefTbl.t;
  (* the number of each object recorded so far *)
  mutable next : int;
  (* the number the next new object takes *)
  mutable size : int;
  (* the bytes written to [fd] so far *)
}

let output fd = { fd; numbers = RefTbl.create 1024; next = 0; size = 0 }

(* [None] where this process records nothing: before [start], after
   [collect], in a worker without a file, once a write failed, and once
   the file would have passed [file_cap]. *)
let current : output option ref = ref None

(* The main process's files, from [start] to [collect]. *)
type files = {
  spool : Unix.file_descr;
  own : Unix.file_descr;
  cap : int;
  (* the bytes the spool may take: [spool_cap ()] *)
  mutable spooled : int;
  (* the bytes of the segments appended to [spool] so far *)
  mutable spool_whole : bool;
  (* false once a write to [spool] failed, or a segment would have taken
     it past [cap]: a segment may then be cut short, and no record is
     used *)
}

let files : files option ref = ref None

(* Every write of the records, and only those, is made with SIGXFSZ
   ignored, and the action it had is restored after. A write past the
   limit on the size of a file (RLIMIT_FSIZE, [ulimit -f]) then fails with
   EFBIG, which the caller takes as a failure of the recording, instead of
   raising that signal, whose default action kills the process: without
   records, rocqchk writes none of these files, and a limit that they meet
   must not end a run it would finish. If the action cannot be set, nothing
   is written, and that is a failure of the recording too. Every other
   write, such as the output of a worker, keeps the action it has. *)
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

let rec read_all fd b ofs len =
  if len > 0 then
    match Unix.read fd b ofs len with
    | 0 -> failwith "ReportRecords.read_all"
    | n -> read_all fd b (ofs + n) (len - n)
    | exception Unix.Unix_error (Unix.EINTR, _, _) -> read_all fd b ofs len

let segment_header = 8

let copy_buffer = lazy (Bytes.create 65536)

(* Appends the file [fd], whole, to the spool of [f] as one segment. An
   empty file adds nothing. Fails, writing nothing, if the segment would
   take the spool past its cap. *)
let append_segment f fd =
  let size = Unix.lseek fd 0 Unix.SEEK_END in
  if size > 0 then begin
    let spooled = f.spooled + segment_header + size in
    if spooled > f.cap then failwith "ReportRecords.append_segment";
    ignore (Unix.lseek fd 0 Unix.SEEK_SET);
    let header = Bytes.create segment_header in
    Bytes.set_int64_be header 0 (Int64.of_int size);
    write_all f.spool header 0 segment_header;
    let b = Lazy.force copy_buffer in
    let rec copy left =
      if left > 0 then begin
        let n = min left (Bytes.length b) in
        read_all fd b 0 n;
        write_all f.spool b 0 n;
        copy (left - n)
      end
    in
    copy size;
    f.spooled <- spooled
  end

(** {6 Recording} *)

(* The second stage of the hook, in whichever process checked the body [c]
   of check [index], in [env]. It raises nothing but an interrupt, which is
   the user's: any failure stops the recording in this process only, and
   so does a frame that would take its file past [file_cap]. *)
let record index env c =
  match !current with
  | None -> ()
  | Some o ->
    try
      let objs = Check_closure.opaque_body_refs env c in
      let defs = ref [] in
      let number obj = match RefTbl.find_opt o.numbers obj with
        | Some k -> k
        | None ->
          let k = o.next in
          o.next <- k + 1;
          RefTbl.add o.numbers obj k;
          defs := obj :: !defs;
          k
      in
      let ids = Array.of_list (List.map number objs) in
      let r = { index; defs = Array.of_list (List.rev !defs); ids } in
      let frame = Marshal.to_bytes r [] in
      let size = Bytes.length frame in
      if o.size + size > file_cap then current := None
      else begin
        write_all o.fd frame 0 size;
        o.size <- o.size + size
      end
    with
    | Sys.Break as e -> raise e
    | _ -> current := None

(* The second stage of a check that is not recorded. *)
let no_record _ _ = ()

(* In the main process: nothing more is recorded, and no record is used,
   so that the report reads every body it reaches. Allocates nothing, so
   that it can follow any failure. *)
let give_up () =
  (match !files with Some f -> f.spool_whole <- false | None -> ());
  current := None;
  Mod_checking.reset_opaque_check_hook ()

(* The first stage of the hook, in the process that defers the check of
   the opaque [o], the main process: it numbers the check, and the second
   stage carries the number. Every opaque is recorded, with substitutions
   or without: the physical key alone decides which record the report
   uses. The copies that the report makes itself are read: its
   implementation view substitutes the structure of each module it looks
   into ([Check_closure]'s [fields_of_mp], through
   [Modops.subst_structure]), and a copy made there with a substitution is
   a new value, which no record matches. It runs while the main process
   checks, and raises nothing but an interrupt: if anything fails here,
   the main process gives up, and the check runs with no second stage. *)
let deferring o =
  try
    let n = !deferred_count in
    deferred := o :: !deferred;
    deferred_count := n + 1;
    record n
  with
  | Sys.Break as e -> raise e
  | _ -> give_up (); no_record

(** {6 The files of the workers} *)

(* In the main process, before each fork. *)
let open_file () =
  match !files with
  | Some f when f.spool_whole -> CheckWorkers.open_capture ()
  | Some _ | None -> None

(* In a worker, right after the fork. The main process's files are not its
   to write: it closes its copies of their descriptors, and records to its
   own file, if it has one, with a numbering of its own. *)
let in_child fd =
  current := None;
  (match !files with
   | Some f ->
     files := None; CheckWorkers.close_fd f.spool; CheckWorkers.close_fd f.own
   | None -> ());
  Option.iter (fun fd -> current := Some (output fd)) fd

(* In the main process, once the worker whose file is [fd] has ended
   successfully. *)
let done_ok fd =
  Fun.protect ~finally:(fun () -> CheckWorkers.close_fd fd) (fun () ->
      match !files with
      | Some f when f.spool_whole ->
        (try append_segment f fd with
         | Sys.Break as e -> give_up (); raise e
         | _ -> give_up ())
      | Some _ | None -> ())

(** {6 The main process, around the run} *)

(* If anything fails but an interrupt, nothing is recorded, and the files
   that were opened are closed. *)
let start () =
  match CheckWorkers.open_capture_pair () with
  | exception (Sys.Break as e) -> raise e
  | exception _ -> ()
  | None -> ()
  | Some (spool, own) ->
    try
      let f = { spool; own; cap = spool_cap (); spooled = 0; spool_whole = true } in
      let o = output own in
      let worker_file = { CheckWorkers.open_file; in_child; done_ok } in
      files := Some f;
      current := Some o;
      CheckWorkers.set_worker_file worker_file;
      Mod_checking.set_opaque_check_hook deferring
    with
    | Sys.Break as e -> raise e
    | _ ->
      files := None;
      current := None;
      Mod_checking.reset_opaque_check_hook ();
      CheckWorkers.close_fd spool;
      CheckWorkers.close_fd own

(* The records of one segment, in order, for the opaque values [values] of
   the checks, by number. A frame cut short, or one whose record or numbers
   are wrong, ends the segment: what follows it cannot be told apart from
   what it holds. The records read before it are whole, and kept.
   [decoded] counts the numbers of objects decoded so far, in all the
   segments: one that would take it past [id_cap] raises, and then no
   record is used. *)
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
      add_record records values.(r.index) objs;
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

(* Every segment of the spool, in order. The spool is whole: a segment
   that is not raises, and then no record is used. *)
let read_spool values spool =
  let records = make_records 4096 and decoded = ref 0 in
  let size = Unix.lseek spool 0 Unix.SEEK_END in
  ignore (Unix.lseek spool 0 Unix.SEEK_SET);
  let header = Bytes.create segment_header in
  let rec segments left =
    if left > 0 then begin
      if left < segment_header then failwith "ReportRecords.read_spool";
      read_all spool header 0 segment_header;
      let n = Int64.to_int (Bytes.get_int64_be header 0) in
      if n <= 0 || n > left - segment_header then failwith "ReportRecords.read_spool";
      let b = Bytes.create n in
      read_all spool b 0 n;
      read_segment records values decoded b;
      segments (left - segment_header - n)
    end
  in
  segments size;
  records

(* Everything after the run is inside the handler: any failure but an
   interrupt leaves no record, and the files are closed whatever
   happens. *)
let collect () =
  match !files with
  | None -> None
  | Some f ->
    files := None;
    current := None;
    Mod_checking.reset_opaque_check_hook ();
    let checks = !deferred in
    deferred := [];
    deferred_count := 0;
    Fun.protect ~finally:(fun () ->
        CheckWorkers.close_fd f.spool; CheckWorkers.close_fd f.own) @@ fun () ->
    let records =
      try
        if not f.spool_whole then no_records ()
        else begin
          let values = Array.of_list (List.rev checks) in
          append_segment f f.own;
          read_spool values f.spool
        end
      with
      | Sys.Break as e -> raise e
      | _ -> no_records ()
    in
    Some records

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

let print_counts r =
  CheckWorkers.debug (fun () ->
      Pp.(str "statement report: " ++ int r.hits ++
          str " opaque bodies from records, " ++ int r.reads ++ str " read"));
  test_counts r
