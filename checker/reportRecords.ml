(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** With workers, the statement report used to spend nearly all its time on
    the opaque bodies it reaches: the main process read each one from its
    library's table, cooked it and walked it, one after the other, once the
    workers had checked them all. On r188 that report took 387 s; taking the
    objects of each body from what the process that checked it recorded, it
    took 7 s, with the same lines (dispatch://BET-1213).

    The recorder is the hook of [Mod_checking], in two stages. When the main
    process defers the check of an opaque body, it gives the check a number,
    the index of the opaque value in [deferred]. When the check has passed,
    the process that ran it writes the record of that number: the objects
    [Check_closure.opaque_body_refs] finds in the body it checked. After the
    run, the main process maps each number back to its opaque value, and the
    report uses a record only for that very value ([Check_closure], where
    the reason a weaker key would not do is given). A record that is
    missing, because a process could not write it or the main process could
    not read it, only makes the report read that body.

    Nothing here prints anything, except the debug line of [print_counts],
    and nothing here can fail a check or the run: the hook raises nothing
    but an interrupt, and every failure falls back to reading the body. *)

open Names

(** {6 The directory} *)

(* The directory, and the process that made it: the only one that numbers
   deferred checks, reads the records and removes the directory. A worker
   inherits this, but leaves through [Unix._exit], which runs no [at_exit]
   function, and it is checked anyway. *)
type dir = { path : string; owner : int }

let dir : dir option ref = ref None

(* A fresh directory, named after this process with a random part, that
   only this user can enter, or [None]. [Unix.mkdir] fails on a name that
   exists, whatever it is, so the directory is the one made here. *)
let make_dir () =
  let owner = Unix.getpid () in
  let rng = Random.State.make_self_init () in
  let rec attempt n =
    if Int.equal n 0 then None
    else
      let path = Filename.concat (Filename.get_temp_dir_name ())
          (Printf.sprintf "rocqchk_refs_%d_%08x" owner (Random.State.bits rng)) in
      match Unix.mkdir path 0o700 with
      | () -> Some { path; owner }
      | exception Unix.Unix_error (Unix.EEXIST, _, _) -> attempt (n - 1)
      | exception Unix.Unix_error _ -> None
  in
  attempt 10

(** {6 The checks the main process deferred} *)

(* The opaque value of each deferred check whose record is asked for, at
   the number its record carries. Only the main process fills it, while it
   checks the libraries. A worker's checks were deferred before it was
   forked, so their numbers are below the count it inherited, and they name
   in the main process the values they name in the worker. *)
let deferred : Opaqueproof.opaque array ref = ref [||]
let deferred_count = ref 0

let number_deferred o =
  let n = !deferred_count in
  if Int.equal n (Array.length !deferred) then begin
    let a = Array.make (max 1024 (2 * n)) o in
    Array.blit !deferred 0 a 0 n;
    deferred := a
  end;
  (!deferred).(n) <- o;
  deferred_count := n + 1;
  n

(** {6 Records} *)

(* A record. [index] is the number of its check ([number_deferred]). Each
   process numbers the objects it records, 0, 1, ... in the order it first
   records them: [defs] are the objects this record names first, which
   take the next numbers in order, and [ids] are the objects of the body,
   by number, in the order [Check_closure.opaque_body_refs] gives them.
   [fresh] marks the first record a process writes, where the numbering
   starts again: a process can append to the file of an earlier one that
   had the same pid. *)
type record = {
  fresh : bool;
  index : int;
  defs : GlobRef.t array;
  ids : int array;
}

(* On disk, a record is a frame: the length of the marshalled record, on 8
   bytes, big-endian, its MD5 digest, on 16 bytes, then the marshalled
   bytes. The digest makes a frame that was cut short detectable even when
   more bytes follow it: a process whose write failed records nothing more,
   but a later process with the same pid appends to its file, and
   [input_value] checks the header of what it reads, not its data, so it
   would read the end of the frame and the start of the next one as a
   record. *)
let header_size = 24

(* An object keeps one number in its process: two objects equal in this
   table are the same object. *)
module RefTbl = Check_closure.RefTbl

(* The file this process writes its records to, with its numbering of
   objects and the pid they belong to: a worker inherits the main
   process's, if the main process has one, and makes its own. A raw
   descriptor, to which each record goes whole as soon as it is made, so
   that nothing waits in a buffer: a worker leaves through [Unix._exit],
   which flushes nothing. Opened to append, so that a process that gets the
   pid of one that has exited adds to its file instead of emptying it. *)
type output = {
  pid : int;
  fd : Unix.file_descr;
  numbers : int RefTbl.t;
  (* the number of each object recorded so far *)
  mutable next : int;
  (* the number the next new object takes *)
  mutable first : bool;
  (* whether no record has been written yet *)
}

let output : output option ref = ref None

(* The pid of a process whose recording failed: it records nothing more,
   and the report reads the bodies it checked. *)
let stopped : int option ref = ref None

let rec write_all fd b ofs len =
  if len > 0 then
    match Unix.single_write fd b ofs len with
    | 0 -> failwith "ReportRecords.write_all"
    | n -> write_all fd b (ofs + n) (len - n)
    | exception Unix.Unix_error (Unix.EINTR, _, _) -> write_all fd b ofs len

let open_output path pid =
  let file = Filename.concat path (string_of_int pid ^ ".crefs") in
  let fd = Unix.openfile file
      [Unix.O_WRONLY; Unix.O_CREAT; Unix.O_APPEND; Unix.O_CLOEXEC] 0o600 in
  let o = { pid; fd; numbers = RefTbl.create 1024; next = 0; first = true } in
  output := Some o;
  o

(* The second stage of the hook, in whichever process checked the body [c]
   of check [index], in [env]. It raises nothing but an interrupt, which is
   the user's: any failure stops the recording in this process only. *)
let record path index env c =
  let pid = Unix.getpid () in
  let stopped_here = match !stopped with Some p -> Int.equal p pid | None -> false in
  if not stopped_here then
    try
      let o = match !output with
        | Some o when Int.equal o.pid pid -> o
        | Some _ | None -> open_output path pid
      in
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
      let r = { fresh = o.first; index; defs = Array.of_list (List.rev !defs); ids } in
      let payload = Marshal.to_bytes r [] in
      let n = Bytes.length payload in
      let frame = Bytes.create (header_size + n) in
      Bytes.set_int64_be frame 0 (Int64.of_int n);
      Bytes.blit_string (Digest.bytes payload) 0 frame 8 16;
      Bytes.blit payload 0 frame header_size n;
      write_all o.fd frame 0 (Bytes.length frame);
      o.first <- false
    with
    | Sys.Break as e -> raise e
    | _ -> stopped := Some pid

let no_record _ _ = ()

(* The first stage of the hook, in the process that defers the check of
   the opaque [o]: the main process numbers the check, and the second stage
   carries the number. Only an opaque with no substitution is recorded, as
   in the measured design: one with substitutions is a copy that a functor
   application, an [Include] or a signature made, and the report reads its
   body as it does without records. A check deferred anywhere but in the
   main process, which none is, would get a number that names another value
   there, so it is not recorded. On any failure, the check is not
   recorded. *)
let deferring d _kn o =
  try
    let (sub, _, _, _) = Opaqueproof.repr o in
    if CList.is_empty sub && Int.equal (Unix.getpid ()) d.owner then
      record d.path (number_deferred o)
    else no_record
  with
  | Sys.Break as e -> raise e
  | _ -> no_record

(** {6 The main process, around the run} *)

let close_own_output () =
  match !output with
  | Some o when Int.equal o.pid (Unix.getpid ()) ->
    output := None;
    (try Unix.close o.fd with Unix.Unix_error _ -> ())
  | Some _ | None -> ()

(* Once the records are read, and at exit, through [exit] or an uncaught
   exception (a signal that kills the process leaves the directory): by
   then every worker has finished, or been killed and reaped
   ([CheckWorkers.abort]), so no process writes to the directory any more.
   Only the main process acts. *)
let remove_dir () =
  match !dir with
  | Some d when Int.equal (Unix.getpid ()) d.owner ->
    dir := None;
    close_own_output ();
    let files = try Sys.readdir d.path with Sys_error _ -> [||] in
    Array.iter (fun f -> try Sys.remove (Filename.concat d.path f) with Sys_error _ -> ()) files;
    (try Unix.rmdir d.path with Unix.Unix_error _ -> ())
  | Some _ | None -> ()

let start () =
  match make_dir () with
  | None -> ()
  | Some d ->
    dir := Some d;
    at_exit remove_dir;
    Mod_checking.set_opaque_check_hook (deferring d)

(* The records of one file, in order. A frame cut short, or one whose
   digest, record or numbers are wrong, ends the file: what follows it
   cannot be told apart from what it holds. The records read before it
   are whole, and kept. *)
let read_file records path =
  let ic = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in_noerr ic) @@ fun () ->
  let length = in_channel_length ic in
  let header = Bytes.create header_size in
  let objects = ref [||] and known = ref 0 in
  let add (r : record) =
    if r.fresh then known := 0;
    let n = Array.length r.defs in
    if n > 0 then begin
      if !known + n > Array.length !objects then begin
        let a = Array.make (max 1024 (2 * (!known + n))) r.defs.(0) in
        Array.blit !objects 0 a 0 !known;
        objects := a
      end;
      Array.blit r.defs 0 !objects !known n;
      known := !known + n
    end;
    if r.index < 0 || r.index >= !deferred_count
       || Array.exists (fun k -> k < 0 || k >= !known) r.ids
    then false
    else begin
      let objs = Array.fold_right (fun k objs -> (!objects).(k) :: objs) r.ids [] in
      Check_closure.add_opaque_record records (!deferred).(r.index) objs;
      true
    end
  in
  let rec loop () =
    match really_input ic header 0 header_size with
    | exception End_of_file -> ()
    | () ->
      let size = Bytes.get_int64_be header 0 in
      if Int64.compare size 0L > 0
      && Int64.compare size (Int64.of_int (length - pos_in ic)) <= 0 then begin
        let payload = Bytes.create (Int64.to_int size) in
        match really_input ic payload 0 (Int64.to_int size) with
        | exception End_of_file -> ()
        | () ->
          if String.equal (Bytes.sub_string header 8 16) (Digest.bytes payload) then
            match (Marshal.from_bytes payload 0 : record) with
            | r -> if add r then loop ()
            | exception (Failure _ | Invalid_argument _) -> ()
      end
  in
  loop ()

(* A file that cannot be opened or read gives the records read before the
   error. *)
let read_records d =
  let records = Check_closure.opaque_records () in
  Array.iter (fun f ->
      if Filename.check_suffix f ".crefs" then
        try read_file records (Filename.concat d.path f) with Sys_error _ -> ())
    (Sys.readdir d.path);
  records

let collect () =
  match !dir with
  | None -> None
  | Some d ->
    Mod_checking.set_opaque_check_hook (fun _ _ _ _ -> ());
    close_own_output ();
    let records =
      try read_records d
      with
      | Sys.Break as e -> raise e
      | _ -> Check_closure.opaque_records ()
    in
    remove_dir ();
    deferred := [||];
    deferred_count := 0;
    Some records

(* The line CDebug prints for the flag checker-workers, whose printer
   [CheckWorkers] keeps to itself. *)
let print_counts records =
  if CheckWorkers.debugging () then begin
    let hits, reads = Check_closure.opaque_record_counts records in
    Feedback.msg_debug
      Pp.(hv 2 (str "[checker-workers]" ++ spc () ++
                str "statement report: " ++ int hits ++
                str " opaque bodies from records, " ++ int reads ++ str " read"))
  end
