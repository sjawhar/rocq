(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Measurement only. See the interface. *)

type span =
| Load
| Vm_compile
| Cook
| Universes
| Wait
| Check
| Deal
| Output
| Intern
| Statement_report
| Summary
| Validate

(* mainProfile_stubs.c. None allocates. *)
external install_hooks : unit -> unit = "rocqchk_mainprofile_install_hooks" [@@noalloc]
external now_ns : unit -> int = "rocqchk_mainprofile_now_ns" [@@noalloc]
external gc_ns : unit -> int = "rocqchk_mainprofile_gc_ns" [@@noalloc]
external reset_gc_ns : unit -> unit = "rocqchk_mainprofile_reset_gc_ns" [@@noalloc]
external minflt : unit -> int = "rocqchk_mainprofile_minflt" [@@noalloc]
external majflt : unit -> int = "rocqchk_mainprofile_majflt" [@@noalloc]

(* The names of the spans in the trace, by index: 0 is "fork". *)
let names = [|
  "fork"; "load"; "vm_compile"; "cook"; "universes"; "wait"; "check";
  "deal"; "output"; "intern"; "statement_report"; "summary"; "validate";
|]

let fork_index = 0

let index = function
  | Load -> 1
  | Vm_compile -> 2
  | Cook -> 3
  | Universes -> 4
  | Wait -> 5
  | Check -> 6
  | Deal -> 7
  | Output -> 8
  | Intern -> 9
  | Statement_report -> 10
  | Summary -> 11
  | Validate -> 12

(* Absolute, in case the process changes its directory. *)
let path =
  match Sys.getenv_opt "ROCQCHK_MAIN_PROFILE" with
  | None | Some "" -> None
  | Some p ->
    if Filename.is_relative p then
      Some (try Filename.concat (Sys.getcwd ()) p with Sys_error _ -> p)
    else Some p

(* Spans are recorded: only in the main process, while profiling. *)
let enabled = ref false

(* This process is a worker forked while profiling ([in_child]): spans are
   accumulated by kind ([worker_span]), not recorded. *)
let in_worker = ref false

let main_pid = ref 0
let start_ns = ref 0
let child_start_ns = ref 0
let forks = ref 0

(* The events, four ints each: the code (the span's index times 2, plus 1
   for an end), the wall time in ns, the minor faults and the GC time in ns
   so far. Nothing is formatted before the exit. *)
let events : int array ref = ref [||]
let count = ref 0

(* The indices of the spans begun and not ended, innermost last, so that
   the trace closes them at the exit. *)
let stack : int array ref = ref [||]
let depth = ref 0

let grow (a : int array) =
  let b = Array.make (max 16 (2 * Array.length a)) 0 in
  Array.blit a 0 b 0 (Array.length a);
  b

let record code =
  let i = 4 * !count in
  if i + 4 > Array.length !events then events := grow !events;
  let b = !events in
  b.(i) <- code;
  b.(i + 1) <- now_ns ();
  b.(i + 2) <- minflt ();
  b.(i + 3) <- gc_ns ();
  incr count

let enter k =
  let d = !depth in
  if d >= Array.length !stack then stack := grow !stack;
  (!stack).(d) <- k;
  depth := d + 1;
  record (2 * k)

(* Not in a process that became a worker since the span began. *)
let leave k =
  if !enabled then begin
    if !depth > 0 then decr depth;
    record (2 * k + 1)
  end

let span_on k f =
  enter k;
  match f () with
  | v -> leave k; v
  | exception e ->
    let e = Exninfo.capture e in
    leave k;
    Exninfo.iraise e

(* In a worker: for each kind of span, by index, its exclusive wall time and
   GC time, and whether it was entered. The time between two boundaries goes
   to the innermost open span, or to none outside every span. The open spans
   are a fixed stack; a span nested deeper is counted in the deepest one.
   Allocated by [in_child]. *)
let w_ns : int array ref = ref [||]
let w_gc : int array ref = ref [||]
let w_seen : bool array ref = ref [||]
let w_stack : int array ref = ref [||]
let w_depth = ref 0
let w_overflow = ref 0
let w_last_ns = ref 0
let w_last_gc = ref 0

(* The Gc counters when the worker started. *)
let stat0 : Gc.stat option ref = ref None

let w_boundary () =
  let ns = now_ns () in
  let gc = gc_ns () in
  let d = !w_depth in
  if d > 0 then begin
    let k = (!w_stack).(d - 1) in
    (!w_ns).(k) <- (!w_ns).(k) + (ns - !w_last_ns);
    (!w_gc).(k) <- (!w_gc).(k) + (gc - !w_last_gc)
  end;
  w_last_ns := ns;
  w_last_gc := gc

let w_enter k =
  w_boundary ();
  (!w_seen).(k) <- true;
  let d = !w_depth in
  if d < Array.length !w_stack then begin
    (!w_stack).(d) <- k;
    w_depth := d + 1
  end
  else incr w_overflow

let w_leave () =
  w_boundary ();
  if !w_overflow > 0 then decr w_overflow
  else if !w_depth > 0 then decr w_depth

let worker_span k f =
  w_enter k;
  match f () with
  | v -> w_leave (); v
  | exception e ->
    let e = Exninfo.capture e in
    w_leave ();
    Exninfo.iraise e

let[@inline] span s f =
  if !enabled then span_on (index s) f
  else if !in_worker then worker_span (index s) f
  else f ()

let fork f =
  if not !enabled then f ()
  else begin
    enter fork_index;
    match f () with
    | 0 -> 0
    | pid -> incr forks; leave fork_index; pid
    | exception e ->
      let e = Exninfo.capture e in
      leave fork_index;
      Exninfo.iraise e
  end

(* The spans the main process had open at the fork stay open in the child,
   which never returns from them, and are not counted there. *)
let in_child () =
  if !enabled then begin
    enabled := false;
    let n = Array.length names in
    w_ns := Array.make n 0;
    w_gc := Array.make n 0;
    w_seen := Array.make n false;
    w_stack := Array.make 32 0;
    w_depth := 0;
    w_overflow := 0;
    stat0 := Some (Gc.quick_stat ());
    reset_gc_ns ();
    child_start_ns := now_ns ();
    w_last_ns := !child_start_ns;
    w_last_gc := 0;
    in_worker := true
  end

(* [wall_ns] and [gc_ns] are read at the same boundary as the last span
   times, so [wall_ns] minus the sum of the [<kind>_ns] is exactly the time
   outside every span, and the same for the GC times. *)
let worker_exit ~size ~completed ~code =
  if !in_worker then
    match path with
    | None -> ()
    | Some p ->
      try
        w_boundary ();
        let wall = !w_last_ns - !child_start_ns in
        let gc = !w_last_gc in
        let s1 = Gc.quick_stat () in
        let t = Unix.times () in
        let flt = minflt () in
        let maj = majflt () in
        let b = Buffer.create 2048 in
        Printf.bprintf b
          "pid=%d wall_ns=%d utime_s=%.6f stime_s=%.6f gc_ns=%d minflt=%d majflt=%d size=%d completed=%d code=%d"
          (Unix.getpid ()) wall t.Unix.tms_utime t.Unix.tms_stime gc
          flt maj size completed code;
        Array.iteri (fun k seen ->
            if seen then
              Printf.bprintf b " %s_ns=%d %s_gc_ns=%d"
                names.(k) (!w_ns).(k) names.(k) (!w_gc).(k))
          !w_seen;
        (match !stat0 with
         | None -> ()
         | Some s0 ->
           Printf.bprintf b
             " minor_words0=%.0f minor_words1=%.0f promoted_words0=%.0f promoted_words1=%.0f major_words0=%.0f major_words1=%.0f"
             s0.Gc.minor_words s1.Gc.minor_words
             s0.Gc.promoted_words s1.Gc.promoted_words
             s0.Gc.major_words s1.Gc.major_words;
           Printf.bprintf b
             " minor_collections0=%d minor_collections1=%d major_collections0=%d major_collections1=%d heap_words0=%d heap_words1=%d top_heap_words1=%d"
             s0.Gc.minor_collections s1.Gc.minor_collections
             s0.Gc.major_collections s1.Gc.major_collections
             s0.Gc.heap_words s1.Gc.heap_words
             s1.Gc.top_heap_words);
        Buffer.add_char b '\n';
        let line = Buffer.to_bytes b in
        let fd =
          Unix.openfile (p ^ ".workers")
            [Unix.O_WRONLY; Unix.O_APPEND; Unix.O_CREAT; Unix.O_CLOEXEC] 0o644
        in
        Fun.protect ~finally:(fun () -> Unix.close fd) (fun () ->
            ignore (Unix.write fd line 0 (Bytes.length line) : int))
      with _ -> ()

(* One event, as [NewProfile] builds it ([MiniJson.duration], which its
   interface does not export): args, name, ph, ts in microseconds, pid,
   tid. *)
let event pids code ns flt gc : NewProfile.MiniJson.t =
  `Assoc [
    ("args", `Assoc [("minflt", `Intlit (string_of_int flt));
                     ("gc_ns", `Intlit (string_of_int gc))]);
    ("name", `String names.(code lsr 1));
    ("ph", `String (if Int.equal (code land 1) 0 then "B" else "E"));
    ("ts", `Intlit (string_of_int (ns / 1000)));
    ("pid", `Intlit pids);
    ("tid", `Intlit pids);
  ]

(* As [NewProfile] prints a trace: the header, the events separated by
   commas, one per line, and the footer. *)
let write_trace p =
  let ch = open_out_bin p in
  Fun.protect ~finally:(fun () -> close_out_noerr ch) @@ fun () ->
  let fmt = Format.formatter_of_out_channel ch in
  let pids = string_of_int !main_pid in
  let b = !events in
  let n = !count in
  NewProfile.format_header fmt;
  for k = 0 to n - 1 do
    let i = 4 * k in
    Format.fprintf fmt "%a%s\n" NewProfile.MiniJson.pr
      (event pids b.(i) b.(i + 1) b.(i + 2) b.(i + 3))
      (if Int.equal k (n - 1) then "" else ",")
  done;
  NewProfile.format_footer fmt;
  close_out ch

let write_totals p ~wall ~(times : Unix.process_times) ~gc ~flt =
  let ch = open_out_bin p in
  Fun.protect ~finally:(fun () -> close_out_noerr ch) @@ fun () ->
  Printf.fprintf ch
    "wall_ns=%d utime_s=%.6f stime_s=%.6f cutime_s=%.6f cstime_s=%.6f gc_ns=%d minflt=%d forks=%d events=%d\n"
    wall times.Unix.tms_utime times.Unix.tms_stime
    times.Unix.tms_cutime times.Unix.tms_cstime gc flt !forks !count;
  close_out ch

let report_failure p e =
  prerr_endline ("rocqchk: cannot write the main profile " ^ p ^ ": " ^ Printexc.to_string e)

let at_main_exit p =
  if !enabled && Int.equal (Unix.getpid ()) !main_pid then begin
    let wall = now_ns () - !start_ns in
    let times = Unix.times () in
    let gc = gc_ns () in
    let flt = minflt () in
    while !depth > 0 do leave (!stack).(!depth - 1) done;
    enabled := false;
    (try write_trace p with e -> report_failure p e);
    let totals = p ^ ".totals" in
    (try write_totals totals ~wall ~times ~gc ~flt with e -> report_failure totals e)
  end

let () =
  match path with
  | None -> ()
  | Some p ->
    main_pid := Unix.getpid ();
    events := Array.make (4 * 65536) 0;
    stack := Array.make 16 0;
    install_hooks ();
    start_ns := now_ns ();
    at_exit (fun () -> at_main_exit p);
    enabled := true
