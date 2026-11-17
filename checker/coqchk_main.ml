(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Util
open System
open Names
open Environ

let () = at_exit flush_all

let print_fatal_error info =
  flush_all (); Format.eprintf "@[Fatal Error: @[%a@]@]@\n%!" Pp.pp_with info; flush_all ()

let fatal_error info code =
  print_fatal_error info;
  exit code

let rocq_root = Id.of_string "Corelib"
let parse_dir s =
  let len = String.length s in
  let rec decoupe_dirs dirs n =
    if n>=len then dirs else
    let pos =
      try
        String.index_from s n '.'
      with Not_found -> len
    in
    let dir = String.sub s n (pos-n) in
      decoupe_dirs (dir::dirs) (pos+1)
  in
    decoupe_dirs [] 0
let dirpath_of_string s =
  match parse_dir s with
  | [] -> CheckLibrary.default_root_prefix
  | dir -> DirPath.make (List.map Id.of_string dir)
let path_of_string s =
  if Filename.check_suffix s ".vo" then CheckLibrary.PhysicalFile s
  else match parse_dir s with
    | [] -> invalid_arg "path_of_string"
    | l::dir -> CheckLibrary.LogicalFile {dirpath=dir; basename=l}

let get_version env () =
  match env with
  | Boot.Env.Boot -> Coq_config.version
  | Env env ->
  try
    let revision = Boot.Env.(Path.to_string (revision env)) in
    let ch = open_in revision in
    let ver = input_line ch in
    let rev = input_line ch in
    let () = close_in ch in
    Printf.sprintf "%s (%s)" ver rev
  with Sys_error _ | End_of_file -> Coq_config.version

let print_header env () =
  Printf.printf "Welcome to Chicken %s\n%!" (get_version env ())

(* Adding files to Rocq loadpath *)

let add_path ~unix_path:dir ~rocq_root:rocq_dirpath =
  if exists_dir dir then
    begin
      CheckLibrary.add_load_path (dir,rocq_dirpath)
    end
  else
    Feedback.msg_warning (str "Cannot open " ++ str dir)

let convert_string d =
  try Id.of_string d
  with CErrors.UserError _ ->
    Flags.if_verbose Feedback.msg_warning
      (str "Directory " ++ str d ++ str " cannot be used as a Rocq identifier (skipped)");
    raise_notrace Exit

let add_rec_path ~unix_path ~rocq_root =
  if exists_dir unix_path then
    let dirs = all_subdirs ~unix_path in
    let prefix = DirPath.repr rocq_root in
    let convert_dirs (lp, cp) =
      try
        let path = List.rev_map convert_string cp @ prefix in
        Some (lp, Names.DirPath.make path)
      with Exit -> None
    in
    let dirs = List.map_filter convert_dirs dirs in
    List.iter CheckLibrary.add_load_path dirs;
    CheckLibrary.add_load_path (unix_path, rocq_root)
  else
    Feedback.msg_warning (str "Cannot open " ++ str unix_path)

(* By the option -R/-Q of the command line *)
let includes = ref []
(* The same list, kept past [init_with_argv]: the challenge load of
   [-compare] puts the challenge directory on the load path in place of each
   of these physical directories, under the same logical root. *)
let user_includes = ref []
let push_include (s, alias) = includes := (s,alias) :: !includes

let set_include d p =
  let p = if String.equal p "Coq" then "Corelib" else p in
  let p = dirpath_of_string p in
  push_include (d,p)


(* The top-level names the load path can serve WITHOUT a -Q: the corelib
   root, and the subdirectories of every directory bound RECURSIVELY under
   the empty root -- user-contrib, the XDG directories and ROCQPATH. The
   working directory is bound non-recursively, so its subdirectories serve
   no library and are not names here; its own top-level .vo files are
   served under one-word names this check cannot see, which is why a
   graded run starts in a working directory that holds no .vo. A -compare
   run refuses a -Q that binds one of these names, or the empty root,
   which would let the answer's directory shadow a library the challenge
   reads from the image. Filled by [init_load_path]; empty under -boot,
   which a graded run never uses. *)
let image_roots = ref []

let note_image_roots ~unix_path ~rocq_root =
  match List.rev (DirPath.repr rocq_root) with
  | id :: _ -> image_roots := Id.to_string id :: !image_roots
  | [] ->
    if exists_dir unix_path then
      (* a directory we cannot list, or one removed since the test
         above, gives no root rather than raising, as [all_subdirs]
         does through [System]'s own guarded readdir; a root we cannot
         see shadows nothing *)
      let entries = try Sys.readdir unix_path with Sys_error _ -> [||] in
      Array.iter (fun e ->
          if exists_dir (Filename.concat unix_path e) then
            image_roots := e :: !image_roots)
        entries

let init_load_path rocqenv =
  (* the to_string casting won't be necessary once Boot handles
     include paths *)
  let plugins = Boot.Env.plugins rocqenv |> Boot.Path.to_string in
  let theories = Boot.Env.corelib rocqenv |> Boot.Path.to_string in
  let user_contrib = Boot.Env.user_contrib rocqenv |> Boot.Path.to_string in
  let xdg_dirs = Envars.xdg_dirs in
  let rocqpath = Envars.coqpath in
  let add_rec_path ~unix_path ~rocq_root =
    note_image_roots ~unix_path ~rocq_root;
    add_rec_path ~unix_path ~rocq_root
  in
  (* NOTE: These directories are searched from last to first *)
  (* first standard library *)
  add_rec_path ~unix_path:theories ~rocq_root:(Names.DirPath.make[rocq_root]);
  (* then plugins *)
  add_rec_path ~unix_path:plugins ~rocq_root:(Names.DirPath.make [rocq_root]);
  (* then user-contrib *)
  if Sys.file_exists user_contrib then
    add_rec_path ~unix_path:user_contrib ~rocq_root:CheckLibrary.default_root_prefix;
  (* then directories in XDG_DATA_DIRS and XDG_DATA_HOME *)
  List.iter (fun s -> add_rec_path ~unix_path:s ~rocq_root:CheckLibrary.default_root_prefix)
    (xdg_dirs ~warn:(fun x -> Feedback.msg_warning (str x)));
  (* then directories in ROCQPATH *)
  List.iter (fun s -> add_rec_path ~unix_path:s ~rocq_root:CheckLibrary.default_root_prefix) (rocqpath());
  (* then current directory: bound non-recursively, so it adds no image
     root (see [image_roots]) *)
  add_path ~unix_path:"." ~rocq_root:CheckLibrary.default_root_prefix

let init_load_path env : unit =
  NewProfile.profile "init_load_path"
    (fun () -> init_load_path env)
    ()

let impredicative_set = ref false
let set_impredicative_set () = impredicative_set := true

let boot = ref false
let set_boot () = boot := true

let coqlib = ref None
let set_coqlib v = coqlib := Some v

let indices_matter = ref false

let enable_vm = ref false

let statement_report = ref None

(* [rocqchk -compare CONFIG -challenge DIR -compare-out FILE] *)
let compare_config = ref None
let compare_challenge = ref None
let compare_out = ref None
let sha256_files = ref []

let jobs = ref 1
let set_jobs s =
  match int_of_string_opt s with
  | Some n when n >= 1 -> jobs := n
  | _ -> fatal_error (str "Option -j expects a positive integer, got " ++ qstring s ++ str ".") 1

let set_worker_budget s =
  match float_of_string_opt s with
  | Some t when t >= 0. -> CheckWorkers.set_budget t
  | _ ->
    fatal_error (str "Option -worker-budget expects a number of seconds, got " ++ qstring s ++ str ".") 1

(* "<library> <seconds>" per line; a later line for a library replaces an
   earlier one. Costs only order the workers' checks, so nothing about the
   file can stop the check: a malformed line is skipped, and anything but a
   regular file of at most [max_cost_hints_bytes] that can be read to its
   end is ignored whole, with a warning. The bound is on the bytes read,
   not on the size the file reports. *)
let max_cost_hints_bytes = 16 * 1024 * 1024

let set_cost_hints f =
  let ignored why =
    Feedback.msg_warning (str "Ignoring the cost hints " ++ qstring f ++ str " (" ++
                          str why ++ str "); the checks are dealt without them.")
  in
  let parse line =
    let fields = List.filter (fun s -> s <> "")
        (String.split_on_char ' ' (String.map (fun c -> if c = '\t' then ' ' else c) line)) in
    match fields with
    | [lib; s] ->
      (match float_of_string_opt s with
       | Some c when c >= 0. && Float.is_finite c -> Some (lib, c)
       | _ -> None)
    | _ -> None
  in
  (* At most [max_cost_hints_bytes + 1] bytes, so that a source reporting
     a wrong size, or growing, cannot make the read unbounded. *)
  let read_bounded ch =
    let buf = Buffer.create 65536 in
    let chunk = Bytes.create 65536 in
    let rec go () =
      let want = min (Bytes.length chunk) (max_cost_hints_bytes + 1 - Buffer.length buf) in
      if want <= 0 then Error "too large"
      else match input ch chunk 0 want with
        | 0 -> Ok (Buffer.contents buf)
        | n -> Buffer.add_subbytes buf chunk 0 n; go ()
    in
    go ()
  in
  (* Opened without blocking, and its kind read from the open descriptor:
     whatever the path names when it is opened, a FIFO cannot block the
     check and only a regular file is read. *)
  match Unix.openfile f [Unix.O_RDONLY; Unix.O_NONBLOCK; Unix.O_CLOEXEC] 0 with
  | exception Unix.Unix_error (e, _, _) -> ignored (Unix.error_message e)
  | fd ->
    let contents =
      match (Unix.fstat fd).Unix.st_kind with
      | exception Unix.Unix_error (e, _, _) -> Unix.close fd; Error (Unix.error_message e)
      | Unix.S_REG ->
        Unix.clear_nonblock fd;
        let ch = Unix.in_channel_of_descr fd in
        set_binary_mode_in ch true;
        Fun.protect ~finally:(fun () -> close_in_noerr ch) (fun () ->
            try read_bounded ch with Sys_error e -> Error e)
      | _ -> Unix.close fd; Error "not a regular file"
    in
    match contents with
    | Error why -> ignored why
    | Ok s -> CheckWorkers.set_cost_hints (List.filter_map parse (String.split_on_char '\n' s))

let make_senv () =
  let senv = Safe_typing.empty_environment in
  let senv = Safe_typing.set_impredicative_set !impredicative_set senv in
  let senv = Safe_typing.set_indices_matter !indices_matter senv in
  let senv = Safe_typing.set_VM !enable_vm senv in
  let senv = Safe_typing.set_allow_sprop true senv in (* be smarter later *)
  Safe_typing.set_native_compiler false senv

let admit_list = ref ([] : CheckLibrary.object_file list)
let add_admit s =
  admit_list := path_of_string s :: !admit_list

let norec_list = ref ([] : CheckLibrary.object_file list)
let add_norec s =
  norec_list := path_of_string s :: !norec_list

let compile_list = ref ([] : CheckLibrary.object_file list)
let add_compile s =
  compile_list := path_of_string s :: !compile_list

(*s Parsing of the command line.
    We no longer use [Arg.parse], in order to use share [Usage.print_usage]
    between coqtop and coqc. *)

let compile_files senv =
  CheckLibrary.recheck_library ~output_context:!Check_stat.output_context senv
    ~norec:(List.rev !norec_list)
    ~admit:(List.rev !admit_list)
    ~check:(List.rev !compile_list)

let version () =
  Printf.printf "The Rocq Proof Checker, version %s\n" Coq_config.version;
  exit 0

(* print the usage of coqtop (or coqc) on channel co *)

let print_usage_channel co command =
  output_string co command;
  output_string co "coqchk options are:\n";
  output_string co
"\
\n  -Q dir coqdir               map physical dir to logical coqdir\
\n  -R dir coqdir               synonymous for -Q\
\n  -coqlib dir                 set coqchk's standard library location\
\n  -boot                       don't initialize the library paths automatically\
\n\
\n  -admit module               load module and dependencies without checking\
\n  -norec module               check module but admit dependencies without checking\
\n\
\n  -d (d1,..,dn)               enable specified debug messages\
\n  -debug                      enable all debug messages\
\n  -profile file               output profiling info to file\
\n  -where                      print coqchk's standard library location and exit\
\n  -v, --version               print coqchk version and exit\
\n  -o, --output-context        print the list of assumptions\
\n  -m, --memory                print the maximum heap size\
\n  -silent                     disable trace of constants being checked\
\n  -j n                        check opaque proofs in parallel, using up to n\
\n                              processes (default is 1, no parallelism)\
\n  -worker-budget s            with -j, a worker process stops after s seconds\
\n                              (default is 20) and its remaining checks are given\
\n                              to another one; this bounds the memory it uses\
\n  -cost-hints f               with -j, deal first the checks of the libraries that f\
\n                              says cost most (\"<library> <seconds>\" per line)\
\n  -statement-report f         print, for each statement named in f, whether its model\
\n                              constant has its trusted constant's type and the axioms its\
\n                              closure uses\
\n  -compare config             grade the checked answer against a challenge: compare every\
\n                              challenge declaration with the answer's declaration of the\
\n                              same kernel name and judge each named theorem's axioms\
\n                              (needs -challenge and -compare-out)\
\n  -challenge dir              the directory holding the challenge's .vo files\
\n  -compare-out f              write the comparator's JSON verdict to f\
\n  -sha256 f                   print the SHA-256 of f and exit\
\n\
\n  -impredicative-set          set sort Set impredicative\
\n  -indices-matter             levels of indices (and nonuniform parameters)\
\n                              contribute to the level of inductives\
\n  -bytecode-compiler (yes|no) enable the vm_compute reduction machine (default is no)\
\n  -merge-inductives           treat a loaded inductive type that matches one already\
\n                              loaded as the same type (off by default); the match is\
\n                              recomputed here, never read from a .vo\
\n  -merge-inductives-verbose   -merge-inductives, and print each merge\
\n\
\n  -h, --help                  print this list of options\
\n"

(* print the usage on standard error *)

let print_usage = print_usage_channel stderr

let print_usage_rocqtop () =
  print_usage "Usage: coqchk <options> modules\n\n"

let usage exitcode =
  print_usage_rocqtop ();
  flush stderr;
  exit exitcode

open Type_errors

let anomaly_string () = str "Anomaly: "
let report () = strbrk (". Please report at " ^ Coq_config.wwwbugtracker ^ ".")

let guill s = str "\"" ++ str s ++ str "\""

let rec explain_exn = function
  | Sys_error msg ->
      hov 0 (anomaly_string () ++ str "uncaught exception Sys_error " ++ guill msg ++ report() )
  | UserError pps ->
      hov 1 (str "User error: " ++ pps)
  | Out_of_memory ->
      hov 0 (str "Out of memory")
  | Stack_overflow ->
      hov 0 (str "Stack overflow")
  | Match_failure(filename,pos1,pos2) ->
      hov 1 (anomaly_string () ++ str "Match failure in file " ++
             guill filename ++ str " at line " ++ int pos1 ++
             str " character " ++ int pos2 ++ report ())
  | Not_found ->
      hov 0 (anomaly_string () ++ str "uncaught exception Not_found" ++ report ())
  | Failure s ->
      hov 0 (str "Failure: " ++ str s ++ report ())
  | Invalid_argument s ->
      hov 0 (anomaly_string () ++ str "uncaught exception Invalid_argument " ++ guill s ++ report ())
  | Sys.Break ->
    hov 0 (fnl () ++ str "User interrupt.")
  | UGraph.UniverseInconsistency i ->
    let msg =
      if CDebug.(get_flag misc) then
        str "." ++ spc() ++
          UGraph.explain_universe_inconsistency Sorts.QVar.raw_pr Univ.Level.raw_pr i
      else
        mt() in
    hov 0 (str "Error: Universe inconsistency" ++ msg ++ str ".")
  | QGraph.EliminationError e ->
    let msg =
      if CDebug.(get_flag misc) then
        str "." ++ spc() ++
          QGraph.explain_elimination_error Sorts.QVar.raw_pr e
      else
        mt() in
    hov 0 (str "Error: Elimination error" ++ msg ++ str ".")
  | TypeError(ctx,te) ->
      hov 0 (str "Type error: " ++
      (match te with
      | UnboundRel i -> str"UnboundRel " ++ int i
      | UnboundVar v -> str"UnboundVar" ++ str(Names.Id.to_string v)
      | NotAType _ -> str"NotAType"
      | BadAssumption _ -> str"BadAssumption"
      | ReferenceVariables _ -> str"ReferenceVariables"
      | ElimArity _ -> str"ElimArity"
      | CaseNotInductive _ -> str"CaseNotInductive"
      | CaseOnPrivateInd _ -> str"CaseOnPrivateInd"
      | WrongCaseInfo _ -> str"WrongCaseInfo"
      | NumberBranches _ -> str"NumberBranches"
      | IllFormedBranch _ -> str"IllFormedBranch"
      | IllFormedCaseParams -> str "IllFormedCaseParams"
      | BadProjType _ -> str "BadProjType"
      | Generalization _ -> str"Generalization"
      | ActualType _ -> str"ActualType"
      | IncorrectPrimitive _ -> str"IncorrectPrimitive"
      | CantApplyBadType ((n,a,b),{uj_val = hd; uj_type = hdty},args) ->
        let pp_arg i judge =
          hv 1 (str"arg " ++ int (i+1) ++ str"= " ++
                Constr.debug_print judge.uj_val ++
                str ",type= " ++ Constr.debug_print judge.uj_type) ++ fnl ()
        in
        Feedback.msg_notice (str"====== ill-typed term ====" ++ fnl () ++
                       hov 2 (str"application head= " ++ Constr.debug_print hd) ++ fnl () ++
                       hov 2 (str"head type= " ++ Constr.debug_print hdty) ++ fnl () ++
                       str"arguments:" ++ fnl () ++ hv 1 (prvecti pp_arg args));
        Feedback.msg_notice (str"====== type error ====@" ++ fnl () ++
                             Constr.debug_print b ++ fnl () ++
                             str"is not convertible with" ++ fnl () ++
                             Constr.debug_print a ++ fnl ());
        Feedback.msg_notice (str"====== universes ====" ++ fnl () ++
                             (UGraph.pr_universes Univ.Level.raw_pr
                                (UGraph.repr (Environ.universes ctx))));
        str "CantApplyBadType at argument " ++ int n
      | CantApplyNonFunctional _ -> str"CantApplyNonFunctional"
      | IllFormedRecBody _ -> str"IllFormedRecBody"
      | IllTypedRecBody _ -> str"IllTypedRecBody"
      | UnsatisfiedUnivConstraints _ -> str"UnsatisfiedUnivConstraints"
      | UnsatisfiedPConstraints _ -> str"UnsatisfiedPConstraints"
      | NotAllowedSProp -> str"NotAllowedSProp"
      | BadBinderRelevance _ -> str"BadBinderRelevance"
      | BadCaseRelevance _ -> str"BadCaseRelevance"
      | BadInvert -> str"BadInvert"
      | UndeclaredQualities _ -> str"UndeclaredQualities"
      | UndeclaredUniverses _ -> str"UndeclaredUniverse"
      | BadVariance _ -> str "BadVariance"
      | BadQVariance _ -> str "BadQVariance"
      | UndeclaredUsedVariables _ -> str "UndeclaredUsedVariables"
      | IllFormedConstant _ -> str "IllFormedConstant"
      | IllFormedInductive _ -> str "IllFormedInductive"
      | ArrayTooLong _ -> str "ArrayTooLong"
      ))

  | InductiveError (env,e) ->
      hov 0 (str "Error related to inductive types")
(*      let ctx = Check.get_env() in
      hov 0
        (str "Error:" ++ spc () ++ Himsg.explain_inductive_error ctx e)*)

  | CheckInductive.InductiveMismatch (mind,field) ->
    hov 0 (MutInd.print mind ++ str ": field " ++ str field ++ str " is incorrect.")

  | Mod_checking.BadConstant (cst, why) ->
    hov 0 (Constant.print cst ++ spc() ++ why)

  | CheckWorkers.CheckError (job, e) ->
    explain_exn e ++ fnl () ++
    hov 0 (str "while " ++ CheckWorkers.pr_doing job ++ str ".")

  | CheckWorkers.WorkerFailed (pid, status, batch) ->
    let status = match status with
      | Unix.WEXITED n -> str "exited with code " ++ int n
      | Unix.WSIGNALED s -> str "was killed by " ++ str (CheckWorkers.signal_name s)
      | Unix.WSTOPPED s -> str "was stopped by " ++ str (CheckWorkers.signal_name s)
    in
    hov 0 (str "Worker process " ++ int pid ++ spc () ++ status ++ spc () ++
           str "while checking " ++ CheckWorkers.pr_batch batch ++ str ".")

  | Assert_failure (s,b,e) ->
      hov 0 (anomaly_string () ++ str "assert failure" ++ spc () ++
               (if s = "" then mt ()
                else
                  (str "(file \"" ++ str s ++ str "\", line " ++ int b ++
                   str ", characters " ++ int e ++ str "-" ++
                   int (e+6) ++ str ")")) ++
               report ())
  | e -> CErrors.print e (* for anomalies and other uncaught exceptions *)

let profile = ref None

(* The verdict file of a -compare run goes first, before the command line is
   parsed or anything is checked, so that a run that stops early -- a usage
   error, a malformed config, a challenge file's sha256, an answer that fails
   its check -- leaves no earlier run's verdict where a reader would take it
   for this run's (dispatch://BET-895, P2-1). The file is the argument after
   any "-compare-out" token. One that cannot be removed is emptied, which no
   reader takes for a verdict. *)
let remove_stale_verdicts args =
  let rec scan = function
    | "-compare-out" :: f :: rem ->
      (try Sys.remove f with Sys_error _ ->
         try close_out (open_out_gen [Open_wronly; Open_trunc] 0 f) with Sys_error _ -> ());
      scan rem
    | _ :: rem -> scan rem
    | [] -> ()
  in
  scan args

let parse_args argv =
  let rec parse = function
    | [] -> ()
    | "-merge-inductives" :: rem ->
        Indmerge.set_enabled true; parse rem

    | "-merge-inductives-verbose" :: rem ->
        Indmerge.set_enabled true; Indmerge.set_verbose true; parse rem

    | "-impredicative-set" :: rem ->
      set_impredicative_set (); parse rem

    | "-indices-matter" :: rem ->
      indices_matter:=true; parse rem

    | "-bytecode-compiler" :: "yes" :: rem ->
      enable_vm := true; parse rem
    | "-bytecode-compiler" :: "no" :: rem ->
      enable_vm := false; parse rem

    | "-coqlib" :: s :: rem ->
      if not (exists_dir s) then
        fatal_error (str "Directory '" ++ str s ++ str "' does not exist") 1;
      set_coqlib s;
      parse rem

    | "-boot" :: rem ->
      set_boot ();
      parse rem

    | ("-Q"|"-R") :: d :: p :: rem -> set_include d p;parse rem
    | ("-Q"|"-R") :: ([] | [_]) -> usage 1

    | "-d" :: s :: rem ->
      CDebug.set_flags s;
      parse rem
    | "-debug" :: rem -> CDebug.set_debug_all true; parse rem

    | "-profile" :: s :: rem ->
      profile := Some s;
      parse rem

    | "-profile" :: [] -> usage 1

    | "-where" :: _ ->
      let env = Boot.Env.init_with ~coqlib:!coqlib in
      let rocqlib = Boot.Env.coqlib env |> Boot.Path.to_string in
      print_endline rocqlib;
      exit 0

    | ("-?"|"-h"|"-H"|"-help"|"--help") :: _ -> usage 0

    | ("-v"|"--version") :: _ -> version ()
    | ("-m" | "--memory") :: rem -> Check_stat.memory_stat := true; parse rem
    | ("-o" | "--output-context") :: rem ->
        Check_stat.output_context := true; parse rem

    | "-admit" :: s :: rem -> add_admit s; parse rem
    | "-admit" :: [] -> usage 1

    | "-norec" :: s :: rem -> add_norec s; parse rem
    | "-norec" :: [] -> usage 1

    | "-silent" :: rem ->
        Flags.quiet := true; parse rem

    | "-j" :: n :: rem -> set_jobs n; parse rem
    | "-j" :: [] -> usage 1

    | "-worker-budget" :: s :: rem -> set_worker_budget s; parse rem
    | "-worker-budget" :: [] -> usage 1

    | "-cost-hints" :: f :: rem -> set_cost_hints f; parse rem
    | "-cost-hints" :: [] -> usage 1

    | "-statement-report" :: f :: rem ->
        (* Read now, so that a malformed file stops the run before any
           library is loaded. *)
        statement_report := Some (Check_closure.read_requests f); parse rem
    | "-statement-report" :: [] -> usage 1

    | "-compare" :: f :: rem ->
        (* Read now, so that a malformed config stops the run before any
           library is loaded. A pre-checked library loads without a check,
           through the admit list. *)
        let cfg = Check_compare.read_config f in
        List.iter add_admit (Check_compare.prechecked_libraries cfg);
        compare_config := Some cfg; parse rem
    | "-compare" :: [] -> usage 1

    | "-challenge" :: d :: rem ->
        if not (exists_dir d) then
          fatal_error (str "Directory '" ++ str d ++ str "' does not exist") 1;
        compare_challenge := Some d; parse rem
    | "-challenge" :: [] -> usage 1

    | "-compare-out" :: f :: rem -> compare_out := Some f; parse rem
    | "-compare-out" :: [] -> usage 1

    | "-sha256" :: f :: rem ->
        print_endline (Check_compare.sha256_of_file f);
        sha256_files := f :: !sha256_files; parse rem
    | "-sha256" :: [] -> usage 1

    | s :: _ when s<>"" && s.[0]='-' ->
        fatal_error (str "Unknown option " ++ str s) 1
    | s :: rem ->  add_compile s; parse rem
  in
  let args = List.tl (Array.to_list argv) in
  remove_stale_verdicts args;
  parse args;
  (* [-sha256] is a probe of the comparator's own digest, nothing else. *)
  if not (CList.is_empty !sha256_files) then exit 0;
  match !compare_config, !compare_challenge, !compare_out with
  | None, None, None | Some _, Some _, Some _ -> ()
  | _ ->
    fatal_error
      (str "Options -compare, -challenge and -compare-out go together.") 1

let init_profile ~file =
  let ch = open_out file in
  let fname = Filename.basename file in
  NewProfile.init { output = Format.formatter_of_out_channel ch; fname; };
  at_exit (fun () ->
      NewProfile.finish ();
      close_out ch)

(* The console feedback listener, which a forked report child removes. *)
let console_feeder = ref None

(* XXX: At some point we need to either port the checker to use the
   feedback system or to remove its use completely. *)
let init_with_argv argv =
  console_feeder := Some Feedback.(add_feeder (console_feedback_listener Format.err_formatter));
  try
    parse_args argv;
    Option.iter (fun file -> init_profile ~file) !profile;
    CheckWorkers.set_jobs ~profiling:(Option.has_some !profile) !jobs;
    if CDebug.(get_flag misc) then Printexc.record_backtrace true;
    let coqenv = Boot.Env.maybe_init ~boot:!boot ~coqlib:!coqlib
        ~warn_ignored_coqlib:CWarnings.warn_ignored_coqlib
    in
    Flags.if_verbose (fun () -> print_header coqenv ()) ();
    let () = match coqenv with
      | Boot -> ()
      | Env coqenv -> init_load_path coqenv
    in
    (* additional loadpath, given with -R/-Q options *)
    NewProfile.profile "add_load_paths" (fun () ->
        List.iter
          (fun (unix_path, rocq_root) -> add_rec_path ~unix_path ~rocq_root)
          (List.rev !includes))
      ();
    user_includes := List.rev !includes;
    includes := [];
    make_senv ()
  with e ->
    fatal_error (str "Error during initialization :" ++ (explain_exn e)) (CErrors.exit_code e)

let init() = init_with_argv Sys.argv

let exit_code = function
  | CheckWorkers.CheckError (_, e) -> CErrors.exit_code e
  | CheckWorkers.WorkerFailed (_, Unix.WEXITED n, _) when n <> 0 -> n
  | CheckWorkers.WorkerFailed _ -> 1
  | e -> CErrors.exit_code e

(* The error [e] ends the run: its backtrace with -d misc, its text, then its
   exit code. *)
let fatal_exn e =
  if CDebug.(get_flag misc) then Printexc.print_backtrace stderr;
  fatal_error (explain_exn e) (exit_code e)

(* Prints a worker's error as [fatal_exn] does but does not exit; the
   worker's handler returns the exit code. *)
let () = CheckWorkers.set_error_printer (fun e ->
    if CDebug.(get_flag misc) then Printexc.print_backtrace stderr;
    print_fatal_error (explain_exn e))

let run senv =
  try
    let senv = compile_files senv in
    flush_all(); senv
  with e -> fatal_exn e

(* The report is evidence beside the verdict, never the verdict: a report
   that cannot be completed is left without its end marker, which a reader
   takes as no report, and the exit status is unchanged. It comes before the
   context summary. The run goes on to exit 0, so the warning escapes the text
   of the exception, which can quote a name read from a library (checkNames.mli).
   The text is the one [explain_exn] returns: it prints the terms of a
   [CantApplyBadType] type error itself, but nothing in the report raises one. *)
(* Prototype (measurement only, never merged): ROCQCHK_REPORT_MINOR_WORDS and
   ROCQCHK_REPORT_SPACE_OVERHEAD, when set, replace the GC settings of the
   process that computes the report, from the report on. *)
let tune_report_gc () =
  let env_int v = Option.bind (Sys.getenv_opt v) int_of_string_opt in
  let gc = Gc.get () in
  let gc = match env_int "ROCQCHK_REPORT_MINOR_WORDS" with
    | Some n -> { gc with Gc.minor_heap_size = n } | None -> gc in
  let gc = match env_int "ROCQCHK_REPORT_SPACE_OVERHEAD" with
    | Some n -> { gc with Gc.space_overhead = n } | None -> gc in
  Gc.set gc

let print_statement_report ?records env requests =
  tune_report_gc ();
  try Check_closure.print ?records env CheckLibrary.indirect_accessor requests
  with e when (match e with Sys.Break | Out_of_memory -> false | _ -> true) ->
    Feedback.msg_warning
      (str "Statement report stopped: " ++
       str (String.escaped (Pp.string_of_ppcmds (explain_exn e))))

(* The report needs only the final environment. With workers, a child forked
   once the last library is checked computes it while the main process waits
   for them ([CheckLibrary.set_final_env_hook]), and the main process prints
   it where it always did, after the workers. The child prints nothing: it
   keeps each feedback message the report emits, in order, in a file, then an
   end marker, and the main process sends each one through the feedback
   system again, so the same listener prints the same bytes on the same
   channel. A capture without the end marker, from a child that failed or
   that wrote to a standard channel, is not used, nor one from a child whose
   exit code is known not to be 0: the main process then computes the report
   itself, as without the child. ROCQCHK_REPORT_CHILD=0 turns the child off.
   The child is no worker: [CheckWorkers] neither counts it nor gives it a
   slot. *)
type captured = Captured of Feedback.feedback | Capture_end

type report_child = { pid : int; file : string; parent : int }

let report_child = ref None

let rec waitpid_non_intr flags pid =
  try Unix.waitpid flags pid
  with Unix.Unix_error (Unix.EINTR, _, _) -> waitpid_non_intr flags pid

let remove_noerr f = try Sys.remove f with Sys_error _ -> ()

(* At exit, and once the report is read, so that a run that stops on an
   error leaves no child behind. A child that has exited stays a zombie
   until it is reaped, so a pid that [waitpid] reports as running cannot
   have been reused; a child that [CheckWorkers.finish], which reaps any
   child, has reaped already is not signalled. Only the main process acts:
   a worker forked later inherits this, but leaves through its own exit. *)
let reap_report_child () =
  match !report_child with
  | Some c when Int.equal (Unix.getpid ()) c.parent ->
    report_child := None;
    (match waitpid_non_intr [Unix.WNOHANG] c.pid with
     | 0, _ ->
       (try Unix.kill c.pid Sys.sigkill with Unix.Unix_error _ -> ());
       (try ignore (waitpid_non_intr [] c.pid) with Unix.Unix_error _ -> ())
     | _ -> ()
     | exception Unix.Unix_error _ -> ());
    remove_noerr c.file
  | Some _ | None -> ()

(* In the child. It never returns, and never runs the main process's at_exit
   functions, which would print its buffered output a second time. *)
let run_report_child ~parent ~file requests senv =
  at_exit (fun () -> Unix._exit 3);
  let code =
    try
      (* What the main process had buffered goes nowhere, and so does
         anything written to the standard channels from now on. *)
      let null = Unix.openfile "/dev/null" [Unix.O_WRONLY] 0 in
      Unix.dup2 ~cloexec:false null Unix.stdout;
      Unix.dup2 ~cloexec:false null Unix.stderr;
      Unix.close null;
      Format.pp_print_flush Format.std_formatter ();
      Format.pp_print_flush Format.err_formatter ();
      let out_pos = pos_out stdout and err_pos = pos_out stderr in
      (* As in a worker ([CheckWorkers]): the heap is shared copy-on-write
         with the main process, so compaction, which would copy all of it,
         is off, and a larger minor heap promotes less. *)
      let gc = Gc.get () in
      Gc.set { gc with Gc.minor_heap_size = max gc.Gc.minor_heap_size (4 * 1024 * 1024);
                       max_overhead = 1000000 };
      let oc = open_out_gen [Open_wronly; Open_creat; Open_trunc; Open_binary] 0o600 file in
      Option.iter Feedback.del_feeder !console_feeder;
      let _ : int = Feedback.add_feeder (fun fb ->
          (* Nobody will read the report any more. *)
          if not (Int.equal (Unix.getppid ()) parent) then (remove_noerr file; Unix._exit 1);
          try Marshal.to_channel oc (Captured fb) [] with _ -> Unix._exit 1)
      in
      print_statement_report (Safe_typing.env_of_safe_env senv) requests;
      (* What the report printed other than through the feedback system is
         not kept, so the main process must compute the report itself. *)
      Format.pp_print_flush Format.std_formatter ();
      Format.pp_print_flush Format.err_formatter ();
      if not (Int.equal (pos_out stdout) out_pos && Int.equal (pos_out stderr) err_pos) then 4
      else begin
        Marshal.to_channel oc Capture_end [];
        close_out oc;
        0
      end
    with _ -> 1
  in
  Unix._exit code

(* The hook: a failed fork, or no temporary file, leaves no child, and the
   main process computes the report itself. *)
let start_report_child requests senv =
  match Filename.temp_file "rocqchk_report" ".cap" with
  | exception Sys_error _ -> ()
  | file ->
    let parent = Unix.getpid () in
    match Unix.fork () with
    | 0 -> run_report_child ~parent ~file requests senv
    | pid ->
      report_child := Some { pid; file; parent };
      at_exit reap_report_child
    | exception Unix.Unix_error _ -> remove_noerr file

(* The messages the child kept, or [None] when there is no child or its
   capture is not to be used. [CheckWorkers.finish] reaps any child that has
   exited, not only its workers, so a child that ended before the workers
   did has no status left to read: then the end marker, which it writes
   last, alone says that it completed the report. *)
let collect_report_child () =
  match !report_child with
  | None -> None
  | Some c ->
    let usable = match waitpid_non_intr [] c.pid with
      | _, Unix.WEXITED 0 -> true
      | _, (Unix.WEXITED _ | Unix.WSIGNALED _ | Unix.WSTOPPED _) -> false
      | exception Unix.Unix_error (Unix.ECHILD, _, _) -> true
      | exception Unix.Unix_error _ -> false
    in
    let read () =
      let ic = open_in_bin c.file in
      Fun.protect ~finally:(fun () -> close_in_noerr ic) (fun () ->
          let rec loop acc = match (input_value ic : captured) with
            | Captured fb -> loop (fb :: acc)
            | Capture_end -> Some (List.rev acc)
          in
          loop [])
    in
    let captured =
      if not usable then None
      else try read () with Sys_error _ | End_of_file | Failure _ -> None
    in
    reap_report_child ();
    captured

(* The child's messages, sent as they were first emitted, or else the report
   computed here. *)
let print_report ?records env requests =
  match collect_report_child () with
  | Some captured ->
    List.iter (fun fb ->
        Feedback.feedback ~did:fb.Feedback.doc_id ~id:fb.Feedback.span_id
          ~route:fb.Feedback.route fb.Feedback.contents)
      captured
  | None -> print_statement_report ?records env requests

let report_child_enabled () =
  CheckWorkers.parallel ()
  && (match Sys.getenv_opt "ROCQCHK_REPORT_CHILD" with
      | Some "0" -> false
      | Some _ | None -> true)

(* Prototype C7 (measurement only, never merged). With workers and a
   statement report, each process that checks an opaque body whose opaque has
   no substitution writes the record [(kn, dp, index, objects)] of that body
   ([Check_closure.opaque_body_refs]) to a file of its own, [<pid>.refs], in a
   fresh directory only this user can enter. Once every worker has finished
   and every check has passed, the main process reads the records, removes
   the directory, and the report takes the objects of each recorded body from
   them instead of reading and walking the body ([Check_closure.print]).
   ROCQCHK_REPORT_REFS=0 turns this off. The report child is off with it: it
   would run before the records exist. *)
type refs_record = Constant.t * DirPath.t * int * GlobRef.t list

type refs_dir = { dir : string; owner : int }

let refs_dir = ref None

(* The file this process writes its records to, with the pid that opened it:
   a worker inherits the main process's, and opens its own. A raw descriptor,
   to which each record goes whole as soon as it is made, so that nothing
   waits in a buffer: a worker leaves without flushing ([CheckWorkers]), and
   a channel inherited from the main process would be flushed by the worker
   too. Opened to append, so that a worker that gets the pid of one that has
   exited adds to its file instead of emptying it. *)
let refs_out : (int * Unix.file_descr) option ref = ref None

(* The pid of a process whose recording failed: it records nothing more. *)
let refs_stopped = ref None

let refs_enabled () =
  match Sys.getenv_opt "ROCQCHK_REPORT_REFS" with
  | Some "0" -> false
  | Some _ | None -> true

let rec write_all fd b ofs len =
  if len > 0 then
    match Unix.single_write fd b ofs len with
    | n -> write_all fd b (ofs + n) (len - n)
    | exception Unix.Unix_error (Unix.EINTR, _, _) -> write_all fd b ofs len

(* The hook of [Mod_checking], in whichever process checked the body. It
   raises nothing: a failure only stops the recording in this process, whose
   bodies the report then reads. *)
let record_refs dir kn o env c =
  let pid = Unix.getpid () in
  let stopped = match !refs_stopped with Some p -> Int.equal p pid | None -> false in
  if not stopped then
    try
      let (sub, _, dp, i) = Opaqueproof.repr o in
      if CList.is_empty sub then begin
        let fd = match !refs_out with
          | Some (p, fd) when Int.equal p pid -> fd
          | Some _ | None ->
            let file = Filename.concat dir (string_of_int pid ^ ".refs") in
            let fd = Unix.openfile file
                [Unix.O_WRONLY; Unix.O_CREAT; Unix.O_APPEND; Unix.O_CLOEXEC] 0o600 in
            refs_out := Some (pid, fd);
            fd
        in
        let record : refs_record =
          (kn, dp, Opaqueproof.repr_handle i, Check_closure.opaque_body_refs env c) in
        let b = Marshal.to_bytes record [] in
        write_all fd b 0 (Bytes.length b)
      end
    with _ -> refs_stopped := Some pid

(* A fresh directory named after this process, or [None]. *)
let make_refs_dir () =
  let rng = Random.State.make_self_init () in
  let owner = Unix.getpid () in
  let rec attempt n =
    if Int.equal n 0 then None
    else
      let dir = Filename.concat (Filename.get_temp_dir_name ())
          (Printf.sprintf "rocqchk_refs_%d_%08x" owner (Random.State.bits rng)) in
      match Unix.mkdir dir 0o700 with
      | () -> Some { dir; owner }
      | exception Unix.Unix_error (Unix.EEXIST, _, _) -> attempt (n - 1)
      | exception Unix.Unix_error _ -> None
  in
  attempt 10

let close_main_refs_out owner =
  match !refs_out with
  | Some (p, fd) when Int.equal p owner ->
    refs_out := None;
    (try Unix.close fd with Unix.Unix_error _ -> ())
  | Some _ | None -> ()

(* At exit, and once the records are read. Only the main process, which made
   the directory, acts: a worker inherits this, but leaves through its own
   exit. *)
let remove_refs_dir () =
  match !refs_dir with
  | Some d when Int.equal (Unix.getpid ()) d.owner ->
    refs_dir := None;
    close_main_refs_out d.owner;
    let files = try Sys.readdir d.dir with Sys_error _ -> [||] in
    Array.iter (fun f -> remove_noerr (Filename.concat d.dir f)) files;
    (try Unix.rmdir d.dir with Unix.Unix_error _ -> ())
  | Some _ | None -> ()

(* Before the run, in the main process: whether the records are on. *)
let start_refs_records () =
  match make_refs_dir () with
  | None -> false
  | Some d ->
    refs_dir := Some d;
    at_exit remove_refs_dir;
    Mod_checking.set_opaque_checked_hook (record_refs d.dir);
    true

(* After the run, once every worker has finished: the records of every
   process, then the directory is removed. A record cut short ends the
   reading of its file; a file that cannot be opened gives no record. If the
   reading itself fails, there are no records, and the report reads every
   body. *)
let collect_refs_records () =
  match !refs_dir with
  | None -> None
  | Some d ->
    Mod_checking.set_opaque_checked_hook (fun _ _ _ _ -> ());
    close_main_refs_out d.owner;
    let t0 = Unix.gettimeofday () in
    let read () =
      let records = Check_closure.opaque_records () in
      let files = try Sys.readdir d.dir with Sys_error _ -> [||] in
      let nfiles = ref 0 in
      Array.iter (fun f ->
          if Filename.check_suffix f ".refs" then
            match open_in_bin (Filename.concat d.dir f) with
            | exception Sys_error _ -> ()
            | ic ->
              incr nfiles;
              let rec loop () =
                match (input_value ic : refs_record) with
                | (kn, dp, i, objs) -> Check_closure.add_opaque_record records kn dp i objs; loop ()
                | exception (End_of_file | Failure _ | Sys_error _) -> ()
              in
              Fun.protect ~finally:(fun () -> close_in_noerr ic) loop)
        files;
      Check_closure.note_opaque_records_read records ~files:!nfiles
        ~seconds:(Unix.gettimeofday () -. t0);
      records
    in
    let records = try Some (read ()) with e when CErrors.noncritical e -> None in
    remove_refs_dir ();
    records

(* The comparator's verdict is the point of the run, not evidence beside it:
   a run that could not complete -- a challenge file whose sha256 differs, a
   pre-checked library the two sides disagree on, a theorem the challenge
   does not hold -- exits non-zero and writes no verdict file. A verdict,
   whatever it says, leaves the exit status at 0, except with -o: the context
   summary is printed after the verdict file is written, and a summary the
   walk of mod_impl.ml could not complete makes the run exit 1. *)
let run_compare env =
  match !compare_config with
  | None -> ()
  | Some cfg ->
    let dir = Option.get !compare_challenge and out = Option.get !compare_out in
    let answer_deps = CheckLibrary.interned_deps () in
    (* The challenge directory stands in for the answer's directory under
       each root that an answer library named on the command line lives
       under. A root that only a pre-checked library or another shared tree
       uses is left alone: the challenge directory does not hold it.

       Both selection forms that name a library to CHECK count: the
       positional names ([compile_list], checked with their dependencies)
       and -norec ([norec_list], checked alone), which is the form the
       grading side sends. -admit names a library to load WITHOUT
       checking it and never selects an answer library, so [admit_list]
       is left out -- it also holds the config's pre-checked libraries,
       which are exactly the ones the challenge does not stand in for. *)
    let name_of = function
      | CheckLibrary.LogicalFile p ->
        String.concat "." (List.rev p.CheckLibrary.dirpath @ [p.CheckLibrary.basename])
      | CheckLibrary.PhysicalFile f -> Filename.remove_extension (Filename.basename f)
    in
    let checked_names =
      List.map name_of !compile_list @ List.map name_of !norec_list
    in
    let substitutes root =
      let r = DirPath.to_string root in
      List.exists (fun n -> String.equal n r || CString.is_prefix (r ^ ".") n) checked_names
    in
    (* A library under one of those roots is the answer's own: the challenge
       directory holds its counterpart. Every other library the answer
       loaded is a shared one -- the image's installed libraries -- and the
       challenge environment loads the same ones, so that a constraint one
       of them carries is not read as a constraint the answer invented.

       The premise is the one R5 of dispatch://BET-894 already states: every
       answer library is CHECKED in this run. A library of the answer's own
       therefore lives under a root some checked name lives under, which is
       a root the challenge stands in for; what is left over is the image's.
       A run that loaded an answer library without checking it would be
       refused long before this, and nothing here weakens that. *)
    let under_challenge_root lib =
      let l = DirPath.to_string lib in
      List.exists (fun (_, rocq_root) ->
          let r = DirPath.to_string rocq_root in
          substitutes rocq_root && (String.equal l r || CString.is_prefix (r ^ ".") l))
        !user_includes
    in
    (* The bound roots the challenge does NOT stand in for. The answer's
       build can write under one of them, so the comparator refuses a run
       that loaded a library from one unless the config pins it. *)
    let open_roots =
      CList.map_filter (fun (unix_path, rocq_root) ->
          if substitutes rocq_root then None else Some (rocq_root, unix_path))
        !user_includes
    in
    (* A -Q that binds one of the image's own top-level names, or the empty
       root, puts the answer's directory where a library the challenge reads
       from the image is looked up: the two sides would then read different
       files under one name, and the one the answer wrote would decide. The
       empty root binds EVERY name. Refused outright, because no config can
       make it safe, and nothing a graded run does needs it: the route binds
       one root, the project's own. *)
    List.iter (fun (unix_path, rocq_root) ->
        let head = match List.rev (DirPath.repr rocq_root) with
          | [] -> None
          | id :: _ -> Some (Id.to_string id)
        in
        match head with
        | None ->
          fatal_error
            (str ("The directory " ^ unix_path ^ " is bound to the empty root, which binds \
                   every library name the image serves. A -compare run refuses it."))
            1
        | Some h when List.exists (String.equal h) !image_roots ->
          fatal_error
            (str ("The directory " ^ unix_path ^ " is bound to " ^ DirPath.to_string rocq_root ^
                  ", a name the image's own load path serves. A -compare run refuses it: the \
                   two sides would read different files under one library name."))
            1
        | Some _ -> ())
      !user_includes;
    try
      let t =
        Check_compare.prepare cfg ~dir ~out ~under_challenge_root ~open_roots
          ~bound_dirs:(List.map fst !user_includes)
          ~add_challenge_load_path:(fun () ->
              List.iter (fun (_, rocq_root) ->
                  if substitutes rocq_root then add_rec_path ~unix_path:dir ~rocq_root)
                !user_includes)
      in
      Check_compare.run t env CheckLibrary.indirect_accessor (make_senv ()) ~answer_deps
    with e -> fatal_exn e


(* Prototype G (measurement only, never merged): ROCQCHK_MAIN_MINOR_WORDS and
   ROCQCHK_MAIN_SPACE_OVERHEAD, when set, replace the main process's minor
   heap size and space overhead from the start. Unset, the base's settings. *)
let tune_main_gc () =
  let env_int v = Option.bind (Sys.getenv_opt v) int_of_string_opt in
  let gc = Gc.get () in
  let gc = match env_int "ROCQCHK_MAIN_MINOR_WORDS" with
    | Some n -> { gc with Gc.minor_heap_size = n } | None -> gc in
  let gc = match env_int "ROCQCHK_MAIN_SPACE_OVERHEAD" with
    | Some n -> { gc with Gc.space_overhead = n } | None -> gc in
  Gc.set gc

let main () =
  tune_main_gc ();
  let senv = init() in
  Check_stat.start_summary !Check_stat.output_context;
  let records_on = match !statement_report with
    | Some _ when CheckWorkers.parallel () && refs_enabled () -> start_refs_records ()
    | Some _ | None -> false
  in
  (match !statement_report with
   | Some requests when not records_on && report_child_enabled () ->
     CheckLibrary.set_final_env_hook (start_report_child requests)
   | Some _ | None -> ());
  let senv, opac = run senv in
  let env = Safe_typing.env_of_safe_env senv in
  let records = collect_refs_records () in
  Option.iter (print_report ?records env) !statement_report;
  run_compare env;
  (* A summary the walk of mod_impl.ml could not complete is refused with a
     user error, reported as a check's error is. *)
  (try Check_stat.stats env opac with e -> fatal_exn e);
  exit 0
