(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The comparator of [rocqchk -compare CONFIG -challenge DIR -compare-out FILE].

    The challenge is a set of [.vo] files that setup compiled and checked, and
    the answer is the tree the agent handed back, compiled at the same paths
    and under the same library names. [rocqchk] checks the answer with the
    kernel as it does today; this module loads the challenge into a second
    environment without a check, compares every declaration of the challenge
    files' closure, but those of the pre-checked libraries and of the shared
    libraries they rest on, with the answer declaration of the same kernel
    name, computes each named theorem's axiom closure, and writes a JSON
    verdict.

    The comparison is structural: two declarations are equal when their terms
    are the same after a one-to-one renaming of universe levels and, inside
    the signature of a functor, of its parameters. There is no conversion and
    no reduction, and no constant is unfolded. Whether the answer may fill a
    constant that the challenge leaves without a body depends on the sort of
    the type the challenge states for it ([stated_sort]), not on that type
    reduced ([eq_const_body]). *)

open Util
open Names
open Declarations

(************************************************************************)
(** {6 SHA-256}

    FIPS 180-4's SHA-256, tested against the standard vectors in
    test-suite/misc/compare.sh (case [sha256]), which also compares it with
    [sha256sum] on every file the suite builds. The checker also links
    clib's [Sha256] (clib/sha256.ml, through [boot]), which the module below
    shadows in this file. clib's [string] and [file] give the same digests
    as [hex_of_string] and [hex_of_file], also as 64 lowercase hexadecimal
    digits. The one difference is a file that is not a regular file or
    cannot be read: clib's [file] opens it, and raises [Sys_error], blocks
    or reads without end, and [hex_of_file] raises a user error, one of its
    own, before opening it, for a file that is not a regular file, and the
    system's message for a file that does not open or fails once open. *)

module Sha256 : sig
  val hex_of_string : string -> string
  val hex_of_file : string -> string
end = struct

  let k = [|
    0x428a2f98; 0x71374491; 0xb5c0fbcf; 0xe9b5dba5;
    0x3956c25b; 0x59f111f1; 0x923f82a4; 0xab1c5ed5;
    0xd807aa98; 0x12835b01; 0x243185be; 0x550c7dc3;
    0x72be5d74; 0x80deb1fe; 0x9bdc06a7; 0xc19bf174;
    0xe49b69c1; 0xefbe4786; 0x0fc19dc6; 0x240ca1cc;
    0x2de92c6f; 0x4a7484aa; 0x5cb0a9dc; 0x76f988da;
    0x983e5152; 0xa831c66d; 0xb00327c8; 0xbf597fc7;
    0xc6e00bf3; 0xd5a79147; 0x06ca6351; 0x14292967;
    0x27b70a85; 0x2e1b2138; 0x4d2c6dfc; 0x53380d13;
    0x650a7354; 0x766a0abb; 0x81c2c92e; 0x92722c85;
    0xa2bfe8a1; 0xa81a664b; 0xc24b8b70; 0xc76c51a3;
    0xd192e819; 0xd6990624; 0xf40e3585; 0x106aa070;
    0x19a4c116; 0x1e376c08; 0x2748774c; 0x34b0bcb5;
    0x391c0cb3; 0x4ed8aa4a; 0x5b9cca4f; 0x682e6ff3;
    0x748f82ee; 0x78a5636f; 0x84c87814; 0x8cc70208;
    0x90befffa; 0xa4506ceb; 0xbef9a3f7; 0xc67178f2 |]

  let mask = 0xffffffff
  let rotr x n = ((x lsr n) lor (x lsl (32 - n))) land mask

  type t = {
    h : int array;
    buf : Bytes.t;        (* a partial block, [len] bytes of it *)
    mutable len : int;
    mutable total : int;  (* bytes fed so far *)
    w : int array;
  }

  let create () = {
    h = [| 0x6a09e667; 0xbb67ae85; 0x3c6ef372; 0xa54ff53a;
           0x510e527f; 0x9b05688c; 0x1f83d9ab; 0x5be0cd19 |];
    buf = Bytes.create 64;
    len = 0;
    total = 0;
    w = Array.make 64 0;
  }

  let block st b off =
    let w = st.w in
    for i = 0 to 15 do
      let j = off + 4 * i in
      w.(i) <-
        (Char.code (Bytes.get b j) lsl 24)
        lor (Char.code (Bytes.get b (j + 1)) lsl 16)
        lor (Char.code (Bytes.get b (j + 2)) lsl 8)
        lor Char.code (Bytes.get b (j + 3))
    done;
    for i = 16 to 63 do
      let x = w.(i - 15) and y = w.(i - 2) in
      let s0 = rotr x 7 lxor rotr x 18 lxor (x lsr 3) in
      let s1 = rotr y 17 lxor rotr y 19 lxor (y lsr 10) in
      w.(i) <- (w.(i - 16) + s0 + w.(i - 7) + s1) land mask
    done;
    let a = ref st.h.(0) and b1 = ref st.h.(1) and c = ref st.h.(2) and d = ref st.h.(3) in
    let e = ref st.h.(4) and f = ref st.h.(5) and g = ref st.h.(6) and h = ref st.h.(7) in
    for i = 0 to 63 do
      let s1 = rotr !e 6 lxor rotr !e 11 lxor rotr !e 25 in
      let ch = (!e land !f) lxor (lnot !e land mask land !g) in
      let t1 = (!h + s1 + ch + k.(i) + w.(i)) land mask in
      let s0 = rotr !a 2 lxor rotr !a 13 lxor rotr !a 22 in
      let maj = (!a land !b1) lxor (!a land !c) lxor (!b1 land !c) in
      let t2 = (s0 + maj) land mask in
      h := !g; g := !f; f := !e; e := (!d + t1) land mask;
      d := !c; c := !b1; b1 := !a; a := (t1 + t2) land mask
    done;
    st.h.(0) <- (st.h.(0) + !a) land mask;
    st.h.(1) <- (st.h.(1) + !b1) land mask;
    st.h.(2) <- (st.h.(2) + !c) land mask;
    st.h.(3) <- (st.h.(3) + !d) land mask;
    st.h.(4) <- (st.h.(4) + !e) land mask;
    st.h.(5) <- (st.h.(5) + !f) land mask;
    st.h.(6) <- (st.h.(6) + !g) land mask;
    st.h.(7) <- (st.h.(7) + !h) land mask

  let feed st b off len =
    st.total <- st.total + len;
    let off = ref off and len = ref len in
    if st.len > 0 then begin
      let take = min (64 - st.len) !len in
      Bytes.blit b !off st.buf st.len take;
      st.len <- st.len + take;
      off := !off + take;
      len := !len - take;
      if st.len = 64 then (block st st.buf 0; st.len <- 0)
    end;
    while !len >= 64 do
      block st b !off;
      off := !off + 64;
      len := !len - 64
    done;
    if !len > 0 then begin
      Bytes.blit b !off st.buf 0 !len;
      st.len <- !len
    end

  let finish st =
    let bits = st.total * 8 in
    let pad = Bytes.make 72 '\000' in
    Bytes.set pad 0 '\x80';
    (* enough zero bytes to leave room for the 8-byte length at a block end *)
    let n = if st.len < 56 then 56 - st.len else 120 - st.len in
    for i = 0 to 7 do
      Bytes.set pad (n + i) (Char.chr ((bits lsr (8 * (7 - i))) land 0xff))
    done;
    feed st pad 0 (n + 8);
    let b = Buffer.create 64 in
    Array.iter (fun x -> Buffer.add_string b (Printf.sprintf "%08x" x)) st.h;
    Buffer.contents b

  let hex_of_string s =
    let st = create () in
    feed st (Bytes.of_string s) 0 (String.length s);
    finish st

  (* A file that is not a regular one, as [Unix.stat] sees it through links,
     is refused before it is opened: a FIFO would block the open, and a link
     to /dev/zero would never end. The message is the system's without the
     file's name, which [open_in_bin]'s starts with: each caller names the
     file itself. *)
  let hex_of_file f =
    let refuse e = CErrors.user_err (Pp.str e) in
    let not_regular kind = refuse ("Is " ^ kind ^ ", not a regular file") in
    match (Unix.stat f).Unix.st_kind with
    | exception Unix.Unix_error (e, _, _) -> refuse (Unix.error_message e)
    | Unix.S_DIR -> not_regular "a directory"
    | Unix.S_CHR -> not_regular "a character device"
    | Unix.S_BLK -> not_regular "a block device"
    | Unix.S_LNK -> not_regular "a symbolic link"
    | Unix.S_FIFO -> not_regular "a named pipe"
    | Unix.S_SOCK -> not_regular "a socket"
    | Unix.S_REG ->
      try
        let ch = open_in_bin f in
        Fun.protect ~finally:(fun () -> close_in_noerr ch) (fun () ->
            let st = create () in
            let b = Bytes.create 65536 in
            let rec loop () =
              let n = input ch b 0 65536 in
              if n > 0 then (feed st b 0 n; loop ())
            in
            loop ();
            finish st)
      with Sys_error e ->
        let named = f ^ ": " in
        if CString.is_prefix named e then
          refuse (String.sub e (String.length named) (String.length e - String.length named))
        else refuse e
end

(* [rocqchk -sha256 FILE]: the error names the file, as every other caller
   of [Sha256.hex_of_file] does. *)
let sha256_of_file f =
  try Sha256.hex_of_file f
  with CErrors.UserError msg ->
    CErrors.user_err Pp.(str ("The file " ^ f ^ " cannot be read: ") ++ msg ++ str ".")

(************************************************************************)
(** {6 JSON}

    A reader and a writer of its own. The checker links no JSON reader. The
    one JSON printer it links, [NewProfile.MiniJson] (lib/newProfile.ml),
    copies the bytes above 127 of a string as they are, so a name that is
    not UTF-8 would make the verdict invalid JSON. The writer below escapes
    every such byte and every control character (see [escape]), so any name
    stays one valid JSON string, a line break included. The reader is
    strict, because the config decides a grade: a duplicate key, a byte
    after the top-level value, a byte sequence that is not UTF-8, a control
    character in a string, a leading zero or a number that is not an
    integer are each an error. *)

module Json = struct

  type t =
    | Null
    | Bool of bool
    | Int of int
    | Str of string
    | List of t list
    | Obj of (string * t) list

  let error msg = CErrors.user_err Pp.(str ("The comparator config is not valid JSON: " ^ msg ^ "."))

  (* The whole input is UTF-8 or the file is refused. *)
  let check_utf8 s =
    let n = String.length s in
    let byte i = Char.code s.[i] in
    let cont i = i < n && byte i land 0xc0 = 0x80 in
    let rec loop i =
      if i >= n then ()
      else
        let c = byte i in
        if c < 0x80 then loop (i + 1)
        else if c land 0xe0 = 0xc0 then
          if c < 0xc2 || not (cont (i + 1)) then error "invalid UTF-8"
          else loop (i + 2)
        else if c land 0xf0 = 0xe0 then
          if not (cont (i + 1) && cont (i + 2)) then error "invalid UTF-8"
          else
            let cp = ((c land 0x0f) lsl 12) lor ((byte (i + 1) land 0x3f) lsl 6)
                     lor (byte (i + 2) land 0x3f) in
            if cp < 0x800 || (cp >= 0xd800 && cp <= 0xdfff) then error "invalid UTF-8"
            else loop (i + 3)
        else if c land 0xf8 = 0xf0 then
          if not (cont (i + 1) && cont (i + 2) && cont (i + 3)) then error "invalid UTF-8"
          else
            let cp = ((c land 0x07) lsl 18) lor ((byte (i + 1) land 0x3f) lsl 12)
                     lor ((byte (i + 2) land 0x3f) lsl 6) lor (byte (i + 3) land 0x3f) in
            if cp < 0x10000 || cp > 0x10ffff then error "invalid UTF-8"
            else loop (i + 4)
        else error "invalid UTF-8"
    in
    loop 0

  let add_utf8 b cp =
    if cp < 0x80 then Buffer.add_char b (Char.chr cp)
    else if cp < 0x800 then begin
      Buffer.add_char b (Char.chr (0xc0 lor (cp lsr 6)));
      Buffer.add_char b (Char.chr (0x80 lor (cp land 0x3f)))
    end else if cp < 0x10000 then begin
      Buffer.add_char b (Char.chr (0xe0 lor (cp lsr 12)));
      Buffer.add_char b (Char.chr (0x80 lor ((cp lsr 6) land 0x3f)));
      Buffer.add_char b (Char.chr (0x80 lor (cp land 0x3f)))
    end else begin
      Buffer.add_char b (Char.chr (0xf0 lor (cp lsr 18)));
      Buffer.add_char b (Char.chr (0x80 lor ((cp lsr 12) land 0x3f)));
      Buffer.add_char b (Char.chr (0x80 lor ((cp lsr 6) land 0x3f)));
      Buffer.add_char b (Char.chr (0x80 lor (cp land 0x3f)))
    end

  let parse s =
    check_utf8 s;
    let n = String.length s in
    let pos = ref 0 in
    let peek () = if !pos < n then Some s.[!pos] else None in
    let advance () = incr pos in
    let rec skip () =
      match peek () with
      | Some (' ' | '\t' | '\n' | '\r') -> advance (); skip ()
      | _ -> ()
    in
    let expect c =
      match peek () with
      | Some c' when c' = c -> advance ()
      | _ -> error (Printf.sprintf "expected %c at byte %d" c !pos)
    in
    let hex4 () =
      if !pos + 4 > n then error "truncated \\u escape";
      let v = ref 0 in
      for _ = 1 to 4 do
        let c = s.[!pos] in
        let d =
          if c >= '0' && c <= '9' then Char.code c - 48
          else if c >= 'a' && c <= 'f' then Char.code c - 87
          else if c >= 'A' && c <= 'F' then Char.code c - 55
          else error "bad \\u escape"
        in
        v := (!v * 16) + d;
        advance ()
      done;
      !v
    in
    let string_lit () =
      expect '"';
      let b = Buffer.create 32 in
      let rec loop () =
        match peek () with
        | None -> error "unterminated string"
        | Some '"' -> advance (); Buffer.contents b
        | Some '\\' ->
          advance ();
          (match peek () with
           | None -> error "unterminated escape"
           | Some c ->
             advance ();
             (match c with
              | '"' -> Buffer.add_char b '"'
              | '\\' -> Buffer.add_char b '\\'
              | '/' -> Buffer.add_char b '/'
              | 'b' -> Buffer.add_char b '\b'
              | 'f' -> Buffer.add_char b '\012'
              | 'n' -> Buffer.add_char b '\n'
              | 'r' -> Buffer.add_char b '\r'
              | 't' -> Buffer.add_char b '\t'
              | 'u' ->
                let cp = hex4 () in
                let cp =
                  if cp >= 0xd800 && cp <= 0xdbff then begin
                    if !pos + 1 < n && s.[!pos] = '\\' && s.[!pos + 1] = 'u' then begin
                      advance (); advance ();
                      let lo = hex4 () in
                      if lo < 0xdc00 || lo > 0xdfff then error "bad surrogate pair";
                      0x10000 + ((cp - 0xd800) lsl 10) + (lo - 0xdc00)
                    end else error "lone surrogate"
                  end
                  else if cp >= 0xdc00 && cp <= 0xdfff then error "lone surrogate"
                  else cp
                in
                add_utf8 b cp
              | _ -> error "unknown escape");
             loop ())
        | Some c when Char.code c < 0x20 -> error "control character in a string"
        | Some c -> advance (); Buffer.add_char b c; loop ()
      in
      loop ()
    in
    let number () =
      let start = !pos in
      if peek () = Some '-' then advance ();
      let digits_start = !pos in
      let rec digits () =
        match peek () with
        | Some c when c >= '0' && c <= '9' -> advance (); digits ()
        | _ -> ()
      in
      digits ();
      if !pos = digits_start then error "expected a number";
      if !pos - digits_start > 1 && s.[digits_start] = '0' then error "leading zero in a number";
      (match peek () with
       | Some ('.' | 'e' | 'E') -> error "only integers are accepted"
       | _ -> ());
      let lit = String.sub s start (!pos - start) in
      match int_of_string_opt lit with
      | Some i -> Int i
      | None -> error "the number does not fit"
    in
    let literal lit v =
      let l = String.length lit in
      if !pos + l <= n && String.sub s !pos l = lit then (pos := !pos + l; v)
      else error "unknown literal"
    in
    let rec value () =
      skip ();
      match peek () with
      | None -> error "the file is empty"
      | Some '{' -> obj ()
      | Some '[' -> arr ()
      | Some '"' -> Str (string_lit ())
      | Some 't' -> literal "true" (Bool true)
      | Some 'f' -> literal "false" (Bool false)
      | Some 'n' -> literal "null" Null
      | Some _ -> number ()
    and obj () =
      expect '{';
      skip ();
      if peek () = Some '}' then (advance (); Obj [])
      else
        let rec loop acc =
          skip ();
          let key = string_lit () in
          if List.mem_assoc key acc then error ("the key " ^ key ^ " appears twice");
          skip ();
          expect ':';
          let v = value () in
          let acc = (key, v) :: acc in
          skip ();
          match peek () with
          | Some ',' -> advance (); loop acc
          | Some '}' -> advance (); Obj (List.rev acc)
          | _ -> error "expected , or } in an object"
        in
        loop []
    and arr () =
      expect '[';
      skip ();
      if peek () = Some ']' then (advance (); List [])
      else
        let rec loop acc =
          let v = value () in
          let acc = v :: acc in
          skip ();
          match peek () with
          | Some ',' -> advance (); loop acc
          | Some ']' -> advance (); List (List.rev acc)
          | _ -> error "expected , or ] in an array"
        in
        loop []
    in
    let v = value () in
    skip ();
    if !pos <> n then error "there are bytes after the top-level value";
    v

  let parse_file f =
    let ch = try open_in_bin f with Sys_error e -> CErrors.user_err (Pp.str e) in
    let s =
      Fun.protect ~finally:(fun () -> close_in_noerr ch) (fun () ->
          really_input_string ch (in_channel_length ch))
    in
    parse s

  (* The writer. Every byte above 127 is written as a \u escape of the code
     point it starts, and a byte that is not part of a valid UTF-8 sequence as
     U+FFFD, so the output is valid JSON whatever a name holds. *)
  let escape b s =
    let n = String.length s in
    let byte i = Char.code s.[i] in
    let cont i = i < n && byte i land 0xc0 = 0x80 in
    let unicode cp =
      if cp < 0x10000 then Buffer.add_string b (Printf.sprintf "\\u%04x" cp)
      else begin
        let cp = cp - 0x10000 in
        Buffer.add_string b (Printf.sprintf "\\u%04x" (0xd800 lor (cp lsr 10)));
        Buffer.add_string b (Printf.sprintf "\\u%04x" (0xdc00 lor (cp land 0x3ff)))
      end
    in
    let rec loop i =
      if i >= n then ()
      else
        let c = byte i in
        if c = Char.code '"' then (Buffer.add_string b "\\\""; loop (i + 1))
        else if c = Char.code '\\' then (Buffer.add_string b "\\\\"; loop (i + 1))
        else if c = 8 then (Buffer.add_string b "\\b"; loop (i + 1))
        else if c = 12 then (Buffer.add_string b "\\f"; loop (i + 1))
        else if c = 10 then (Buffer.add_string b "\\n"; loop (i + 1))
        else if c = 13 then (Buffer.add_string b "\\r"; loop (i + 1))
        else if c = 9 then (Buffer.add_string b "\\t"; loop (i + 1))
        else if c < 0x20 || c = 0x7f then (unicode c; loop (i + 1))
        else if c < 0x80 then (Buffer.add_char b s.[i]; loop (i + 1))
        else if c land 0xe0 = 0xc0 && c >= 0xc2 && cont (i + 1) then
          (unicode (((c land 0x1f) lsl 6) lor (byte (i + 1) land 0x3f)); loop (i + 2))
        else if c land 0xf0 = 0xe0 && cont (i + 1) && cont (i + 2) then
          (unicode (((c land 0x0f) lsl 12) lor ((byte (i + 1) land 0x3f) lsl 6)
                    lor (byte (i + 2) land 0x3f));
           loop (i + 3))
        else if c land 0xf8 = 0xf0 && cont (i + 1) && cont (i + 2) && cont (i + 3) then
          (unicode (((c land 0x07) lsl 18) lor ((byte (i + 1) land 0x3f) lsl 12)
                    lor ((byte (i + 2) land 0x3f) lsl 6) lor (byte (i + 3) land 0x3f));
           loop (i + 4))
        else (unicode 0xfffd; loop (i + 1))
    in
    loop 0

  let rec write b = function
    | Null -> Buffer.add_string b "null"
    | Bool true -> Buffer.add_string b "true"
    | Bool false -> Buffer.add_string b "false"
    | Int i -> Buffer.add_string b (string_of_int i)
    | Str s -> Buffer.add_char b '"'; escape b s; Buffer.add_char b '"'
    | List l ->
      Buffer.add_char b '[';
      List.iteri (fun i v -> if i > 0 then Buffer.add_char b ','; write b v) l;
      Buffer.add_char b ']'
    | Obj l ->
      Buffer.add_char b '{';
      List.iteri (fun i (k, v) ->
          if i > 0 then Buffer.add_char b ',';
          Buffer.add_char b '"'; escape b k; Buffer.add_string b "\":";
          write b v) l;
      Buffer.add_char b '}'

  let to_string v = let b = Buffer.create 1024 in write b v; Buffer.contents b
end

(************************************************************************)
(** {6 The config} *)

type theorem = {
  th_name : string;
  th_axioms : string list option;  (** replaces the global list for this one *)
}

(** [pc_library] is the library's name, parsed once by [read_config]. *)
type prechecked = { pc_library : DirPath.t; pc_sha256 : string }

type challenge_file = { cf_path : string; cf_sha256 : string }

type config = {
  cfg_theorems : theorem list;
  cfg_axioms : string list;
  cfg_flags : (string * string option) list;
      (** (kind, object): [None] is the kind on any object *)
  cfg_rewrite_rules : bool;
  cfg_prechecked : prechecked list;
  cfg_challenge_files : challenge_file list;
}

let answer_universe_constraints = "answer-universe-constraints"

(* A pre-checked library loads through the existing -admit path: rocqchk adds
   it to the admit list once [check_prechecked_files] has checked its pin, so
   the config is the only place that names it. *)
let prechecked_libraries cfg = List.map (fun p -> p.pc_library) cfg.cfg_prechecked

let cfg_error msg = CErrors.user_err Pp.(str ("The comparator config is wrong: " ^ msg ^ "."))

(* [String.split_on_char] gives at least one component, and [Id.of_string]
   refuses an empty one, so the empty name too. *)
let dirpath_of_string s =
  DirPath.make (List.rev_map Id.of_string (String.split_on_char '.' s))

let fields where keys l =
  List.iter (fun (k, _) ->
      if not (List.mem k keys) then
        cfg_error ("the key " ^ k ^ " of " ^ where ^ " is not a key this version knows"))
    l

let get l k = List.assoc_opt k l

let as_string where = function
  | Json.Str s -> s
  | _ -> cfg_error (where ^ " must be a string")

let as_bool where = function
  | Json.Bool b -> b
  | _ -> cfg_error (where ^ " must be true or false")

let as_list where = function
  | Json.List l -> l
  | _ -> cfg_error (where ^ " must be a list")

let as_obj where = function
  | Json.Obj l -> l
  | _ -> cfg_error (where ^ " must be an object")

let string_list where v = List.map (as_string (where ^ "'s entries")) (as_list where v)

let read_config file =
  let top = as_obj "the config" (Json.parse_file file) in
  fields "the config"
    ["theorems"; "permitted_axioms"; "tolerated_flags"; "rewrite_rules";
     "prechecked"; "challenge_files"] top;
  let theorems =
    match get top "theorems" with
    | None -> cfg_error "the config has no theorems"
    | Some v ->
      List.map (fun e ->
          let e = as_obj "a theorem" e in
          fields "a theorem" ["name"; "permitted_axioms"] e;
          let name = match get e "name" with
            | None -> cfg_error "a theorem has no name"
            | Some v -> as_string "a theorem's name" v
          in
          { th_name = name;
            th_axioms = Option.map (string_list "a theorem's permitted_axioms")
                (get e "permitted_axioms") })
        (as_list "theorems" v)
  in
  (* A config that names no theorem grades nothing, and a name twice over
     would write two records a reader cannot tell apart. *)
  if CList.is_empty theorems then cfg_error "the config names no theorem";
  let rec no_repeat = function
    | [] -> ()
    | th :: tl ->
      if List.exists (fun o -> String.equal o.th_name th.th_name) tl then
        cfg_error ("the theorem " ^ th.th_name ^ " is named twice");
      no_repeat tl
  in
  no_repeat theorems;
  let axioms = match get top "permitted_axioms" with
    | None -> [] | Some v -> string_list "permitted_axioms" v
  in
  (* A tolerated flag names the kind, and may name the object it is
     tolerated on. With an object, a relaxed condition the standard library
     rests on does not tolerate the same condition in the agent's own
     declaration.

     [assumed-positive], [unsafe-fixpoint] and [type-in-type] are refused
     with an object or without ([never_tolerated]): each is how a proof of
     False is written, and the route this comparator replaces denies it
     whatever the object (grading-tools [_axiom_kinds.py],
     [_ALWAYS_ALLOWED_KINDS]). The check comes before the object is read,
     so both forms reach it.

     [unchecked-eliminations] is how a proof of False is written too, but
     the replaced route vouches for one name at a time, so it is tolerated
     on a named object alone, and a kind-only entry for it is refused.

     [indices-not-mattering] and [uip] take both forms. Without an object,
     [indices-not-mattering] tolerates the kind wherever it appears: every
     inductive of an image built without [-indices-matter] may carry it, and
     the replaced route always allows it. The config has no [allow_uip]
     input, so a kind-only [uip] entry is that switch: writing it is the
     task saying definitional UIP is allowed wherever its proof reaches. An
     entry with an object allows it on that object alone, when the object is
     the task's declaration, and leaving both out is the task saying it is
     not allowed.

     [answer-universe-constraints] is kind-only, and has a narrower meaning:
     it skips only the answer-to-challenge universe comparison. It names no
     declaration, so an object would not make the requested relaxation more
     precise, and an entry with one is refused. *)
  let never_tolerated = ["assumed-positive"; "unsafe-fixpoint"; "type-in-type"] in
  let kind_only_allowed =
    ["indices-not-mattering"; "uip"; answer_universe_constraints]
  in
  let flags = match get top "tolerated_flags" with
    | None -> []
    | Some v ->
      List.map (fun e ->
          let e = as_obj "a tolerated flag" e in
          fields "a tolerated flag" ["kind"; "object"] e;
          let k = match get e "kind" with
            | None -> cfg_error "a tolerated flag needs a kind"
            | Some k -> as_string "a tolerated flag's kind" k
          in
          if List.exists (String.equal k) never_tolerated then
            cfg_error ("the tolerated flag " ^ k ^ " is refused with an object or without: " ^
                       "the route this comparator replaces denies it whatever the object");
          match get e "object" with
          | Some o ->
            if String.equal k answer_universe_constraints then
              cfg_error ("the tolerated flag " ^ answer_universe_constraints ^
                         " does not name an object");
            k, Some (as_string "a tolerated flag's object" o)
          | None ->
            if not (List.exists (String.equal k) kind_only_allowed) then
              cfg_error ("the tolerated flag " ^ k ^ " needs an object: only " ^
                         "indices-not-mattering and uip tolerate every object; " ^
                         answer_universe_constraints ^ " is a global check");
            k, None)
        (as_list "tolerated_flags" v)
  in
  let rewrite_rules = match get top "rewrite_rules" with
    | None -> false | Some v -> as_bool "rewrite_rules" v
  in
  let prechecked = match get top "prechecked" with
    | None -> []
    | Some v ->
      List.map (fun e ->
          let e = as_obj "a prechecked entry" e in
          fields "a prechecked entry" ["library"; "sha256"] e;
          match get e "library", get e "sha256" with
          | Some l, Some h ->
            { pc_library = dirpath_of_string (as_string "a prechecked library" l);
              pc_sha256 = as_string "a prechecked sha256" h }
          | _ -> cfg_error "a prechecked entry needs a library and a sha256")
        (as_list "prechecked" v)
  in
  let challenge_files = match get top "challenge_files" with
    | None -> cfg_error "the config has no challenge_files"
    | Some v ->
      List.map (fun e ->
          let e = as_obj "a challenge file" e in
          fields "a challenge file" ["path"; "sha256"] e;
          match get e "path", get e "sha256" with
          | Some p, Some h ->
            { cf_path = as_string "a challenge file's path" p;
              cf_sha256 = as_string "a challenge file's sha256" h }
          | _ -> cfg_error "a challenge file needs a path and a sha256")
        (as_list "challenge_files" v)
  in
  if CList.is_empty challenge_files then cfg_error "challenge_files is empty";
  { cfg_theorems = theorems; cfg_axioms = axioms; cfg_flags = flags;
    cfg_rewrite_rules = rewrite_rules; cfg_prechecked = prechecked;
    cfg_challenge_files = challenge_files }

(************************************************************************)
(** {6 The universe level map}

    One map for the whole run, a bijection between the challenge's
    monomorphic levels and the answer's. It is seeded ([seed_umap]) with the
    identity on every level that both graphs hold of a library that is one
    file for both sides ([one_file]) -- a pre-checked library, or a SHARED
    one, outside the roots the challenge stands in for and not pre-checked,
    whose file passed [check_provenance] -- and of every library of the
    answer's pre-checked closure ([prechecked_closure]: the pre-checked
    libraries and every library they rest on, each of which [run] has
    refused unless it is pre-checked, pinned by its sha256 as a challenge
    file or the image's own). So a constraint between a level of the
    challenge's own and one of those is a constraint between two mapped
    levels, which the constraint check ([check_constraints]) sees. Without
    the seed a level no compared term names is not in the map at all, and a
    constraint reaching it is passed over: an opaque body is never compared,
    so a challenge proof's own constraint on such a level would be lost. The
    rest of the map is built while the declarations are compared.

    A level of a polymorphic context is a [Level.var], bound by position, so
    it is compared by its index and never enters the map.

    A functor parameter is named by a counter of the process that compiled
    the functor ([MBId.make]), which the two sides need not share. While the
    signature of a functor is compared ([eq_signature]), the map also holds
    the substitution in force: each challenge parameter of the functors
    being compared, to the answer's parameter of the same position. Each
    challenge name is renamed by it before it is compared ([rename]), as
    the kernel's subtyping check ([Subtyping.check_modtypes]) renames a
    functor's parameters. Outside a functor there is no substitution and no
    name is renamed. *)

type umap = {
  fwd : Univ.Level.t Univ.Level.Map.t;  (** challenge to answer *)
  bwd : Univ.Level.t Univ.Level.Map.t;  (** answer to challenge *)
  params : Mod_subst.substitution option;
      (** the challenge's parameters of the functors whose signatures are
          being compared, each to the answer's; [None] outside them *)
  bound : MBId.Set.t;  (** the answer's parameters of those functors *)
}

let empty_umap = {
  fwd = Univ.Level.Map.empty; bwd = Univ.Level.Map.empty;
  params = None; bound = MBId.Set.empty;
}

(* The challenge's name [x], with each functor parameter it lies under
   renamed to the answer's ([umap.params]); [f] substitutes a name. *)
let rename m f x = match m.params with
  | None -> x
  | Some s -> f s x

type diff = string

exception Diff of diff

let diff fmt = Printf.ksprintf (fun s -> raise (Diff s)) fmt

(* A universe whose levels no comparison so far has mapped, and that one
   pass cannot map alone (two entries of one increment), or a constraint of
   a template context on a global level the map does not hold yet. The
   declaration is compared again once the others have been, since a later
   declaration -- the one that introduced those levels -- may map them. *)
exception Undecided of diff

let level_name u = Univ.Level.to_string u

let add_level m u v =
  { m with fwd = Univ.Level.Map.add u v m.fwd; bwd = Univ.Level.Map.add v u m.bwd }

let map_level m u v =
  match Univ.Level.var_index u, Univ.Level.var_index v with
  | Some i, Some j ->
    if i <> j then diff "bound universe %s against %s" (level_name u) (level_name v);
    m
  | Some _, None | None, Some _ ->
    diff "universe %s against %s" (level_name u) (level_name v)
  | None, None ->
    match Univ.Level.name u, Univ.Level.name v with
    | None, _ | _, None ->
      (* Set and the other levels with no global name stand for themselves. *)
      if not (Univ.Level.equal u v) then
        diff "universe %s against %s" (level_name u) (level_name v);
      m
    | Some _, Some _ ->
      match Univ.Level.Map.find_opt u m.fwd with
      | Some v' ->
        if not (Univ.Level.equal v v') then
          diff "universe %s is already mapped to %s, not to %s"
            (level_name u) (level_name v') (level_name v);
        m
      | None ->
        match Univ.Level.Map.find_opt v m.bwd with
        | Some u' ->
          diff "universe %s is already the image of %s, so %s cannot map to it"
            (level_name v) (level_name u') (level_name u)
        | None -> add_level m u v

(* A universe is a maximum of levels raised by a constant. Entries whose level
   the map already fixes are matched by that level; the rest are matched by
   their increment, in order. *)
let map_universe m u v =
  let lu = Univ.Universe.repr u and lv = Univ.Universe.repr v in
  if List.length lu <> List.length lv then
    diff "universe %s against %s"
      (Pp.string_of_ppcmds (Univ.Universe.raw_pr u))
      (Pp.string_of_ppcmds (Univ.Universe.raw_pr v));
  let m = ref m in
  let rest = ref lv in
  let fresh = ref [] in
  let take_level target n =
    let rec go seen = function
      | [] ->
        diff "universe %s has no %s+%d" (Pp.string_of_ppcmds (Univ.Universe.raw_pr v))
          (level_name target) n
      | (l2, n2) :: tl when Univ.Level.equal l2 target && Int.equal n2 n ->
        List.rev_append seen tl
      | e :: tl -> go (e :: seen) tl
    in
    rest := go [] !rest
  in
  List.iter (fun (l, n) ->
      match Univ.Level.var_index l, Univ.Level.name l with
      (* a level of a polymorphic context, or Set: it stands for itself *)
      | Some _, _ | None, None -> take_level l n
      | None, Some _ ->
        match Univ.Level.Map.find_opt l !m.fwd with
        | None -> fresh := (l, n) :: !fresh
        | Some l' -> take_level l' n)
    lu;
  (* What is left on each side is unmapped. Pair only what one pass can
     decide: an entry whose increment is unique among what remains. Each
     pairing can map a level, which may let an earlier entry be matched by
     its level on the next pass, so the passes run until none decides
     anything. Two entries of the same increment and no mapped level are
     ambiguous, and picking by [Universe.repr]'s order would pick
     differently on the two sides, so the comparison stops instead. *)
  let fresh = ref (List.rev !fresh) in
  let rec passes () =
    if CList.is_empty !fresh then ()
    else begin
      if not (List.length !fresh = List.length !rest) then
        diff "universe %s against %s"
          (Pp.string_of_ppcmds (Univ.Universe.raw_pr u))
          (Pp.string_of_ppcmds (Univ.Universe.raw_pr v));
      let decided = ref false in
      let keep = ref [] in
      List.iter (fun (l, n) ->
          match Univ.Level.Map.find_opt l !m.fwd with
          | Some l' ->
            (* mapped since this entry was set aside: match it by level *)
            let rec take seen = function
              | [] ->
                diff "universe %s has no %s+%d"
                  (Pp.string_of_ppcmds (Univ.Universe.raw_pr v)) (level_name l') n
              | (l2, n2) :: tl when Univ.Level.equal l2 l' && Int.equal n2 n ->
                List.rev_append seen tl
              | e :: tl -> take (e :: seen) tl
            in
            rest := take [] !rest;
            decided := true
          | None ->
            match List.filter (fun (_, n2) -> Int.equal n n2) !rest with
            | [ (l2, _) ] ->
              m := map_level !m l l2;
              rest := List.filter (fun (l3, n3) ->
                  not (Univ.Level.equal l3 l2 && Int.equal n3 n)) !rest;
              decided := true
            | [] ->
              diff "universe %s has no entry of increment %d"
                (Pp.string_of_ppcmds (Univ.Universe.raw_pr v)) n
            | _ :: _ :: _ -> keep := (l, n) :: !keep)
        !fresh;
      let left = List.rev !keep in
      if not !decided then
        raise (Undecided (Printf.sprintf
          "universe %s against %s: which level of the answer each level of the \
           challenge stands for is not decided"
          (Pp.string_of_ppcmds (Univ.Universe.raw_pr u))
          (Pp.string_of_ppcmds (Univ.Universe.raw_pr v))));
      fresh := left;
      passes ()
    end
  in
  passes ();
  !m

let map_quality q1 q2 =
  if not (Sorts.Quality.equal q1 q2) then diff "sort quality"

let map_sort m s1 s2 =
  let open Sorts in
  match s1, s2 with
  | SProp, SProp | Prop, Prop | Set, Set -> m
  | Type u, Type v -> map_universe m u v
  | QSort (q1, u), QSort (q2, v) ->
    if not (QVar.equal q1 q2) then diff "sort variable";
    map_universe m u v
  | (SProp | Prop | Set | Type _ | QSort _), _ -> diff "sort"

let map_instance m i1 i2 =
  let q1, u1 = UVars.Instance.to_array i1 and q2, u2 = UVars.Instance.to_array i2 in
  if Array.length q1 <> Array.length q2 || Array.length u1 <> Array.length u2 then
    diff "universe instance";
  Array.iter2 map_quality q1 q2;
  Array.fold_left2 map_level m u1 u2

let map_relevance r1 r2 =
  if not (Sorts.relevance_equal r1 r2) then diff "relevance"

let map_annot a1 a2 =
  map_relevance a1.Context.binder_relevance a2.Context.binder_relevance

(************************************************************************)
(** {6 Structural equality of terms}

    No conversion, no reduction, and no constant is unfolded: two terms are
    equal when they have the same shape, the same kernel names (a challenge
    name under a functor parameter renamed to the answer's parameter first,
    [rename]) and universes the map pairs. Binder names are not compared,
    their relevance is. A [Cast] is a type ascription the kernel has already
    used, so it is stripped on both sides. *)

let rec eq_constr m c1 c2 =
  let open Constr in
  match kind c1, kind c2 with
  | Cast (c1, _, _), _ -> eq_constr m c1 c2
  | _, Cast (c2, _, _) -> eq_constr m c1 c2
  | Rel i, Rel j -> if not (Int.equal i j) then diff "de Bruijn index"; m
  | Var i, Var j -> if not (Id.equal i j) then diff "section variable"; m
  | Meta _, _ | _, Meta _ -> diff "a term holds a metavariable"
  | Evar _, _ | _, Evar _ -> diff "a term holds an existential variable"
  | Sort s1, Sort s2 -> map_sort m s1 s2
  | Prod (a1, t1, b1), Prod (a2, t2, b2) ->
    map_annot a1 a2; eq_constr (eq_constr m t1 t2) b1 b2
  | Lambda (a1, t1, b1), Lambda (a2, t2, b2) ->
    map_annot a1 a2; eq_constr (eq_constr m t1 t2) b1 b2
  | LetIn (a1, v1, t1, b1), LetIn (a2, v2, t2, b2) ->
    map_annot a1 a2; eq_constr (eq_constr (eq_constr m v1 v2) t1 t2) b1 b2
  | App (f1, a1), App (f2, a2) ->
    if not (Int.equal (Array.length a1) (Array.length a2)) then diff "number of arguments";
    Array.fold_left2 eq_constr (eq_constr m f1 f2) a1 a2
  | Const (c1, u1), Const (c2, u2) ->
    let c1 = rename m Mod_subst.subst_constant c1 in
    if not (Constant.CanOrd.equal c1 c2) then
      diff "constant %s against %s" (Constant.to_string c1) (Constant.to_string c2);
    map_instance m u1 u2
  | Ind ((i1, n1), u1), Ind ((i2, n2), u2) ->
    let i1 = rename m Mod_subst.subst_mind i1 in
    if not (MutInd.CanOrd.equal i1 i2 && Int.equal n1 n2) then
      diff "inductive %s against %s" (MutInd.to_string i1) (MutInd.to_string i2);
    map_instance m u1 u2
  | Construct (((i1, n1), k1), u1), Construct (((i2, n2), k2), u2) ->
    let i1 = rename m Mod_subst.subst_mind i1 in
    if not (MutInd.CanOrd.equal i1 i2 && Int.equal n1 n2 && Int.equal k1 k2) then
      diff "constructor of %s against %s" (MutInd.to_string i1) (MutInd.to_string i2);
    map_instance m u1 u2
  | Case (ci1, u1, pms1, p1, iv1, s1, br1), Case (ci2, u2, pms2, p2, iv2, s2, br2) ->
    let (m1, n1) = ci1.ci_ind and (m2, n2) = ci2.ci_ind in
    let m1 = rename m Mod_subst.subst_mind m1 in
    if not (MutInd.CanOrd.equal m1 m2 && Int.equal n1 n2) then diff "match on another inductive";
    if not (Int.equal ci1.ci_npar ci2.ci_npar) then diff "match parameters";
    let m = map_instance m u1 u2 in
    if not (Int.equal (Array.length pms1) (Array.length pms2)) then diff "match parameters";
    let m = Array.fold_left2 eq_constr m pms1 pms2 in
    let ((nas1, t1), r1) = p1 and ((nas2, t2), r2) = p2 in
    if not (Int.equal (Array.length nas1) (Array.length nas2)) then diff "match return clause";
    Array.iter2 map_annot nas1 nas2;
    map_relevance r1 r2;
    let m = eq_constr m t1 t2 in
    let m = match iv1, iv2 with
      | NoInvert, NoInvert -> m
      | CaseInvert { indices = a1 }, CaseInvert { indices = a2 } ->
        if not (Int.equal (Array.length a1) (Array.length a2)) then diff "match indices";
        Array.fold_left2 eq_constr m a1 a2
      | (NoInvert | CaseInvert _), _ -> diff "match inversion"
    in
    let m = eq_constr m s1 s2 in
    if not (Int.equal (Array.length br1) (Array.length br2)) then diff "number of branches";
    Array.fold_left2 (fun m (nas1, b1) (nas2, b2) ->
        if not (Int.equal (Array.length nas1) (Array.length nas2)) then diff "branch binders";
        Array.iter2 map_annot nas1 nas2;
        eq_constr m b1 b2)
      m br1 br2
  | Fix ((ln1, i1), (nas1, tl1, bl1)), Fix ((ln2, i2), (nas2, tl2, bl2)) ->
    if not (Array.equal Int.equal ln1 ln2 && Int.equal i1 i2) then diff "fixpoint structure";
    eq_recdecl m (nas1, tl1, bl1) (nas2, tl2, bl2)
  | CoFix (i1, (nas1, tl1, bl1)), CoFix (i2, (nas2, tl2, bl2)) ->
    if not (Int.equal i1 i2) then diff "cofixpoint structure";
    eq_recdecl m (nas1, tl1, bl1) (nas2, tl2, bl2)
  | Proj (p1, r1, c1), Proj (p2, r2, c2) ->
    let p1 = rename m Mod_subst.subst_proj p1 in
    if not (Projection.CanOrd.equal p1 p2) then
      diff "projection %s against %s" (Projection.to_string p1) (Projection.to_string p2);
    map_relevance r1 r2;
    eq_constr m c1 c2
  | Int i, Int j -> if not (Uint63.equal i j) then diff "integer literal"; m
  | Float f, Float g -> if not (Float64.equal f g) then diff "float literal"; m
  | String s, String t -> if not (Pstring.equal s t) then diff "string literal"; m
  | Array (u1, v1, d1, t1), Array (u2, v2, d2, t2) ->
    if not (Int.equal (Array.length v1) (Array.length v2)) then diff "array length";
    let m = map_instance m u1 u2 in
    let m = Array.fold_left2 eq_constr m v1 v2 in
    eq_constr (eq_constr m d1 d2) t1 t2
  | (Rel _ | Var _ | Sort _ | Prod _ | Lambda _ | LetIn _ | App _ | Const _
    | Ind _ | Construct _ | Case _ | Fix _ | CoFix _ | Proj _ | Int _ | Float _
    | String _ | Array _), _ -> diff "the terms have different shapes"

and eq_recdecl m (nas1, tl1, bl1) (nas2, tl2, bl2) =
  if not (Int.equal (Array.length tl1) (Array.length tl2)) then diff "recursive block size";
  Array.iter2 map_annot nas1 nas2;
  let m = Array.fold_left2 eq_constr m tl1 tl2 in
  Array.fold_left2 eq_constr m bl1 bl2

(************************************************************************)
(** {6 Declarations} *)

let eq_rel_context m c1 c2 =
  let open Context.Rel.Declaration in
  if not (Int.equal (List.length c1) (List.length c2)) then diff "context length";
  List.fold_left2 (fun m d1 d2 ->
      match d1, d2 with
      | LocalAssum (a1, t1), LocalAssum (a2, t2) -> map_annot a1 a2; eq_constr m t1 t2
      | LocalDef (a1, b1, t1), LocalDef (a2, b2, t2) ->
        map_annot a1 a2; eq_constr (eq_constr m b1 b2) t1 t2
      | (LocalAssum _ | LocalDef _), _ -> diff "a let-in of the context")
    m c1 c2

let eq_universes m u1 u2 = match u1, u2 with
  | Monomorphic, Monomorphic -> m
  | Polymorphic a1, Polymorphic a2 ->
    if UVars.AbstractContext.size a1 <> UVars.AbstractContext.size a2 then
      diff "the universe context has another size";
    let (e1, c1) = UVars.UContext.constraints (UVars.AbstractContext.repr a1) in
    let (e2, c2) = UVars.UContext.constraints (UVars.AbstractContext.repr a2) in
    if not (Univ.UnivConstraints.equal c1 c2 && Sorts.ElimConstraints.equal e1 e2) then
      diff "the universe context has other constraints";
    m
  | Monomorphic, Polymorphic _ -> diff "a monomorphic declaration is polymorphic in the answer"
  | Polymorphic _, Monomorphic -> diff "a polymorphic declaration is monomorphic in the answer"

(* What the challenge leaves without a body ([Admitted], [Axiom] and
   [Parameter] give the same .vo content, so the kind of the declaration
   cannot tell them apart), the answer may fill under two rules, both read
   from the sort of the type the challenge states for the constant
   ([stated_sort]), never from that type reduced nor from the answer's.

   (1) The answer may give it a body, opaque or transparent, only when the
   challenge states it as a proposition or the config names it as a
   theorem. Proving a lemma is the point. A constant of any other sort --
   an open definition -- must stay without a body, or the answer could
   choose the function the statements are about, unless the config names
   it: the challenge then asks the answer to choose it, as for a function
   [f] left open with a lemma [f_spec] about it.

   (2) A constant that another compared challenge declaration names in what
   the comparison reads of it, a type or a transparent body but not an
   opaque proof ([named], which [compare_declarations] computes with
   [constr_names]), must stay opaque, whether the config names it or not,
   unless the challenge states it as data. The challenge states that
   declaration about a constant that does not unfold, and a transparent
   body would let conversion unfold it there, which changes what the
   declaration states:
   with [L : exists n, n = 0] left without a body,
   [L = ex_intro _ 0 eq_refl] is not provable, and once [L] is defined as
   that term it is proved by reflexivity. A constant that no other
   declaration names changes no statement but its own. A function
   [f : nat -> nat] that the config names is not held to this: it is data,
   and [f_spec] is stated about the function the answer chooses.

   In [Prop] or [SProp], the constant is a proposition. In [Set] or [Type],
   it is data, even when its type unfolds to a proposition, so a challenge
   that wants a lemma kept opaque states it in [Prop]. In a sort variable
   or a global sort, when the type cannot be typed, and for a field of a
   module type, the run cannot tell, and each rule takes its refusing side:
   such a constant is no proposition for (1) and no data for (2). *)
type sort_class = Proposition | Data | Undetermined

(* The class of the sort of the type that the challenge states for its
   constant [cb]: the sort [Typeops.infer_type] gives that type in [env],
   the challenge environment, under the constant's own typing flags
   ([CheckFlags.set_local_flags]) and universe context, as the kernel check
   types a constant ([Mod_checking.check_constant_declaration]). The type
   is not reduced, and the challenge environment holds no declaration of
   the answer's, so no body the answer chose is unfolded. [Undetermined]
   for a sort variable or a global sort ([QSort]), and for a type that
   cannot be typed there. *)
let stated_sort env (cb : constant_body) =
  let sort () =
    let env = CheckFlags.set_local_flags cb.const_typing_flags env in
    let env = match cb.const_universes with
      | Monomorphic -> env
      | Polymorphic ctx ->
        Environ.push_context ~strict:false (UVars.AbstractContext.repr ctx) env
    in
    (Typeops.infer_type env cb.const_type).Environ.utj_type
  in
  match sort () with
  | Sorts.Prop | Sorts.SProp -> Proposition
  | Sorts.Set | Sorts.Type _ -> Data
  | Sorts.QSort _ -> Undetermined
  | exception e when CErrors.noncritical e -> Undetermined

(* [sort] is the class of the sort of the type the challenge states for
   the constant ([stated_sort]), or [Undetermined] for a field of a module
   type; [is_theorem] says whether the config names the constant as a
   theorem, and [named] whether another compared challenge declaration
   names it. [sort] and [named] are forced only by a constant the
   challenge leaves without a body and the answer fills. *)
let eq_const_body ~sort ~is_theorem ~named m (cb1 : constant_body) (cb2 : constant_body) =
  map_relevance cb1.const_relevance cb2.const_relevance;
  let m = eq_universes m cb1.const_universes cb2.const_universes in
  let m = eq_constr m cb1.const_type cb2.const_type in
  match cb1.const_body, cb2.const_body with
  | Undef _, Undef _ -> m
  | Undef _, (Def _ | OpaqueDef _)
    when not is_theorem
         && (match Lazy.force sort with Proposition -> false | Data | Undetermined -> true) ->
    diff "the challenge leaves this declaration open and the answer defines it"
  | Undef _, Def _
    when (match Lazy.force sort with Data -> false | Proposition | Undetermined -> true)
         && Lazy.force named ->
    diff "the challenge leaves this constant without a body, another challenge \
          declaration names it, and the answer gives it a transparent body"
  | Undef _, (Def _ | OpaqueDef _) -> m
  | Undef _, _ -> diff "an assumption is a primitive or a symbol in the answer"
  (* An opaque body is never compared, but a proof stays a proof: a Qed in
     the challenge may not become a transparent definition, which would let
     the answer's body reach conversion where the challenge's could not. *)
  | OpaqueDef _, OpaqueDef _ -> m
  | Def b1, Def b2 -> eq_constr m b1 b2
  | Def _, OpaqueDef _ -> diff "a transparent definition is opaque in the answer"
  | Def _, _ -> diff "a transparent definition is not a definition in the answer"
  | OpaqueDef _, _ -> diff "an opaque proof is not an opaque proof in the answer"
  | Primitive p1, Primitive p2 ->
    if not (CPrimitives.equal p1 p2) then diff "another primitive"; m
  | Primitive _, _ -> diff "a primitive is not a primitive in the answer"
  | Symbol _, Symbol _ -> m
  | Symbol _, _ -> diff "a symbol is not a symbol in the answer"

let eq_record m r1 r2 = match r1, r2 with
  | NotRecord, NotRecord | FakeRecord, FakeRecord -> m
  | PrimRecord p1, PrimRecord p2 ->
    if not (Id.equal p1.id p2.id) then diff "the record binder name";
    if not (Array.equal Id.equal p1.projections p2.projections) then diff "the projections";
    if not (Array.equal Sorts.relevance_equal p1.relevances p2.relevances) then
      diff "a projection's relevance";
    if p1.has_eta <> p2.has_eta then diff "the record's eta";
    if not (Int.equal (Array.length p1.tys) (Array.length p2.tys)) then diff "the projections";
    Array.fold_left2 eq_constr m p1.tys p2.tys
  | (NotRecord | FakeRecord | PrimRecord _), _ -> diff "the record kind"

let eq_variance v1 v2 = match v1, v2 with
  | None, None -> ()
  | Some (a1, b1), Some (a2, b2) ->
    if not (Array.equal (fun x y -> x = y) a1 a2 && Array.equal (fun x y -> x = y) b1 b2) then
      diff "the universe variance"
  | None, Some _ | Some _, None -> diff "the universe variance"

(* The relaxed kernel conditions a declaration was typed under are part of
   what it claims. The conversion oracle and the performance switches are
   not: they change how the kernel works, not what it accepted. *)
let eq_typing_flags (f1 : typing_flags) (f2 : typing_flags) =
  if f1.check_guarded <> f2.check_guarded
  || f1.check_positive <> f2.check_positive
  || f1.check_universes <> f2.check_universes
  || f1.check_eliminations <> f2.check_eliminations
  || f1.indices_matter <> f2.indices_matter
  || f1.impredicative_set <> f2.impredicative_set
  then diff "the kernel conditions the declaration was typed under"

let eq_one_ind m (mip1 : one_inductive_body) (mip2 : one_inductive_body) =
  if not (Id.equal mip1.mind_typename mip2.mind_typename) then diff "the type's name";
  map_relevance mip1.mind_relevance mip2.mind_relevance;
  let m = eq_rel_context m mip1.mind_arity_ctxt mip2.mind_arity_ctxt in
  let m = eq_constr m mip1.mind_user_arity mip2.mind_user_arity in
  let m = map_sort m mip1.mind_sort mip2.mind_sort in
  if not (Int.equal mip1.mind_nrealargs mip2.mind_nrealargs) then diff "the number of indices";
  if (match mip1.mind_squashed, mip2.mind_squashed with
      | None, None -> false
      | Some AlwaysSquashed, Some AlwaysSquashed -> false
      | Some (SometimesSquashed q1), Some (SometimesSquashed q2) ->
        not (Sorts.Quality.Set.equal q1 q2)
      | _ -> true)
  then diff "the elimination restriction";
  if not (Array.equal Id.equal mip1.mind_consnames mip2.mind_consnames) then
    diff "the constructor names";
  if not (Int.equal (Array.length mip1.mind_user_lc) (Array.length mip2.mind_user_lc)) then
    diff "the number of constructors";
  let m = Array.fold_left2 eq_constr m mip1.mind_user_lc mip2.mind_user_lc in
  eq_record m mip1.mind_record mip2.mind_record

(* The template data of two template-polymorphic blocks ([mind_template]),
   by which the kernel types an application of the block: which parameters
   bind a sort, and its levels ([template_param_arguments]); the block's
   sort in terms of those ([template_concl]); the context that binds them
   ([template_context]); and the levels it instantiates them with where it
   reads the block at no application ([template_defaults]). A level that
   the template context binds is a [Level.var], compared by its position,
   as [eq_universes] compares a polymorphic context's; every other level
   goes through the map, so the same block declared after one more
   universe compares equal. The context's universe constraints are equal
   when, each global level they name taken through the map, they are the
   same set; a global level that no comparison has mapped yet leaves the
   block undecided ([Undecided]). Its elimination constraints relate
   qualities, which are compared by identity. A difference names the
   field. *)
let[@warning "+9"] eq_template m
    { template_param_arguments; template_concl; template_context; template_defaults }
    (t2 : template_universes) =
  let field what f = try f () with Diff d -> diff "the template-polymorphic %s: %s" what d in
  if not (Int.equal (List.length template_param_arguments)
            (List.length t2.template_param_arguments))
  then diff "the template-polymorphic parameters";
  if UVars.AbstractContext.size template_context
     <> UVars.AbstractContext.size t2.template_context
  then diff "the template-polymorphic universe context has another size";
  let m =
    field "default universes" (fun () ->
        map_instance m template_defaults t2.template_defaults)
  in
  let m = field "conclusion" (fun () -> map_sort m template_concl t2.template_concl) in
  let m =
    List.fold_left2 (fun m a1 a2 -> match a1, a2 with
        | Some s1, Some s2 -> field "parameters" (fun () -> map_sort m s1 s2)
        | None, None -> m
        | (None | Some _), _ -> diff "the template-polymorphic parameters")
      m template_param_arguments t2.template_param_arguments
  in
  let (e1, c1) = UVars.UContext.constraints (UVars.AbstractContext.repr template_context) in
  let (e2, c2) = UVars.UContext.constraints (UVars.AbstractContext.repr t2.template_context) in
  let other () = diff "the template-polymorphic universe context has other constraints" in
  if not (Sorts.ElimConstraints.equal e1 e2) then other ();
  if not (Int.equal (Univ.UnivConstraints.cardinal c1) (Univ.UnivConstraints.cardinal c2)) then
    other ();
  let level u = match Univ.Level.var_index u, Univ.Level.name u with
    | Some _, _ | None, None -> u
    | None, Some _ ->
      match Univ.Level.Map.find_opt u m.fwd with
      | Some v -> v
      | None ->
        raise (Undecided (Printf.sprintf
          "the template-polymorphic universe context constrains the universe %s, \
           which no comparison has mapped"
          (level_name u)))
  in
  let c1 =
    Univ.UnivConstraints.fold (fun (u, k, v) acc ->
        Univ.UnivConstraints.add (level u, k, level v) acc)
      c1 Univ.UnivConstraints.empty
  in
  if not (Univ.UnivConstraints.equal c1 c2) then other ();
  m

let eq_mib_body m (mib1 : mutual_inductive_body) (mib2 : mutual_inductive_body) =
  if mib1.mind_finite <> mib2.mind_finite then diff "the recursivity kind";
  if not (Int.equal mib1.mind_nparams mib2.mind_nparams) then diff "the number of parameters";
  if not (Int.equal mib1.mind_nparams_rec mib2.mind_nparams_rec) then
    diff "the number of uniform parameters";
  if mib1.mind_private <> mib2.mind_private then diff "the private flag";
  let template = match mib1.mind_template, mib2.mind_template with
    | None, None -> None
    | Some t1, Some t2 -> Some (t1, t2)
    | (None | Some _), _ ->
      diff "a template-polymorphic inductive type is not template-polymorphic in the answer"
  in
  eq_typing_flags mib1.mind_typing_flags mib2.mind_typing_flags;
  eq_variance mib1.mind_variance mib2.mind_variance;
  eq_variance mib1.mind_sec_variance mib2.mind_sec_variance;
  let m = eq_universes m mib1.mind_universes mib2.mind_universes in
  let m = eq_rel_context m mib1.mind_params_ctxt mib2.mind_params_ctxt in
  if not (Int.equal (Array.length mib1.mind_packets) (Array.length mib2.mind_packets)) then
    diff "the number of types in the block";
  let m = Array.fold_left2 eq_one_ind m mib1.mind_packets mib2.mind_packets in
  (* after the types, whose terms may map a global level the template
     context's constraints name *)
  match template with
  | None -> m
  | Some (t1, t2) -> eq_template m t1 t2

(* The primitive type that [env] registers the constant [c] as
   ([Primitive int := #int63_type.]): [#int63_type], [#float64_type],
   [#string_type] or [#array_type], or [None]. A registration names a
   constant, compared with [c] by canonical name, as conversion compares
   constants, so another name of a registered constant is that primitive
   type too. The record is bound field by field, so a field the kernel adds
   to it is a compile error here. The registrations of inductive types are
   not read: they choose the inductive type in which a primitive operation
   builds its result, and a primitive operation is a [Primitive] constant,
   which [eq_const_body] compares. *)
let primitive_type env c =
  let[@warning "+9"] Retroknowledge.{
      retro_int63; retro_float64; retro_string; retro_array;
      retro_bool = _; retro_carry = _; retro_pair = _; retro_cmp = _; retro_f_cmp = _;
      retro_f_class = _;
    } = Environ.retroknowledge env
  in
  let is = function Some c' -> Constant.CanOrd.equal c c' | None -> false in
  let name t = Some ("#" ^ CPrimitives.prim_type_to_string t) in
  if is retro_int63 then name CPrimitives.PT_int63
  else if is retro_float64 then name CPrimitives.PT_float64
  else if is retro_string then name CPrimitives.PT_string
  else if is retro_array then name CPrimitives.PT_array
  else None

(* A compared constant, [c1] as the challenge environment names it and [c2]
   as the answer environment does, is the same primitive type on both
   sides, or none on either ([primitive_type]). A primitive type's body is
   [Undef], as a parameter's, so [eq_const_body] does not see the
   difference, which changes what the constant is: a parameter that the
   answer registers as a primitive type has literals, so the answer could
   prove it inhabited. *)
let eq_primitive_type ~challenge_env ~answer_env c1 c2 =
  let t1 = primitive_type challenge_env c1 and t2 = primitive_type answer_env c2 in
  if not (Option.equal String.equal t1 t2) then
    let name = function Some t -> "the primitive type " ^ t | None -> "no primitive type" in
    diff "this constant is %s in the challenge and %s in the answer" (name t1) (name t2)

(************************************************************************)
(** {6 Module types}

    A field of a [Module Type] is not a constant of the environment, so the
    walk over the environment's constants does not see it. Each challenge
    module type is compared with the answer's module type of the same path,
    field by field.

    Of a module type, and of a module field of one, the expanded signature
    ([mod_type]) is compared. The algebraic form it was expanded from
    ([mod_type_alg]), a module field's implementation ([mod_expr]) and the
    delta resolver ([mod_delta]) are not read, nor any module path they
    name. A field is matched by its label, and the kernel names that the
    fields hold are compared by [eq_constr] and, for the symbols of a block
    of rewrite rules, here, each challenge name renamed first ([rename]).

    A functor is compared parameter by parameter. The challenge's parameter
    [p1] stands for the answer's parameter [p2] of the same position in
    [p1]'s own type and in the rest of the signature ([umap.params]), as
    the kernel's subtyping check ([Subtyping.check_modtypes]) maps them.
    Once the functor is compared, the substitution and the answer's
    parameters bound around it are those of before it; the levels mapped
    inside stay mapped.

    No field is compared for a primitive-type registration
    ([eq_primitive_type]). The constants of a module, sealed or not, are
    constants of the environment, whose registrations
    [compare_declarations] compares. What keeps a registration off a field
    of a module type of an answer library is rocqchk's own check of that
    library (checker/mod_checking.ml), since the answer's files need not be
    coqc's:
    - [check_module_type] checks a module type with no registration in
      force, and [check_module] and [check_signature] withhold them
      ([without_constant_registrations]) while they check the type of a
      sealed, algebraic or declared module or the body of a functor;
    - [check_module] refuses a registration that no module body declares,
      and [get_retroknowlege] one that gives its constant another canonical
      name, so a registered constant is a field of a module body, named as
      declared;
    - a field whose canonical name differs from its user name, as a delta
      resolver that maps a module-type field to a registered constant makes
      it, must be a [Def] convertible with the constant its canonical name
      names ([check_structure_field], through
      [Subtyping.check_constant_alias]), and [eq_const_body] compares that
      body: a challenge field left open refuses any body the answer gives
      it.
    The one exception is a library given with -admit, which is not checked:
    a forged delta resolver of one of its module types, mapping a field to
    a registered constant, is not caught here. The verdict lists that
    library under [admitted]. *)

let rec eq_signature m s1 s2 =
  match s1, s2 with
  | NoFunctor b1, NoFunctor b2 -> eq_structure m b1 b2
  | MoreFunctor (p1, t1, s1), MoreFunctor (p2, t2, s2) ->
    (* The answer's parameters in scope stay one-to-one with the
       challenge's: were [p2] bound again inside, a name under either
       binding would stand for both. *)
    if MBId.Set.mem p2 m.bound then diff "the answer binds one functor parameter twice";
    let mp2 = ModPath.MPbound p2 in
    (* [add_mbid], not [join]: each challenge parameter is renamed once, so
       one that has the name of an answer parameter is not renamed again. *)
    let params =
      Mod_subst.add_mbid p1 mp2 (Mod_subst.empty_delta_resolver mp2)
        (Option.default Mod_subst.empty_subst m.params)
    in
    let inner = { m with params = Some params; bound = MBId.Set.add p2 m.bound } in
    let inner = eq_modtype inner t1 t2 in
    let inner = eq_signature inner s1 s2 in
    { inner with params = m.params; bound = m.bound }
  | NoFunctor _, MoreFunctor _ -> diff "a module type is a functor in the answer"
  | MoreFunctor _, NoFunctor _ -> diff "a functor is not a functor in the answer"

and eq_structure m b1 b2 =
  List.fold_left (fun m (l, f1) ->
      match List.assoc_opt l b2 with
      | None -> diff "the field %s is missing from the answer" (Id.to_string l)
      | Some f2 ->
        match f1, f2 with
        | SFBconst c1, SFBconst c2 ->
          (* A field of a module type is never a config-named theorem: the
             config names a constant of the environment. A field of a
             module type has no environment to type it in: no environment
             holds the other fields or the functor parameters, which its
             type may name. So its sort is [Undetermined], the first rule
             of [eq_const_body] refuses any body the answer gives it, and
             [named] is never asked. *)
          eq_const_body ~sort:(Lazy.from_val Undetermined) ~is_theorem:false
            ~named:(Lazy.from_val true) m c1 c2
        | SFBmind i1, SFBmind i2 -> eq_mib_body m i1 i2
        | SFBrules r1, SFBrules r2 ->
          (* The symbols the block rewrites must be the same ones, in the
             same order. The machine rules themselves are not compared: a
             rewrite rule reaches a verdict through the rewrite_rules
             switch of the config, which refuses every one of them unless
             the task permits them. *)
          let names b = List.map fst b.rewrules_rules in
          let names1 = List.map (rename m Mod_subst.subst_constant) (names r1) in
          if not (CList.equal Constant.CanOrd.equal names1 (names r2)) then
            diff "the field %s rewrites other symbols in the answer" (Id.to_string l);
          m
        | SFBmodule mb1, SFBmodule mb2 ->
          eq_signature m (Mod_declarations.mod_type mb1) (Mod_declarations.mod_type mb2)
        | SFBmodtype t1, SFBmodtype t2 -> eq_modtype m t1 t2
        | (SFBconst _ | SFBmind _ | SFBrules _ | SFBmodule _ | SFBmodtype _), _ ->
          diff "the field %s is of another kind in the answer" (Id.to_string l))
    m b1

(* The module types [t1] of the challenge and [t2] of the answer, by their
   expanded signatures. *)
and eq_modtype m t1 t2 =
  eq_signature m (Mod_declarations.mod_type t1) (Mod_declarations.mod_type t2)

(************************************************************************)
(** {6 The run} *)

type t = {
  cfg : config;
  dir : string;
  out : string;
  files : string list;           (** the challenge files, absolute or as given *)
  challenge_dir : string option;
      (** The real path of [dir]; [None] when it cannot be found, and then
          no file lies under it ([check_challenge_dir]). *)
  prechecked : DirPath.t list;
  add_challenge_load_path : unit -> unit;
  under_challenge_root : DirPath.t -> bool;
      (** Is this library name under a root the challenge directory stands in
          for: the root's name followed by at least one more component, so
          that [path_below_root] gives its path? Those, unless pre-checked,
          are the answer's own libraries ([origin]). Every other library the
          answer loaded, unless pre-checked, is a shared one, and
          [check_provenance] refuses a run unless the file the loader
          recorded for it lies in no place an answer's file is found in
          ([answer_place]) and was found in a trusted directory
          ([trusted_dirs]). *)
  open_roots : (DirPath.t * string) list;
      (** The roots the command line binds that the challenge does NOT stand
          in for, with the directory each is bound to. A library under one of
          them is the answer's side of the run and the challenge has no
          counterpart for it, so [check_open_roots] refuses the run unless
          the config pre-checks it. *)
  cwd : string option;
      (** The real path of the working directory. The load path binds it
          implicitly and NOT recursively, so a library is found there only
          as a file directly in it. *)
  bound_dirs : string list;
      (** The real paths of the directories the command line binds, each
          with its subdirectories. *)
  trusted_dirs : string list;
      (** The real paths of the directories the run trusts for the image's
          own libraries, each with its subdirectories: the corelib
          directory, user-contrib and the directories of ROCQPATH and
          COQPATH (none under -boot), those of them whose real path exists. *)
  outside : DirPath.t list;
      (** The shared libraries the answer loaded whose recorded file passed
          [check_provenance]; filled by [run]. *)
  path_below_root : DirPath.t -> string option;
      (** The path of a library's [.vo] file below the directory of the root
          the challenge stands in for that holds it ([Some "X/Y.vo"] for
          [<root>.X.Y]); [None] for a library under no such root. The
          challenge directory holds the challenge's file of that library at
          that path ([pinned]). *)
  pins : (string * string) list;
      (** The real path of each challenge file, and the sha256 the config
          pins for it ([pinned]). *)
  answer_files : string DirPath.Map.t;
      (** The file the answer's loader recorded for each library it loaded;
          filled by [run]. *)
  prechecked_closure : DirPath.Set.t;
      (** The pre-checked libraries and every library they rest on, in the
          answer's dependency graph; filled by [run]. *)
}

let realpath p =
  try Some (Unix.realpath p) with Unix.Unix_error _ | Invalid_argument _ | Sys_error _ -> None

let path_under ~dir file =
  String.equal file dir
  || CString.is_prefix (if String.equal dir "/" then dir else dir ^ "/") file

(* Whether [a] and [b] resolve to one real path. A path that cannot be
   resolved is the same file as none. *)
let same_real_file a b = match realpath a, realpath b with
  | Some ra, Some rb -> String.equal ra rb
  | None, _ | _, None -> false

(* The sha256 of each file this run hashed, by its real path, or by the path
   given when it has none. *)
let hashed_files : (string, string) Hashtbl.t = Hashtbl.create 17

(* The sha256 of [file]. A run hashes each file at most once: every later
   question about the same file is answered from [hashed_files]. A file
   that is not a regular file or cannot be read refuses the run: [what ()]
   says which file it is, and the reason [Sha256.hex_of_file] gives
   follows. *)
let file_sha256 ~what file =
  let key = Option.default file (realpath file) in
  match Hashtbl.find_opt hashed_files key with
  | Some h -> h
  | None ->
    let h =
      try Sha256.hex_of_file file
      with CErrors.UserError msg -> CErrors.user_err Pp.(str (what () ^ ": ") ++ msg ++ str ".")
    in
    Hashtbl.add hashed_files key h;
    h

(* The place an answer's file could have been found in that holds [file],
   the path the loader recorded: the working directory, for a file directly
   in it, or a directory the command line binds, for a file anywhere below
   it. Both the directory the loader found the file in and the file's own
   real path are tested, so a link in such a place to a file elsewhere, or a
   link elsewhere to a file in one, is found. A path that cannot be resolved
   is in an unknown place, which counts as the answer's. [None]: in no such
   place. This says where the recorded file is, not who wrote it. *)
let answer_place t file =
  let found_in = realpath (Filename.dirname file) and real = realpath file in
  match found_in, real with
  | None, _ | _, None -> Some file
  | Some d, Some f ->
    let in_cwd p = match t.cwd with
      | Some c -> String.equal (Filename.dirname p) c || String.equal p c
      | None -> true
    in
    if in_cwd (Filename.concat d (Filename.basename file)) || in_cwd f then
      Some "the working directory"
    else
      List.find_map (fun dir ->
          if path_under ~dir d || path_under ~dir f then Some ("the bound directory " ^ dir)
          else None)
        t.bound_dirs

(* Before the challenge is loaded: the challenge files the config pins must be
   there and have the sha256 it gives. [trusted] are the directories the run
   trusts for the image's own libraries; only those whose real path exists
   are kept, as real paths. *)
let prepare cfg ~dir ~out ~add_challenge_load_path ~under_challenge_root ~path_below_root
    ~open_roots ~bound_dirs ~trusted =
  let files =
    List.map (fun f ->
        let p = if Filename.is_relative f.cf_path then Filename.concat dir f.cf_path
          else f.cf_path in
        if not (Sys.file_exists p) then
          CErrors.user_err Pp.(str ("The challenge file " ^ p ^ " is not there."));
        let got = file_sha256 p ~what:(fun () -> "The challenge file " ^ p ^ " cannot be read") in
        if not (String.equal got f.cf_sha256) then
          CErrors.user_err
            (Pp.str ("The challenge file " ^ p ^ " has sha256 " ^ got ^
                     ", and the config pins " ^ f.cf_sha256 ^ "."));
        p)
      cfg.cfg_challenge_files
  in
  (* A challenge file whose real path cannot be found pins nothing. *)
  let pins =
    List.filter_map (fun (p, f) -> Option.map (fun r -> r, f.cf_sha256) (realpath p))
      (List.combine files cfg.cfg_challenge_files)
  in
  (* The verdict file is already gone: rocqchk removes it before it parses
     its command line (coqchk_main.ml), so no stop before the verdict, here
     or earlier, leaves yesterday's verdict to be read as today's. *)
  { cfg; dir; out; files;
    challenge_dir = realpath dir;
    prechecked = prechecked_libraries cfg;
    add_challenge_load_path; under_challenge_root; open_roots;
    cwd = realpath (Sys.getcwd ());
    bound_dirs = List.filter_map realpath bound_dirs;
    trusted_dirs = List.filter_map realpath trusted;
    outside = [];
    path_below_root; pins;
    answer_files = DirPath.Map.empty;
    prechecked_closure = DirPath.Set.empty }

(* Refuses [file] as the file of the pre-checked library [p] unless it has the
   sha256 the config pins for [p], or when it cannot be read. *)
let check_pin p file =
  let lib = DirPath.to_string p.pc_library in
  let got =
    file_sha256 file ~what:(fun () ->
        "The pre-checked library " ^ lib ^ " is " ^ file ^ ", which cannot be read")
  in
  if not (String.equal got p.pc_sha256) then
    CErrors.user_err
      (Pp.str ("The pre-checked library " ^ lib ^ " is " ^ file ^
               ", whose sha256 is " ^ got ^ ", and the config pins " ^ p.pc_sha256 ^ "."))

(* Before any library is read: each pre-checked library, resolved on the
   answer's load path, the one in place when this runs, must have the sha256
   the config pins. A pre-checked library loads without a check, so the file
   its name resolves to is not unmarshalled before its pin is checked. The
   loader reads that file, unless the command line names another file of
   that library: the loader reads that one instead, before any pin is
   checked on it, and [check_prechecked_read] hashes it after the read. *)
let check_prechecked_files cfg =
  List.iter (fun p -> check_pin p (CheckLibrary.library_file p.pc_library)) cfg.cfg_prechecked

(* After the read: the file the answer's loader recorded for each pre-checked
   library must have its pin as well. [check_prechecked_files] hashed the file
   the name resolves to, and the load path has not changed since, so only a
   file of another real path is hashed here. A pre-checked library the answer
   did not load is refused: its pin would be checked on no file it read. *)
let check_prechecked_read t =
  List.iter (fun p ->
      let dp = p.pc_library in
      match DirPath.Map.find_opt dp t.answer_files with
      | None ->
        CErrors.user_err
          Pp.(str ("The answer did not load the pre-checked library " ^ DirPath.to_string dp ^
                   ", which the config names."))
      | Some file ->
        if not (same_real_file file (CheckLibrary.library_file dp)) then check_pin p file)
    t.cfg.cfg_prechecked

(* A root the command line binds that the challenge does not stand in for is
   an open root: the answer's build put files there, and the challenge
   directory holds nothing under it. Such a library is neither compared
   (the challenge has no counterpart) nor pinned, and loading it into the
   challenge environment as a shared one would let a file the answer wrote
   decide a universe constraint on BOTH sides, which is the forgery this
   refuses: the run stops unless the config pre-checks every library the
   answer loaded from under that root, which pins its sha256.

   Unlike the rule of [under_challenge_root], this one counts a library
   named exactly as an open root too, which is stricter: such a library is
   refused unless pre-checked, even when it is under a root the challenge
   stands in for (with -Q d1 A -Q d2 A.B and A.B open, the library A.B,
   which is d1/B.vo).

   Production binds one root, the answer's project root, which every checked
   answer library lives under and the challenge therefore stands in for, so
   the list is empty there. A test harness that binds a stand-in for the
   image's libraries pre-checks them, as the config's pre-checked list is
   for. *)
let check_open_roots t ~answer_deps =
  let under root lib =
    let r = DirPath.to_string root and l = DirPath.to_string lib in
    String.equal l r || CString.is_prefix (r ^ ".") l
  in
  List.iter (fun (lib, _) ->
      List.iter (fun (root, path) ->
          if under root lib && not (List.exists (DirPath.equal lib) t.prechecked) then
            CErrors.user_err
              Pp.(str ("The answer loaded the library " ^ DirPath.to_string lib ^
                       " from " ^ path ^ ", bound to " ^ DirPath.to_string root ^
                       ", which the challenge does not stand in for and the config \
                        does not declare pre-checked. Every library of such a root \
                        must be pre-checked, so that its bytes are pinned.")))
        t.open_roots)
    answer_deps

let rec mp_root mp = match mp with
  | ModPath.MPfile dp -> Some dp
  | ModPath.MPdot (mp, _) -> mp_root mp
  | ModPath.MPbound _ -> None

let in_libs libs mp = match mp_root mp with
  | None -> false
  | Some dp -> List.exists (DirPath.equal dp) libs

(* What a library is to the run, by its name alone: a pre-checked one, whose
   bytes the config pins, wherever it lies; otherwise the answer's own when it
   lies under a root the challenge stands in for, and a shared one when it
   does not. The checks that tell these three apart read this. Two tests are
   of other classes: [check_open_roots] asks only whether a library under an
   open root, or named as one, is pre-checked, and [check_constraints] tells
   a level of a library under a root the challenge stands in for,
   pre-checked or not, from every other level. *)
type origin = Prechecked | Own | Shared

let origin t dp =
  if List.exists (DirPath.equal dp) t.prechecked then Prechecked
  else if t.under_challenge_root dp then Own
  else Shared

(* The image's own library: a shared one -- outside every root the challenge
   stands in for, not pre-checked -- whose file, as the answer's loader
   recorded it, passed [check_provenance] ([outside]): it lies in no place
   an answer's file is found in ([answer_place]: the working directory, a
   bound directory) and was found in a directory the run trusts for the
   image's own libraries ([trusted_dirs]). What this establishes is where
   the loaded file is, from the path the loader recorded; that no answer
   wrote such a file rests on the launch keeping the trusted directories out
   of the answer's reach (check_compare.mli). [check_provenance] refuses a
   run whose answer loaded a shared library from anywhere else, so in a run
   that goes on, every shared library the answer loaded is the image's
   own. *)
let image_own t dp = match origin t dp with
  | Shared -> List.exists (DirPath.equal dp) t.outside
  | Prechecked | Own -> false

(* A library that is one file for both sides: a pre-checked one, whose bytes
   the config pins, or the image's own ([image_own]). The challenge load must
   read a shared library from the answer's file, and a pre-checked one from
   the answer's file or from a file of the pinned sha256
   ([check_same_files]). *)
let one_file t dp = match origin t dp with
  | Prechecked -> true
  | Own | Shared -> image_own t dp

let rooted_one_file t mp = match mp_root mp with
  | None -> false
  | Some dp -> one_file t dp

(* A library a side loaded that is neither under a root the challenge stands
   in for nor pre-checked counts as the image's own, so its file must lie in
   no place an answer's file is found in ([answer_place]): otherwise a file
   the answer put in the working directory, which the load path binds
   implicitly, could stand in for an image library of the same name. And the
   directory the loader found it in must lie, by its real path, under one of
   the directories the run trusts for the image's own libraries
   ([trusted_dirs]): otherwise a file in a directory the load path binds
   without a [-Q], such as an XDG directory, could. A directory whose real
   path cannot be found is under none. [libs] are a side's loaded libraries
   with the files the loader recorded. Returns those that pass. *)
let check_provenance t ~side libs =
  CList.map_filter (fun (dp, file) ->
      match origin t dp with
      | Prechecked | Own -> None
      | Shared ->
        match answer_place t file with
        | Some place ->
          CErrors.user_err
            Pp.(str ("The " ^ side ^ " loaded the library " ^ DirPath.to_string dp ^
                     " from " ^ file ^ ", in " ^ place ^ ", where an answer's files are \
                      found. No root the challenge stands in for holds it and the config \
                      does not pre-check it, so it would count as the image's own. A \
                      -compare run refuses it."))
        | None ->
          let trusted = match realpath (Filename.dirname file) with
            | None -> false
            | Some found_in -> List.exists (fun dir -> path_under ~dir found_in) t.trusted_dirs
          in
          if trusted then Some dp
          else
            let dirs = match t.trusted_dirs with
              | [] -> "none in this run"
              | l -> String.concat ", " l
            in
            CErrors.user_err
              Pp.(str ("The " ^ side ^ " loaded the library " ^ DirPath.to_string dp ^
                       " from " ^ file ^ ", which is under none of the directories a \
                        -compare run trusts for the image's own libraries: the corelib \
                        directory, user-contrib and the directories of ROCQPATH and \
                        COQPATH (" ^ dirs ^ "). A -compare run refuses it.")))
    libs

(* Whether the answer's library [dp] is pinned by its sha256 as a challenge
   file: it is the answer's own, the challenge file at its path below the
   root the challenge stands in for ([path_below_root]) is one the config
   pins (real paths), and the file the answer's loader read it from has that
   file's sha256. The bytes then are the challenge's file of that library,
   whose own pin [prepare] checked. An answer file that cannot be read is
   not pinned, and the run is refused, naming the library and its file: each
   caller would refuse a library that is not pinned, and this says why. *)
let pinned t dp = match origin t dp with
  | Prechecked | Shared -> false
  | Own ->
    match t.path_below_root dp, DirPath.Map.find_opt dp t.answer_files with
    | None, _ | _, None -> false
    | Some rel, Some file ->
      match realpath (Filename.concat t.dir rel) with
      | None -> false
      | Some path ->
        let sha () =
          file_sha256 file ~what:(fun () ->
              "The answer loaded the library " ^ DirPath.to_string dp ^ " from " ^ file ^
              ", which cannot be read")
        in
        List.exists (fun (real, pin) -> String.equal real path && String.equal pin (sha ()))
          t.pins

(* The dependency digests each library records, as a map by library. *)
let deps_map deps =
  List.fold_left (fun m (dp, a) -> DirPath.Map.add dp a m) DirPath.Map.empty deps

(* [roots] and every library they rest on, by the dependencies [deps] (a
   [deps_map]) records for each library of the closure, transitively. *)
let closure deps roots =
  let rec walk acc = function
    | [] -> acc
    | dp :: tl ->
      if DirPath.Set.mem dp acc then walk acc tl
      else
        let next = match DirPath.Map.find_opt dp deps with
          | None -> []
          | Some a -> Array.to_list (Array.map fst a)
        in
        walk (DirPath.Set.add dp acc) (next @ tl)
  in
  walk DirPath.Set.empty roots

(* What a pre-checked library rests on: every library of the closure of a
   pre-checked one, [closures] in the config's order, must be pre-checked
   itself, pinned by its sha256 as a challenge file, or the image's own. The
   digest a pre-checked library records for a dependency is the one the
   dependency's own file states, which pins nothing, and the pre-checked
   library was never checked against the run's file of it, so a kernel check
   of that file in this run is not enough either. The refusal names the
   first pre-checked library, in the config's order, whose closure holds the
   library refused. *)
let check_prechecked_deps t ~closures =
  List.iter (fun (p, deps) ->
      DirPath.Set.iter (fun dep ->
          match origin t dep with
          | Prechecked -> ()
          | Own | Shared ->
            if not (pinned t dep || image_own t dep) then
              CErrors.user_err
                Pp.(str ("The pre-checked library " ^ DirPath.to_string p ^
                         " depends on the library " ^ DirPath.to_string dep ^
                         ", which is neither pre-checked by the config, nor pinned by its \
                          sha256 as a challenge file, nor the image's own. The digest the \
                          pre-checked library records for it pins nothing: a library's \
                          digest is the one its own file states. A kernel check of it is \
                          not enough either, since the pre-checked library was not checked \
                          against it. A -compare run refuses it.")))
        deps)
    closures

(* A library under a root the challenge stands in for that the run loaded
   without a kernel check ([CheckLibrary.unchecked]: a library given with
   -admit, or a dependency of one given with -norec or -admit) is refused
   unless the config pre-checks it, the config pins its sha256 as a challenge
   file, or -admit names it itself ([admitted]): a library an [admitted] one
   depends on is not exempt. Such a library is not checked, and unless the
   challenge files Require it, it is not compared either. A shared library is
   not refused here. *)
let check_unchecked t ~admitted =
  List.iter (fun dp ->
      match origin t dp with
      | Prechecked | Shared -> ()
      | Own ->
        if not (List.exists (DirPath.equal dp) admitted || pinned t dp) then
          CErrors.user_err
            Pp.(str ("The answer library " ^ DirPath.to_string dp ^ " was loaded without \
                      a check, as a dependency of a library given with -norec or -admit, \
                      and it is neither pre-checked by the config, nor pinned by its \
                      sha256 as a challenge file, nor given with -admit itself. A \
                      -compare run refuses it.")))
    (CheckLibrary.unchecked ())

(* The dependency digests a challenge library and its answer library record
   for a library that is one file for both sides ([one_file]) must be equal:
   otherwise the two sides were built against different copies of it, and
   their kernel names would name different objects. That is every pre-checked
   library, and every shared library the answer loaded -- outside the roots
   the challenge stands in for and not pre-checked -- whose file passed
   [check_provenance]. Checked before the challenge is imported. *)
let check_dep_digests t ~challenge ~answer =
  let digest_of deps dp =
    Array.fold_left (fun acc (d, dg) -> if DirPath.equal d dp then Some dg else acc) None deps
  in
  let same (Safe_typing.Dvo_or_vi x) (Safe_typing.Dvo_or_vi y) = String.equal x y in
  List.iter (fun (lib, ch_deps) ->
      match List.find_opt (fun (l, _) -> DirPath.equal l lib) answer with
      | None -> ()
      | Some (_, an_deps) ->
        Array.iter (fun (dep, ch_digest) ->
            if one_file t dep then
              let prechecked = List.exists (DirPath.equal dep) t.prechecked in
              match digest_of an_deps dep with
              | Some an_digest when not (same ch_digest an_digest) ->
                CErrors.user_err
                  Pp.(str ("The library " ^ DirPath.to_string lib ^
                           " depends on the " ^
                           (if prechecked then "pre-checked" else "shared") ^
                           " library " ^ DirPath.to_string dep ^
                           " with a different digest on the challenge side and on the \
                            answer side."))
              | _ -> ())
          ch_deps)
    challenge

(* The challenge load puts the challenge directory in front of the answer's
   directories under the roots it stands in for, and leaves those behind it:
   a challenge library that the directory does not hold would be read from
   the answer's file and then compared with itself. So a library the
   challenge loaded under such a root must have been read from a file whose
   real path lies under the real path of the challenge directory, unless it
   is pre-checked: a pre-checked library may resolve to the answer's file,
   and [check_same_files] tests that it is read from pinned bytes. A file or
   a challenge directory whose real path cannot be found is not under it.
   [libs] are the challenge's loaded libraries with the files the loader
   recorded. *)
let check_challenge_dir t libs =
  List.iter (fun (dp, file) ->
      match origin t dp with
      | Prechecked | Shared -> ()
      | Own ->
        let inside = match t.challenge_dir, realpath file with
          | Some dir, Some f -> path_under ~dir f
          | None, _ | _, None -> false
        in
        if not inside then
          CErrors.user_err
            Pp.(str ("The challenge loaded the library " ^ DirPath.to_string dp ^ " from " ^
                     file ^ ", which is not under the challenge directory. A challenge \
                      library under a root the challenge stands in for is read from the \
                      challenge directory unless it is pre-checked. A -compare run \
                      refuses it.")))
    libs

(* A library that is one file for both sides ([one_file]) is so only if the
   challenge load reads it from the file the answer read. The challenge's
   load path is the answer's with the challenge directory bound in front
   under the roots it stands in for, but that binding can take a directory
   from another logical path (a link in the challenge directory to a
   directory the load path already binds), and a name the two sides share
   may then resolve to another file. So a shared library the answer loaded
   too must come from the answer's file, by real path. A pre-checked library
   must come from the answer's file, or from another file of the sha256 the
   config pins, such as a copy in the challenge directory: the answer's file
   has that sha256 as well ([check_prechecked_files],
   [check_prechecked_read]), so either way the bytes are pinned. [libs] are
   the challenge's loaded libraries with the files the loader recorded. *)
let check_same_files t libs =
  List.iter (fun (dp, file) ->
      match origin t dp with
      | Own -> ()
      | Shared ->
        (match DirPath.Map.find_opt dp t.answer_files with
         | Some an_file when not (same_real_file file an_file) ->
           CErrors.user_err
             Pp.(str ("The challenge loaded the shared library " ^ DirPath.to_string dp ^
                      " from " ^ file ^ ", and the answer loaded it from " ^ an_file ^
                      ": the two sides would read different files under one library \
                       name. A -compare run refuses it."))
         | Some _ | None -> ())
      | Prechecked ->
        let answers = match DirPath.Map.find_opt dp t.answer_files with
          | Some an_file -> same_real_file an_file file
          | None -> false
        in
        if not answers then
          let got =
            file_sha256 file ~what:(fun () ->
                "The challenge loaded the pre-checked library " ^ DirPath.to_string dp ^
                " from " ^ file ^ ", which cannot be read")
          in
          let pins p = DirPath.equal p.pc_library dp && String.equal p.pc_sha256 got in
          if not (List.exists pins t.cfg.cfg_prechecked) then
            CErrors.user_err
              Pp.(str ("The challenge loaded the pre-checked library " ^ DirPath.to_string dp ^
                       " from " ^ file ^ ", which is not the file the answer loaded it \
                        from, and whose sha256 is " ^ got ^ ", not the one the config \
                        pins. A -compare run refuses it.")))
    libs

(* The challenge load, between two swaps of this process's per-library tables.
   The challenge libraries have the answer's names, so they need tables of
   their own; nothing of the challenge is left in them afterwards.

   The challenge files' own Require lines decide which shared libraries their
   closure reaches, and the answer's tree may Require more of the image than
   they do. A shared library carries universe constraints, and some of them
   relate levels of OTHER shared libraries, which both sides do know; loading
   one more of the image is not something the answer asserted, so the
   challenge environment loads the same shared libraries the answer did
   (dispatch://BET-901). What is left for the constraint check to catch is a
   constraint the answer's OWN libraries add, which is the answer's doing.

   Only the challenge files' closure is compared declaration by declaration.

   What pins each library this load reads, and so what the comparison rests
   on:
   - a challenge library under a root the challenge stands in for, unless
     pre-checked, is read from a file under the challenge directory
     ([check_challenge_dir]);
   - a pre-checked library is read from the file the answer's loader read,
     whose sha256 is the one the config pins ([check_prechecked_files],
     [check_prechecked_read]), or from another file of that sha256
     ([check_same_files]);
   - a shared library lies in no place an answer's file is found in and was
     found in a directory the run trusts for the image's own libraries
     ([check_provenance], on this side as on the answer's), it is read from
     the file the answer's loader read when the answer loaded it too
     ([check_same_files]), and every library naming it as a dependency
     records the same digest on both sides ([check_dep_digests]).
   [check_open_roots] has already refused the run if the answer loaded a
   library the config does not pre-check from a bound root the challenge
   does not stand in for. Each check refuses the run rather than reporting a
   verdict, and the checks of this load all run before anything is
   imported. *)
let load_challenge t senv0 ~answer_deps =
  let saved = CheckLibrary.swap_tables (CheckLibrary.fresh_tables ()) in
  let restore () = ignore (CheckLibrary.swap_tables saved) in
  Fun.protect ~finally:restore (fun () ->
      t.add_challenge_load_path ();
      (* A pre-checked library is NOT a shared one, whatever root it sits
         under. The config names it, and the option puts it on the admit
         list, so the answer's environment holds it whether its tree
         Requires it or not; were it shared too, a config could add a
         library to the CHALLENGE's graph and so decide what the challenge
         stands on. The config pins bytes; it does not say what the
         challenge is. In production this changes nothing -- a pre-checked
         library is a registered answer object, under the root the
         challenge stands in for -- and the challenge still loads one
         whose own files Require it, through its closure. *)
      let shared =
        CList.map_filter (fun (dp, _) ->
            match origin t dp with
            | Shared -> Some dp
            | Prechecked | Own -> None)
          answer_deps
      in
      let needed, all = CheckLibrary.intern_challenge t.files shared in
      let files = CheckLibrary.challenge_files all in
      check_challenge_dir t files;
      ignore (check_provenance t ~side:"challenge" files);
      let challenge_deps = CheckLibrary.challenge_deps needed in
      check_dep_digests t ~challenge:(CheckLibrary.challenge_deps all) ~answer:answer_deps;
      check_same_files t files;
      let senv = CheckLibrary.import_challenge senv0 all in
      Safe_typing.env_of_safe_env senv, challenge_deps)

(************************************************************************)
(** {6 Comparing the two environments} *)

type failure = { f_name : string; f_reason : string }

(* The identity seed: a level of a library that is one file for both sides
   ([one_file]: a pre-checked library, or a shared one outside the roots the
   challenge stands in for), or of a library of the answer's pre-checked
   closure ([prechecked_closure]), every library of which [run] has refused
   unless it is pre-checked, pinned by its sha256 as a challenge file or the
   image's own. A level no compared declaration names is in the map only
   through this: the body of an opaque proof is never compared, and the
   libraries of the closure that [run] skips are not compared at all, so a
   challenge proof's constraint on such a level would otherwise never be
   asked of the answer. *)
let seed_umap t ~challenge_env ~answer_env =
  let seeded dp = one_file t dp || DirPath.Set.mem dp t.prechecked_closure in
  let gch = Environ.universes challenge_env and gan = Environ.universes answer_env in
  let an = UGraph.domain gan in
  Univ.Level.Set.fold (fun u m ->
      match Univ.Level.name u with
      | None -> m
      | Some ug ->
        let dp, _, _ = Univ.UGlobal.repr ug in
        if seeded dp && Univ.Level.Set.mem u an then add_level m u u else m)
    (UGraph.domain gch) empty_umap

(* The items a reason lists: sorted, the first five, then [(and <n> more)]
   for the rest; [None] for no item. [around] puts the shown items in the
   sentence that names them, before the count of the rest. *)
let summarize ?(around = Fun.id) items =
  match List.sort String.compare items with
  | [] -> None
  | l ->
    let shown = 5 in
    let n = List.length l in
    Some (around (String.concat ", " (CList.firstn (min shown n) l)) ^
          (if n > shown then Printf.sprintf " (and %d more)" (n - shown) else ""))

(* The two directions are not the same question.

   Every challenge constraint, mapped, must hold in the answer: the answer
   must stand where the challenge stands. It is also where an answer that
   contradicts the challenge is caught: the answer's graph alone is
   consistent, since the kernel checked it, so if the answer entails every
   challenge constraint the union of the two is satisfiable.

   The other direction asks what the answer ADDS, and passes over one shape
   alone: a constraint between two of the IMAGE's levels. A proof adds
   those as a matter of course -- it instantiates the image's definitions,
   and the kernel records what that costs -- and they say nothing about the
   task, since the challenge's statements do not stand on the image's
   levels relative to each other. Today's grade of record, a Checker file
   compiled against the task's statements with the kernel merging the
   proof's constraints into one environment, accepts all of them, and two
   runs of the real task show what refusing them costs: the key failed on
   LinuxProcessSemantics.LinuxProcessSem.Fs.33 <= Stdlib.Logic.Classical_Pred_Type.21
   and the untouched control on Fs.33 < Corelib.Init.Logic.22, each between
   two of the image's levels, every theorem of both runs failing on that
   one line (dispatch://BET-901).

   Every other pair is compared, the challenge's own levels to each other
   AND to the image's. An answer that relates one of the challenge's own
   universes to one of the image's has fixed where that universe sits, and
   a statement over it then says less than the challenge's does: a
   statement that injects Type@{u} into a type at an image level is not
   provable while u and that level are apart, and is provable once the
   answer puts u below it. That is a forgery, and it carries no Constraint
   command -- the Qed records it (the adversarial review of 0de0865d26).

   A config that tolerates [answer-universe-constraints] skips this
   direction alone, and only once the challenge-to-answer direction has
   passed; the declaration comparison, the axiom checks and the kernel
   check are untouched. The flag is recorded on every theorem the answer
   holds only when this direction would have failed. Its object is the
   bounded summary of the skipped constraints, so a passing verdict says
   what it cost.

   Both directions compare the PROJECTION of one graph onto the mapped
   levels ([constraints_for], which walks on through a level it does not
   keep), so a path through levels the map does not hold is compared like a
   direct edge, and a forgery cannot be routed around.

   Every failing constraint is reported, not the first: a run that names one
   costs another run to learn whether there are more. *)
let check_constraints t ~challenge_env ~answer_env m =
  let gch = Environ.universes challenge_env and gan = Environ.universes answer_env in
  let own u = match Univ.Level.name u with
    | None -> false
    | Some ug -> let dp, _, _ = Univ.UGlobal.repr ug in t.under_challenge_root dp
  in
  let kept_ch = Univ.Level.Map.domain m.fwd and kept_an = Univ.Level.Map.domain m.bwd in
  (* [constraints_for ~kept] emits only constraints between kept levels, and
     the kept set IS the map's domain, so a level with no image cannot reach
     here. It is an anomaly rather than a pass: a constraint passed over in
     silence is a check that did not run. *)
  let image map u = match Univ.Level.Map.find_opt u map with
    | Some v -> v
    | None ->
      CErrors.anomaly
        Pp.(str ("The comparator projected a universe constraint onto " ^
                 Univ.Level.to_string u ^ ", which its level map does not hold."))
  in
  let fails ~skip map graph cs =
    let bad = Univ.UnivConstraints.fold (fun (u, k, v) acc ->
        let u' = image map u and v' = image map v in
        if skip u' v' || UGraph.check_constraint graph (u', k, v') then acc
        else
          Printf.sprintf "%s %s %s"
            (Univ.Level.to_string u)
            (match k with Univ.UnivConstraint.Lt -> "<" | Le -> "<=" | Eq -> "=")
            (Univ.Level.to_string v) :: acc)
        cs []
    in
    summarize ~around:(Printf.sprintf "the constraint %s does not hold on the other side") bad
  in
  let never _ _ = false in
  match fails ~skip:never m.fwd gan (UGraph.constraints_for ~kept:kept_ch gch) with
  | Some e -> Some ("the challenge has a universe constraint the answer does not: " ^ e), None
  | None ->
    let both_image u' v' = not (own u') && not (own v') in
    match fails ~skip:both_image m.bwd gch (UGraph.constraints_for ~kept:kept_an gan) with
    | Some e when List.mem_assoc answer_universe_constraints t.cfg.cfg_flags -> None, Some e
    | Some e -> Some ("the answer has a universe constraint the challenge does not: " ^ e), None
    | None -> None, None

(* The global elimination constraints: which sort qualities eliminate to
   which. An environment's quality graph ([Environ.qualities]) holds the
   constant qualities Prop, SProp and Type and every global sort a loaded
   library declares ([Sort s]), with the elimination constraints between
   them ([Constraint s -> Prop]). Such a constraint is not part of any
   declaration the comparison walks, yet it decides what a match on a value
   of a type in that sort may return, and so what a statement over it says.

   Qualities are compared by identity, with no map: in 9.2 a global sort is
   a [Sorts.QGlobal.t], its library and its name, which [QGlobal.equal]
   compares, and the kernel numbers no quality, so the challenge's sort and
   the answer's sort of one library and one name are one quality.

   Let Q be the global sorts of the challenge graph. (1) Every ordered pair
   (a, b), a <> b, of the challenge graph's qualities with a or b in Q that
   eliminates in the challenge must have both qualities declared in the
   answer graph and eliminate there. (2) Every ordered pair (a, b), a <> b,
   of the answer graph's qualities with a or b in Q that eliminates in the
   answer must have both qualities declared in the challenge graph and
   eliminate there. [QGraph.eliminates_to] is reachability in the graph, so
   a path through a sort only the answer declares counts, and a pair of a
   challenge sort and a sort only the answer declares that eliminates in the
   answer fails. Pairs of two sorts only the answer declares, and pairs of
   two constants, are not compared.

   Both graphs are read with [ignore_constraints] off, so that
   [eliminates_to] answers from the constraints themselves, and it is asked
   only of qualities its graph declares ([QGraph.is_declared]): on any
   other it raises an anomaly. The tolerance [answer-universe-constraints]
   skips neither direction. Direction (1) is checked first, and the failing
   pairs of the first direction that fails are listed as [check_constraints]
   lists universe constraints ([summarize]): sorted, up to five, then how
   many more. *)
let check_elim_constraints ~challenge_env ~answer_env =
  let gch = QGraph.set_ignore_constraints false (Environ.qualities challenge_env)
  and gan = QGraph.set_ignore_constraints false (Environ.qualities answer_env) in
  let globals = Sorts.Quality.Set.filter Sorts.Quality.is_qglobal (QGraph.domain gch) in
  let eliminates g a b =
    QGraph.is_declared a g && QGraph.is_declared b g && QGraph.eliminates_to g a b
  in
  let name = function
    | Sorts.Quality.QConstant c -> Pp.string_of_ppcmds (Sorts.Quality.Constants.pr c)
    | Sorts.Quality.QVar v ->
      match Sorts.QVar.repr v with
      | Sorts.QVar.Global g -> Sorts.QGlobal.to_string g
      | Sorts.QVar.Var _ | Sorts.QVar.Unif _ -> Sorts.QVar.to_string v
  in
  (* The pairs of [from]'s qualities, one of them in Q, that eliminate in
     [from] and not in [onto]. *)
  let fails from onto =
    let qs = Sorts.Quality.Set.elements (QGraph.domain from) in
    let bad = List.fold_left (fun acc a ->
        List.fold_left (fun acc b ->
            if Sorts.Quality.equal a b
            || not (Sorts.Quality.Set.mem a globals || Sorts.Quality.Set.mem b globals)
            || not (eliminates from a b)
            || eliminates onto a b
            then acc
            else Printf.sprintf "%s -> %s" (name a) (name b) :: acc)
          acc qs)
        [] qs
    in
    summarize bad
  in
  match fails gch gan with
  | Some e -> Some ("the challenge has an elimination constraint the answer does not: " ^ e)
  | None ->
    match fails gan gch with
    | Some e -> Some ("the answer has an elimination constraint the challenge does not: " ^ e)
    | None -> None

(* The kernel names of the constants that a challenge declaration names in
   what the comparison reads of it -- a constant's type and transparent
   body, a block's parameters, arities, constructor types and projection
   types, and every field of a module type, the types of its functor
   parameters included -- each under its user name and its canonical one,
   so a reference through another name of the constant counts. An opaque
   body is not read: it is not compared, and what it names unfolds into no
   statement. Nor is a rewrite rule, of which the comparison reads the
   symbols only. *)
let rec constr_names acc c = match Constr.kind c with
  | Constr.Const (k, _) ->
    KerName.Set.add (Constant.user k) (KerName.Set.add (Constant.canonical k) acc)
  | _ -> Constr.fold constr_names acc c

let const_names acc (cb : constant_body) =
  let acc = constr_names acc cb.const_type in
  match cb.const_body with
  | Def b -> constr_names acc b
  | Undef _ | OpaqueDef _ | Primitive _ | Symbol _ -> acc

let mind_names acc (mib : mutual_inductive_body) =
  let context acc ctx =
    List.fold_left (fun acc d ->
        Context.Rel.Declaration.fold_constr (fun c acc -> constr_names acc c) d acc)
      acc ctx
  in
  Array.fold_left (fun acc mip ->
      let acc = context acc mip.mind_arity_ctxt in
      let acc = constr_names acc mip.mind_user_arity in
      let acc = Array.fold_left constr_names acc mip.mind_user_lc in
      match mip.mind_record with
      | PrimRecord p -> Array.fold_left constr_names acc p.tys
      | NotRecord | FakeRecord -> acc)
    (context acc mib.mind_params_ctxt) mib.mind_packets

let rec signature_names acc = function
  | NoFunctor struc ->
    List.fold_left (fun acc (_, field) -> match field with
        | SFBconst cb -> const_names acc cb
        | SFBmind mib -> mind_names acc mib
        | SFBrules _ -> acc
        | SFBmodule mb -> signature_names acc (Mod_declarations.mod_type mb)
        | SFBmodtype mtb -> signature_names acc (Mod_declarations.mod_type mtb))
      acc struc
  | MoreFunctor (_, mtb, sign) ->
    signature_names (signature_names acc (Mod_declarations.mod_type mtb)) sign

(* Every challenge declaration, in the order the name sorts. A declaration the
   answer does not hold is a failure; a declaration only the answer holds is
   not visited.

   A constant is compared in three steps: whether the answer holds it at
   all, the primitive type each side registers it as ([eq_primitive_type],
   on each side the constant under the canonical name that side's
   environment gives it), and then [eq_const_body]. Its [named] reads the
   names that the compared challenge declarations -- the constants,
   inductive blocks and module types this walks -- name ([constr_names] and
   the functions after it), collected once in the run, the first time
   [eq_const_body] asks: for a challenge constant without a body, not
   stated as data, that the answer gives a transparent body.

   Returns the declarations that fail; apart from them, the global records
   that fail, [<universes>] ([check_constraints]) before [<qualities>]
   ([check_elim_constraints]); and the answer's universe constraints that
   the tolerance [answer-universe-constraints] skipped, summarized. *)
let compare_declarations t ~challenge_env ~answer_env ~libs ~theorems =
  let m = ref (seed_umap t ~challenge_env ~answer_env) in
  let failures = ref [] in
  let fail name reason = failures := { f_name = name; f_reason = reason } :: !failures in
  let deferred = ref [] in
  let step name f =
    match f !m with
    | m' -> m := m'
    | exception Diff d -> fail name d
    | exception Undecided d -> deferred := (name, f, d) :: !deferred
  in
  (* The module types an environment holds, by path. *)
  let modtypes env = Environ.(Internal.View.((view env).env_modtypes)) in
  let ch_modtypes = modtypes challenge_env in
  let names = lazy (
    let acc =
      Environ.fold_constants (fun c cb acc ->
          if in_libs libs (Constant.modpath c) then const_names acc cb else acc)
        challenge_env KerName.Set.empty
    in
    let acc =
      Environ.fold_inductives (fun i mib acc ->
          if in_libs libs (MutInd.modpath i) then mind_names acc mib else acc)
        challenge_env acc
    in
    ModPath.Map.fold (fun mp mt acc ->
        if in_libs libs mp then signature_names acc (Mod_declarations.mod_type mt) else acc)
      ch_modtypes acc)
  in
  Environ.fold_constants (fun c cb () ->
      if in_libs libs (Constant.modpath c) then
        let name = Constant.to_string c in
        if not (Environ.mem_constant c answer_env) then fail name "missing"
        else
          let cb', _, canonical = Environ.lookup_constant_key c answer_env in
          let c' = Constant.make (Constant.user c) canonical in
          let named = lazy (let names = Lazy.force names in
                            KerName.Set.mem (Constant.user c) names
                            || KerName.Set.mem (Constant.canonical c) names)
          in
          let sort = lazy (stated_sort challenge_env cb) in
          step name (fun m ->
              eq_primitive_type ~challenge_env ~answer_env c c';
              eq_const_body ~sort ~is_theorem:(CString.Set.mem name theorems) ~named m cb cb'))
    challenge_env ();
  Environ.fold_inductives (fun i mib () ->
      if in_libs libs (MutInd.modpath i) then
        let name = MutInd.to_string i in
        if not (Environ.mem_mind i answer_env) then fail name "missing"
        else step name (fun m -> eq_mib_body m mib (Environ.lookup_mind i answer_env)))
    challenge_env ();
  let an_modtypes = modtypes answer_env in
  ModPath.Map.iter (fun mp mt ->
      if in_libs libs mp then
        let name = ModPath.to_string mp in
        match ModPath.Map.find_opt mp an_modtypes with
        | None -> fail name "missing"
        | Some mt' ->
          step name (fun m -> eq_modtype m mt mt'))
    ch_modtypes;
  (* The declarations set aside as undecided, again, until a pass decides
     none of them. Each pending entry keeps the reason of its last
     comparison, so what is still undecided fails with that reason; no
     declaration is left both uncompared and unfailed. *)
  let rec again pending =
    let progress = ref false in
    let still = CList.map_filter (fun (name, f, _) ->
        match f !m with
        | m' -> m := m'; progress := true; None
        | exception Diff d -> fail name d; progress := true; None
        | exception Undecided d -> Some (name, f, d))
        pending
    in
    if not (CList.is_empty still) then
      if !progress then again still
      else List.iter (fun (name, _, d) -> fail name d) still
  in
  again (List.rev !deferred);
  let universes, skipped_answer_constraints =
    check_constraints t ~challenge_env ~answer_env !m
  in
  let qualities = check_elim_constraints ~challenge_env ~answer_env in
  let globals =
    List.filter_map (fun (name, reason) ->
        Option.map (fun r -> { f_name = name; f_reason = r }) reason)
      ["<universes>", universes; "<qualities>", qualities]
  in
  List.rev !failures, globals, skipped_answer_constraints

(************************************************************************)
(** {6 The verdict} *)

(* Every constant of [env] under the name it prints. Two constants can print
   the same name (the constant [thm] of a module [Q] of the library [R.P]
   and the constant [thm] of the library [R.P.Q]), so a name maps to all of
   them. *)
let constant_index env =
  Environ.fold_constants (fun c _ acc ->
      CString.Map.update (Constant.to_string c)
        (fun l -> Some (c :: Option.default [] l)) acc)
    env CString.Map.empty

(* Every constant of [env] under its kernel name. *)
let kernel_index env =
  Environ.fold_constants (fun c _ acc -> KerName.Map.add (Constant.user c) c acc) env KerName.Map.empty

(* Where an object lives, in words, for a refusal: "the constant g of
   module Q of the library R.P". *)
let describe_object obj =
  let rec path = function
    | ModPath.MPfile dp -> "the library " ^ DirPath.to_string dp
    | ModPath.MPdot (mp, l) -> "module " ^ Id.to_string l ^ " of " ^ path mp
    | ModPath.MPbound _ as mp -> "the functor parameter " ^ ModPath.to_string mp
  in
  match obj with
  | GlobRef.ConstRef c ->
    "the constant " ^ Id.to_string (Constant.label c) ^ " of " ^ path (Constant.modpath c)
  | GlobRef.IndRef (mind, _) | GlobRef.ConstructRef ((mind, _), _) ->
    "the inductive block " ^ Id.to_string (MutInd.label mind) ^ " of " ^ path (MutInd.modpath mind)
  | GlobRef.VarRef id -> "the section variable " ^ Id.to_string id


(* The first rewrite rule a module declares, as the symbol it rewrites. The
   walk reads the declarations themselves, not the environment's table of
   rules, which is keyed by the symbol a rule rewrites: a rule may rewrite
   a symbol of another library, and a module sealed by a signature that
   hides its rule puts no rule in the environment at all, though its body
   was checked with the rule in force. So it reads the signature, the
   structure that implements it, submodules, functor parameters and module
   types. A [Symbol] declaration is a constant, not a rule: it is an
   assumption, which the axiom check counts. *)
let rec rule_in_signature = function
  | NoFunctor struc -> rule_in_structure struc
  | MoreFunctor (_, mtb, sign) ->
    (match rule_in_signature (Mod_declarations.mod_type mtb) with
     | Some _ as r -> r
     | None -> rule_in_signature sign)

and rule_in_structure struc =
  List.find_map (fun (_, field) -> match field with
      | SFBrules { rewrules_rules = (c, _) :: _ } -> Some c
      | SFBrules { rewrules_rules = [] } | SFBconst _ | SFBmind _ -> None
      | SFBmodule mb -> rule_in_module mb
      | SFBmodtype mtb -> rule_in_signature (Mod_declarations.mod_type mtb))
    struc

and rule_in_module mb =
  match rule_in_signature (Mod_declarations.mod_type mb) with
  | Some _ as r -> r
  | None ->
    match Mod_declarations.mod_expr mb with
    | Mod_declarations.Struct (_, struc) -> rule_in_structure struc
    | Mod_declarations.(Abstract | Algebraic _ | FullStruct) -> None

(* The first rewrite rule one of [libs] declares, in the answer's
   environment, which holds every library the answer loaded. *)
let answer_rewrite_rule env libs =
  List.find_map (fun dp ->
      match Environ.lookup_module (ModPath.MPfile dp) env with
      | mb -> rule_in_module mb
      | exception Not_found ->
        CErrors.user_err
          Pp.(str ("The answer loaded the library " ^ DirPath.to_string dp ^
                   ", which its environment does not hold.")))
    libs

(* A permitted axiom is a declaration the task hands the agent, so it is
   matched by its kernel name, not by the name it prints: a module path and
   a library path can print alike, and the constant [g] of a module [Q] of
   the library [R.P] prints [R.P.Q.g], the name of the constant [g] of the
   library [R.P.Q]. An axiom constant the answer's proof reaches is the
   task's declaration when either
   - its module path, followed through every [MPdot] to its [MPfile], is
     rooted at a library that is one file for both sides ([one_file]): a
     pre-checked library, whose bytes the config pins by their sha256, or a
     shared one, outside the challenge's roots and not pre-checked, read
     from a file that lies in no place an answer's file is found in and that
     was found in a directory the run trusts for the image's own libraries
     ([check_provenance] refuses a run that read one from anywhere else). No
     answer file the run reads can add a constant under such an [MPfile].
     The constant may be a field of a sealed module that the library does
     not export: the closure walk reaches it through the implementation,
     where no environment lookup sees it, and it is still the library's own;
     or
   - both the challenge environment and the answer environment declare the
     same kernel name (the challenge's own files, which the declaration
     comparison holds the answer to, and the libraries both sides read from
     one file). These lookups see only exported fields. Requiring the
     answer's to export it keeps the constant under that comparison: an
     answer that seals a challenge module, hides its axiom and gives it
     another type is refused. An axiom hidden inside a sealed module of a
     challenge file is refused even when the challenge hides it too:
     fail-closed, since the comparison does not see such a field.
   A forged constant declared in a changed file has a module path rooted
   at that file, which lies under a root the challenge stands in for, so
   its kernel name is neither under a one-file [MPfile] nor one the
   challenge declares.
   The same rule, on the inductive block's kernel name, decides whether a
   tolerated flag's object is the task's own. An axiom that is no constant
   is reached only when no library declares it, so the verdict counts it
   as no declaration of the task's without asking this rule. *)
let task_declares t ~challenge_env ~answer_env = function
  | GlobRef.ConstRef c ->
    rooted_one_file t (Constant.modpath c)
    || (Environ.mem_constant c challenge_env && Environ.mem_constant c answer_env)
  | GlobRef.IndRef (mind, _) | GlobRef.ConstructRef ((mind, _), _) ->
    rooted_one_file t (MutInd.modpath mind)
    || (Environ.mem_mind mind challenge_env && Environ.mem_mind mind answer_env)
  | GlobRef.VarRef _ -> false

(* Why [task_declares] refused [obj], for the refusal's text. *)
let why_not_task ~challenge_env ~answer_env obj =
  let ch, an = match obj with
    | GlobRef.ConstRef c -> Environ.mem_constant c challenge_env, Environ.mem_constant c answer_env
    | GlobRef.IndRef (mind, _) | GlobRef.ConstructRef ((mind, _), _) ->
      Environ.mem_mind mind challenge_env, Environ.mem_mind mind answer_env
    | GlobRef.VarRef _ -> false, false
  in
  let why =
    match obj with
    | GlobRef.VarRef _ -> "a section variable is no declaration of the task's"
    | _ ->
      if ch && not an then
        "the challenge declares it but the answer does not export it, and it lies under no \
         pre-checked or shared library"
      else
        "the challenge does not declare it (or hides it in a sealed module), and it lies \
         under no pre-checked or shared library"
  in
  "the proof reaches " ^ describe_object obj ^ ": " ^ why

let run t env access senv0 ~answer_deps ~admitted =
  let loaded = CheckLibrary.interned_files () in
  let t =
    { t with answer_files =
               List.fold_left (fun m (dp, file) -> DirPath.Map.add dp file m)
                 DirPath.Map.empty loaded }
  in
  check_prechecked_read t;
  check_open_roots t ~answer_deps;
  let t = { t with outside = check_provenance t ~side:"answer" loaded } in
  (* The answer's pre-checked closure, computed once: the closure of each
     pre-checked library, in the config's order, and their union. *)
  let answer_graph = deps_map answer_deps in
  let closures = List.map (fun p -> p, closure answer_graph [p]) t.prechecked in
  let t =
    { t with prechecked_closure =
               List.fold_left (fun s (_, c) -> DirPath.Set.union s c) DirPath.Set.empty closures }
  in
  check_prechecked_deps t ~closures;
  check_unchecked t ~admitted;
  let challenge_env, all_deps = load_challenge t senv0 ~answer_deps in
  (* A library of the challenge's pre-checked closure that is pre-checked or
     shared is not compared: the config pins a pre-checked library's bytes, a
     shared one is the image's, and walking them would read the whole
     standard library on every run. A library of the closure that is the
     answer's own, such as one pinned by its sha256 as a challenge file, is
     compared, as every other library of the challenge files' closure is. *)
  let skip =
    DirPath.Set.filter (fun dp -> match origin t dp with
        | Prechecked | Shared -> true
        | Own -> false)
      (closure (deps_map all_deps) t.prechecked)
  in
  let libs =
    CList.map_filter (fun (dp, _) -> if DirPath.Set.mem dp skip then None else Some dp)
      all_deps
  in
  let ch_index = constant_index challenge_env in
  (* A theorem the challenge does not state, or states twice under one
     printed name, is a config error, not a verdict. *)
  let ch_theorem th =
    match CString.Map.find_opt th.th_name ch_index with
    | None | Some [] ->
      CErrors.user_err
        Pp.(str ("The config names the theorem " ^ th.th_name ^
                 ", which the challenge does not hold."))
    | Some [c] -> c
    | Some (_ :: _ :: _) ->
      CErrors.user_err
        Pp.(str ("The config names the theorem " ^ th.th_name ^
                 ", a name that two constants of the challenge print."))
  in
  List.iter (fun th -> ignore (ch_theorem th)) t.cfg.cfg_theorems;
  let theorems =
    List.fold_left (fun acc th -> CString.Set.add th.th_name acc) CString.Set.empty
      t.cfg.cfg_theorems
  in
  let failures, globals, skipped_answer_constraints =
    compare_declarations t ~challenge_env ~answer_env:env ~libs ~theorems
  in
  let failed_decl =
    List.fold_left (fun acc f -> CString.Map.add f.f_name f.f_reason acc) CString.Map.empty failures
  in
  (* The theorem a verdict reads is the answer's constant of the challenge
     theorem's kernel name, not whichever answer constant prints its name:
     a module Q of the library R.P holding a constant thm prints R.P.Q.thm,
     the name of the theorem thm of the library R.P.Q. When the answer holds
     both, the theorem fails as declared twice under one name; when it lacks
     the theorem's kernel name, it fails as missing (the declaration
     comparison, which matches by kernel name too, says the same). Either
     way the verdict's axioms and flags are the kernel-name constant's, never
     the other's. *)
  let an_index = constant_index env in
  let an_kernel = kernel_index env in
  (* Every library the answer loaded is the answer's to answer for, except
     one that is one file for both sides ([one_file]): a pre-checked one and
     a shared one may carry rules the task did not write. That includes a
     library only the answer has, which the declaration comparison does not
     visit, and a library a pre-checked one rests on that is pinned by its
     sha256 as a challenge file: its rules are the challenge's, and the
     answer's copy declares them again. *)
  let rewrite_rule =
    if t.cfg.cfg_rewrite_rules then None
    else
      answer_rewrite_rule env
        (CList.map_filter (fun (dp, _) -> if one_file t dp then None else Some dp)
            answer_deps)
  in
  let st = Check_closure.closure_state env access in
  let records =
    List.map (fun th ->
        let permitted = match th.th_axioms with
          | Some l -> l
          | None -> t.cfg.cfg_axioms
        in
        let verdict, reason, axioms, flags =
          let printing = Option.default [] (CString.Map.find_opt th.th_name an_index) in
          match KerName.Map.find_opt (Constant.user (ch_theorem th)) an_kernel with
          | None -> "fail", "missing", [], []
          | Some kn ->
            let axioms, flags = Check_closure.axioms_and_flags st kn in
            let flags = List.map (fun (k, o, obj) -> k, o, Some obj) flags in
            let flags =
              match skipped_answer_constraints with
              | Some constraints ->
                (answer_universe_constraints, constraints, None) :: flags
              | None -> flags
            in
            let bad_axioms = List.filter (fun (a, _) -> not (List.mem a permitted)) axioms in
            (* A permitted name the proof reaches through an object the
               task did not declare: a forgery of that name. *)
            let forged_axioms =
              List.filter (fun (a, obj) ->
                  List.mem a permitted
                  && not (match obj with
                      | GlobRef.ConstRef _ -> task_declares t ~challenge_env ~answer_env:env obj
                      | GlobRef.IndRef _ | GlobRef.ConstructRef _ | GlobRef.VarRef _ -> false))
                axioms
            in
            let axioms = CString.Set.elements (CString.Set.of_list (List.map fst axioms)) in
            (* A config entry tolerates a flag when it names the same kind
               and either no object at all, or the flag's object by the name
               it prints AND that object is the task's own declaration of
               that name, by the rule for permitted axioms
               ([task_declares]). *)
            let names_it (kind, printed, _) (k, o) =
              String.equal k kind && (match o with None -> true | Some o -> String.equal o printed)
            in
            let tolerated ((_, _, obj) as f) =
              List.exists (fun ((_, o) as entry) ->
                  names_it f entry
                  && (match o, obj with
                      | None, _ -> true
                      | Some _, Some obj -> task_declares t ~challenge_env ~answer_env:env obj
                      | Some _, None -> false))
                t.cfg.cfg_flags
            in
            let bad_flags = List.filter (fun f -> not (tolerated f)) flags in
            (* The verdict prints each (kind, printed object) once, in the
               order of [flags]: sorted, after any skipped constraints. *)
            let flags =
              List.fold_right (fun (k, o, _) acc ->
                  match acc with
                  | (k', o') :: _ when String.equal k k' && String.equal o o' -> acc
                  | _ -> (k, o) :: acc)
                flags []
            in
            (* A challenge declaration the answer changed is a changed task,
               whichever theorem names it: the statements are written against
               those definitions, so no theorem of the run can pass. The
               theorem's own record names its own difference when it has one. *)
            let reason =
              if List.length printing > 1 then
                let objs =
                  List.sort String.compare
                    (List.map (fun c -> describe_object (GlobRef.ConstRef c)) printing)
                in
                Some ("the answer declares " ^ string_of_int (List.length printing) ^
                      " constants that print the theorem's name: " ^ String.concat " and " objs)
              else
              match CString.Map.find_opt th.th_name failed_decl with
              | Some d -> Some d
              | None ->
                match failures with
                | f :: _ ->
                  Some ("the challenge declaration " ^ f.f_name ^ " differs: " ^ f.f_reason)
                | [] ->
                  match globals with
                  | g :: _ -> Some g.f_reason
                  | [] ->
                    match rewrite_rule with
                    | Some c ->
                      Some ("the answer declares a rewrite rule on " ^ Constant.to_string c)
                    | None ->
                    match bad_axioms with
                      | (a, _) :: _ -> Some ("the axiom " ^ a ^ " is not permitted")
                      | [] ->
                      match forged_axioms with
                      | (a, obj) :: _ ->
                        Some ("the axiom " ^ a ^ " is not the task's declaration of that name: " ^
                              why_not_task ~challenge_env ~answer_env:env obj)
                      | [] ->
                        match bad_flags with
                        | ((k, o, obj) as f) :: _ ->
                          let by_name =
                            List.exists (fun ((_, e) as entry) -> Option.has_some e && names_it f entry)
                              t.cfg.cfg_flags
                          in
                          Some ("the relaxed typing flag " ^ k ^ " on " ^ o ^ " is not tolerated" ^
                                match by_name, obj with
                                | true, Some obj ->
                                  ": the config tolerates it on that name, but " ^ o ^
                                  " is not the task's declaration of that name: " ^
                                  why_not_task ~challenge_env ~answer_env:env obj
                                | _ -> "")
                        | [] -> None
            in
            (match reason with
             | Some r -> "fail", r, axioms, flags
             | None -> "pass", "", axioms, flags)
        in
        Json.Obj [
          "name", Json.Str th.th_name;
          "verdict", Json.Str verdict;
          "reason", Json.Str reason;
          "axioms", Json.List (List.map (fun a -> Json.Str a) axioms);
          "flags", Json.List (List.map (fun (k, o) -> Json.Obj ["kind", Json.Str k;
                                                                "object", Json.Str o]) flags);
        ])
      t.cfg.cfg_theorems
  in
  let decls =
    List.map (fun f -> Json.Obj ["name", Json.Str f.f_name; "reason", Json.Str f.f_reason])
      (failures @ globals)
  in
  (* The libraries given with -admit, which the run loads without a check:
     [admitted] as the caller gives it, each by its full logical name, once,
     in command-line order; a pre-checked library only when -admit names it
     too. *)
  let doc = Json.Obj [
      "format", Json.Int 1;
      "theorems", Json.List records;
      "declarations", Json.List decls;
      "admitted", Json.List (List.map (fun dp -> Json.Str (DirPath.to_string dp)) admitted);
    ] in
  let ch = open_out t.out in
  Fun.protect ~finally:(fun () -> close_out ch) (fun () ->
      output_string ch (Json.to_string doc);
      output_char ch '\n')
