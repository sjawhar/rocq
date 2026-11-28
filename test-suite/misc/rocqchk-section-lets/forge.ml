(* Forge the .vo files of rocqchk_section_lets.sh. GOOD and BAD are two
   compilations of one library. The helpers, and the value layouts they
   rely on, are those of misc/rocqchk_forge_lib.ml; this file also relies
   on these, from checker/values.ml:

   - constant_body field 2: OpaqueDef is tag 2 [handle], a handle being
     [substitutions; cooking information; library; index], the index that
     of the proof in its library's table of opaque proofs; field 8: the
     typing flags;
   - opaques segment: the table, an array of
     Some ((proof, private universes), _) | None.

   Commands (each writes a new file; the inputs are left as they are):
     forge.ml splice GOOD.vo BAD.vo NAME OUT.vo
       GOOD with BAD's table of opaque proofs. The tables must have the
       same length and hold the same lemmas in the same order (BAD's pad*
       for any of GOOD's), and NAME's two proofs must differ;
     forge.ml handle GOOD.vo BAD.vo NAME OUT.vo
       GOOD with NAME's opaque handle, its cooking information included,
       taken from BAD; NAME must be the same entry of both tables;
     forge.ml user GOOD.vo NAME N FROM TO OUT.vo
       GOOD where, in its stored proof of NAME, the Nth constant labelled
       FROM (N from 1) gets the user name of the constant labelled TO that
       the proof names; its canonical name stays FROM's. The constants are
       counted in a depth-first, left-to-right walk of the proof, a node
       shared by two places once at each: the order in which the binding
       and rocqchk's typing meet them in the cooked proof;
     forge.ml flags SRC.vo NAME DONOR OUT.vo
       SRC with the typing flags of its constant DONOR given to its
       constant NAME. *)

#use "./misc/rocqchk_forge_lib.ml";;

let cb_of file name = constant_of (root_struc (library_value file)) name

(* The index in its library's table of the opaque proof of a constant_body. *)
let opaque_index what cb =
  let body = field cb 2 in
  expect ~size:1 (what ^ "'s body (OpaqueDef)") 2 body;
  let o = field body 0 in
  expect ~size:4 (what ^ "'s opaque handle") 0 o;
  to_int (field o 3)

(* The (index, label) of the opaque constants of a library's root
   structure, by index. *)
let opaque_labels file =
  list_of (root_struc (library_value file))
  |> List.filter_map (fun it ->
         let sfb = item_field it in
         if tag sfb <> 0 then None
         else
           let cb = field sfb 0 in
           let body = field cb 2 in
           if is_block body && tag body = 2 then Some (opaque_index (item_label it) cb, item_label it)
           else None)
  |> List.sort compare

let table file = segment_value file "opaques"

let entry_term what tbl i =
  if i < 0 || i >= size tbl then fail "%s: no entry %d in a table of %d" what i (size tbl);
  let e = field tbl i in
  if Obj.is_int e then fail "%s: entry %d of the table is empty" what i;
  field (field (field e 0) 0) 0

(* Write [dst], [src] with the constant_body of its constant [name]
   replaced by [f] of it. *)
let rewrite_constant ~src ~dst name f =
  rewrite_vo ~src ~dst
    [ ("library", fun disk ->
          set_root_struc disk (constant_update (root_struc disk) name f);
          disk) ]

let splice good bad name out =
  let ig = opaque_index ("good " ^ name) (cb_of good name)
  and ib = opaque_index ("bad " ^ name) (cb_of bad name) in
  if ig <> ib then fail "%s is entry %d of the good table and %d of the bad one" name ig ib;
  let tg = table good and tb = table bad in
  if size tg <> size tb then
    fail "the good table has %d entries and the bad one %d" (size tg) (size tb);
  let lg = opaque_labels good and lb = opaque_labels bad in
  if List.length lg <> size tg || List.length lb <> size tb then
    fail "the tables have %d entries, the libraries %d and %d opaque constants"
      (size tg) (List.length lg) (List.length lb);
  List.iter2
    (fun (i, a) (j, b) ->
      if i <> j || not (String.equal a b || String.starts_with ~prefix:"pad" b) then
        fail "entry %d of the good table is the proof of %s, entry %d of the bad one of %s" i a j b)
    lg lb;
  if compare (entry_term "good" tg ig) (entry_term "bad" tb ib) = 0 then
    fail "the two proofs of %s are the same" name;
  let header, _, contents = read_vo good in
  let opaques = segment bad "opaques" in
  let contents =
    Array.map (fun (n, data) -> if String.equal n "opaques" then (n, opaques) else (n, data)) contents
  in
  ignore (write_vo out header contents);
  say "spliced %s: the library of %s, the table of %s (%d proofs); %s is entry %d"
    out good bad (size tg) name ig

let handle good bad name out =
  let bad_cb = cb_of bad name in
  let ib = opaque_index ("bad " ^ name) bad_cb in
  let bad_body = field bad_cb 2 in
  rewrite_constant ~src:good ~dst:out name (fun cb ->
      let ig = opaque_index ("good " ^ name) cb in
      if ig <> ib then fail "%s is entry %d of the good table and %d of the bad one" name ig ib;
      if compare (field cb 2) bad_body = 0 then fail "the two handles of %s are the same" name;
      say "forging: %s's opaque handle (entry %d) taken from %s" name ig bad;
      set 2 bad_body cb)

let user good name nth from to_ out =
  let i = opaque_index name (cb_of good name) in
  rewrite_vo ~src:good ~dst:out
    [ ("opaques", fun tbl ->
          let t = entry_term name tbl i in
          let label p = kn_label (cst_user (field p 0)) in
          let target = ref None in
          ignore (map_constr (fun p ->
              if Option.is_none !target && String.equal (label p) to_ then
                target := Some (cst_user (field p 0));
              None) t);
          let to_kn = match !target with
            | Some kn -> kn
            | None -> fail "the proof of %s names no %s" name to_
          in
          let seen = ref 0 in
          let t' = map_constr (fun p ->
              if String.equal (label p) from then begin
                incr seen;
                if !seen = nth then
                  Some (block 0 [| dual to_kn (cst_user (field p 0)); field p 1 |])
                else None
              end
              else None) t
          in
          if nth < 1 || !seen < nth then
            fail "the proof of %s names %s %d times, and has no %s number %d" name from !seen from nth;
          say "forging: in the proof of %s (entry %d), %s number %d of %d has the user name %s"
            name i from nth !seen (kn_to_string to_kn);
          let tbl' = Obj.dup tbl in
          Obj.set_field tbl' i (upd 0 (upd 0 (set 0 t')) (field tbl i));
          tbl') ]

let flags src name donor out =
  let donor_flags = field (cb_of src donor) 8 in
  rewrite_constant ~src ~dst:out name (fun cb ->
      if compare (field cb 8) donor_flags = 0 then fail "%s already has the typing flags of %s" name donor;
      say "forging: %s gets the typing flags of %s" name donor;
      set 8 donor_flags cb)

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [ "splice"; good; bad; name; out ] -> splice good bad name out
  | [ "handle"; good; bad; name; out ] -> handle good bad name out
  | [ "user"; good; name; nth; from; to_; out ] -> user good name (int_of_string nth) from to_ out
  | [ "flags"; src; name; donor; out ] -> flags src name donor out
  | _ ->
    prerr_endline
      "usage: ocaml forge.ml splice GOOD.vo BAD.vo NAME OUT.vo\n\
      \       | handle GOOD.vo BAD.vo NAME OUT.vo | user GOOD.vo NAME N FROM TO OUT.vo\n\
      \       | flags SRC.vo NAME DONOR OUT.vo";
    exit 2
