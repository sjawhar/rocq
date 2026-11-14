(* Forge the .vo files of rocqchk_repeated_label.sh: give a label of a
   library's structure to a second field, which coqc never does
   (Safe_typing.add_field). The helpers, and the value layouts they rely
   on, are those of misc/rocqchk_forge_lib.ml; this file also relies on
   these, from checker/values.ml:

   - constant_body field 2: Undef is tag 0 [inline], an option, None
     being the integer 0;
   - module_body and module_type_body field 3: the delta resolver, whose
     field 0 is its root;
   - module path: MPdot is tag 2 [module path; label].

   Commands (each writes a new file; the input is left as it is):
     forge.ml param LIB.vo OUT.vo LABEL
       insert before the constant LABEL of the library a parameter with
       the same label and the same type;
     forge.ml rename LIB.vo OUT.vo FROM TO
       give the field FROM of the library the label TO. A module or a
       module type also gets the root of its delta resolver renamed, from
       the path that ends in FROM to the one that ends in TO;
     forge.ml client CLIENT.vo LIB.vo LIB_DIRPATH OUT.vo *)

#use "./misc/rocqchk_forge_lib.ml";;

let param label disk =
  let root = root_struc disk in
  let cb = constant_of root label in
  let undef = block 0 [| empty |] in
  let item = block 0 [| Obj.repr label; block 0 [| set 2 undef cb |] |] in
  let rec insert l =
    if Obj.is_int l then fail "no field %s" label
    else if String.equal (item_label (field l 0)) label then block 0 [| item; l |]
    else block 0 [| field l 0; insert (field l 1) |]
  in
  set_root_struc disk (insert root);
  say "forging: a parameter %s, with the type of the constant %s, inserted before it" label label;
  disk

let rename from_label to_label disk =
  let root = root_struc disk in
  let rename_root mb =
    let reso = field mb 3 in
    let mp = field reso 0 in
    if not (mp_is_dot from_label mp) then
      fail "the root of %s's delta resolver is %s" from_label (mp_to_string mp);
    let mp' = block 2 [| field mp 0; Obj.repr to_label |] in
    say "forging: the root of %s's delta resolver becomes %s" from_label (mp_to_string mp');
    set 3 (set 0 mp' reso) mb
  in
  let found = ref false in
  let rename_item item =
    if not (String.equal (item_label item) from_label) then item
    else begin
      if !found then fail "two fields %s" from_label;
      found := true;
      let sfb = item_field item in
      let sfb = if tag sfb = 3 || tag sfb = 4 then upd 0 rename_root sfb else sfb in
      block 0 [| Obj.repr to_label; sfb |]
    end
  in
  let root = map_list rename_item root in
  if not !found then fail "no field %s" from_label;
  set_root_struc disk root;
  say "forging: the field %s gets the label %s" from_label to_label;
  disk

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [ "param"; src; dst; label ] -> rewrite_vo ~src ~dst [ "library", param label ]
  | [ "rename"; src; dst; from_label; to_label ] ->
    rewrite_vo ~src ~dst [ "library", rename from_label to_label ]
  | [ "client"; src; lib; lib_dp; dst ] -> client ~src ~lib ~lib_dp ~dst
  | _ ->
    prerr_endline
      "usage: ocaml forge.ml param LIB.vo OUT.vo LABEL\n\
      \       | rename LIB.vo OUT.vo FROM TO\n\
      \       | client CLIENT.vo LIB.vo LIB_DIRPATH OUT.vo";
    exit 2
