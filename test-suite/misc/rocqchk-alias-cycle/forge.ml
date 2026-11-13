(* Give Cycle.vo the alias cycles coqc refuses to write: the expression of
   each module below, an alias of Defines or of Outer in the honest file,
   becomes an alias of the path beside it.
     Self -> Self,  Ping -> Pong,  Pong -> Ping,  Up -> Down,  Down -> Up.C
   The file is rewritten in place. The helpers, and the value layouts they
   rely on, are those of misc/rocqchk_forge_lib.ml. This file adds
   checker/values.ml's layouts of what an Algebraic implementation holds,
   [expression], of an expression MENoFunctor (tag 0) [algebraic
   expression], of an algebraic expression MEident (tag 0) [module path],
   and of a module path MPfile (tag 0) [dirpath] | MPbound (tag 1) | MPdot
   (tag 2) [module path; label]. Each block is checked to have the expected
   shape before it is used.

   Command:
     forge.ml CYCLE.vo *)

#use "./misc/rocqchk_forge_lib.ml";;

(* The path that the module_body [mb] is an alias of: its field 0 is the
   implementation wrapper (tag 0) [implementation], the implementation is
   Algebraic [expression], the expression MENoFunctor [algebraic
   expression], and that MEident [module path]. *)
let alias_target what mb =
  let wrapper = field mb 0 in
  expect ~size:1 (what ^ "'s implementation wrapper") 0 wrapper;
  let impl = field wrapper 0 in
  expect ~size:1 (what ^ "'s implementation (Algebraic)") 0 impl;
  let me = field impl 0 in
  expect ~size:1 (what ^ "'s expression (MENoFunctor)") 0 me;
  let alg = field me 0 in
  expect ~size:1 (what ^ "'s expression (MEident)") 0 alg;
  field alg 0

(* The implementation wrapper of an alias of [target]. *)
let alias_of target = block 0 [| block 0 [| block 0 [| block 0 [| target |] |] |] |]

let dot mp label = block 2 [| mp; Obj.repr label |]

let forge disk =
  let root = root_struc disk in
  let defines = alias_target "Self" (module_of root "Self") in
  expect ~size:2 "Defines' path (MPdot)" 2 defines;
  let file = field defines 0 in
  expect ~size:1 "the library's path (MPfile)" 0 file;
  let root =
    List.fold_left
      (fun root (name, target) ->
        ignore (alias_target name (module_of root name));
        (* Only the blocks above the new field 0 are copied: the module_body,
           its SFBmodule block and item, the list cells before it, and
           (set_root_struc) the root's signature and module_body. The rest
           is shared as it is. *)
        let root = struc_update root name (upd 0 (set 0 (alias_of target))) in
        say "forge: %s is now an alias" name;
        root)
      root
      [ "Self", dot file "Self";
        "Ping", dot file "Pong";
        "Pong", dot file "Ping";
        "Up", dot file "Down";
        "Down", dot (dot file "Up") "C" ]
  in
  set_root_struc disk root;
  disk

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [ file ] -> rewrite_vo ~src:file ~dst:file [ "library", forge ]
  | _ ->
    prerr_endline "usage: forge.ml CYCLE.vo";
    exit 2
