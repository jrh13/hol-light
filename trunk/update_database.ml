(* ========================================================================= *)
(* Create search database from OCaml / modify search database dynamically.   *)
(*                                                                           *)
(* This file assigns to "theorems", which is a list of name-theorem pairs.   *)
(* The core system already has such a database set up. Use this file if you  *)
(* want to update the database beyond the core, so you can search it.        *)
(*                                                                           *)
(* The trickery to get at the OCaml environment is due to oleg@pobox.com     *)
(* (see his message to the caml-list on Tuesday 26th September 2006).        *)
(* ========================================================================= *)

(* !!!!!!! You must set this to point at the source directory in
   !!!!!!! which OCaml was built. (And don't do "make clean" beforehand.)
 *)

let ocaml_source_dir =
  Filename.concat (Sys.getenv "HOME")
  ("software/ocaml-"^Sys.ocaml_version);;

do_list (fun s -> Topdirs.dir_directory(Filename.concat ocaml_source_dir s))
        ["parsing"; "typing"; "toplevel"; "utils"];;

(* This must be loaded first! It is stateful, and affects Predef *)
#load "ident.cmo";;

#load "misc.cmo";;
#load "path.cmo";;
#load "types.cmo";;
#load "btype.cmo";;
#load "tbl.cmo";;
#load "subst.cmo";;
#load "predef.cmo";;
#load "datarepr.cmo";;
#load "config.cmo";;
#load "consistbl.cmo";;
#load "clflags.cmo";;
#load "env.cmo";;
#load "ctype.cmo";;
#load "printast.cmo";;
#load "oprint.cmo";;
#load "primitive.cmo";;
#load "printtyp.cmo";;

(* ------------------------------------------------------------------------- *)
(* Get the toplevel environment as raw data.                                 *)
(* ------------------------------------------------------------------------- *)

let get_value_bindings env =
   let rec get_val acc = function
        | Env.Env_empty -> acc
        | Env.Env_value (next, ident, val_descr) ->
                get_val ((ident,val_descr)::acc) next
        | Env.Env_type (next,_,_) -> get_val acc next
        | Env.Env_exception (next,_,_) -> get_val acc next
        | Env.Env_module (next,_,_) -> get_val acc next
        | Env.Env_modtype (next,_,_) -> get_val acc next
        | Env.Env_class (next,_,_) -> get_val acc next
        | Env.Env_cltype (next,_,_) -> get_val acc next
        | Env.Env_open (next,_) -> get_val acc next
  in get_val [] (Env.summary env);;

(* ------------------------------------------------------------------------- *)
(* Convert a type to a string, for ease of comparison.                       *)
(* ------------------------------------------------------------------------- *)

let type_to_str (x : Types.type_expr) =
  Printtyp.type_expr Format.str_formatter x;
         Format.flush_str_formatter ();;

(* ------------------------------------------------------------------------- *)
(* Put an assignment of a theorem database in the named file.                *)
(* ------------------------------------------------------------------------- *)

let make_database_assignment filename =
  let all_bnds = get_value_bindings (!Toploop.toplevel_env) in
  let thm_bnds = filter (fun (ident,val_descr) ->
                          type_to_str val_descr.Types.val_type = "thm")
                        all_bnds in
  let names =
    subtract (map (fun (ident,val_descr) -> Ident.name ident) thm_bnds)
             ["it"] in
  let entries = map (fun n -> "\""^n^"\","^n) (uniq(sort (<) names)) in
  let text = "theorems :=\n[\n"^
             end_itlist (fun a b -> a^";\n"^b) entries^"\n];;\n" in
  file_of_string filename text;;

(* ------------------------------------------------------------------------- *)
(* Remove bindings in first list from second assoc list (all ordered).       *)
(* ------------------------------------------------------------------------- *)

let rec demerge s l =
  match (s,l) with
    u::t,(x,y as p)::m ->
        if u = x then demerge t m
        else if u < x then demerge t l
        else p::(demerge s m)
  | _ -> l;;

(* ------------------------------------------------------------------------- *)
(* Incrementally update database.                                            *)
(* ------------------------------------------------------------------------- *)

let update_database =
  let value_bindings_checked = ref 0
  and theorem_bindings_existing = ref undefined in
  let listify l = if l = [] then "[]"
                  else "[\n"^end_itlist (fun a b -> a^";\n"^b) l^"\n]\n" in
  let purenames = map (fun n -> "\""^n^"\"")
  and pairnames = map (fun n -> "\""^n^"\","^n) in
  fun () ->
    let old_count = !value_bindings_checked
    and old_ths = !theorem_bindings_existing in
    let all_bnds = get_value_bindings (!Toploop.toplevel_env) in
    let new_bnds = funpow old_count tl all_bnds in
    let new_count = old_count + length new_bnds
    and new_ths =
      rev_itlist (fun (ident,val_descr) ->
        let n = Ident.name ident in
        if type_to_str val_descr.Types.val_type = "thm" & n <> "it"
        then (n |-> ()) else undefine n) new_bnds old_ths in
    value_bindings_checked := new_count;
    if new_ths = old_ths then () else
    (print_string "Updating search database\n";
     theorem_bindings_existing := new_ths;
     let all_ths = combine (fun _ _ -> ()) (fun _ -> false) old_ths new_ths in
     let del_ths = combine (fun _ _ -> ()) (fun _ -> true) all_ths new_ths
     and add_ths = combine (fun _ _ -> ()) (fun _ -> true) all_ths old_ths in
     let del_names = mergesort (<) (foldr (fun a _ l -> a::l) del_ths [])
     and add_names = mergesort (<) (foldr (fun a _ l -> a::l) add_ths []) in
     let exptext =
      "theorems :=\n merge (increasing fst) (demerge "^
      (listify(purenames del_names))^
      " (!theorems)) "^
      (listify(pairnames add_names))^
      ";;\n" in
     (let filename = Filename.temp_file "database" ".ml" in
      file_of_string filename exptext;
      loadt filename;
      Sys.remove filename));;

(* ------------------------------------------------------------------------- *)
(* Include a call to this on each search.                                    *)
(* ------------------------------------------------------------------------- *)

let search =
  let rec immediatesublist l1 l2 =
    match (l1,l2) with
      [],_ -> true
    | _,[] -> false
    | (h1::t1,h2::t2) -> h1 = h2 & immediatesublist t1 t2 in
  let rec sublist l1 l2 =
    match (l1,l2) with
      [],_ -> true
    | _,[] -> false
    | (h1::t1,h2::t2) -> immediatesublist l1 l2 or sublist l1 t2 in
  let exists_subterm_satisfying p (n,th) = can (find_term p) (concl th)
  and name_contains s (n,th) = sublist (explode s) (explode n) in
  let rec filterpred tm =
    match tm with
      Comb(Var("<omit this pattern>",_),t) -> not o filterpred t
    | Comb(Var("<match theorem name>",_),Var(pat,_)) -> name_contains pat
    | Comb(Var("<match aconv>",_),pat) -> exists_subterm_satisfying (aconv pat)
    | pat -> exists_subterm_satisfying (can (term_match [] pat)) in
  fun pats -> 
    update_database();
    let triv,nontriv = partition is_var pats in
    (if triv <> [] then
      warn true
         ("Ignoring plain variables in search: "^
          end_itlist (fun s t -> s^", "^t) (map (fst o dest_var) triv))
     else ());
    (if nontriv = [] & triv <> [] then []
     else itlist (filter o filterpred) pats (!theorems));;

(* ------------------------------------------------------------------------- *)
(* Update to bring things back to current state.                             *)
(* ------------------------------------------------------------------------- *)

theorems := [];;

update_database();;
