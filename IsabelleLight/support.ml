(* ========================================================================= *)
(*                              Isabelle Light                               *)
(*   Isabelle/Procedural style additions and other user-friendly shortcuts.  *)
(*                                                                           *)
(*                   Petros Papapanagiotou, Jacques Fleuriot                 *)
(*              Center of Intelligent Systems and their Applications         *)
(*                          University of Edinburgh                          *)
(*                                 2009-2012                                 *)
(* ========================================================================= *)
(* FILE         : support.ml                                                 *)
(* DESCRIPTION  : Support functions and various shortcuts.                   *)
(* LAST MODIFIED: October 2012                                               *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Functions to deal with triplets:                                          *)
(* ------------------------------------------------------------------------- *)

let fst3 (x,_,_) = x;;
let snd3 (_,x,_) = x;;
let thd3 (_,_,x) = x;;


(*----------------------------------------------------------------------------*)
(* num_list : a' list -> (a' * int) list                                      *)
(*                                                                            *)
(* Numbers a list of elements,                                                *)
(* e.g. [`a`;`b`;`c`] ---> [(0,`a`);(1,`b`);(2,`c`)].                         *)
(*----------------------------------------------------------------------------*)

let num_list l =
   let rec number_list' n l =
      if ( l = [] ) then []
      else (n,hd l)::(number_list' (n + 1) (tl l))
   in number_list' 0 l;;


(* ------------------------------------------------------------------------- *)
(* list_match_first: (a' -> b') -> a' list -> b'                             *)
(* Tries to apply a function to the members of a list. Returns the result    *)
(* from the first member that succeeds.                                      *)
(* ------------------------------------------------------------------------- *)

let rec list_match_first f alist =
  if (alist = []) then failwith "list_match_first: No matches!"
  else try f (hd alist) with Failure _ -> list_match_first f (tl alist);;


(* ------------------------------------------------------------------------- *)
(* terms_match: term list -> term -> term list -> instantiation              *)
(* Tries to apply term_match to the first possible term in a list.           *)
(* Returns the insantiation.                                                 *)
(* ------------------------------------------------------------------------- *)

let (terms_match: term list -> term -> term list -> instantiation ) =
  fun consts key tlist ->
    try (list_match_first (term_match consts key) tlist)
    with Failure _ -> failwith "terms_match: No terms match!";;


(* ------------------------------------------------------------------------- *)
(* thm_mk_primed_vars: term list -> thm -> thm                               *)
(* Renames all free variables in a theorem to avoid specified and constant   *)
(* names.                                                                    *)
(* ------------------------------------------------------------------------- *)

let thm_mk_primed_vars avoids thm =
  let fvars = thm_frees thm in
  let new_vars = map (mk_primed_var avoids) fvars in
  let insts = List.combine new_vars fvars in
  INST insts thm;;


(* ------------------------------------------------------------------------- *)
(* gl_frees: goal -> term list                                               *)
(* Finds the free variables in a subgoal (assumptions and goal).             *)
(* ------------------------------------------------------------------------- *)

let gl_frees : goal -> term list =
  fun (asl,w) -> itlist (union o thm_frees o snd) asl (frees w);;


(* ------------------------------------------------------------------------- *)
(* ADD_HYP: thm -> thm -> thm                                                *)
(* Trivially adds the hypotheses of a theorem to the premises of another.    *)
(* ------------------------------------------------------------------------- *)
(* (+) Used in the justification of erule and drule to add the eliminated    *)
(* assumption to the proven subgoals.                                        *)
(* (+) Could have been based on ADD_ASSUM but it's more convenient this way. *)
(* ------------------------------------------------------------------------- *)

let ADD_HYP hyp_thm thm = CONJUNCT2 (CONJ hyp_thm thm);;


(* ------------------------------------------------------------------------- *)
(* DISCHL: term list -> thm -> thm                                           *)
(* Applies DISCH for several terms.                                          *)
(* ------------------------------------------------------------------------- *)

let rec (DISCHL: term list -> thm -> thm) =
  fun tms thm ->
    if (tms = []) then thm
        else DISCH (hd tms) (DISCHL (tl tms) thm);;


(* ------------------------------------------------------------------------- *)
(* print_thl:                                                                *)
(* Print a list of theorems (for debugging).                                 *)
(* ------------------------------------------------------------------------- *)

let print_thl thl =
  map (fun thm -> ( print_thm thm ; print_newline ())) thl;;


(* ------------------------------------------------------------------------- *)
(* print_tml:                                                                *)
(* Print a list of terms (for debugging).                                    *)
(* ------------------------------------------------------------------------- *)

let print_tml tml =
    map (fun tm -> ( print_term tm ; print_newline ())) tml;;


(* ------------------------------------------------------------------------- *)
(* print_varandtype, show_types, hide_types:                                 *)
(* Prints the type after each variable.  Useful for "debugging" type issues. *)
(* ------------------------------------------------------------------------- *)
(* Source:                                                                   *)
(* http://code.google.com/p/flyspeck/wiki/TipsAndTricks#Investigating_Types  *)
(* ------------------------------------------------------------------------- *)

let print_varandtype fmt tm =
  let hop,args = strip_comb tm in
  let s = name_of hop
  and ty = type_of hop in
  if is_var hop && args = [] then
   (pp_print_string fmt "(";
    pp_print_string fmt s;
    pp_print_string fmt ":";
    pp_print_type fmt ty;
    pp_print_string fmt ")")
  else fail() ;;

let show_types,hide_types =
  (fun () -> install_user_printer ("Show Types",print_varandtype)),
  (fun () -> try delete_user_printer "Show Types"
             with Failure _ -> failwith ("hide_types: "^
                                         "Types are already hidden."));;


(* ------------------------------------------------------------------------- *)
(* count_goals : unit -> int                                                 *)
(* Shortcut to count the subgoals in the current goalstate.                  *)
(* ------------------------------------------------------------------------- *)

let count_goals () =
  if (!current_goalstack = []) then 0 else
  ( let _,gls,_ = hd !current_goalstack in length gls );;



(* ------------------------------------------------------------------------- *)
(* top_asms : goalstack -> (string * thm) list                               *)
(* Shortcut to get the assumption list of the top goal of a given goalstack. *)
(* ------------------------------------------------------------------------- *)

let top_asms (gs:goalstack) = (fst o hd o snd3 o hd) gs;;


(* ------------------------------------------------------------------------- *)
(* top_metas : goalstack -> term list                                        *)
(* Returns the list of metavariables in the current goalstate.               *)
(* ------------------------------------------------------------------------- *)

let top_metas (gs:goalstack) = (fst o fst3 o hd) gs;;


(* ------------------------------------------------------------------------- *)
(* top_inst : goalstack -> instantiation                                     *)
(* Returns the metavariable instantiations in the current goalstate.         *)
(* ------------------------------------------------------------------------- *)

let top_inst (gs:goalstack) = (snd o fst3 o hd) gs;;


(* ------------------------------------------------------------------------- *)
(* print_goalstack_all :                                                     *)
(* Alternative goalstack printer that always prints all subgoals.            *)
(* Also prints list of metavariables with their types.                       *)
(* ------------------------------------------------------------------------- *)
(* Original printer only prints more than one subgoals iff they were         *)
(* generated by the last step. Otherwise it only prints the 'active' subgoal.*)
(* Replace by #install_printer print_goalstack_all;;                         *)
(* Revert to original by #install_printer print_goalstack;;                  *)
(* ------------------------------------------------------------------------- *)

let (print_goalstack_all:goalstack->unit) =
  let print_goalstate k gs =
    let ((mvs,_),gl,_) = gs in
    let n = length gl in
    let s = if n = 0 then "No subgoals" else
              (string_of_int k)^" subgoal"^(if k > 1 then "s" else "")
           ^" ("^(string_of_int n)^" total)" in
    let print_mv v = print_string " `" ;
                     print_varandtype std_formatter v ;
                     print_string "`;" in
    print_string s; print_newline();
    if (length mvs > 0) then (
      print_string "Metas:" ; let _ = map print_mv mvs in () ; print_newline()
    ) ;
    if gl = [] then () else
    do_list (print_goal o C el gl) (rev(0--(k-1))) in
  fun l ->
    if l = [] then print_string "Empty goalstack"
    else
      let (_,gl,_ as gs) = hd l in
      print_goalstate (length gl) gs;;


(* ------------------------------------------------------------------------- *)
(* print_goalstack :                                                         *)
(* Upgrade to print_goalstack that also prints a list of metavariables with  *)
(* their types.                                                              *)
(* ------------------------------------------------------------------------- *)

let (print_goalstack:goalstack->unit) =
  let print_goalstate k gs =
    let ((mvs,_),gl,_) = gs in
    let n = length gl in
    let s = if n = 0 then "No subgoals" else
              (string_of_int k)^" subgoal"^(if k > 1 then "s" else "")
           ^" ("^(string_of_int n)^" total)" in
    let print_mv v = print_string " `" ;
                     print_varandtype std_formatter v ;
                     print_string "`;" in
    print_string s; print_newline();
    if (length mvs > 0) then (
      print_string "Metas:" ; let _ = map print_mv mvs in () ; print_newline()
    ) ;
    if gl = [] then () else
    do_list (print_goal o C el gl) (rev(0--(k-1))) in
  fun l ->
    if l = [] then print_string "Empty goalstack"
    else if tl l = [] then
      let (_,gl,_ as gs) = hd l in
      print_goalstate 1 gs
    else
      let (_,gl,_ as gs) = hd l
      and (_,gl0,_) = hd(tl l) in
      let p = length gl - length gl0 in
      let p' = if p < 1 then 1 else p + 1 in
      print_goalstate p' gs;;

#install_printer print_goalstack;;



