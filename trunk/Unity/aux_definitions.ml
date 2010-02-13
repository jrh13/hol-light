(*
  File:        aux_definitions.ml

  Description: This file defines a few useful functions

  Author:       (c) Copyright 1989-2008 by Flemming Andersen
  Date:         October 23, 1989
  Last Update:  December 30, 2007
*)

let prove_thm ((thm_name:string), thm_term, thm_tactic) =
    prove (thm_term, thm_tactic);;

(* Uniform error facility *)
let UNITY_ERR (func,mesg) = ( failwith func, Failure mesg );;

(*----------------------------------------------------------------------*)
(* Auxilliary definitions                                               *)
(*----------------------------------------------------------------------*)

let UNDISCH_ALL_TAC =
    let th_tac (th:thm) (tac:tactic) = (MP_TAC th) THEN tac  in
    let u_asml (thml:thm list) = itlist  th_tac thml ALL_TAC in
        POP_ASSUM_LIST u_asml
    ;;

let UNDISCH_ONE_TAC =
    let th_tac (th:thm) (tac:tactic) = (UNDISCH_TAC (concl th)) THEN tac in
    let u_asm  (th:thm) = itlist  th_tac [th] ALL_TAC in
        FIRST_ASSUM u_asm
    ;;

let LIST_INDUCT = list_INDUCT;;

let CONTRAPOS =
  let a = `a:bool` and b = `b:bool` in
  let pth = ITAUT `(a ==> b) ==> (~b ==> ~a)` in
  fun th ->
    try let P,Q = dest_imp(concl th) in
        MP (INST [P,a; Q,b] pth) th
    with Failure _ -> failwith "CONTRAPOS";;


let OP_FIX = 200;;

let new_infix_definition (define_name, name_org, define_term, fixity) =
(
  let defined_thm            = new_definition define_term           in
  let (infix_num, assoc_str) = get_infix_status name_org            in
  let defined_infix          =
   ( parse_as_infix ( define_name, (infix_num + fixity, assoc_str) ) ) in
    (fst (defined_thm, defined_infix))
);;

(*
get_infix_status
infixes();;

get_prefix_status

prefixes();;

*)

let new_binder_definition def_term def_binder =
(
  let def_thm  = ( new_definition  def_term )   in
  let def_bind = ( parse_as_binder def_binder ) in
    (fst (def_thm, def_bind))
);;
