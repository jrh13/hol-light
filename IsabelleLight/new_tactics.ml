(* ========================================================================= *)
(*                              Isabelle Light                               *)
(*   Isabelle/Procedural style additions and other user-friendly shortcuts.  *)
(*                                                                           *)
(*                   Petros Papapanagiotou, Jacques Fleuriot                 *)
(*              Center of Intelligent Systems and their Applications         *)
(*                          University of Edinburgh                          *)
(*                                 2009-2010                                 *)
(* ========================================================================= *)
(* FILE         : new_tactics.ml                                             *)
(* DESCRIPTION  : Various tactics to facilitate procedural-style users.      *)
(*                Mostly inspired by Isabelle's similar tactics.             *)
(* LAST MODIFIED: October 2012                                               *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* e_all : tactic -> goalstack                                               *) 
(* Same as "e" but applies tactic to ALL subgoals.                           *)
(* ------------------------------------------------------------------------- *)

let e_all tac =
  let c = (count_goals()) in
  let rec f i = ( 
    if (i = 0) 
    then (!current_goalstack) 
    else let _ = e tac in let _ = r 1 in f (i-1) 
   ) in f c;;


(* ------------------------------------------------------------------------- *)
(* ROTATE_N_TAC:                                                             *)
(* Rotates assumptions N times.                                              *)
(* ------------------------------------------------------------------------- *)
(* Pops the entire assumption list doing nothing (K ALL_TAC) then maps       *)
(* LABEL_TAC to the rotated list of assumptions. The list is reversed so as  *)
(* to match the external order. The result is applied to (asl,w) so as to    *)
(* obtain the resulting goalstate as required by the tactic type.            *)
(* ------------------------------------------------------------------------- *)

let (ROTATE_N_TAC :int->tactic) = 
  fun n (asl,w) ->
    let rotateasm = fun (asl) -> (tl asl)@[hd asl] in
    (POP_ASSUM_LIST(K ALL_TAC) THEN 
       MAP_EVERY (fun (s,th) -> LABEL_TAC s th) (funpow n rotateasm (rev asl))) 
      (asl,w);;


(* ------------------------------------------------------------------------- *)
(* ROTATE_TAC:                                                               *)
(* Rotates assumptions once.                                                 *)
(* ------------------------------------------------------------------------- *)

let (ROTATE_TAC :tactic) = (ROTATE_N_TAC 1);;



(* ------------------------------------------------------------------------- *)
(* DRULE_N_TAC:                                                              *)
(* Applies an inference rule to Nth assumption only.                         *)
(* Like drule for HOL Light's inference rules without matching.              *)
(* ------------------------------------------------------------------------- *)
(* Works like RULE_ASSUM_TAC except it numbers the assumption list with      *)
(* num_list and only applies the rule to the Nth assumption.                 *)
(* ------------------------------------------------------------------------- *)

let (DRULE_N_TAC :int->(thm->thm)->tactic) =
  fun n rule (asl,w) -> (POP_ASSUM_LIST(K ALL_TAC) THEN 
			   MAP_EVERY (fun (i,(s,th)) -> LABEL_TAC s (if (i=n) then (rule th) else th))
                           (num_list(rev asl))) (asl,w);;



(* ------------------------------------------------------------------------- *)
(* FRULE_N_TAC:                                                              *)
(* Applies an inference rule to Nth assumption only then adds the result as  *)
(* a new assumption.                                                         *)
(* Like frule for HOL Light's inference rules without matching.              *)
(* ------------------------------------------------------------------------- *)
(* Works like DRULE_N_TAC except it leaves the assumption intact and         *)
(* adds the result as a new assumption.                                      *)
(* ------------------------------------------------------------------------- *)

let (FRULE_N_TAC :int->(thm->thm)->tactic) =
  fun n rule (asl,w) -> (
    let asmlist = num_list(rev asl) in
    let (_,asm_n) = try assoc n asmlist with Failure _ ->
      failwith("FRULE_N_TAC: didn't find assumption "^string_of_int(n)) in
    ASSUME_TAC (rule asm_n)) (asl,w);;



(* ------------------------------------------------------------------------- *)
(* FRULE_MN_TAC:                                                       *)
(* Applies an inference rule (such as MP) to the Mth and Nth assumptions and *)
(* adds the result as a new assumption.                                      *)
(* ------------------------------------------------------------------------- *)
(* Numbers the assumption list, finds the Mth and Nth assumptions, applies   *)
(* the rule to them and adds the result as a new assumption.                 *)
(* ------------------------------------------------------------------------- *)

let (FRULE_MN_TAC :int->int->(thm->thm->thm)->tactic) =
fun  m n rule (asl,w) -> ( 
  let asmlist = num_list(rev asl) in
  let (_,asm_m) = try assoc m asmlist with Failure _ ->
    failwith("FRULE_MN_TAC: didn't find assumption "^string_of_int(m)) in
  let (_,asm_n) = try assoc n asmlist with Failure _ ->
    failwith("FRULE_MN_TAC: didn't find assumption "^string_of_int(n)) in
  ASSUME_TAC (rule asm_m asm_n)) (asl,w);;




(* ------------------------------------------------------------------------- *)
(* ----------------------- SIMP TACTICS START HERE!! ----------------------- *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* GENERAL_ASM_TAC: (thm list -> thm -> thm) -> thm list -> tactic           *)
(* General function that uses a rewrite rule to rewrite the assumptions.     *)
(* Each assumption is rewritten using the rest of the assumptions and the    *)
(* given list of theorems.                                                   *)
(* ------------------------------------------------------------------------- *)
(* A filter is applied to ensure that the assumption is not used to rewrite  *)
(* itself.                                                                   *)
(* ------------------------------------------------------------------------- *)

let GENERAL_ASM_TAC = fun rule thl (asl,w) ->
  let asm = map snd asl in
  (POP_ASSUM_LIST(K ALL_TAC) THEN 
     MAP_EVERY (fun (s,th) -> LABEL_TAC s 
	 (rule ((filter (fun x -> not (th = x)) asm) @ thl) th)
	       ) (rev asl)) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Using the above GENERAL_ASSUM_TAC, we define 4 tactics to rewrite         *)
(* assumptions based on the 4 rewrite rules available in HOL Light.          *)
(* ------------------------------------------------------------------------- *)

let REWRITE_ASM_TAC,ONCE_REWRITE_ASM_TAC,PURE_REWRITE_ASM_TAC,
  PURE_ONCE_REWRITE_ASM_TAC =
  GENERAL_ASM_TAC REWRITE_RULE,
  GENERAL_ASM_TAC ONCE_REWRITE_RULE,
  GENERAL_ASM_TAC PURE_REWRITE_RULE,
  GENERAL_ASM_TAC PURE_ONCE_REWRITE_RULE;;

(* ------------------------------------------------------------------------- *)
(* And for simplification.                                                   *)
(* ------------------------------------------------------------------------- *)

let SIMP_ASM_TAC,ONCE_SIMP_ASM_TAC,PURE_SIMP_ASM_TAC =  
  GENERAL_ASM_TAC SIMP_RULE,
  GENERAL_ASM_TAC ONCE_SIMP_RULE,
  GENERAL_ASM_TAC PURE_SIMP_RULE;;

(* ------------------------------------------------------------------------- *)
(* FULL_REWRITE_TAC : thm list -> tactic                                     *)
(* simp             : thm list -> tactic                                     *)
(* Similar to Isabelle's simp. Rewrites assumptions then rewrites goal       *)
(* using the assumptions.                                                    *)
(* ------------------------------------------------------------------------- *)

let FULL_REWRITE_TAC thl = 
  REWRITE_ASM_TAC thl THEN ASM_SIMP_TAC thl;;

let simp = FULL_REWRITE_TAC;;

(* ------------------------------------------------------------------------- *)
(* FULL_SIMP_TAC : thm list -> tactic                                        *)
(* Hybrid simplifier. Uses HOL Light's SIMP_TAC then FULL_REWRITE_TAC.       *)
(* ------------------------------------------------------------------------- *)

let FULL_SIMP_TAC thl = 
  SIMP_TAC thl THEN REWRITE_ASM_TAC thl THEN ASM_REWRITE_TAC thl;;



(* ------------------------------------------------------------------------- *)
(* assumption (tactic):                                                      *)
(* Shortcut to match an assumption to the goal as Isabelle's "assumption".   *)
(* ------------------------------------------------------------------------- *)

let assumption = FIRST_ASSUM MATCH_ACCEPT_TAC;;


(* ------------------------------------------------------------------------- *)
(* ALL_UNIFY_ACCEPT_TAC (term list -> thm -> tactic):                        *)
(* Altered UNIFY_ACCEPT_TAC. Uses INSTANTIATE_ALL instead of INSTANTIATE.    *)
(* ------------------------------------------------------------------------- *)
(* This allows for some valid instantiations that weren't otherwise allowed. *)
(* eg After using allE, the `a` metavariable can't be instantiated otherwise.*)
(* ------------------------------------------------------------------------- *)

let ALL_UNIFY_ACCEPT_TAC mvs th (asl,w) =
  let insts = term_unify mvs (concl th) w in
  ([],insts),[],
  let th' = INSTANTIATE_ALL insts th in
  fun i [] -> INSTANTIATE_ALL i th';;



(* ------------------------------------------------------------------------- *)
(* meta_assumption (term list -> tactic):                                    *)
(* Shortcut to match an assumption to the goal as Isabelle's "assumption".   *)
(* This version also tries unification by instantiation of meta-variables    *)
(* which, unfortunately, need to be given manually in a list.                *)
(* ------------------------------------------------------------------------- *)
(* Invalid instantiations may be produced.                                   *)
(* eg g `!x:num. (?a:num. R a x) ==> (?y. R y x)`;;                          *)
(*    e GEN_TAC;;                                                            *)
(*    e (rule impI);;                                                        *)
(*    e (rule exI);;                                                         *)
(*    e (FIRST_X_ASSUM (X_CHOOSE_TAC `b:num`));;                             *)
(*    e (meta_assumption [`a:num`]);;                                        *)
(* This succeeds but top_thm() is unable to reconstruct the theorem.         *)
(* ------------------------------------------------------------------------- *)

let meta_assumption mvs = (FIRST_ASSUM MATCH_ACCEPT_TAC) ORELSE 
                      (FIRST_ASSUM (ALL_UNIFY_ACCEPT_TAC mvs));;


(* ------------------------------------------------------------------------- *)
(* Shortcut for interactive proofs so that you don't have to enumerate       *)
(* metavariables.                                                            *)
(* ------------------------------------------------------------------------- *)

let ema () = (e o meta_assumption o top_metas o p) ()  ;;


(* ------------------------------------------------------------------------- *)
(* X_MATCH_CHOOSE_TAC : (term -> tactic)                                     *)
(* Version of X_CHOOSE_TAC with type matching.                               *)
(* ------------------------------------------------------------------------- *)
(* If the variable given as an argument has a vartype then its type is       *)
(* instantiated to the type of the existentially quantified variable.        *)
(* Usefull so that the user need not specify the type for his variable.      *)
(* It is still acceptable if the user does specify it.                       *)
(* ------------------------------------------------------------------------- *)

let (X_MATCH_CHOOSE_TAC: term -> thm_tactic) =
  fun x' xth ->
    try let xtm = concl xth in
        let x,bod = dest_exists xtm in
	let x'type = type_of x' in
	let x'' = if (is_vartype x'type) then
	  inst (type_match x'type (type_of x) []) x'
	else x' in
        let pat = vsubst[x'',x] bod in
        let xth' = ASSUME pat in
        fun (asl,w) ->
          let avoids = itlist (union o frees o concl o snd) asl
                              (union (frees w) (thm_frees xth)) in
          if mem x' avoids then failwith "X_CHOOSE_TAC" else
          null_meta,[("",xth')::asl,w],
          fun i [th] -> CHOOSE(x'',INSTANTIATE_ALL i xth) th
    with Failure _ -> failwith "X_CHOOSE_TAC";;




(* ------------------------------------------------------------------------- *)
(* exE : (term -> tactic)                                                    *)
(* Existential elimination tactic (since we are unable to accommodate        *)
(* erule exE with the current meta_rule system because of lack of meta-level *)
(* quantification).                                                          *)
(* ------------------------------------------------------------------------- *)

let exE = FIRST_X_ASSUM o X_MATCH_CHOOSE_TAC;;


(* ------------------------------------------------------------------------- *)
(* allI : (term -> tactic)                                                   *)
(* Universal introduction tactic (since we are unable to accommodate         *)
(* rule allI with the current meta_rule system because of lack of meta-level *)
(* quantification).                                                          *)
(* ------------------------------------------------------------------------- *)
(* (+) We can use X_GEN_TAC to allow the user to give his own term, but      *)
(* this is rarely useful in procedural style proofs.                         *)
(* ------------------------------------------------------------------------- *)

let allI = GEN_TAC;;


(* ------------------------------------------------------------------------- *)
(* qed : (unit -> thm)                                                       *)
(* Reconstructs the theorem at the end of an interactive proof.              *)
(* May fail if an incorrect metavariable instantiation has occured during the*)
(* proof.                                                                    *)
(* ------------------------------------------------------------------------- *)
(* (+) There are plans to upgrade this for better accommodation of proofs    *)
(* containing meta-level implication (see meta_rules.ml and gmm).            *)
(* ------------------------------------------------------------------------- *)

let qed = top_thm;;


(* ------------------------------------------------------------------------- *)
(* ASM_STRUCT_CASES_TAC : (thm_tactic)                                       *)
(* Replacement/fix of STRUCT_CASES_TAC where each case is added as an        *)
(* assumption like ASM_CASES_TAC does for booleans.                          *)
(* ------------------------------------------------------------------------- *)

let ASM_STRUCT_CASES_TAC =
    REPEAT_TCL STRIP_THM_THEN ASSUME_TAC;;

(* ------------------------------------------------------------------------- *)
(* case_tac : (term -> tactic)                                               *)
(* Isabelle's case_tac for splitting cases.                                  *)
(* ------------------------------------------------------------------------- *)

let (case_tac:term->tactic) =
  fun tm ((_,w) as g) ->
    let trymatch = fun tm1 tm2 ->
      try ( let inst = term_match (gl_frees g) tm1 tm2 in
	    if (is_var tm1) 
	    then match inst with
		[],[],_ -> true
	      | _  -> false
	    else true )
      with Failure _ -> false in		
    let tm' = try (find_term (trymatch tm) w)
      with Failure _ -> tm in
    let ty = (fst o dest_type o type_of) tm' in
    let thm = try (cases ty) 
      with Failure _ -> failwith ("case_tac: Failed to find cases theorem for type \"" ^ ty ^ "\".") in
    ASM_STRUCT_CASES_TAC (ISPEC tm' thm) g;;


(* ------------------------------------------------------------------------- *)
(* gen_case_tac : tactic                                                     *)
(* Case split on the leading universal quantifier of the goal.               *)
(* ------------------------------------------------------------------------- *)

let (gen_case_tac:tactic) =
  fun ((_,w) as g) ->
    case_tac ((fst o dest_forall) w) g;;


(* ------------------------------------------------------------------------- *)
(* subgoal_tac : (term -> tactic)                                            *)
(* Introduces a new subgoal which gets added as an assumption.               *)
(* Isabelle's subgoal_tac.                                                   *)
(* ------------------------------------------------------------------------- *)

let subgoal_tac = fun tm -> SUBGOAL_THEN tm ASSUME_TAC;;


(* ------------------------------------------------------------------------- *)
(* meson : (thm list -> tactic)                                              *)
(* Lower-case shortcut for ASM_MESON_TAC                                     *)
(* ------------------------------------------------------------------------- *)

let meson = ASM_MESON_TAC;;

