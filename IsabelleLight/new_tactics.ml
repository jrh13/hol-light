(* ========================================================================= *)
(*                              Isabelle Light                               *)
(*   Isabelle/Procedural style additions and other user-friendly shortcuts.  *)
(*                                                                           *)
(*                   Petros Papapanagiotou, Jacques Fleuriot                 *)
(*              Center of Intelligent Systems and their Applications         *)
(*                          University of Edinburgh                          *)
(*                                 2009-2015                                 *)
(* ========================================================================= *)
(* FILE         : new_tactics.ml                                             *)
(* DESCRIPTION  : Various tactics to facilitate procedural-style users.      *)
(*                Mostly inspired by Isabelle's similar tactics.             *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Small shortcut that I use quite often.                                    *)
(* ------------------------------------------------------------------------- *)

let GEN_ALL_TAC = REPEAT GEN_TAC;;


(* ------------------------------------------------------------------------- *)
(* ----------------------- SIMP TACTICS START HERE!! ----------------------- *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* GENERAL_ASM_TAC: (thm list -> thm -> thm) -> thm list -> tactic           *)
(* General function that uses a rewrite rule to rewrite the assumptions.     *)
(* Each assumption is rewritten using the rest of the assumptions and the    *)
(* given list of theorems.                                                   *)
(* ------------------------------------------------------------------------- *)

let (GENERAL_ASM_TAC:(thm list -> thm -> thm) -> thm list -> tactic) =
  let map_asms l = (* Pairs each assumption with all the rest. *)
    let chop_map ls n =
      let l,r = chop_list n ls in
      last l,map snd (butlast l @ r) in
    map (chop_map l) (1--(length l)) in

  fun rule thl ->
  let apply_rule ((s,th),asm) = LABEL_TAC s (rule (asm @ thl) th) in

  fun asl,w ->
  (POP_ASSUM_LIST(K ALL_TAC) THEN
     MAP_EVERY apply_rule (map_asms (rev asl))) (asl,w);; (* rev ensures correct order *)

(* ------------------------------------------------------------------------- *)
(* Using the above GENERAL_ASSUM_TAC, we define 4 tactics to rewrite         *)
(* assumptions based on the 4 rewriting rules available in HOL Light.        *)
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
(*    e (GEN_TAC THEN DISCH_TAC);;                                           *)
(*    e (X_META_EXISTS_TAC `c:num`);;                                        *)
(*    e (FIRST_X_ASSUM (X_CHOOSE_TAC `b:num`));;                             *)
(*    e (meta_assumption [`c:num`]);;                                        *)
(* This succeeds but top_thm() is unable to reconstruct the theorem.         *)
(* b is not free in the goal when X_CHOOSE_TAC is applied but it is during   *)
(* justification because the free c has been instantiated to b.              *)
(* ------------------------------------------------------------------------- *)

let meta_assumption mvs = (FIRST_ASSUM MATCH_ACCEPT_TAC) ORELSE
                      (FIRST_ASSUM (ALL_UNIFY_ACCEPT_TAC mvs));;


(* ------------------------------------------------------------------------- *)
(* Shortcut for interactive proofs so that you don't have to enumerate       *)
(* metavariables.                                                            *)
(* ------------------------------------------------------------------------- *)

let ema () = (e o meta_assumption o top_metas o p) ()  ;;


(* ------------------------------------------------------------------------- *)
(* X_MATCH_GEN_TAC : (term -> tactic)                                        *)
(* X_MATCH_CHOOSE_TAC : (term -> thm_tactic)                                 *)
(* MATCH_EXISTS_TAC : (term -> tactic)                                       *)
(* Versions of X_GEN_TAC, X_CHOOSE_TAC, and EXISTS_TAC with type matching.   *)
(* ------------------------------------------------------------------------- *)
(* If the variable given as an argument has a vartype then its type is       *)
(* instantiated to the type of the existentially quantified variable.        *)
(* Usefull so that the user need not specify the type for the given variable.*)
(* It is still acceptable if the user does specify it.                       *)
(* ------------------------------------------------------------------------- *)


let (X_MATCH_GEN_TAC: term -> tactic),
  (X_MATCH_CHOOSE_TAC: term -> thm_tactic),
  (MATCH_EXISTS_TAC: term -> tactic) =
  let tactic_type_compatibility_check pfx e g =
    let et = type_of e in
    let g' = try_type et g in
    let gt = type_of g' in
    if et = gt then g'
    else failwith(pfx ^ ": expected type :"^string_of_type et^" but got :"^
                    string_of_type gt) in
  let X_MATCH_GEN_TAC x' =
    if not(is_var x') then failwith "X_GEN_TAC: not a variable" else
      fun (asl,w) ->
        let x,bod = try dest_forall w
          with Failure _ -> failwith "X_GEN_TAC: Not universally quantified" in
        let x'' = tactic_type_compatibility_check "X_GEN_TAC" x x' in
        let avoids = itlist (union o thm_frees o snd) asl (frees w) in
        if mem x'' avoids then failwith "X_GEN_TAC: invalid variable" else
          let afn = CONV_RULE(GEN_ALPHA_CONV x) in
          null_meta,[asl,vsubst[x'',x] bod],
          fun i [th] -> afn (GEN x'' th)
  and X_MATCH_CHOOSE_TAC x' xth =
    let xtm = concl xth in
    let x,bod = try dest_exists xtm
      with Failure _ -> failwith "X_CHOOSE_TAC: not existential" in
    let x'' = tactic_type_compatibility_check "X_CHOOSE_TAC" x x' in
    let pat = vsubst[x'',x] bod in
    let xth' = ASSUME pat in
    fun (asl,w) ->
      let avoids = itlist (union o frees o concl o snd) asl
        (union (frees w) (thm_frees xth)) in
      if mem x'' avoids then failwith "X_CHOOSE_TAC: invalid variable" else
        null_meta,[("",xth')::asl,w],
        fun i [th] -> CHOOSE(x'',INSTANTIATE_ALL i xth) th
  and MATCH_EXISTS_TAC t (asl,w) =
    let v,bod = try dest_exists w with Failure _ ->
      failwith "EXISTS_TAC: Goal not existentially quantified" in
    let t' = tactic_type_compatibility_check "EXISTS_TAC" v t in
    null_meta,[asl,vsubst[t',v] bod],
    fun i [th] -> EXISTS (instantiate i w,instantiate i t') th in
  X_MATCH_GEN_TAC,X_MATCH_CHOOSE_TAC,MATCH_EXISTS_TAC;;


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
(* (+) We can use X_GEN_TAC to allow the user to give their own term, but    *)
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
(* John Harrison adapted the HOL Light version as well now so this is        *)
(* redundant, but left here for historical reasons.                          *)
(* ------------------------------------------------------------------------- *)

let ASM_STRUCT_CASES_TAC =
    REPEAT_TCL STRIP_THM_THEN ASSUME_TAC;;

(* ------------------------------------------------------------------------- *)
(* case_tac : (term -> tactic)                                               *)
(* Isabelle's case_tac for splitting cases.                                  *)
(* ------------------------------------------------------------------------- *)
(* We instantiate type variables in the given term in an attempt to match    *)
(* free variables in the term with free variables of the same name in the    *)
(* goal. This helps so that the user does not need to give explicit types.   *)
(* ------------------------------------------------------------------------- *)

let (case_tac:term->tactic) =
  let trymatch = fun v1 v2 ->
    match (term_match [v2] v1 v2) with
        [],[],ti -> ti
      | _  -> failwith "" in

  fun tm ((_,w) as g) ->
    let gvs = gl_frees g
    and tvs = frees tm in
    let subs = mapfilter (fun x -> tryfind (trymatch x) gvs) tvs in
    let tm' = inst (flat subs) tm in
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
(* induct_tac : tactic                                                       *)
(* Induction over any inductive type.                                        *)
(* ------------------------------------------------------------------------- *)
(* John Harrison introduces custom induction tactics for each type (such as  *)
(* LIST_INDUCT_TAC). This is because of the inconvenient, automated naming   *)
(* of variables in the induction theorems generated by define_type and       *)
(* because you can select to get rid of universal quantifiers of constructor *)
(* parameters automatically. This function is useful if such a custom tactic *)
(* does not exist.                                                           *)
(* ------------------------------------------------------------------------- *)

let (induct_tac:tactic) =
  fun ((_,w) as g) ->
    let tyname = (fst o dest_type o type_of o fst o dest_forall) w in
    let thm = try (snd3 (assoc tyname (!inductive_type_store)))
              with Failure _ -> failwith ("induct_tac: Type " ^ tyname ^ " is not inductive.") in
    (MATCH_MP_TAC thm THEN REPEAT CONJ_TAC) g;;


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

