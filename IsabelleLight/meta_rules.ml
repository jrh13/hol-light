(* ========================================================================= *)
(*                              Isabelle Light                               *)
(*   Isabelle/Procedural style additions and other user-friendly shortcuts.  *)
(*                                                                           *)
(*                   Petros Papapanagiotou, Jacques Fleuriot                 *)
(*              Center of Intelligent Systems and their Applications         *)
(*                          University of Edinburgh                          *)
(*                                 2009-2012                                 *)
(* ========================================================================= *)
(* FILE         : meta_rules.ml                                              *)
(* DESCRIPTION  : Meta rules is a formalisation used to accommodate          *)
(*                Isabelle's inference rules in HOL Light.The technical      *)
(*                details are described in the comments that follow.         *)
(*                Isabelle rule application tactics (rule, erule, etc.) have *)
(*                been defined to work with meta rules.                      *)
(*                We have not been able to accommodate first order rules     *)
(*                allI and exE. We also make use of metavariables which are  *)
(*                restricted by the limitations of term_unify                *)
(*                (ie. no HO unification and no type instantiation).         *)
(* LAST MODIFIED: October 2012                                               *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* ----------------------- META-LEVEL IMPLICATION -------------------------- *)
(* ------------------------------------------------------------------------- *)
(* Emulation of meta-level implication at the object level.                  *)
(* This is purely for syntax and parsing purposes. It solves a number of     *)
(* problems when parsing theorems as meta-rules (see below).                 *)
(* It is applied at the logic level only for transparency.                   *)
(* ------------------------------------------------------------------------- *)
(* Thanks to Phil Scott for the suggestion.                                  *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Syntax definition.                                                        *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("===>",(4,"right"));;

let is_mimp = is_binary "===>";;
let dest_mimp = dest_binary "===>";;


(* ------------------------------------------------------------------------- *)
(* Logic definition: Equivalent to object-level implication.                 *)
(* ------------------------------------------------------------------------- *)

let MIMP_DEF = new_basic_definition
  `(===>) = \p q. p ==> q`;;


(* ------------------------------------------------------------------------- *)
(* CONV, RULE and TACTIC to get rid of meta-level implication in proofs.     *)
(* ------------------------------------------------------------------------- *)

let MIMP_TO_IMP_CONV = BETA_RULE o (PURE_REWRITE_CONV [MIMP_DEF]);;
let MIMP_TO_IMP_RULE = BETA_RULE o (PURE_REWRITE_RULE [MIMP_DEF]);;
let MIMP_TAC = (PURE_REWRITE_TAC [MIMP_DEF]) THEN BETA_TAC;;


(* ------------------------------------------------------------------------- *)
(* Equivalent of TAUT after getting rid of meta-level implication.           *)
(* Helps prove simple propositional meta-rules easily.                       *)
(* ------------------------------------------------------------------------- *)

let MTAUT tm =
    let th = MIMP_TO_IMP_CONV tm in
    EQ_MP (SYM th) ((TAUT o snd o dest_iff o concl) th);;


(* ------------------------------------------------------------------------- *)
(* RULE to replace implication by meta-level implication to easily create    *) 
(* meta-theorems from normal theorems.                                       *)
(* ------------------------------------------------------------------------- *)

let MIMP_THM = MTAUT `(p==>q) <=> (p===>q)`;;
let MIMP_RULE = PURE_REWRITE_RULE[MIMP_THM];;


(* ------------------------------------------------------------------------- *)
(* UNDISCH for meta-level implication.                                       *)
(* Also gets rid of meta-level implication in the undischarged term.         *)
(* ------------------------------------------------------------------------- *)

let MUNDISCH th = 
    let mth = BETA_RULE (AP_THM (AP_THM MIMP_DEF `p:bool`) `q:bool`) in 
    let th =  PURE_ONCE_REWRITE_RULE [mth] th in
    try let undisch_tm = (rand o rator o concl) th in
    PROVE_HYP ((UNDISCH o snd o EQ_IMP_RULE o MIMP_TO_IMP_CONV) undisch_tm) (UNDISCH th)
    with Failure _ -> failwith "MUNDISCH";;


(* ------------------------------------------------------------------------- *)
(* -------------------------- HELPFUL FUNCTIONS ---------------------------- *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* REV_PART_MATCH_I: term list -> (term -> term) -> thm -> term              *)
(*                                                         -> instantiation  *)
(* Does a reverse PART_MATCH and returns the resulting instantiation.        *)
(* Avoids instantiating any of the given variables/constants.                *)
(* Does not apply SPEC_ALL like PART_MATCH does.                             *)
(* ------------------------------------------------------------------------- *)
(* The original PART_MATCH matches a term to part of a theorem so that we can*)
(* instantiate that part with the term.                                      *)
(* The reverse used here, matches the part of the theorem with the term so   *)
(* that the term can be instantiated with the part of the theorem.           *)
(* We use this in cases such as erule where we want (part of) an assumption  *)
(* to match a premise of the rule. We need the instantiation of the rule when*)
(* matched to the assumption (thm) and not the other way around.             *)
(* ------------------------------------------------------------------------- *)

let REV_PART_MATCH_I =
  let rec match_bvs t1 t2 acc =
    try let v1,b1 = dest_abs t1
        and v2,b2 = dest_abs t2 in
        let n1 = fst(dest_var v1) and n2 = fst(dest_var v2) in
        let newacc = if n1 = n2 then acc else insert (n1,n2) acc in
        match_bvs b1 b2 newacc
    with Failure _ -> try
        let l1,r1 = dest_comb t1
        and l2,r2 = dest_comb t2 in
        match_bvs l1 l2 (match_bvs r1 r2 acc)
    with Failure _ -> acc in
  fun avoids partfn th ->
    let bod = concl th in
    let pbod = partfn bod in
    let lconsts = union avoids (intersect (frees (concl th)) (freesl(hyp th))) in
    fun tm ->
      let bvms = match_bvs pbod tm [] in
      let atm = deep_alpha bvms tm in
      term_match lconsts atm (partfn bod) ;; (* whereas in PART_MATCH we do it the other way around *)


(* ------------------------------------------------------------------------- *)
(* term_to_asm_match : term list -> term -> (string * thm) list ->           *)
(*                               (string * thm) list * (thm * instantiation) *)
(* ------------------------------------------------------------------------- *)
(* term_to_asm_match tries to match key to one of the assumptions using      *)
(* REV_PART_MATCH_I. Returns the new assumption list (with the matching      *)
(* assumption removed), the matching assumption and the resulting            *)
(* instantiation used.                                                       *)
(* ------------------------------------------------------------------------- *)
(* It is doubtful that this has practical use outside the Xrule_tac's.       *)
(* It is used in erule, drule and frule to match the major premise to one of *)
(* the assumptions.                                                          *)
(* ------------------------------------------------------------------------- *)

let rec (term_to_asm_match: term list -> term -> (string * thm) list -> (string * thm) list * (thm * instantiation)) =
  fun avoids key asms ->
    if (asms = []) then failwith ("No assumptions match `" ^ (string_of_term key) ^ "`!")
    else try 
      let asm = (snd o hd) asms in
      let i = REV_PART_MATCH_I avoids I asm key in
      (tl asms),(asm,i)
    with Failure _ -> let res,inst = term_to_asm_match avoids key (tl asms) in ((hd asms)::res),inst;;


(* ------------------------------------------------------------------------- *)
(* term_to_asm_n_match : term list -> term -> (string * thm) list -> int ->  *)
(*                               (string * thm) list * (thm * instantiation) *)
(* ------------------------------------------------------------------------- *)
(* Same as term_to_asm_match but only tries to match nth assumption.         *)
(* ------------------------------------------------------------------------- *)
(* It is doubtful that this has practical use outside the Xrulen_tac's.      *)
(* It is used in erulen, drulen and frulen to match the major premise to one *)
(* of the assumptions.                                                       *)
(* ------------------------------------------------------------------------- *)

let rec (term_to_asm_n_match: term list -> term -> (string * thm) list -> int -> (string * thm) list * (thm * instantiation)) =
  fun avoids key asms n ->
    if (asms = []) then failwith "No such assumption found!"
    else try match n with
	0 ->  
	  let asm = (snd o hd) asms in
	  let i = REV_PART_MATCH_I avoids I asm key in
	    (tl asms),(asm,i)
      | _ -> let re_asms,m = term_to_asm_n_match avoids key (tl asms) (n-1) in
	  (hd asms)::re_asms,m
    with Failure _ -> failwith ("Assumption `" ^ ((string_of_term o concl o snd o hd) asms) ^ "` doesn't match `" ^ (string_of_term key) ^ "`!");;



(* gmm is not to be used until qed is updated *)
(* We need a MDISCH for that...               *)

let gmm t =
  let fvs = sort (<) (map (fst o dest_var) (frees t)) in
  (if fvs <> [] then
     let errmsg = end_itlist (fun s t -> s^", "^t) fvs in
     warn true ("Free variables in goal: "^errmsg)
   else ());
  let rec split_mimp = fun tm ->
    if (is_mimp tm) 
    then 
      let (a,b) = dest_mimp tm in
      let (asms, concl) = split_mimp b in
      (a::asms,concl)
    else ([],tm) in
   set_goal (split_mimp t);;


(* ------------------------------------------------------------------------- *)
(* gm : term -> goalstack                                                    *)
(* This is used to set a term containing meta-level implication as a goal.   *)
(* ------------------------------------------------------------------------- *)
(* (+) Uses g to set the goal then MIMP_TAC to get rid of meta-implication.  *)
(* (+) Note that if the goal has normal implication it gets discharged as    *)
(* well. This will be fixed when gmm is fixed.                               *)
(* ------------------------------------------------------------------------- *)

let gm t = g t ; e (MIMP_TAC THEN REPEAT DISCH_TAC);;


(* ------------------------------------------------------------------------- *)
(* Isabelle's natural deduction rules as thms with meta-level implication.   *)
(* ------------------------------------------------------------------------- *)

let conjI = MTAUT `p===>q===>p/\q`;;
let conjunct1 = MTAUT `p/\q===>p`;;
let conjunct2 = MTAUT `p/\q===>q`;;
let conjE = MTAUT `p/\q===>(p===>q===>r)===>r`;; 
let disjI1 = MTAUT `p===>p\/q`;;
let disjI2 = MTAUT `q===>p\/q`;;
let disjE = MTAUT `p\/q===>(p===>r)===>(q===>r)===>r`;;

let impI = MTAUT `(p===>q)===>(p==>q)`;;
let impE = MTAUT `(p==>q)===>p===>(q===>r)===>r`;;
let mp = MTAUT `(p==>q)===>(p===>q)`;;

let iffI = MTAUT `(a===>b)===>(b===>a)===>(a<=>b)`;;
let iffE = MTAUT `(a<=>b)===>((a==>b) ===> (b==>a) ===> r) ===> r`;;

let allE = prove( `(!x:A. P x) ===> (P (a:A) ===> (r:bool)) ===> r` ,
                  MIMP_TAC THEN MESON_TAC[]);;
let exI = prove (`P (a:A)===> ?x:A. P x`, 
                          MIMP_TAC THEN
			  DISCH_TAC THEN 
			    (EXISTS_TAC `a:A`) THEN 
			    (FIRST_ASSUM ACCEPT_TAC));;

let notI = MTAUT `(p===>F)===> ~p`;;
let notE = MTAUT `~a ===> a ===> r`;;


(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------ META-RULES START HERE!! ------------------------ *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* meta_rule (type)                                                          *)
(* The representation of an Isabelle inference rule in HOL Light.            *)
(* ------------------------------------------------------------------------- *)
(* term = The conclusion of the inference rule.                              *)
(* goal list = The premises represented as "meta-subgoals".                  *)
(* thm = The representation of the rule as a theorem used for justification. *)
(*                                                                           *)
(* (+) thm must be of the form H1,H2,...,Hn |- G                             *)
(* (+) H1--Hn must be represented as "meta-subgoals" in any order (1)        *)
(* (+) [|P;Q|] ==> R (in Isabelle notation) is translated as "meta-subgoal"  *)
(*     P,Q ?- R and as P==>Q==>R in the justification theorem.               *)
(* (+) The form of the premises (assumption order etc) must be kept in the   *)
(*     justification theorem (see example in (2))                            *)
(* (+) Use "mk_meta_rule" to create proper meta rules from theorems.         *)
(* ------------------------------------------------------------------------- *)
(* (1) Since we use PROVE_HYP instead of MP to justify rule, erule etc, the  *)
(* order of the subgoals is no longer essential.                             *)
(* (2) Example: conjE                                                        *)
(* In Isabelle:     P/\Q  [|P;Q|]==> R                                       *)
(*                  ------------------                                       *)
(*                          R                                                *)
(*                                                                           *)
(* As a meta rule (briefly - see conjEm below for full notation):            *)
(*              `R`,                           - conclusion                  *)
(*              [                              - premises list               *)
(*                [       ], `P/\Q`  ;                                       *)
(*                [`P`;`Q`], `R`                                             *)
(*              ],                                                           *)
(*              `P/\Q, P==>Q==>R |- R`         - justification theorem       *)
(*                                                                           *)
(* The form of the premises must be preserved in the justification theorem.  *)
(* ie. using `P/\Q, Q==>P==>R |- R` or `Q/\P, P==>Q==>R |- R` as a           *)
(* justification theorem would break the justification and result in an      *)
(* "invalid tactic" exception.                                               *)
(* ------------------------------------------------------------------------- *)

type meta_rule = term * goal list * thm;;


let print_meta_rule: meta_rule->unit = 
  fun (c,glist,j) ->
    print_term c ; hd (map (print_newline () ; print_goal) glist) ;
    print_newline () ; print_thm j ; print_newline ();;


(* ------------------------------------------------------------------------- *)
(* inst_meta_rule: instantiation -> meta_rule -> meta_rule                   *)
(* ------------------------------------------------------------------------- *)
(* Instantiates all parts of meta_rules based on an instantiation.           *)
(* ------------------------------------------------------------------------- *)

let inst_meta_rule:instantiation->meta_rule->meta_rule =
  fun inst (c,glist,j) ->
    instantiate inst c,
    map (inst_goal inst) glist,
    INSTANTIATE_ALL inst j;;


(* ------------------------------------------------------------------------- *)
(* meta_rule_frees: meta_rule -> term list                                   *)
(* ------------------------------------------------------------------------- *)
(* Returns the list of free variables (or Isabelle ?metavariables) in a      *)
(* meta_rule.                                                                *)
(* ------------------------------------------------------------------------- *)

let meta_rule_frees: meta_rule -> term list =
  fun (c,glist,l) ->
    itlist (union o gl_frees) glist (union (frees c) (thm_frees l));;


(* ------------------------------------------------------------------------- *)
(* meta_rule_mk_primed_vars_I: term_list -> meta_rule ->                     *)
(*                                            meta_rule * instantiation      *)
(* ------------------------------------------------------------------------- *)
(* Applies mk_primed_var to all the free variables in a meta_rule.           *)
(* Returns the new meta_rule and the instantiation for the variable renaming.*)
(* ------------------------------------------------------------------------- *)

let meta_rule_mk_primed_vars_I: term list -> meta_rule -> meta_rule * instantiation = 
  fun avoids r ->
    let fvars =  meta_rule_frees r in
    let rec mk_primed_l = fun avoids vars ->
      match vars with 
	[] -> null_inst
      | v::rest -> 
	  let new_v = mk_primed_var avoids v in
	  compose_insts (term_match [] v new_v) (mk_primed_l (new_v::avoids) rest)
    in
    let inst = mk_primed_l avoids fvars in
    (inst_meta_rule inst r),inst;;


(* ------------------------------------------------------------------------- *)
(* meta_rule_mk_primed_vars: term_list -> meta_rule -> meta_rule             *)
(* ------------------------------------------------------------------------- *)
(* Applies mk_primed_var to all the free variables in a meta_rule.           *)
(* ------------------------------------------------------------------------- *)

let meta_rule_mk_primed_vars: term list -> meta_rule -> meta_rule = 
  fun avoids r -> fst (meta_rule_mk_primed_vars_I avoids r);;



(* ------------------------------------------------------------------------- *)
(* inst_meta_rule_vars:                                                      *)
(*                 (term * term) list -> meta_rule -> term list -> meta_rule *)
(* ------------------------------------------------------------------------- *)
(* Instantiates the free variables in a meta_rule. Also renames the          *)
(* uninstantiated variables so as to avoid clashes with free variables and   *)
(* constants in the given goal.                                              *)
(* Essentially it prepares the meta_rule for use with any of xrulem_tac.     *)
(* ------------------------------------------------------------------------- *)
(* (+) By instlist we mean the list of variables and instantiation pairs     *)
(* given by the user.                                                        *)
(* (+) First we check the terms given as variables in the instlist. We must  *)
(* check if they are indeed variables and if they are free variables in the  *)
(* given meta_rule.                                                          *)
(* (+) "match_var" is used to compare a variable with a free variable in the *)
(*  meta_rule. *NOTE* that a variable is accepted as long as it can match a  *)
(* free variable in the meta_rule allowing only type instantiation.          *)
(* (+) "mcheck_var" does the is_var check and tries to find a match with the *)
(* meta_rule's free vars (rfrees) using match_var.                           *)
(* (+) "mcheck_gvar" tries to match variables on the rhs of each instlist    *)
(* pair with the free variables in the goal so as to instantiate their types *)
(* properly. This is done to free the user from declaring the variable types.*)
(* (+) Given variables are replaced with the meta_rule variables (effectively*)
(* achieving type instantiation) and later recombined into the instlist.     *)
(* (+) Secondly, we rename all the variables in the meta_rule using          *)
(* "meta_rule_mk_primed_vars_I" so that they don't match any of the free     *)
(* variables in the goal.                                                    *)
(* (+) We use the same instantiation to rename instlist variables so that    *)
(* they properly match the new variables of the meta_rule.                   *)
(* (+) "new_instlist" should contain variables that fully match primed       *)
(* variables in the meta_rule (new_r).                                       *)
(* (+) For each instlist pair, we find the instantiation that allows the     *)
(* variable to be substituted by the given term. *NOTE* that no check is     *)
(* made on that term. It is the user's responsibility to give a sensible,    *)
(* matching and correctly typed term.                                        *)
(* (+) All the instantiations produced by the instlist are composed into one *)
(* which is then applied to new_r to give the result.                        *)
(* ------------------------------------------------------------------------- *)


let inst_meta_rule_vars: (term * term) list -> meta_rule -> term list -> meta_rule =
  fun instlist r gfrees ->
    let rfrees = meta_rule_frees r in
    let vars,subs = List.split instlist in
    
    let match_var = fun tm1 tm2 ->
      let inst = try term_match [] tm1 tm2 with Failure _ -> [],[tm2,tm1],[] in
      match inst with
	[],[],_ -> tm2
      | _  -> failwith "match_var: no match" in
    
    let mcheck_var = fun tm ->
      if (not (is_var tm)) then failwith ("inst_meta_rule_vars: `" ^ string_of_term tm ^ "` is not a variable")
      else try list_match_first (match_var tm) rfrees 
      with Failure _ -> failwith ("inst_meta_rule_vars: `" ^ string_of_term tm ^ "` could not be found in the meta_rule") in

    let mcheck_gvar = fun var ->
      try let mvar = list_match_first (match_var var) gfrees in
      term_match [] var mvar
      with Failure _ ->  
	warn true ("inst_meta_rule_vars: `" ^ string_of_term var ^ "` could not be found in the goal") ;
	null_inst in 

    let new_r,prim_inst = meta_rule_mk_primed_vars_I gfrees r in
    let new_vars = map ((instantiate prim_inst) o mcheck_var) vars in

    let subs_vars = flat (map frees subs) in
    let new_subs_inst = itlist compose_insts (map mcheck_gvar subs_vars) null_inst in
    let new_subs = map (instantiate new_subs_inst) subs in

    let new_instlist = List.combine new_vars new_subs in
    let mk_inst = fun t1,t2 -> term_match [] t1 t2 in
    let inst = itlist compose_insts (map mk_inst new_instlist) null_inst in
    let result_r = inst_meta_rule inst new_r in
    result_r;;



(* ------------------------------------------------------------------------- *)
(* mk_meta_rule: thm -> meta_rule                                            *)
(* Creates a meta_rule out of a theorem.                                     *)
(* Theorem must be of the form |- H1 ===> H2 ===> ...===> Hn ===> C          *)
(* "===>" is the emulation of meta-level implication so this corresponds to  *)
(* [|H1;H2;...;Hn|] ==> C in Isabelle)                                       *)
(* For each Hi that is a meta-level implication, a "meta_subgoal" is created.*)
(* ------------------------------------------------------------------------- *)
(* (+) undisch_premises uses MUNDISCH to handle meta-level implication. All  *)
(* the premises are undischarged. It returns the list of premises paired     *)
(* with the resulting theorem. Note that MUNDISCH also removes meta-level    *)
(* implication from the undischarged premises.                               *)
(* (+) "mk_meta_subgoal" creates a meta_subgoal from a term. If the term is  *)
(* an implication, the lhs is added as an assumption/premise of the          *)
(* meta_subgoal and mk_meta_subgoal is called recursively for the rhs.       *)
(* (+) The conclusion of the undischarged theorem is the first part of the   *)
(* produced meta_rule.                                                       *)
(* (+) mk_meta_subgoal creates the meta_subgoals for all the premises. They  *)
(* form the second part of the meta_rule.                                    *)
(* (+) The theorem itself is used as the justification theorem, after        *)
(* eliminating any remaining meta-level implication in the conclusion.       *)
(* In theory, the conclusion should never have any remaining meta-level      *)
(* implications. We're just making sure because we don't want any meta-level *)
(* implications to appear in our new subgoals.                               *)
(* ------------------------------------------------------------------------- *)

let (mk_meta_rule: thm -> meta_rule) =
  fun thm ->
    let rec undisch_premises th =
        if is_mimp (concl th) 
        then let rest,res_th = undisch_premises (MUNDISCH th) in
             (rand(rator(concl th)))::rest,res_th
        else [],th in
    let (prems,thm) = undisch_premises thm in
    let rec mk_meta_subgoal tm = (
      if (is_mimp(tm)) then 
	let (a,c) = dest_mimp tm in
	let (prems,concl) = mk_meta_subgoal c in
	("",ASSUME a)::prems,concl
     else [],tm
     ) in
    concl thm,map mk_meta_subgoal prems,MIMP_TO_IMP_RULE thm;;
    

(* ------------------------------------------------------------------------- *)
(* mk_meta_rule_old: thm -> meta_rule                                        *)
(* Creates a meta_rule out of a theorem. === DEPRECATED ===                  *)
(* Theorem must be of the form H1,H2,...,Hn |- C                             *)
(* If Hi is of the form Hi1==>Hi2==>...==>Hik==>HiC then it is treated as    *)
(* Hi1,Hi2,...,Hik ?- HiC (or "meta-level" implication                       *)
(* [|Hi1;Hi2;...;Hik|] ==> HiC in Isabelle) and the corresponding            *)
(* meta_subgoal is created.                                                  *)
(* ------------------------------------------------------------------------- *)
(* --As a result you CANNOT have rules with implication in their premises!-- *)
(*  (You'll have to use mk_elim_meta_rule or build the meta_rule yourself.)  *)
(* ------------------------------------------------------------------------- *)
(* (+) The theorem is destroyed to its hypothesis list and its conclusion.   *)
(* The conclusion is the first part of the meta_rule.                        *)
(* (+) "mk_meta_subgoal" creates a meta_subgoal from a term. If the term is  *)
(* an implication, the lhs is added as an assumption/premise of the          *)
(* meta_subgoal and mk_meta_subgoal is called recursively for the rhs.       *)
(* (+) The theorem itself is used as the justification theorem.              *)
(* ------------------------------------------------------------------------- *)
(* Deprecated. New mk_meta_rule uses meta-level implication.                 *)
(* Kept until new mk_meta_rule is tested and stable.                         *)
(* ------------------------------------------------------------------------- *)

let (mk_meta_rule_old: thm -> meta_rule) =
  fun thm ->
    let (hyps,concl) = dest_thm thm in
    let rec mk_meta_subgoal tm = (
      if (is_imp(tm)) then 
	let (a,c) = dest_imp tm in
	let (prems,concl) = mk_meta_subgoal c in
	("",ASSUME a)::prems,concl
     else [],tm
     ) in
    concl,map mk_meta_subgoal hyps,thm;;



(* ------------------------------------------------------------------------- *)
(* mk_elim_meta_rule_old: thm -> meta_rule                                   *)
(* Creates a meta_rule out of a theorem. === DEPRECATED ===                  *)
(* Works like mk_meta_rule but acommodates elimination/destruction rules     *)
(* a little bit better by not breaking the major premise. This effectively   *)
(* allows the major premise to be an implication.                            *)
(* ------------------------------------------------------------------------- *)
(* In an elimination or destruction rule, the first or major premise is      *)
(* matched against one of the assumptions. Therefore, you cannot have a      *)
(* meta_subgoal for a major premise. If there is an implication there we     *)
(* shall leave it intact and not treat it as "meta-level" implication.       *)
(* This still disallows the use of implication in the rest of the premises   *)
(* (by treating it as "meta-level" implication).                             *)
(* ------------------------------------------------------------------------- *)
(* Deprecated. New mk_meta_rule uses meta-level implication.                 *)
(* Kept until new mk_meta_rule is tested and stable.                         *)
(* ------------------------------------------------------------------------- *)

let (mk_elim_meta_rule_old: thm -> meta_rule) =
  fun thm ->
    let (hyps,concl) = dest_thm thm in
    if (hyps = []) then failwith "mk_elim_meta_rule: Invalid rule - no premises!"
	else let major_prem,hyps = ([],hd hyps),tl hyps in
    let rec mk_meta_subgoal tm = (
      if (is_imp(tm)) then 
	let (a,c) = dest_imp tm in
	let (prems,concl) = mk_meta_subgoal c in
	("",ASSUME a)::prems,concl
     else [],tm
     ) in
    concl,major_prem :: (map mk_meta_subgoal hyps),thm;;



(* ------------------------------------------------------------------------- *)
(* Isabelle's natural deduction inference rules as meta_rules.               *)
(* ------------------------------------------------------------------------- *)
(* The trailing 'm' indicates they are represented as meta_rules as opposed  *)
(* to theorems.                                                              *)
(* Use "mk_meta_rule" to create meta_rules from theorems.                    *)
(* Most of the following can be created using mk_meta_rule but are left here *)
(* as examples.                                                              *)
(* ------------------------------------------------------------------------- *)
(* Deprecated. New mk_meta_rule uses meta-level implication so now ALL of    *)
(* these can be represented at the object-level and turned into meta_rules   *)
(* using mk_meta_rule.                                                       *)
(* ------------------------------------------------------------------------- *)

let conjIm:meta_rule =
  (`p/\q`,
   [
   [],`p:bool`;
   [],`q:bool`
  ],
   conjI);;

let conjEm:meta_rule =
  (`r:bool`,
   [
   [],`p/\q`;
   [("",ASSUME `p:bool`);("",ASSUME `q:bool`)],`r:bool`
  ],
  (UNDISCH o UNDISCH o TAUT) `p/\q==>(p==>q==>r)==>r`
);;

let notEm:meta_rule =
  (`r:bool`,
   [
   [],`~a`;
   [],`a:bool`
  ],
  (UNDISCH o UNDISCH o TAUT) `~a==>a==>r`
);;

let disjI1m:meta_rule =
  (`p\/q`,
   [
   [],`p:bool`;
  ],
   UNDISCH ( TAUT `p==>p\/q` ));;

let disjI2m:meta_rule =
  (`p\/q`,
   [
   [],`q:bool`;
  ],
   UNDISCH ( TAUT `q==>p\/q` ));;

let disjEm:meta_rule =
  (`r:bool`,
   [
   [],`p\/q`;
   [("",ASSUME `p:bool`)],`r:bool`;
   [("",ASSUME `q:bool`)],`r:bool`
  ],
   (UNDISCH o UNDISCH o UNDISCH) ( TAUT `p\/q==>(p==>r)==>(q==>r)==>r`)
  );;


let impIm:meta_rule =
  (`p==>q`,
   [
   [("",ASSUME `p:bool`)],`q:bool`
  ],
   UNDISCH (TAUT `(p==>q)==>(p==>q)`)
);;


let impEm:meta_rule =
  (`r:bool`,
   [
    [],`p==>q`;
    [],`p:bool`;
    [("",ASSUME `q:bool`)],`r:bool`
  ],
   (UNDISCH o UNDISCH o UNDISCH o TAUT) `(p==>q)==>p==>(q==>r)==>r`
);;


let mpm:meta_rule =
  (`q:bool`,
   [
    [],`p==>q`;
    [],`p:bool`
  ],
   (UNDISCH o UNDISCH o TAUT) `(p==>q)==>(p==>q)`
);;

(* Note from old mk_meta_rule:                                               *)
(* This one cannot be expressed as a theorem because HOL Light insists on    *)
(* ordering the assumptions of the theorem so the major premise is `p`       *)
(* instead of `~p`.                                                          *)

let notEm:meta_rule =
  (`r:bool`,
   [
   [],`~a`;
   [],`a:bool`
  ],
  (UNDISCH o UNDISCH o TAUT) `~a==>a==>r`
);;
  

(* ------------------------------------------------------------------------- *)
(* rulem_tac: ((term * term) list -> meta_rule -> tactic):                   *)
(* Isabelle's rule as a HOL Light meta_rule tactic.                          *)
(* Uses a rule of the form  H1,H2,...,Hn |- C represented as a meta_rule     *)
(* to solve A1,A2,...,Am ?- G                                                *)
(* Matches C to the goal G, then splits the goal to                          *)
(*          A1,A2,...,Am ?- H1                                               *)
(*          A1,A2,...,Am ?- H2                                               *)
(*          ...                                                              *)
(*          A1,A2,...,Am ?- Hn                                               *)
(* Hi can be of the form Hi1,Hi2,...,Hik ?- HiC then the goal produced is    *)
(*          A1,A2,...,Am,Hi1,Hi2,...,Hik ?- HiC                              *)
(* ------------------------------------------------------------------------- *)
(* (+) "avoids" lists all the free variables in the assumptions and goal so  *)
(* as to avoid instantiating those (as in variable conflicts with the rule   *)
(* or partly instantiated rule in the case of erule)                         *)
(* (+) First we check if C matches G. If it does we keep the resulting       *)
(* instantiation (ins).                                                      *)
(* (+) We instantiate the "meta-subgoals" of the meta_rule using ins.        *)
(* In essence we're instantiating the premises of the rule. (new_hyps)       *)
(* (+) The "create_goal" function creates the new goals by adding the        *)
(* assumption list A1--Am to the instantiated "meta-subgoal".                *)
(* (+) create_goal is mapped on new_hyps to create the new subgoal list.     *)
(* (+) The "create_dischl" function creates the list of the terms involved   *)
(* in the premises of each instantiated meta-subgoal. In order to create the *)
(* justification of the tactic, we need to convert Hi1,Hi2,...,Hik |- HiC    *)
(* into |- Hi1==>Hi2==>...==>Hik==>HiC. That is the only way we can capture  *)
(* the notion of a "subgoal" within a HOL Light object-level theorem.        *)
(* We will then use PROVE_HYP to eliminate each of the proven subgoals from  *)
(* the rule's justification theorem. In order to achieve this conversion we  *)
(* need to keep a list of the instantiated premises of the rule (dischls)    *)
(* for each meta_subgoal so as to avoid discharging the original goal's      *)
(* assumptions or _FALSITY_.                                                 *)
(* (+) "disch_pair" is used for convenience. dishls is combined with the     *)
(* list of proven subgoals so that each subgoal is attached to its           *)
(* corresponding premises list (dischl). disch_pair then does the discharges.*)
(* It also takes care of instantiating the meta-variables in those premises  *)
(* for proper justification.                                                 *)
(* (+) normalfrees is used to calculate the list of metavariables that will  *)
(* end up in the new subgoals. It contains all the free variables in the     *)
(* goal and instlist.                                                        *)
(* (+) The newly introduced metavariables are found by subtracting           *)
(* normalfrees from the set of all free variables in all new goals.          *)
(* ------------------------------------------------------------------------- *)

let (rulem_tac: (term*term) list->meta_rule->tactic) =
  fun instlist r ((asl,w) as g) ->
    let (c,hyps,thm) = inst_meta_rule_vars instlist r (gl_frees g) in

    let ins = try ( term_match [] c w ) with Failure _ -> failwith "Rule doesn't match!" in

    let new_hyps = map (inst_goal ins) hyps in
    let create_goal = fun asms (hs,gl) -> (hs@asms,gl) in
    let new_goals = map (create_goal asl) new_hyps in
    let rec create_dischl = fun (asms,g) -> if (asms = []) then [] else ((concl o snd o hd) asms)::(create_dischl ((tl asms),g)) in
    let dischls = map create_dischl new_hyps in
    let disch_pair = fun i (dischl,thm) -> DISCHL (map (instantiate i) dischl) thm in
    let normalfrees = itlist union (map ( fun (_,y) -> frees y ) instlist ) (gl_frees g) in
    let mvs = subtract (itlist union (map gl_frees new_goals) []) normalfrees in
    (mvs,null_inst),new_goals,fun i l ->  
      List.fold_left (fun t1 t2 -> PROVE_HYP (INSTANTIATE_ALL i t2) t1) (INSTANTIATE_ALL (compose_insts ins i) thm) (map (disch_pair i) (List.combine dischls l));;


(* ------------------------------------------------------------------------- *)
(* erulem_tac: ((term * term) list -> meta_rule -> tactic):                  *)
(* Isabelle's erule as a HOL Light meta_rule tactic.                         *)
(* Works like rulem but also matches the first hypothesis H1 with one of the *)
(* assumptions A1--Am and instantiates accordingly.                          *)
(* A "proper" elimination rule H1 is of the form ?- H1 (ie. has no premises) *)
(* ------------------------------------------------------------------------- *)
(* Same as rulem with some added stuff.                                      *)
(* (+) If there are no "meta_subgoals" (no new subgoals to create) we fail.  *)
(* (+) Otherwise we use the first "meta_subgoal" as our primary hypothesis   *)
(* (the one that will be eliminated - prim_hyp).                             *)
(* (+) If prim_hyp has premises then this is not a "proper" elimination rule.*)
(* (+) Otherwise try to match any of the assumptions with prim_hyp. The      *)
(* resulting instantiation is elim_inst.                                     *)
(* (+) Instantiate all generated meta_subgoals with elim_inst. Retrieve the  *)
(* (now instantiated) prim_hyp and remove it from the new subgoals (it is    *)
(* trivially proven). We get a "pattern-matching is not exhaustive" warning  *)
(* here, but we have already checked that new_hyps is non-empty.             *)
(* (+) prim_thm is a trivial theorem that proves the subgoal corresponding   *)
(* to prim_hyp.                                                              *)
(* (+) Instantiate the justification theorem with elim_thm.                  *)
(* (+) Add prim_hyp to the justification (pretending its a proven subgoal).  *)
(* (+) Use a hack to add the eliminated assumption to the proven subgoals so *)
(* that we pass the validity check properly.                                 *)
(* ------------------------------------------------------------------------- *)

let (erulem_tac: (term * term) list -> meta_rule->tactic) =
  fun instlist r ((asl,w) as g) ->
    let (c,hyps,thm) = inst_meta_rule_vars instlist r (gl_frees g) in

    let ins = try ( term_match [] c w ) 
    with Failure _ -> failwith "Rule doesn't match!" in
    let new_hyps = map (inst_goal ins) hyps in

    let (prems,prim_hyp) = 
      if (new_hyps = []) then failwith "erule: Not a proper elimination rule: no premises!" 
      else hd new_hyps in
    let avoids = gl_frees g in

    let asl,(prim_thm,elim_inst) = 
      if (prems = []) 
      then try term_to_asm_match avoids prim_hyp asl with Failure s -> failwith ("erule: " ^ s) 
      else failwith "erule: Not a proper elimination rule: major premise has assumptions!" in
    let (_,prim_hyp)::new_hyps = map (inst_goal elim_inst) new_hyps in
    let thm = INSTANTIATE_ALL elim_inst thm in
    
    let create_goal = fun asms (hs,gl) -> (hs@asms,gl) in
    let new_goals = map (create_goal asl) new_hyps in
    let rec create_dischl = 
      fun (asms,g) -> 
	if (asms = []) then [] 
	else ((concl o snd o hd) asms)::(create_dischl ((tl asms),g)) in
    let dischls = map create_dischl new_hyps in
    let disch_pair = fun i (dischl,thm) -> DISCHL (map (instantiate i) dischl) thm in

    let normalfrees = itlist union (map ( fun (_,y) -> frees y ) instlist ) (gl_frees g) in
    let mvs = subtract (itlist union (map gl_frees new_goals) []) normalfrees in
    (mvs,null_inst),new_goals,fun i l ->  
      let major_thmi = INSTANTIATE_ALL i prim_thm in
      List.fold_left (fun t1 t2 -> PROVE_HYP (INSTANTIATE_ALL i t2) t1) (INSTANTIATE_ALL (compose_insts ins i) thm) 
	(major_thmi :: map (ADD_HYP major_thmi) (map (disch_pair i) (List.combine dischls l)));;


(* ------------------------------------------------------------------------- *)
(* drulem_tac: ((term * term) list -> meta_rule -> tactic):                  *)
(* Isabelle's drule as a HOL Light meta_rule tactic.                         *)
(* Uses rules as shown in "rule".                                            *)
(* Matches the first hypothesis H1 with one of the                           *)
(* assumptions A1--Am and instantiates accordingly.                          *)
(* The assumption is removed from the list and the trivial goal is proven    *)
(* automatically.                                                            *)
(* A "proper" destructio rule H1 is of the form ?- H1 (ie. has no premises)  *)
(* The goal A1,A2,...,Am,G ?- C is also added.                               *)     
(* ------------------------------------------------------------------------- *)
(* Same as erulem with a few differences.                                    *)
(* [+] Does not try to match the goal c.                                     *)
(* [+] Adds an extra goal c ?- w after instantiating c.                      *)
(* [+] The new goal is treated slightly different in the justification.      *)
(* It is the one whose premises must be proven so as to get to the final     *)
(* goal. So it gets proven using PROVE_HYP by the result of the              *)
(* justification on the original rule.                                       *) 
(* ------------------------------------------------------------------------- *)

let (drulem_tac: (term * term) list -> meta_rule->tactic) =
  fun instlist r ((asl,w) as g) ->
    let (c,hyps,thm) = inst_meta_rule_vars instlist r (gl_frees g) in

    let (prems,major_prem) = 
      if (hyps = []) then failwith "drule: Not a proper destruction rule: no premises!" 
      else hd hyps in
    let avoids = gl_frees g in

    let asl,(major_thm,elim_inst) = 
      if (prems = [])
      then try term_to_asm_match avoids major_prem asl with Failure s -> failwith ("drule: " ^ s) 
      else failwith "drule: not a proper destruction rule: major premise has assumptions!" in
    let (_,major_asm)::new_hyps = map (inst_goal elim_inst) hyps in
    let thm = INSTANTIATE_ALL elim_inst thm in
    let create_goal = fun asms (hs,gl) -> (hs@asms,gl) in
    let new_goals = (map (create_goal asl) new_hyps) @ [create_goal asl (["",ASSUME (instantiate elim_inst c)],w)] in

    let rec create_dischl = 
      fun (asms,g) -> 
	if (asms = []) then [] 
	else ((concl o snd o hd) asms)::(create_dischl ((tl asms),g)) in
    (* We add an empty discharge list at the end for the extra goal. *)
    let dischls = map create_dischl new_hyps @ [[]] in
    let disch_pair = fun i (dischl,thm) -> DISCHL (map (instantiate i) dischl) thm in

    let normalfrees = itlist union (map ( fun (_,y) -> frees y ) instlist ) (gl_frees g) in
    let mvs = subtract (itlist union (map gl_frees new_goals) []) normalfrees in
    (mvs,null_inst),new_goals,fun i l ->  
      let major_thmi = INSTANTIATE_ALL i major_thm in
      let l = (major_thmi :: map (ADD_HYP major_thmi) (map (disch_pair i) (List.combine dischls l))) in
      PROVE_HYP (List.fold_left (fun t1 t2 -> PROVE_HYP (INSTANTIATE_ALL i t2) t1) (INSTANTIATE_ALL i thm) ((butlast) l)) (last l);;


(* ------------------------------------------------------------------------- *)
(* frulem_tac: ((term * term) list -> meta_rule -> tactic):                  *)
(* Isabelle's frule as a HOL Light meta_rule tactic.                         *)
(* Same as drule, but does not remove the matching assumption from the list. *)
(* ------------------------------------------------------------------------- *)
(* Same as drulem only skipping the parts that eat up the assumption and     *)
(* re-add it to the proven subgoals.                                         *)
(* ------------------------------------------------------------------------- *)

let (frulem_tac: (term * term) list -> meta_rule->tactic) =
  fun instlist r ((asl,w) as g) ->
    let (c,hyps,thm) = inst_meta_rule_vars instlist r (gl_frees g) in

    let (prems,major_prem) = 
      if (hyps = []) then failwith "frule: Not a proper destruction rule: no premises!" 
      else hd hyps in
    let avoids = gl_frees g in

    let _,(major_thm,elim_inst) = 
      if (prems = []) 
      then try term_to_asm_match avoids major_prem asl with Failure s -> failwith ("frule: " ^ s) 
      else failwith "frule: Not a proper destruction rule: major premise has assumptions!" in
    let (_,major_asm)::new_hyps = map (inst_goal elim_inst) hyps in
    let thm = INSTANTIATE_ALL elim_inst thm in
    let create_goal = fun asms (hs,gl) -> (hs@asms,gl) in
    let new_goals = (map (create_goal asl) new_hyps) @ [create_goal asl (["",ASSUME (instantiate elim_inst c)],w)] in

    let rec create_dischl = 
      fun (asms,g) -> 
	if (asms = []) then [] 
	else ((concl o snd o hd) asms)::(create_dischl ((tl asms),g)) in
    let dischls = map create_dischl new_hyps @ [[]] in
    let disch_pair = fun i (dischl,thm) -> DISCHL (map (instantiate i) dischl) thm in

    let normalfrees = itlist union (map ( fun (_,y) -> frees y ) instlist ) (gl_frees g) in
    let mvs = subtract (itlist union (map gl_frees new_goals) []) normalfrees in
    (mvs,null_inst),new_goals,fun i l ->  
      let major_thmi = INSTANTIATE_ALL i major_thm in
      let l = (major_thmi :: ((map (disch_pair i)) o (List.combine dischls)) l) in
      PROVE_HYP (List.fold_left (fun t1 t2 -> PROVE_HYP (INSTANTIATE_ALL i t2) t1) (INSTANTIATE_ALL i thm) ((butlast) l)) (last l);;


(* ------------------------------------------------------------------------- *)
(* cutm_tac: ((term * term) list -> meta_rule -> tactic):                    *)
(* Isabelle's cut_tac as a HOL Light meta_rule tactic.                       *)
(* Inserts a theorem in the assumptions.                                     *)
(* ------------------------------------------------------------------------- *)
(* (+) WARNING: It does not introduce metavariables like the other tactics   *)
(* do! In the TODO list...                                                   *)
(* ------------------------------------------------------------------------- *)

let (cutm_tac: (term * term) list -> meta_rule->tactic) =
    fun instlist r g ->
    let (_,_,thm) = inst_meta_rule_vars instlist r (gl_frees g) in
    (ASSUME_TAC thm) g;;


(* ------------------------------------------------------------------------- *)
(* erulenm_tac : (term * term) list -> int -> meta_rule->tactic)             *)
(* drulenm_tac : (term * term) list -> int -> meta_rule->tactic)             *)
(* frulenm_tac : (term * term) list -> int -> meta_rule->tactic)             *)
(* Identical to their counterparts, the only difference being that they try  *)
(* to match a particular assumption given by number.                         *)
(* ------------------------------------------------------------------------- *)

let (erulenm_tac: (term * term) list -> int -> meta_rule->tactic) =
  fun instlist n r ((asl,w) as g) ->
    let (c,hyps,thm) = inst_meta_rule_vars instlist r (gl_frees g) in

    let ins = try ( term_match [] c w ) 
    with Failure _ -> failwith "Rule doesn't match!" in
    let new_hyps = map (inst_goal ins) hyps in

    let (prems,prim_hyp) = 
      if (new_hyps = []) then failwith "erule: Not a proper elimination rule: no premises!" 
      else hd new_hyps in
    let avoids = gl_frees g in

    let asl,(prim_thm,elim_inst) = 
      if (prems = []) 
      then try term_to_asm_n_match avoids prim_hyp (rev asl) n with Failure s -> failwith ("erule: " ^ s) 
      else failwith "erule: Not a proper elimination rule: major premise has assumptions!" in
    let (_,prim_hyp)::new_hyps = map (inst_goal elim_inst) new_hyps in
    let thm = INSTANTIATE_ALL elim_inst thm in
    
    let create_goal = fun asms (hs,gl) -> (hs@asms,gl) in
    let new_goals = map (create_goal asl) new_hyps in
    let rec create_dischl = 
      fun (asms,g) -> 
	if (asms = []) then [] 
	else ((concl o snd o hd) asms)::(create_dischl ((tl asms),g)) in
    let dischls = map create_dischl new_hyps in
    let disch_pair = fun i (dischl,thm) -> DISCHL (map (instantiate i) dischl) thm in

    let normalfrees = itlist union (map ( fun (_,y) -> frees y ) instlist ) (gl_frees g) in
    let mvs = subtract (itlist union (map gl_frees new_goals) []) normalfrees in
    (mvs,null_inst),new_goals,fun i l ->  
      let major_thmi = INSTANTIATE_ALL i prim_thm in
      List.fold_left (fun t1 t2 -> PROVE_HYP (INSTANTIATE_ALL i t2) t1) (INSTANTIATE_ALL (compose_insts ins i) thm) 
	(major_thmi :: map (ADD_HYP major_thmi) (map (disch_pair i) (List.combine dischls l)));;


let (drulenm_tac: (term * term) list -> int -> meta_rule->tactic) =
  fun instlist n r ((asl,w) as g) ->
    let (c,hyps,thm) = inst_meta_rule_vars instlist r (gl_frees g) in

    let (prems,major_prem) = 
      if (hyps = []) then failwith "drule: Not a proper destruction rule: no premises!" 
      else hd hyps in
    let avoids = gl_frees g in

    let asl,(major_thm,elim_inst) = 
      if (prems = [])
      then try term_to_asm_n_match avoids major_prem (rev asl) n with Failure s -> failwith ("drule: " ^ s) 
      else failwith "drule: not a proper destruction rule: major premise has assumptions!" in
    let (_,major_asm)::new_hyps = map (inst_goal elim_inst) hyps in
    let thm = INSTANTIATE_ALL elim_inst thm in
    let create_goal = fun asms (hs,gl) -> (hs@asms,gl) in
    let new_goals = (map (create_goal asl) new_hyps) @ [create_goal asl (["",ASSUME (instantiate elim_inst c)],w)] in

    let rec create_dischl = 
      fun (asms,g) -> 
	if (asms = []) then [] 
	else ((concl o snd o hd) asms)::(create_dischl ((tl asms),g)) in
    (* We add an empty discharge list at the end for the extra goal. *)
    let dischls = map create_dischl new_hyps @ [[]] in
    let disch_pair = fun i (dischl,thm) -> DISCHL (map (instantiate i) dischl) thm in

    let normalfrees = itlist union (map ( fun (_,y) -> frees y ) instlist ) (gl_frees g) in
    let mvs = subtract (itlist union (map gl_frees new_goals) []) normalfrees in
    (mvs,null_inst),new_goals,fun i l ->  
      let major_thmi = INSTANTIATE_ALL i major_thm in
      let l = (major_thmi :: map (ADD_HYP major_thmi) (map (disch_pair i) (List.combine dischls l))) in
      PROVE_HYP (List.fold_left (fun t1 t2 -> PROVE_HYP (INSTANTIATE_ALL i t2) t1) (INSTANTIATE_ALL i thm) ((butlast) l)) (last l);;


let (frulenm_tac: (term * term) list -> int -> meta_rule->tactic) =
  fun instlist n r ((asl,w) as g) ->
    let (c,hyps,thm) = inst_meta_rule_vars instlist r (gl_frees g) in

    let (prems,major_prem) = 
      if (hyps = []) then failwith "frule: Not a proper destruction rule: no premises!" 
      else hd hyps in
    let avoids = gl_frees g in

    let _,(major_thm,elim_inst) = 
      if (prems = []) 
      then try term_to_asm_n_match avoids major_prem (rev asl) n with Failure s -> failwith ("frule: " ^ s) 
      else failwith "frule: Not a proper destruction rule: major premise has assumptions!" in
    let (_,major_asm)::new_hyps = map (inst_goal elim_inst) hyps in
    let thm = INSTANTIATE_ALL elim_inst thm in
    let create_goal = fun asms (hs,gl) -> (hs@asms,gl) in
    let new_goals = (map (create_goal asl) new_hyps) @ [create_goal asl (["",ASSUME (instantiate elim_inst c)],w)] in

    let rec create_dischl = 
      fun (asms,g) -> 
	if (asms = []) then [] 
	else ((concl o snd o hd) asms)::(create_dischl ((tl asms),g)) in
    let dischls = map create_dischl new_hyps @ [[]] in
    let disch_pair = fun i (dischl,thm) -> DISCHL (map (instantiate i) dischl) thm in

    let normalfrees = itlist union (map ( fun (_,y) -> frees y ) instlist ) (gl_frees g) in
    let mvs = subtract (itlist union (map gl_frees new_goals) []) normalfrees in
    (mvs,null_inst),new_goals,fun i l ->  
      let major_thmi = INSTANTIATE_ALL i major_thm in
      let l = (major_thmi :: ((map (disch_pair i)) o (List.combine dischls)) l) in
      PROVE_HYP (List.fold_left (fun t1 t2 -> PROVE_HYP (INSTANTIATE_ALL i t2) t1) (INSTANTIATE_ALL i thm) ((butlast) l)) (last l);;


(* ------------------------------------------------------------------------- *)
(* Xrulem versions for empty instlist.                                       *)
(* ------------------------------------------------------------------------- *)

let rulem: meta_rule -> tactic = rulem_tac [];;
let erulem: meta_rule -> tactic = erulem_tac [];;
let drulem: meta_rule -> tactic = drulem_tac [];;
let frulem: meta_rule -> tactic = frulem_tac [];;

let erulenm: int -> meta_rule -> tactic = erulenm_tac [];;
let drulenm: int -> meta_rule -> tactic = drulenm_tac [];;
let frulenm: int -> meta_rule -> tactic = frulenm_tac [];;

(* For consistency with HOL Light capitalized tactics: *)
let RULEM,ERULEM,DRULEM,FRULEM = rulem,erulem,drulem,frulem;;
let ERULENM,DRULENM,FRULENM = erulenm,drulenm,frulenm;;


(* ------------------------------------------------------------------------- *)
(* Xrule and Xrule_tac using arbitrary inference rules in the form of thms.  *)
(* (see mk_meta_rule and meta_rule type)                                     *)
(* ------------------------------------------------------------------------- *)

let rule_tac: (term * term) list -> thm -> tactic =
  fun instlist thm ->
    rulem_tac instlist (mk_meta_rule thm);;

let erule_tac: (term * term) list -> thm -> tactic =
  fun instlist thm ->
    erulem_tac instlist (mk_meta_rule thm);;

let drule_tac: (term * term) list -> thm -> tactic =
  fun instlist thm ->
    drulem_tac instlist (mk_meta_rule thm);;

let frule_tac: (term * term) list -> thm -> tactic =
  fun instlist thm ->
    frulem_tac instlist (mk_meta_rule thm);;

let cut_tac: (term * term) list -> thm -> tactic =
  fun instlist thm ->
    cutm_tac instlist (mk_meta_rule thm);;

let RULE_TAC,ERULE_TAC,DRULE_TAC,FRULE_TAC,CUT_TAC = rule_tac,erule_tac,drule_tac,frule_tac,cut_tac;;


let erulen_tac: (term * term) list -> int -> thm -> tactic =
  fun instlist n thm ->
    erulenm_tac instlist n (mk_meta_rule thm);;

let drulen_tac: (term * term) list -> int -> thm -> tactic =
  fun instlist n thm ->
    drulenm_tac instlist n (mk_meta_rule thm);;

let frulen_tac: (term * term) list -> int -> thm -> tactic =
  fun instlist n thm ->
    frulenm_tac instlist n (mk_meta_rule thm);;

let ERULEN_TAC,DRULEN_TAC,FRULEN_TAC = erulen_tac,drulen_tac,frulen_tac;;


let rule: (thm -> tactic) = rule_tac [];;
let erule: (thm -> tactic) = erule_tac [];;
let drule: (thm -> tactic) = drule_tac [];;
let frule: (thm -> tactic) = frule_tac [];;

let RULE,ERULE,DRULE,FRULE = rule,erule,drule,frule;;


let erulen: (int -> thm -> tactic) = erulen_tac [];;
let drulen: (int -> thm -> tactic) = drulen_tac [];;
let frulen: (int -> thm -> tactic) = frulen_tac [];;

let ERULEN,DRULEN,FRULEN = erulen,drulen,frulen;;
