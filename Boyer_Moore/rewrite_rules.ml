(******************************************************************************)
(* FILE          : rewrite_rules.ml                                           *)
(* DESCRIPTION   : Using axioms and lemmas as rewrite rules.                  *)
(*                                                                            *)
(* READS FILES   : <none>                                                     *)
(* WRITES FILES  : <none>                                                     *)
(*                                                                            *)
(* AUTHOR        : R.J.Boulton                                                *)
(* DATE          : 14th May 1991                                              *)
(*                                                                            *)
(* LAST MODIFIED : R.J.Boulton                                                *)
(* DATE          : 15th October 1992                                          *)
(*                                                                            *)
(* LAST MODIFIED : P. Papapanagiotou (University of Edinburgh)                *)
(* DATE          : 2008                                                       *)
(******************************************************************************)

(*----------------------------------------------------------------------------*)
(* is_permutative : term -> bool                                              *)
(*                                                                            *)
(* Determines whether or not an equation is permutative (the left-hand and    *)
(* right-hand sides are instances of one another). A permutative equation may *)
(* cause looping when it is used for rewriting.                               *)
(*----------------------------------------------------------------------------*)

let is_permutative tm =
 try (let (l,r) = dest_eq tm
  in  let bind1 = term_match [] l r
      and bind2 = term_match [] r l
  in  true
 ) with Failure _ -> false;;


(*----------------------------------------------------------------------------*)
(* lex_smaller_term : term -> term -> bool                                    *)
(*                                                                            *)
(* Computes whether the first term is `alphabetically' smaller than the       *)
(* second term. Used to avoid looping when rewriting with permutative rules.  *)
(*                                                                            *)
(* A constant is considered to be smaller than a variable which in turn is    *)
(* considered to be smaller than an application. Two variables or two         *)
(* constants are compared alphabetically by name. An application (f1 x1) is   *)
(* considered to be smaller than another application (f2 x2) if either f1 is  *)
(* smaller than f2, or f1 equals f2 and x1 is smaller than x2.                *)
(*----------------------------------------------------------------------------*)

let rec lex_smaller_term tm1 tm2 =
try
 (if (is_const tm1) then
     (if (is_const tm2)
      then let (name1,type1) = dest_const tm1
           and (name2,type2) = dest_const tm2
           in  (if (type1 = type2)
                then name1 < name2
                else failwith "" )
      else true)
  else if (is_var tm1) then
     (if (is_const tm2) then false
      else if (is_var tm2)
      then let (name1,type1) = dest_var tm1
           and (name2,type2) = dest_var tm2
           in  (if (type1 = type2)
                then name1 < name2
                else failwith "" )
      else true)
  else if (is_comb tm1) then
     (if (is_comb tm2)
      then let (rator1,rand1) = dest_comb tm1
           and (rator2,rand2) = dest_comb tm2
           in  (lex_smaller_term rator1 rator2) ||
               ((rator1 = rator2) && (lex_smaller_term rand1 rand2))
      else false)
  else failwith ""
 ) with Failure _ -> failwith "lex_smaller_term";;

(*----------------------------------------------------------------------------*)
(* inst_eq_thm : ((term # term) list # (type # type) list) -> thm -> thm      *)
(*                                                                            *)
(* Instantiates a theorem (possibly having hypotheses) with a binding.        *)
(* Assumes the conclusion is an equality, so that discharging then undisching *)
(* cannot cause parts of the conclusion to be moved into the hypotheses.      *)
(*----------------------------------------------------------------------------*)

let inst_eq_thm (tm_bind,ty_bind) th =
   let (insts,vars) = List.split tm_bind
   in  (UNDISCH_ALL o (SPECL insts) o (GENL vars) o
        (INST_TYPE ty_bind) o DISCH_ALL) th;;

(*----------------------------------------------------------------------------*)
(* applicable_rewrites : term -> thm list                                     *)
(*                                                                            *)
(* Returns the results of rewriting the term with those rewrite rules that    *)
(* are applicable to it. A rewrite rule is not applicable if it's permutative *)
(* and the rewriting does not produce an alphabetically smaller term.         *)
(*----------------------------------------------------------------------------*)

let applicable_rewrites tm =
   let applicable_rewrite tm th =
      let conc = concl th
      in  let (_,tm_bind,ty_bind) = term_match [] (lhs conc) tm
      in  let instth = inst_eq_thm (tm_bind,ty_bind) th
      in  if (is_permutative conc)
          then (let (l,r) = dest_eq (concl instth)
                in  if (lex_smaller_term r l)
                    then instth
                    else failwith "")
          else instth
   in  mapfilter ((applicable_rewrite tm) o snd) !system_rewrites;;

(*----------------------------------------------------------------------------*)
(* ARGS_CONV : conv -> conv                                                   *)
(*                                                                            *)
(* Applies a conversion to every argument of an application of the form       *)
(* "f x1 ... xn".                                                             *)
(*----------------------------------------------------------------------------*)

let rec ARGS_CONV conv tm =
try (
 ((RATOR_CONV (ARGS_CONV conv)) THENC (RAND_CONV conv)) tm
 ) with Failure _ -> ALL_CONV tm;;

(*----------------------------------------------------------------------------*)
(* assump_inst_hyps : term list ->                                            *)
(*                    term ->                                                 *)
(*                    term list ->                                            *)
(*                    ((term # term) list # (type # type) list)               *)
(*                                                                            *)
(* Searches a list of hypotheses for one that matches the specified           *)
(* assumption such that the variables instantiated are precisely those in the *)
(* list of variables given. If such a hypothesis is found, the binding        *)
(* produced by the match is returned.                                         *)
(*----------------------------------------------------------------------------*)

let rec assump_inst_hyps vars assump hyps =
 try(let (_,tm_bind,ty_bind) = term_match [] (hd hyps) assump
  in let bind = (tm_bind,ty_bind)
  in  if (set_eq vars (map snd (fst bind)))
      then bind
      else failwith "")
 with Failure _ -> try (assump_inst_hyps vars assump (tl hyps))
 with Failure _ -> failwith "assump_inst_hyps";;

(*----------------------------------------------------------------------------*)
(* assumps_inst_hyps : term list ->                                           *)
(*                     term list ->                                           *)
(*                     term list ->                                           *)
(*                     ((term # term) list # (type # type) list)              *)
(*                                                                            *)
(* Searches a list of hypotheses and a list of assumptions for a pairing that *)
(* match (the assumption is an instance of the hypothesis) such that the      *)
(* variables instantiated are precisely those in the list of variables given. *)
(* If such a pair is found, the binding produced by the match is returned.    *)
(*----------------------------------------------------------------------------*)

let rec assumps_inst_hyps vars assumps hyps =
 try (assump_inst_hyps vars (hd assumps) hyps)
 with Failure _ -> try (assumps_inst_hyps vars (tl assumps) hyps)
 with Failure _ -> failwith "assumps_inst_hyps";;

(*----------------------------------------------------------------------------*)
(* inst_frees_in_hyps : term list -> thm -> thm                               *)
(*                                                                            *)
(* Takes a theorem (possibly with hypotheses) and computes a list of          *)
(* variables that are free in the hypotheses but not in the conclusion.       *)
(* If this list of variables is empty the original theorem is returned.       *)
(* The function also takes a list of assumptions as another argument. Once it *)
(* has the list of variables it searches for an assumption and a hypothesis   *)
(* such that the hypothesis matches the assumption binding precisely those    *)
(* variables in the list. If this is successful the original theorem is       *)
(* returned having had the variables in the list instantiated.                *)
(*----------------------------------------------------------------------------*)

let inst_frees_in_hyps assumps th =
 try (let hyps = hyp th
  in  let hyp_frees = setify (flat (map frees hyps))
  in  let vars = subtract hyp_frees (frees (concl th))
  in  if (vars = [])
      then th
      else let bind = assumps_inst_hyps vars assumps hyps
           in  inst_eq_thm bind th
 ) with Failure _ -> failwith "inst_frees_in_hyps";;

(*----------------------------------------------------------------------------*)
(* NOT_IMP_EQ_EQ_EQ_OR = |- (~x ==> (y = y')) = ((y \/ x) = (y' \/ x))        *)
(*----------------------------------------------------------------------------*)

let NOT_IMP_EQ_EQ_EQ_OR =
 prove
  (`(~x ==> (y = y')) = ((y \/ x) = (y' \/ x))`,
   BOOL_CASES_TAC `x:bool` THEN
   BOOL_CASES_TAC `y:bool` THEN
   BOOL_CASES_TAC `y':bool` THEN
   REWRITE_TAC []);;

(*----------------------------------------------------------------------------*)
(* IMP_EQ_EQ_EQ_OR_NOT = |- (x ==> (y = y')) = ((y \/ ~x) = (y' \/ ~x))       *)
(*----------------------------------------------------------------------------*)

let IMP_EQ_EQ_EQ_OR_NOT =
 prove
  (`(x ==> (y = y')) = ((y \/ ~x) = (y' \/ ~x))`,
   BOOL_CASES_TAC `x:bool` THEN
   BOOL_CASES_TAC `y:bool` THEN
   BOOL_CASES_TAC `y':bool` THEN
   REWRITE_TAC []);;

(*----------------------------------------------------------------------------*)
(* NOT_IMP_EQ_OR_EQ_EQ_OR_OR =                                                *)
(* |- (~x ==> ((y \/ t) = (y' \/ t))) = ((y \/ (x \/ t)) = (y' \/ (x \/ t)))  *)
(*----------------------------------------------------------------------------*)

let NOT_IMP_EQ_OR_EQ_EQ_OR_OR =
 prove
  (`(~x ==> ((y \/ t) = (y' \/ t))) = ((y \/ (x \/ t)) = (y' \/ (x \/ t)))`,
   BOOL_CASES_TAC `x:bool` THEN
   BOOL_CASES_TAC `y:bool` THEN
   BOOL_CASES_TAC `y':bool` THEN
   BOOL_CASES_TAC `t:bool` THEN
   REWRITE_TAC []);;

(*----------------------------------------------------------------------------*)
(* IMP_EQ_OR_EQ_EQ_OR_NOT_OR =                                                *)
(* |- (x ==> ((y \/ t) = (y' \/ t))) = ((y \/ (~x \/ t)) = (y' \/ (~x \/ t))) *)
(*----------------------------------------------------------------------------*)

let IMP_EQ_OR_EQ_EQ_OR_NOT_OR =
 prove
  (`(x ==> ((y \/ t) = (y' \/ t))) = ((y \/ (~x \/ t)) = (y' \/ (~x \/ t)))`,
   BOOL_CASES_TAC `x:bool` THEN
   BOOL_CASES_TAC `y:bool` THEN
   BOOL_CASES_TAC `y':bool` THEN
   BOOL_CASES_TAC `t:bool` THEN
   REWRITE_TAC []);;

(*----------------------------------------------------------------------------*)
(* IMP_EQ_EQ_EQ_NOT_OR = |- (x ==> (t = t')) = ((~x \/ t) = (~x \/ t'))       *)
(*----------------------------------------------------------------------------*)

let IMP_EQ_EQ_EQ_NOT_OR =
 prove
  (`(x ==> (t = t')) = ((~x \/ t) = (~x \/ t'))`,
   BOOL_CASES_TAC `x:bool` THEN
   BOOL_CASES_TAC `t:bool` THEN
   BOOL_CASES_TAC `t':bool` THEN
   REWRITE_TAC []);;

(*----------------------------------------------------------------------------*)
(* IMP_NOT_EQ_EQ_EQ_OR = |- (~x ==> (t = t')) = ((x \/ t) = (x \/ t'))        *)
(*----------------------------------------------------------------------------*)

let IMP_NOT_EQ_EQ_EQ_OR =
 prove
  (`(~x ==> (t = t')) = ((x \/ t) = (x \/ t'))`,
   BOOL_CASES_TAC `x:bool` THEN
   BOOL_CASES_TAC `t:bool` THEN
   BOOL_CASES_TAC `t':bool` THEN
   REWRITE_TAC []);;

(*----------------------------------------------------------------------------*)
(* T_OR = |- T \/ t = T                                                       *)
(* OR_T = |- t \/ T = T                                                       *)
(* F_OR = |- F \/ t = t                                                       *)
(* OR_F = |- t \/ F = t                                                       *)
(*----------------------------------------------------------------------------*)

let [T_OR;OR_T;F_OR;OR_F;_] = CONJUNCTS (SPEC_ALL OR_CLAUSES);;

(*----------------------------------------------------------------------------*)
(* UNDER_DISJ_DISCH : term -> thm -> thm                                      *)
(*                                                                            *)
(*    A, ~x |- y \/ t = y' \/ t          A, x |- y \/ t = y' \/ t             *)
(*    -------------------------------    ---------------------------------    *)
(*    A |- y \/ x \/ t = y' \/ x \/ t    A |- y \/ ~x \/ t = y' \/ ~x \/ t    *)
(*                                                                            *)
(*    A, ~x |- y = y'                    A, x |- y = y'                       *)
(*    ---------------------              -----------------------              *)
(*    A |- y \/ x = y' \/ x              A |- y \/ ~x = y' \/ ~x              *)
(*                                                                            *)
(* The function assumes that y is a literal, so it is valid to test the LHS   *)
(* of the theorem to see if it is a disjunction in order to determine which   *)
(* rule to use.                                                               *)
(*----------------------------------------------------------------------------*)

let UNDER_DISJ_DISCH tm th =
try
 (let rewrite =
     if (is_disj (lhs (concl th)))
     then if (is_neg tm)
          then NOT_IMP_EQ_OR_EQ_EQ_OR_OR
          else IMP_EQ_OR_EQ_EQ_OR_NOT_OR
     else if (is_neg tm)
          then NOT_IMP_EQ_EQ_EQ_OR
          else IMP_EQ_EQ_EQ_OR_NOT
  in  CONV_RULE (REWR_CONV rewrite) (DISCH tm th)
 ) with Failure _ -> failwith "UNDER_DISJ_DISCH";;

(*----------------------------------------------------------------------------*)
(* OVER_DISJ_DISCH : term -> thm -> thm                                       *)
(*                                                                            *)
(*    A, ~x |- t = t'                    A, x |- t = t'                       *)
(*    ---------------------              -----------------------              *)
(*    A |- x \/ t = x \/ t'              A |- ~x \/ t = ~x \/ t'              *)
(*----------------------------------------------------------------------------*)

let OVER_DISJ_DISCH tm th =
 try (let rewrite =
     if (is_neg tm)
     then IMP_NOT_EQ_EQ_EQ_OR
     else IMP_EQ_EQ_EQ_NOT_OR
  in  CONV_RULE (REWR_CONV rewrite) (DISCH tm th)
 ) with Failure _ -> failwith "OVER_DISJ_DISCH";;

(*----------------------------------------------------------------------------*)
(* MULTI_DISJ_DISCH : (term list # term list) -> thm -> thm                   *)
(*                                                                            *)
(* Examples:                                                                  *)
(*                                                                            *)
(*    MULTI_DISJ_DISCH (["x1"; "x2"],["~x3"; "x4"]) x1, ~x3, x4, x2 |- y = y' *)
(*    --->                                                                    *)
(*    |- ~x1 \/ ~x2 \/ y \/ x3 \/ ~x4 = ~x1 \/ ~x2 \/ y' \/ x3 \/ ~x4         *)
(*                                                                            *)
(*                                                                            *)
(*    MULTI_DISJ_DISCH (["x1"; "x2"],["~x3"; "x4"]) x1, ~x3, x4, x2 |- y = F  *)
(*    --->                                                                    *)
(*    |- ~x1 \/ ~x2 \/ y \/ x3 \/ ~x4 = ~x1 \/ ~x2 \/ x3 \/ ~x4               *)
(*                                                                            *)
(*                                                                            *)
(*    MULTI_DISJ_DISCH (["x1"; "x2"],["~x3"; "x4"]) x1, ~x3, x4, x2 |- y = T  *)
(*    --->                                                                    *)
(*    |- ~x1 \/ ~x2 \/ y \/ x3 \/ ~x4 = T                                     *)
(*----------------------------------------------------------------------------*)

let MULTI_DISJ_DISCH (overs,unders) th =
try
 (let th1 = itlist UNDER_DISJ_DISCH unders th
  in  let tm1 = rhs (concl th1)
  in  let th2 = 
         if (try(is_T (fst (dest_disj tm1))) with Failure _ -> false) then
            (CONV_RULE (RAND_CONV (REWR_CONV T_OR)) th1)
         else if (try(is_F (fst (dest_disj tm1))) with Failure _ -> false) then
            (CONV_RULE (RAND_CONV (REWR_CONV F_OR)) th1)
         else th1
  in  let tm2 = rhs (concl th2)
  in  let rule =
         if (is_T tm2) then CONV_RULE (RAND_CONV (REWR_CONV OR_T)) else I
  in  itlist (fun tm th -> rule (OVER_DISJ_DISCH tm th)) overs th2
 ) with Failure _ -> failwith "MULTI_DISJ_DISCH";;
