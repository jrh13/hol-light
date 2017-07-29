(******************************************************************************)
(* FILE          : main.ml                                                    *)
(* DESCRIPTION   : The main functions for the Boyer-Moore-style prover.       *)
(*                                                                            *)
(* READS FILES   : <none>                                                     *)
(* WRITES FILES  : <none>                                                     *)
(*                                                                            *)
(* AUTHOR        : R.J.Boulton                                                *)
(* DATE          : 27th June 1991                                             *)
(*                                                                            *)
(* LAST MODIFIED : R.J.Boulton                                                *)
(* DATE          : 13th October 1992                                          *)
(*                                                                            *)
(* LAST MODIFIED : P. Papapanagiotou (University of Edinburgh)                *)
(* DATE          : July 2009                                                  *)
(******************************************************************************)

(*----------------------------------------------------------------------------*)
(* BOYER_MOORE : conv                                                         *)
(*                                                                            *)
(* Boyer-Moore-style automatic theorem prover.                                *)
(* Given a term "tm", attempts to prove |- tm.                                *)
(*----------------------------------------------------------------------------*)

let BOYER_MOORE_FINAL l tm =
my_gen_terms := []; 
counterexamples := 0; 
 proof_print_depth := 0;
bm_steps := (0,0);
try  (proof_print_newline
     (FILTERED_WATERFALL
         [taut_heuristic;
          clausal_form_heuristic;
          setify_heuristic;
          subst_heuristic;
          HL_simplify_heuristic l;
          use_equality_heuristic;
          generalize_heuristic_ext;
          irrelevance_heuristic]
         induction_heuristic []
         (tm,false))
 ) with Failure _ -> failwith "BOYER_MOORE";;

let BOYER_MOORE_MESON l tm =
my_gen_terms := []; 
counterexamples := 0; 
proof_print_depth := 0;
bm_steps := (0,0);
try  (proof_print_newline
     (FILTERED_WATERFALL
         [taut_heuristic;
          clausal_form_heuristic;
          setify_heuristic;
          subst_heuristic;
          HL_simplify_heuristic l;
          meson_heuristic l;
          use_equality_heuristic;
          generalize_heuristic_aderhold;
          irrelevance_heuristic]
         induction_heuristic []
         (tm,false))
 ) with Failure _ -> failwith "BOYER_MOORE";;

let BOYER_MOORE_GEN l tm =
my_gen_terms := []; 
counterexamples := 0; 
 proof_print_depth := 0;
bm_steps := (0,0);
try  (proof_print_newline
     (FILTERED_WATERFALL
         [taut_heuristic;
          clausal_form_heuristic;
          setify_heuristic;
          subst_heuristic;
          HL_simplify_heuristic l;
          use_equality_heuristic;
          generalize_heuristic_aderhold;
          irrelevance_heuristic]
         induction_heuristic []
         (tm,false))
 ) with Failure _ -> failwith "BOYER_MOORE";;

let BOYER_MOORE_EXT tm =
my_gen_terms := []; 
counterexamples := 0; 
proof_print_depth := 0;
bm_steps := (0,0);
try  (proof_print_newline
     (FILTERED_WATERFALL
         [taut_heuristic;
          clausal_form_heuristic;
          setify_heuristic;
          subst_heuristic;
          use_equality_heuristic;
          simplify_heuristic;
(*          meson_heuristic; *)
          generalize_heuristic;
          irrelevance_heuristic]
         induction_heuristic []
         (tm,false))
 ) with Failure _ -> failwith "BOYER_MOORE";;


let BOYER_MOORE_RE l tm =
my_gen_terms := []; 
counterexamples := 0; 
proof_print_depth := 0;
bm_steps := (0,0);
try  (proof_print_newline
     (FILTERED_WATERFALL
         [taut_heuristic;
          clausal_form_heuristic;
          setify_heuristic;
          subst_heuristic;
          use_equality_heuristic;
          HL_simplify_heuristic l;
(*          meson_heuristic; *)
          generalize_heuristic;
          irrelevance_heuristic]
         induction_heuristic []
         (tm,false))
 ) with Failure _ -> failwith "BOYER_MOORE";;

let BOYER_MOORE tm =
counterexamples := 0; 
my_gen_terms := []; 
 proof_print_depth := 0;
bm_steps := (0,0);
try  (proof_print_newline
     (WATERFALL
         [clausal_form_heuristic;
          subst_heuristic;
          simplify_heuristic;
          use_equality_heuristic;
          generalize_heuristic;
          irrelevance_heuristic]
         induction_heuristic
         (tm,false))
 ) with Failure _ -> failwith "BOYER_MOORE";;

(*----------------------------------------------------------------------------*)
(* BOYER_MOORE_CONV : conv                                                    *)
(*                                                                            *)
(* Boyer-Moore-style automatic theorem prover.                                *)
(* Given a term "tm", attempts to prove |- tm = T.                            *)
(*----------------------------------------------------------------------------*)

let BOYER_MOORE_CONV tm =
try (EQT_INTRO (BOYER_MOORE tm)) with Failure _ -> failwith "BOYER_MOORE_CONV";;

(*----------------------------------------------------------------------------*)
(* HEURISTIC_TAC :                                                            *)
(*    ((term # bool) -> ((term # bool) list # proof)) list -> tactic          *)
(*                                                                            *)
(* Tactic to do automatic proof using a list of heuristics. The tactic will   *)
(* fail if it thinks the goal is not a theorem. Otherwise it will either      *)
(* prove the goal, or return as subgoals the conjectures it couldn't handle.  *)
(*                                                                            *)
(* If the `proof_printing' flag is set to true, the tactic displays each new  *)
(* conjecture it generates, prints blank lines between subconjectures which   *)
(* resulted from a split, and prints a final blank line when it can do no     *)
(* more.                                                                      *)
(*                                                                            *)
(* Given a goal, the tactic constructs an implication from it, so that the    *)
(* hypotheses are made available. It then tries to prove this implication.    *)
(* When it can do no more, the function splits the clauses that it couldn't   *)
(* prove into disjuncts. The last disjunct is assumed to be a conclusion, and *)
(* the rest are taken to be hypotheses. These new goals are returned together *)
(* with a proof of the original goal.                                         *)
(*                                                                            *)
(* The proof takes a list of theorems for the subgoals and discharges the     *)
(* hypotheses so that the theorems are in clausal form. These clauses are     *)
(* then used to prove the implication that was constructed from the original  *)
(* goal. Finally the antecedants of this implication are undischarged to give *)
(* a theorem for the original goal.                                           *)
(*----------------------------------------------------------------------------*)

let HEURISTIC_TAC heuristics (asl,w) =
  proof_print_depth := 0; try
 (let asl = map (concl o snd) asl in
   let negate tm = if (is_neg tm) then (rand tm) else (mk_neg tm)
   and NEG_DISJ_DISCH tm th =
     if (is_neg tm)
     then DISJ_DISCH (rand tm) th
     else CONV_RULE (REWR_CONV IMP_DISJ_THM) (DISCH tm th)
  in  let tm = list_mk_imp (asl,w)
  in  let tree = proof_print_newline
                    (filtered_waterfall (clausal_form_heuristic::heuristics) [] (tm,false))
  in  let tml = map fst (fringe_of_clause_tree tree)
  in  let disjsl = map disj_list tml
  in  let goals = map (fun disjs -> (map negate (butlast disjs),last disjs)) disjsl
  in  let HL_goals = map (fun (asmtms,g) -> (map (fun tm -> ("",ASSUME tm)) asmtms),g) goals
  in  let proof _ thl =
         let thl' = map (fun (th,goal)-> itlist NEG_DISJ_DISCH (fst goal) th)
                           (lcombinep (thl,goals))
         in  funpow (length asl) UNDISCH (fprove_clause_tree tree thl')
  in  (null_meta,HL_goals,proof)
 ) with Failure s -> failwith ("HEURISTIC_TAC: " ^ s);;

(*----------------------------------------------------------------------------*)
(* BOYER_MOORE_TAC : tactic                                                   *)
(*                                                                            *)
(* Tactic to do automatic proof using Boyer & Moore's heuristics. The tactic  *)
(* will fail if it thinks the goal is not a theorem. Otherwise it will either *)
(* prove the goal, or return as subgoals the conjectures it couldn't handle.  *)
(*----------------------------------------------------------------------------*)

let (BOYER_MOORE_TAC:tactic) =
  fun aslw  ->
    try (HEURISTIC_TAC
	   [subst_heuristic;
	    simplify_heuristic;
	    use_equality_heuristic;
	    generalize_heuristic;
	    irrelevance_heuristic;
	    induction_heuristic]
	   aslw
    ) with Failure s -> failwith ("BOYER_MOORE_TAC: " ^ s);;


let (BM_SAFE_TAC:thm list -> tactic) =
  fun l aslw ->
    try (HEURISTIC_TAC
	   [taut_heuristic;
	    setify_heuristic;
	    subst_heuristic;
	    HL_simplify_heuristic l;
(*	    use_equality_heuristic;*)
	    induction_heuristic]
	   aslw
    ) with Failure s -> failwith ("BM_SAFE_TAC: " ^ s);;

let (BMG_TAC:thm list -> tactic) =
  fun l aslw ->
    try (HEURISTIC_TAC
	   [taut_heuristic;
	    setify_heuristic;
	    subst_heuristic;
	    HL_simplify_heuristic l;
	    use_equality_heuristic;
	    generalize_heuristic_aderhold;
	    irrelevance_heuristic;
	    induction_heuristic]
	   aslw
    ) with Failure s -> failwith ("BMG_TAC: " ^ s);;

let (BMF_TAC:thm list -> tactic) =
  fun l aslw ->
    try (HEURISTIC_TAC
	   [taut_heuristic;
	    setify_heuristic;
	    subst_heuristic;
	    HL_simplify_heuristic l;
	    use_equality_heuristic; 
	    generalize_heuristic_ext;
	    irrelevance_heuristic; 
	    induction_heuristic]
	   aslw
    ) with Failure s -> failwith ("BMF_TAC: " ^ s);;

let (BMF_NOEQ_TAC:thm list -> tactic) =
  fun l aslw ->
    try (HEURISTIC_TAC
	   [taut_heuristic;
	    setify_heuristic;
	    subst_heuristic;
	    HL_simplify_heuristic l;
	    generalize_heuristic_ext;
	    irrelevance_heuristic;
	    induction_heuristic]
	   aslw
    ) with Failure s -> failwith ("BMF_NOEQ_TAC: " ^ s);;


(*----------------------------------------------------------------------------*)
(* BM_SIMPLIFY_TAC : tactic                                                   *)
(*                                                                            *)
(* Tactic to do automatic simplification using Boyer & Moore's heuristics.    *)
(* The tactic will fail if it thinks the goal is not a theorem. Otherwise, it *)
(* will either prove the goal or return the simplified conjectures as         *)
(* subgoals.                                                                  *)
(*----------------------------------------------------------------------------*)

let BM_SIMPLIFY_TAC aslw =
 try (HEURISTIC_TAC [subst_heuristic;simplify_heuristic] aslw
 ) with Failure _ -> failwith "BM_SIMPLIFY_TAC";;

(*----------------------------------------------------------------------------*)
(* BM_INDUCT_TAC : tactic                                                     *)
(*                                                                            *)
(* Tactic which attempts to do a SINGLE induction using Boyer & Moore's       *)
(* heuristics. The cases of the induction are returned as subgoals.           *)
(*----------------------------------------------------------------------------*)

let BM_INDUCT_TAC aslw =
try  (let induct = ref true
  in  let once_induction_heuristic x =
         if !induct then (induct := false; induction_heuristic x) else failwith ""
  in  HEURISTIC_TAC [once_induction_heuristic] aslw
 ) with Failure _ -> failwith "BM_INDUCT_TAC";;
