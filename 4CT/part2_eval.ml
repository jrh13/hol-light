(* ========================================================================= *)
(* 4CT/part2_eval.ml                                                         *)
(*                                                                           *)
(* Part 2 evaluation layers: computable, first-order, step-reduced and       *)
(* clause-fused reformulations of the reducibility checker, each proved      *)
(* equal to the definitions, and the eval_compile rule databases.            *)
(* ========================================================================= *)

needs "4CT/birkhoff.ml";;
needs "eval_compile/eval_compile.hl";;
needs "eval_compile/eval_default_db.hl";;
needs "4CT/quiztree_eval.ml";;

(* ------------------------------------------------------------------------- *)
(* Equality theorems per type (REFL + both-direction distinctness + inj).    *)
(* ------------------------------------------------------------------------- *)

let make_eq_thm type_name =
  let ty = mk_type(type_name, []) in
  let refl = INST_TYPE [ty, `:A`] REFL_CLAUSE in
  let eqf_clauses =
    try
      let dist_clauses = CONJUNCTS (distinctness type_name) in
      List.concat (List.map (fun th ->
        let th' = SPEC_ALL th in
        let neg_eq = concl th' in
        if is_neg neg_eq then
          let eq = dest_neg neg_eq in
          let l,r = dest_eq eq in
          let fwd = EQF_INTRO th' in
          if l = r then [fwd]
          else [fwd; EQF_INTRO
                (SPEC_ALL(GEN_ALL(ONCE_REWRITE_RULE[EQ_SYM_EQ] th')))]
        else [th']) dist_clauses)
    with _ -> [] in
  let inj_clauses = try CONJUNCTS (injectivity type_name) with _ -> [] in
  let all = refl :: eqf_clauses @ inj_clauses in
  if List.length all = 1 then refl else end_itlist CONJ all;;

let EQ_COLOR = make_eq_thm "color" and EQ_EDGE_PERM = make_eq_thm "edge_perm"
and EQ_CPSTEP = make_eq_thm "cpstep" and EQ_CTREE = make_eq_thm "ctree"
and EQ_GTREE = make_eq_thm "gtree" and EQ_BIT_STACK = make_eq_thm "bit_stack"
and EQ_GRAM_SYMBOL = make_eq_thm "gram_symbol"
and EQ_GTREE_RESTRICTION = make_eq_thm "gtree_restriction"
and EQ_CTREE_RESTRICTION = make_eq_thm "ctree_restriction"
and EQ_CTREE_PAIR = make_eq_thm "ctree_pair"
and EQ_GTREE_PAIR = make_eq_thm "gtree_pair";;

(* ------------------------------------------------------------------------- *)
(* Computable reformulations (eval_compile needs first-order constructor     *)
(* patterns, no function-valued results, no partial-application lambdas, no  *)
(* 0-ary non-constructor constants as values, no `?`/`@`/match).             *)
(* ------------------------------------------------------------------------- *)

(* eta-expand function-valued clauses: f args = \x. b  ==>  f args x = b     *)
let rec eta_expand_eq th =
  let r = rhs (concl th) in
  if is_abs r then
    let v = variant (frees (concl th)) (bndvar r) in
    eta_expand_eq (CONV_RULE (RAND_CONV BETA_CONV) (AP_THM th v))
  else th;;
let eta_clauses th = end_itlist CONJ
  (map (fun c -> GEN_ALL (eta_expand_eq c)) (BODY_CONJUNCTS th));;

let CTREE_CONS_E_CLAUSES = prove
 (`!t. ctree_cons_e Color0 t = ctree_cons0 t /\
 ctree_cons_e Color1 t = ctree_cons1 t /\
       ctree_cons_e Color2 t = ctree_cons2 t /\
       ctree_cons_e Color3 t = ctree_cons3 t`,
  REWRITE_TAC[ctree_cons_e; palette]);;
let CTREE_CONS_PERM_CLAUSES = prove
 (`!g c t. ctree_cons_perm g c t = ctree_cons_e (g c) t`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `c:color` (cases "color")) THEN
  REWRITE_TAC[ctree_cons_perm; palette]);;
let CTREE_SEL_CLAUSES = prove
 (
 `(!t1 t2 t3. ctree_sel (CtreeNode t1 t2 t3) Color0 = CtreeEmpty /\
  ctree_sel (CtreeNode t1 t2 t3) Color1 = t1 /\
               ctree_sel (CtreeNode t1 t2 t3) Color2 = t2 /\
               ctree_sel (CtreeNode t1 t2 t3) Color3 = t3) /\
   (!t c. ctree_sel (CtreeLeaf t) c = CtreeEmpty) /\
   (!c. ctree_sel CtreeEmpty c = CtreeEmpty)`,
  REWRITE_TAC[ctree_sel; palette]);;

(* cpcolor0's ITLIST cpcolor1 .. cpbranch as a first-order function          *)
let cpcol = new_definition `cpcol cp et = ITLIST cpcolor1 cp cpbranch et`;;
let CPCOL_CLAUSES =
  let prove_cl tm =
 prove(tm, REPEAT GEN_TAC THEN REWRITE_TAC[cpcol; ITLIST] THEN
 REWRITE_TAC CPCOLOR1_CASES THEN
                              REWRITE_TAC[GSYM cpcol]) in
  end_itlist CONJ (map prove_cl
   [`!et. cpcol [] et = cpbranch et`;
    `!n cp et. cpcol (CONS (CpR n) cp) et = cpcol cp (rot_list n et)`;
    `!cp et. cpcol (CONS CpRr cp) et = if LENGTH et <= 1 then CtreeEmpty
     else cpcol cp (rotr_list 1 et)`;
    `!cp et. cpcol (CONS CpY cp) et =
       if et = [] then CtreeEmpty
       else ctree_union
 (cpcol cp (CONS (permc Eperm231 (HD et)) (CONS (permc Eperm312
                                                 (HD et)) (TL et))))
                        (cpcol cp (CONS (permc Eperm312 (HD et))
                                   (CONS (permc Eperm231 (HD et)) (TL et))))`;
    `!cp et. cpcol (CONS CpH cp) et =
       if LENGTH et < 2 then CtreeEmpty
       else if HD et = HD (TL et)
            then ctree_union
 (cpcol cp (CONS (permc Eperm231 (HD et)) (CONS (permc Eperm231 (HD et))
                                           (TL (TL et)))))
                             (cpcol cp (CONS (permc Eperm312 (HD et))
                                 (CONS (permc Eperm312 (HD et)) (TL (TL et)))))
            else cpcol cp (CONS (HD (TL et)) (CONS (HD et) (TL (TL et))))`;
    `!cp et. cpcol (CONS CpU cp) et =
       ctree_union (cpcol cp (CONS Color1 (CONS Color1 et)))
                   (ctree_union (cpcol cp (CONS Color2 (CONS Color2 et)))
                   (cpcol cp (CONS Color3 (CONS Color3 et))))`;
    `!cp et. cpcol (CONS CpK cp) et =
       if LENGTH et < 2 then CtreeEmpty
       else if HD et = HD (TL et) then CtreeEmpty
            else cpcol cp (CONS (addc (HD et) (HD (TL et))) (TL (TL et)))`;
    `!cp et. cpcol (CONS CpA cp) et =
       if LENGTH et < 2 then CtreeEmpty
       else if HD et = HD (TL et)
       then cpcol cp (if TL (TL et) = [] then et else TL (TL et))
            else CtreeEmpty`]);;
let CPCOLOR0_CPCOL = end_itlist CONJ
  (map (REWRITE_RULE[GSYM cpcol]) (CONJUNCT1 cpcolor0 :: CPCOLOR0_CASES));;

(* ctree_add_dyck_fn's lambda argument (a partial application) as a helper   *)
let ctree_add_dyck_iter = new_definition
  `ctree_add_dyck_iter n' k lf =
   iteri_ctree k (\m'. ctree_add_dyck_fn n' (SUC m')) lf`;;
let CTREE_ADD_DYCK_ITER_NUM = NUM_FORM (prove
 (`(!n' lf. ctree_add_dyck_iter n' 0 lf = lf) /\
   (!n' k lf. ctree_add_dyck_iter n' (SUC k) lf =
   ctree_add_dyck_fn n' (SUC k) (ctree_add_dyck_iter n' k lf))`,
  REWRITE_TAC[ctree_add_dyck_iter; iteri_ctree]));;
let CTREE_ADD_DYCK_FN_ITER_NUM = NUM_FORM (prove
 (`(!m lf. ctree_add_dyck_fn 0 m lf = CtreeLeaf lf) /\
   (!n' m lf. ctree_add_dyck_fn (SUC n') m lf =
   ctree_add_dyck_iter n' (SUC m) lf)`,
  REWRITE_TAC[ctree_add_dyck_iter; ctree_add_dyck_fn]));;

(* eta-expanded (and numeral-friendly) forms of the function-valued          *)
(* definitions                                                               *)
let ctree_table_sub_e = eta_clauses ctree_table_sub
and gtree_table_sub_e = eta_clauses gtree_table_sub
and gtr_split_fn_e = eta_clauses gtr_split_fn
and ctr_split_fn_e = eta_clauses ctr_split_fn
and has_match_fn_e = eta_clauses has_match_fn
and match_count_fn_e = eta_clauses match_count_fn;;
let gen_dyck_fn_eN = NUM_FORM (eta_clauses gen_dyck_fn)
and leaf_from1_fn_eN = NUM_FORM (eta_clauses leaf_from1_fn)
and gtree_merge_line_fn_eN = NUM_FORM (eta_clauses gtree_merge_line_fn)
and gtree_init_table_fn_eN = NUM_FORM (eta_clauses gtree_init_table_fn)
and ctree_restrict_fn_eN = NUM_FORM (eta_clauses ctree_restrict_fn)
and kempe_tree_closure_fn_eN = NUM_FORM (eta_clauses kempe_tree_closure_fn);;
let ITERI_CTREE_NUM = NUM_FORM iteri_ctree
and CTREE_DECR_NUM = NUM_FORM ctree_decr and ITER_NUM = NUM_FORM ITER;;

(* ktc_step computes ctree_restrict twice (for the two components of the     *)
(* pair): let-bind it, otherwise the work doubles at every closure level.    *)
let KTC_STEP_LET = prove
 (`!h ktc0 ctu gtr gtu.
     ktc_step h ktc0 ctu gtr gtu =
       (if ctree_empty ctu then (ctu, GtreePair gtr gtu)
        else if gtree_empty gtr then (ctu, GtreePair gtr gtu)
        else if gtree_empty gtu then (CtreeEmpty, empty_gtree_pair)
        else let p = ctree_restrict h ctu (CtrCons Bstack0 gtr CtrNil) in
             ktc0 (ctree_pair_sub p F)
             (ctree_rotlr (ctree_pair_sub p T)) gtu)`,
  REWRITE_TAC[ktc_step; LET_DEF; LET_END_DEF]);;

(* 0-ary constants with constructor values must be expanded in every rule    *)
let zero_ary =
  [ctree_simple_leaf; ctree_empty_pair; empty_gtree_pair; init_gtree_h1;
  gtp_0_e; gtp_1_e; gtp_2_e; gtp_3_e; gtp_01_e; gtp_12_e; gtp_13_e; gtp_23_e;
  gtp_e_0; gtp_e_1; gtp_e_2; gtp_e_3;
  gtp_e_01; gtp_e_12; gtp_e_13; gtp_e_23; gtp_0_1; gtp_1_0; gtp_1_2; gtp_2_1;
  gtp_1_3; gtp_3_1; gtp_2_3; gtp_3_2];;
let zx th = PURE_REWRITE_RULE zero_ary th;;
let ctree_of_ttail_x = zx ctree_of_ttail and ctree_union_x = zx ctree_union
and ctree_union_rotlr_x = zx ctree_union_rotlr
and cfcbr2_x = zx cfcbr2 and cfcbr1_x = zx cfcbr1
and gtree_restrict_x = zx gtree_restrict and ktc_step_x = zx KTC_STEP_LET
and gtree_merge_line_fn_eNx = zx gtree_merge_line_fn_eN
and gtree_init_table_fn_eNx = zx gtree_init_table_fn_eN
and ctree_restrict_fn_eNx = zx ctree_restrict_fn_eN;;

(* cprsize is semantic (ring length of cpmap): an OCaml conversion rule      *)
let conv_cprsize = let c = `cprsize`
in fun a opt -> trans_opt opt (cprsize_conv (mk_comb (c, a)));;

(* ------------------------------------------------------------------------- *)
(* The database (kempe_tree side).                                           *)
(* ------------------------------------------------------------------------- *)

let p1_kempe_thms () =
  ["EQ_COLOR",EQ_COLOR,[]; "EQ_EDGE_PERM",EQ_EDGE_PERM,[];
   "EQ_CPSTEP",EQ_CPSTEP,[]; "EQ_CTREE",EQ_CTREE,[];
   "EQ_GTREE",EQ_GTREE,[]; "EQ_BIT_STACK",EQ_BIT_STACK,[];
   "EQ_GRAM_SYMBOL",EQ_GRAM_SYMBOL,[];
   "EQ_GTREE_RESTRICTION",EQ_GTREE_RESTRICTION,[];
   "EQ_CTREE_RESTRICTION",EQ_CTREE_RESTRICTION,[];
   "EQ_CTREE_PAIR",EQ_CTREE_PAIR,[]; "EQ_GTREE_PAIR",EQ_GTREE_PAIR,[];
   "HD",HD,[]; "TL",TL,[]; "APPEND",APPEND,[]; "LENGTH",LENGTH,[];
   "FILTER",FILTER,[]; "EX",EX,[]; "ALL",ALL,[];
   "MAP",MAP,[]; "MEM",MEM,[]; "REVERSE",REVERSE,[]; "LAST",LAST,[];
   "BUTLAST",BUTLAST,[]; "REPLICATE_NUM",REPLICATE_NUM,[];
   "EL_NUM",EL_NUM,[]; "FST",FST,[]; "SND",SND,[]; "ITLIST",ITLIST,[];
   "ITER_NUM",ITER_NUM,[];
   "addc_DEF",addc_DEF,[]; "permc_DEF",permc_DEF,[];
   "edge_rot_DEF",edge_rot_DEF,[]; "ptrace",ptrace,[]; "sumt",sumt,[];
   "permt",permt,[]; "proper_trace",proper_trace,[]; "even_tail",even_tail,[];
   "ttail",ttail,[]; "even_trace",even_trace,[];
   "etrace_perm",etrace_perm,[]; "etrace",etrace,[]; "etail",etail,[];
   "ctree_empty",ctree_empty,[]; "ctree_leaf",ctree_leaf,[];
   "ctree_lsub",ctree_lsub,[]; "ctree_msub",ctree_msub,[];
   "ctree_rsub",ctree_rsub,[]; "CTREE_SEL_CLAUSES",CTREE_SEL_CLAUSES,[];
   "ctree_sub",ctree_sub,[]; "ctree_mem",ctree_mem,[];
   "ctree_pair_sub",ctree_pair_sub,[]; "ctree_leaf_of",ctree_leaf_of,[];
   "ctree_empty_node",ctree_empty_node,[];
   "ctree_cons",ctree_cons,[]; "ctree_cons0",ctree_cons0,[];
   "ctree_cons1",ctree_cons1,[]; "ctree_cons2",ctree_cons2,[];
   "ctree_cons3",ctree_cons3,[];
 "CTREE_CONS_E_CLAUSES",CTREE_CONS_E_CLAUSES,[];
 "ctree_of_ttail_x",ctree_of_ttail_x,[];
   "ctree_union_x",ctree_union_x,[]; "ctree_rotl",ctree_rotl,[];
   "ctree_rotr",ctree_rotr,[]; "ctree_cons_rot",ctree_cons_rot,[];
   "ctree_union_rotlr_x",ctree_union_rotlr_x,[]; "ctree_rotlr",ctree_rotlr,[];
   "ctree_disjoint",ctree_disjoint,[];
   "TAKE_LIST_NUM",TAKE_LIST_NUM,[];
 "DROP_LIST_NUM",DROP_LIST_NUM,[]; "rot_list",rot_list,[];
 "rotr_list",rotr_list,[];
   "CTREE_CONS_PERM_CLAUSES",CTREE_CONS_PERM_CLAUSES,[];
   "cfcbr2_x",cfcbr2_x,[]; "cfcbr1_x",cfcbr1_x,[]; "cpbranch",cpbranch,[];
   "cfprog",cfprog,[]; "CPCOL_CLAUSES",CPCOL_CLAUSES,[];
   "CPCOLOR0_CPCOL",CPCOLOR0_CPCOL,[]; "cpcolor",cpcolor,[];
   "gtree_empty",gtree_empty,[]; "gtree_isleaf",gtree_isleaf,[];
   "gtree_sel",gtree_sel,[]; "gtree_leaf_mem",gtree_leaf_mem,[];
   "GTREE_MEM_CLAUSES",GTREE_MEM_CLAUSES,[]; "case_bitstack",case_bitstack,[];
   "has_match_fn_e",has_match_fn_e,[];
   "has_match",has_match,[]; "match_count_fn_e",match_count_fn_e,[];
   "match_count",match_count,[]; "gtree_sub",gtree_sub,[];
   "gtree_empty_and",gtree_empty_and,[]; "gtree_empty4",gtree_empty4,[];
   "gtree_pair_sub",gtree_pair_sub,[];
   "gtree_pair_partition",gtree_pair_partition,[];
   "gtree_cons_pairs",gtree_cons_pairs,[];
   "gen_dyck_fn_eN",gen_dyck_fn_eN,[]; "gen_dyck",gen_dyck,[]; "dyck",dyck,[];
   "count_cbit1",count_cbit1,[]; "ctree_table_sub_e",ctree_table_sub_e,[];
   "ITERI_CTREE_NUM",ITERI_CTREE_NUM,[];
   "CTREE_ADD_DYCK_FN_ITER_NUM",CTREE_ADD_DYCK_FN_ITER_NUM,[];
   "CTREE_ADD_DYCK_ITER_NUM",CTREE_ADD_DYCK_ITER_NUM,[];
   "ctree_add_dyck",ctree_add_dyck,[]; "leaf_from1_fn_eN",leaf_from1_fn_eN,[];
   "ctree_leaf_table_from",ctree_leaf_table_from,[];
   "ctree_leaf_table",ctree_leaf_table,[];
   "ctree_merge_pair",ctree_merge_pair,[]; "ctree_pairmap",ctree_pairmap,[];
   "ctree_merge_table",ctree_merge_table,[]; "ctree_prune_1",ctree_prune_1,[];
   "ctree_prune_2",ctree_prune_2,[];
   "ctree_prune_3",ctree_prune_3,[]; "ctree_init_tree",ctree_init_tree,[];
   "gtree_merge_pairs",gtree_merge_pairs,[];
   "gtree_table_sub_e",gtree_table_sub_e,[];
   "gtree_merge_line_fn_eNx",gtree_merge_line_fn_eNx,[];
   "gtree_merge_line",gtree_merge_line,[];
   "gtree_init_table_fn_eNx",gtree_init_table_fn_eNx,[];
  "gtree_init_table",gtree_init_table,[]; "gtree_init_tree",gtree_init_tree,[];
   "gtr_mem",gtr_mem,[]; "gtr_cons",gtr_cons,[]; "gtr_isnil",gtr_isnil,[];
   "case_ctree_node",case_ctree_node,[];
   "cons_pop",cons_pop,[]; "gtr_split_fn_e",gtr_split_fn_e,[];
   "gtr_split",gtr_split,[]; "gsplit",gsplit,[];
   "gtr_match0",gtr_match0,[]; "gtr_match1",gtr_match1,[];
   "gtr_match2",gtr_match2,[]; "gtr_match3",gtr_match3,[];
   "gtree_restrict_x",gtree_restrict_x,[];
   "ctr_cons",ctr_cons,[]; "ctr_sub",ctr_sub,[];
   "case_gtree_node",case_gtree_node,[]; "ctr_cons_pop",ctr_cons_pop,[];
   "ctr_split_fn_e",ctr_split_fn_e,[]; "ctr_split",ctr_split,[];
   "csplit",csplit,[]; "ctree_leaf_child",ctree_leaf_child,[];
   "CTREE_DECR_NUM",CTREE_DECR_NUM,[]; "ctr_e_decr",ctr_e_decr,[];
   "ctr_decr",ctr_decr,[]; "cdecr",cdecr,[];
   "ctree_cons_pairs",ctree_cons_pairs,[];
   "ctree_partition",ctree_partition,[]; "ctree_if_e",ctree_if_e,[];
   "ctree_leaf_pair",ctree_leaf_pair,[]; "ctr_isnil",ctr_isnil,[];
   "ctree_restrict_fn_eNx",ctree_restrict_fn_eNx,[];
   "ctree_restrict",ctree_restrict,[];
   "ctree_size",ctree_size,[]; "ctrace_a",ctrace_a,[];
   "ktc_step_x",ktc_step_x,[]; "ktc_stepp",ktc_stepp,[];
   "kempe_tree_closure_fn_eN",kempe_tree_closure_fn_eN,[];
   "kempe_tree_closure",kempe_tree_closure,[]; "kempe_tree",kempe_tree,[]];;

(* ------------------------------------------------------------------------- *)
(* Contract side (cfcontract.ml): computable reformulations.                 *)
(* ------------------------------------------------------------------------- *)

(* the constructor clauses of the clausal definitions (cpstep order CpR n,   *)
(* CpRr, CpY, CpH, CpU, CpK, CpA), as rule theorems                          *)
let CTRMSIZE_CASES = ctrmsize;;
let CFCTR_OK_CASES = cfctr_ok;;
let CFCTR_MAP_CASES = cfctr_map;;
let CTRBAND_CASES0 = tl (CONJUNCTS ctrband);;
(* The CpR clause of ctrband and of cpadj mention the recursive call twice:  *)
(* let-bind it                                                               *)
let CTRBAND_CPR_LET = prove
 (`!cm n cp'. ctrband cm (CONS (CpR n) cp') = let r = ctrband cm cp' in
 (rot_list n (FST r), SND r)`,
  REWRITE_TAC[hd CTRBAND_CASES0; LET_DEF; LET_END_DEF]);;
let CTRBAND_CASES = end_itlist CONJ
  (CONJUNCT1 ctrband :: CTRBAND_CPR_LET :: tl CTRBAND_CASES0);;
let CPADJ_CLAUSES = let cls = CONJUNCTS cpadj in
end_itlist CONJ (el 0 cls :: CPADJ_CPR_LET :: tl (tl cls));;
let CTRMASK_REC_NUM = NUM_FORM ctrmask_rec and CPTRIAD_NUM = NUM_FORM cptriad
and MASK_PRED1_FROM_NUM = NUM_FORM mask_pred1_from;;

(* contract_ctree's `match` on the cfctr option, check_reducible's           *)
(* existential: option helpers                                               *)
let contract_ctree_opt = new_recursive_definition option_RECURSION
 `(contract_ctree_opt cm cp NONE = NONE) /\
  (contract_ctree_opt cm cp (SOME cpc) = if valid_ctrm cm cp
  then SOME (cpcolor cpc) else NONE)`;;
let CONTRACT_CTREE_OPT = prove
 (`!cf. contract_ctree cf =
        contract_ctree_opt (cfcontract_mask cf) (cfprog cf)
          (cfctr (REPLICATE (cprsize (cfprog cf)) F) (cfcontract_mask cf)
          (cfprog cf))`,
  GEN_TAC THEN REWRITE_TAC[contract_ctree; LET_DEF; LET_END_DEF] THEN
  STRUCT_CASES_TAC(ISPEC
 `cfctr (REPLICATE (cprsize (cfprog cf)) F) (cfcontract_mask cf) (cfprog cf)`
 (cases "option")) THEN
  REWRITE_TAC[contract_ctree_opt] THEN
  CONV_TAC(ONCE_DEPTH_CONV MATCH_CONV) THEN REWRITE_TAC[]);;
let check_red_opt = new_recursive_definition option_RECURSION
 `(check_red_opt (kp:ctree) NONE <=> F) /\
  (check_red_opt kp (SOME cct) <=> ctree_disjoint kp cct)`;;
let CHECK_REDUCIBLE_OPT = prove
 (`!cf. check_reducible cf <=>
 check_red_opt (kempe_tree (cfprog cf)) (contract_ctree cf)`,
  GEN_TAC THEN REWRITE_TAC[check_reducible] THEN
  STRUCT_CASES_TAC(ISPEC `contract_ctree cf` (cases "option")) THEN
  REWRITE_TAC[check_red_opt; distinctness "option"; injectivity "option"] THEN
  MESON_TAC[]);;

let p1_contract_thms () =
 ["CTRMSIZE_CASES",CTRMSIZE_CASES,[]; "CTRMASK_REC_NUM",CTRMASK_REC_NUM,[];
  "ctrmask",ctrmask,[]; "nsp",nsp,[];
  "CFCTR_OK_CASES",CFCTR_OK_CASES,[]; "CFCTR_MAP_CASES",CFCTR_MAP_CASES,[];
  "cfctr",cfctr,[]; "mask_list",mask_list,[];
  "cfcontract_mask",cfcontract_mask,[]; "cfcontract_ref",cfcontract_ref,[];
  "cfmask1",cfmask1,[]; "mask_pred1",mask_pred1,[];
  "MASK_PRED1_FROM_NUM",MASK_PRED1_FROM_NUM,[];
  "CPADJ_CLAUSES",CPADJ_CLAUSES,[]; "CTRBAND_CASES",CTRBAND_CASES,[];
  "CPTRIAD_NUM",CPTRIAD_NUM,[]; "valid_ctrm",valid_ctrm,[];
  "cpksize",cpksize,[];
  "contract_ctree_opt",contract_ctree_opt,[];
  "CONTRACT_CTREE_OPT",CONTRACT_CTREE_OPT,[];
  "check_red_opt",check_red_opt,[];
  "CHECK_REDUCIBLE_OPT",CHECK_REDUCIBLE_OPT,[]];;

(* ========================================================================= *)
(* First-order forms.  HOL Light's INST (the kernel's vsubst) runs the       *)
(* capture-avoidance check `vfree_in v t` at every lambda of the             *)
(* instantiated theorem, walking each instantiated argument term in full;    *)
(* eval_compile instantiates a clause theorem with the actual                *)
(* (subtree-sized) arguments at every call, so a clause containing a         *)
(* continuation or a case-analysis lambda costs about a millisecond per      *)
(* call.  The clauses below are defunctionalised equivalents, with           *)
(* accumulator tuples and FST/SND helper constants instead of continuations  *)
(* and function arguments, each proved equal to the original definition;     *)
(* p1_fo_thms replaces the lambda-carrying rules (p1_fo_drop) by them in the *)
(* eval_compile database.  Nothing in the Part 1 files changes.              *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* gtree_restriction splitting (gtreerestrict.ml gtr_split_fn, CPS).         *)
(* ------------------------------------------------------------------------- *)

let gtr_split_acc = define
 `(gtr_split_acc (CtreeNode t1 t2 t3) bs
     (q:gtree_restriction#gtree_restriction#gtree_restriction
      #gtree_restriction) =
     (gtr_cons (Bpush0 bs) t2 (gtr_cons (Bpush1 bs) t3 (FST q)),
      gtr_cons bs t1 (FST (SND q)),
      cons_pop bs t2 t3 (FST (SND (SND q))),
      cons_pop bs t3 t2 (SND (SND (SND q))))) /\
  (gtr_split_acc (CtreeLeaf lf) bs q = q) /\
  (gtr_split_acc CtreeEmpty bs q = q)`;;

let gtr_split4 = define
 `(gtr_split4 GtrNil
 (q:gtree_restriction#gtree_restriction#gtree_restriction#gtree_restriction) =
 q) /\
  (gtr_split4 (GtrCons bs t r) q = gtr_split4 r (gtr_split_acc t bs q))`;;

let gtr_apply4 = new_definition
 `gtr_apply4
 (continue:gtree_restriction->gtree_restriction->gtree_restriction
  ->gtree_restriction->A)
             (q:gtree_restriction#gtree_restriction#gtree_restriction
              #gtree_restriction) =
    continue (FST q) (FST (SND q)) (FST (SND (SND q))) (SND (SND (SND q)))`;;

let GTR_SPLIT_FN_FO = prove
 (
 `!r
 (continue:gtree_restriction->gtree_restriction->gtree_restriction
  ->gtree_restriction->A) r0 r1 r2 r3.
     gtr_split_fn r continue r0 r1 r2 r3 =
     gtr_apply4 continue (gtr_split4 r (r0,r1,r2,r3))`,
  MATCH_MP_TAC gtree_restriction_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[gtr_split_fn; gtr_split4; gtr_apply4; FST; SND];
    MAP_EVERY X_GEN_TAC [`bs:bit_stack`; `t:ctree`; `r:gtree_restriction`] THEN
    DISCH_TAC THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[gtr_split_fn; gtr_split4] THEN
    STRUCT_CASES_TAC(SPEC `t:ctree` (cases "ctree")) THEN
    ASM_REWRITE_TAC[case_ctree_node; gtr_split_acc; FST; SND]]);;

(* gtree_restrict's node clause without the continuation lambda              *)
let gtree_restrict_q = new_definition
 `gtree_restrict_q t0 t1 t2 t3
  (q:gtree_restriction#gtree_restriction#gtree_restriction#gtree_restriction) =
    gtree_cons_pairs (GtreeNode t0 t1 t2 t3)
      (gtree_restrict t0 (FST q)) (gtree_restrict t1 (FST (SND q)))
      (gtree_restrict t2 (FST (SND (SND q))))
      (gtree_restrict t3 (SND (SND (SND q))))`;;

let GTREE_RESTRICT_FO_NODE = prove
 (`!t0 t1 t2 t3 r.
     gtree_restrict (GtreeNode t0 t1 t2 t3) r =
     (if gtr_isnil r then GtreePair GtreeEmpty (GtreeNode t0 t1 t2 t3)
      else gtree_restrict_q t0 t1 t2 t3
      (gtr_split4 r (GtrNil,GtrNil,GtrNil,GtrNil)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[gtree_restrict; gtr_split; GTR_SPLIT_FN_FO; gtr_apply4;
              gtree_restrict_q]);;

(* The full rule set: new node clause + the original leaf/empty clauses      *)
let GTREE_RESTRICT_FO =
  let is_node_clause c =
    let l = lhs (concl (SPEC_ALL c)) in is_comb (hd (snd (strip_comb l))) in
  end_itlist CONJ (GTREE_RESTRICT_FO_NODE ::
                   map GEN_ALL (filter (fun c -> not (is_node_clause c))
                                (CONJUNCTS gtree_restrict)));;
let gtree_restrict_fo_x = zx GTREE_RESTRICT_FO;;

(* ------------------------------------------------------------------------- *)
(* gtr_match0..3 without case_ctree_node / case_bitstack lambdas.            *)
(* ------------------------------------------------------------------------- *)

let gtr_match0_t = define
 `(gtr_match0_t (CtreeNode t1 t2 t3) = (ctree_leaf t2 \/ ctree_leaf t3)) /\
  (gtr_match0_t (CtreeLeaf lf) = F) /\ (gtr_match0_t CtreeEmpty = F)`;;
let gtr_match1_t = define
 `(gtr_match1_t (CtreeNode t1 t2 t3) = ctree_leaf t1) /\
  (gtr_match1_t (CtreeLeaf lf) = F) /\ (gtr_match1_t CtreeEmpty = F)`;;
let gtr_match2_bs = define
 `(gtr_match2_bs Bstack0 (t2:ctree) (t3:ctree) = F) /\
  (gtr_match2_bs (Bpush0 bs') t2 t3 = ctree_leaf t2) /\
  (gtr_match2_bs (Bpush1 bs') t2 t3 = ctree_leaf t3)`;;
let gtr_match2_t = define
 `(gtr_match2_t (CtreeNode t1 t2 t3) bs = gtr_match2_bs bs t2 t3) /\
  (gtr_match2_t (CtreeLeaf lf) bs = F) /\ (gtr_match2_t CtreeEmpty bs = F)`;;
let gtr_match3_t = define
 `(gtr_match3_t (CtreeNode t1 t2 t3) bs = gtr_match2_bs bs t3 t2) /\
  (gtr_match3_t (CtreeLeaf lf) bs = F) /\ (gtr_match3_t CtreeEmpty bs = F)`;;

let GTR_MATCH0_FO = prove
 (`gtr_match0 GtrNil = F /\
   (!bs t r'. gtr_match0 (GtrCons bs t r') =
   (gtr_match0_t t \/ gtr_match0 r'))`,
  CONJ_TAC THENL
   [REWRITE_TAC[gtr_match0];
    REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `t:ctree` (cases "ctree")) THEN
    REWRITE_TAC[gtr_match0; case_ctree_node; gtr_match0_t; DISJ_ASSOC]]);;
let GTR_MATCH1_FO = prove
 (`gtr_match1 GtrNil = F /\
   (!bs t r'. gtr_match1 (GtrCons bs t r') =
   (gtr_match1_t t \/ gtr_match1 r'))`,
  CONJ_TAC THENL
   [REWRITE_TAC[gtr_match1];
    REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `t:ctree` (cases "ctree")) THEN
    REWRITE_TAC[gtr_match1; case_ctree_node; gtr_match1_t; DISJ_ASSOC]]);;
let GTR_MATCH2_FO = prove
 (`gtr_match2 GtrNil = F /\
   (!bs t r'. gtr_match2 (GtrCons bs t r') =
   (gtr_match2_t t bs \/ gtr_match2 r'))`,
  CONJ_TAC THENL
   [REWRITE_TAC[gtr_match2];
    REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `t:ctree` (cases "ctree")) THEN
    STRUCT_CASES_TAC(SPEC `bs:bit_stack` (cases "bit_stack")) THEN
    REWRITE_TAC[gtr_match2; case_ctree_node; case_bitstack; gtr_match2_t;
                gtr_match2_bs; DISJ_ASSOC]]);;
let GTR_MATCH3_FO = prove
 (`gtr_match3 GtrNil = F /\
   (!bs t r'. gtr_match3 (GtrCons bs t r') =
   (gtr_match3_t t bs \/ gtr_match3 r'))`,
  CONJ_TAC THENL
   [REWRITE_TAC[gtr_match3];
    REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `t:ctree` (cases "ctree")) THEN
    STRUCT_CASES_TAC(SPEC `bs:bit_stack` (cases "bit_stack")) THEN
    REWRITE_TAC[gtr_match3; case_ctree_node; case_bitstack; gtr_match3_t;
                gtr_match2_bs; DISJ_ASSOC]]);;

(* ------------------------------------------------------------------------- *)
(* ctree_restriction splitting / decrementing (ctreerestrict.ml, CPS).       *)
(* ------------------------------------------------------------------------- *)

let ctr_split_acc = define
 `(ctr_split_acc (GtreeNode t0 t1 t2 t3) bs
  (q:ctree_restriction#ctree_restriction#ctree_restriction) =
     (ctr_cons bs t1 (FST q),
      ctr_cons (Bpush0 bs) t0 (ctr_cons_pop bs t2 t3 (FST (SND q))),
      ctr_cons (Bpush1 bs) t0 (ctr_cons_pop bs t3 t2 (SND (SND q))))) /\
  (ctr_split_acc GtreeLeaf0 bs q = q) /\ (ctr_split_acc GtreeLeaf1 bs q = q) /\
  (ctr_split_acc GtreeLeaf2 bs q = q) /\ (ctr_split_acc GtreeLeaf3 bs q = q) /\
  (ctr_split_acc GtreeLeaf01 bs q = q) /\
  (ctr_split_acc GtreeLeaf12 bs q = q) /\
  (ctr_split_acc GtreeLeaf13 bs q = q) /\
  (ctr_split_acc GtreeLeaf23 bs q = q) /\
  (ctr_split_acc GtreeEmpty bs q = q)`;;

let ctr_split3 = define
 `(ctr_split3 CtrNil
  (q:ctree_restriction#ctree_restriction#ctree_restriction) = q) /\
  (ctr_split3 (CtrCons bs t r) q = ctr_split3 r (ctr_split_acc t bs q))`;;

let ctr_apply3 = new_definition
 `ctr_apply3
  (continue:ctree_restriction->ctree_restriction->ctree_restriction->A)
             (q:ctree_restriction#ctree_restriction#ctree_restriction) =
    continue (FST q) (FST (SND q)) (SND (SND q))`;;

let CTR_SPLIT_FN_FO = prove
 (
 `!r (continue:ctree_restriction->ctree_restriction->ctree_restriction->A) r1
  r2 r3.
     ctr_split_fn r continue r1 r2 r3 =
     ctr_apply3 continue (ctr_split3 r (r1,r2,r3))`,
  MATCH_MP_TAC ctree_restriction_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[ctr_split_fn; ctr_split3; ctr_apply3; FST; SND];
    MAP_EVERY X_GEN_TAC [`bs:bit_stack`; `t:gtree`; `r:ctree_restriction`] THEN
    DISCH_TAC THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[ctr_split_fn; ctr_split3] THEN
    STRUCT_CASES_TAC(SPEC `t:gtree` (cases "gtree")) THEN
    ASM_REWRITE_TAC[case_gtree_node; ctr_split_acc; FST; SND]]);;

let ctr_decr3 = define
 `(ctr_decr3 (lf1:ctree) (lf2:ctree) (lf3:ctree) CtrNil = (lf1,lf2,lf3)) /\
  (ctr_decr3 lf1 lf2 lf3 (CtrCons bs t r) =
     ctr_decr3 (ctr_e_decr bs t Color1 lf1) (ctr_e_decr bs t Color2 lf2)
     (ctr_e_decr bs t Color3 lf3) r)`;;

let ctree_apply3 = new_definition
 `ctree_apply3 (cont:ctree->ctree->ctree->A) (q:ctree#ctree#ctree) =
  cont (FST q) (FST (SND q)) (SND (SND q))`;;

let CTR_DECR_FO = prove
 (`!r (cont:ctree->ctree->ctree->A) lf1 lf2 lf3.
     ctr_decr cont lf1 lf2 lf3 r =
     ctree_apply3 cont (ctr_decr3 lf1 lf2 lf3 r)`,
  MATCH_MP_TAC ctree_restriction_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[ctr_decr; ctr_decr3; ctree_apply3; FST; SND];
    MAP_EVERY X_GEN_TAC [`bs:bit_stack`; `t:gtree`; `r:ctree_restriction`] THEN
    DISCH_TAC THEN
    REPEAT GEN_TAC THEN ASM_REWRITE_TAC[ctr_decr; ctr_decr3]]);;

(* ------------------------------------------------------------------------- *)
(* ctree_restrict by height, lambda-free.                                    *)
(* ------------------------------------------------------------------------- *)

let ctree_leaf_pair_q = new_definition
 `ctree_leaf_pair_q lf1 lf2 lf3 (q:ctree#ctree#ctree) =
    ctree_leaf_pair lf1 lf2 lf3 (FST q) (FST (SND q)) (SND (SND q))`;;

let ctree_restrict_split = new_definition
 `ctree_restrict_split h t1 t2 t3
  (q:ctree_restriction#ctree_restriction#ctree_restriction) =
    ctree_cons_pairs (ctree_restrict h t1 (FST q))
    (ctree_restrict h t2 (FST (SND q)))
                     (ctree_restrict h t3 (SND (SND q)))`;;

let ctree_restrict_node = define
 `(ctree_restrict_node h (CtreeNode t1 t2 t3) r =
     (if h = 0 then ctree_leaf_pair_q t1 t2 t3 (ctr_decr3 t1 t2 t3 r)
      else ctree_restrict_split (h - 1) t1 t2 t3
      (ctr_split3 r (CtrNil,CtrNil,CtrNil)))) /\
  (ctree_restrict_node h (CtreeLeaf lf) r = ctree_empty_pair) /\
  (ctree_restrict_node h CtreeEmpty r = ctree_empty_pair)`;;

let CTREE_RESTRICT_FO = prove
 (`!h t r. ctree_restrict h t r =
           (if ctr_isnil r then CtreePair t CtreeEmpty
           else ctree_restrict_node h t r)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `h:num` num_CASES) THEN
  REWRITE_TAC[ctree_restrict; ctree_restrict_fn] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(SPEC `t:ctree` (cases "ctree")) THEN
  REWRITE_TAC[case_ctree_node; ctree_restrict_node; NOT_SUC; SUC_SUB1;
              CTR_DECR_FO; ctree_apply3;
              ctree_leaf_pair_q; ctr_split; CTR_SPLIT_FN_FO; ctr_apply3;
              ctree_restrict_split;
              ctree_restrict]);;

let ctree_restrict_node_x = zx ctree_restrict_node;;

(* ------------------------------------------------------------------------- *)
(* ktc_step (restrict computed once, no let) and kempe_tree (no let).        *)
(* ------------------------------------------------------------------------- *)

let ktc_apply = new_definition
 `ktc_apply (ktc0:ctree->ctree->gtree->ctree#gtree_pair)
  (p:ctree_pair) gtu =
    ktc0 (ctree_pair_sub p F) (ctree_rotlr (ctree_pair_sub p T)) gtu`;;

let KTC_STEP_FO = prove
 (`!h ktc0 ctu gtr gtu.
     ktc_step h ktc0 ctu gtr gtu =
     (if ctree_empty ctu then (ctu, GtreePair gtr gtu)
      else if gtree_empty gtr then (ctu, GtreePair gtr gtu)
      else if gtree_empty gtu then (CtreeEmpty, empty_gtree_pair)
      else ktc_apply ktc0
      (ctree_restrict h ctu (CtrCons Bstack0 gtr CtrNil)) gtu)`,
  REWRITE_TAC[ktc_step; ktc_apply]);;
let ktc_step_fo_x = zx KTC_STEP_FO;;

let kempe_tree_h = new_definition
 `kempe_tree_h h (cp:(cpstep)list) =
    FST (kempe_tree_closure h (SUC (SUC h)) (ctree_init_tree (SUC h))
         (cpcolor cp) (gtree_init_tree (SUC h)))`;;

let KEMPE_TREE_FO = prove
 (`!cp. kempe_tree cp =
 (if 2 <= cprsize cp then kempe_tree_h (cprsize cp - 2) cp else CtreeEmpty)`,
  REWRITE_TAC[kempe_tree; kempe_tree_h; LET_DEF; LET_END_DEF]);;

(* ------------------------------------------------------------------------- *)
(* The database: p1_kempe_thms minus the lambda-carrying rules, plus these.  *)
(* ------------------------------------------------------------------------- *)

let p1_fo_drop =
  ["gtr_split_fn_e"; "gtr_split"; "gsplit"; "gtr_match0"; "gtr_match1";
   "gtr_match2"; "gtr_match3";
   "gtree_restrict_x"; "ctr_split_fn_e"; "ctr_split"; "csplit";
   "ctr_decr"; "cdecr";
   "ctree_restrict_fn_eNx"; "ctree_restrict"; "ktc_step_x"; "kempe_tree";
   "case_ctree_node"; "case_gtree_node"];;

let p1_fo_thms () =
  ["gtr_split_acc",gtr_split_acc,[]; "gtr_split4",gtr_split4,[];
   "gtree_restrict_q",gtree_restrict_q,[];
   "gtree_restrict_fo_x",gtree_restrict_fo_x,[];
   "gtr_match0_t",gtr_match0_t,[]; "gtr_match1_t",gtr_match1_t,[];
   "gtr_match2_bs",gtr_match2_bs,[];
   "gtr_match2_t",gtr_match2_t,[]; "gtr_match3_t",gtr_match3_t,[];
   "GTR_MATCH0_FO",GTR_MATCH0_FO,[]; "GTR_MATCH1_FO",GTR_MATCH1_FO,[];
   "GTR_MATCH2_FO",GTR_MATCH2_FO,[]; "GTR_MATCH3_FO",GTR_MATCH3_FO,[];
   "ctr_split_acc",ctr_split_acc,[]; "ctr_split3",ctr_split3,[];
   "ctr_decr3",ctr_decr3,[];
   "ctree_leaf_pair_q",ctree_leaf_pair_q,[];
   "ctree_restrict_split",ctree_restrict_split,[];
   "ctree_restrict_node_x",ctree_restrict_node_x,[];
   "CTREE_RESTRICT_FO",CTREE_RESTRICT_FO,[];
   "ktc_apply",ktc_apply,[]; "ktc_step_fo_x",ktc_step_fo_x,[];
   "kempe_tree_h",kempe_tree_h,[]; "KEMPE_TREE_FO",KEMPE_TREE_FO,[]];;

let p1_kempe_thms_fo () =
  filter (fun (n,_,_) -> not (mem n p1_fo_drop)) (p1_kempe_thms()) @
    p1_fo_thms();;

(* ========================================================================= *)
(* Step-reduced forms.  In a call-count profile of the generated evaluator   *)
(* the leaf decrement chain ctr_e_decr -> gtree_sub -> match_count_fn ->     *)
(* gtree_mem -> gtree_leaf_mem (with the color and gram_symbol equality      *)
(* tests) accounts for about a third of all calls, the gtr_cons / ctr_cons   *)
(* emptiness tests for a tenth and the FST/SND tuple projections for         *)
(* another.  Hence: (1) gtr_cons / ctr_cons by constructor cases, (2) tuple  *)
(* patterns instead of FST/SND projections, (3) cdec1, cdec2, cdec3 =        *)
(* ctr_e_decr at a fixed colour, with its 90 (bit_stack x gtree constructor) *)
(* clauses pre-evaluated by rewriting.  All proved from the definitions;     *)
(* p1_fo2_thms and p1_fo2_drop give the database.                            *)
(* ========================================================================= *)

(* (1) cons-with-emptiness-test by constructor cases                         *)
let GTR_CONS_FO = prove
 (`(!bs r. gtr_cons bs CtreeEmpty r = r) /\
   (!bs lf r. gtr_cons bs (CtreeLeaf lf) r = GtrCons bs (CtreeLeaf lf) r) /\
   (!bs t1 t2 t3 r. gtr_cons bs (CtreeNode t1 t2 t3) r =
   GtrCons bs (CtreeNode t1 t2 t3) r)`,
  REWRITE_TAC[gtr_cons; ctree_empty]);;

let CTR_CONS_FO = prove
 (`(!bs r. ctr_cons bs GtreeEmpty r = r) /\
   (!bs t0 t1 t2 t3 r. ctr_cons bs (GtreeNode t0 t1 t2 t3) r =
   CtrCons bs (GtreeNode t0 t1 t2 t3) r) /\
   (!bs r. ctr_cons bs GtreeLeaf0 r = CtrCons bs GtreeLeaf0 r) /\
   (!bs r. ctr_cons bs GtreeLeaf1 r = CtrCons bs GtreeLeaf1 r) /\
   (!bs r. ctr_cons bs GtreeLeaf2 r = CtrCons bs GtreeLeaf2 r) /\
   (!bs r. ctr_cons bs GtreeLeaf3 r = CtrCons bs GtreeLeaf3 r) /\
   (!bs r. ctr_cons bs GtreeLeaf01 r = CtrCons bs GtreeLeaf01 r) /\
   (!bs r. ctr_cons bs GtreeLeaf12 r = CtrCons bs GtreeLeaf12 r) /\
   (!bs r. ctr_cons bs GtreeLeaf13 r = CtrCons bs GtreeLeaf13 r) /\
   (!bs r. ctr_cons bs GtreeLeaf23 r = CtrCons bs GtreeLeaf23 r)`,
  REWRITE_TAC[ctr_cons; gtree_empty]);;

(* (2) tuple patterns instead of FST/SND projections                         *)
let GTR_SPLIT_ACC_P = prove
 (`(!t1 t2 t3 bs r0 r1 r2 r3.
      gtr_split_acc (CtreeNode t1 t2 t3) bs (r0,r1,r2,r3) =
      (gtr_cons (Bpush0 bs) t2 (gtr_cons (Bpush1 bs) t3 r0), gtr_cons bs t1 r1,
       cons_pop bs t2 t3 r2, cons_pop bs t3 t2 r3)) /\
   (!lf bs q. gtr_split_acc (CtreeLeaf lf) bs q = q) /\
   (!bs q. gtr_split_acc CtreeEmpty bs q = q)`,
  REWRITE_TAC[gtr_split_acc; FST; SND]);;

let GTREE_RESTRICT_Q_P = prove
 (`!t0 t1 t2 t3 r0 r1 r2 r3.
     gtree_restrict_q t0 t1 t2 t3 (r0,r1,r2,r3) =
     gtree_cons_pairs (GtreeNode t0 t1 t2 t3) (gtree_restrict t0 r0)
     (gtree_restrict t1 r1)
                      (gtree_restrict t2 r2) (gtree_restrict t3 r3)`,
  REWRITE_TAC[gtree_restrict_q; FST; SND]);;

let CTR_SPLIT_ACC_P = prove
 (`(!t0 t1 t2 t3 bs r1 r2 r3.
      ctr_split_acc (GtreeNode t0 t1 t2 t3) bs (r1,r2,r3) =
      (ctr_cons bs t1 r1, ctr_cons (Bpush0 bs) t0 (ctr_cons_pop bs t2 t3 r2),
       ctr_cons (Bpush1 bs) t0 (ctr_cons_pop bs t3 t2 r3))) /\
   (!bs q. ctr_split_acc GtreeLeaf0 bs q = q) /\
   (!bs q. ctr_split_acc GtreeLeaf1 bs q = q) /\
   (!bs q. ctr_split_acc GtreeLeaf2 bs q = q) /\
   (!bs q. ctr_split_acc GtreeLeaf3 bs q = q) /\
   (!bs q. ctr_split_acc GtreeLeaf01 bs q = q) /\
   (!bs q. ctr_split_acc GtreeLeaf12 bs q = q) /\
   (!bs q. ctr_split_acc GtreeLeaf13 bs q = q) /\
   (!bs q. ctr_split_acc GtreeLeaf23 bs q = q) /\
   (!bs q. ctr_split_acc GtreeEmpty bs q = q)`,
  REWRITE_TAC[ctr_split_acc; FST; SND]);;

let CTREE_RESTRICT_SPLIT_P = prove
 (`!h t1 t2 t3 r1 r2 r3.
     ctree_restrict_split h t1 t2 t3 (r1,r2,r3) =
     ctree_cons_pairs (ctree_restrict h t1 r1) (ctree_restrict h t2 r2)
     (ctree_restrict h t3 r3)`,
  REWRITE_TAC[ctree_restrict_split; FST; SND]);;

let CTREE_LEAF_PAIR_Q_P = prove
 (`!lf1 lf2 lf3 a b c. ctree_leaf_pair_q lf1 lf2 lf3 (a,b,c) =
 ctree_leaf_pair lf1 lf2 lf3 a b c`,
  REWRITE_TAC[ctree_leaf_pair_q; FST; SND]);;

(* (3) the leaf decrements at a fixed colour, pre-evaluated per constructor  *)
let cdec1 = new_definition `cdec1 bs t lf = ctr_e_decr bs t Color1 lf`;;
let cdec2 = new_definition `cdec2 bs t lf = ctr_e_decr bs t Color2 lf`;;
let cdec3 = new_definition `cdec3 bs t lf = ctr_e_decr bs t Color3 lf`;;

let CTR_DECR3_FO = prove
 (`(!lf1 lf2 lf3. ctr_decr3 lf1 lf2 lf3 CtrNil = (lf1,lf2,lf3)) /\
   (!lf1 lf2 lf3 bs t r.
      ctr_decr3 lf1 lf2 lf3 (CtrCons bs t r) =
      ctr_decr3 (cdec1 bs t lf1) (cdec2 bs t lf2) (cdec3 bs t lf3) r)`,
  REWRITE_TAC[ctr_decr3; cdec1; cdec2; cdec3]);;

let CTREE_DECR_0 =
  prove(`!lf. ctree_decr lf 0 = lf`, REWRITE_TAC[ctree_decr]);;
let CTREE_DECR_1 = prove
 (`!lf. ctree_decr lf 1 = (if ctree_leaf lf then ctree_leaf_child lf else lf)`,
  REWRITE_TAC[num_CONV `1`; ctree_decr]);;

let cdec_conv =
  REWRITE_CONV
    [cdec1; cdec2; cdec3; ctr_e_decr; gtree_sub; match_count; match_count_fn_e;
                GTREE_MEM_CLAUSES; gtree_sel; gtree_leaf_mem; gtree_empty;
                gtree_isleaf; case_bitstack;
                EQ_GRAM_SYMBOL; EQ_COLOR; NOT_CONS_NIL] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV[CTREE_DECR_0; CTREE_DECR_1];;

let cdec_rules c =
  let bs_pats = [`Bstack0`; `Bpush0 bs'`; `Bpush1 bs'`] in
  let t_pats =
  [`GtreeNode a b c d`; `GtreeLeaf0`; `GtreeLeaf1`; `GtreeLeaf2`; `GtreeLeaf3`;
                `GtreeLeaf01`; `GtreeLeaf12`; `GtreeLeaf13`; `GtreeLeaf23`;
                `GtreeEmpty`] in
  end_itlist CONJ
    (flat (map (fun bsp -> map (fun tp -> GEN_ALL (cdec_conv
                            (list_mk_comb (c, [bsp; tp; `lf:ctree`])))) t_pats)
               bs_pats));;
let CDEC1_RULES = cdec_rules `cdec1` and CDEC2_RULES = cdec_rules `cdec2`
and CDEC3_RULES = cdec_rules `cdec3`;;

(* sanity: every clause RHS is lf, or the leaf-pop conditional, or a         *)
(* ctree_decr residual                                                       *)
let _ =
  let residual = filter
 (fun c -> can
 (find_term (fun t -> is_const t && fst (dest_const t) = "gtree_sub"))
   (concl c))
                        (CONJUNCTS CDEC1_RULES @ CONJUNCTS CDEC2_RULES @
                          CONJUNCTS CDEC3_RULES) in
  Printf.printf "CDEC rules: %d clauses, %d with unevaluated gtree_sub\n%!"
    (length (CONJUNCTS CDEC1_RULES) * 3) (length residual);;

(* ------------------------------------------------------------------------- *)
(* The database.                                                             *)
(* ------------------------------------------------------------------------- *)

let p1_fo2_drop =
  ["gtr_cons"; "ctr_cons"; "gtr_split_acc"; "gtree_restrict_q";
   "ctr_split_acc"; "ctree_restrict_split";
   "ctree_leaf_pair_q"; "ctr_decr3"];;

let p1_fo2_thms () =
  ["GTR_CONS_FO",GTR_CONS_FO,[]; "CTR_CONS_FO",CTR_CONS_FO,[];
   "GTR_SPLIT_ACC_P",GTR_SPLIT_ACC_P,[];
   "GTREE_RESTRICT_Q_P",GTREE_RESTRICT_Q_P,[];
   "CTR_SPLIT_ACC_P",CTR_SPLIT_ACC_P,[];
   "CTREE_RESTRICT_SPLIT_P",CTREE_RESTRICT_SPLIT_P,[];
   "CTREE_LEAF_PAIR_Q_P",CTREE_LEAF_PAIR_Q_P,[];
   "CTR_DECR3_FO",CTR_DECR3_FO,[]; "CDEC1_RULES",CDEC1_RULES,[];
   "CDEC2_RULES",CDEC2_RULES,[];
   "CDEC3_RULES",CDEC3_RULES,[]];;

let p1_kempe_thms_fo2 () =
  filter (fun (n,_,_) -> not (mem n p1_fo2_drop)) (p1_kempe_thms_fo()) @
    p1_fo2_thms();;

(* ========================================================================= *)
(* Clause-fused forms.  In HOL every clause application costs the same few   *)
(* kernel operations, so the right tuning is fewer, bigger clauses: each     *)
(* helper call that only inspects constructors is folded into its caller by  *)
(* enumerating the constructor cases and pre-evaluating the clause by        *)
(* rewriting.  Everything is proved from the definitions (p3_tabulate =      *)
(* REWRITE_CONV over all constructor combinations); nothing in the Part 1    *)
(* files changes.  The fusion comes in four layers, (1)-(5), (6)-(9),        *)
(* (10)-(14) and (15) below, each halving the number of calls again.         *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Tabulation: all combinations of argument patterns, each clause pre-       *)
(* evaluated by a rewriting conversion and generalised.                      *)
(* ------------------------------------------------------------------------- *)

let p3_combos =
  let rec go = function
      [] -> [[]]
    | ps::rest -> let r = go rest in
    flat (map (fun p -> map (fun l -> p::l) r) ps) in
  go;;

let p3_tabulate conv c patss =
  map (fun args -> GEN_ALL (conv (list_mk_comb (c, args)))) (p3_combos patss);;

(* clauses whose RHS still mentions one of the given constants               *)
let p3_residual names ths =
  filter (fun c -> can (find_term (fun t -> is_const t && mem
                                   (fst(dest_const t)) names))
                       (rand(concl(SPEC_ALL c)))) ths;;

let bs_pats = [`Bstack0`; `Bpush0 bs'`; `Bpush1 bs'`];;

let ct_pats k =
  [list_mk_comb(`CtreeNode`
  , [mk_var("a"^k,`:ctree`); mk_var("b"^k,`:ctree`); mk_var("c"^k,`:ctree`)]);
   mk_comb(`CtreeLeaf`, mk_var("l"^k,`:ctree`)); `CtreeEmpty`];;

let gt_pats k =
  list_mk_comb(`GtreeNode`, [mk_var("a"^k,`:gtree`); mk_var("b"^k,`:gtree`);
                             mk_var("c"^k,`:gtree`); mk_var("d"^k,`:gtree`)])
                               ::
  [`GtreeLeaf0`; `GtreeLeaf1`; `GtreeLeaf2`; `GtreeLeaf3`;
   `GtreeLeaf01`; `GtreeLeaf12`; `GtreeLeaf13`; `GtreeLeaf23`; `GtreeEmpty`];;

(* ------------------------------------------------------------------------- *)
(* (1) gtr_split_acc: the node clause fused over bs x t1 x t2 x t3 (81       *)
(* clauses); every gtr_cons / cons_pop resolved at tabulation time.          *)
(* ------------------------------------------------------------------------- *)

let gtr_split_acc_conv = REWRITE_CONV[GTR_SPLIT_ACC_P; GTR_CONS_FO; cons_pop];;

let GTR_SPLIT_ACC_FUSED = zx (end_itlist CONJ
  (p3_tabulate gtr_split_acc_conv `gtr_split_acc`
     [map (fun l -> list_mk_comb(`CtreeNode`, l))
       (p3_combos [ct_pats "1"; ct_pats "2"; ct_pats "3"]);
      bs_pats;
      [
 `(r0:gtree_restriction,r1:gtree_restriction,r2:gtree_restriction,
  r3:gtree_restriction)`]]
   @ tl (CONJUNCTS GTR_SPLIT_ACC_P)));;

(* ------------------------------------------------------------------------- *)
(* (2) ctr_split_acc: the node clause fused over bs x t1 (30 clauses); the   *)
(* ctr_cons steps on t0 remain (gtree has 10 constructors, so enumerating t0 *)
(* as well would give 300 clauses).                                          *)
(* ------------------------------------------------------------------------- *)

let ctr_split_acc_conv =
  REWRITE_CONV[CTR_SPLIT_ACC_P; CTR_CONS_FO; ctr_cons_pop];;

let CTR_SPLIT_ACC_FUSED = zx (end_itlist CONJ
  (p3_tabulate ctr_split_acc_conv `ctr_split_acc`
     [map (fun t1 -> list_mk_comb(`GtreeNode`, [`t0:gtree`; t1; `t2:gtree`;
                                                `t3:gtree`])) (gt_pats "1");
      bs_pats;
      [`(r1:ctree_restriction,r2:ctree_restriction,r3:ctree_restriction)`]]
   @ tl (CONJUNCTS CTR_SPLIT_ACC_P)));;

(* ------------------------------------------------------------------------- *)
(* (3) the leaf-counter layer: ctr_decr3 fused over bs x t (30 clauses) with *)
(* The per-colour decrements pre-evaluated (amounts are 0 or 1 here; 2 would *)
(* give cd1 (cd1 lf)); cd1 = decrement by one, by constructor cases.         *)
(* ------------------------------------------------------------------------- *)

let cd1 = new_definition `cd1 lf = ctree_decr lf 1`;;

let CD1_FO = prove
 (`(!l. cd1 (CtreeLeaf l) = l) /\
 (!a b c. cd1 (CtreeNode a b c) = CtreeNode a b c) /\
   cd1 CtreeEmpty = CtreeEmpty`,
  REWRITE_TAC[cd1; CTREE_DECR_1; ctree_leaf; ctree_leaf_child]);;

let CD1_FOLD = prove
 (`!lf. (if ctree_leaf lf then ctree_leaf_child lf else lf) = cd1 lf`,
  REWRITE_TAC[cd1; CTREE_DECR_1]);;

let CTREE_DECR_2 = prove
 (`!lf. ctree_decr lf 2 = cd1 (cd1 lf)`,
  GEN_TAC THEN REWRITE_TAC[cd1; num_CONV `2`; num_CONV `1`; ctree_decr] THEN
  ASM_CASES_TAC `ctree_leaf lf` THEN ASM_REWRITE_TAC[]);;

let ctr_decr3_conv =
  REWRITE_CONV[CTR_DECR3_FO; CDEC1_RULES; CDEC2_RULES; CDEC3_RULES; CD1_FOLD;
               CTREE_DECR_2];;

let CTR_DECR3_FUSED = end_itlist CONJ
  (hd (CONJUNCTS CTR_DECR3_FO) ::
   p3_tabulate ctr_decr3_conv `ctr_decr3`
     [[`lf1:ctree`]; [`lf2:ctree`]; [`lf3:ctree`];
      map (fun l -> match l with
             [bs;t] -> list_mk_comb(`CtrCons`, [bs; t; `r:ctree_restriction`])
           | _ -> fail()) (p3_combos [bs_pats; gt_pats ""])]);;

(* ------------------------------------------------------------------------- *)
(* (4) emptiness tests folded into constructor cases.                        *)
(* ------------------------------------------------------------------------- *)

let CTREE_CONS_FO = end_itlist CONJ
  (p3_tabulate (REWRITE_CONV[ctree_cons; ctree_empty]) `ctree_cons`
  [ct_pats "1"; ct_pats "2"; ct_pats "3"]);;

let CTREE_EMPTY_NODE_FO = end_itlist CONJ
  (p3_tabulate (REWRITE_CONV[ctree_empty_node; ctree_empty]) `ctree_empty_node`
     [map (fun l -> list_mk_comb(`CtreeNode`, l))
       (p3_combos [ct_pats "1"; ct_pats "2"; ct_pats "3"])]
   @ [el 0 (CONJUNCTS ctree_empty_node); el 1 (CONJUNCTS ctree_empty_node)]);;

let CTREE_IF_E_FO = end_itlist CONJ
  (p3_tabulate (REWRITE_CONV[ctree_if_e; ctree_empty]) `ctree_if_e`
  [[`lf:ctree`]; ct_pats "'"]);;

let GTREE_EMPTY_AND_FO = end_itlist CONJ
  (p3_tabulate (REWRITE_CONV[gtree_empty_and; gtree_empty]) `gtree_empty_and`
  [gt_pats ""; [`b:bool`]]);;

let CTREE_LEAF_PAIR_FUSED = zx (end_itlist CONJ
  (p3_tabulate (REWRITE_CONV[ctree_leaf_pair; CTREE_CONS_FO; CTREE_IF_E_FO])
    `ctree_leaf_pair`
     [[`lf1:ctree`]; [`lf2:ctree`]; [`lf3:ctree`]; ct_pats "1'"; ct_pats "2'";
      ct_pats "3'"]));;

(* ------------------------------------------------------------------------- *)
(* (5) the nil tests of the two restrict recursions by constructor cases on  *)
(* r                                                                         *)
(* ------------------------------------------------------------------------- *)

let gtree_restrict_fo3_x = zx (end_itlist CONJ
  (p3_tabulate (REWRITE_CONV[GTREE_RESTRICT_FO; gtr_isnil]) `gtree_restrict`
     [gt_pats ""; [`GtrNil`; `GtrCons bs t r`]]));;

let CTREE_RESTRICT_FO3 = zx (end_itlist CONJ
  (p3_tabulate (REWRITE_CONV[CTREE_RESTRICT_FO; ctr_isnil]) `ctree_restrict`
     [[`h:num`]; [`t:ctree`]; [`CtrNil`; `CtrCons bs g r`]]));;

(* sanity: no unevaluated helper left in any fused RHS                       *)
let _ =
  let chk name th bad =
    let n = length (p3_residual bad (CONJUNCTS th)) in
    Printf.printf "FO3 %-22s %4d clauses, residual %d\n%!" name
      (length (CONJUNCTS th)) n;
    if n <> 0 then failwith ("part2_fo3_dev: residual in " ^ name) in
  chk "GTR_SPLIT_ACC_FUSED" GTR_SPLIT_ACC_FUSED
    ["gtr_cons";"cons_pop";"gtr_split_acc"];
  chk "CTR_SPLIT_ACC_FUSED" CTR_SPLIT_ACC_FUSED
    ["ctr_cons_pop";"ctr_split_acc"];
  chk "CTR_DECR3_FUSED" CTR_DECR3_FUSED
 ["cdec1";"cdec2";"cdec3";"ctree_decr";"ctree_leaf";"ctree_leaf_child";"COND"];
  chk "CTREE_CONS_FO" CTREE_CONS_FO ["ctree_empty";"COND"];
  chk "CTREE_EMPTY_NODE_FO" CTREE_EMPTY_NODE_FO ["ctree_empty"];
  chk "CTREE_IF_E_FO" CTREE_IF_E_FO ["ctree_empty";"COND"];
  chk "GTREE_EMPTY_AND_FO" GTREE_EMPTY_AND_FO
    ["gtree_empty";"gtree_empty_and"];
  chk "CTREE_LEAF_PAIR_FUSED" CTREE_LEAF_PAIR_FUSED
    ["ctree_if_e";"ctree_empty";"COND";"ctree_leaf_pair"];
  chk "gtree_restrict_fo3_x" gtree_restrict_fo3_x ["gtr_isnil"];
  chk "CTREE_RESTRICT_FO3" CTREE_RESTRICT_FO3 ["ctr_isnil";"COND"];;

(* ------------------------------------------------------------------------- *)
(* The second layer.                                                         *)
(* (6) the list walkers gtr_split4 / ctr_split3 absorb the (fused) split_acc *)
(* step; (7) ctree_union / ctree_union_rotlr by constructor cases (no        *)
(* ctree_empty / ctree_leaf / sub-selector steps); (8) gtree_empty4 as a     *)
(* short-circuit chain ge4 -> ge3 -> ge2 -> gtree_empty by first-argument    *)
(* cases; (9) ctree_cons_pairs with its first emptiness test pre-resolved.   *)
(* ------------------------------------------------------------------------- *)

let GTR_SPLIT4_FUSED = zx (end_itlist CONJ
  (hd (CONJUNCTS gtr_split4) ::
   p3_tabulate (REWRITE_CONV[gtr_split4; GTR_SPLIT_ACC_FUSED]) `gtr_split4`
     [map (fun l -> match l with
             [bs;t] -> list_mk_comb(`GtrCons`, [bs; t; `r:gtree_restriction`])
           | _ -> fail())
          (p3_combos [bs_pats;
                      map (fun l -> list_mk_comb(`CtreeNode`, l))
                        (p3_combos [ct_pats "1"; ct_pats "2"; ct_pats "3"])
                      @ [`CtreeLeaf lf`; `CtreeEmpty`]]);
      [
 `(r0:gtree_restriction,r1:gtree_restriction,r2:gtree_restriction,
  r3:gtree_restriction)`]]));;

let CTR_SPLIT3_FUSED = zx (end_itlist CONJ
  (hd (CONJUNCTS ctr_split3) ::
   p3_tabulate (REWRITE_CONV[ctr_split3; CTR_SPLIT_ACC_FUSED]) `ctr_split3`
     [map (fun l -> match l with
             [bs;t] -> list_mk_comb(`CtrCons`, [bs; t; `r:ctree_restriction`])
           | _ -> fail())
          (p3_combos [bs_pats;
                      map (fun t1 -> list_mk_comb(`GtreeNode`, [`t0:gtree`; t1;
                                        `t2:gtree`; `t3:gtree`])) (gt_pats "1")
                      @ tl (gt_pats "")]);
      [`(r1:ctree_restriction,r2:ctree_restriction,r3:ctree_restriction)`]]));;

let CTREE_UNION_FO = zx (end_itlist CONJ
  (p3_tabulate
 (REWRITE_CONV[ctree_union; ctree_empty; ctree_leaf; ctree_lsub; ctree_msub;
               ctree_rsub])
     `ctree_union` [ct_pats "l"; ct_pats "r"]));;

let CTREE_UNION_ROTLR_FO = zx (end_itlist CONJ
  (p3_tabulate
 (REWRITE_CONV[ctree_union_rotlr; ctree_empty; ctree_leaf; ctree_lsub;
               ctree_msub; ctree_rsub;
                             ctree_rotl; ctree_rotr; CTREE_UNION_FO])
     `ctree_union_rotlr` [ct_pats "l"; ct_pats "r"]));;

let ge4 = new_definition
 `ge4 a b c d =
  (gtree_empty a /\ gtree_empty b /\ gtree_empty c /\ gtree_empty d)`;;
let ge3 = new_definition
  `ge3 b c d = (gtree_empty b /\ gtree_empty c /\ gtree_empty d)`;;
let ge2 = new_definition `ge2 c d = (gtree_empty c /\ gtree_empty d)`;;

(* NB: the first-argument patterns use the suffix "0" so that no pattern     *)
(* variable coincides with the other arguments b c d (a shared variable      *)
(* would make the generated match non-linear and fail at run time).          *)
let GE4_FO = end_itlist CONJ
  (p3_tabulate (REWRITE_CONV[ge4; GSYM ge3; gtree_empty]) `ge4`
  [gt_pats "0"; [`b:gtree`]; [`c:gtree`]; [`d:gtree`]]);;
let GE3_FO = end_itlist CONJ
  (p3_tabulate (REWRITE_CONV[ge3; GSYM ge2; gtree_empty]) `ge3`
  [gt_pats "0"; [`c:gtree`]; [`d:gtree`]]);;
let GE2_FO = end_itlist CONJ
  (p3_tabulate (REWRITE_CONV[ge2; gtree_empty]) `ge2`
  [gt_pats "0"; [`d:gtree`]]);;

let GTREE_EMPTY4_FO = end_itlist CONJ
  (prove(`!a b c d. gtree_empty4 (GtreeNode a b c d) = ge4 a b c d`,
         REWRITE_TAC[gtree_empty4; gtree_empty_and; ge4]) :: tl
           (CONJUNCTS gtree_empty4));;

let CTREE_CONS_PAIRS_FO = zx (end_itlist CONJ
  (p3_tabulate (REWRITE_CONV[ctree_cons_pairs; CTREE_EMPTY_NODE_FO])
    `ctree_cons_pairs`
     [map (fun t -> list_mk_comb(`CtreePair`, [t; `t1':ctree`])) (ct_pats "1");
      map (fun t -> list_mk_comb(`CtreePair`, [t; `t2':ctree`])) (ct_pats "2");
      map (fun t -> list_mk_comb(`CtreePair`, [t; `t3':ctree`]))
        (ct_pats "3")]));;

let _ =
  let chk name th bad =
    let n = length (p3_residual bad (CONJUNCTS th)) in
    Printf.printf "FO3 %-22s %4d clauses, residual %d\n%!" name
      (length (CONJUNCTS th)) n;
    if n <> 0 then failwith ("part2_fo3_dev: residual in " ^ name) in
  chk "GTR_SPLIT4_FUSED" GTR_SPLIT4_FUSED
    ["gtr_split_acc";"gtr_cons";"cons_pop"];
  chk "CTR_SPLIT3_FUSED" CTR_SPLIT3_FUSED ["ctr_split_acc";"ctr_cons_pop"];
  chk "CTREE_UNION_FO" CTREE_UNION_FO
 ["ctree_empty";"ctree_leaf";"COND";"ctree_lsub";"ctree_msub";"ctree_rsub";
  "ctree_simple_leaf"];
  chk "CTREE_UNION_ROTLR_FO" CTREE_UNION_ROTLR_FO
 ["ctree_empty";"ctree_leaf";"COND";"ctree_lsub";"ctree_msub";"ctree_rsub";
  "ctree_simple_leaf"];
  chk "GE4_FO" GE4_FO ["gtree_empty"]; chk "GE3_FO" GE3_FO ["gtree_empty"];
  chk "GTREE_EMPTY4_FO" GTREE_EMPTY4_FO ["gtree_empty_and"];;

(* ------------------------------------------------------------------------- *)
(* The third layer.                                                          *)
(* (10) the restriction height as a unary list instead of a numeral: the     *)
(* generated code evaluated `h = 0` (NUM_EQ_CONV, 2.5 us) and `h - 1`        *)
(* (NUM_SUB_CONV, 11 us) plus the COND machinery at EVERY node visit;        *)
(* ctree_restrict_u hs = ctree_restrict (LENGTH hs) dispatches on [] / CONS  *)
(* and on the tree and restriction constructors in one clause. (11) the leaf *)
(* conditionals of gtree_restrict become boolean selectors gl1/gl2 (one step *)
(* instead of 9-18 kernel operations per COND). (12) gtree_empty4 by first-  *)
(* child cases, gtree_cons_pairs testing with ge4 directly.                  *)
(* (14) the decrement table with the leaf counters' constructors included    *)
(* (leaf counters are CtreeLeaf _ or CtreeEmpty; a CtreeNode there would be  *)
(* a run-time "No match" failure, never an unsound result).                  *)
(* ------------------------------------------------------------------------- *)

let ctree_restrict_u = new_definition
 `ctree_restrict_u (hs:bool list) t r = ctree_restrict (LENGTH hs) t r`;;

let ctree_restrict_split_u = new_definition
 `ctree_restrict_split_u hs t1 t2 t3
  (q:ctree_restriction#ctree_restriction#ctree_restriction) =
    ctree_cons_pairs (ctree_restrict_u hs t1 (FST q))
    (ctree_restrict_u hs t2 (FST (SND q)))
                     (ctree_restrict_u hs t3 (SND (SND q)))`;;

let CTREE_RESTRICT_SPLIT_U_P = prove
 (`!hs t1 t2 t3 r1 r2 r3.
     ctree_restrict_split_u hs t1 t2 t3 (r1,r2,r3) =
     ctree_cons_pairs (ctree_restrict_u hs t1 r1) (ctree_restrict_u hs t2 r2)
     (ctree_restrict_u hs t3 r3)`,
  REWRITE_TAC[ctree_restrict_split_u; FST; SND]);;

let CTREE_RESTRICT_U = prove
 (`(!hs t. ctree_restrict_u hs t CtrNil = CtreePair t CtreeEmpty) /\
   (!t1 t2 t3 bs g r. ctree_restrict_u [] (CtreeNode t1 t2 t3)
   (CtrCons bs g r) =
        ctree_leaf_pair_q t1 t2 t3 (ctr_decr3 t1 t2 t3 (CtrCons bs g r))) /\
   (!b hs t1 t2 t3 bs g r. ctree_restrict_u (CONS b hs) (CtreeNode t1 t2 t3)
   (CtrCons bs g r) =
        ctree_restrict_split_u hs t1 t2 t3
        (ctr_split3 (CtrCons bs g r) (CtrNil,CtrNil,CtrNil))) /\
   (!hs lf bs g r. ctree_restrict_u hs (CtreeLeaf lf) (CtrCons bs g r) =
   CtreePair CtreeEmpty CtreeEmpty) /\
   (!hs bs g r. ctree_restrict_u hs CtreeEmpty (CtrCons bs g r) =
   CtreePair CtreeEmpty CtreeEmpty)`,
  REWRITE_TAC[ctree_restrict_split_u; ctree_restrict_u; CTREE_RESTRICT_FO;
              ctr_isnil; ctree_restrict_node;
              LENGTH; NOT_SUC; SUC_SUB1; ctree_restrict_split;
              ctree_empty_pair]);;

let KTC_STEP_FO_U = prove
 (`!h ktc0 ctu gtr gtu.
     ktc_step h ktc0 ctu gtr gtu =
     (if ctree_empty ctu then (ctu, GtreePair gtr gtu)
      else if gtree_empty gtr then (ctu, GtreePair gtr gtu)
      else if gtree_empty gtu then (CtreeEmpty, empty_gtree_pair)
      else ktc_apply ktc0
     (ctree_restrict_u (REPLICATE h T) ctu (CtrCons Bstack0 gtr CtrNil)) gtu)`,
  REWRITE_TAC[KTC_STEP_FO; ctree_restrict_u; LENGTH_REPLICATE]);;
let ktc_step_fo_u_x = zx KTC_STEP_FO_U;;

let GTREE_EMPTY4_FO2 = end_itlist CONJ
  (p3_tabulate
 (REWRITE_CONV[gtree_empty4; gtree_empty_and; gtree_empty; GSYM ge3])
   `gtree_empty4`
     [map (fun a -> list_mk_comb(`GtreeNode`, [a; `b:gtree`; `c:gtree`;
                                               `d:gtree`])) (gt_pats "0")]
   @ tl (CONJUNCTS gtree_empty4));;

let GTREE_CONS_PAIRS_GE = REWRITE_RULE[hd (CONJUNCTS GTREE_EMPTY4_FO)]
  gtree_cons_pairs;;

let gl1 = new_definition
  `gl1 (b:bool) (p1:gtree_pair) p2 = if b then p1 else p2`;;
let gl2 = new_definition
 `gl2 (b0:bool) (b1:bool) (p1:gtree_pair) p2 p3 p4 =
    if b0 then (if b1 then p1 else p2) else (if b1 then p3 else p4)`;;
let GL1_FO =
 prove(`(!p1 p2. gl1 T p1 p2 = p1) /\ (!p1 p2. gl1 F p1 p2 = p2)`
 , REWRITE_TAC[gl1]);;
let GL2_FO = prove
 (`(!p1 p2 p3 p4. gl2 T T p1 p2 p3 p4 = p1) /\
 (!p1 p2 p3 p4. gl2 T F p1 p2 p3 p4 = p2) /\
   (!p1 p2 p3 p4. gl2 F T p1 p2 p3 p4 = p3) /\
   (!p1 p2 p3 p4. gl2 F F p1 p2 p3 p4 = p4)`,
  REWRITE_TAC[gl2]);;
let gtree_restrict_fo3g_x = PURE_REWRITE_RULE[GSYM gl2; GSYM gl1]
  gtree_restrict_fo3_x;;

let cs3 = new_definition
 `cs3 (t0:gtree) b0 b1 (x:ctree_restriction)
  (q:ctree_restriction#ctree_restriction) =
    (x, ctr_cons b0 t0 (FST q), ctr_cons b1 t0 (SND q))`;;
(* pattern variables az bz cz dz: must not coincide with the other arguments *)
(* b0 b1                                                                     *)
let CS3_FO = end_itlist CONJ
  (p3_tabulate (REWRITE_CONV[cs3; CTR_CONS_FO; FST; SND]) `cs3`
     [gt_pats "z"; [`b0:bit_stack`]; [`b1:bit_stack`]; [`x:ctree_restriction`];
      [`(a:ctree_restriction,b:ctree_restriction)`]]);;

let cc2 = new_definition
 `cc2 bs (t2:gtree) (t3:gtree) (r2:ctree_restriction) (r3:ctree_restriction) =
    (ctr_cons bs t2 r2, ctr_cons bs t3 r3)`;;
let CC2_FO = end_itlist CONJ
  (p3_tabulate (REWRITE_CONV[cc2; CTR_CONS_FO]) `cc2`
     [[`bs:bit_stack`]; gt_pats "2"; gt_pats "3"; [`r2:ctree_restriction`];
      [`r3:ctree_restriction`]]);;

let cc2p = new_definition
 `cc2p bs (t2:gtree) (t3:gtree) (r2:ctree_restriction) (r3:ctree_restriction) =
    (ctr_cons_pop bs t2 t3 r2, ctr_cons_pop bs t3 t2 r3)`;;
let CC2P_FO = prove
 (`(!t2 t3 r2 r3. cc2p Bstack0 t2 t3 r2 r3 = (r2,r3)) /\
   (!bs' t2 t3 r2 r3. cc2p (Bpush0 bs') t2 t3 r2 r3 = cc2 bs' t2 t3 r2 r3) /\
   (!bs' t2 t3 r2 r3. cc2p (Bpush1 bs') t2 t3 r2 r3 = cc2 bs' t3 t2 r2 r3)`,
  REWRITE_TAC[cc2p; cc2; ctr_cons_pop]);;

let CTR_SPLIT_ACC_CS = prove
 (`!t0 t1 t2 t3 bs r1 r2 r3.
     ctr_split_acc (GtreeNode t0 t1 t2 t3) bs (r1,r2,r3) =
     cs3 t0 (Bpush0 bs) (Bpush1 bs) (ctr_cons bs t1 r1) (cc2p bs t2 t3 r2 r3)`,
  REWRITE_TAC[CTR_SPLIT_ACC_P; cs3; cc2p; FST; SND]);;
let CTR_SPLIT_ACC_LEAVES = end_itlist CONJ (tl (CONJUNCTS CTR_SPLIT_ACC_P));;

let CTR_SPLIT3_FUSED2 = zx (end_itlist CONJ
  (hd (CONJUNCTS ctr_split3) ::
   p3_tabulate (REWRITE_CONV[ctr_split3; CTR_SPLIT_ACC_CS;
                      CTR_SPLIT_ACC_LEAVES; CTR_CONS_FO; CC2P_FO]) `ctr_split3`
     [map (fun l -> match l with
             [bs;t] -> list_mk_comb(`CtrCons`, [bs; t; `r:ctree_restriction`])
           | _ -> fail())
          (p3_combos [bs_pats;
                      map (fun t1 -> list_mk_comb(`GtreeNode`, [`t0:gtree`; t1;
                                        `t2:gtree`; `t3:gtree`])) (gt_pats "1")
                      @ tl (gt_pats "")]);
      [`(r1:ctree_restriction,r2:ctree_restriction,r3:ctree_restriction)`]]));;

let lf_pats k = [mk_comb(`CtreeLeaf`, mk_var("l"^k,`:ctree`)); `CtreeEmpty`];;
let CTR_DECR3_FUSED2 = end_itlist CONJ
  (hd (CONJUNCTS CTR_DECR3_FO) ::
   p3_tabulate (REWRITE_CONV[CTR_DECR3_FUSED; CD1_FO]) `ctr_decr3`
     [lf_pats "1"; lf_pats "2"; lf_pats "3";
      map (fun l -> match l with
             [bs;t] -> list_mk_comb(`CtrCons`, [bs; t; `r:ctree_restriction`])
           | _ -> fail()) (p3_combos [bs_pats; gt_pats ""])]);;

let _ =
  let chk name th bad =
    let n = length (p3_residual bad (CONJUNCTS th)) in
    Printf.printf "FO3 %-22s %4d clauses, residual %d\n%!" name
      (length (CONJUNCTS th)) n;
    if n <> 0 then failwith ("part2_fo3_dev: residual in " ^ name) in
  chk "CTREE_RESTRICT_U" CTREE_RESTRICT_U
    ["ctree_restrict";"ctr_isnil";"COND";"ctree_empty_pair"];
  chk "GTREE_EMPTY4_FO2" GTREE_EMPTY4_FO2 ["gtree_empty_and"];
  chk "gtree_restrict_fo3g_x" gtree_restrict_fo3g_x ["COND";"gtr_isnil"];
  chk "CS3_FO" CS3_FO ["ctr_cons";"FST";"SND"];
  chk "CC2_FO" CC2_FO ["ctr_cons"];
  chk "CTR_SPLIT3_FUSED2" CTR_SPLIT3_FUSED2
    ["ctr_split_acc";"ctr_cons_pop";"cc2p";"ctr_cons"];
  chk "CTR_DECR3_FUSED2" CTR_DECR3_FUSED2 ["cd1";"ctree_decr"];;

(* ------------------------------------------------------------------------- *)
(* The fourth layer: (15) the chromogram match tests gtr_match0..3 by        *)
(* constructor cases of the list                                             *)
(* element (the ctree_leaf tests and the disjunctions resolved at tabulation *)
(* time; one step per list element, still short-circuiting on the first      *)
(* hit).                                                                     *)
(* ------------------------------------------------------------------------- *)

let gm_conv =
  REWRITE_CONV[GTR_MATCH0_FO; GTR_MATCH1_FO; GTR_MATCH2_FO; GTR_MATCH3_FO;
               gtr_match0_t; gtr_match1_t;
               gtr_match2_t; gtr_match3_t; gtr_match2_bs; ctree_leaf];;
let node_pats k2 k3 =
  map (fun l -> match l with [t2;t3] -> list_mk_comb(`CtreeNode`, [`t1:ctree`;
                                                        t2; t3]) | _ -> fail())
      (p3_combos [ct_pats k2; ct_pats k3]);;
let cons_pats bss ts =
  map (fun l -> match l with [bs;t] -> list_mk_comb(`GtrCons`, [bs; t;
                                        `r':gtree_restriction`]) | _ -> fail())
      (p3_combos [bss; ts]);;
let GTR_MATCH0_FUSED = end_itlist CONJ
  (hd (CONJUNCTS GTR_MATCH0_FO) ::
   p3_tabulate gm_conv `gtr_match0`
 [cons_pats [`bs:bit_stack`
 ] (node_pats "2" "3" @ [`CtreeLeaf lf`; `CtreeEmpty`])]);;
let GTR_MATCH1_FUSED = end_itlist CONJ
  (hd (CONJUNCTS GTR_MATCH1_FO) ::
   p3_tabulate gm_conv `gtr_match1`
     [cons_pats [`bs:bit_stack`]
        (map (fun t1 -> list_mk_comb(`CtreeNode`, [t1; `t2:ctree`;
              `t3:ctree`])) (ct_pats "1") @ [`CtreeLeaf lf`; `CtreeEmpty`])]);;
let GTR_MATCH2_FUSED = end_itlist CONJ
  (hd (CONJUNCTS GTR_MATCH2_FO) ::
   p3_tabulate gm_conv `gtr_match2`
   [cons_pats bs_pats (node_pats "2" "3" @ [`CtreeLeaf lf`; `CtreeEmpty`])]);;
let GTR_MATCH3_FUSED = end_itlist CONJ
  (hd (CONJUNCTS GTR_MATCH3_FO) ::
   p3_tabulate gm_conv `gtr_match3`
   [cons_pats bs_pats (node_pats "2" "3" @ [`CtreeLeaf lf`; `CtreeEmpty`])]);;

let _ =
  let chk name th bad =
    let n = length (p3_residual bad (CONJUNCTS th)) in
    Printf.printf "FO3 %-22s %4d clauses, residual %d\n%!" name
      (length (CONJUNCTS th)) n;
    if n <> 0 then failwith ("part2_fo3_dev: residual in " ^ name) in
  chk "GTR_MATCH0_FUSED" GTR_MATCH0_FUSED ["ctree_leaf";"gtr_match0_t";"\\/"];
  chk "GTR_MATCH1_FUSED" GTR_MATCH1_FUSED ["ctree_leaf";"gtr_match1_t";"\\/"];
  chk "GTR_MATCH2_FUSED" GTR_MATCH2_FUSED
    ["ctree_leaf";"gtr_match2_t";"gtr_match2_bs";"\\/"];
  chk "GTR_MATCH3_FUSED" GTR_MATCH3_FUSED
    ["ctree_leaf";"gtr_match3_t";"gtr_match2_bs";"\\/"];;

(* ------------------------------------------------------------------------- *)
(* The database (all four layers).  The superseded fused sets                *)
(* (CTR_DECR3_FUSED, gtree_restrict_fo3_x, CTREE_RESTRICT_FO3,               *)
(* CTR_SPLIT3_FUSED, GTREE_EMPTY4_FO) are not registered: one clause set per *)
(* constant.                                                                 *)
(* ------------------------------------------------------------------------- *)

let p1_fo3_drop =
  ["GTR_SPLIT_ACC_P"; "CTR_SPLIT_ACC_P"; "CTR_DECR3_FO"; "CDEC1_RULES";
   "CDEC2_RULES"; "CDEC3_RULES";
   "ctree_cons"; "ctree_empty_node"; "ctree_if_e"; "ctree_leaf_pair";
   "gtree_empty_and";
   "gtree_restrict_fo_x"; "CTREE_RESTRICT_FO"; "ctree_restrict_node_x";
   "CTREE_RESTRICT_SPLIT_P"; "ktc_step_fo_x";
   "gtr_split4"; "ctr_split3"; "ctree_union_x"; "ctree_union_rotlr_x";
   "gtree_empty4"; "ctree_cons_pairs";
   "GTR_MATCH0_FO"; "GTR_MATCH1_FO"; "GTR_MATCH2_FO"; "GTR_MATCH3_FO"];;

let p1_fo3_thms () =
  ["GTR_SPLIT_ACC_FUSED",GTR_SPLIT_ACC_FUSED,[];
   "CTR_SPLIT_ACC_FUSED",CTR_SPLIT_ACC_FUSED,[];
   "CD1_FO",CD1_FO,[]; "CTREE_CONS_FO",CTREE_CONS_FO,[];
   "CTREE_EMPTY_NODE_FO",CTREE_EMPTY_NODE_FO,[];
   "CTREE_IF_E_FO",CTREE_IF_E_FO,[];
   "CTREE_LEAF_PAIR_FUSED",CTREE_LEAF_PAIR_FUSED,[];
   "GTREE_EMPTY_AND_FO",GTREE_EMPTY_AND_FO,[];
   "GTR_SPLIT4_FUSED",GTR_SPLIT4_FUSED,[]; "CTREE_UNION_FO",CTREE_UNION_FO,[];
   "CTREE_UNION_ROTLR_FO",CTREE_UNION_ROTLR_FO,[]; "GE4_FO",GE4_FO,[];
   "GE3_FO",GE3_FO,[]; "GE2_FO",GE2_FO,[];
   "CTREE_CONS_PAIRS_FO",CTREE_CONS_PAIRS_FO,[];
   "CTREE_RESTRICT_U",CTREE_RESTRICT_U,[];
   "CTREE_RESTRICT_SPLIT_U_P",CTREE_RESTRICT_SPLIT_U_P,[];
   "ktc_step_fo_u_x",ktc_step_fo_u_x,[];
   "GTREE_EMPTY4_FO2",GTREE_EMPTY4_FO2,[];
   "GTREE_CONS_PAIRS_GE",GTREE_CONS_PAIRS_GE,[]; "GL1_FO",GL1_FO,[];
   "GL2_FO",GL2_FO,[];
   "gtree_restrict_fo3g_x",gtree_restrict_fo3g_x,[]; "CS3_FO",CS3_FO,[];
   "CC2_FO",CC2_FO,[];
   "CTR_SPLIT3_FUSED2",CTR_SPLIT3_FUSED2,[];
   "CTR_DECR3_FUSED2",CTR_DECR3_FUSED2,[];
   "GTR_MATCH0_FUSED",GTR_MATCH0_FUSED,[];
   "GTR_MATCH1_FUSED",GTR_MATCH1_FUSED,[];
   "GTR_MATCH2_FUSED",GTR_MATCH2_FUSED,[];
   "GTR_MATCH3_FUSED",GTR_MATCH3_FUSED,[]];;

let p1_kempe_thms_fo3 () =
  filter (fun (n,_,_) -> not (mem n p1_fo3_drop)) (p1_kempe_thms_fo2()) @
    p1_fo3_thms();;

let p1_build_db_fo3 extra =
  let db = default_db "p2fo3" in
  set_rule db `cprsize` ~name:"conv_cprsize";
  ignore(add_thms db (p1_kempe_thms_fo3() @ extra)); db;;

