(* ========================================================================= *)
(* 4CT/quiztree_eval.ml                                                      *)
(*                                                                           *)
(* The value of the quiz tree the_quiz_tree (present.ml) computed by         *)
(* call-by-value evaluation (compute_fast.ml): numeral-driven forms of the   *)
(* cfquiz definitions, the compset cfquiz_compset for cfquiz and             *)
(* the_quiz_tree, and THE_QUIZ_TREE_VALUE, the explicit tree (qzt_size 3361, *)
(* Coq's leaf count), which redpart_eval.ml and present_eval.ml evaluate     *)
(* against.                                                                  *)
(* ========================================================================= *)

needs "4CT/compute_fast.ml";;
needs "4CT/present.ml";;

let TAKE_LIST_NUM = prove
 (`!n (l:A list). take_list n l =
     if n = 0 then [] else if l = [] then []
     else CONS (HD l) (take_list (n - 1) (TL l))`,
  INDUCT_TAC THEN REWRITE_TAC[take_list; NOT_SUC; SUC_SUB1]);;

let DROP_LIST_NUM = prove
 (`!n (l:A list). drop_list n l = if n = 0 then l else if l = [] then []
 else drop_list (n - 1) (TL l)`,
  INDUCT_TAC THEN REWRITE_TAC[drop_list; NOT_SUC; SUC_SUB1]);;

let MASK_PRED1_FROM_NUM_ADD1 = prove
 (`!n j i. mask_pred1_from j i n = if n = 0 then []
 else CONS (j = i) (mask_pred1_from (j + 1) i (n - 1))`,
  GEN_TAC THEN STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
  REWRITE_TAC[mask_pred1_from; NOT_SUC; SUC_SUB1; ADD1]);;

let CPRADIUS2_NUM = prove
 (`!cp i. cpradius2 cp i =
      if i = 0 then F else
      (let cm0 = cfmask1 cp (i - 1) in
       let mk1 = SND (cpadj cm0 cp) in
       let mk2 = SND (cpadj (FST cm0, mk1) cp) in
       if ALL (\b. b) mk2 then T else cpradius2 cp (i - 1))`,
  GEN_TAC THEN GEN_TAC THEN STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THEN
  REWRITE_TAC[cpradius2; NOT_SUC; SUC_SUB1]);;

(* cpadj's CpR clause mentions the recursive call twice (FST .. and SND ..): *)
(* CBV would evaluate it twice per R step => 2^(#R steps) blow-up (cf633:    *)
(* 158 s). Let-bound form: linear (cf633: 0.37 s).                           *)
let CPADJ_CPR_LET = prove
 (`!cm n cp'. cpadj cm (CONS (CpR n) cp') =
      let res = cpadj (rotr_list n (FST cm), SND cm) cp' in
      (rot_list n (FST res), SND res)`,
  REWRITE_TAC[cpadj; LET_DEF; LET_END_DEF]);;

(* The 633 configuration definitions cf001..cf633                            *)
let cf_definitions () =
  filter (fun th -> try let s = fst(dest_const(lhs(concl th))) in
                        String.length s = 5 && String.sub s 0 2 = "cf" &&
                        (try ignore(int_of_string(String.sub s 2 3));
                         true with _ -> false)
                    with _ -> false) (definitions());;

(* The compset for cfquiz / the_quiz_tree.                                   *)
let cfquiz_compset () =
  let cs = Compute.bool_compset() in
  let cpadj_cls = CONJUNCTS cpadj in
  Compute.set_skip cs `COND:bool->A->A->A` (Some 1);
  List.iter (fun c -> Compute.add_conv c cs)
    [(`SUC`, 1, NUM_SUC_CONV); (`(+):num->num->num`, 2, NUM_ADD_CONV);
     (`(-):num->num->num`, 2, NUM_SUB_CONV);
     (`(<):num->num->bool`, 2, NUM_LT_CONV);
     (`(<=):num->num->bool`, 2, NUM_LE_CONV);
     (`(=):num->num->bool`, 2, NUM_EQ_CONV); (`cprsize`, 1, cprsize_conv)];
  Compute.add_thms
    (both_dirs (distinctness "cpstep") @ both_dirs (distinctness "question") @
                    both_dirs (distinctness "qarity") @
                    [injectivity "cpstep"; injectivity "question"; REFL_CLAUSE;
                     FST; SND; LET_END_DEF;
                     cfprog; CPKSIZE_CLAUSES]) cs;
  Compute.add_thms
 [cfquiz; cfquiz_rec; cfquiz_Y; cfquiz_H; rqs_Y; rqs_H; small_qarity;
  bad_small_arity;
                    large_qarity; bad_ring_arity; isQaskL; isQaskR; isCpR;
                    cpr_arg; noquiz; nat_of_qarity;
                    qra; qrb; rot_list; rotr_list; TAKE_LIST_NUM;
                    DROP_LIST_NUM; REPLICATE_NUM; LENGTH; HD; TL;
                    APPEND; ALL; NOT_CONS_NIL; CPRADIUS2_NUM; cfmask1;
                    mask_pred1; MASK_PRED1_FROM_NUM_ADD1;
                    el 0 cpadj_cls; CPADJ_CPR_LET; el 2 cpadj_cls;
                    el 3 cpadj_cls; EL_NUM] cs;
  Compute.add_thms
 [store_cf_qz; store_qz; store_qz_aux; normq; isQaskLR; qLR_l; qLR_r;
  qzt_put; qzt_put3;
                    qzt_put3rot; qzt_put1; qzt_empty; isQztHubNode; flipqz;
                    flipq; cfquiz_tree; cfquiz_tree_rec;
                    ZIP; the_quiz_tree; qzt_size] cs;
  Compute.add_thms (cf_definitions()) cs;
  Compute.add_thms [the_configs; the_configs_sym] cs;
  cs;;

(* ------------------------------------------------------------------------- *)
(* The value of the_quiz_tree (Coq quiztree.v / present.v the_quiz_tree):    *)
(* computed at load time by CBV, qzt_size = 3361 = Coq's leaf count.         *)
(* ------------------------------------------------------------------------- *)

let the_cfquiz_compset = cfquiz_compset();;

let THE_QUIZ_TREE_VALUE =
  let t0 = Sys.time() in
  let th = Compute.CBV_CONV the_cfquiz_compset `the_quiz_tree` in
  (Printf.printf "QUIZTREE_EVAL: the_quiz_tree evaluated in %.1f s\n%!"
    (Sys.time() -. t0); th);;

(* The compset for later redpart / hubcap evaluations: the_quiz_tree |-> its *)
(* value                                                                     *)
Compute.add_thms [THE_QUIZ_TREE_VALUE] the_cfquiz_compset;;

