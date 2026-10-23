(* ========================================================================= *)
(* 4CT/cfquiz.ml                                                             *)
(*                                                                           *)
(* cfquiz.v: the quiz of a configuration (cfquiz, with the correctness       *)
(* theorem CFQUIZ_MAIN, Coq cfquizP).  The quiz testing for the occurrence   *)
(* of a configuration is compiled by walking the construction program        *)
(* backwards, keeping for each ring dart a question rooted at its node that  *)
(* covers the kernel faces already detached; the two final questions form    *)
(* the quiz.  Also cpradius2 (the kernel has radius at most 2).              *)
(*                                                                           *)
(* A configuration is a pair (cpstep)list # (num)list (cfprog = FST); the    *)
(* carrier is num and Coq's injection injcp is the identity, so the ring     *)
(* question "node (ic x)" is node_map in the full map.  A ring_question is a *)
(* triple bool # num # question (kernel flag, outer arity, question).  The   *)
(* invariant rqs_proper is stated for the full map G0 and the dart set D and *)
(* ring r of the current sub-map only: the outer arity is measured as        *)
(* subarity G0 D x, the number of sub-map darts in the G0-face of x (the     *)
(* arity in the sub-map, by the cface agreement injcp_ctx), so the Y and H   *)
(* steps never compute arities in the intermediate maps.  Both steps are     *)
(* instances of the transfer lemma RQS_PROPER_STEP.                          *)
(* ========================================================================= *)

needs "4CT/general.ml";;
needs "4CT/geometry.ml";;
needs "4CT/coloring.ml";;
needs "4CT/jordan.ml";;
needs "4CT/patch.ml";;
needs "4CT/snip.ml";;
needs "4CT/revsnip.ml";;
needs "4CT/embed_prelim.ml";;
needs "4CT/cfmap.ml";;
needs "4CT/cpcolor_correct.ml";;
needs "4CT/cfcontract.ml";;
needs "4CT/quiz.ml";;
needs "4CT/cube.ml";;            (* CFACE_INV_FACE *)

let ADJP = prove
 (`!(H:(A)hypermap) x y.
     adj H x y <=> ?z. cface H x z /\ cface H (edge_map H z) y`,
  REWRITE_TAC[adj; rlink; cface]);;

let small_qarity = new_definition
 `small_qarity a =
    if a = 3 then Qa5 else if a = 4 then Qa6 else if a = 5 then Qa7 else
    if a = 6 then Qa8 else if a = 7 then Qa10 else Qa9`;;

let bad_small_arity = new_recursive_definition qarity_RECURSION
 `(bad_small_arity Qa5 = F) /\ (bad_small_arity Qa6 = F) /\
  (bad_small_arity Qa7 = F) /\ (bad_small_arity Qa8 = F) /\
  (bad_small_arity Qa9 = T) /\ (bad_small_arity Qa10 = T) /\
  (bad_small_arity Qa11 = T)`;;

let large_qarity = new_definition
 `large_qarity a =
    if a = 7 then Qa9 else if a = 8 then Qa10 else if a = 9 then Qa11
    else small_qarity a`;;

let bad_ring_arity = new_definition
 `bad_ring_arity a <=> a = 0 \/ 5 <= a`;;

let isQaskL = new_recursive_definition question_RECURSION
 `(isQaskL Qask0 = F) /\ (isQaskL (Qask1 qa) = F) /\
  (isQaskL (QaskL qa ql) = T) /\ (isQaskL (QaskR qa qr) = F) /\
  (isQaskL (QaskLR qa ql qr) = F) /\ (isQaskL (QaskLL qa qll) = F) /\
  (isQaskL (QaskRR qa qrr) = F)`;;

let isCpR = new_recursive_definition cpstep_RECURSION
 `(isCpR (CpR n) = T) /\ (isCpR CpRr = F) /\ (isCpR CpY = F) /\
  (isCpR CpH = F) /\
  (isCpR CpU = F) /\ (isCpR CpK = F) /\ (isCpR CpA = F)`;;

let cpr_arg = new_recursive_definition cpstep_RECURSION
 `(cpr_arg (CpR n) = n) /\ (cpr_arg CpRr = 0) /\ (cpr_arg CpY = 0) /\
  (cpr_arg CpH = 0) /\
  (cpr_arg CpU = 0) /\ (cpr_arg CpK = 0) /\ (cpr_arg CpA = 0)`;;

let noquiz = new_definition `noquiz = Quiz Qask0 Qask0`;;

let rqs_Y = new_definition
 `rqs_Y (rq1:bool#num#question) (rq3:bool#num#question)
        (qs:(bool#num#question)list) (q1':question) =
    CONS (FST rq1, SUC (FST (SND rq1)), q1')
         (CONS (FST rq3, SUC (FST (SND rq3)), SND (SND rq3)) qs)`;;

let cfquiz_Y = new_definition
 `cfquiz_Y (rq1:bool#num#question) (rq2:bool#num#question)
           (rqs':question->(bool#num#question)list) =
    let q1 = SND (SND rq1) and k2 = FST rq2 and a2 = FST (SND rq2)
    and q2 = SND (SND rq2) in
    if k2 then
      (let qa2 = small_qarity a2 in
       if bad_small_arity qa2 then [] else
       rqs' (if q1 = Qask0 then (if q2 = Qask0 then Qask1 qa2 else
                                 QaskL qa2 q2)
             else (if q2 = Qask0 then QaskR qa2 q1 else QaskLR qa2 q2 q1)))
    else
      (if bad_ring_arity a2 then [] else
       if q1 = Qask0 /\ q2 = Qask0 then rqs' Qask0
       else if isQaskR q1 /\ q2 = Qask0 then rqs' (QaskRR (qra q1) (qrb q1))
       else if q1 = Qask0 /\ isQaskL q2 then rqs' (QaskLL (qra q2) (qrb q2))
       else [])`;;

let rqs_H = new_definition
 `rqs_H (rq1:bool#num#question) (rq3:bool#num#question)
        (qs:(bool#num#question)list) (q1':question) (q2':question) =
    CONS (FST rq1, SUC (FST (SND rq1)), q1')
         (CONS (T, 1, q2')
               (CONS (FST rq3, SUC (FST (SND rq3)), SND (SND rq3)) qs))`;;

let cfquiz_H = new_definition
 `cfquiz_H (rq1:bool#num#question) (rq2:bool#num#question)
           (rqs':question->question->(bool#num#question)list) =
    let k1 = FST rq1 and q1 = SND (SND rq1) and
        k2 = FST rq2 and a2 = FST (SND rq2) and q2 = SND (SND rq2) in
    if k2 then
      (let qa2 = small_qarity (SUC a2) in
       if bad_small_arity qa2 then [] else
       if q1 = Qask0 /\ q2 = Qask0
       then (if k1 then rqs' (Qask1 qa2) q2 else rqs' q1 (Qask1 qa2))
       else if q1 = Qask0 then rqs' q1 (QaskL qa2 q2)
       else if q2 = Qask0 then rqs' (QaskR qa2 q1) q2
       else [])
    else
      (if bad_ring_arity (SUC a2) then [] else
       if q1 = Qask0 /\ q2 = Qask0 then rqs' q1 q2 else [])`;;

let cfquiz_rec = new_recursive_definition list_RECURSION
 `(cfquiz_rec [] (qs:(bool#num#question)list) =
     (if LENGTH qs < 2 then noquiz else
      let rq1 = HD qs and rq2 = HD (TL qs) in
      let k1 = FST rq1 and a1 = FST (SND rq1) and q1 = SND (SND rq1) and
          k2 = FST rq2 and a2 = FST (SND rq2) and q2 = SND (SND rq2) in
      if ~(k1 /\ k2) then noquiz else
      let qa1 = large_qarity (a1 - 1) and qa2 = small_qarity (a2 - 1) in
      if ~(nat_of_qarity qa1 = a1 + 1) \/ bad_small_arity qa2 then noquiz
      else Quiz (QaskR qa1 q2) (QaskR qa2 q1))) /\
  (cfquiz_rec (CONS s cp') qs =
     (if LENGTH qs < 3 then noquiz else
      let rq1 = HD qs and rq2 = HD (TL qs) and rq3 = HD (TL (TL qs))
      and qs' = TL (TL (TL qs)) in
      if isCpR s then cfquiz_rec cp' (rotr_list (cpr_arg s) qs)
      else if s = CpY
      then cfquiz_rec cp' (cfquiz_Y rq1 rq2 (rqs_Y rq1 rq3 qs'))
      else if s = CpH
      then cfquiz_rec cp' (cfquiz_H rq1 rq2 (rqs_H rq1 rq3 qs'))
      else noquiz))`;;

let cpradius2 = new_recursive_definition num_RECURSION
 `(cpradius2 (cp:(cpstep)list) 0 = F) /\
  (cpradius2 cp (SUC i) =
     (let cm0 = cfmask1 cp i in
      let mk1 = SND (cpadj cm0 cp) in
      let mk2 = SND (cpadj (FST cm0, mk1) cp) in
      if ALL (\b. b) mk2 then T else cpradius2 cp i))`;;

let cfquiz = new_definition
 `cfquiz (cf:(cpstep)list#(num)list) =
    let cp = cfprog cf in
    if cpradius2 cp (cpksize cp)
    then cfquiz_rec cp (REPLICATE (cprsize cp) (F, 0, Qask0))
    else noquiz`;;

let radius2_kernel = new_definition
 `radius2_kernel (Gc:(A)hypermap) (rc:(A)list) <=>
    ?x0. x0 IN kernel Gc rc /\
         (!w. w IN kernel Gc rc
              ==> ?w1 w2. cface Gc x0 w1 /\ cface Gc w w2 /\
                          edge_map Gc w1 IN kernel Gc rc /\
                          cface Gc (edge_map Gc w1) (edge_map Gc w2))`;;

(* The number of darts of the sub-map D in the G0-face of x.                 *)
let subarity = new_definition
 `subarity (G0:(num)hypermap) (D:num->bool) x =
    CARD {z | z IN D /\ cface G0 x z}`;;

let rqs_fit = define
 `(rqs_fit (G0:(num)hypermap) (D:num->bool) [] ([]:(num)list) <=> T) /\
  (rqs_fit G0 D [] (CONS (x:num) p) <=> F) /\
  (rqs_fit G0 D (CONS (rq:bool#num#question) qs) [] <=> F) /\
  (rqs_fit G0 D (CONS rq qs) (CONS x p) <=>
     arity G0 x = FST(SND rq) + subarity G0 D x /\
     fitq G0 (node_map G0 x) (SND(SND rq)) /\ rqs_fit G0 D qs p)`;;

let rqs_walk = define
 `(rqs_walk (G0:(num)hypermap) (CONS (rq:bool#num#question) qs)
            (CONS (u:num) p) =
     APPEND (if FST rq then [u] else [])
            (APPEND (walkq (SND(SND rq)) G0 (node_map G0 u))
                    (rqs_walk G0 qs p))) /\
  (rqs_walk G0 [] (p:(num)list) = []) /\
  (rqs_walk G0 (CONS rq qs) [] = [])`;;

let rqs_proper = new_definition
 `rqs_proper (G0:(num)hypermap) (x00:num) (D:num->bool) (r:(num)list)
             (qs:(bool#num#question)list) <=>
    rqs_fit G0 D qs r /\
    (!u. MEM u (cpring G0 x00) /\ ~(u IN D) /\ ~fband G0 r u
         ==> good_ring_arity G0 u) /\
    face_simple G0 (APPEND (rqs_walk G0 qs r) (cpring G0 x00)) /\
    (!u. u IN dart G0
         ==> (fband G0 (APPEND (rqs_walk G0 qs r) (cpring G0 x00)) u <=>
              ~(u IN D) \/ fband G0 r u))`;;
let ISQUIZR_NOQUIZ = prove
 (`~isQuizR noquiz`,
  REWRITE_TAC[noquiz; isQuizR; isQaskR]);;
let CFQUIZ_REC_CONS = prove
 (`!s cp' qs. cfquiz_rec (CONS s cp') qs =
     (if LENGTH qs < 3 then noquiz else
      if isCpR s then cfquiz_rec cp' (rotr_list (cpr_arg s) qs)
      else if s = CpY
      then cfquiz_rec cp'
             (cfquiz_Y (HD qs) (HD (TL qs))
                       (rqs_Y (HD qs) (HD (TL (TL qs))) (TL (TL (TL qs)))))
      else if s = CpH
      then cfquiz_rec cp'
             (cfquiz_H (HD qs) (HD (TL qs))
                       (rqs_H (HD qs) (HD (TL (TL qs))) (TL (TL (TL qs)))))
      else noquiz)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cfquiz_rec] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN REFL_TAC);;
let CFQUIZ_REC_NIL_NOTR = prove
 (`!cp. ~isQuizR (cfquiz_rec cp [])`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[cfquiz_rec; CFQUIZ_REC_CONS; LENGTH] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ARITH_RULE `0 < 2 /\ 0 < 3`; ISQUIZR_NOQUIZ]);;
let CFQUIZ_UNFOLD = prove
 (`!cf. isQuizR (cfquiz cf)
        ==> cpradius2 (cfprog cf) (cpksize (cfprog cf)) /\
            cfquiz cf = cfquiz_rec (cfprog cf)
                          (REPLICATE (cprsize (cfprog cf)) (F,0,Qask0))`,
  GEN_TAC THEN REWRITE_TAC[cfquiz] THEN CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ISQUIZR_NOQUIZ]);;
let CFQUIZ_Y_CASES = prove
 (`!rq1 rq2 f. cfquiz_Y rq1 rq2 f = [] \/ ?q. cfquiz_Y rq1 rq2 f = f q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cfquiz_Y] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;
let CFQUIZ_H_CASES = prove
 (`!rq1 rq2 f. cfquiz_H rq1 rq2 f = [] \/
               ?q1 q2. cfquiz_H rq1 rq2 f = f q1 q2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cfquiz_H] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;
let LENGTH_RQS_Y = prove
 (`!rq1 rq3 qs q. LENGTH (rqs_Y rq1 rq3 qs q) = LENGTH qs + 2`,
  REWRITE_TAC[rqs_Y; LENGTH] THEN ARITH_TAC);;
let LENGTH_RQS_H = prove
 (`!rq1 rq3 qs q1 q2. LENGTH (rqs_H rq1 rq3 qs q1 q2) = LENGTH qs + 3`,
  REWRITE_TAC[rqs_H; LENGTH] THEN ARITH_TAC);;
let CFQUIZ_REC_CONFIG_STEPS = prove
 (`!cp qs. isQuizR (cfquiz_rec cp qs) ==> ALL config_step cp`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL] THEN GEN_TAC THEN
  REWRITE_TAC[CFQUIZ_REC_CONS] THEN REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[ISQUIZR_NOQUIZ] THEN DISCH_TAC THEN
  (CONJ_TAC THENL [POP_ASSUM(K ALL_TAC) THEN REPEAT(POP_ASSUM MP_TAC) THEN
                   STRUCT_CASES_TAC(ISPEC `h:cpstep` (cases "cpstep")) THEN
                   REWRITE_TAC[isCpR; config_step; distinctness "cpstep"];
                   ASM_MESON_TAC[]]));;
let CONFIG_STEPS_CUBIC = prove
 (`!cp. ALL config_step cp ==> cubic_prog cp`,
  REWRITE_TAC[cubic_prog] THEN GEN_TAC THEN MATCH_MP_TAC MONO_ALL THEN
  REWRITE_TAC[CONFIG_STEP_CASES; CUBIC_STEP_CASES] THEN MESON_TAC[]);;
let CFQUIZ_REC_CONFIG_PROG = prove
 (`!cp qs. isQuizR (cfquiz_rec cp qs) /\ LENGTH qs = cprsize cp
           ==> cp = [] \/ config_prog cp`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[] THEN
  X_GEN_TAC `qs:(bool#num#question)list` THEN
  REWRITE_TAC[CFQUIZ_REC_CONS; CONFIG_PROG_CONS_CASES; NOT_CONS_NIL] THEN
  COND_CASES_TAC THEN REWRITE_TAC[ISQUIZR_NOQUIZ] THEN
  STRUCT_CASES_TAC(ISPEC `h:cpstep` (cases "cpstep")) THEN
  REWRITE_TAC[isCpR; cpr_arg; distinctness "cpstep"; injectivity "cpstep";
              ISQUIZR_NOQUIZ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN ASSUME_TAC(MATCH_MP
    CONFIG_STEPS_CUBIC (MATCH_MP CFQUIZ_REC_CONFIG_STEPS th))) THEN
  MP_TAC(ISPEC `qs:(bool#num#question)list` LENGTH_TL3) THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC]) THENL
   [MP_TAC(SPECL [`a:num`; `t:(cpstep)list`] CPRSIZE_CONS_R) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
                  `rotr_list a (qs:(bool#num#question)list)`) THEN
    ASM_REWRITE_TAC[LENGTH_ROTR_LIST] THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC) THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[CPRSIZE_NIL]) THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN MESON_TAC[]];
    MP_TAC(ISPECL [`HD (qs:(bool#num#question)list)`;
                   `HD (TL (qs:(bool#num#question)list))`;
                   `rqs_Y (HD qs) (HD (TL (TL qs)))
                    (TL (TL (TL (qs:(bool#num#question)list))))`]
           CFQUIZ_Y_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
               (X_CHOOSE_THEN `q:question` SUBST_ALL_TAC)) THENL
     [ASM_MESON_TAC[CFQUIZ_REC_NIL_NOTR]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `rqs_Y (HD qs) (HD (TL (TL qs)))
                                 (TL (TL (TL (qs:(bool#num#question)list))))
                                 q`) THEN
    ASM_REWRITE_TAC[LENGTH_RQS_Y] THEN
    MP_TAC(SPEC `t:(cpstep)list` CPRSIZE_CONS_Y) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ANTS_TAC THENL
     [ASM_ARITH_TAC; SIMP_TAC[]];
    MP_TAC(ISPECL [`HD (qs:(bool#num#question)list)`;
                   `HD (TL (qs:(bool#num#question)list))`;
                   `rqs_H (HD qs) (HD (TL (TL qs)))
                    (TL (TL (TL (qs:(bool#num#question)list))))`]
           CFQUIZ_H_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `q1:question`
                                               (X_CHOOSE_THEN `q2:question`
                                                SUBST_ALL_TAC))) THENL
     [ASM_MESON_TAC[CFQUIZ_REC_NIL_NOTR]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `rqs_H (HD qs) (HD (TL (TL qs)))
                                 (TL (TL (TL (qs:(bool#num#question)list)))) q1
                                 q2`) THEN
    ASM_REWRITE_TAC[LENGTH_RQS_H] THEN
    MP_TAC(SPEC `t:(cpstep)list` CPRSIZE_CONS_H) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[CPMAP_PROPER]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ANTS_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (fun th -> REWRITE_TAC[th])) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[CPRSIZE_NIL]) THEN ASM_ARITH_TAC]);;
let CFQUIZ_REC_NIL_INIT = prove
 (`!n. ~isQuizR (cfquiz_rec [] (REPLICATE n (F,0,Qask0)))`,
  GEN_TAC THEN REWRITE_TAC[cfquiz_rec] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
  REWRITE_TAC[REPLICATE; HD; TL; LENGTH; ARITH_RULE `0 < 2`; COND_ID;
              ISQUIZR_NOQUIZ]);;
let CFQUIZ_CONFIG_PROG = prove
 (`!cf. isQuizR (cfquiz cf) ==> config_prog (cfprog cf)`,
  GEN_TAC THEN
  DISCH_THEN(fun th -> MP_TAC th THEN
             STRIP_ASSUME_TAC(MATCH_MP CFQUIZ_UNFOLD th)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`cfprog cf`; `REPLICATE (cprsize (cfprog cf)) (F,0,Qask0)`]
         CFQUIZ_REC_CONFIG_PROG) THEN
  ASM_REWRITE_TAC[LENGTH_REPLICATE] THEN ASM_MESON_TAC[CFQUIZ_REC_NIL_INIT]);;
let CPRING_REVERSE_NODE_CYCLE = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> list_cycle (\a b. node_map H a = b) (REVERSE (cpring H x0))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cpring; REVERSE_REVERSE] THEN
  REWRITE_TAC[list_cycle; orbit_list; NOT_CONS_NIL; list_path] THEN
  SUBGOAL_THEN `node_map H (node_map H (x0:num)) IN dart H` ASSUME_TAC THENL
   [ASM_MESON_TAC[NODE_MAP_PERMUTES; PERMUTES_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `0 < orbit_size (node_map H) (node_map H (node_map H (x0:num)))`
    ASSUME_TAC THENL
   [ASM_MESON_TAC[ORBIT_SIZE_POS; FINITE_DART; NODE_MAP_PERMUTES];
    ALL_TAC] THEN
  REWRITE_TAC[LIST_PATH_ITERLIST_FUN] THEN
  MP_TAC(ISPECL
         [`node_map (H:(num)hypermap)`; `node_map H (node_map H (x0:num))`]
         LAST_ORBIT_LIST) THEN
  ASM_REWRITE_TAC[orbit_list] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM(CONJUNCT2 ITER)] THEN
  SUBGOAL_THEN `SUC (orbit_size (node_map H) (node_map H (node_map H (x0:num)))
                - 1) = orbit_size (node_map H) (node_map H (node_map H x0))`
    SUBST1_TAC THENL
   [ASM_ARITH_TAC;
    MATCH_MP_TAC ITER_ORBIT_SIZE THEN EXISTS_TAC `dart(H:(num)hypermap)` THEN
    ASM_REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES]]);;
let CFRING_NODE_SCYCLE = prove
 (`!cf. isQuizR (cfquiz cf)
        ==> scycle (FST (cfmap cf)) (\a b. node_map (FST (cfmap cf)) a = b)
                   (cfring cf) /\
            PAIRWISE (\a b. ~(a = b)) (cfring cf) /\
            ALL (\w. w IN dart (FST (cfmap cf))) (cfring cf)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CFQUIZ_CONFIG_PROG) THEN
  REWRITE_TAC[cfring; cfmap] THEN DISCH_TAC THEN
  MP_TAC(SPEC `cfprog cf` CPMAP_PT_IN_DART) THEN DISCH_TAC THEN
  ASM_SIMP_TAC[scycle; CPRING_REVERSE_NODE_CYCLE; FACE_SIMPLE_REVERSE;
               PAIRWISE_REVERSE_SYM; PAIRWISE_CPRING] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP CPMAP_SIMPLE) THEN
    REWRITE_TAC[FACE_SIMPLE_APPEND'] THEN SIMP_TAC[];
    REWRITE_TAC[GSYM ALL_MEM; MEM_REVERSE] THEN
    ASM_MESON_TAC[MEM_CPRING_IN_DART]]);;
let KERNEL_CFRING_FBAND_CPKER = prove
 (`!cp u. config_prog cp /\ u IN dart (FST(cpmap cp))
          ==> (kernel (FST(cpmap cp))
                 (REVERSE (cpring (FST(cpmap cp)) (SND(cpmap cp)))) u <=>
               fband (FST(cpmap cp)) (cpker cp) u)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[kernel; FBAND_REVERSE] THEN
  MP_TAC(SPEC `cp:(cpstep)list` CPMAP_COVER) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `u:num`) THEN
  MP_TAC(SPEC `cp:(cpstep)list` CPMAP_SIMPLE) THEN
  ASM_REWRITE_TAC[FACE_SIMPLE_APPEND'; FBAND_APPEND] THEN
  REWRITE_TAC[FBAND_MEM_IFF] THEN ASM_MESON_TAC[CFACE_SYM; CFACE_TRANS]);;
let CPMASK_ADJ1 = prove
 (`!cp i x. config_prog cp /\ i < cpksize cp
            ==> (fband (FST(cpmap cp)) (cpmask (cpadj (cfmask1 cp i) cp) cp) x
                 <=> adj (FST(cpmap cp)) x (EL i (cpker cp)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`cp:(cpstep)list`; `cfmask1 cp i`] CPMASK_ADJ) THEN
  ASM_SIMP_TAC[PROPER_CPMASK1; CPMASK1; EX]);;
let CPMASK_ADJ2 = prove
 (`!cp i x. config_prog cp /\ i < cpksize cp
            ==> (fband (FST(cpmap cp))
                   (cpmask (cpadj (FST(cfmask1 cp i),
                                   SND(cpadj (cfmask1 cp i) cp)) cp) cp) x <=>
                 EX (adj (FST(cpmap cp)) x)
                    (mask_list (SND(cpadj (cfmask1 cp i) cp)) (cpker cp)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`cp:(cpstep)list`;
                 `(FST(cfmask1 cp i), SND(cpadj (cfmask1 cp i) cp))`]
         CPMASK_ADJ) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`cp:(cpstep)list`; `cfmask1 cp i`] CPADJ_PROPER) THEN
    ASM_REWRITE_TAC[PROPER_CPMASK1; proper_cpmask] THEN
    SIMP_TAC[cfmask1; LENGTH_REPLICATE];
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[cpmask; cfmask1; MASK_LIST_REPLICATE_F; APPEND]]);;
let CPRADIUS2_WITNESS = prove
 (`!cp i. config_prog cp /\ i < cpksize cp /\
          ALL (\b. b) (SND (cpadj (FST (cfmask1 cp i),
                                   SND (cpadj (cfmask1 cp i) cp)) cp))
          ==> radius2_kernel (FST(cpmap cp))
                (REVERSE (cpring (FST(cpmap cp)) (SND(cpmap cp))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ABBREV_TAC `x0 = EL i (cpker cp)` THEN
  ABBREV_TAC `m1 = SND (cpadj (cfmask1 cp i) cp)` THEN
  ABBREV_TAC `cm2 = cpadj (FST (cfmask1 cp i), m1:(bool)list) cp` THEN
  SUBGOAL_THEN `plain_hypermap (FST(cpmap cp))` ASSUME_TAC THENL
   [ASM_MESON_TAC[CPMAP_PLAIN; CONFIG_PROG_CUBIC]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. MEM y (cpker cp) ==> y IN dart (FST(cpmap cp))`
    ASSUME_TAC THENL
   [ASM_MESON_TAC[CPKER_IN_DART; config_prog]; ALL_TAC] THEN
  SUBGOAL_THEN `MEM (x0:num) (cpker cp)` ASSUME_TAC THENL
   [EXPAND_TAC "x0" THEN MATCH_MP_TAC MEM_EL THEN ASM_SIMP_TAC[SIZE_CPKER];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. MEM y (cpker cp) ==> MEM y (cpmask cm2 cp)`
    ASSUME_TAC THENL
   [REWRITE_TAC[cpmask; MEM_APPEND] THEN
    SUBGOAL_THEN
      `mask_list (SND (cm2:(bool)list#(bool)list)) (cpker cp) = cpker cp`
      (fun th -> SIMP_TAC[th]) THEN
    MATCH_MP_TAC MASK_LIST_ALL_T THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`cp:(cpstep)list`; `(FST(cfmask1 cp i), m1:(bool)list)`]
           CPADJ_PROPER) THEN
    ASM_REWRITE_TAC[proper_cpmask; cfmask1; LENGTH_REPLICATE] THEN
    EXPAND_TAC "m1" THEN
    MP_TAC(ISPECL [`cp:(cpstep)list`; `cfmask1 cp i`] CPADJ_PROPER) THEN
    ASM_SIMP_TAC[PROPER_CPMASK1; proper_cpmask; SIZE_CPKER];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. MEM y (mask_list m1 (cpker cp))
                ==> y IN dart (FST(cpmap cp)) /\ adj (FST(cpmap cp)) y x0`
    ASSUME_TAC THENL
   [X_GEN_TAC `y:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`cp:(cpstep)list`; `i:num`; `y:num`] CPMASK_ADJ1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MEM_MASK_LIST]; ALL_TAC] THEN
    MATCH_MP_TAC FBAND_MEM THEN EXPAND_TAC "m1" THEN
    ASM_REWRITE_TAC[cpmask; MEM_APPEND];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u. u IN dart (FST(cpmap cp))
                ==>
                (~fband (FST(cpmap cp))
                (REVERSE (cpring (FST(cpmap cp)) (SND(cpmap cp)))) u
                <=> fband (FST(cpmap cp)) (cpker cp) u)` ASSUME_TAC THENL
   [ASM_MESON_TAC[KERNEL_CFRING_FBAND_CPKER; kernel]; ALL_TAC] THEN
  REWRITE_TAC[radius2_kernel; IN_KERNEL] THEN EXISTS_TAC `x0:num` THEN
  SUBGOAL_THEN `(x0:num) IN dart (FST(cpmap cp))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[FBAND_MEM]; ALL_TAC] THEN
  X_GEN_TAC `w:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `fband (FST(cpmap cp)) (cpker cp) w` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `fband (FST(cpmap cp)) (cpmask cm2 cp) w` MP_TAC THENL
   [UNDISCH_TAC `fband (FST(cpmap cp)) (cpker cp) w` THEN
    REWRITE_TAC[FBAND_MEM_IFF] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`cp:(cpstep)list`; `i:num`; `w:num`] CPMASK_ADJ2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM EX_MEM; ADJP] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:num) IN dart (FST(cpmap cp)) /\ adj (FST(cpmap cp)) y x0`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(z:num) IN dart (FST(cpmap cp)) /\ edge_map (FST(cpmap cp)) z
                IN dart (FST(cpmap cp))` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CFT_DART; EDGE_IN_DART]; ALL_TAC] THEN
  SUBGOAL_THEN `adj (FST(cpmap cp)) x0 (edge_map (FST(cpmap cp)) z)`
    MP_TAC THENL
   [MATCH_MP_TAC ADJ_SYM THEN ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`cp:(cpstep)list`; `i:num`; `edge_map (FST(cpmap cp)) z`]
           CPMASK_ADJ1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC FBAND_CFACE THEN EXISTS_TAC `y:num` THEN
    ASM_SIMP_TAC[CFACE_SYM] THEN MATCH_MP_TAC FBAND_MEM THEN
    EXPAND_TAC "m1" THEN ASM_REWRITE_TAC[cpmask; MEM_APPEND];
    ALL_TAC] THEN
  REWRITE_TAC[ADJP] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`t:num`; `z:num`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(t:num) IN dart (FST(cpmap cp)) /\ edge_map (FST(cpmap cp)) t
                IN dart (FST(cpmap cp))` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CFT_DART; EDGE_IN_DART]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC FBAND_CFACE THEN
  EXISTS_TAC `edge_map (FST(cpmap cp)) z` THEN ASM_SIMP_TAC[CFACE_SYM] THEN
  MATCH_MP_TAC FBAND_CFACE THEN EXISTS_TAC `y:num` THEN
  ASM_SIMP_TAC[CFACE_SYM] THEN MATCH_MP_TAC FBAND_MEM THEN
  ASM_MESON_TAC[MEM_MASK_LIST]);;
let CPRADIUS2_IMP = prove
 (`!cp. config_prog cp
        ==> !i. i <= cpksize cp /\ cpradius2 cp i
                ==> radius2_kernel (FST(cpmap cp))
                      (REVERSE (cpring (FST(cpmap cp)) (SND(cpmap cp))))`,
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC[cpradius2] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN COND_CASES_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC CPRADIUS2_WITNESS THEN EXISTS_TAC `i:num` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC]);;
let CPRADIUS2P = prove
 (`!cf. isQuizR (cfquiz cf) ==> radius2_kernel (FST (cfmap cf)) (cfring cf)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[cfring; cfmap] THEN
  MP_TAC(SPEC `cfprog cf` CPRADIUS2_IMP) THEN
  ASM_SIMP_TAC[CFQUIZ_CONFIG_PROG] THEN DISCH_THEN MATCH_MP_TAC THEN
  EXISTS_TAC `cpksize (cfprog cf)` THEN REWRITE_TAC[LE_REFL] THEN
  ASM_SIMP_TAC[CFQUIZ_UNFOLD]);;
let RQS_FIT_LENGTH = prove
 (`!(G0:(num)hypermap) D qs p. rqs_fit G0 D qs p ==> LENGTH qs = LENGTH p`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[rqs_fit; LENGTH] THEN ASM_MESON_TAC[]);;
let RQS_FIT_APPEND = prove
 (`!(G0:(num)hypermap) D qs1 p1 qs2 p2.
     LENGTH qs1 = LENGTH p1
     ==> (rqs_fit G0 D (APPEND qs1 qs2) (APPEND p1 p2) <=>
          rqs_fit G0 D qs1 p1 /\ rqs_fit G0 D qs2 p2)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH] THEN DISCH_THEN(MP_TAC o SYM) THEN
    REWRITE_TAC[LENGTH_EQ_NIL] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[APPEND; rqs_fit];
    GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `p1:(num)list` list_CASES) THEN
    REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; APPEND; rqs_fit] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[CONJ_ACI]]);;
let RQS_WALK_APPEND = prove
 (`!(G0:(num)hypermap) qs1 p1 qs2 p2.
     LENGTH qs1 = LENGTH p1
     ==> rqs_walk G0 (APPEND qs1 qs2) (APPEND p1 p2) =
         APPEND (rqs_walk G0 qs1 p1) (rqs_walk G0 qs2 p2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH] THEN DISCH_THEN(MP_TAC o SYM) THEN
    REWRITE_TAC[LENGTH_EQ_NIL] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[APPEND; rqs_walk];
    GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `p1:(num)list` list_CASES) THEN
    REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; APPEND; rqs_walk] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[APPEND_ASSOC]]);;
let RQS_WALK_MEM_DART = prove
 (`!(G0:(num)hypermap) qs p. (!u. MEM u p ==> u IN dart G0)
     ==> !z. MEM z (rqs_walk G0 qs p) ==> z IN dart G0`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[rqs_walk; MEM] THEN
  X_GEN_TAC `p:(num)list` THEN
  STRUCT_CASES_TAC(ISPEC `p:(num)list` list_CASES) THEN
  REWRITE_TAC[rqs_walk; MEM; MEM_APPEND; MEM_COND_SING] THEN DISCH_TAC THEN
  X_GEN_TAC `z:num` THEN STRIP_TAC THENL
   [ASM_MESON_TAC[];
    MP_TAC(ISPECL [`SND(SND (h:bool#num#question))`; `G0:(num)hypermap`;
                   `node_map G0 (h':num)`] WALKQ_MEM_DART) THEN
    ASM_SIMP_TAC[NODE_FACE_IN_DART; GSYM ALL_MEM];
    ASM_MESON_TAC[]]);;
let SUBARITY_CFACE = prove
 (`!(G0:(num)hypermap) D x y.
     x IN dart G0 /\ cface G0 x y ==> subarity G0 D y = subarity G0 D x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[subarity] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[CFACE_TRANS]);;
let SUBARITY_DART = prove
 (`!(G0:(num)hypermap) x.
     x IN dart G0 ==> subarity G0 (dart G0) x = arity G0 x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[subarity; ARITY_CARD_CFACE] THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  ASM_MESON_TAC[CFT_DART]);;
let SUBARITY_SAME = prove
 (`!(G0:(num)hypermap) D D' x.
     D SUBSET D' /\ (!z. z IN D' /\ ~(z IN D) ==> ~cface G0 x z)
     ==> subarity G0 D' x = subarity G0 D x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[subarity] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[SUBSET]);;
let SUBARITY_INSERT = prove
 (`!(G0:(num)hypermap) D D' x w.
     FINITE D' /\ D SUBSET D' /\ w IN D' /\ ~(w IN D) /\
     (!z. z IN D' /\ ~(z IN D) ==> (cface G0 x z <=> z = w))
     ==> subarity G0 D' x = subarity G0 D x + 1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[subarity] THEN
  SUBGOAL_THEN `{z | z IN D' /\ cface G0 x z} = (w:num) INSERT {z | z IN D /\
                cface G0 x z}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `FINITE {z | z IN (D:num->bool) /\ cface (G0:(num)hypermap) x z}`
    ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `D':num->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_CLAUSES; IN_ELIM_THM] THEN ARITH_TAC);;

(* The sub-arity of x when the darts of D' in its G0-face are exactly the    *)
(* new darts l (none of D, e.g. the apex face of a Y or H step).             *)
let SUBARITY_NEW_FACE = prove
 (`!(G0:(num)hypermap) D D' x l.
     PAIRWISE (\p q. ~(p = q)) l /\
     (!z. MEM z l ==> z IN D' /\ ~(z IN D)) /\
     (!z. z IN D ==> ~cface G0 z x) /\
     (!z. z IN D' /\ ~(z IN D) ==> (cface G0 x z <=> MEM z l))
     ==> subarity G0 D' x = LENGTH l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[subarity] THEN
  SUBGOAL_THEN `{z | z IN D' /\ cface (G0:(num)hypermap) x z} = set_of_list l`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SET_OF_LIST] THEN
    X_GEN_TAC `z:num` THEN ASM_CASES_TAC `(z:num) IN D` THENL
     [MATCH_MP_TAC(TAUT `~b /\ ~c ==> (a /\ b <=> c)`) THEN
      ASM_MESON_TAC[CFACE_SYM_GEN];
      ASM_CASES_TAC `(z:num) IN D'` THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]];
    ASM_SIMP_TAC[CARD_SET_OF_LIST_PAIRWISE]]);;
let CFACESET_EQ_CFACE = prove
 (`!(H:(A)hypermap) x y. x IN dart H
     ==> ({z | cface H x z} = {z | cface H y z} <=> cface H x y)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `y:A` o REWRITE_RULE[EXTENSION; IN_ELIM_THM]) THEN
    REWRITE_TAC[CFACE_REFL];
    ASM_MESON_TAC[CFACE_SET_EQ]]);;
let FACE_SIMPLE_CARD_CFACESET = prove
 (`!(H:(A)hypermap) l. (!z. MEM z l ==> z IN dart H)
     ==> (face_simple H l <=>
          CARD (IMAGE (\x. {z | cface H x z}) (set_of_list l)) = LENGTH l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MEM; face_simple; set_of_list; IMAGE_CLAUSES; CARD_CLAUSES;
              LENGTH] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `face_simple (H:(A)hypermap) t
                <=> CARD (IMAGE (\x. {z | cface H x z}) (set_of_list t)) =
                LENGTH t` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x. {z | cface (H:(A)hypermap) x z}) h IN IMAGE
                (\x. {z | cface H x z}) (set_of_list t) <=> fband H t h`
    ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE; IN_SET_OF_LIST; FBAND_MEM_IFF] THEN
    ASM_MESON_TAC[CFACESET_EQ_CFACE];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD
                (IMAGE (\x. {z | cface (H:(A)hypermap) x z}) (set_of_list t))
                <= LENGTH t` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD (set_of_list (t:(A)list))` THEN
    SIMP_TAC[CARD_IMAGE_LE; FINITE_SET_OF_LIST; CARD_SET_OF_LIST_LE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_IMAGE; FINITE_SET_OF_LIST] THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV BETA_CONV)) THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `fband (H:(A)hypermap) t h` THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;
let FACE_SIMPLE_FBAND_EQ = prove
 (`!(H:(A)hypermap) p q.
     (!z. MEM z p ==> z IN dart H) /\ (!z. MEM z q ==> z IN dart H) /\
     (!u. u IN dart H ==> (fband H p u <=> fband H q u)) /\
     LENGTH p = LENGTH q
     ==> (face_simple H p <=> face_simple H q)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FACE_SIMPLE_CARD_CFACESET] THEN
  SUBGOAL_THEN `IMAGE (\x. {z | cface (H:(A)hypermap) x z}) (set_of_list p) =
                IMAGE (\x. {z | cface H x z}) (set_of_list q)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SET_OF_LIST] THEN
    X_GEN_TAC `s:A->bool` THEN EQ_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `fband (H:(A)hypermap) p x /\ fband H q x /\ x IN dart H`
      STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[FBAND_MEM];
      ALL_TAC;
      ASM_MESON_TAC[FBAND_MEM];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FBAND_MEM_IFF]) THEN
    ASM_MESON_TAC[CFACE_SET_EQ];
    ASM_REWRITE_TAC[]]);;
let RQS_PROPER_STEP = prove
 (`!(G0:(num)hypermap) x00 D D' r r' qs qs' E u0.
     rqs_proper G0 x00 D' r' qs' /\ x00 IN dart G0 /\
     D SUBSET D' /\ D' SUBSET dart G0 /\
     (!z. MEM z r ==> z IN D) /\ (!z. MEM z r' ==> z IN D') /\
     (!z. MEM z E ==> z IN D') /\ u0 IN D' /\
     rqs_fit G0 D qs r /\
     (!u. u IN dart G0
          ==> (fband G0 (rqs_walk G0 qs r) u <=>
               fband G0 (rqs_walk G0 qs' r') u \/ fband G0 E u)) /\
     LENGTH (rqs_walk G0 qs r) = LENGTH (rqs_walk G0 qs' r') + LENGTH E /\
     face_simple G0 E /\
     (!e. MEM e E
          ==> ~fband G0 (APPEND (rqs_walk G0 qs' r') (cpring G0 x00)) e) /\
     (!u. u IN dart G0
          ==> (fband G0 r' u \/ fband G0 E u <=>
               fband G0 r u \/ cface G0 u u0)) /\
     (!u. u IN D' /\ ~(u IN D) ==> fband G0 r u \/ cface G0 u u0) /\
     (!u. u IN D ==> ~cface G0 u u0) /\
     (fband G0 (rqs_walk G0 qs' r') u0 \/ good_ring_arity G0 u0)
     ==> rqs_proper G0 x00 D r qs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rqs_proper] THEN
  INTRO_TAC "(fitO goodO simpO bandO) x00in Dsub Dsub2 rD rD2 ED u0D fit band
             len simpE Enot ring new apex ok" THEN
  SUBGOAL_THEN `!z. MEM z (cpring G0 x00) ==> z IN dart (G0:(num)hypermap)`
    ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM_CPRING_IN_DART]; ALL_TAC] THEN
  SUBGOAL_THEN `(!z. MEM z (rqs_walk G0 qs r) ==> z IN dart (G0:(num)hypermap))
                /\ (!z. MEM z (rqs_walk G0 qs' r') ==> z IN dart G0) /\
                (!z. MEM z (E:(num)list) ==> z IN dart G0) /\
                (u0:num) IN dart G0` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC RQS_WALK_MEM_DART) THEN
    USE_THEN "Dsub" MP_TAC THEN USE_THEN "Dsub2" MP_TAC THEN
    USE_THEN "rD" MP_TAC THEN USE_THEN "rD2" MP_TAC THEN
    USE_THEN "ED" MP_TAC THEN USE_THEN "u0D" MP_TAC THEN MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `face_simple G0 (APPEND E (APPEND (rqs_walk G0 qs' r') (cpring G0 x00)))`
    ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[FACE_SIMPLE_APPEND'] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!u. u IN dart G0
                ==> (fband G0 (APPEND (rqs_walk G0 qs r) (cpring G0 x00)) u
                <=> fband G0
                (APPEND E (APPEND (rqs_walk G0 qs' r') (cpring G0 x00))) u)`
    (LABEL_TAC "bandEq") THENL
   [X_GEN_TAC `u:num` THEN DISCH_TAC THEN
    USE_THEN "band" (MP_TAC o SPEC `u:num`) THEN
    REWRITE_TAC[ASSUME `(u:num) IN dart G0`; FBAND_APPEND] THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (APPEND (rqs_walk G0 qs r) (cpring G0 x00)) = LENGTH
                (APPEND E (APPEND (rqs_walk G0 qs' r') (cpring G0 x00)))`
    ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND] THEN USE_THEN "len" MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(!z. MEM z (APPEND (rqs_walk G0 qs r) (cpring G0 x00))
                ==> z IN dart (G0:(num)hypermap)) /\
                (!z. MEM z
                (APPEND E (APPEND (rqs_walk G0 qs' r') (cpring G0 x00)))
                ==> z IN dart G0)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEM_APPEND] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "fit" (fun th -> REWRITE_TAC[th]) THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `u:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(u:num) IN dart G0` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `cface G0 (u:num) u0` THENL
     [USE_THEN "ok" DISJ_CASES_TAC THENL
       [SUBGOAL_THEN `fband G0 (rqs_walk G0 qs' r') u` MP_TAC THENL
         [MATCH_MP_TAC FBAND_CFACE THEN EXISTS_TAC `u0:num` THEN
          ASM_SIMP_TAC[CFACE_SYM];
          ALL_TAC] THEN
        REWRITE_TAC[FBAND_MEM_IFF] THEN
        DISCH_THEN(X_CHOOSE_THEN `w:num` STRIP_ASSUME_TAC) THEN
        USE_THEN "simpO" (MP_TAC o REWRITE_RULE[FACE_SIMPLE_APPEND']) THEN
        DISCH_THEN(MP_TAC o SPEC `w:num` o CONJUNCT2 o CONJUNCT2) THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `fband G0 (cpring G0 x00) w`
          (fun th -> REWRITE_TAC[th]) THEN
        MATCH_MP_TAC FBAND_CFACE THEN EXISTS_TAC `u:num` THEN
        ASM_SIMP_TAC[FBAND_MEM];
        UNDISCH_TAC `good_ring_arity G0 (u0:num)` THEN
        REWRITE_TAC[good_ring_arity] THEN
        MP_TAC(ISPECL [`G0:(num)hypermap`; `u:num`; `u0:num`] ARITY_CFACE) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
      USE_THEN "goodO" MATCH_MP_TAC THEN
      REMOVE_THEN "ring" (MP_TAC o SPEC `u:num`) THEN
      REMOVE_THEN "new" (MP_TAC o SPEC `u:num`) THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC TAUT];
    MP_TAC(ISPECL [`G0:(num)hypermap`;
                   `APPEND (rqs_walk G0 qs r) (cpring G0 x00)`;
                   `APPEND E (APPEND (rqs_walk G0 qs' r') (cpring G0 x00))`]
           FACE_SIMPLE_FBAND_EQ) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `u:num` THEN DISCH_TAC THEN
    REMOVE_THEN "bandEq" (MP_TAC o SPEC `u:num`) THEN
    REMOVE_THEN "bandO" (MP_TAC o SPEC `u:num`) THEN
    REMOVE_THEN "ring" (MP_TAC o SPEC `u:num`) THEN
    REMOVE_THEN "new" (MP_TAC o SPEC `u:num`) THEN
    REMOVE_THEN "apex" (MP_TAC o SPEC `u:num`) THEN
    USE_THEN "Dsub" (MP_TAC o SPEC `u:num` o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[ASSUME `(u:num) IN dart G0`; FBAND_APPEND] THEN
    CONV_TAC TAUT]);;

let injcp_ctx = new_definition
 `injcp_ctx (G:(num)hypermap) (x0:num) (G0:(num)hypermap) <=>
    dart G SUBSET dart G0 /\
    (!x. x IN dart G ==> edge_map G0 x = edge_map G x) /\
    (!x. x IN dart G /\ ~MEM x (cpring G x0) ==> node_map G0 x = node_map G x)
    /\
    (!x y. x IN dart G /\ y IN dart G ==> (cface G0 x y <=> cface G x y))`;;
let INJCP_CTX_REFL = prove
 (`!(G:(num)hypermap) x0. injcp_ctx G x0 G`,
  REWRITE_TAC[injcp_ctx; SUBSET_REFL]);;
let INJCP_CTX_TRANS = prove
 (`!(G:(num)hypermap) x0 (G':(num)hypermap) x0' (G0:(num)hypermap).
     injcp_ctx G x0 G' /\ injcp_ctx G' x0' G0 /\
     (!x. x IN dart G /\ ~MEM x (cpring G x0) ==> ~MEM x (cpring G' x0'))
     ==> injcp_ctx G x0 G0`,
  REWRITE_TAC[injcp_ctx] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS];
    ASM_MESON_TAC[SUBSET];
    ASM_MESON_TAC[SUBSET];
    ASM_MESON_TAC[SUBSET]]);;
let MEM_TL_CPRING = prove
 (`!(G:(num)hypermap) x0 x. x0 IN dart G /\ MEM x (TL (cpring G x0))
                            ==> MEM x (cpring G x0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CPRING_CONS_HEAD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[MEM]);;
let MEM_TL_TL_CPRING = prove
 (`!(G:(num)hypermap) x0 x. x0 IN dart G /\ proper_cpring G x0 /\
                            MEM x (TL (TL (cpring G x0)))
                            ==> MEM x (cpring G x0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] HEAD_PROPER_CPRING) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[MEM]);;
let INJCP_CTX_Y = prove
 (`!(G:(num)hypermap) x0. x0 IN dart G /\ proper_cpring G x0
     ==> injcp_ctx G x0 (ecpY G x0) /\
         (!x. x IN dart G /\ ~MEM x (cpring G x0)
              ==> ~MEM x (cpring (ecpY G x0) (ecpY_pt G x0)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `G:(num)hypermap` HYPERMAP_LEMMA) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPY_FRESH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[injcp_ctx; DART_SUBSET_ECPY; EDGE_ECPY_OLD; CFACE_ICPY;
               CPRING_ECPY; MEM] THEN
  CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC NODE_ECPY_OLD THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~MEM x (cpring (G:(num)hypermap) x0)` THEN
    ASM_SIMP_TAC[MEM_CPRING; cnode; node];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[MEM_TL_CPRING]]);;
let INJCP_CTX_H = prove
 (`!(G:(num)hypermap) x0. x0 IN dart G /\ proper_cpring G x0
     ==> injcp_ctx G x0 (ecpH G x0) /\
         (!x. x IN dart G /\ ~MEM x (cpring G x0)
              ==> ~MEM x (cpring (ecpH G x0) (ecpH_pt G x0)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `G:(num)hypermap` HYPERMAP_LEMMA) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPY_FRESH) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPH_FRESH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[injcp_ctx; DART_SUBSET_ECPH; EDGE_ECPH_OLD; CFACE_ICPH;
               CPRING_ECPH; NODE_ECPY_PT_VALUE; MEM] THEN
  CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC NODE_ECPH_OLD THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~MEM x (cpring (G:(num)hypermap) x0)` THEN
    ASM_SIMP_TAC[MEM_CPRING; cnode; node];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[MEM_TL_TL_CPRING]]);;
let INJCP_CTX_CONS = prove
 (`!s cp. config_step s /\ cubic_prog cp
     ==> injcp_ctx (FST(cpmap cp)) (SND(cpmap cp)) (FST(cpmap (CONS s cp))) /\
         (!x. x IN dart (FST(cpmap cp)) /\
              ~MEM x (cpring (FST(cpmap cp)) (SND(cpmap cp)))
              ==> ~MEM x (cpring (FST(cpmap (CONS s cp)))
                                 (SND(cpmap (CONS s cp)))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONFIG_STEP_CASES] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[CPMAP_CONS_R; CPMAP_CONS_Y; CPMAP_CONS_H] THEN
  ASM_SIMP_TAC[ecpR; INJCP_CTX_REFL; MEM_CPRING_ECPR; CPMAP_PT_IN_DART;
               INJCP_CTX_Y; INJCP_CTX_H; CPMAP_PROPER]);;
let CUBIC_PROG_APPEND = prove
 (`!cp1 cp2. ALL config_step cp1 /\ cubic_prog cp2
             ==> cubic_prog (APPEND cp1 cp2)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP CONFIG_STEPS_CUBIC) THEN
  UNDISCH_TAC `cubic_prog cp2` THEN REWRITE_TAC[cubic_prog; ALL_APPEND] THEN
  SIMP_TAC[]);;
let INJCP_CTX_CPMAP = prove
 (`!cp1 cp2. ALL config_step cp1 /\ cubic_prog cp2
     ==> injcp_ctx (FST(cpmap cp2)) (SND(cpmap cp2))
                   (FST(cpmap (APPEND cp1 cp2))) /\
         (!x. x IN dart (FST(cpmap cp2)) /\
              ~MEM x (cpring (FST(cpmap cp2)) (SND(cpmap cp2)))
              ==> ~MEM x (cpring (FST(cpmap (APPEND cp1 cp2)))
                                 (SND(cpmap (APPEND cp1 cp2)))))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; APPEND; INJCP_CTX_REFL] THEN
  SIMP_TAC[] THEN GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `cp2:(cpstep)list`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`h:cpstep`; `APPEND (t:(cpstep)list) cp2`]
         INJCP_CTX_CONS) THEN
  ASM_SIMP_TAC[CUBIC_PROG_APPEND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `dart (FST(cpmap cp2)) SUBSET dart (FST(cpmap (APPEND t cp2)))`
    ASSUME_TAC THENL
   [ASM_MESON_TAC[injcp_ctx]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INJCP_CTX_TRANS THEN
    MAP_EVERY EXISTS_TAC [`FST(cpmap (APPEND (t:(cpstep)list) cp2))`;
                          `SND(cpmap (APPEND (t:(cpstep)list) cp2))`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;
let FACE_SIMPLE_APPEND_SWAP = prove
 (`!(H:(num)hypermap) p q r. face_simple H (APPEND (APPEND p q) r) <=>
                             face_simple H (APPEND (APPEND q p) r)`,
  REWRITE_TAC[FACE_SIMPLE_EQ_PAIRWISE; PAIRWISE_APPEND; MEM_APPEND] THEN
  MESON_TAC[CFACE_SYM_GEN]);;
let LENGTH_TAKE_DROP_LIST = prove
 (`!n (l:A list). LENGTH (take_list n l) + LENGTH (drop_list n l) = LENGTH l`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM TAKE_DROP_LIST] THEN
  REWRITE_TAC[LENGTH_APPEND]);;
let RQS_PROPER_ROT = prove
 (`!(G0:(num)hypermap) x00 D r n qs.
     rqs_proper G0 x00 D (rot_list n r) qs
     ==> rqs_proper G0 x00 D r (rotr_list n qs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rqs_proper] THEN
  ABBREV_TAC `qs' = rotr_list n (qs:(bool#num#question)list)` THEN
  SUBGOAL_THEN `qs = rot_list n (qs':(bool#num#question)list)` SUBST1_TAC THENL
   [EXPAND_TAC "qs'" THEN REWRITE_TAC[ROT_LIST_ROTR_CANCEL_GEN]; ALL_TAC] THEN
  REWRITE_TAC[FBAND_ROT] THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (qs':(bool#num#question)list) = LENGTH (r:(num)list)`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP RQS_FIT_LENGTH) THEN
    REWRITE_TAC[LENGTH_ROT_LIST];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (drop_list n (qs':(bool#num#question)list)) = LENGTH
                (drop_list n (r:(num)list)) /\
                LENGTH (take_list n (qs':(bool#num#question)list)) = LENGTH
                (take_list n (r:(num)list))` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`n:num`; `qs':(bool#num#question)list`]
           LENGTH_TAKE_DROP_LIST) THEN
    MP_TAC(ISPECL [`n:num`; `r:(num)list`] LENGTH_TAKE_DROP_LIST) THEN
    ASM_REWRITE_TAC[LENGTH_DROP_LIST] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G0:(num)hypermap`; `D:num->bool`;
                 `drop_list n (qs':(bool#num#question)list)`;
                 `drop_list n (r:(num)list)`;
                 `take_list n (qs':(bool#num#question)list)`;
                 `take_list n (r:(num)list)`] RQS_FIT_APPEND) THEN
  MP_TAC(ISPECL [`G0:(num)hypermap`; `D:num->bool`;
                 `take_list n (qs':(bool#num#question)list)`;
                 `take_list n (r:(num)list)`;
                 `drop_list n (qs':(bool#num#question)list)`;
                 `drop_list n (r:(num)list)`] RQS_FIT_APPEND) THEN
  MP_TAC(ISPECL [`G0:(num)hypermap`;
                 `drop_list n (qs':(bool#num#question)list)`;
                 `drop_list n (r:(num)list)`;
                 `take_list n (qs':(bool#num#question)list)`;
                 `take_list n (r:(num)list)`] RQS_WALK_APPEND) THEN
  MP_TAC(ISPECL [`G0:(num)hypermap`;
                 `take_list n (qs':(bool#num#question)list)`;
                 `take_list n (r:(num)list)`;
                 `drop_list n (qs':(bool#num#question)list)`;
                 `drop_list n (r:(num)list)`] RQS_WALK_APPEND) THEN
  ASM_REWRITE_TAC[GSYM rot_list; TAKE_DROP_LIST] THEN
  DISCH_THEN SUBST1_TAC THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[FACE_SIMPLE_APPEND_SWAP] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `u:num` o check (is_forall o concl)) THEN
  REWRITE_TAC[ASSUME `(u:num) IN dart G0`; FBAND_APPEND] THEN CONV_TAC TAUT);;
let SMALL_QARITYP = prove
 (`!a. bad_small_arity (small_qarity a) <=>
       ~(nat_of_qarity (small_qarity a) = a + 2)`,
  GEN_TAC THEN REWRITE_TAC[small_qarity] THEN REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[bad_small_arity; nat_of_qarity] THEN ASM_ARITH_TAC);;
let NOT_BAD_RING_ARITY = prove
 (`!(G:(A)hypermap) x. ~(bad_ring_arity (arity G x - 2))
                       ==> good_ring_arity G x`,
  REWRITE_TAC[bad_ring_arity; good_ring_arity] THEN ARITH_TAC);;
let FBAND_COND = prove
 (`!(H:(A)hypermap) b x u. fband H (if b then [x] else []) u <=>
                           b /\ cface H u x`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[FBAND_CONS; FBAND_NIL]);;
(* The Y-step question combination (Coq simq / selq): q' rooted at nv walks  *)
(* q1 from qstepR nv and q2 from qstepL nv, plus nv itself when k2.          *)
let walk_Y = new_definition
 `walk_Y (H:(num)hypermap) (nv:num) (k2:bool) (a2:num) (q1:question)
         (q2:question) (q':question) <=>
    (fitq H nv q' <=>
       (k2 ==> arity H nv = a2 + 2) /\ fitq H (qstepR H nv) q1 /\
       fitq H (qstepL H nv) q2) /\
    (!u. u IN dart H
         ==> (fband H (walkq q' H nv) u <=>
              (k2 /\ cface H u nv) \/ fband H (walkq q1 H (qstepR H nv)) u \/
              fband H (walkq q2 H (qstepL H nv)) u)) /\
    LENGTH (walkq q' H nv) =
      (if k2 then 1 else 0) + LENGTH (walkq q1 H (qstepR H nv)) +
      LENGTH (walkq q2 H (qstepL H nv))`;;
let WALK_Y_TAC =
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[walk_Y; fitq; flatq; walkq; MAP; MAP_APPEND; CONS_11; FBAND_CONS;
              FBAND_APPEND; FBAND_NIL; LENGTH; LENGTH_APPEND] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  (ARITH_TAC ORELSE (REWRITE_TAC[DISJ_ACI] THEN NO_TAC) ORELSE MESON_TAC[]);;
let WALK_Y_LR = prove
 (`!(H:(num)hypermap) nv a2 qa q1 q2.
     nat_of_qarity qa = a2 + 2 ==> walk_Y H nv T a2 q1 q2 (QaskLR qa q2 q1)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[walk_Y; fitq; flatq; walkq; MAP; MAP_APPEND; CONS_11; FBAND_CONS;
              FBAND_APPEND; LENGTH; LENGTH_APPEND] THEN
  MP_TAC(ISPECL [`flatq q2`; `flatq q1`;
                 `MAP (arity (H:(num)hypermap)) (walkq q2 H (qstepL H nv))`;
                 `MAP (arity (H:(num)hypermap)) (walkq q1 H (qstepR H nv))`]
         APPEND_EQ_SAME_LENGTH) THEN
  REWRITE_TAC[LENGTH_MAP; SIZE_WALKQ] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MESON_TAC[]; REWRITE_TAC[DISJ_ACI]; ARITH_TAC]);;
let WALK_Y_L = prove
 (`!(H:(num)hypermap) nv a2 qa q2.
     nat_of_qarity qa = a2 + 2 ==> walk_Y H nv T a2 Qask0 q2 (QaskL qa q2)`,
  WALK_Y_TAC);;
let WALK_Y_R = prove
 (`!(H:(num)hypermap) nv a2 qa q1.
     nat_of_qarity qa = a2 + 2 ==> walk_Y H nv T a2 q1 Qask0 (QaskR qa q1)`,
  WALK_Y_TAC);;
let WALK_Y_1 = prove
 (`!(H:(num)hypermap) nv a2 qa.
     nat_of_qarity qa = a2 + 2 ==> walk_Y H nv T a2 Qask0 Qask0 (Qask1 qa)`,
  WALK_Y_TAC);;
let WALK_Y_0 = prove
 (`!(H:(num)hypermap) nv a2. walk_Y H nv F a2 Qask0 Qask0 Qask0`,
  WALK_Y_TAC);;
let WALK_Y_RR = prove
 (`!(H:(num)hypermap) nv a2 qa q1r.
     walk_Y H nv F a2 (QaskR qa q1r) Qask0 (QaskRR qa q1r)`,
  WALK_Y_TAC);;
let WALK_Y_LL = prove
 (`!(H:(num)hypermap) nv a2 qa q2l.
     nv IN dart H ==> walk_Y H nv F a2 Qask0 (QaskL qa q2l) (QaskLL qa q2l)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `qstepL (H:(num)hypermap) nv IN dart H` ASSUME_TAC THENL
   [ASM_MESON_TAC[QSTEP_IN_DART]; ALL_TAC] THEN
  ASM_SIMP_TAC[walk_Y; fitq; flatq; walkq; MAP; CONS_11; FBAND_CONS; FBAND_NIL;
               LENGTH; ADD_CLAUSES; ARITY_EN; CFACE_INV_FACE]);;
let QASKR_EXPAND = prove
 (`!q. isQaskR q ==> q = QaskR (qra q) (qrb q)`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `q:question` (cases "question")) THEN
  REWRITE_TAC[isQaskR; qra; qrb]);;
let QASKL_EXPAND = prove
 (`!q. isQaskL q ==> q = QaskL (qra q) (qrb q)`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `q:question` (cases "question")) THEN
  REWRITE_TAC[isQaskL; qra; qrb]);;

(* The case analysis of cfquiz_Y: a nonempty result is f q' for a q' that    *)
(* walks q1 and q2 (and the ring-arity check passed when ~k2).               *)
let CFQUIZ_Y_SPEC = prove
 (`!rq1 rq2 (f:question->(bool#num#question)list) (H:(num)hypermap) nv.
     nv IN dart H /\ ~(cfquiz_Y rq1 rq2 f = [])
     ==> ?q'. cfquiz_Y rq1 rq2 f = f q' /\
              (~FST rq2 ==> ~bad_ring_arity (FST(SND rq2))) /\
              walk_Y H nv (FST rq2) (FST(SND rq2)) (SND(SND rq1))
                     (SND(SND rq2)) q'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cfquiz_Y; LET_DEF; LET_END_DEF] THEN
  ASM_CASES_TAC `FST (rq2:bool#num#question)` THEN ASM_REWRITE_TAC[] THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `nat_of_qarity
                  (small_qarity (FST(SND (rq2:bool#num#question)))) =
                  FST(SND rq2) + 2` ASSUME_TAC THENL
     [ASM_MESON_TAC[SMALL_QARITYP]; ALL_TAC] THEN
    EXISTS_TAC `if SND(SND (rq1:bool#num#question)) = Qask0 then
                (if SND(SND (rq2:bool#num#question)) = Qask0 then Qask1
                (small_qarity (FST(SND rq2))) else QaskL
                (small_qarity (FST(SND rq2))) (SND(SND rq2))) else
                (if SND(SND rq2) = Qask0 then QaskR
                (small_qarity (FST(SND rq2))) (SND(SND rq1)) else QaskLR
                (small_qarity (FST(SND rq2))) (SND(SND rq2))
                (SND(SND rq1)))` THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN
    (MATCH_MP_TAC WALK_Y_1 ORELSE MATCH_MP_TAC WALK_Y_L ORELSE MATCH_MP_TAC
     WALK_Y_R ORELSE MATCH_MP_TAC WALK_Y_LR) THEN
    ASM_REWRITE_TAC[];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THENL
     [STRIP_TAC THEN EXISTS_TAC `Qask0` THEN ASM_REWRITE_TAC[WALK_Y_0];
      ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [STRIP_TAC THEN
      EXISTS_TAC `QaskRR (qra (SND(SND (rq1:bool#num#question))))
                  (qrb (SND(SND rq1)))` THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(fun th ->
                  ONCE_REWRITE_TAC[MATCH_MP QASKR_EXPAND (CONJUNCT1 th)]) THEN
      REWRITE_TAC[qra; qrb; WALK_Y_RR];
      ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `QaskLL (qra (SND(SND (rq2:bool#num#question))))
                (qrb (SND(SND rq2)))` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th ->
                ONCE_REWRITE_TAC[MATCH_MP QASKL_EXPAND (CONJUNCT2 th)]) THEN
    REWRITE_TAC[qra; qrb] THEN MATCH_MP_TAC WALK_Y_LL THEN
    ASM_REWRITE_TAC[]]);;
let RQS_FIT_SUBARITY_CONG = prove
 (`!(G0:(num)hypermap) D D' qs p.
     (!x. MEM x p ==> subarity G0 D' x = subarity G0 D x)
     ==> (rqs_fit G0 D' qs p <=> rqs_fit G0 D qs p)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  X_GEN_TAC `p:(num)list` THEN
  STRUCT_CASES_TAC(ISPEC `p:(num)list` list_CASES) THEN
  REWRITE_TAC[rqs_fit; MEM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `subarity G0 D' (h':num) = subarity G0 D h'` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t':(num)list`) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])]);;

(* The G0-level geometry of a Y step at x0 (Coq en_v1, enn_v1, nu0FnG ...):  *)
(* a = FST(new_dart2(dart G)) (= ecpU_pt), b = SND(..), u0 = ecpY_pt (apex), *)
(* b' = SND(new_dart2(dart(ecpU G x0))); node v1 = a, edge a = b, node a =   *)
(* b', edge b' = u0 in the full map; b ~ v1, u0 ~ a, b' ~ x0, and the apex   *)
(* face contains no old dart.                                                *)
let ECPY_STEP_FACTS = prove
 (`!(G:(num)hypermap) x0 (G0:(num)hypermap).
     x0 IN dart G /\ proper_cpring G x0 /\ face_simple G (cpring G x0) /\
     injcp_ctx (ecpY G x0) (ecpY_pt G x0) G0
     ==> injcp_ctx G x0 G0 /\
         node_map G0 (node_map G x0) = FST(new_dart2(dart G)) /\
         edge_map G0 (FST(new_dart2(dart G))) = SND(new_dart2(dart G)) /\
         node_map G0 (FST(new_dart2(dart G))) =
           SND(new_dart2(dart(ecpU G x0))) /\
         edge_map G0 (SND(new_dart2(dart(ecpU G x0)))) = ecpY_pt G x0 /\
         cface G0 (SND(new_dart2(dart G))) (node_map G x0) /\
         cface G0 (ecpY_pt G x0) (FST(new_dart2(dart G))) /\
         cface G0 (SND(new_dart2(dart(ecpU G x0)))) x0 /\
         (!u. u IN dart G ==> ~cface G0 u (ecpY_pt G x0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `G:(num)hypermap` HYPERMAP_LEMMA) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPY_FRESH) THEN
  ASM_REWRITE_TAC[ecpU_pt] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] INJCP_CTX_Y) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `injcp_ctx G x0 (G0:(num)hypermap)` ASSUME_TAC THENL
   [MATCH_MP_TAC INJCP_CTX_TRANS THEN
    MAP_EVERY EXISTS_TAC
      [`ecpY (G:(num)hypermap) x0`; `ecpY_pt (G:(num)hypermap) x0`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] HEAD_PROPER_CPRING) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `r1 = TL(TL(cpring (G:(num)hypermap) x0))` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CPRING_ECPY) THEN
  ASM_REWRITE_TAC[TL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(node_map G x0 = x0) /\ ~MEM (node_map G x0) (r1:(num)list) /\
                (!z. MEM z r1 ==> z IN dart (G:(num)hypermap))`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `face_simple G (cpring (G:(num)hypermap) x0)` THEN
    UNDISCH_TAC `proper_cpring (G:(num)hypermap) x0` THEN
    ASM_REWRITE_TAC[face_simple; FBAND_CONS; proper_cpring] THEN
    REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[];
      ASM_MESON_TAC[FBAND_MEM];
      MATCH_MP_TAC MEM_CPRING_IN_DART THEN EXISTS_TAC `x0:num` THEN
      ASM_REWRITE_TAC[MEM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `node_map G x0 IN dart (G:(num)hypermap) /\
                FST(new_dart2(dart G)) IN dart (ecpY G x0) /\
                SND(new_dart2(dart G)) IN dart (ecpY G x0) /\
                SND(new_dart2(dart(ecpU G x0))) IN dart (ecpY G x0) /\
                node_map G x0 IN dart (ecpY G x0) /\ x0 IN dart (ecpY G x0) /\
                ecpY_pt G x0 IN dart (ecpY G x0)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[DART_ECPY_CASES; ecpU_pt; NODE_FACE_IN_DART]; ALL_TAC] THEN
  SUBGOAL_THEN `~MEM (node_map G x0)
                (cpring (ecpY (G:(num)hypermap) x0) (ecpY_pt G x0)) /\
                ~MEM (FST(new_dart2(dart G)))
                (cpring (ecpY G x0) (ecpY_pt G x0))` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MEM; DE_MORGAN_THM] THEN REPEAT CONJ_TAC THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `injcp_ctx (ecpY G x0) (ecpY_pt G x0) (G0:(num)hypermap)` THEN
  REWRITE_TAC[injcp_ctx] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] NODE_ECPY_3CYCLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] EDGE_ECPY_ECPUPT) THEN
  ASM_REWRITE_TAC[ecpU_pt] THEN DISCH_TAC THEN
  SUBGOAL_THEN `node_map G0 (node_map G x0) =
                FST(new_dart2(dart (G:(num)hypermap))) /\
                edge_map G0 (FST(new_dart2(dart G))) = SND(new_dart2(dart G))
                /\ node_map G0 (FST(new_dart2(dart G))) =
                SND(new_dart2(dart(ecpU G x0))) /\
                edge_map G0 (SND(new_dart2(dart(ecpU G x0)))) = ecpY_pt G x0`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[] THEN ASM_SIMP_TAC[EDGE_ECPY_B_GEN]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`G0:(num)hypermap`; `node_map (G:(num)hypermap) x0`]
           nodeK) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[CFT_FACE];
    MP_TAC(ISPECL
           [`G0:(num)hypermap`; `FST(new_dart2(dart (G:(num)hypermap)))`]
           nodeK) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[CFT_FACE];
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPY_FACE_EDGE_PT) THEN
    ASM_SIMP_TAC[EDGE_ECPY_APEX_GEN] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
    REWRITE_TAC[CFT_FACE];
    X_GEN_TAC `u:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(u:num) IN dart (ecpY G x0)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] DART_SUBSET_ECPY) THEN
      ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `u:num`]
           CFACE_ECPY_APEX_OLD) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[CFACE_SYM_GEN]]);;

(* ------------------------------------------------------------------------- *)
(* The CpY step of Coq cfquizP: rqs_proper transfers from (ecpY G x0, rq1 :: *)
(* rq2 :: rq3 :: qs3) to (G, cfquiz_Y rq1 rq2 (rqs_Y rq1 rq3 qs3)) when the  *)
(* latter is nonempty.  Darts a = FST(new_dart2(dart G)), b = SND(..), the   *)
(* apex u0 = ecpY_pt G x0, b' = SND(new_dart2(dart(ecpU G x0))); v1 = node   *)
(* x0; cpring G x0 = v1 :: x0 :: r1, cpring (ecpY G x0) u0 = b :: u0 :: x0   *)
(* :: r1.  The new question q' (CFQUIZ_Y_SPEC) is rooted at a = node G0 v1.  *)
(* ------------------------------------------------------------------------- *)

(* NEW_DARTS_TAC proves !z. (z IN D' /\ ~(z IN D) ==> ...) by cases on the   *)
(* new dart z (D' = D plus explicit darts) and CFACE_TAC; NEWCF_TAC          *)
(* discharges !z. z IN D' /\ ~(z IN D) ==> .. from the assumption "newcf".   *)
let NEW_DARTS_TAC =
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CFACE_TAC[];;

let NEWCF_TAC =
  X_GEN_TAC `z:num` THEN DISCH_TAC THEN
  USE_THEN "newcf" (MP_TAC o SPEC `z:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_SIMP_TAC[]];;

(* The faces in G0 of the darts a, b, u0, b' added by a Y step: b and b'     *)
(* join the faces of the ring darts v1 and x0, a the apex face of u0, which  *)
(* holds no old dart.                                                        *)
let ECPY_NEW_FACES = prove
 (`!(G0:(num)hypermap) D D' x0 a b u0 b' v1 r1.
     (!z. z IN D' <=> z = a \/ z = b \/ z = u0 \/ z = b' \/ z IN D) /\
     ~(a IN D) /\ ~(b IN D) /\ ~(u0 IN D) /\ ~(b' IN D) /\
     ~(a = b) /\ ~(u0 = a) /\ ~(u0 = b) /\ ~(b' = a) /\ ~(b' = b) /\
     ~(u0 = b') /\
     cface G0 b v1 /\ cface G0 u0 a /\ cface G0 b' x0 /\
     (!u. u IN D ==> ~cface G0 u u0) /\ v1 IN D /\ x0 IN D /\
     ~cface G0 v1 x0 /\
     (!x. MEM x r1 ==> x IN D /\ ~cface G0 x v1 /\ ~cface G0 x x0)
     ==> (!u. (cface G0 u b <=> cface G0 u v1) /\
              (cface G0 u a <=> cface G0 u u0) /\
              (cface G0 u b' <=> cface G0 u x0)) /\
         (!z. z IN D' /\ ~(z IN D)
              ==> (cface G0 v1 z <=> z = b) /\ (cface G0 x0 z <=> z = b') /\
                  (cface G0 u0 z <=> z = u0 \/ z = a) /\
                  (!x. MEM x r1 ==> ~cface G0 x z)) /\
         (!z. z IN D' /\ ~(z IN D)
              ==> fband G0 (v1 :: x0 :: r1) z \/ cface G0 z u0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONJ_TAC THENL [CFACE_TAC[]; CONJ_TAC THEN NEW_DARTS_TAC]);;

let RQS_PROPER_Y = prove
 (`!(G:(num)hypermap) x0 (G0:(num)hypermap) x00 k1 a1 q1 k2 a2 q2 k3 a3 q3 qs3.
     x0 IN dart G /\ proper_cpring G x0 /\ face_simple G (cpring G x0) /\
     injcp_ctx (ecpY G x0) (ecpY_pt G x0) G0 /\ x00 IN dart G0 /\
     rqs_proper G0 x00 (dart (ecpY G x0)) (cpring (ecpY G x0) (ecpY_pt G x0))
                (CONS (k1,a1,q1) (CONS (k2,a2,q2) (CONS (k3,a3,q3) qs3))) /\
     ~(cfquiz_Y (k1,a1,q1) (k2,a2,q2) (rqs_Y (k1,a1,q1) (k3,a3,q3) qs3) = [])
     ==> rqs_proper G0 x00 (dart G) (cpring G x0)
           (cfquiz_Y (k1,a1,q1) (k2,a2,q2) (rqs_Y (k1,a1,q1) (k3,a3,q3) qs3))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `G0:(num)hypermap`]
         ECPY_STEP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `G:(num)hypermap` HYPERMAP_LEMMA) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPY_FRESH) THEN
  ASM_REWRITE_TAC[ecpU_pt] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] HEAD_PROPER_CPRING) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `r1 = TL(TL(cpring (G:(num)hypermap) x0))` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CPRING_ECPY) THEN
  ASM_REWRITE_TAC[TL] THEN DISCH_TAC THEN
  ABBREV_TAC `a = FST(new_dart2(dart (G:(num)hypermap)))` THEN
  ABBREV_TAC `b = SND(new_dart2(dart (G:(num)hypermap)))` THEN
  ABBREV_TAC `u0 = ecpY_pt (G:(num)hypermap) x0` THEN
  ABBREV_TAC `b' = SND(new_dart2(dart(ecpU (G:(num)hypermap) x0)))` THEN
  ABBREV_TAC `v1 = node_map (G:(num)hypermap) x0` THEN
  (* The darts of ecpY G x0, all in G0; the old ring is v1 :: x0 :: r1.    *)
  SUBGOAL_THEN `!z. z IN dart (ecpY (G:(num)hypermap) x0) <=>
                    z = a \/ z = b \/ z = u0 \/ z = b' \/ z IN dart G`
    ASSUME_TAC THENL
   [GEN_TAC THEN ASM_SIMP_TAC[DART_ECPY_CASES; ecpU_pt] THEN
    REWRITE_TAC[DISJ_ACI];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!z. z IN dart (ecpY G x0) ==> z IN dart (G0:(num)hypermap)) /\
                (!x y. x IN dart G /\ y IN dart G
                       ==> (cface G0 x y <=> cface G x y))`
    (CONJUNCTS_THEN2 (LABEL_TAC "sub0") ASSUME_TAC) THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[injcp_ctx; SUBSET]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `a IN dart G0 /\ b IN dart G0 /\ u0 IN dart G0 /\
                b' IN dart G0 /\
                (!z. z IN dart G ==> z IN dart (G0:(num)hypermap))`
    STRIP_ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "sub0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v1:num) IN dart G /\ (!z. MEM z r1 ==> z IN dart G)`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "v1" THEN ASM_SIMP_TAC[NODE_FACE_IN_DART] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MEM_CPRING_IN_DART THEN
    EXISTS_TAC `x0:num` THEN ASM_REWRITE_TAC[MEM];
    ALL_TAC] THEN
  (* The old ring darts lie in distinct faces of G0, none the apex face.    *)
  SUBGOAL_THEN `~cface G0 (v1:num) x0 /\
                (!x. MEM x r1 ==> ~cface G0 x v1 /\ ~cface G0 x x0 /\
                                  ~cface G0 x u0)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `face_simple G (cpring (G:(num)hypermap) x0)` THEN
    ASM_REWRITE_TAC[face_simple; FBAND_CONS; FBAND_MEM_IFF] THEN
    MAP_EVERY UNDISCH_TAC
     [`!x y. x IN dart G /\ y IN dart G
             ==> (cface (G0:(num)hypermap) x y <=> cface G x y)`;
      `!u. u IN dart G ==> ~cface G0 u (u0:num)`;
      `!z. MEM z (r1:(num)list) ==> z IN dart (G:(num)hypermap)`;
      `(v1:num) IN dart G`; `(x0:num) IN dart G`] THEN
    MESON_TAC[CFACE_SYM_GEN];
    ALL_TAC] THEN
  (* The faces of the new darts.                                             *)
  MP_TAC(ISPECL [`G0:(num)hypermap`; `dart (G:(num)hypermap)`;
                 `dart (ecpY (G:(num)hypermap) x0)`; `x0:num`; `a:num`;
                 `b:num`; `u0:num`; `b':num`; `v1:num`; `r1:(num)list`]
         ECPY_NEW_FACES) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cf")
             (CONJUNCTS_THEN2 (LABEL_TAC "newcf") ASSUME_TAC)) THEN
  (* The arities in the sub-maps.                                            *)
  SUBGOAL_THEN
   `subarity G0 (dart (ecpY G x0)) b = subarity G0 (dart G) v1 + 1 /\
    subarity G0 (dart (ecpY G x0)) x0 = subarity G0 (dart G) x0 + 1 /\
    subarity G0 (dart (ecpY G x0)) u0 = 2 /\
    (!x. MEM x r1
         ==> subarity G0 (dart (ecpY G x0)) x = subarity G0 (dart G) x) /\
    arity G0 b = arity G0 v1 /\ arity G0 a = arity G0 u0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`G0:(num)hypermap`; `dart (ecpY (G:(num)hypermap) x0)`;
                     `b:num`; `v1:num`] SUBARITY_CFACE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC SUBARITY_INSERT THEN EXISTS_TAC `b:num`;
      MATCH_MP_TAC SUBARITY_INSERT THEN EXISTS_TAC `b':num`;
      MP_TAC(ISPECL [`G0:(num)hypermap`; `dart (G:(num)hypermap)`;
                     `dart (ecpY (G:(num)hypermap) x0)`; `u0:num`;
                     `[u0:num; a]`] SUBARITY_NEW_FACE) THEN
      REWRITE_TAC[LENGTH; ARITH] THEN DISCH_THEN MATCH_MP_TAC;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBARITY_SAME;
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC ARITY_CFACE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC ARITY_CFACE THEN ASM_REWRITE_TAC[]] THEN
    ASM_REWRITE_TAC[FINITE_DART; SUBSET; PAIRWISE; ALL; MEM] THEN
    REPEAT CONJ_TAC THEN TRY(GEN_TAC THEN ASM_SIMP_TAC[] THEN NO_TAC) THEN
    TRY(GEN_TAC THEN DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
        ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    NEWCF_TAC;
    ALL_TAC] THEN
  (* The old fit, and the new question q' at a = node v1.                    *)
  UNDISCH_TAC `rqs_proper G0 x00 (dart (ecpY G x0)) (cpring (ecpY G x0) u0)
               ((k1,a1,q1) :: (k2,a2,q2) :: (k3,a3,q3) :: qs3)` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
             MP_TAC(CONJUNCT1(REWRITE_RULE[rqs_proper] th))) THEN
  ASM_REWRITE_TAC[rqs_fit; FST; SND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `rqs_fit G0 (dart G) qs3 (r1:(num)list)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G0:(num)hypermap`; `dart (G:(num)hypermap)`;
                   `dart (ecpY (G:(num)hypermap) x0)`;
                   `qs3:(bool#num#question)list`; `r1:(num)list`]
           RQS_FIT_SUBARITY_CONG) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(k1,a1,q1):bool#num#question`;
                 `(k2,a2,q2):bool#num#question`;
                 `rqs_Y (k1,a1,q1) (k3,a3,q3) qs3`; `G0:(num)hypermap`;
                 `a:num`] CFQUIZ_Y_SPEC) THEN
  ASM_REWRITE_TAC[FST; SND] THEN
  DISCH_THEN(X_CHOOSE_THEN `q':question` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `walk_Y G0 a k2 a2 q1 q2 q'` THEN
  REWRITE_TAC[walk_Y; qstepR; qstepL] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
             (CONJUNCTS_THEN2 (LABEL_TAC "wband") ASSUME_TAC)) THEN
  (* The transfer.                                                           *)
  MP_TAC(ISPECL [`G0:(num)hypermap`; `x00:num`; `dart (G:(num)hypermap)`;
                 `dart (ecpY (G:(num)hypermap) x0)`; `(v1:num) :: x0 :: r1`;
                 `cpring (ecpY (G:(num)hypermap) x0) u0`;
                 `rqs_Y (k1,a1,q1) (k3,a3,q3) qs3 q'`;
                 `(k1,a1,q1) :: (k2,a2,q2) :: (k3,a3,q3) ::
                  (qs3:(bool#num#question)list)`;
                 `[]:(num)list`; `u0:num`] RQS_PROPER_STEP) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[rqs_Y; rqs_walk; FST; SND; MEM; LENGTH; face_simple;
              FBAND_NIL] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[SUBSET];
    ASM_REWRITE_TAC[SUBSET];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    REWRITE_TAC[MEM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    REWRITE_TAC[rqs_fit; FST; SND] THEN ASM_REWRITE_TAC[ADD1] THEN
    ARITH_TAC;
    X_GEN_TAC `u:num` THEN DISCH_TAC THEN
    USE_THEN "wband" (MP_TAC o SPEC `u:num`) THEN
    USE_THEN "cf" (MP_TAC o SPEC `u:num`) THEN
    REWRITE_TAC[ASSUME `(u:num) IN dart G0`; rqs_walk; FST; SND;
                FBAND_APPEND; FBAND_COND; FBAND_NIL] THEN
    CONV_TAC TAUT;
    REWRITE_TAC[rqs_walk; FST; SND; LENGTH_APPEND; LENGTH_COND_SING;
                LENGTH] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    X_GEN_TAC `u:num` THEN DISCH_TAC THEN
    USE_THEN "cf" (MP_TAC o SPEC `u:num`) THEN
    REWRITE_TAC[ASSUME `(u:num) IN dart G0`; FBAND_CONS; FBAND_NIL] THEN
    CONV_TAC TAUT;
    ASM_CASES_TAC `k2:bool` THENL
     [DISJ1_TAC THEN MATCH_MP_TAC FBAND_MEM THEN
      ASM_REWRITE_TAC[rqs_walk; FST; SND; MEM_APPEND; MEM_COND_SING; MEM];
      DISJ2_TAC THEN MATCH_MP_TAC NOT_BAD_RING_ARITY THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(a2 + 2) - 2 = a2` SUBST1_TAC THENL
       [ARITH_TAC; ASM_SIMP_TAC[]]]]);;

(* ------------------------------------------------------------------------- *)
(* The H-step question combination (Coq cfquiz_H, q11ok / q21ok): the two    *)
(* new questions q1' (at nv1) and q2' (at nv2) together walk q1 (from qstepR *)
(* nv1) and q2 (from qstepL nv2), plus one apex dart when k2; nv1 and nv2    *)
(* both lie in the apex face of u0.                                          *)
(* ------------------------------------------------------------------------- *)

let walk_H = new_definition
 `walk_H (H:(num)hypermap) (u0:num) (nv1:num) (nv2:num) (k2:bool) (a2:num)
         (q1:question) (q2:question) (q1':question) (q2':question) <=>
    ((fitq H nv1 q1' /\ fitq H nv2 q2') <=>
     (k2 ==> arity H u0 = a2 + 3) /\ fitq H (qstepR H nv1) q1 /\
     fitq H (qstepL H nv2) q2) /\
    (!u. u IN dart H
         ==> (fband H (walkq q1' H nv1) u \/ fband H (walkq q2' H nv2) u <=>
              (k2 /\ cface H u u0) \/ fband H (walkq q1 H (qstepR H nv1)) u \/
              fband H (walkq q2 H (qstepL H nv2)) u)) /\
    LENGTH (walkq q1' H nv1) + LENGTH (walkq q2' H nv2) =
      (if k2 then 1 else 0) + LENGTH (walkq q1 H (qstepR H nv1)) +
      LENGTH (walkq q2 H (qstepL H nv2))`;;
let WALK_H_PREP = prove
 (`!(H:(num)hypermap) u0 nv1 nv2.
     u0 IN dart H /\ cface H u0 nv1 /\ cface H u0 nv2
     ==> arity H nv1 = arity H u0 /\ arity H nv2 = arity H u0 /\
         (!u. u IN dart H
              ==> (cface H u nv1 <=> cface H u u0) /\
                  (cface H u nv2 <=> cface H u u0))`,
  REPEAT STRIP_TAC THEN
  TRY(MATCH_MP_TAC ARITY_CFACE THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ASM_MESON_TAC[CFACE_SYM_GEN; CFACE_TRANS]);;
let WALK_H_TAC =
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `u0:num`; `nv1:num`; `nv2:num`]
         WALK_H_PREP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[walk_H; fitq; flatq; walkq; MAP; CONS_11; FBAND_CONS; FBAND_NIL;
              LENGTH] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  (ARITH_TAC ORELSE
   (GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN REWRITE_TAC[DISJ_ACI] THEN
    NO_TAC) ORELSE
   MESON_TAC[]);;
let WALK_H_A = prove
 (`!(H:(num)hypermap) u0 nv1 nv2 a2 qa.
     (u0 IN dart H /\ cface H u0 nv1 /\ cface H u0 nv2) /\
     nat_of_qarity qa = a2 + 3
     ==> walk_H H u0 nv1 nv2 T a2 Qask0 Qask0 (Qask1 qa) Qask0`,
  WALK_H_TAC);;
let WALK_H_B = prove
 (`!(H:(num)hypermap) u0 nv1 nv2 a2 qa.
     (u0 IN dart H /\ cface H u0 nv1 /\ cface H u0 nv2) /\
     nat_of_qarity qa = a2 + 3
     ==> walk_H H u0 nv1 nv2 T a2 Qask0 Qask0 Qask0 (Qask1 qa)`,
  WALK_H_TAC);;
let WALK_H_C = prove
 (`!(H:(num)hypermap) u0 nv1 nv2 a2 qa q2.
     (u0 IN dart H /\ cface H u0 nv1 /\ cface H u0 nv2) /\
     nat_of_qarity qa = a2 + 3
     ==> walk_H H u0 nv1 nv2 T a2 Qask0 q2 Qask0 (QaskL qa q2)`,
  WALK_H_TAC);;
let WALK_H_D = prove
 (`!(H:(num)hypermap) u0 nv1 nv2 a2 qa q1.
     (u0 IN dart H /\ cface H u0 nv1 /\ cface H u0 nv2) /\
     nat_of_qarity qa = a2 + 3
     ==> walk_H H u0 nv1 nv2 T a2 q1 Qask0 (QaskR qa q1) Qask0`,
  WALK_H_TAC);;
let WALK_H_E = prove
 (`!(H:(num)hypermap) u0 nv1 nv2 a2.
     walk_H H u0 nv1 nv2 F a2 Qask0 Qask0 Qask0 Qask0`,
  REWRITE_TAC[walk_H; fitq; flatq; walkq; MAP; FBAND_NIL; LENGTH;
              ADD_CLAUSES]);;

(* The case analysis of cfquiz_H (Coq Dk2, q11ok / q21ok, case q1 / q2 / k1).*)
let CFQUIZ_H_SPEC = prove
 (`!rq1 rq2 (f:question->question->(bool#num#question)list)
    (H:(num)hypermap) u0 nv1 nv2.
     u0 IN dart H /\ cface H u0 nv1 /\ cface H u0 nv2 /\
     ~(cfquiz_H rq1 rq2 f = [])
     ==> ?q1' q2'. cfquiz_H rq1 rq2 f = f q1' q2' /\
                   (~FST rq2 ==> ~bad_ring_arity (SUC (FST(SND rq2)))) /\
                   walk_H H u0 nv1 nv2 (FST rq2) (FST(SND rq2)) (SND(SND rq1))
                          (SND(SND rq2)) q1' q2'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cfquiz_H; LET_DEF; LET_END_DEF] THEN
  ASM_CASES_TAC `FST (rq2:bool#num#question)` THEN ASM_REWRITE_TAC[] THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `nat_of_qarity
                  (small_qarity (SUC (FST(SND (rq2:bool#num#question))))) =
                  FST(SND rq2) + 3` ASSUME_TAC THENL
     [MP_TAC(SPEC `SUC (FST(SND (rq2:bool#num#question)))` SMALL_QARITYP) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
       [MAP_EVERY EXISTS_TAC
          [`Qask1 (small_qarity (SUC (FST(SND (rq2:bool#num#question)))))`;
           `SND(SND (rq2:bool#num#question))`] THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WALK_H_A THEN ASM_REWRITE_TAC[];
        MAP_EVERY EXISTS_TAC [`SND(SND (rq1:bool#num#question))`;
          `Qask1 (small_qarity (SUC (FST(SND (rq2:bool#num#question)))))`] THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WALK_H_B THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`SND(SND (rq1:bool#num#question))`;
                            `QaskL
                             (small_qarity
                             (SUC (FST(SND (rq2:bool#num#question)))))
                             (SND(SND rq2))`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WALK_H_C THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`QaskR
                           (small_qarity
                           (SUC (FST(SND (rq2:bool#num#question)))))
                           (SND(SND (rq1:bool#num#question)))`;
                          `SND(SND (rq2:bool#num#question))`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WALK_H_D THEN ASM_REWRITE_TAC[];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`SND(SND (rq1:bool#num#question))`;
                          `SND(SND (rq2:bool#num#question))`] THEN
    ASM_REWRITE_TAC[WALK_H_E]]);;
let RQS_FIT_REPLICATE = prove
 (`!(G0:(num)hypermap) p. (!x. MEM x p ==> x IN dart G0)
     ==> rqs_fit G0 (dart G0) (REPLICATE (LENGTH p) (F,0,Qask0)) p`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[LENGTH; REPLICATE; rqs_fit; FST; SND; ADD_CLAUSES; fitq; flatq;
               walkq; MAP; MEM; SUBARITY_DART]);;
let RQS_WALK_REPLICATE_NIL = prove
 (`!(G0:(num)hypermap) p.
     rqs_walk G0 (REPLICATE (LENGTH p) (F,0,Qask0)) p = []`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LENGTH; REPLICATE; rqs_walk; FST; SND; walkq; APPEND]);;

(* The initial invariant (Coq: rqs_proper (@injcp [::] cp) qs).              *)
let RQS_PROPER_INIT = prove
 (`!cp. config_prog cp
        ==> rqs_proper (FST(cpmap cp)) (SND(cpmap cp)) (dart (FST(cpmap cp)))
                       (cpring (FST(cpmap cp)) (SND(cpmap cp)))
                       (REPLICATE (cprsize cp) (F,0,Qask0))`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[rqs_proper; cprsize; RQS_WALK_REPLICATE_NIL; APPEND] THEN
  SUBGOAL_THEN `!x. MEM x (cpring (FST(cpmap cp)) (SND(cpmap cp)))
                ==> x IN dart (FST(cpmap cp))` ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM_CPRING_IN_DART; CPMAP_PT_IN_DART]; ALL_TAC] THEN
  ASM_SIMP_TAC[RQS_FIT_REPLICATE] THEN
  MP_TAC(SPEC `cp:(cpstep)list` CPMAP_SIMPLE) THEN
  ASM_REWRITE_TAC[FACE_SIMPLE_APPEND'] THEN ASM_MESON_TAC[]);;
let QS_TRIPLE = prove
 (`!rq:bool#num#question. ?k a q. rq = (k,a,q)`,
  GEN_TAC THEN
  MAP_EVERY EXISTS_TAC [`FST (rq:bool#num#question)`;
                        `FST(SND (rq:bool#num#question))`;
                        `SND(SND (rq:bool#num#question))`] THEN
  REWRITE_TAC[PAIR]);;
let CFQUIZ_REC_BASE_QUIZ = prove
 (`!k1 a1 q1 k2 a2 q2.
     isQuizR (cfquiz_rec [] [(k1,a1,q1); (k2,a2,q2)])
     ==> k1 /\ k2 /\ nat_of_qarity (large_qarity (a1 - 1)) = a1 + 1 /\
         nat_of_qarity (small_qarity (a2 - 1)) = a2 + 1 /\
         cfquiz_rec [] [(k1,a1,q1); (k2,a2,q2)] =
         Quiz (QaskR (large_qarity (a1 - 1)) q2)
              (QaskR (small_qarity (a2 - 1)) q1)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[cfquiz_rec; LENGTH; HD; TL; ARITH_RULE `~(SUC(SUC 0) < 2)`] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[FST; SND] THEN
  COND_CASES_TAC THEN REWRITE_TAC[ISQUIZR_NOQUIZ] THEN COND_CASES_TAC THEN
  REWRITE_TAC[ISQUIZR_NOQUIZ] THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `a2 = 0` THENL
   [UNDISCH_TAC `~bad_small_arity (small_qarity (a2 - 1))` THEN
    ASM_REWRITE_TAC[SUB_0; small_qarity] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[bad_small_arity];
    MP_TAC(SPEC `a2 - 1` SMALL_QARITYP) THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC]);;
let SUBARITY_FULL = prove
 (`!(G0:(num)hypermap) D x. (!z. cface G0 x z ==> z IN D)
                            ==> subarity G0 D x = arity G0 x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[subarity; ARITY_CARD_CFACE] THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

(* The G0-level geometry of an H step at x0 (Coq en_v1, enn_v2, nu0Fv1 ...): *)
(* new darts a, b (ecpU), a' = ecpY_pt, b' (ecpY), u0 = ecpH_pt (apex), b'' =*)
(* SND(new_dart2(dart(ecpY G x0))); v1 = node x0, v3 = face (edge x0);       *)
(* cpring G x0 = v1 :: x0 :: v3 :: r1, cpring (ecpH G x0) u0 = b :: u0 :: v3 *)
(* :: r1; in the full map node v1 = a, edge a = b, node x0 = a', node a' =   *)
(* b'', edge b'' = u0; b ~ v1, u0 ~ a ~ a', b' ~ x0, b'' ~ v3.               *)
let ECPH_STEP_FACTS = prove
 (`!(G:(num)hypermap) x0 (G0:(num)hypermap).
     x0 IN dart G /\ proper_cpring G x0 /\ long_cpring G x0 /\
     plain_hypermap G /\ face_simple G (cpring G x0) /\
     injcp_ctx (ecpH G x0) (ecpH_pt G x0) G0
     ==> injcp_ctx G x0 G0 /\
         node_map G0 (node_map G x0) = FST(new_dart2(dart G)) /\
         edge_map G0 (FST(new_dart2(dart G))) = SND(new_dart2(dart G)) /\
         node_map G0 x0 = ecpY_pt G x0 /\
         node_map G0 (ecpY_pt G x0) = SND(new_dart2(dart(ecpY G x0))) /\
         edge_map G0 (SND(new_dart2(dart(ecpY G x0)))) = ecpH_pt G x0 /\
         cface G0 (SND(new_dart2(dart G))) (node_map G x0) /\
         cface G0 (ecpH_pt G x0) (FST(new_dart2(dart G))) /\
         cface G0 (ecpH_pt G x0) (ecpY_pt G x0) /\
         cface G0 (SND(new_dart2(dart(ecpU G x0)))) x0 /\
         cface G0 (SND(new_dart2(dart(ecpY G x0))))
                  (face_map G (edge_map G x0)) /\
         (!u. u IN dart G ==> ~cface G0 u (ecpH_pt G x0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `G:(num)hypermap` HYPERMAP_LEMMA) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPY_FRESH) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPH_FRESH) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPH_FRESH2) THEN
  ASM_REWRITE_TAC[ecpU_pt] THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] INJCP_CTX_H) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `injcp_ctx G x0 (G0:(num)hypermap)` ASSUME_TAC THENL
   [MATCH_MP_TAC INJCP_CTX_TRANS THEN
    MAP_EVERY EXISTS_TAC
      [`ecpH (G:(num)hypermap) x0`; `ecpH_pt (G:(num)hypermap) x0`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] HEAD_LONG_CPRING) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `r1 = TL(TL(TL(cpring (G:(num)hypermap) x0)))` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CPRING_ECPY) THEN
  ASM_REWRITE_TAC[TL] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CPRING_ECPH) THEN
  ASM_SIMP_TAC[NODE_ECPY_PT_VALUE; TL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `node_map G x0 IN dart (G:(num)hypermap) /\
                face_map G (edge_map G x0) IN dart G /\ ~(node_map G x0 = x0)
                /\ ~(node_map G x0 = face_map G (edge_map G x0)) /\
                ~(x0 = face_map G (edge_map G x0)) /\ ~MEM (node_map G x0)
                (r1:(num)list) /\ ~MEM x0 r1 /\
                ~MEM (face_map G (edge_map G x0)) r1 /\
                (!z. MEM z r1 ==> z IN dart G)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[NODE_FACE_IN_DART; EDGE_IN_DART] THEN
    UNDISCH_TAC `face_simple G (cpring (G:(num)hypermap) x0)` THEN
    UNDISCH_TAC `proper_cpring (G:(num)hypermap) x0` THEN
    UNDISCH_TAC `long_cpring (G:(num)hypermap) x0` THEN
    ASM_REWRITE_TAC[face_simple; FBAND_CONS; proper_cpring; long_cpring] THEN
    REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[];
      ASM_MESON_TAC[];
      ASM_MESON_TAC[CFACE_REFL];
      ASM_MESON_TAC[FBAND_MEM];
      ASM_MESON_TAC[FBAND_MEM];
      ASM_MESON_TAC[FBAND_MEM];
      MATCH_MP_TAC MEM_CPRING_IN_DART THEN EXISTS_TAC `x0:num` THEN
      ASM_REWRITE_TAC[MEM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `FST(new_dart2(dart G)) IN dart (ecpH (G:(num)hypermap) x0) /\
                SND(new_dart2(dart G)) IN dart (ecpH G x0) /\
                ecpY_pt G x0 IN dart (ecpH G x0) /\
                SND(new_dart2(dart(ecpU G x0))) IN dart (ecpH G x0) /\
                ecpH_pt G x0 IN dart (ecpH G x0) /\
                SND(new_dart2(dart(ecpY G x0))) IN dart (ecpH G x0) /\
                node_map G x0 IN dart (ecpH G x0) /\ x0 IN dart (ecpH G x0) /\
                face_map G (edge_map G x0) IN dart (ecpH G x0) /\
                node_map G x0 IN dart (ecpY G x0) /\ ecpY_pt G x0 IN dart
                (ecpY G x0)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[DART_ECPH_CASES; DART_ECPY_CASES; ecpU_pt]; ALL_TAC] THEN
  SUBGOAL_THEN `~MEM (node_map G x0)
                (cpring (ecpY (G:(num)hypermap) x0) (ecpY_pt G x0)) /\
                ~MEM (node_map G x0) (cpring (ecpH G x0) (ecpH_pt G x0)) /\
                ~MEM x0 (cpring (ecpH G x0) (ecpH_pt G x0)) /\
                ~MEM (ecpY_pt G x0) (cpring (ecpH G x0) (ecpH_pt G x0))`
    STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MEM; DE_MORGAN_THM] THEN REPEAT CONJ_TAC THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `injcp_ctx (ecpH G x0) (ecpH_pt G x0) (G0:(num)hypermap)` THEN
  REWRITE_TAC[injcp_ctx] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] NODE_ECPY_3CYCLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] NODE_ECPH_3CYCLE) THEN
  ASM_SIMP_TAC[ECPY_FACE_EDGE_PT] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] EDGE_ECPH_ECPUPT) THEN
  ASM_REWRITE_TAC[ecpU_pt] THEN DISCH_TAC THEN
  SUBGOAL_THEN `node_map (ecpH G x0) (node_map G x0) =
                FST(new_dart2(dart (G:(num)hypermap)))` ASSUME_TAC THENL
   [MP_TAC(ISPECL
           [`G:(num)hypermap`; `x0:num`; `node_map (G:(num)hypermap) x0`]
           NODE_ECPH_ECPY_OFF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`ecpY (G:(num)hypermap) x0`; `ecpY_pt (G:(num)hypermap) x0`;
                   `node_map (G:(num)hypermap) x0`] MEM_CPRING) THEN
    ASM_REWRITE_TAC[cnode; node] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] EDGE_ECPH_B) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `node_map G0 (node_map G x0) =
                FST(new_dart2(dart (G:(num)hypermap))) /\
                edge_map G0 (FST(new_dart2(dart G))) = SND(new_dart2(dart G))
                /\ node_map G0 x0 = ecpY_pt G x0 /\ node_map G0 (ecpY_pt G x0)
                = SND(new_dart2(dart(ecpY G x0))) /\
                edge_map G0 (SND(new_dart2(dart(ecpY G x0)))) = ecpH_pt G x0`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPH_B_NODE) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPH_APEX_YA) THEN
    ASM_REWRITE_TAC[ecpU_pt] THEN SIMP_TAC[];
    MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPH_APEX_YA) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPH_BPRIME) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPH_B_PT) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `u:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(u:num) IN dart (ecpH G x0)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] DART_SUBSET_ECPH) THEN
      ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `u:num`]
           CFACE_ECPH_APEX_OLD) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[CFACE_SYM_GEN]]);;

(* ------------------------------------------------------------------------- *)
(* The CpH step of Coq cfquizP: rqs_proper transfers from (ecpH G x0, rq1 :: *)
(* rq2 :: rq3 :: qs3) to (G, cfquiz_H rq1 rq2 (rqs_H rq1 rq3 qs3)).  The new *)
(* ring dart x0 carries the kernel question (T, 1, q2') rooted at a' = node  *)
(* G0 x0; its G0-face lies inside ecpH G x0 (clause 4 of the old invariant), *)
(* so arity G0 x0 = subarity (dart (ecpH G x0)) x0 = subarity (dart G) x0 +  *)
(* 1 (Coq nFv2).  The old walk gains exactly the dart x0.                    *)
(* ------------------------------------------------------------------------- *)

(* The faces in G0 of the darts a, b, a', b', u0, b'' added by an H step: b, *)
(* b' and b'' join the faces of the ring darts v1, x0 and v3, a and a' the   *)
(* apex face of u0, which holds no old dart; x0 leaves the ring.             *)
let ECPH_NEW_FACES = prove
 (`!(G0:(num)hypermap) D D' x0 a b a' b' u0 b'' v1 v3 r1.
     (!z. z IN D' <=> z = a \/ z = b \/ z = a' \/ z = b' \/ z = u0 \/
                      z = b'' \/ z IN D) /\
     ~(a IN D) /\ ~(b IN D) /\ ~(a' IN D) /\ ~(b' IN D) /\ ~(u0 IN D) /\
     ~(b'' IN D) /\
     ~(a = b) /\ ~(a' = a) /\ ~(a' = b) /\ ~(b' = a) /\ ~(b' = b) /\
     ~(a' = b') /\ ~(u0 = b) /\ ~(u0 = a') /\ ~(u0 = a) /\ ~(u0 = b') /\
     ~(b'' = b) /\ ~(b'' = a') /\ ~(b'' = a) /\ ~(b'' = b') /\ ~(u0 = b'') /\
     cface G0 b v1 /\ cface G0 u0 a /\ cface G0 u0 a' /\ cface G0 b' x0 /\
     cface G0 b'' v3 /\
     (!u. u IN D ==> ~cface G0 u u0) /\ v1 IN D /\ x0 IN D /\ v3 IN D /\
     ~cface G0 v1 x0 /\ ~cface G0 v1 v3 /\ ~cface G0 x0 v3 /\
     (!x. MEM x r1 ==> x IN D /\ ~cface G0 x v1 /\ ~cface G0 x x0 /\
                       ~cface G0 x v3)
     ==> (!u. (cface G0 u b <=> cface G0 u v1) /\
              (cface G0 u a <=> cface G0 u u0) /\
              (cface G0 u a' <=> cface G0 u u0) /\
              (cface G0 u b' <=> cface G0 u x0) /\
              (cface G0 u b'' <=> cface G0 u v3)) /\
         (!z. z IN D' /\ ~(z IN D)
              ==> (cface G0 v1 z <=> z = b) /\ (cface G0 x0 z <=> z = b') /\
                  (cface G0 v3 z <=> z = b'') /\
                  (cface G0 u0 z <=> z = u0 \/ z = a' \/ z = a) /\
                  (!x. MEM x r1 ==> ~cface G0 x z)) /\
         (!z. z IN D' /\ ~(z IN D)
              ==> fband G0 (v1 :: x0 :: v3 :: r1) z \/ cface G0 z u0) /\
         ~fband G0 (b :: u0 :: v3 :: r1) x0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [CFACE_TAC[]; NEW_DARTS_TAC; NEW_DARTS_TAC;
    REWRITE_TAC[FBAND_CONS] THEN
    REWRITE_TAC[FBAND_MEM_IFF; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
    REPEAT CONJ_TAC THEN TRY(CFACE_TAC[] THEN NO_TAC) THEN
    ASM_MESON_TAC[CFACE_SYM_GEN]]);;

let RQS_PROPER_H = prove
 (`!(G:(num)hypermap) x0 (G0:(num)hypermap) x00 k1 a1 q1 k2 a2 q2 k3 a3 q3 qs3.
     x0 IN dart G /\ proper_cpring G x0 /\ long_cpring G x0 /\
     plain_hypermap G /\ face_simple G (cpring G x0) /\
     injcp_ctx (ecpH G x0) (ecpH_pt G x0) G0 /\ x00 IN dart G0 /\
     rqs_proper G0 x00 (dart (ecpH G x0)) (cpring (ecpH G x0) (ecpH_pt G x0))
                (CONS (k1,a1,q1) (CONS (k2,a2,q2) (CONS (k3,a3,q3) qs3))) /\
     ~(cfquiz_H (k1,a1,q1) (k2,a2,q2) (rqs_H (k1,a1,q1) (k3,a3,q3) qs3) = [])
     ==> rqs_proper G0 x00 (dart G) (cpring G x0)
           (cfquiz_H (k1,a1,q1) (k2,a2,q2) (rqs_H (k1,a1,q1) (k3,a3,q3) qs3))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `G0:(num)hypermap`]
         ECPH_STEP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `G:(num)hypermap` HYPERMAP_LEMMA) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPY_FRESH) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPH_FRESH) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPH_FRESH2) THEN
  ASM_REWRITE_TAC[ecpU_pt] THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] HEAD_LONG_CPRING) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `r1 = TL(TL(TL(cpring (G:(num)hypermap) x0)))` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CPRING_ECPH) THEN
  ASM_SIMP_TAC[NODE_ECPY_PT_VALUE; TL] THEN DISCH_TAC THEN
  ABBREV_TAC `a = FST(new_dart2(dart (G:(num)hypermap)))` THEN
  ABBREV_TAC `b = SND(new_dart2(dart (G:(num)hypermap)))` THEN
  ABBREV_TAC `a' = ecpY_pt (G:(num)hypermap) x0` THEN
  ABBREV_TAC `b' = SND(new_dart2(dart(ecpU (G:(num)hypermap) x0)))` THEN
  ABBREV_TAC `u0 = ecpH_pt (G:(num)hypermap) x0` THEN
  ABBREV_TAC `b'' = SND(new_dart2(dart(ecpY (G:(num)hypermap) x0)))` THEN
  ABBREV_TAC `v1 = node_map (G:(num)hypermap) x0` THEN
  ABBREV_TAC `v3 = face_map (G:(num)hypermap) (edge_map G x0)` THEN
  (* The darts of ecpH G x0, all in G0; the old ring is                     *)
  (* v1 :: x0 :: v3 :: r1.                                                   *)
  SUBGOAL_THEN `!z. z IN dart (ecpH (G:(num)hypermap) x0) <=>
                    z = a \/ z = b \/ z = a' \/ z = b' \/ z = u0 \/ z = b'' \/
                    z IN dart G`
    ASSUME_TAC THENL
   [GEN_TAC THEN ASM_SIMP_TAC[DART_ECPH_CASES; DART_ECPY_CASES; ecpU_pt] THEN
    REWRITE_TAC[DISJ_ACI];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!z. z IN dart (ecpH G x0) ==> z IN dart (G0:(num)hypermap)) /\
                (!x y. x IN dart G /\ y IN dart G
                       ==> (cface G0 x y <=> cface G x y))`
    (CONJUNCTS_THEN2 (LABEL_TAC "sub0") ASSUME_TAC) THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[injcp_ctx; SUBSET]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `a IN dart G0 /\ b IN dart G0 /\ a' IN dart G0 /\
                b' IN dart G0 /\ u0 IN dart G0 /\ b'' IN dart G0 /\
                x0 IN dart G0 /\
                (!z. z IN dart G ==> z IN dart (G0:(num)hypermap))`
    STRIP_ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "sub0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v1:num) IN dart G /\ (v3:num) IN dart G /\
                (!z. MEM z r1 ==> z IN dart G)`
    STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["v1"; "v3"] THEN
    ASM_SIMP_TAC[NODE_FACE_IN_DART; EDGE_IN_DART] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MEM_CPRING_IN_DART THEN
    EXISTS_TAC `x0:num` THEN ASM_REWRITE_TAC[MEM];
    ALL_TAC] THEN
  (* The old ring darts lie in distinct faces of G0, none the apex face.    *)
  SUBGOAL_THEN `~cface G0 (v1:num) x0 /\ ~cface G0 v1 v3 /\ ~cface G0 x0 v3 /\
                (!x. MEM x r1 ==> ~cface G0 x v1 /\ ~cface G0 x x0 /\
                                  ~cface G0 x v3 /\ ~cface G0 x u0)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `face_simple G (cpring (G:(num)hypermap) x0)` THEN
    ASM_REWRITE_TAC[face_simple; FBAND_CONS; FBAND_MEM_IFF] THEN
    MAP_EVERY UNDISCH_TAC
     [`!x y. x IN dart G /\ y IN dart G
             ==> (cface (G0:(num)hypermap) x y <=> cface G x y)`;
      `!u. u IN dart G ==> ~cface G0 u (u0:num)`;
      `!z. MEM z (r1:(num)list) ==> z IN dart (G:(num)hypermap)`;
      `(v1:num) IN dart G`; `(x0:num) IN dart G`;
      `(v3:num) IN dart G`] THEN
    MESON_TAC[CFACE_SYM_GEN];
    ALL_TAC] THEN
  (* The faces of the new darts.                                             *)
  MP_TAC(ISPECL [`G0:(num)hypermap`; `dart (G:(num)hypermap)`;
                 `dart (ecpH (G:(num)hypermap) x0)`; `x0:num`; `a:num`;
                 `b:num`; `a':num`; `b':num`; `u0:num`; `b'':num`; `v1:num`;
                 `v3:num`; `r1:(num)list`] ECPH_NEW_FACES) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cf")
             (CONJUNCTS_THEN2 (LABEL_TAC "newcf") STRIP_ASSUME_TAC)) THEN
  (* The arities in the sub-maps.                                            *)
  SUBGOAL_THEN
   `subarity G0 (dart (ecpH G x0)) b = subarity G0 (dart G) v1 + 1 /\
    subarity G0 (dart (ecpH G x0)) x0 = subarity G0 (dart G) x0 + 1 /\
    subarity G0 (dart (ecpH G x0)) v3 = subarity G0 (dart G) v3 + 1 /\
    subarity G0 (dart (ecpH G x0)) u0 = 3 /\
    (!x. MEM x r1
         ==> subarity G0 (dart (ecpH G x0)) x = subarity G0 (dart G) x) /\
    arity G0 b = arity G0 v1 /\ arity G0 a = arity G0 u0 /\
    arity G0 a' = arity G0 u0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`G0:(num)hypermap`; `dart (ecpH (G:(num)hypermap) x0)`;
                     `b:num`; `v1:num`] SUBARITY_CFACE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC SUBARITY_INSERT THEN EXISTS_TAC `b:num`;
      MATCH_MP_TAC SUBARITY_INSERT THEN EXISTS_TAC `b':num`;
      MATCH_MP_TAC SUBARITY_INSERT THEN EXISTS_TAC `b'':num`;
      MP_TAC(ISPECL [`G0:(num)hypermap`; `dart (G:(num)hypermap)`;
                     `dart (ecpH (G:(num)hypermap) x0)`; `u0:num`;
                     `[u0:num; a'; a]`] SUBARITY_NEW_FACE) THEN
      REWRITE_TAC[LENGTH; ARITH] THEN DISCH_THEN MATCH_MP_TAC;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBARITY_SAME;
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC ARITY_CFACE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC ARITY_CFACE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC ARITY_CFACE THEN ASM_REWRITE_TAC[]] THEN
    ASM_REWRITE_TAC[FINITE_DART; SUBSET; PAIRWISE; ALL; MEM] THEN
    REPEAT CONJ_TAC THEN TRY(GEN_TAC THEN ASM_SIMP_TAC[] THEN NO_TAC) THEN
    TRY(GEN_TAC THEN DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
        ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    NEWCF_TAC;
    ALL_TAC] THEN
  (* The old fit; x0 leaves the ring and becomes a kernel dart whose face    *)
  (* lies inside ecpH G x0, so its sub-map arity is its arity in G0.         *)
  UNDISCH_TAC `rqs_proper G0 x00 (dart (ecpH G x0)) (cpring (ecpH G x0) u0)
               ((k1,a1,q1) :: (k2,a2,q2) :: (k3,a3,q3) :: qs3)` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    LABEL_TAC "bandO" (last(CONJUNCTS(REWRITE_RULE[rqs_proper] th))) THEN
    MP_TAC(CONJUNCT1(REWRITE_RULE[rqs_proper] th))) THEN
  ASM_REWRITE_TAC[rqs_fit; FST; SND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `rqs_fit G0 (dart G) qs3 (r1:(num)list)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G0:(num)hypermap`; `dart (G:(num)hypermap)`;
                   `dart (ecpH (G:(num)hypermap) x0)`;
                   `qs3:(bool#num#question)list`; `r1:(num)list`]
           RQS_FIT_SUBARITY_CONG) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~fband G0 (cpring (ecpH G x0) u0) (x0:num)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `~fband G0 (APPEND (rqs_walk G0 ((k1,a1,q1) :: (k2,a2,q2) :: (k3,a3,q3) ::
                                    qs3) (cpring (ecpH G x0) u0))
                      (cpring G0 x00)) (x0:num)`
    ASSUME_TAC THENL
   [USE_THEN "bandO" (MP_TAC o SPEC `x0:num`) THEN
    REWRITE_TAC[ASSUME `(x0:num) IN dart G0`;
                ASSUME `~fband G0 (cpring (ecpH G x0) u0) (x0:num)`] THEN
    MATCH_MP_TAC(TAUT `b ==> (a <=> ~b) ==> ~a`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `arity G0 (x0:num) = subarity G0 (dart (ecpH G x0)) x0`
    ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUBARITY_FULL THEN
    X_GEN_TAC `z:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:num) IN dart G0` ASSUME_TAC THENL
     [MATCH_MP_TAC CFT_DART THEN EXISTS_TAC `x0:num` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "bandO" (MP_TAC o SPEC `z:num`) THEN
    REWRITE_TAC[ASSUME `(z:num) IN dart G0`] THEN
    MATCH_MP_TAC(TAUT `~a ==> (a <=> ~b \/ c) ==> b`) THEN
    DISCH_TAC THEN
    UNDISCH_TAC `~fband G0 (APPEND (rqs_walk G0 ((k1,a1,q1) :: (k2,a2,q2) ::
                                    (k3,a3,q3) :: qs3) (cpring (ecpH G x0) u0))
                      (cpring G0 x00)) (x0:num)` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC FBAND_CFACE THEN EXISTS_TAC `z:num` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CFACE_SYM_GEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* The new questions q1' at a and q2' at a', both in the apex face.        *)
  MP_TAC(ISPECL [`(k1,a1,q1):bool#num#question`;
                 `(k2,a2,q2):bool#num#question`;
                 `rqs_H (k1,a1,q1) (k3,a3,q3) qs3`; `G0:(num)hypermap`;
                 `u0:num`; `a:num`; `a':num`] CFQUIZ_H_SPEC) THEN
  ASM_REWRITE_TAC[FST; SND] THEN
  DISCH_THEN(X_CHOOSE_THEN `q1':question`
             (X_CHOOSE_THEN `q2':question` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `walk_H G0 u0 a a' k2 a2 q1 q2 q1' q2'` THEN
  REWRITE_TAC[walk_H; qstepR; qstepL] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
             (CONJUNCTS_THEN2 (LABEL_TAC "wband") ASSUME_TAC)) THEN
  (* The transfer, with E = [x0].                                            *)
  MP_TAC(ISPECL [`G0:(num)hypermap`; `x00:num`; `dart (G:(num)hypermap)`;
                 `dart (ecpH (G:(num)hypermap) x0)`;
                 `(v1:num) :: x0 :: v3 :: r1`;
                 `cpring (ecpH (G:(num)hypermap) x0) u0`;
                 `rqs_H (k1,a1,q1) (k3,a3,q3) qs3 q1' q2'`;
                 `(k1,a1,q1) :: (k2,a2,q2) :: (k3,a3,q3) ::
                  (qs3:(bool#num#question)list)`;
                 `[x0:num]`; `u0:num`] RQS_PROPER_STEP) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[rqs_H; rqs_walk; FST; SND; MEM; LENGTH; face_simple;
              FBAND_NIL] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[SUBSET];
    ASM_REWRITE_TAC[SUBSET];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    REWRITE_TAC[MEM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[rqs_fit; FST; SND] THEN ASM_REWRITE_TAC[ADD1] THEN ARITH_TAC;
    X_GEN_TAC `u:num` THEN DISCH_TAC THEN
    USE_THEN "wband" (MP_TAC o SPEC `u:num`) THEN
    USE_THEN "cf" (MP_TAC o SPEC `u:num`) THEN
    REWRITE_TAC[ASSUME `(u:num) IN dart G0`; rqs_walk; FST; SND;
                FBAND_APPEND; FBAND_COND; FBAND_NIL; FBAND_CONS] THEN
    CONV_TAC TAUT;
    REWRITE_TAC[rqs_walk; FST; SND; LENGTH_APPEND; LENGTH_COND_SING;
                LENGTH] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      free_in `LENGTH (walkq (q1':question) G0 (a:num))` (concl th))) THEN
    ARITH_TAC;
    GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `~fband G0 (APPEND (rqs_walk G0 ((k1,a1,q1) :: (k2,a2,q2) ::
                                    (k3,a3,q3) :: qs3) (cpring (ecpH G x0) u0))
                      (cpring G0 x00)) (x0:num)` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `u:num` THEN DISCH_TAC THEN
    USE_THEN "cf" (MP_TAC o SPEC `u:num`) THEN
    REWRITE_TAC[ASSUME `(u:num) IN dart G0`; FBAND_CONS; FBAND_NIL] THEN
    CONV_TAC TAUT;
    ASM_CASES_TAC `k2:bool` THENL
     [DISJ1_TAC THEN MATCH_MP_TAC FBAND_MEM THEN
      ASM_REWRITE_TAC[rqs_walk; FST; SND; MEM_APPEND; MEM_COND_SING; MEM];
      DISJ2_TAC THEN MATCH_MP_TAC NOT_BAD_RING_ARITY THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(a2 + 3) - 2 = SUC a2` SUBST1_TAC THENL
       [ARITH_TAC; ASM_SIMP_TAC[]]]]);;

(* ------------------------------------------------------------------------- *)
(* cfquizP, base case: on the two-dart base map cpmap0 (ring [0; 1]) the two *)
(* ring questions give the quiz Quiz (QaskR qa1 q2) (QaskR qa2 q1) rooted at *)
(* dart 0; the invariant yields the good ring arities (simplicity of walk ++ *)
(* ring forbids ring darts in the faces of 0 and 1) and the valid quiz.      *)
(* ------------------------------------------------------------------------- *)

let CFQUIZ_REC_BASE = prove
 (`!(G0:(num)hypermap) x00 k1 a1 q1 k2 a2 q2.
     x00 IN dart G0 /\ injcp_ctx cpmap0 1 G0 /\
     rqs_proper G0 x00 (dart cpmap0) (cpring cpmap0 1)
                [(k1,a1,q1); (k2,a2,q2)] /\
     isQuizR (cfquiz_rec [] [(k1,a1,q1); (k2,a2,q2)])
     ==> (!w. MEM w (cpring G0 x00) ==> good_ring_arity G0 w) /\
         (?x0. x0 IN dart G0 /\
               valid_quiz G0 (cpring G0 x00) x0
                          (cfquiz_rec [] [(k1,a1,q1); (k2,a2,q2)]))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP CFQUIZ_REC_BASE_QUIZ) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
                                         (CONJUNCTS_THEN2 ASSUME_TAC
                                          (CONJUNCTS_THEN2 ASSUME_TAC
                                           SUBST1_TAC)))) THEN
  UNDISCH_TAC `rqs_proper G0 x00 (dart cpmap0) (cpring cpmap0 1)
               [(k1,a1,q1); (k2,a2,q2)]` THEN
  ASM_REWRITE_TAC[rqs_proper; rqs_fit; rqs_walk; CPRING_CPMAP0;
                  CPMAP0_COMPONENTS; FST; SND; APPEND; APPEND_NIL] THEN
  STRIP_TAC THEN UNDISCH_TAC `injcp_ctx cpmap0 1 (G0:(num)hypermap)` THEN
  REWRITE_TAC[injcp_ctx; CPMAP0_COMPONENTS; SUBSET; IN_INSERT;
              NOT_IN_EMPTY] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `0 IN dart (G0:(num)hypermap) /\ 1 IN dart G0 /\
                edge_map G0 0 = 1 /\ edge_map G0 1 = 0 /\ ~cface G0 0 1 /\
                ~cface G0 1 0 /\ node_map G0 0 IN dart G0 /\
                node_map G0 1 IN dart G0` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[swap; ARITH_EQ; CFACE_CPMAP0] THEN
    ASM_MESON_TAC[NODE_MAP_PERMUTES; PERMUTES_IN_IMAGE];
    ALL_TAC] THEN
  ABBREV_TAC `W1 = walkq q1 (G0:(num)hypermap) (node_map G0 0)` THEN
  ABBREV_TAC `W2 = walkq q2 (G0:(num)hypermap) (node_map G0 1)` THEN
  ABBREV_TAC `r0 = cpring (G0:(num)hypermap) x00` THEN
  SUBGOAL_THEN `0 :: APPEND (APPEND W1 (1 :: W2)) r0 = APPEND
                (0 :: APPEND W1 (1 :: (W2:(num)list))) r0`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[APPEND]; ALL_TAC] THEN
  ABBREV_TAC `W = 0 :: APPEND W1 (1 :: (W2:(num)list))` THEN
  SUBGOAL_THEN `!z. MEM z (r0:(num)list) ==> z IN dart (G0:(num)hypermap)`
    ASSUME_TAC THENL
   [EXPAND_TAC "r0" THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MEM_CPRING_IN_DART THEN EXISTS_TAC `x00:num` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!z. MEM z (W1:(num)list) ==> z IN dart (G0:(num)hypermap)) /\
                (!z. MEM z (W2:(num)list) ==> z IN dart G0)`
    STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["W1"; "W2"] THEN
    MP_TAC(ISPECL [`q1:question`; `G0:(num)hypermap`; `node_map G0 0`]
           WALKQ_MEM_DART) THEN
    MP_TAC(ISPECL [`q2:question`; `G0:(num)hypermap`; `node_map G0 1`]
           WALKQ_MEM_DART) THEN
    ASM_REWRITE_TAC[GSYM ALL_MEM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. MEM z (W:(num)list) ==> z IN dart (G0:(num)hypermap)`
    ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[MEM; MEM_APPEND] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `face_simple (G0:(num)hypermap) W /\ face_simple G0 r0 /\
                (!x. MEM x (W:(num)list) ==> ~fband G0 r0 x)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `face_simple G0 (APPEND (W:(num)list) r0)` THEN
    REWRITE_TAC[FACE_SIMPLE_APPEND'];
    ALL_TAC] THEN
  SUBGOAL_THEN `~fband (G0:(num)hypermap) r0 0 /\ ~fband G0 r0 1`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "W" THEN
    REWRITE_TAC[MEM; MEM_APPEND];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `subarity G0 {0,1} 0 = 1 /\ subarity (G0:(num)hypermap) {0,1} 1 = 1`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[subarity] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `{z | z IN {0,1} /\ cface (G0:(num)hypermap) 0 z} = {0}`
        SUBST1_TAC;
      SUBGOAL_THEN `{z | z IN {0,1} /\ cface (G0:(num)hypermap) 1 z} = {1}`
        SUBST1_TAC] THEN
    REWRITE_TAC[CARD_SING] THEN
    REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM] THEN
    X_GEN_TAC `z:num` THEN ASM_CASES_TAC `z = 0` THEN
    ASM_REWRITE_TAC[CFACE_REFL] THEN ASM_CASES_TAC `z = 1` THEN
    ASM_REWRITE_TAC[CFACE_REFL; ARITH_EQ];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `w:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> free_in
      `good_ring_arity:(num)hypermap->num->bool` (concl th))) THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; FBAND_CONS; FBAND_NIL;
                    DE_MORGAN_THM] THEN
    SUBGOAL_THEN `(w:num) IN dart G0` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~fband (G0:(num)hypermap) r0 0` THEN
    UNDISCH_TAC `~fband (G0:(num)hypermap) r0 1` THEN
    REWRITE_TAC[FBAND_MEM_IFF] THEN UNDISCH_TAC `MEM (w:num) r0` THEN
    UNDISCH_TAC `(w:num) IN dart G0` THEN MESON_TAC[CFACE_SYM; CFACE_REFL];
    ALL_TAC] THEN
  EXISTS_TAC `0` THEN
  ASM_REWRITE_TAC[valid_quiz; isQuizR; isQaskR; fitqz; flatqz; flatq] THEN
  SUBGOAL_THEN `walkqz
                (Quiz (QaskR (large_qarity (a1 - 1)) q2)
                (QaskR (small_qarity (a2 - 1)) q1)) (G0:(num)hypermap) 0 = 0 ::
                APPEND W2 (1 :: W1)` SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["W1"; "W2"] THEN
    ASM_REWRITE_TAC[walkqz; walkq; qstepR; APPEND];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[fitq; ASSUME
      `walkq q1 (G0:(num)hypermap) (node_map G0 0) = W1`; ASSUME
      `walkq q2 (G0:(num)hypermap) (node_map G0 1) = W2`]) THEN
    ASM_REWRITE_TAC[MAP; MAP_APPEND; APPEND];
    MP_TAC(ISPECL [`G0:(num)hypermap`; `0 :: APPEND W2 (1 :: (W1:(num)list))`;
                   `W:(num)list`] FACE_SIMPLE_FBAND_EQ) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REWRITE_TAC[MEM; MEM_APPEND] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
        FIRST_ASSUM ACCEPT_TAC;
        EXPAND_TAC "W" THEN REWRITE_TAC[FBAND_CONS; FBAND_APPEND; DISJ_ACI];
        EXPAND_TAC "W" THEN REWRITE_TAC[LENGTH; LENGTH_APPEND] THEN ARITH_TAC];
      DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    X_GEN_TAC `x:num` THEN REWRITE_TAC[kernel] THEN
    SUBGOAL_THEN
      `fband (G0:(num)hypermap) (0 :: APPEND W2 (1 :: W1)) x <=> fband G0 W x`
      SUBST1_TAC THENL
     [EXPAND_TAC "W" THEN REWRITE_TAC[FBAND_CONS; FBAND_APPEND; DISJ_ACI];
      ALL_TAC] THEN
    ASM_CASES_TAC `(x:num) IN dart G0` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `~(fband (G0:(num)hypermap) W x /\ fband G0 r0 x)`
        ASSUME_TAC THENL
       [DISCH_THEN(CONJUNCTS_THEN2
         (X_CHOOSE_THEN `y:num` STRIP_ASSUME_TAC o REWRITE_RULE[FBAND_MEM_IFF])
         ASSUME_TAC) THEN
        SUBGOAL_THEN `fband (G0:(num)hypermap) r0 y` MP_TAC THENL
         [MATCH_MP_TAC FBAND_CFACE THEN EXISTS_TAC `x:num` THEN
          ASM_REWRITE_TAC[];
          ASM_SIMP_TAC[]];
        ALL_TAC] THEN
      UNDISCH_TAC `!u. u IN dart (G0:(num)hypermap)
                   ==> (fband G0 (APPEND W r0) u <=> ~(u IN {0,1}) \/
                   fband G0 [0;1] u)` THEN
      DISCH_THEN(MP_TAC o SPEC `x:num`) THEN
      REWRITE_TAC[ASSUME `(x:num) IN dart G0`; FBAND_APPEND; FBAND_CONS;
                  FBAND_NIL; IN_INSERT; NOT_IN_EMPTY] THEN
      UNDISCH_TAC `~(fband (G0:(num)hypermap) W x /\ fband G0 r0 x)` THEN
      MESON_TAC[CFACE_REFL];
      MATCH_MP_TAC FBAND_OUT_DART THEN ASM_REWRITE_TAC[]]]);;
let CPMAP_RING_FACE_SIMPLE = prove
 (`!cp. cp = [] \/ config_prog cp
        ==> face_simple (FST(cpmap cp))
                        (cpring (FST(cpmap cp)) (SND(cpmap cp)))`,
  GEN_TAC THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[CPMAP_NIL_PAIR; FST; SND] THEN
    MP_TAC SIMPLE_CPMAP0_BASE THEN REWRITE_TAC[APPEND_NIL];
    MP_TAC(SPEC `cp:(cpstep)list` CPMAP_SIMPLE) THEN
    ASM_REWRITE_TAC[FACE_SIMPLE_APPEND'] THEN SIMP_TAC[]]);;
let QS2_TRIPLES = prove
 (`!qs:(bool#num#question)list.
     LENGTH qs = 2 ==> ?k1 a1 q1 k2 a2 q2. qs = [(k1,a1,q1); (k2,a2,q2)]`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 = SUC(SUC 0)`; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[QS_TRIPLE]);;
let QS3_TRIPLES = prove
 (`!qs:(bool#num#question)list.
     3 <= LENGTH qs
     ==> ?k1 a1 q1 k2 a2 q2 k3 a3 q3 qs3.
           qs = CONS (k1,a1,q1) (CONS (k2,a2,q2) (CONS (k3,a3,q3) qs3))`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP LENGTH3_HDTL) THEN
  MP_TAC(ISPEC `HD (qs:(bool#num#question)list)` QS_TRIPLE) THEN
  MP_TAC(ISPEC `HD (TL (qs:(bool#num#question)list))` QS_TRIPLE) THEN
  MP_TAC(ISPEC `HD (TL (TL (qs:(bool#num#question)list)))` QS_TRIPLE) THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The main induction of Coq cfquizP: walking the construction program       *)
(* backwards (cp2 still to be processed, cp1 done, cp = APPEND cp1 cp2), the *)
(* rqs_proper invariant is preserved by the R / Y / H steps and yields the   *)
(* quiz on the base map cpmap0.                                              *)
(* ------------------------------------------------------------------------- *)

let CFQUIZ_REC_MAIN = prove
 (`!cp. config_prog cp
        ==> !cp2 cp1 qs.
               APPEND cp1 cp2 = cp /\ ALL config_step cp1 /\
               (cp2 = [] \/ config_prog cp2) /\
               rqs_proper (FST(cpmap cp)) (SND(cpmap cp))
                          (dart (FST(cpmap cp2)))
                          (cpring (FST(cpmap cp2)) (SND(cpmap cp2))) qs /\
               isQuizR (cfquiz_rec cp2 qs)
               ==> (!w. MEM w (cpring (FST(cpmap cp)) (SND(cpmap cp)))
                        ==> good_ring_arity (FST(cpmap cp)) w) /\
                   (?x0. x0 IN dart (FST(cpmap cp)) /\
                         valid_quiz (FST(cpmap cp))
                           (cpring (FST(cpmap cp)) (SND(cpmap cp))) x0
                           (cfquiz_rec cp2 qs))`,
  GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[CPMAP_NIL_PAIR; FST; SND; CPRING_CPMAP0]) THEN
    MP_TAC(ISPEC `qs:(bool#num#question)list` QS2_TRIPLES) THEN ANTS_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP RQS_FIT_LENGTH o CONJUNCT1 o
                  REWRITE_RULE[rqs_proper] o check (fun th ->
        is_const(fst(strip_comb(concl th))) &&
        fst(dest_const(fst(strip_comb(concl th)))) = "rqs_proper")) THEN
      REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC] THEN
    MATCH_MP_TAC CFQUIZ_REC_BASE THEN
    ASM_REWRITE_TAC[CPMAP_PT_IN_DART; CPRING_CPMAP0] THEN
    MP_TAC(ISPECL [`cp1:(cpstep)list`; `[]:(cpstep)list`] INJCP_CTX_CPMAP) THEN
    ASM_REWRITE_TAC[cubic_prog; ALL; CPMAP_NIL_PAIR; FST; SND] THEN SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
  REWRITE_TAC[NOT_CONS_NIL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `cubic_prog (CONS (h:cpstep) t) /\ cubic_prog t`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[CONFIG_PROG_CUBIC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CONFIG_PROG_CUBIC) THEN
    SIMP_TAC[cubic_prog; ALL];
    ALL_TAC] THEN
  UNDISCH_TAC `isQuizR (cfquiz_rec (CONS (h:cpstep) t) qs)` THEN
  REWRITE_TAC[CFQUIZ_REC_CONS] THEN COND_CASES_TAC THEN
  REWRITE_TAC[ISQUIZR_NOQUIZ] THEN
  MP_TAC(ISPEC `qs:(bool#num#question)list` QS3_TRIPLES) THEN ANTS_TAC THENL
   [ASM_ARITH_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[HD; TL] THEN
  MP_TAC(ISPECL [`h:cpstep`; `t:(cpstep)list`] CONFIG_PROG_CONS_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN2
             (CONJUNCTS_THEN2 (X_CHOOSE_THEN `n:num` SUBST_ALL_TAC) ASSUME_TAC)
             (DISJ_CASES_THEN2 (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)
              (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THEN
  REWRITE_TAC[isCpR; cpr_arg; distinctness "cpstep"] THEN DISCH_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[CPMAP_CONS_R; ecpR; FST; SND]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
    EXISTS_TAC `APPEND cp1 [CpR n]` THEN
    ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; ALL_APPEND; ALL;
                    config_step] THEN
    MATCH_MP_TAC RQS_PROPER_ROT THEN
    MP_TAC(ISPECL [`FST(cpmap t)`; `SND(cpmap t)`; `n:num`]
           CPRING_ECPR_ROT_GEN) THEN
    REWRITE_TAC[ecpR; CPMAP_PT_IN_DART; NODE_MAP_PERMUTES; FINITE_DART] THEN
    DISCH_THEN(fun th -> ASM_REWRITE_TAC[GSYM th]);
    RULE_ASSUM_TAC(REWRITE_RULE[CPMAP_CONS_Y; FST; SND]) THEN
    SUBGOAL_THEN `~(cfquiz_Y (k1,a1,q1) (k2,a2,q2)
                  (rqs_Y (k1,a1,q1) (k3,a3,q3) qs3) = [])` ASSUME_TAC THENL
     [DISCH_THEN(fun th -> UNDISCH_TAC `isQuizR
                                        (cfquiz_rec t
                                        (cfquiz_Y (k1,a1,q1) (k2,a2,q2)
                                        (rqs_Y (k1,a1,q1) (k3,a3,q3) qs3)))`
                 THEN REWRITE_TAC[th; CFQUIZ_REC_NIL_NOTR]);
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
    EXISTS_TAC `APPEND cp1 [CpY]` THEN
    ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; ALL_APPEND; ALL;
                    config_step] THEN
    MATCH_MP_TAC RQS_PROPER_Y THEN
    ASM_SIMP_TAC[CPMAP_PT_IN_DART; CPMAP_PROPER; CPMAP_RING_FACE_SIMPLE] THEN
    MP_TAC(ISPECL [`cp1:(cpstep)list`; `CONS CpY t`] INJCP_CTX_CPMAP) THEN
    ASM_REWRITE_TAC[CPMAP_CONS_Y; FST; SND] THEN SIMP_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[CPMAP_CONS_H; FST; SND]) THEN
    SUBGOAL_THEN `~(cfquiz_H (k1,a1,q1) (k2,a2,q2)
                  (rqs_H (k1,a1,q1) (k3,a3,q3) qs3) = [])` ASSUME_TAC THENL
     [DISCH_THEN(fun th -> UNDISCH_TAC `isQuizR
                                        (cfquiz_rec t
                                        (cfquiz_H (k1,a1,q1) (k2,a2,q2)
                                        (rqs_H (k1,a1,q1) (k3,a3,q3) qs3)))`
                 THEN REWRITE_TAC[th; CFQUIZ_REC_NIL_NOTR]);
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
    EXISTS_TAC `APPEND cp1 [CpH]` THEN
    ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; ALL_APPEND; ALL;
                    config_step] THEN
    MATCH_MP_TAC RQS_PROPER_H THEN
    ASM_SIMP_TAC[CPMAP_PT_IN_DART; CPMAP_PROPER; CPMAP_RING_FACE_SIMPLE;
                 CFMAP_LONG; CPMAP_PLAIN] THEN
    MP_TAC(ISPECL [`cp1:(cpstep)list`; `CONS CpH t`] INJCP_CTX_CPMAP) THEN
    ASM_REWRITE_TAC[CPMAP_CONS_H; FST; SND] THEN SIMP_TAC[]]);;

(* Coq cfquizP for the cpring (cfring = REVERSE cpring).                     *)
let CFQUIZ_MAIN = prove
 (`!cf. isQuizR (cfquiz cf)
        ==> (!w. MEM w (cpring (FST(cfmap cf)) (SND(cfmap cf)))
                 ==> good_ring_arity (FST(cfmap cf)) w) /\
            (?x0. x0 IN dart (FST(cfmap cf)) /\
                  valid_quiz (FST(cfmap cf))
                    (cpring (FST(cfmap cf)) (SND(cfmap cf))) x0 (cfquiz cf))`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CFQUIZ_UNFOLD) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CFQUIZ_CONFIG_PROG) THEN
  ASM_REWRITE_TAC[cfmap] THEN MP_TAC(SPEC `cfprog cf` CFQUIZ_REC_MAIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`cfprog cf`; `[]:(cpstep)list`;
    `REPLICATE (cprsize (cfprog cf)) (F,0,Qask0)`]) THEN
  ASM_SIMP_TAC[APPEND; ALL; RQS_PROPER_INIT] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_MESON_TAC[]);;
let CFQUIZ_GOOD_RING = prove
 (`!cf. isQuizR (cfquiz cf)
        ==> !x. MEM x (cfring cf) ==> good_ring_arity (FST (cfmap cf)) x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[cfring; MEM_REVERSE] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CFQUIZ_MAIN) THEN SIMP_TAC[]);;
let VALID_CFQUIZ = prove
 (`!cf. isQuizR (cfquiz cf)
        ==> ?u. u IN dart (FST (cfmap cf)) /\
                valid_quiz (FST (cfmap cf)) (cfring cf) u (cfquiz cf)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[cfring; valid_quiz; kernel; FBAND_REVERSE] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CFQUIZ_MAIN) THEN
  REWRITE_TAC[valid_quiz; kernel] THEN SIMP_TAC[]);;
let CFQUIZ_CFMAP_PROPS = prove
 (`!cf. isQuizR (cfquiz cf)
        ==> planar_hypermap (FST (cfmap cf)) /\ bridgeless (FST (cfmap cf)) /\
            connected_hypermap (FST (cfmap cf)) /\
            plain_hypermap (FST (cfmap cf))`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CONFIG_PROG_CUBIC o MATCH_MP
              CFQUIZ_CONFIG_PROG) THEN
  REWRITE_TAC[cfmap] THEN
  SIMP_TAC[CPMAP_PLANAR; CPMAP_BRIDGELESS; CPMAP_CONNECTED; CPMAP_PLAIN]);;
