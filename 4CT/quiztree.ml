(* ========================================================================= *)
(* 4CT/quiztree.ml                                                           *)
(*                                                                           *)
(* quiztree.v: the quiz tree.  The configuration quizzes (with their         *)
(* rotations and, unless the configuration is symmetric, their reflections)  *)
(* are compiled by cfquiz_tree into a tree indexed by the arities of the     *)
(* three faces around a node, so that redpart does one lookup per node;      *)
(* qzt_fit says some stored quiz fits at a node, and QZT_FIT_CFQUIZ (Coq     *)
(* qzt_fit_cfquiz) says a fitting leaf comes from a configuration whose quiz *)
(* is valid there.  The configurations come with their symmetry flag as      *)
(* pairs (cf, sym) : ((cpstep)list # (num)list) # bool (configurations.ml    *)
(* provides the_configs and the_configs_sym).                                *)
(* ========================================================================= *)

needs "4CT/cfquiz.ml";;
needs "4CT/part_converse.ml";;   (* NORM_TAC, IN_DART_EQS, FE_NN_U *)

let quiz_tree_INDUCT,quiz_tree_RECURSION = define_type
  "quiz_tree = QztNil
             | QztLeaf question question question quiz_tree
             | QztNode quiz_tree quiz_tree quiz_tree quiz_tree
             | QztHubNode quiz_tree quiz_tree quiz_tree quiz_tree";;

let qzt_proper = new_recursive_definition quiz_tree_RECURSION
 `(qzt_proper QztNil = F) /\
  (qzt_proper (QztLeaf q1 q2 q3 t) = T) /\
  (qzt_proper (QztNode t5 t6 t7 t8) = T) /\
  (qzt_proper (QztHubNode t58 t9 t10 t11) = T)`;;

let isQztHubNode = new_recursive_definition quiz_tree_RECURSION
 `(isQztHubNode QztNil = F) /\
  (isQztHubNode (QztLeaf q1 q2 q3 t) = F) /\
  (isQztHubNode (QztNode t5 t6 t7 t8) = F) /\
  (isQztHubNode (QztHubNode t58 t9 t10 t11) = T)`;;

(* Update/store operations.                                                  *)
let qzt_put1 = new_recursive_definition quiz_tree_RECURSION
 `(qzt_put1 qa (qr:quiz_tree->quiz_tree) QztNil = QztNil) /\
  (qzt_put1 qa qr (QztLeaf q1 q2 q3 t) = QztLeaf q1 q2 q3 t) /\
  (qzt_put1 qa qr (QztNode t5 t6 t7 t8) =
     (if qa = Qa5 then QztNode (qr t5) t6 t7 t8
      else if qa = Qa6 then QztNode t5 (qr t6) t7 t8
      else if qa = Qa7 then QztNode t5 t6 (qr t7) t8
      else if qa = Qa8 then QztNode t5 t6 t7 (qr t8)
      else QztNode t5 t6 t7 t8)) /\
  (qzt_put1 qa qr (QztHubNode t58 t9 t10 t11) =
     (if qa = Qa9 then QztHubNode t58 (qr t9) t10 t11
      else if qa = Qa10 then QztHubNode t58 t9 (qr t10) t11
      else if qa = Qa11 then QztHubNode t58 t9 t10 (qr t11)
      else QztHubNode (qzt_put1 qa qr t58) t9 t10 t11))`;;

let qzt_put3 = new_definition
 `qzt_put3 qa1 qa2 qa3 q1 q2 q3 =
    qzt_put1 qa1 (qzt_put1 qa2 (qzt_put1 qa3 (QztLeaf q1 q2 q3)))`;;

let qzt_put3rot = new_definition
 `qzt_put3rot qa1 qa2 qa3 q1 q2 q3 t =
    qzt_put3 qa1 qa2 qa3 q1 q2 q3
      (qzt_put3 qa2 qa3 qa1 q2 q3 q1 (qzt_put3 qa3 qa1 qa2 q3 q1 q2 t))`;;

let qzt_put = new_definition
 `qzt_put qa1 qa2 qa3 q1 q2 q3 =
    if 8 < nat_of_qarity qa1 then qzt_put3 qa1 qa2 qa3 q1 q2 q3
    else qzt_put3rot qa1 qa2 qa3 q1 q2 q3`;;

let qzt_empty = new_definition
 `qzt_empty =
    let mkn = \t. QztNode t t t t in
    let n2 = mkn (mkn QztNil) in
    QztHubNode (mkn n2) n2 n2 n2`;;

let normq = new_recursive_definition question_RECURSION
 `(normq Qask0 = Qask0) /\
  (normq (Qask1 qa) = QaskLR qa Qask0 Qask0) /\
  (normq (QaskL qa ql) = QaskLR qa ql Qask0) /\
  (normq (QaskR qa qr) = QaskLR qa Qask0 qr) /\
  (normq (QaskLR qa ql qr) = QaskLR qa ql qr) /\
  (normq (QaskLL qa qll) = QaskLL qa qll) /\
  (normq (QaskRR qa qrr) = QaskRR qa qrr)`;;

let isQaskLR = new_recursive_definition question_RECURSION
 `(isQaskLR Qask0 = F) /\ (isQaskLR (Qask1 qa) = F) /\
  (isQaskLR (QaskL qa ql) = F) /\ (isQaskLR (QaskR qa qr) = F) /\
  (isQaskLR (QaskLR qa ql qr) = T) /\ (isQaskLR (QaskLL qa qll) = F) /\
  (isQaskLR (QaskRR qa qrr) = F)`;;

(* The two subquestions of a QaskLR (Qask0 otherwise)                        *)
let qLR_l = new_recursive_definition question_RECURSION
 `(qLR_l Qask0 = Qask0) /\ (qLR_l (Qask1 qa) = Qask0) /\
  (qLR_l (QaskL qa ql) = Qask0) /\ (qLR_l (QaskR qa qr) = Qask0) /\
  (qLR_l (QaskLR qa ql qr) = ql) /\ (qLR_l (QaskLL qa qll) = Qask0) /\
  (qLR_l (QaskRR qa qrr) = Qask0)`;;

let qLR_r = new_recursive_definition question_RECURSION
 `(qLR_r Qask0 = Qask0) /\ (qLR_r (Qask1 qa) = Qask0) /\
  (qLR_r (QaskL qa ql) = Qask0) /\ (qLR_r (QaskR qa qr) = Qask0) /\
  (qLR_r (QaskLR qa ql qr) = qr) /\ (qLR_r (QaskLL qa qll) = Qask0) /\
  (qLR_r (QaskRR qa qrr) = Qask0)`;;

(* store_qz (Quiz (QaskR qa1 q1) (QaskR qa2 q2)) t; identity otherwise.      *)
let store_qz_aux = new_definition
 `store_qz_aux qa1 qa2 q1 q2 t =
    let nq1 = normq q1 and nq2 = normq q2 in
    if isQaskLR nq1 /\ isQaskLR nq2 then
      (if nat_of_qarity (qra nq1) < nat_of_qarity (qra nq2)
       then qzt_put qa1 qa2 (qra nq1) (qLR_l nq1) q2 (qLR_r nq1) t
       else qzt_put qa1 (qra nq2) qa2 q1 (qLR_r nq2) (qLR_l nq2) t)
    else if isQaskLR nq1
    then qzt_put qa1 qa2 (qra nq1) (qLR_l nq1) q2 (qLR_r nq1) t
    else if isQaskLR nq2
    then qzt_put qa1 (qra nq2) qa2 q1 (qLR_r nq2) (qLR_l nq2) t
    else t`;;

let store_qz = new_recursive_definition quiz_RECURSION
 `store_qz (Quiz q0 q1) t =
    if isQaskR q0 /\ isQaskR q1
    then store_qz_aux (qra q0) (qra q1) (qrb q0) (qrb q1) t
    else t`;;

let store_cf_qz = new_definition
 `store_cf_qz qz sym t =
  store_qz qz (if sym then t else store_qz (flipqz qz) t)`;;

(* cfquiz_tree_rec over (config, sym) pairs.                                 *)
let cfquiz_tree_rec = new_recursive_definition list_RECURSION
 `(cfquiz_tree_rec qt ([]:(((cpstep)list#(num)list)#bool)list) = qt) /\
  (cfquiz_tree_rec qt (CONS cfs cfs') =
     (let qt' = store_cf_qz (cfquiz (FST cfs)) (SND cfs) qt in
      if isQztHubNode qt' then cfquiz_tree_rec qt' cfs' else QztNil))`;;

let cfquiz_tree = new_definition
 `cfquiz_tree cfs = cfquiz_tree_rec qzt_empty cfs`;;

(* Sizes.                                                                    *)
let qzt_size = new_recursive_definition quiz_tree_RECURSION
 `(qzt_size QztNil = 0) /\
  (qzt_size (QztLeaf q1 q2 q3 t) = SUC (qzt_size t)) /\
  (qzt_size (QztNode t5 t6 t7 t8) =
  qzt_size t5 + (qzt_size t6 + (qzt_size t7 + qzt_size t8))) /\
  (qzt_size (QztHubNode t58 t9 t10 t11) =
     qzt_size t58 + (qzt_size t9 + (qzt_size t10 + qzt_size t11)))`;;

(* Lookup.                                                                   *)
let qzt_get1 = new_recursive_definition quiz_tree_RECURSION
 `(qzt_get1 qa QztNil = QztNil) /\
  (qzt_get1 qa (QztLeaf q1 q2 q3 t) = QztNil) /\
  (qzt_get1 qa (QztNode t5 t6 t7 t8) =
     (if qa = Qa5 then t5 else if qa = Qa6 then t6 else if qa = Qa7 then t7
      else if qa = Qa8 then t8 else QztNil)) /\
  (qzt_get1 qa (QztHubNode t58 t9 t10 t11) =
     (if qa = Qa9 then t9 else if qa = Qa10 then t10 else if qa = Qa11 then t11
      else qzt_get1 qa t58))`;;

let qzt_get2 = new_definition
  `qzt_get2 qa2 qa3 t = qzt_get1 qa3 (qzt_get1 qa2 t)`;;
let qzt_get3 = new_definition
  `qzt_get3 qa1 qa2 qa3 t = qzt_get2 qa2 qa3 (qzt_get1 qa1 t)`;;

(* Fitting: x1, node x1, node^2 x1 have arities in [5,11] (qzt_fita) and     *)
(* some leaf under those arities fits at the three qstepR darts (qzt_fitl).  *)
let qzt_fita = new_definition
 `qzt_fita (G:(A)hypermap) x1 <=>
    let x2 = node_map G x1 in let x3 = node_map G x2 in
    nat_of_qarity (qarity_of_nat (arity G x1)) = arity G x1 /\
    nat_of_qarity (qarity_of_nat (arity G x2)) = arity G x2 /\
    nat_of_qarity (qarity_of_nat (arity G x3)) = arity G x3`;;

let qzt_fitl = new_recursive_definition quiz_tree_RECURSION
 `(qzt_fitl (G:(A)hypermap) x1 QztNil = F) /\
  (qzt_fitl G x1 (QztLeaf q1 q2 q3 t) =
     ((fitq G (qstepR G x1) q1 /\
       fitq G (qstepR G (node_map G x1)) q2 /\
       fitq G (qstepR G (node_map G (node_map G x1))) q3) \/
      qzt_fitl G x1 t)) /\
  (qzt_fitl G x1 (QztNode t5 t6 t7 t8) = F) /\
  (qzt_fitl G x1 (QztHubNode t58 t9 t10 t11) = F)`;;

let qzt_fit = new_definition
 `qzt_fit (G:(A)hypermap) x1 t <=>
    qzt_fita G x1 /\
    qzt_fitl G x1 (qzt_get3 (qarity_of_nat (arity G x1))
                            (qarity_of_nat (arity G (node_map G x1)))
                            (qarity_of_nat
                            (arity G (node_map G (node_map G x1)))) t)`;;

let qzt_truncate = new_definition
 `qzt_truncate (t:quiz_tree) =
    match t with
      QztHubNode (QztNode t5 t6 t7 t8) t9 t10 t11 -> QztNode t5 t6 t7 t8
    | t -> t`;;

(* ------------------------------------------------------------------------- *)
(* Lemmas (Coq quiztree.v Section FitQuizTree). Dart identities are closed   *)
(* by NORM_TAC (part_converse.ml); fitqz atoms are expanded by               *)
(* FITQZ_EXPAND_TAC (fitqz/walkq/flatq unfolding + FITQ_CAT) and compared    *)
(* modulo CONJ_ACI.                                                          *)
(* ------------------------------------------------------------------------- *)

let QARITY_DISTINCT = let th = distinctness "qarity" in
CONJ th (ONCE_REWRITE_RULE[EQ_SYM_EQ] th);;

(* Coq FIT_NORMQ.                                                            *)
let FIT_NORMQ = prove
 (`!(G:(A)hypermap) x q. fitq G x (normq q) <=> fitq G x q`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `q:question` (cases "question")) THEN
  REWRITE_TAC[normq; fitq; flatq; walkq; APPEND_NIL; APPEND; MAP;
              MAP_APPEND]);;

(* Coq QZT_GET_PUT1.                                                         *)
let QZT_GET_PUT1 = prove
 (`!t qa qa' (qr:quiz_tree->quiz_tree).
     (qa = qa' /\ qr (qzt_get1 qa t) = qzt_get1 qa (qzt_put1 qa' qr t)) \/
     qzt_get1 qa t = qzt_get1 qa (qzt_put1 qa' qr t)`,
  MATCH_MP_TAC quiz_tree_INDUCT THEN REPEAT CONJ_TAC THEN BETA_TAC THENL
   [REWRITE_TAC[qzt_put1; qzt_get1];
    REWRITE_TAC[qzt_put1; qzt_get1];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC(ISPEC `qa':qarity` (cases "qarity")) THEN
    STRUCT_CASES_TAC(ISPEC `qa:qarity` (cases "qarity")) THEN
    REWRITE_TAC[qzt_put1; qzt_get1; QARITY_DISTINCT];
    REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    REPEAT GEN_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL[`qa:qarity`; `qa':qarity`;
                                 `qr:quiz_tree->quiz_tree`]) THEN
    STRUCT_CASES_TAC(ISPEC `qa':qarity` (cases "qarity")) THEN
    STRUCT_CASES_TAC(ISPEC `qa:qarity` (cases "qarity")) THEN
    REWRITE_TAC[qzt_put1; qzt_get1; QARITY_DISTINCT]]);;

(* The empty tree has no leaves at depth 3.                                  *)
let QZT_GET1_NODE4 = prove
 (`!a t. qzt_get1 a (QztNode t t t t) = if nat_of_qarity a <= 8 then t
 else QztNil`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `a:qarity` (cases "qarity")) THEN
  REWRITE_TAC[qzt_get1; QARITY_DISTINCT; nat_of_qarity] THEN
  CONV_TAC NUM_REDUCE_CONV);;
let QZT_GET1_HUB4 = prove
 (`!a t t'. qzt_get1 a (QztHubNode t t' t' t') = if nat_of_qarity a <= 8
 then qzt_get1 a t else t'`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `a:qarity` (cases "qarity")) THEN
  REWRITE_TAC[qzt_get1; QARITY_DISTINCT; nat_of_qarity] THEN
  CONV_TAC NUM_REDUCE_CONV);;
let QZT_GET3_EMPTY = prove
 (`!a1 a2 a3. qzt_get3 a1 a2 a3 qzt_empty = QztNil`,
  REPEAT GEN_TAC THEN REWRITE_TAC[qzt_get3; qzt_get2; qzt_empty] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[QZT_GET1_HUB4; QZT_GET1_NODE4] THEN
  REPEAT(COND_CASES_TAC THEN REWRITE_TAC[QZT_GET1_NODE4; qzt_get1]));;
let QZT_FIT_NIL = prove
 (`!(G:(A)hypermap) x1. ~(qzt_fit G x1 QztNil)`,
  REWRITE_TAC[qzt_fit; qzt_get3; qzt_get2; qzt_get1; qzt_fitl]);;
let QZT_FIT_EMPTY = prove
 (`!(G:(A)hypermap) x1. ~(qzt_fit G x1 qzt_empty)`,
  REWRITE_TAC[qzt_fit; QZT_GET3_EMPTY; qzt_fitl]);;

let QASKLR_EXPAND = prove
 (`!q. isQaskLR q ==> q = QaskLR (qra q) (qLR_l q) (qLR_r q)`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `q:question` (cases "question")) THEN
  REWRITE_TAC[isQaskLR; qra; qLR_l; qLR_r]);;
let ISQUIZR_FLIPQZ = prove
 (`!qz. isQuizR (flipqz qz) <=> isQuizR qz`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `qz:quiz` (cases "quiz")) THEN
  REWRITE_TAC[flipqz] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[isQuizR; isQaskR]);;

(* Expand fitqz of a concrete quiz into its arity/fitq atoms (right-nesting  *)
(* the APPENDs so FITQ_CAT applies).                                         *)
let FITQZ_EXPAND_TAC =
  REWRITE_TAC[fitqz; flatqz; flatq; walkqz; walkq; APPEND; GSYM APPEND_ASSOC;
              MAP; CONS_11; FITQ_CAT] THEN
  REWRITE_TAC[GSYM fitq];;

(* The leaf quiz quiz3 qa1 qa2 qa3 q1 q2 q3 at the dart e (n x1).            *)
let FITQZ_QUIZ3 = prove
 (`!(G:(A)hypermap) x1 qa1 qa2 qa3 q1 q2 q3.
     plain_hypermap G /\ cubic_hypermap G
     ==>
 (fitqz G (edge_map G (node_map G x1))
 (Quiz (QaskR qa1 (QaskLR qa3 q1 q3)) (QaskR qa2 q2)) <=>
          nat_of_qarity qa1 = arity G x1 /\
          nat_of_qarity qa3 = arity G (node_map G (node_map G x1)) /\
          fitq G (qstepR G x1) q1 /\
          fitq G (qstepR G (node_map G (node_map G x1))) q3 /\
          nat_of_qarity qa2 = arity G (node_map G x1) /\
          fitq G (qstepR G (node_map G x1)) q2)`,
  REPEAT STRIP_TAC THEN FITQZ_EXPAND_TAC THEN REWRITE_TAC[qstepL; qstepR] THEN
  NORM_TAC THEN REWRITE_TAC[CONJ_ACI]);;

(* Coq FITQZ_ROT / FITQZ_SWAP.                                               *)
let FITQZ_ROT = prove
 (`!(G:(A)hypermap) y qa1 qa2 qa3 q1 q2 q3.
     plain_hypermap G /\ cubic_hypermap G
     ==> (fitqz G y (Quiz (QaskR qa1 (QaskLR qa3 q1 q3)) (QaskR qa2 q2)) <=>
          fitqz G (edge_map G (face_map G y))
          (Quiz (QaskR qa3 (QaskLR qa2 q3 q2)) (QaskR qa1 q1)))`,
  REPEAT STRIP_TAC THEN FITQZ_EXPAND_TAC THEN REWRITE_TAC[qstepL; qstepR] THEN
  NORM_TAC THEN REWRITE_TAC[CONJ_ACI]);;
let FITQZ_SWAP = prove
 (`!(G:(A)hypermap) y qa1 qa2 qa3 q1 q2 q3.
     plain_hypermap G /\ cubic_hypermap G
     ==> (fitqz G y (Quiz (QaskR qa1 (QaskLR qa3 q1 q3)) (QaskR qa2 q2)) <=>
          fitqz G (face_map G y)
          (Quiz (QaskR qa1 q1) (QaskR qa3 (QaskLR qa2 q3 q2))))`,
  REPEAT STRIP_TAC THEN FITQZ_EXPAND_TAC THEN REWRITE_TAC[qstepL; qstepR] THEN
  NORM_TAC THEN REWRITE_TAC[CONJ_ACI]);;
let FITQZ_NORMQ_L = prove
 (`!(G:(A)hypermap) y a b p r.
     fitqz G y (Quiz (QaskR a (normq p)) (QaskR b r)) <=>
     fitqz G y (Quiz (QaskR a p) (QaskR b r))`,
  REPEAT GEN_TAC THEN FITQZ_EXPAND_TAC THEN REWRITE_TAC[FIT_NORMQ]);;
let FITQZ_NORMQ_R = prove
 (`!(G:(A)hypermap) y a b p r.
     fitqz G y (Quiz (QaskR a p) (QaskR b (normq r))) <=>
     fitqz G y (Quiz (QaskR a p) (QaskR b r))`,
  REPEAT GEN_TAC THEN FITQZ_EXPAND_TAC THEN REWRITE_TAC[FIT_NORMQ]);;

(* Three get/put steps: the lookup is unchanged, or all arities match and    *)
(* the leaf is found.                                                        *)
let QZT_GET3_PUT3 = prove
 (`!t a1 a2 a3 qa1 qa2 qa3 q1 q2 q3.
     qzt_get3 a1 a2 a3 (qzt_put3 qa1 qa2 qa3 q1 q2 q3 t) =
     qzt_get3 a1 a2 a3 t \/
     a1 = qa1 /\ a2 = qa2 /\ a3 = qa3 /\
     qzt_get3 a1 a2 a3 (qzt_put3 qa1 qa2 qa3 q1 q2 q3 t) =
     QztLeaf q1 q2 q3 (qzt_get3 a1 a2 a3 t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[qzt_get3; qzt_get2; qzt_put3] THEN
  MP_TAC(ISPECL[`t:quiz_tree`; `a1:qarity`; `qa1:qarity`;
                `qzt_put1 qa2 (qzt_put1 qa3 (QztLeaf q1 q2 q3))`]
         QZT_GET_PUT1) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM))
             (SUBST1_TAC o SYM)) THEN
  MP_TAC(ISPECL[`qzt_get1 a1 t`; `a2:qarity`; `qa2:qarity`;
                `qzt_put1 qa3 (QztLeaf q1 q2 q3)`] QZT_GET_PUT1) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM))
             (SUBST1_TAC o SYM)) THEN
  MP_TAC(ISPECL[`qzt_get1 a2 (qzt_get1 a1 t)`; `a3:qarity`; `qa3:qarity`;
                `QztLeaf q1 q2 q3`] QZT_GET_PUT1) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM))
             (SUBST1_TAC o SYM)) THEN
  ASM_REWRITE_TAC[]);;

(* Coq QZT_FIT_PUT3.                                                         *)
let QZT_FIT_PUT3 = prove
 (`!(G:(A)hypermap) x1 qa1 qa2 qa3 q1 q2 q3 t.
     plain_hypermap G /\ cubic_hypermap G /\
     qzt_fit G x1 (qzt_put3 qa1 qa2 qa3 q1 q2 q3 t)
     ==> fitqz G (edge_map G (node_map G x1))
               (Quiz (QaskR qa1 (QaskLR qa3 q1 q3)) (QaskR qa2 q2)) \/
         qzt_fit G x1 t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[FITQZ_QUIZ3] THEN
  UNDISCH_TAC
    `qzt_fit (G:(A)hypermap) x1 (qzt_put3 qa1 qa2 qa3 q1 q2 q3 t)` THEN
  REWRITE_TAC[qzt_fit; qzt_fita] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`t:quiz_tree`; `qarity_of_nat (arity (G:(A)hypermap) x1)`;
    `qarity_of_nat (arity (G:(A)hypermap) (node_map G x1))`;
    `qarity_of_nat (arity (G:(A)hypermap) (node_map G (node_map G x1)))`;
    `qa1:qarity`; `qa2:qarity`; `qa3:qarity`; `q1:question`;
    `q2:question`; `q3:question`] QZT_GET3_PUT3) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC STRIP_ASSUME_TAC) THENL
   [DISCH_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[qzt_fitl] THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM o check
   (fun th -> is_eq (concl th) && is_comb (lhs (concl th)) &&
              (rator(lhs(concl th)) = `qarity_of_nat`)))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* Coq QZT_FIT_PUT: the rotations land on e x2, e x1, e x3.                  *)
let QZT_FIT_PUT = prove
 (`!(G:(A)hypermap) x1 qa1 qa2 qa3 q1 q2 q3 t.
     plain_hypermap G /\ cubic_hypermap G /\ x1 IN dart G /\
     qzt_fit G x1 (qzt_put qa1 qa2 qa3 q1 q2 q3 t)
     ==> (?y. y IN dart G /\
              fitqz G y
                (Quiz (QaskR qa1 (QaskLR qa3 q1 q3)) (QaskR qa2 q2))) \/
         qzt_fit G x1 t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC
    `qzt_fit (G:(A)hypermap) x1 (qzt_put qa1 qa2 qa3 q1 q2 q3 t)` THEN
  REWRITE_TAC[qzt_put] THEN COND_CASES_TAC THEN REWRITE_TAC[qzt_put3rot] THEN
  DISCH_TAC THENL
   [MP_TAC(ISPECL[`G:(A)hypermap`; `x1:A`; `qa1:qarity`; `qa2:qarity`;
                  `qa3:qarity`; `q1:question`; `q2:question`; `q3:question`;
                  `t:quiz_tree`] QZT_FIT_PUT3) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN
    EXISTS_TAC `edge_map G (node_map G (x1:A))` THEN
    ASM_REWRITE_TAC IN_DART_EQS;
    ALL_TAC] THEN
  MP_TAC(ISPECL[`G:(A)hypermap`; `x1:A`; `qa1:qarity`; `qa2:qarity`;
                `qa3:qarity`; `q1:question`; `q2:question`; `q3:question`;
    `qzt_put3 qa2 qa3 qa1 q2 q3 q1 (qzt_put3 qa3 qa1 qa2 q3 q1 q2 t)`]
         QZT_FIT_PUT3) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [DISJ1_TAC THEN EXISTS_TAC `edge_map G (node_map G (x1:A))` THEN
    ASM_REWRITE_TAC IN_DART_EQS;
    ALL_TAC] THEN
  MP_TAC(ISPECL[`G:(A)hypermap`; `x1:A`; `qa2:qarity`; `qa3:qarity`;
                `qa1:qarity`; `q2:question`; `q3:question`; `q1:question`;
                `qzt_put3 qa3 qa1 qa2 q3 q1 q2 t`] QZT_FIT_PUT3) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [DISJ1_TAC THEN EXISTS_TAC `edge_map G (x1:A)` THEN
    ASM_REWRITE_TAC IN_DART_EQS THEN
    MP_TAC(ISPECL[`G:(A)hypermap`; `edge_map G (node_map G (x1:A))`;
                  `qa2:qarity`; `qa3:qarity`; `qa1:qarity`; `q2:question`;
                  `q3:question`; `q1:question`] FITQZ_ROT) THEN
    ASM_REWRITE_TAC[nodeK];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`G:(A)hypermap`; `x1:A`; `qa3:qarity`; `qa1:qarity`;
                `qa2:qarity`; `q3:question`; `q1:question`; `q2:question`;
                `t:quiz_tree`] QZT_FIT_PUT3) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN
  EXISTS_TAC `edge_map G (node_map G (node_map G (x1:A)))` THEN
  ASM_REWRITE_TAC IN_DART_EQS THEN
  MP_TAC(ISPECL[`G:(A)hypermap`; `edge_map G (node_map G (x1:A))`;
                `qa3:qarity`; `qa1:qarity`; `qa2:qarity`; `q3:question`;
                `q1:question`; `q2:question`] FITQZ_ROT) THEN
  ASM_REWRITE_TAC[nodeK] THEN
  MP_TAC(ISPECL[`G:(A)hypermap`; `edge_map G (x1:A)`; `qa2:qarity`;
                `qa3:qarity`; `qa1:qarity`; `q2:question`; `q3:question`;
                `q1:question`] FITQZ_ROT) THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[FE_NN_U] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* Coq QZT_FIT_STORE, split: the QaskR/QaskR core and the wrapper.           *)
let QZT_FIT_STORE_AUX = prove
 (`!(G:(A)hypermap) x1 qa1 qa2 q1 q2 t.
     plain_hypermap G /\ cubic_hypermap G /\ x1 IN dart G /\
     qzt_fit G x1 (store_qz_aux qa1 qa2 q1 q2 t)
     ==> (?y. y IN dart G /\ fitqz G y (Quiz (QaskR qa1 q1) (QaskR qa2 q2))) \/
         qzt_fit G x1 t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `qzt_fit (G:(A)hypermap) x1 (store_qz_aux qa1 qa2 q1 q2 t)` THEN
  REWRITE_TAC[store_qz_aux] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_CASES_TAC `isQaskLR (normq q1)` THEN
  ASM_CASES_TAC `isQaskLR (normq q2)` THEN
  ASM_REWRITE_TAC[] THEN TRY COND_CASES_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST
   [MP_TAC(ISPECL[`G:(A)hypermap`;`x1:A`;`qa1:qarity`;`qa2:qarity`;
                  `qra (normq q1)`;`qLR_l (normq q1)`;
                  `q2:question`;`qLR_r (normq q1)`;`t:quiz_tree`] QZT_FIT_PUT)
                    THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN
    EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM FITQZ_NORMQ_L] THEN
    ONCE_REWRITE_TAC[MATCH_MP QASKLR_EXPAND (ASSUME `isQaskLR (normq q1)`)]
      THEN
    FIRST_ASSUM ACCEPT_TAC;
    MP_TAC(ISPECL[`G:(A)hypermap`;`x1:A`;`qa1:qarity`;`qra (normq q2)`;
                  `qa2:qarity`;`q1:question`;
                  `qLR_r (normq q2)`;`qLR_l (normq q2)`;`t:quiz_tree`
                  ] QZT_FIT_PUT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN
    EXISTS_TAC `face_map G (y:A)` THEN ASM_REWRITE_TAC IN_DART_EQS THEN
    ONCE_REWRITE_TAC[GSYM FITQZ_NORMQ_R] THEN
    ONCE_REWRITE_TAC[MATCH_MP QASKLR_EXPAND (ASSUME `isQaskLR (normq q2)`)]
      THEN
    MP_TAC(ISPECL[`G:(A)hypermap`;`y:A`;`qa1:qarity`;`qra (normq q2)`;
                  `qa2:qarity`;`q1:question`;
                  `qLR_r (normq q2)`;`qLR_l (normq q2)`] FITQZ_SWAP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN ACCEPT_TAC]);;

let QZT_FIT_STORE = prove
 (`!(G:(A)hypermap) x1 qz t.
     plain_hypermap G /\ cubic_hypermap G /\ x1 IN dart G /\
     qzt_fit G x1 (store_qz qz t)
     ==> (isQuizR qz /\ ?y. y IN dart G /\ fitqz G y qz) \/ qzt_fit G x1 t`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `qz:quiz` (cases "quiz")) THEN
  REWRITE_TAC[store_qz; isQuizR] THEN
  ASM_CASES_TAC `isQaskR a0 /\ isQaskR a1` THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL[`G:(A)hypermap`; `x1:A`; `qra a0`; `qra a1`; `qrb a0`;
                `qrb a1`; `t:quiz_tree`] QZT_FIT_STORE_AUX) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(MATCH_MP QASKR_EXPAND
         (CONJUNCT1 (ASSUME `isQaskR a0 /\ isQaskR a1`))) THEN
  MP_TAC(MATCH_MP QASKR_EXPAND
         (CONJUNCT2 (ASSUME `isQaskR a0 /\ isQaskR a1`))) THEN
  DISCH_THEN(fun th2 ->
             DISCH_THEN(fun th1 -> REWRITE_TAC[GSYM th1; GSYM th2])));;

(* Coq QZT_FIT_STORE_CF (FITQZ_FLIP for the reflected quiz).                 *)
let QZT_FIT_STORE_CF = prove
 (`!(G:(A)hypermap) x1 qz sym t.
     plain_hypermap G /\ cubic_hypermap G /\ x1 IN dart G /\
     qzt_fit G x1 (store_cf_qz qz sym t)
     ==> (isQuizR qz /\
          ((?y. y IN dart G /\ fitqz G y qz) \/
          (?y. y IN dart (mirror G) /\ fitqz (mirror G) y qz))) \/
         qzt_fit G x1 t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `qzt_fit (G:(A)hypermap) x1 (store_cf_qz qz sym t)` THEN
  REWRITE_TAC[store_cf_qz] THEN BOOL_CASES_TAC `sym:bool` THEN
  REWRITE_TAC[] THEN DISCH_TAC THENL
   [MP_TAC(ISPECL[`G:(A)hypermap`; `x1:A`; `qz:quiz`; `t:quiz_tree`]
           QZT_FIT_STORE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT DISJ1_TAC THEN EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL[`G:(A)hypermap`; `x1:A`; `qz:quiz`; `store_qz (flipqz qz) t`]
           QZT_FIT_STORE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [REPEAT DISJ1_TAC THEN EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL[`G:(A)hypermap`; `x1:A`; `flipqz qz`; `t:quiz_tree`]
           QZT_FIT_STORE) THEN
    ASM_REWRITE_TAC[ISQUIZR_FLIPQZ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISJ1_TAC THEN DISJ2_TAC THEN EXISTS_TAC `face_map G (y:A)` THEN
    REWRITE_TAC[DART_MIRROR] THEN ASM_REWRITE_TAC IN_DART_EQS THEN
    MP_TAC(ISPEC `G:(A)hypermap` FITQZ_FLIP) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o ISPECL[`qz:quiz`; `y:A`]) THEN ASM_REWRITE_TAC[]]);;

(* Coq qzt_fit_cfquiz, generalised over the accumulator, by list induction.  *)
let QZT_FIT_CFQUIZ_REC = prove
 (`!(G:(A)hypermap) x1. plain_hypermap G /\ cubic_hypermap G /\ x1 IN dart G
     ==> !cfs qt0. ~(qzt_fit G x1 qt0) /\
                   qzt_fit G x1 (cfquiz_tree_rec qt0 cfs)
           ==> ?i. i < LENGTH cfs /\
                   ?qz. ((?y. y IN dart G /\ fitqz G y qz) \/
                         (?y. y IN dart (mirror G) /\
                              fitqz (mirror G) y qz)) /\
                        isQuizR qz /\ qz = cfquiz (FST (EL i cfs)) /\
                        (planar_hypermap (FST (cfmap (FST (EL i cfs)))) /\
                         bridgeless (FST (cfmap (FST (EL i cfs)))) /\
                         connected_hypermap (FST (cfmap (FST (EL i cfs)))) /\
                         plain_hypermap (FST (cfmap (FST (EL i cfs))))) /\
                        radius2_kernel (FST (cfmap (FST (EL i cfs))))
                        (cfring (FST (EL i cfs))) /\
                        (?u. valid_quiz (FST (cfmap (FST (EL i cfs))))
                        (cfring (FST (EL i cfs))) u qz)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[cfquiz_tree_rec] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `qt0:quiz_tree` THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  COND_CASES_TAC THEN REWRITE_TAC[QZT_FIT_NIL] THEN STRIP_TAC THEN
  ASM_CASES_TAC
   `qzt_fit (G:(A)hypermap) x1
      (store_cf_qz (cfquiz (FST (h:((cpstep)list#(num)list)#bool))) (SND h)
                   qt0)` THENL
   [MP_TAC(ISPECL[`G:(A)hypermap`; `x1:A`;
                  `cfquiz (FST (h:((cpstep)list#(num)list)#bool))`;
                  `SND (h:((cpstep)list#(num)list)#bool)`; `qt0:quiz_tree`]
           QZT_FIT_STORE_CF) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[LENGTH; LT_0; EL; HD] THEN
    EXISTS_TAC `cfquiz (FST (h:((cpstep)list#(num)list)#bool))` THEN
    ASM_SIMP_TAC[CFQUIZ_CFMAP_PROPS; CPRADIUS2P] THEN
    ASM_MESON_TAC[VALID_CFQUIZ];
    FIRST_X_ASSUM(MP_TAC o SPEC
     `store_cf_qz (cfquiz (FST (h:((cpstep)list#(num)list)#bool))) (SND h)
                  qt0`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num`
     (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `qz:quiz` ASSUME_TAC))) THEN
    EXISTS_TAC `SUC i` THEN ASM_REWRITE_TAC[LENGTH; LT_SUC; EL; TL] THEN
    EXISTS_TAC `qz:quiz` THEN ASM_REWRITE_TAC[]]);;

let QZT_FIT_CFQUIZ = prove
 (`!(G:(A)hypermap) x1 cfs.
     plain_cubic G /\ x1 IN dart G /\ qzt_fit G x1 (cfquiz_tree cfs)
     ==> ?i. i < LENGTH cfs /\
             ?qz. ((?y. y IN dart G /\ fitqz G y qz) \/
                   (?y. y IN dart (mirror G) /\ fitqz (mirror G) y qz)) /\
                  isQuizR qz /\ qz = cfquiz (FST (EL i cfs)) /\
                  (planar_hypermap (FST (cfmap (FST (EL i cfs)))) /\
                   bridgeless (FST (cfmap (FST (EL i cfs)))) /\
                   connected_hypermap (FST (cfmap (FST (EL i cfs)))) /\
                   plain_hypermap (FST (cfmap (FST (EL i cfs))))) /\
                  radius2_kernel (FST (cfmap (FST (EL i cfs))))
                  (cfring (FST (EL i cfs))) /\
                  (?u. valid_quiz (FST (cfmap (FST (EL i cfs))))
                  (cfring (FST (EL i cfs))) u qz)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[plain_cubic; cfquiz_tree] THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`G:(A)hypermap`; `x1:A`] QZT_FIT_CFQUIZ_REC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL[`cfs:(((cpstep)list#(num)list)#bool)list`;
                            `qzt_empty`]) THEN
  ASM_REWRITE_TAC[QZT_FIT_EMPTY]);;

(* Coq QZT_GET1_TRUNCATE.                                                    *)
let QZT_GET1_TRUNCATE = prove
 (`!qa t. qzt_proper (qzt_get1 qa (qzt_truncate t))
          ==> qzt_get1 qa (qzt_truncate t) = qzt_get1 qa t`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `t:quiz_tree` (cases "quiz_tree")) THEN
  REWRITE_TAC[qzt_truncate] THEN
  STRUCT_CASES_TAC(ISPEC `a0:quiz_tree` (cases "quiz_tree")) THEN
  REWRITE_TAC[qzt_truncate] THEN
  STRUCT_CASES_TAC(ISPEC `qa:qarity` (cases "qarity")) THEN
  REWRITE_TAC[qzt_get1; qzt_proper; QARITY_DISTINCT]);;

