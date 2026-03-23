(* ========================================================================= *)
(* The Central Limit Theorem for integrable random variables.                *)
(*                                                                           *)
(* Follows Williams "Probability with Martingales" Chapter 18.               *)
(* Includes characteristic function bounds for integrable RVs, product       *)
(* formulas for independent integrable sums, CLT characteristic function     *)
(* convergence (general version), Levy continuity theorem (integrable        *)
(* version), and the final INTEGRABLE_CLT theorem.                           *)
(* ========================================================================= *)

needs "Probability/characteristic_functions.ml";;

(* ========================================================================= *)
(* Phase 19: Characteristic function bounds for integrable RVs               *)
(* ========================================================================= *)

(* ONE_MINUS_COS_NONNEG: 0 <= 1 - cos(x) *)
let ONE_MINUS_COS_NONNEG = prove
 (`!x. &0 <= &1 - cos(x)`,
  GEN_TAC THEN MP_TAC(SPEC `x:real` COS_BOUNDS) THEN REAL_ARITH_TAC);;

(* COS_LOWER_BOUND: cos(x) >= 1 - x^2/2 *)
let COS_LOWER_BOUND = prove
 (`!x. &1 - x pow 2 / &2 <= cos(x)`,
  GEN_TAC THEN MP_TAC(SPEC `x:real` ONE_MINUS_COS_LE) THEN REAL_ARITH_TAC);;

(* GEN_CHAR_FN_RE_LOWER_BOUND: E[cos(tX)] >= 1 - t^2 * E[X^2] / 2 *)
let GEN_CHAR_FN_RE_LOWER_BOUND = prove
 (`!p:A prob_space X t.
     integrable p X /\ integrable p (\x. X x pow 2)
     ==> &1 - t pow 2 * expectation p (\x. X x pow 2) / &2
         <= gen_char_fn_re p X t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gen_char_fn_re] THEN
  SUBGOAL_THEN `&1 - t pow 2 * expectation p (\x. (X:A->real) x pow 2) / &2 =
                expectation p (\x. &1 - t pow 2 * X x pow 2 / &2)` SUBST1_TAC THENL
  [SUBGOAL_THEN `random_variable p (X:A->real)` ASSUME_TAC THENL
   [ASM_MESON_TAC[integrable]; ALL_TAC] THEN
   SUBGOAL_THEN
     `expectation p (\x:A. &1 - t pow 2 * X x pow 2 / &2) =
      expectation p (\x. &1) - expectation p (\x. t pow 2 * X x pow 2 / &2)`
     SUBST1_TAC THENL
   [MATCH_MP_TAC EXPECTATION_SUB THEN CONJ_TAC THENL
    [REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC] THEN
    SUBGOAL_THEN `(\x:A. t pow 2 * X x pow 2 / &2) = (\x. (t pow 2 / &2) * X x pow 2)`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[EXPECTATION_CONST] THEN
    SUBGOAL_THEN `(\x:A. t pow 2 * X x pow 2 / &2) = (\x. (t pow 2 / &2) * X x pow 2)`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[EXPECTATION_CMUL] THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  MATCH_MP_TAC EXPECTATION_MONO THEN REPEAT CONJ_TAC THENL
  [SUBGOAL_THEN `(\x:A. &1 - t pow 2 * X x pow 2 / &2) =
                 (\x. (\x. &1) x + (-- (t pow 2 / &2)) * (\x. X x pow 2) x)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
   [REWRITE_TAC[INTEGRABLE_CONST];
    MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]];
   MATCH_MP_TAC INTEGRABLE_COS_CMUL THEN ASM_MESON_TAC[integrable];
   GEN_TAC THEN DISCH_TAC THEN
   MP_TAC(SPEC `t * (X:A->real) x` COS_LOWER_BOUND) THEN
   REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC]);;

(* GEN_CHAR_FN_RE_UPPER_BOUND: gen_char_fn_re p X t <= 1 *)
let GEN_CHAR_FN_RE_UPPER_BOUND = prove
 (`!p:A prob_space X t.
     integrable p X /\ integrable p (\x. X x pow 2)
     ==> gen_char_fn_re p X t <= &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gen_char_fn_re] THEN
  SUBGOAL_THEN `&1 = expectation (p:A prob_space) (\x:A. &1)` SUBST1_TAC THENL
  [REWRITE_TAC[EXPECTATION_CONST]; ALL_TAC] THEN
  MATCH_MP_TAC EXPECTATION_MONO THEN REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_COS_CMUL THEN ASM_MESON_TAC[integrable];
   REWRITE_TAC[INTEGRABLE_CONST];
   GEN_TAC THEN DISCH_TAC THEN
   MP_TAC(SPEC `t * (X:A->real) x` COS_BOUNDS) THEN REAL_ARITH_TAC]);;

(* Phase 20: Generalized CLT for integrable RVs *)

(* Tightness from second moments - integrable version *)
let TIGHTNESS_FROM_SECOND_MOMENTS = prove
 (`!p:A prob_space (X:num->A->real) C.
      (!n. integrable p (X n)) /\
      (!n. integrable p (\x. X n x pow 2)) /\
      &0 < C /\
      (!n. expectation p (\x. X n x pow 2) <= C)
      ==>
      !e. &0 < e ==>
        ?M. &0 < M /\
        !n:num.
          prob (p:A prob_space) {a | a IN prob_carrier p /\
                                      abs((X:num->A->real) n a) >= M} < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `M = sqrt(C / e) + &1` THEN
  EXISTS_TAC `M:real` THEN
  SUBGOAL_THEN `&0 <= sqrt(C / e)` ASSUME_TAC THENL
  [MATCH_MP_TAC SQRT_POS_LE THEN
   MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 < M` ASSUME_TAC THENL
  [EXPAND_TAC "M" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `C / e < (M:real) pow 2` ASSUME_TAC THENL
  [EXPAND_TAC "M" THEN
   SUBGOAL_THEN `sqrt(C / e) pow 2 = C / e` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POW_2 THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
   SUBGOAL_THEN `(sqrt(C / e) + &1) pow 2 =
     sqrt(C / e) pow 2 + &2 * sqrt(C / e) + &1` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `C < M pow 2 * e` ASSUME_TAC THENL
  [SUBGOAL_THEN `C / e * e = (C:real)` (SUBST1_TAC o SYM) THENL
   [MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN
  SUBGOAL_THEN `random_variable (p:A prob_space) ((X:num->A->real) n)` ASSUME_TAC THENL
  [ASM_MESON_TAC[integrable]; ALL_TAC] THEN
  ABBREV_TAC `S = {a:A | a IN prob_carrier p /\ abs((X:num->A->real) n a) >= M}` THEN
  SUBGOAL_THEN `(S:A->bool) IN prob_events p` ASSUME_TAC THENL
  [EXPAND_TAC "S" THEN
   SUBGOAL_THEN `{a:A | a IN prob_carrier p /\ abs((X:num->A->real) n a) >= M} =
     {a | a IN prob_carrier p /\ X n a >= M} UNION
     {a | a IN prob_carrier p /\ --(X n a) >= M}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN GEN_TAC THEN
    ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC PROB_UNION_IN_EVENTS THEN CONJ_TAC THENL
    [MATCH_MP_TAC RV_LEVEL_GE_IN_EVENTS THEN
     REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC RV_LEVEL_GE_IN_EVENTS THEN
     MATCH_MP_TAC RANDOM_VARIABLE_NEG THEN
     REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]]];
   ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (indicator_fn (S:A->bool))` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `prob p (S:A->bool) = expectation (p:A prob_space) (indicator_fn S)` SUBST1_TAC THENL
  [MATCH_MP_TAC(GSYM EXPECTATION_INDICATOR) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `expectation (p:A prob_space) (\x:A. (X:num->A->real) n x pow 2) / M pow 2` THEN
  CONJ_TAC THENL
  [SUBGOAL_THEN `&0 < M pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
   ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
   SUBGOAL_THEN `M pow 2 * expectation (p:A prob_space) (indicator_fn (S:A->bool)) =
     expectation p (\x:A. M pow 2 * indicator_fn S x)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXPECTATION_CMUL THEN
    ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
   MATCH_MP_TAC EXPECTATION_MONO THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[indicator_fn] THEN
    COND_CASES_TAC THENL
    [REWRITE_TAC[REAL_MUL_RID] THEN
     SUBGOAL_THEN `(x:A) IN S` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
     REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS; REAL_POW2_ABS] THEN
     ASM_REAL_ARITH_TAC;
     REWRITE_TAC[REAL_MUL_RZERO; REAL_LE_POW_2]]];
   ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_POW_LT] THEN
   MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `C:real` THEN
   ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
   ASM_REWRITE_TAC[]]);;

(* Variance = E[X^2] for mean-zero integrable RVs *)
let VARIANCE_MEAN_ZERO = prove
 (`!p:A prob_space (X:A->real).
    integrable p X /\ integrable p (\x. X x pow 2) /\
    expectation p X = &0
    ==> expectation p (\x. X x pow 2) = variance p X`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[VARIANCE_ALT] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* INTEGRABLE_CLT: proved below in Phase 23 with full proof *)

(* ========================================================================= *)
(* Independence for strict inequalities (P(X<a,Y<b) = P(X<a)*P(Y<b))         *)
(* ========================================================================= *)

(* For independent RVs, the CDF factorization extends to strict inequalities.
   Uses PROB_CONTINUITY_FROM_BELOW and REALLIM_UNIQUE. *)
let INDEP_RV_STRICT_INEQ = prove
 (`!p:A prob_space (X:A->real) (Y:A->real) a b.
       indep_rv p X Y
       ==> prob p {x | x IN prob_carrier p /\ X x < a /\ Y x < b} =
           prob p {x | x IN prob_carrier p /\ X x < a} *
           prob p {x | x IN prob_carrier p /\ Y x < b}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[indep_rv] THEN STRIP_TAC THEN
  (* Union characterization for X *)
  SUBGOAL_THEN
    `!c:real. UNIONS {(\n:num. {x:A | x IN prob_carrier p /\
       (X:A->real) x <= c - &1 / &(SUC n)}) n | n IN (:num)} =
       {x | x IN prob_carrier p /\ X x < c}` ASSUME_TAC THENL
  [X_GEN_TAC `c:real` THEN
   REWRITE_TAC[SIMPLE_IMAGE; UNIONS_IMAGE; IN_UNIV] THEN BETA_TAC THEN
   REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `z:A` THEN
   EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < &1 / &(SUC n)` MP_TAC THENL
    [SIMP_TAC[REAL_LT_DIV; REAL_LT_01; REAL_OF_NUM_LT; LT_0];
     ASM_REAL_ARITH_TAC];
    STRIP_TAC THEN
    SUBGOAL_THEN `?m:num. ~(m = 0) /\ &0 < inv(&m) /\
       inv(&m) < c - (X:A->real) z` MP_TAC THENL
    [REWRITE_TAC[GSYM REAL_ARCH_INV] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&1 / &(SUC m) <= inv(&m:real)` ASSUME_TAC THENL
    [REWRITE_TAC[real_div; REAL_MUL_LID] THEN
     MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC];
     ASM_REAL_ARITH_TAC]];
   ALL_TAC] THEN
  (* X marginal convergence *)
  SUBGOAL_THEN
    `((\n. prob p {x:A | x IN prob_carrier p /\
       (X:A->real) x <= a - &1 / &(SUC n)}) --->
      prob p {x | x IN prob_carrier p /\ X x < a}) sequentially`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`;
    `\n:num. {x:A | x IN prob_carrier p /\
       (X:A->real) x <= a - &1 / &(SUC n)}`]
    PROB_CONTINUITY_FROM_BELOW) THEN
   BETA_TAC THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [GEN_TAC THEN ASM_MESON_TAC[random_variable];
     GEN_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:A` THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `a - &1 / &(SUC n)` THEN
     ASM_REWRITE_TAC[REAL_LE_SUB_LADD;
       REAL_ARITH `a - x + y <= a <=> y <= x`] THEN
     REWRITE_TAC[real_div; REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
     REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ARITH_TAC];
    FIRST_X_ASSUM(MP_TAC o SPEC `a:real`) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[SIMPLE_IMAGE] THEN DISCH_THEN ACCEPT_TAC];
   ALL_TAC] THEN
  (* Y union characterization *)
  SUBGOAL_THEN
    `!c:real. UNIONS {(\n:num. {x:A | x IN prob_carrier p /\
       (Y:A->real) x <= c - &1 / &(SUC n)}) n | n IN (:num)} =
       {x | x IN prob_carrier p /\ Y x < c}` ASSUME_TAC THENL
  [X_GEN_TAC `c:real` THEN
   REWRITE_TAC[SIMPLE_IMAGE; UNIONS_IMAGE; IN_UNIV] THEN BETA_TAC THEN
   REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `z:A` THEN
   EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < &1 / &(SUC n)` MP_TAC THENL
    [SIMP_TAC[REAL_LT_DIV; REAL_LT_01; REAL_OF_NUM_LT; LT_0];
     ASM_REAL_ARITH_TAC];
    STRIP_TAC THEN
    SUBGOAL_THEN `?m:num. ~(m = 0) /\ &0 < inv(&m) /\
       inv(&m) < c - (Y:A->real) z` MP_TAC THENL
    [REWRITE_TAC[GSYM REAL_ARCH_INV] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&1 / &(SUC m) <= inv(&m:real)` ASSUME_TAC THENL
    [REWRITE_TAC[real_div; REAL_MUL_LID] THEN
     MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC];
     ASM_REAL_ARITH_TAC]];
   ALL_TAC] THEN
  (* Y marginal convergence *)
  SUBGOAL_THEN
    `((\n. prob p {x:A | x IN prob_carrier p /\
       (Y:A->real) x <= b - &1 / &(SUC n)}) --->
      prob p {x | x IN prob_carrier p /\ Y x < b}) sequentially`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`;
    `\n:num. {x:A | x IN prob_carrier p /\
       (Y:A->real) x <= b - &1 / &(SUC n)}`]
    PROB_CONTINUITY_FROM_BELOW) THEN
   BETA_TAC THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [GEN_TAC THEN ASM_MESON_TAC[random_variable];
     GEN_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:A` THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `b - &1 / &(SUC n)` THEN
     ASM_REWRITE_TAC[REAL_LE_SUB_LADD;
       REAL_ARITH `a - x + y <= a <=> y <= x`] THEN
     REWRITE_TAC[real_div; REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
     REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ARITH_TAC];
    FIRST_X_ASSUM(MP_TAC o SPEC `b:real`) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[SIMPLE_IMAGE] THEN DISCH_THEN ACCEPT_TAC];
   ALL_TAC] THEN
  (* Joint union characterization *)
  SUBGOAL_THEN
    `UNIONS {(\n:num. {x:A | x IN prob_carrier p /\
       (X:A->real) x <= a - &1 / &(SUC n) /\
       (Y:A->real) x <= b - &1 / &(SUC n)}) n | n IN (:num)} =
     {x | x IN prob_carrier p /\ X x < a /\ Y x < b}` ASSUME_TAC THENL
  [REWRITE_TAC[SIMPLE_IMAGE; UNIONS_IMAGE; IN_UNIV] THEN BETA_TAC THEN
   REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `z:A` THEN
   EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    SUBGOAL_THEN `&0 < &1 / &(SUC n)` MP_TAC THENL
    [SIMP_TAC[REAL_LT_DIV; REAL_LT_01; REAL_OF_NUM_LT; LT_0];
     ASM_REAL_ARITH_TAC;
     SIMP_TAC[REAL_LT_DIV; REAL_LT_01; REAL_OF_NUM_LT; LT_0];
     ASM_REAL_ARITH_TAC];
    STRIP_TAC THEN
    SUBGOAL_THEN `?m1:num. ~(m1 = 0) /\ &0 < inv(&m1) /\
       inv(&m1) < a - (X:A->real) z` MP_TAC THENL
    [REWRITE_TAC[GSYM REAL_ARCH_INV] THEN ASM_REAL_ARITH_TAC;
     ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `m1:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?m2:num. ~(m2 = 0) /\ &0 < inv(&m2) /\
       inv(&m2) < b - (Y:A->real) z` MP_TAC THENL
    [REWRITE_TAC[GSYM REAL_ARCH_INV] THEN ASM_REAL_ARITH_TAC;
     ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `m2:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `m1 + m2:num` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&1 / &(SUC (m1 + m2)) <= inv(&m1:real) /\
       &1 / &(SUC (m1 + m2)) <= inv(&m2:real)` STRIP_ASSUME_TAC THENL
    [REWRITE_TAC[real_div; REAL_MUL_LID] THEN CONJ_TAC THEN
     MATCH_MP_TAC REAL_LE_INV2 THEN
     REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
     ASM_REAL_ARITH_TAC]];
   ALL_TAC] THEN
  (* Joint sets are in prob_events *)
  SUBGOAL_THEN
    `!c d. {x:A | x IN prob_carrier p /\ (X:A->real) x <= c /\
       (Y:A->real) x <= d} IN prob_events p` ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ (X:A->real) x <= c /\
      (Y:A->real) x <= d} =
      {x | x IN prob_carrier p /\ X x <= c} INTER
      {x | x IN prob_carrier p /\ Y x <= d}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN MESON_TAC[];
    MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN
    ASM_MESON_TAC[random_variable]];
   ALL_TAC] THEN
  (* Joint convergence via PROB_CONTINUITY_FROM_BELOW *)
  MP_TAC(ISPECL [`p:A prob_space`;
    `\n:num. {x:A | x IN prob_carrier p /\ (X:A->real) x <= a - &1 / &(SUC n) /\
       (Y:A->real) x <= b - &1 / &(SUC n)}`]
    PROB_CONTINUITY_FROM_BELOW) THEN
  BETA_TAC THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [GEN_TAC THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:A` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THENL
    [EXISTS_TAC `a - &1 / &(SUC n)`; EXISTS_TAC `b - &1 / &(SUC n)`] THEN
    ASM_REWRITE_TAC[REAL_LE_SUB_LADD;
      REAL_ARITH `a - x + y <= a <=> y <= x`] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ARITH_TAC];
   ALL_TAC] THEN
  (* Rewrite UNIONS to target set, use independence, then limits *)
  SUBGOAL_THEN
    `UNIONS {{x:A | x IN prob_carrier p /\ (X:A->real) x <= a - &1 / &(SUC n) /\
       (Y:A->real) x <= b - &1 / &(SUC n)} | n IN (:num)} =
     UNIONS {(\n. {x | x IN prob_carrier p /\ X x <= a - &1 / &(SUC n) /\
       Y x <= b - &1 / &(SUC n)}) n | n IN (:num)}`
    SUBST1_TAC THENL
  [AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
   MESON_TAC[];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* Now have joint product convergence; use REALLIM_MUL + REALLIM_UNIQUE *)
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC `\n:num. prob (p:A prob_space)
    {x:A | x IN prob_carrier p /\ (X:A->real) x <= a - &1 / &(SUC n)} *
    prob p {x | x IN prob_carrier p /\ (Y:A->real) x <= b - &1 / &(SUC n)}` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REALLIM_MUL THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* NSFA CDF and level set characterizations                                  *)
(* ========================================================================= *)

(* nsfa(p,f,n,x) <= k/2^n iff f(x) < (k+1)/2^n, for k < n*2^n *)
let NSFA_CDF_CHAR = prove
 (`!p:A prob_space (f:A->real) n k x.
    x IN prob_carrier p /\ &0 <= f x /\ k < n * 2 EXP n
    ==> (nonneg_simple_fn_approx p f n x <= &k / &(2 EXP n) <=>
         f x < &(k + 1) / &(2 EXP n))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[nonneg_simple_fn_approx] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `S = IMAGE (\k. &k / &(2 EXP n))
    {k | k <= n * 2 EXP n /\ &k / &(2 EXP n) <= (f:A->real) x}` THEN
  SUBGOAL_THEN `FINITE (S:real->bool) /\ ~(S = {})` STRIP_ASSUME_TAC THENL
  [EXPAND_TAC "S" THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[NONNEG_APPROX_INDEX_FINITE];
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `0` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THENL [ARITH_TAC;
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC]];
   ALL_TAC] THEN
  MP_TAC(SPEC `S:real->bool` SUP_FINITE) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(2 EXP n)` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ; EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  EQ_TAC THENL
  [(* Forward: sup S <= k/2^n ==> f x < (k+1)/2^n *)
   DISCH_TAC THEN
   ASM_CASES_TAC `(f:A->real) x < &(k + 1) / &(2 EXP n)` THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `&(k + 1) / &(2 EXP n) <= (f:A->real) x` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `k + 1 <= n * 2 EXP n` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&(k + 1) / &(2 EXP n) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    EXISTS_TAC `k + 1` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `&(k + 1) / &(2 EXP n) <= sup S` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `&k / &(2 EXP n) < &(k + 1) / &(2 EXP n)` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC;
    ASM_REAL_ARITH_TAC];
   (* Backward: f x < (k+1)/2^n ==> sup S <= k/2^n *)
   DISCH_TAC THEN
   UNDISCH_TAC `sup S IN (S:real->bool)` THEN
   EXPAND_TAC "S" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
   DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[] THEN
   ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
   REWRITE_TAC[REAL_OF_NUM_LE] THEN
   SUBGOAL_THEN `&j / &(2 EXP n) < &(k + 1) / &(2 EXP n)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN
   REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC]);;

(* ========================================================================= *)
(* E[XY] = E[X]*E[Y] for independent integrable RVs (Task #73)               *)
(* ========================================================================= *)

(* For nonneg RV f and a >= 0, either nsfa(f,n) <= a always on carrier,
   or there exists c such that nsfa(f,n,x) <= a iff f(x) < c.
   This characterizes CDF events of nsfa as strict-inequality events. *)
let NSFA_CDF_EQUIV = prove
 (`!p:A prob_space (f:A->real) n a.
    random_variable p f /\ (!x. x IN prob_carrier p ==> &0 <= f x) /\ &0 <= a
    ==> (?c. !x. x IN prob_carrier p
              ==> (nonneg_simple_fn_approx p f n x <= a <=> f x < c)) \/
        (!x. x IN prob_carrier p ==> nonneg_simple_fn_approx p f n x <= a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `?j. j <= n * 2 EXP n /\ ~(&j / &(2 EXP n) <= a)` THENL
  [(* Hard case: some grid point > a. Find the minimum such j0. *)
   DISJ1_TAC THEN
   FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[num_WOP]) THEN
   DISCH_THEN(X_CHOOSE_THEN `j0:num` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `&j0 / &(2 EXP n)` THEN
   X_GEN_TAC `z:A` THEN DISCH_TAC THEN
   (* Establish key facts about j0 *)
   SUBGOAL_THEN `1 <= j0` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= j0 <=> ~(j0 = 0)`] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(&0 / &(2 EXP n) <= a)` THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `j0 - 1 < n * 2 EXP n` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
   (* Apply NSFA_CDF_CHAR with k = j0-1 *)
   SUBGOAL_THEN `nonneg_simple_fn_approx (p:A prob_space) (f:A->real) n z <=
     &(j0 - 1) / &(2 EXP n) <=> f z < &((j0 - 1) + 1) / &(2 EXP n)` ASSUME_TAC THENL
   [MATCH_MP_TAC NSFA_CDF_CHAR THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `(j0 - 1) + 1 = j0` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&(j0 - 1) / &(2 EXP n) <= a` ASSUME_TAC THENL
   [UNDISCH_TAC `!m. m < j0 ==> ~(m <= n * 2 EXP n /\ ~(&m / &(2 EXP n) <= a))` THEN
    DISCH_THEN(MP_TAC o SPEC `j0 - 1`) THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= j0 ==> j0 - 1 < j0`] THEN
    ASM_SIMP_TAC[ARITH_RULE `j0 - 1 < n * 2 EXP n ==> j0 - 1 <= n * 2 EXP n`] THEN
    MESON_TAC[];
    ALL_TAC] THEN
   (* Prove the biconditional nsfa <= a <=> f z < j0/2^n *)
   EQ_TAC THENL
   [(* Forward: nsfa <= a ==> f z < j0/2^n *)
    DISCH_TAC THEN
    MP_TAC(SPECL [`p:A prob_space`; `f:A->real`; `n:num`; `z:A`]
      NONNEG_SIMPLE_FN_APPROX_IN_GRID) THEN
    ASM_SIMP_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    (* k < j0 since k/2^n <= a < j0/2^n *)
    SUBGOAL_THEN `(k:num) < j0` ASSUME_TAC THENL
    [SUBGOAL_THEN `&k / &(2 EXP n) <= a` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `&0 < &(2 EXP n)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ; EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
     SUBGOAL_THEN `a < &j0 / &(2 EXP n)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `&k / &(2 EXP n) < &j0 / &(2 EXP n)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `(&k:real) < &j0` MP_TAC THENL
     [ASM_MESON_TAC[REAL_LT_DIV2_EQ]; ALL_TAC] THEN
     REWRITE_TAC[REAL_OF_NUM_LT];
     ALL_TAC] THEN
    (* k < j0 implies k < n*2^n, then use NSFA_CDF_CHAR *)
    SUBGOAL_THEN `(k:num) < n * 2 EXP n` ASSUME_TAC THENL
    [UNDISCH_TAC `(k:num) < j0` THEN UNDISCH_TAC `j0 <= n * 2 EXP n` THEN ARITH_TAC;
     ALL_TAC] THEN
    SUBGOAL_THEN `(f:A->real) z < &(k + 1) / &(2 EXP n)` ASSUME_TAC THENL
    [MP_TAC(SPECL [`p:A prob_space`; `f:A->real`; `n:num`; `k:num`; `z:A`]
      NSFA_CDF_CHAR) THEN
     ASM_SIMP_TAC[] THEN DISCH_TAC THEN
     SUBGOAL_THEN `nonneg_simple_fn_approx (p:A prob_space) (f:A->real) n z <=
       &k / &(2 EXP n)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN `&(k + 1) / &(2 EXP n) <= &j0 / &(2 EXP n)` MP_TAC THENL
    [SUBGOAL_THEN `&0 < &(2 EXP n)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ; EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
     ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
     REWRITE_TAC[REAL_OF_NUM_LE] THEN
     UNDISCH_TAC `(k:num) < j0` THEN ARITH_TAC;
     ASM_REAL_ARITH_TAC];
    (* Backward: f z < j0/2^n ==> nsfa <= a *)
    DISCH_TAC THEN
    SUBGOAL_THEN `nonneg_simple_fn_approx (p:A prob_space) (f:A->real) n z <=
      &(j0 - 1) / &(2 EXP n)` MP_TAC THENL
    [UNDISCH_TAC `nonneg_simple_fn_approx (p:A prob_space) (f:A->real) n z <=
       &(j0 - 1) / &(2 EXP n) <=> f z < &((j0 - 1) + 1) / &(2 EXP n)` THEN
     UNDISCH_TAC `(j0 - 1) + 1 = j0` THEN
     DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
     ASM_MESON_TAC[];
     ASM_REAL_ARITH_TAC]];
   (* Easy case: no grid point > a, so nsfa <= max grid value <= a always *)
   DISJ2_TAC THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
   MP_TAC(SPECL [`p:A prob_space`; `f:A->real`; `n:num`; `z:A`]
     NONNEG_SIMPLE_FN_APPROX_IN_GRID) THEN
   ASM_SIMP_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `~(?j. j <= n * 2 EXP n /\ ~(&j / &(2 EXP n) <= a))` THEN
   REWRITE_TAC[NOT_EXISTS_THM] THEN
   DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
   ASM_REWRITE_TAC[] THEN CONV_TAC TAUT]);;

(* nsfa compositions of independent RVs are independent *)
let INDEP_RV_NSFA = prove
 (`!p:A prob_space (X:A->real) (Y:A->real) n.
    random_variable p X /\ random_variable p Y /\
    (!x. x IN prob_carrier p ==> &0 <= X x) /\
    (!x. x IN prob_carrier p ==> &0 <= Y x) /\
    indep_rv p X Y
    ==> indep_rv p (nonneg_simple_fn_approx p X n)
                   (nonneg_simple_fn_approx p Y n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[indep_rv] THEN REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_RV THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_RV THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  (* Handle negative a or b: nsfa is nonneg so sets are empty *)
  ASM_CASES_TAC `a < &0` THENL
  [SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ nonneg_simple_fn_approx p X n x <= a /\
     nonneg_simple_fn_approx p Y n x <= b} = {}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`p:A prob_space`; `X:A->real`; `n:num`; `z:A`]
      NONNEG_SIMPLE_FN_APPROX_NONNEG) THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ nonneg_simple_fn_approx p X n x <= a} = {}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`p:A prob_space`; `X:A->real`; `n:num`; `z:A`]
      NONNEG_SIMPLE_FN_APPROX_NONNEG) THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[PROB_EMPTY; REAL_MUL_LZERO]; ALL_TAC] THEN
  ASM_CASES_TAC `b < &0` THENL
  [SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ nonneg_simple_fn_approx p X n x <= a /\
     nonneg_simple_fn_approx p Y n x <= b} = {}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`p:A prob_space`; `Y:A->real`; `n:num`; `z:A`]
      NONNEG_SIMPLE_FN_APPROX_NONNEG) THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ nonneg_simple_fn_approx p Y n x <= b} = {}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`p:A prob_space`; `Y:A->real`; `n:num`; `z:A`]
      NONNEG_SIMPLE_FN_APPROX_NONNEG) THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[PROB_EMPTY; REAL_MUL_RZERO]; ALL_TAC] THEN
  (* Now a >= 0, b >= 0. Apply NSFA_CDF_EQUIV to characterize the CDF events *)
  SUBGOAL_THEN `&0 <= a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`p:A prob_space`; `X:A->real`; `n:num`; `a:real`] NSFA_CDF_EQUIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:A prob_space`; `Y:A->real`; `n:num`; `b:real`] NSFA_CDF_EQUIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
  [(* Case: both X and Y have strict inequality characterizations *)
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ nonneg_simple_fn_approx p X n x <= a /\
     nonneg_simple_fn_approx p Y n x <= b} =
     {x | x IN prob_carrier p /\ X x < c /\ Y x < c'}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
    ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ nonneg_simple_fn_approx p X n x <= a} =
     {x | x IN prob_carrier p /\ X x < c}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
    ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ nonneg_simple_fn_approx p Y n x <= b} =
     {x | x IN prob_carrier p /\ Y x < c'}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
    ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC INDEP_RV_STRICT_INEQ THEN ASM_REWRITE_TAC[];
   (* Case: X has strict ineq, Y is always <= b *)
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ nonneg_simple_fn_approx p X n x <= a /\
     nonneg_simple_fn_approx p Y n x <= b} =
     {x | x IN prob_carrier p /\ nonneg_simple_fn_approx p X n x <= a}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
    ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ nonneg_simple_fn_approx p Y n x <= b} =
     prob_carrier p` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
    ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[PROB_SPACE; REAL_MUL_RID];
   (* Case: X is always <= a, Y has strict ineq *)
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ nonneg_simple_fn_approx p X n x <= a /\
     nonneg_simple_fn_approx p Y n x <= b} =
     {x | x IN prob_carrier p /\ nonneg_simple_fn_approx p Y n x <= b}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
    ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ nonneg_simple_fn_approx p X n x <= a} =
     prob_carrier p` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
    ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[PROB_SPACE; REAL_MUL_LID];
   (* Case: both X and Y are always <= a, <= b *)
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ nonneg_simple_fn_approx p X n x <= a /\
     nonneg_simple_fn_approx p Y n x <= b} = prob_carrier p` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
    ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ nonneg_simple_fn_approx p X n x <= a} =
     prob_carrier p` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
    ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ nonneg_simple_fn_approx p Y n x <= b} =
     prob_carrier p` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
    ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[PROB_SPACE; REAL_MUL_LID]]);;

(* Product of nonneg bounded independent RVs: nn_expectation factors *)
(* Uses MCT on nsfa(X,n)*nsfa(Y,n) -> X*Y, combined with INDEP_RV_NSFA
   and EXPECTATION_PRODUCT_INDEP_SIMPLE for simple RVs, then limits. *)
let NN_EXPECTATION_PRODUCT_BOUNDED_INDEP = prove
 (`!p:A prob_space (X:A->real) (Y:A->real) B_X B_Y.
    random_variable p X /\ random_variable p Y /\
    (!x. x IN prob_carrier p ==> &0 <= X x) /\
    (!x. x IN prob_carrier p ==> &0 <= Y x) /\
    (!x. x IN prob_carrier p ==> X x <= B_X) /\
    (!x. x IN prob_carrier p ==> Y x <= B_Y) /\
    indep_rv p X Y
    ==> nn_expectation p (\x. X x * Y x) =
        nn_expectation p X * nn_expectation p Y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `gn = \n (x:A). nonneg_simple_fn_approx p (X:A->real) n x *
                               nonneg_simple_fn_approx p (Y:A->real) n x` THEN
  (* MCT for product: gn -> X*Y *)
  SUBGOAL_THEN `((\n. nn_expectation (p:A prob_space) ((gn:num->A->real) n)) --->
                  nn_expectation p (\x:A. (X:A->real) x * Y x)) sequentially`
    ASSUME_TAC THENL
  [MATCH_MP_TAC(ISPEC `p:A prob_space` MCT_NN_EXPECTATION_RV) THEN
   EXISTS_TAC `B_X * B_Y:real` THEN REPEAT CONJ_TAC THENL
   [(* random_variable gn n *)
    GEN_TAC THEN EXPAND_TAC "gn" THEN BETA_TAC THEN
    SUBGOAL_THEN `simple_rv p (nonneg_simple_fn_approx p (X:A->real) n)` ASSUME_TAC THENL
    [MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_SIMPLE_RV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `simple_rv p (nonneg_simple_fn_approx p (Y:A->real) n)` ASSUME_TAC THENL
    [MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_SIMPLE_RV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `simple_rv p (\x:A. nonneg_simple_fn_approx p (X:A->real) n x *
      nonneg_simple_fn_approx p (Y:A->real) n x)` MP_TAC THENL
    [MATCH_MP_TAC SIMPLE_RV_MUL THEN
     CONJ_TAC THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[simple_rv] THEN MESON_TAC[]];
    (* gn nonneg *)
    REPEAT GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "gn" THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[NONNEG_SIMPLE_FN_APPROX_NONNEG];
    (* gn monotone *)
    REPEAT GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "gn" THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[NONNEG_SIMPLE_FN_APPROX_NONNEG] THEN
    CONJ_TAC THEN MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_MONO THEN
    ASM_SIMP_TAC[LE; LE_REFL];
    (* gn converges to X*Y *)
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
    EXPAND_TAC "gn" THEN BETA_TAC THEN
    MATCH_MP_TAC REALLIM_MUL THEN CONJ_TAC THEN
    MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_CONVERGES THEN ASM_SIMP_TAC[];
    (* X*Y nonneg *)
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[];
    (* X*Y bounded *)
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  (* MCT for X *)
  SUBGOAL_THEN `((\n. nn_expectation (p:A prob_space) (nonneg_simple_fn_approx p (X:A->real) n)) --->
                  nn_expectation p X) sequentially` ASSUME_TAC THENL
  [MATCH_MP_TAC(ISPEC `p:A prob_space` MCT_NN_EXPECTATION_RV) THEN
   EXISTS_TAC `B_X:real` THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN SUBGOAL_THEN `simple_rv p (nonneg_simple_fn_approx p (X:A->real) n)`
     (fun th -> REWRITE_TAC[REWRITE_RULE[simple_rv] th]) THEN
    MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_SIMPLE_RV THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[NONNEG_SIMPLE_FN_APPROX_NONNEG];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_MONO THEN
    ASM_SIMP_TAC[LE; LE_REFL];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_CONVERGES THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  (* MCT for Y *)
  SUBGOAL_THEN `((\n. nn_expectation (p:A prob_space) (nonneg_simple_fn_approx p (Y:A->real) n)) --->
                  nn_expectation p Y) sequentially` ASSUME_TAC THENL
  [MATCH_MP_TAC(ISPEC `p:A prob_space` MCT_NN_EXPECTATION_RV) THEN
   EXISTS_TAC `B_Y:real` THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN SUBGOAL_THEN `simple_rv p (nonneg_simple_fn_approx p (Y:A->real) n)`
     (fun th -> REWRITE_TAC[REWRITE_RULE[simple_rv] th]) THEN
    MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_SIMPLE_RV THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[NONNEG_SIMPLE_FN_APPROX_NONNEG];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_MONO THEN
    ASM_SIMP_TAC[LE; LE_REFL];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_CONVERGES THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  (* Key: for each n, nn_exp(gn n) = nn_exp(nsfa_X n) * nn_exp(nsfa_Y n) *)
  SUBGOAL_THEN `!n. nn_expectation (p:A prob_space) ((gn:num->A->real) n) =
    nn_expectation p (nonneg_simple_fn_approx p (X:A->real) n) *
    nn_expectation p (nonneg_simple_fn_approx p (Y:A->real) n)` ASSUME_TAC THENL
  [GEN_TAC THEN
   SUBGOAL_THEN `simple_rv p (nonneg_simple_fn_approx p (X:A->real) n)` ASSUME_TAC THENL
   [MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_SIMPLE_RV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `simple_rv p (nonneg_simple_fn_approx p (Y:A->real) n)` ASSUME_TAC THENL
   [MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_SIMPLE_RV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `indep_rv p (nonneg_simple_fn_approx p (X:A->real) n)
                             (nonneg_simple_fn_approx p (Y:A->real) n)` ASSUME_TAC THENL
   [MATCH_MP_TAC INDEP_RV_NSFA THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   EXPAND_TAC "gn" THEN BETA_TAC THEN
   SUBGOAL_THEN `simple_rv p (\x:A. nonneg_simple_fn_approx p (X:A->real) n x *
     nonneg_simple_fn_approx p (Y:A->real) n x)` ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_MUL THEN
    CONJ_TAC THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_SIMP_TAC[NN_EXPECTATION_SIMPLE; NONNEG_SIMPLE_FN_APPROX_NONNEG;
                REAL_LE_MUL] THEN
   ASM_SIMP_TAC[GSYM EXPECTATION_SIMPLE_AGREE] THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `nonneg_simple_fn_approx p (X:A->real) n`;
     `nonneg_simple_fn_approx p (Y:A->real) n`]
     EXPECTATION_PRODUCT_INDEP_SIMPLE) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC;
   ALL_TAC] THEN
  (* Combine: use REALLIM_UNIQUE *)
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC `\n. nn_expectation (p:A prob_space) ((gn:num->A->real) n)` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  CONJ_TAC THENL
  [ASM_REWRITE_TAC[];
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REALLIM_MUL THEN ASM_REWRITE_TAC[]]);;

(* For nonneg bounded functions, expectation = nn_expectation *)
let BOUNDED_EXPECTATION_NONNEG_EQ_NN = prove
 (`!p:A prob_space (f:A->real).
    random_variable p f /\
    (!x. x IN prob_carrier p ==> &0 <= f x) /\
    (?B. !x. x IN prob_carrier p ==> f x <= B)
    ==> expectation p f = nn_expectation p f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[expectation] THEN
  SUBGOAL_THEN `nn_expectation (p:A prob_space) (\x. max ((f:A->real) x) (&0)) =
    nn_expectation p f` SUBST1_TAC THENL
  [MATCH_MP_TAC NN_EXPECTATION_EXT THEN GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= f ==> max f (&0) = f`) THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `nn_expectation (p:A prob_space) (\x. max (--((f:A->real) x)) (&0)) = &0`
    (fun th -> REWRITE_TAC[th; REAL_SUB_RZERO]) THEN
  SUBGOAL_THEN `nn_expectation (p:A prob_space) (\x. max (--((f:A->real) x)) (&0)) =
    nn_expectation p (\x:A. &0)` SUBST1_TAC THENL
  [MATCH_MP_TAC NN_EXPECTATION_EXT THEN GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= f ==> max (--f) (&0) = &0`) THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `(\x:A. &0):A->real`] NN_EXPECTATION_SIMPLE) THEN
  REWRITE_TAC[SIMPLE_RV_CONST; REAL_LE_REFL; SIMPLE_EXPECTATION_CONST]);;

(* Shifting preserves independence *)
let INDEP_RV_SHIFT = prove
 (`!p:A prob_space (X:A->real) (Y:A->real) c d.
    indep_rv p X Y
    ==> indep_rv p (\x. X x + c) (\x. Y x + d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[indep_rv] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_SHIFT THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC RANDOM_VARIABLE_SHIFT THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ X x + c <= a /\ Y x + d <= b} =
    {x | x IN prob_carrier p /\ X x <= a - c /\ Y x <= b - d}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
   ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ X x + c <= a} =
    {x | x IN prob_carrier p /\ X x <= a - c}` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
   ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ Y x + d <= b} =
    {x | x IN prob_carrier p /\ Y x <= b - d}` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
   ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   ASM_REWRITE_TAC[]]);;

(* E[XY] = E[X]*E[Y] for bounded independent RVs *)
let EXPECTATION_PRODUCT_BOUNDED_INDEP = prove
 (`!p:A prob_space (X:A->real) (Y:A->real) B_X B_Y.
    random_variable p X /\ random_variable p Y /\
    (!x. x IN prob_carrier p ==> abs(X x) <= B_X) /\
    (!x. x IN prob_carrier p ==> abs(Y x) <= B_Y) /\
    indep_rv p X Y
    ==> expectation p (\x. X x * Y x) = expectation p X * expectation p Y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* B_X >= 0 and B_Y >= 0 *)
  SUBGOAL_THEN `?z:A. z IN prob_carrier p` STRIP_ASSUME_TAC THENL
  [MP_TAC(ISPEC `p:A prob_space` PROB_CARRIER_NONEMPTY) THEN SET_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= B_X /\ &0 <= B_Y` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((X:A->real) z)` THEN
    REWRITE_TAC[REAL_ABS_POS] THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((Y:A->real) z)` THEN
    REWRITE_TAC[REAL_ABS_POS] THEN ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  (* Shifted versions are nonneg and bounded *)
  SUBGOAL_THEN `!x:A. x IN prob_carrier p ==> &0 <= (X:A->real) x + B_X` ASSUME_TAC THENL
  [X_GEN_TAC `w:A` THEN DISCH_TAC THEN
   SUBGOAL_THEN `abs((X:A->real) w) <= B_X` MP_TAC THENL
   [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN prob_carrier p ==> &0 <= (Y:A->real) x + B_Y` ASSUME_TAC THENL
  [X_GEN_TAC `w:A` THEN DISCH_TAC THEN
   SUBGOAL_THEN `abs((Y:A->real) w) <= B_Y` MP_TAC THENL
   [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN prob_carrier p ==> (X:A->real) x + B_X <= &2 * B_X` ASSUME_TAC THENL
  [X_GEN_TAC `w:A` THEN DISCH_TAC THEN
   SUBGOAL_THEN `abs((X:A->real) w) <= B_X` MP_TAC THENL
   [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN prob_carrier p ==> (Y:A->real) x + B_Y <= &2 * B_Y` ASSUME_TAC THENL
  [X_GEN_TAC `w:A` THEN DISCH_TAC THEN
   SUBGOAL_THEN `abs((Y:A->real) w) <= B_Y` MP_TAC THENL
   [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* NN_EXPECTATION_PRODUCT_BOUNDED_INDEP for shifted versions *)
  SUBGOAL_THEN
    `nn_expectation (p:A prob_space) (\x. ((X:A->real) x + B_X) * (Y x + B_Y)) =
     nn_expectation p (\x. X x + B_X) * nn_expectation p (\x. Y x + B_Y)`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `(\x:A. (X:A->real) x + B_X):A->real`;
    `(\x:A. (Y:A->real) x + B_Y):A->real`; `&2 * B_X`; `&2 * B_Y`]
    NN_EXPECTATION_PRODUCT_BOUNDED_INDEP) THEN
   BETA_TAC THEN
   ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_SHIFT THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC RANDOM_VARIABLE_SHIFT THEN ASM_REWRITE_TAC[];
     ASM_SIMP_TAC[];
     ASM_SIMP_TAC[];
     ASM_SIMP_TAC[];
     ASM_SIMP_TAC[];
     MATCH_MP_TAC INDEP_RV_SHIFT THEN ASM_REWRITE_TAC[]];
    SIMP_TAC[]];
   ALL_TAC] THEN
  (* Convert nn_expectation to expectation *)
  SUBGOAL_THEN `nn_expectation (p:A prob_space) (\x. (X:A->real) x + B_X) =
    expectation p (\x. X x + B_X)` SUBST_ALL_TAC THENL
  [CONV_TAC SYM_CONV THEN MATCH_MP_TAC BOUNDED_EXPECTATION_NONNEG_EQ_NN THEN
   REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_SHIFT THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[];
    EXISTS_TAC `&2 * B_X` THEN ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `nn_expectation (p:A prob_space) (\x. (Y:A->real) x + B_Y) =
    expectation p (\x. Y x + B_Y)` SUBST_ALL_TAC THENL
  [CONV_TAC SYM_CONV THEN MATCH_MP_TAC BOUNDED_EXPECTATION_NONNEG_EQ_NN THEN
   REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_SHIFT THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[];
    EXISTS_TAC `&2 * B_Y` THEN ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `nn_expectation (p:A prob_space) (\x. ((X:A->real) x + B_X) * (Y x + B_Y)) =
    expectation p (\x. (X x + B_X) * (Y x + B_Y))` SUBST_ALL_TAC THENL
  [CONV_TAC SYM_CONV THEN MATCH_MP_TAC BOUNDED_EXPECTATION_NONNEG_EQ_NN THEN
   BETA_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN CONJ_TAC THEN
    MATCH_MP_TAC RANDOM_VARIABLE_SHIFT THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `w:A` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[];
    EXISTS_TAC `(&2 * B_X) * (&2 * B_Y)` THEN X_GEN_TAC `w:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  (* E[X + B_X] = E[X] + B_X and E[Y + B_Y] = E[Y] + B_Y *)
  SUBGOAL_THEN `expectation (p:A prob_space) (\x. (X:A->real) x + B_X) =
    expectation p X + B_X` ASSUME_TAC THENL
  [SUBGOAL_THEN `expectation (p:A prob_space) (\x. (X:A->real) x + B_X) =
    expectation p X + expectation p (\x:A. B_X)` SUBST1_TAC THENL
   [MATCH_MP_TAC BOUNDED_EXPECTATION_ADD THEN REPEAT CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     REWRITE_TAC[RANDOM_VARIABLE_CONST];
     EXISTS_TAC `B_X:real` THEN ASM_SIMP_TAC[];
     EXISTS_TAC `B_X:real` THEN GEN_TAC THEN DISCH_TAC THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[EXPECTATION_CONST]];
   ALL_TAC] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (\x. (Y:A->real) x + B_Y) =
    expectation p Y + B_Y` ASSUME_TAC THENL
  [SUBGOAL_THEN `expectation (p:A prob_space) (\x. (Y:A->real) x + B_Y) =
    expectation p Y + expectation p (\x:A. B_Y)` SUBST1_TAC THENL
   [MATCH_MP_TAC BOUNDED_EXPECTATION_ADD THEN REPEAT CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     REWRITE_TAC[RANDOM_VARIABLE_CONST];
     EXISTS_TAC `B_Y:real` THEN ASM_SIMP_TAC[];
     EXISTS_TAC `B_Y:real` THEN GEN_TAC THEN DISCH_TAC THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[EXPECTATION_CONST]];
   ALL_TAC] THEN
  (* Expand (X+B_X)(Y+B_Y) as XY + B_X*Y + B_Y*X + B_X*B_Y *)
  SUBGOAL_THEN `expectation (p:A prob_space) (\x. ((X:A->real) x + B_X) * ((Y:A->real) x + B_Y)) =
    expectation p (\x. X x * Y x + B_X * Y x + B_Y * X x + B_X * B_Y)` SUBST_ALL_TAC THENL
  [MATCH_MP_TAC EXPECTATION_EXT THEN X_GEN_TAC `w:A` THEN DISCH_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Split using BOUNDED_EXPECTATION_ADD *)
  MP_TAC(ISPECL [`p:A prob_space`; `(\x:A. (X:A->real) x * (Y:A->real) x):A->real`;
    `(\x:A. B_X * (Y:A->real) x + B_Y * (X:A->real) x + B_X * B_Y):A->real`]
    BOUNDED_EXPECTATION_ADD) THEN
  SUBGOAL_THEN `(\x:A. (\x. (X:A->real) x * (Y:A->real) x) x +
    (\x. B_X * Y x + B_Y * X x + B_X * B_Y) x) =
    (\x. X x * Y x + B_X * Y x + B_Y * X x + B_X * B_Y)`
    (fun th -> REWRITE_TAC[th]) THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN BETA_TAC THEN REFL_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`p:A prob_space`;
      `(\x:A. B_X * (Y:A->real) x + B_Y * (X:A->real) x):A->real`;
      `(\x:A. B_X * B_Y):A->real`] RANDOM_VARIABLE_ADD) THEN
    BETA_TAC THEN REWRITE_TAC[REAL_ADD_ASSOC] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN CONJ_TAC THEN
     MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[RANDOM_VARIABLE_CONST]];
    EXISTS_TAC `(B_X:real) * B_Y` THEN X_GEN_TAC `w:A` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_ABS_POS] THEN ASM_SIMP_TAC[];
    EXISTS_TAC `(B_X:real) * B_Y + B_Y * B_X + B_X * B_Y` THEN
    X_GEN_TAC `w:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs((X:A->real) w) <= B_X /\ abs((Y:A->real) w) <= B_Y`
      STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
      `abs a <= a1 /\ abs b <= b1 /\ abs c <= c1 ==> abs(a + b + c) <= a1 + b1 + c1`) THEN
    REPEAT CONJ_TAC THENL
    [REWRITE_TAC[REAL_ABS_MUL] THEN
     SUBGOAL_THEN `abs(B_X) = B_X` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[REAL_ABS_MUL] THEN
     SUBGOAL_THEN `abs(B_Y) = B_Y` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
     SUBGOAL_THEN `abs(B_X * B_Y) = B_X * B_Y` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC]]];
   ALL_TAC] THEN
  DISCH_TAC THEN
  (* Expand E[B_X*Y + B_Y*X + B_X*B_Y] *)
  SUBGOAL_THEN
    `expectation (p:A prob_space) (\x. B_X * (Y:A->real) x + B_Y * (X:A->real) x + B_X * B_Y) =
     B_X * expectation p Y + B_Y * expectation p X + B_X * B_Y`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `(\x:A. B_X * (Y:A->real) x + B_Y * (X:A->real) x):A->real`;
     `(\x:A. B_X * B_Y):A->real`] BOUNDED_EXPECTATION_ADD) THEN
   BETA_TAC THEN REWRITE_TAC[REAL_ADD_ASSOC] THEN
   ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN CONJ_TAC THEN
     MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[RANDOM_VARIABLE_CONST];
     EXISTS_TAC `(B_X:real) * B_Y + B_Y * B_X` THEN X_GEN_TAC `w:A` THEN DISCH_TAC THEN
     SUBGOAL_THEN `abs((X:A->real) w) <= B_X /\ abs((Y:A->real) w) <= B_Y`
       STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
     MATCH_MP_TAC(REAL_ARITH `abs a <= c1 /\ abs b <= c2 ==> abs(a + b) <= c1 + c2`) THEN
     CONJ_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THENL
     [SUBGOAL_THEN `abs(B_X) = B_X` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `abs(B_Y) = B_Y` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
     EXISTS_TAC `(B_X:real) * B_Y` THEN GEN_TAC THEN DISCH_TAC THEN
     SUBGOAL_THEN `abs(B_X * B_Y) = B_X * B_Y` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC]];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC[EXPECTATION_CONST] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `(\x:A. B_X * (Y:A->real) x):A->real`;
      `(\x:A. B_Y * (X:A->real) x):A->real`] BOUNDED_EXPECTATION_ADD) THEN
   BETA_TAC THEN
   ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[];
     EXISTS_TAC `(B_X:real) * B_Y` THEN X_GEN_TAC `w:A` THEN DISCH_TAC THEN
     REWRITE_TAC[REAL_ABS_MUL] THEN
     SUBGOAL_THEN `abs(B_X) = B_X` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[];
     EXISTS_TAC `(B_Y:real) * B_X` THEN X_GEN_TAC `w:A` THEN DISCH_TAC THEN
     REWRITE_TAC[REAL_ABS_MUL] THEN
     SUBGOAL_THEN `abs(B_Y) = B_Y` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `B_X:real`; `Y:A->real`]
     BOUNDED_EXPECTATION_CMUL) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `B_Y:real` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `B_Y:real`; `X:A->real`]
     BOUNDED_EXPECTATION_CMUL) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `B_X:real` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Final algebraic step *)
  SUBGOAL_THEN
    `expectation (p:A prob_space) (\x. (X:A->real) x * Y x) +
     (B_X * expectation p Y + B_Y * expectation p X + B_X * B_Y) =
     (expectation p X + B_X) * (expectation p Y + B_Y)`
    MP_TAC THENL
  [ASM_MESON_TAC[];
   DISCH_TAC THEN
   SUBGOAL_THEN `(expectation (p:A prob_space) (X:A->real) + B_X) * (expectation p Y + B_Y) =
     expectation p X * expectation p Y + B_X * expectation p Y +
     B_Y * expectation p X + B_X * B_Y`
     MP_TAC THENL
   [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* Generalization: E[XY] = E[X]*E[Y] for integrable independent RVs          *)
(* ========================================================================= *)

(* Simple random variables are bounded on the carrier *)
let SIMPLE_RV_ABS_BOUNDED = prove
 (`!p:A prob_space f. simple_rv p f ==>
   ?M. !x. x IN prob_carrier p ==> abs(f x) <= M`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simple_rv] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `p:A prob_space` PROB_CARRIER_NONEMPTY) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `FINITE {abs((f:A->real) x) | x IN prob_carrier (p:A prob_space)}`
    ASSUME_TAC THENL
  [SUBGOAL_THEN `{abs((f:A->real) x) | x IN prob_carrier (p:A prob_space)} =
    IMAGE abs {f x | x IN prob_carrier p}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
    MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN
    `~({abs((f:A->real) x) | x IN prob_carrier (p:A prob_space)} = {})`
    ASSUME_TAC THENL
  [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
   EXISTS_TAC `abs((f:A->real) z)` THEN EXISTS_TAC `z:A` THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC
    `{abs((f:A->real) x) | x IN prob_carrier (p:A prob_space)}` SUP_FINITE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC
    `sup {abs((f:A->real) x) | x IN prob_carrier (p:A prob_space)}` THEN
  X_GEN_TAC `w:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `w:A` THEN ASM_REWRITE_TAC[]);;

(* MCT with integrable limit instead of bounded limit *)
let MCT_NN_EXPECTATION = prove
 (`!p:A prob_space gn f.
     (!n. random_variable p (gn n)) /\
     (!n x. x IN prob_carrier p ==> &0 <= gn n x) /\
     (!n x. x IN prob_carrier p ==> gn n x <= gn (SUC n) x) /\
     (!x. x IN prob_carrier p ==> ((\n. gn n x) ---> f x) sequentially) /\
     (!x. x IN prob_carrier p ==> &0 <= f x) /\
     integrable p f
     ==> ((\n. nn_expectation p (gn n)) ---> nn_expectation p f) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN
  DISCH_TAC THEN
  (* gn n <= f pointwise *)
  SUBGOAL_THEN `!n (x:A). x IN prob_carrier p ==>
    (gn:num->A->real) n x <= f x` ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LBOUND) THEN
   EXISTS_TAC `\n. (gn:num->A->real) n x` THEN
   ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
   EXISTS_TAC `n:num` THEN REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`gn:num->A->real`; `prob_carrier (p:A prob_space)`]
     MONO_SEQ_LE) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  (* nn_exp(gn n) <= nn_exp(f) *)
  SUBGOAL_THEN `!n. nn_expectation (p:A prob_space) ((gn:num->A->real) n) <=
    nn_expectation p f` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC NN_EXPECTATION_MONO THEN
   ASM_SIMP_TAC[]; ALL_TAC] THEN
  (* nn_exp(gn n) is monotonically increasing *)
  SUBGOAL_THEN `!m n. m <= n ==>
    nn_expectation (p:A prob_space) ((gn:num->A->real) m) <=
    nn_expectation p (gn n)` ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC NN_EXPECTATION_MONO THEN
   ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`gn:num->A->real`; `prob_carrier (p:A prob_space)`]
      MONO_SEQ_LE) THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC INTEGRABLE_DOMINATED THEN EXISTS_TAC `f:A->real` THEN
    ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= abs y`) THEN
    ASM_SIMP_TAC[]]; ALL_TAC] THEN
  (* Use NN_EXPECTATION_MIN_LIMIT: for large enough k, nn_exp(min(f,k)) > nn_exp(f) - e/2 *)
  MP_TAC(SPECL [`p:A prob_space`; `f:A->real`] NN_EXPECTATION_MIN_LIMIT) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  ASM_SIMP_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:num` STRIP_ASSUME_TAC) THEN
  (* For this K: nn_exp(min(f, &K)) > nn_exp(f) - e/2 *)
  SUBGOAL_THEN `nn_expectation (p:A prob_space) (f:A->real) - e / &2 <
    nn_expectation p (\x. min (f x) (&K))` ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `K:num`) THEN REWRITE_TAC[LE_REFL] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  (* Use MCT_NN_EXPECTATION_RV for bounded min(gn,K) -> min(f,K) *)
  MP_TAC(ISPECL [`p:A prob_space`;
    `\n (x:A). min ((gn:num->A->real) n x) (&K)`;
    `\x:A. min ((f:A->real) x) (&K)`; `&K`] MCT_NN_EXPECTATION_RV) THEN
  BETA_TAC THEN ANTS_TAC THENL
  [REPEAT CONJ_TAC THENL
   [(* random_variable min(gn n, K) *)
    GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
    REWRITE_TAC[ETA_AX; RANDOM_VARIABLE_CONST] THEN ASM_REWRITE_TAC[];
    (* nonneg *)
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= min a b`) THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    (* monotone *)
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> min a c <= min b c`) THEN
    ASM_SIMP_TAC[];
    (* pointwise convergence *)
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC REALLIM_MIN THEN CONJ_TAC THENL
    [ASM_SIMP_TAC[]; REWRITE_TAC[REALLIM_CONST]];
    (* f nonneg *)
    GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= min a b`) THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    (* bounded by K *)
    GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC]; ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  ASM_SIMP_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  (* For n >= N: nn_exp(min(gn n, K)) is close to nn_exp(min(f, K)) *)
  (* And min(gn n, K) <= gn n, so nn_exp(min(gn n, K)) <= nn_exp(gn n) *)
  SUBGOAL_THEN
    `nn_expectation (p:A prob_space) (\x:A. min ((gn:num->A->real) n x) (&K)) <=
     nn_expectation p (gn n)` ASSUME_TAC THENL
  [MATCH_MP_TAC NN_EXPECTATION_MONO THEN BETA_TAC THEN
   ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= min a b`) THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
    MATCH_MP_TAC INTEGRABLE_DOMINATED THEN EXISTS_TAC `f:A->real` THEN
    ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= abs y`) THEN
    ASM_SIMP_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(nn_expectation (p:A prob_space) (\x:A. min ((gn:num->A->real) n x) (&K)) -
     nn_expectation p (\x. min ((f:A->real) x) (&K))) < e / &2`
    ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `nn_expectation (p:A prob_space) ((gn:num->A->real) n) <=
     nn_expectation p f` ASSUME_TAC THENL
  [MATCH_MP_TAC NN_EXPECTATION_MONO THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Truncation of expectation converges *)
let EXPECTATION_TRUNCATION_LIMIT = prove
 (`!p:A prob_space f.
    integrable p f
    ==> ((\n. expectation p (\x. max (min (f x) (&n)) (--(&n)))) --->
         expectation p f) sequentially`,
  REPEAT STRIP_TAC THEN
  (* Decompose trunc into positive and negative parts *)
  SUBGOAL_THEN `!x:A n. max (min ((f:A->real) x) (&n)) (--(&n)) =
    min (max (f x) (&0)) (&n) - min (max (--(f x)) (&0)) (&n)`
    ASSUME_TAC THENL [REPEAT GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. max ((f:A->real) x) (&0))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_POS_PART THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. max (--((f:A->real) x)) (&0))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_NEG_PART THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`p:A prob_space`; `\x:A. max ((f:A->real) x) (&0)`]
    NN_EXPECTATION_MIN_LIMIT) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL [GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
   ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  MP_TAC(SPECL [`p:A prob_space`; `\x:A. max (--((f:A->real) x)) (&0)`]
    NN_EXPECTATION_MIN_LIMIT) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL [GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
   ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  (* Use REALLIM_SEQUENTIALLY directly to avoid variable capture *)
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(LABEL_TAC "NEG") THEN
  DISCH_THEN(LABEL_TAC "POS") THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REMOVE_THEN "POS" (MP_TAC o SPEC `e / &2`) THEN
  REMOVE_THEN "NEG" (MP_TAC o SPEC `e / &2`) THEN
  ASM_SIMP_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `MAX N1 N2` THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[ARITH_RULE `MAX a b <= n <=> a <= n /\ b <= n`] THEN
  STRIP_TAC THEN
  (* Rewrite E[trunc] as nn_exp difference *)
  SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. min (max ((f:A->real) x) (&0)) (&n) -
    min (max (--(f x)) (&0)) (&n)) =
    nn_expectation p (\x. min (max (f x) (&0)) (&n)) -
    nn_expectation p (\x. min (max (--(f x)) (&0)) (&n))` SUBST1_TAC THENL
  [REWRITE_TAC[expectation] THEN
   BINOP_TAC THEN MATCH_MP_TAC NN_EXPECTATION_EXT THEN
   GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (f:A->real) =
    nn_expectation p (\x. max (f x) (&0)) -
    nn_expectation p (\x. max (--(f x)) (&0))` SUBST1_TAC THENL
  [REWRITE_TAC[expectation]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Independence preserved under min with constant *)
let INDEP_RV_MIN_CONST = prove
 (`!p:A prob_space X Y c.
    indep_rv p X Y
    ==> indep_rv p (\x. min (X x) c) (\x. min (Y x) c)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP INDEP_RV_IMP_RV) THEN
  REWRITE_TAC[indep_rv] THEN REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST];
   MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [indep_rv]) THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `c <= a` THENL
  [SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ min ((X:A->real) x) c <= a} =
    prob_carrier p` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN] THEN GEN_TAC THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ min ((X:A->real) x) c <= a /\
     min ((Y:A->real) x) c <= b} =
     {x | x IN prob_carrier p /\ min (Y x) c <= b}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   REWRITE_TAC[PROB_SPACE; REAL_MUL_LID];
   ALL_TAC] THEN
  ASM_CASES_TAC `c <= b` THENL
  [SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ min ((Y:A->real) x) c <= b} =
    prob_carrier p` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN] THEN GEN_TAC THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ min ((X:A->real) x) c <= a /\
     min ((Y:A->real) x) c <= b} =
     {x | x IN prob_carrier p /\ min (X x) c <= a}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   REWRITE_TAC[PROB_SPACE; REAL_MUL_RID];
   ALL_TAC] THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ min ((X:A->real) x) c <= a} =
    {x | x IN prob_carrier p /\ X x <= a}` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
   ASM_CASES_TAC `x:A IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ min ((Y:A->real) x) c <= b} =
    {x | x IN prob_carrier p /\ Y x <= b}` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
   ASM_CASES_TAC `x:A IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ min ((X:A->real) x) c <= a /\
    min ((Y:A->real) x) c <= b} =
    {x | x IN prob_carrier p /\ X x <= a /\ Y x <= b}` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
   ASM_CASES_TAC `x:A IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

(* Independence preserved under max with constant *)
let INDEP_RV_MAX_CONST = prove
 (`!p:A prob_space X Y c.
    indep_rv p X Y
    ==> indep_rv p (\x. max (X x) c) (\x. max (Y x) c)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP INDEP_RV_IMP_RV) THEN
  REWRITE_TAC[indep_rv] THEN REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST];
   MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [indep_rv]) THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `a < c` THENL
  [SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ max ((X:A->real) x) c <= a} = {}`
    ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
     max ((X:A->real) x) c <= a /\ max ((Y:A->real) x) c <= b} = {}`
     ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[PROB_EMPTY; REAL_MUL_LZERO];
   ALL_TAC] THEN
  ASM_CASES_TAC `b < c` THENL
  [SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ max ((Y:A->real) x) c <= b} = {}`
    ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
     max ((X:A->real) x) c <= a /\ max ((Y:A->real) x) c <= b} = {}`
     ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[PROB_EMPTY; REAL_MUL_RZERO];
   ALL_TAC] THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ max ((X:A->real) x) c <= a} =
    {x | x IN prob_carrier p /\ X x <= a}` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
   ASM_CASES_TAC `x:A IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ max ((Y:A->real) x) c <= b} =
    {x | x IN prob_carrier p /\ Y x <= b}` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
   ASM_CASES_TAC `x:A IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ max ((X:A->real) x) c <= a /\
    max ((Y:A->real) x) c <= b} =
    {x | x IN prob_carrier p /\ X x <= a /\ Y x <= b}` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
   ASM_CASES_TAC `x:A IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

(* Helper lemma: truncation preserves sign *)
let TRUNC_SAME_SIGN = prove
 (`!aa bb. &0 <= bb ==> &0 <= max (min aa bb) (--bb) * aa`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  DISJ_CASES_TAC(REAL_ARITH `&0 <= aa \/ aa < &0`) THENL
  [SUBGOAL_THEN `&0 <= max (min aa bb) (--bb)` MP_TAC THENL
   [REWRITE_TAC[REAL_LE_MAX] THEN DISJ1_TAC THEN
    REWRITE_TAC[REAL_LE_MIN] THEN ASM_REAL_ARITH_TAC;
    ASM_MESON_TAC[REAL_LE_MUL]];
   SUBGOAL_THEN `max (min aa bb) (--bb) <= &0` MP_TAC THENL
   [REWRITE_TAC[REAL_MAX_LE] THEN CONJ_TAC THENL
    [MATCH_MP_TAC(REAL_ARITH `a <= &0 ==> min a b <= &0`) THEN
     ASM_REAL_ARITH_TAC;
     ASM_REAL_ARITH_TAC];
    DISCH_TAC THEN
    SUBGOAL_THEN `max (min aa bb) (--bb) * aa =
      (--max (min aa bb) (--bb)) * (--aa)` SUBST1_TAC THENL
    [REWRITE_TAC[REAL_NEG_MUL2];
     MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]]]);;

(* Helper lemma: abs of truncation equals min of abs *)
let TRUNC_ABS = prove
 (`!aa bb. &0 <= bb ==> abs(max (min aa bb) (--bb)) = min (abs aa) bb`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_max; real_min] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_REAL_ARITH_TAC);;

(* Helper lemma: abs of difference when same sign and |a| <= |b| *)
let ABS_DIFF_SAME_SIGN = prove
 (`!aa bb. &0 <= aa * bb /\ abs aa <= abs bb
           ==> abs(aa - bb) = abs bb - abs aa`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC(REAL_ARITH `&0 <= aa \/ aa < &0`) THENL
  [DISJ_CASES_TAC(REAL_ARITH `&0 <= bb \/ bb < &0`) THENL
   [STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN
    SUBGOAL_THEN `aa = &0` SUBST_ALL_TAC THENL
    [ASM_CASES_TAC `aa = &0` THEN ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN `&0 < aa` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `&0 < aa * (--bb)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_MUL_RNEG] THEN ASM_REAL_ARITH_TAC];
     ASM_REAL_ARITH_TAC]];
   DISJ_CASES_TAC(REAL_ARITH `&0 <= bb \/ bb < &0`) THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `bb = &0` SUBST_ALL_TAC THENL
    [ASM_CASES_TAC `bb = &0` THEN ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN `&0 < bb` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `&0 < (--aa) * bb` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_MUL_LNEG] THEN ASM_REAL_ARITH_TAC];
     ASM_REAL_ARITH_TAC];
    STRIP_TAC THEN ASM_REAL_ARITH_TAC]]);;

(* Helper lemma: product rearrangement *)
let PROD_REARRANGE =
  REAL_RING `!a b c d:real. (a * b) * (c * d) = (a * c) * (b * d)`;;

(* Convergence of E[trunc(X)*trunc(Y)] to E[XY] for integrable RVs *)
let EXPECTATION_TRUNCATION_PRODUCT_LIMIT = prove
 (`!p:A prob_space X Y.
    integrable p X /\ integrable p Y /\
    integrable p (\x. X x * Y x) /\
    random_variable p X /\ random_variable p Y
    ==> ((\n. expectation p
              (\x. max (min (X x) (&n)) (-- &n) *
                   max (min (Y x) (&n)) (-- &n))) --->
         expectation p (\x. X x * Y x)) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  (* Use MCT on min(|X|,n)*min(|Y|,n) -> |XY| *)
  MP_TAC(ISPECL [`p:A prob_space`;
    `\n x. min (abs((X:A->real) x)) (&n) * min (abs((Y:A->real) x)) (&n)`;
    `\x. abs((X:A->real) x * (Y:A->real) x)`]
    MCT_NN_EXPECTATION) THEN
  BETA_TAC THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THENL
   [(* random_variable *)
    GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN CONJ_TAC THEN
    MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
    ASM_SIMP_TAC[RANDOM_VARIABLE_ABS; RANDOM_VARIABLE_CONST];
    (* nonneg *)
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= min a b`) THEN
    REWRITE_TAC[REAL_ABS_POS; REAL_POS];
    (* monotone *)
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_ARITH `&0 <= min a b <=> &0 <= a /\ &0 <= b`;
                REAL_ABS_POS; REAL_POS] THEN
    CONJ_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> min x a <= min x b`) THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    (* pointwise convergence *)
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REALLIM_MUL THEN
    CONJ_TAC THENL
    [REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `ee:real` THEN
     DISCH_TAC THEN
     MP_TAC(ISPEC `abs((X:A->real) x)` REAL_ARCH_SIMPLE) THEN
     DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
     EXISTS_TAC `N:num` THEN X_GEN_TAC `nn:num` THEN DISCH_TAC THEN
     SUBGOAL_THEN `abs((X:A->real) x) <= &nn` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N` THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      ASM_REAL_ARITH_TAC];
     REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `ee:real` THEN
     DISCH_TAC THEN
     MP_TAC(ISPEC `abs((Y:A->real) x)` REAL_ARCH_SIMPLE) THEN
     DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
     EXISTS_TAC `N:num` THEN X_GEN_TAC `nn:num` THEN DISCH_TAC THEN
     SUBGOAL_THEN `abs((Y:A->real) x) <= &nn` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N` THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      ASM_REAL_ARITH_TAC]];
    (* nonneg limit *)
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS];
    (* integrable limit *)
    ASM_SIMP_TAC[INTEGRABLE_ABS]];
   ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N0:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `N0:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  (* integrability of truncated product *)
  SUBGOAL_THEN
    `integrable p (\x:A. max (min ((X:A->real) x) (&n)) (-- &n) *
                         max (min ((Y:A->real) x) (&n)) (-- &n))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
   EXISTS_TAC `&n * &n` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN CONJ_TAC THEN
    MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST];
     REWRITE_TAC[RANDOM_VARIABLE_CONST];
     MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST];
     REWRITE_TAC[RANDOM_VARIABLE_CONST]];
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    CONJ_TAC THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* integrability of difference *)
  SUBGOAL_THEN
    `integrable p (\x:A. max (min ((X:A->real) x) (&n)) (-- &n) *
                         max (min ((Y:A->real) x) (&n)) (-- &n) -
                         X x * Y x)`
    ASSUME_TAC THENL
  [REWRITE_TAC[real_sub] THEN
   ONCE_REWRITE_TAC[REAL_ARITH `a + --b = a + (-- &1) * b`] THEN
   MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* |E[trunc*trunc - XY]| = |E[trunc*trunc - XY]| <= E[|trunc*trunc - XY|] *)
  SUBGOAL_THEN
    `expectation (p:A prob_space)
       (\x. max (min ((X:A->real) x) (&n)) (-- &n) *
            max (min ((Y:A->real) x) (&n)) (-- &n)) -
     expectation p (\x. X x * Y x) =
     expectation p (\x. max (min (X x) (&n)) (-- &n) *
                        max (min (Y x) (&n)) (-- &n) - X x * Y x)`
    SUBST1_TAC THENL
  [CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXPECTATION_SUB THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `expectation (p:A prob_space) (\x.
    abs(max (min ((X:A->real) x) (&n)) (-- &n) *
        max (min ((Y:A->real) x) (&n)) (-- &n) - X x * Y x))` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC EXPECTATION_ABS_BOUND THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* E[|trunc*trunc - XY|] = E[|XY| - min|X|*min|Y|] *)
  SUBGOAL_THEN
    `!x:A. x IN prob_carrier p ==>
       abs(max (min ((X:A->real) x) (&n)) (-- &n) *
           max (min ((Y:A->real) x) (&n)) (-- &n) - X x * Y x) =
       abs(X x * Y x) - min (abs(X x)) (&n) * min (abs(Y x)) (&n)`
    ASSUME_TAC THENL
  [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   SUBGOAL_THEN `abs(max (min ((X:A->real) x) (&n)) (-- &n) *
                     max (min ((Y:A->real) x) (&n)) (-- &n)) =
                 min (abs(X x)) (&n) * min (abs(Y x)) (&n)`
     (LABEL_TAC "ABS_EQ") THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN BINOP_TAC THEN
    MATCH_MP_TAC TRUNC_ABS THEN REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
   MP_TAC(ISPECL
     [`max (min ((X:A->real) x) (&n)) (-- &n) *
       max (min (Y x) (&n)) (-- &n)`;
      `(X:A->real) x * (Y:A->real) x`] ABS_DIFF_SAME_SIGN) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [REWRITE_TAC[PROD_REARRANGE] THEN MATCH_MP_TAC REAL_LE_MUL THEN
     CONJ_TAC THEN MATCH_MP_TAC TRUNC_SAME_SIGN THEN REWRITE_TAC[REAL_POS];
     USE_THEN "ABS_EQ" (fun th -> REWRITE_TAC[th]) THEN
     REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
     REWRITE_TAC[REAL_ARITH `&0 <= min a b <=> &0 <= a /\ &0 <= b`;
                 REAL_ABS_POS; REAL_POS] THEN
     CONJ_TAC THEN MESON_TAC[REAL_MIN_MIN]];
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "ABS_EQ" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[REAL_ABS_MUL]];
   ALL_TAC] THEN
  (* Use pointwise identity to rewrite the expectation *)
  SUBGOAL_THEN
    `expectation (p:A prob_space) (\x.
       abs(max (min ((X:A->real) x) (&n)) (-- &n) *
           max (min ((Y:A->real) x) (&n)) (-- &n) - X x * Y x)) =
     expectation p (\x.
       abs(X x * Y x) - min (abs(X x)) (&n) * min (abs(Y x)) (&n))`
    SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_EXT THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  (* integrability of min*min *)
  SUBGOAL_THEN
    `integrable p (\x:A. min (abs((X:A->real) x)) (&n) * min (abs((Y:A->real) x)) (&n))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
   EXISTS_TAC `&n * &n` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN CONJ_TAC THEN
    MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
    ASM_SIMP_TAC[RANDOM_VARIABLE_ABS; RANDOM_VARIABLE_CONST];
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    CONJ_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= min a b /\ min a b <= b ==> abs(min a b) <= b`) THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= min a b`) THEN
     REWRITE_TAC[REAL_ABS_POS; REAL_POS];
     MESON_TAC[REAL_MIN_MIN];
     MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= min a b`) THEN
     REWRITE_TAC[REAL_ABS_POS; REAL_POS];
     MESON_TAC[REAL_MIN_MIN]]];
   ALL_TAC] THEN
  (* Now: E[|XY| - min*min] < e *)
  SUBGOAL_THEN
    `expectation p (\x:A. abs((X:A->real) x * Y x) -
       min (abs(X x)) (&n) * min (abs(Y x)) (&n)) =
     expectation p (\x. abs(X x * Y x)) -
     expectation p (\x. min (abs(X x)) (&n) * min (abs(Y x)) (&n))`
    SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_SUB THEN
   ASM_SIMP_TAC[INTEGRABLE_ABS];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `expectation p (\x. abs((X:A->real) x * Y x)) =
     nn_expectation p (\x. abs(X x * Y x))`
    SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_NONNEG_EQ_NN THEN
   ASM_SIMP_TAC[INTEGRABLE_ABS; REAL_ABS_POS];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `expectation p (\x. min (abs((X:A->real) x)) (&n) * min (abs((Y:A->real) x)) (&n)) =
     nn_expectation p (\x. min (abs(X x)) (&n) * min (abs(Y x)) (&n))`
    SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_NONNEG_EQ_NN THEN
   ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= min a b`) THEN
   REWRITE_TAC[REAL_ABS_POS; REAL_POS];
   ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Main theorem: E[XY] = E[X]*E[Y] for integrable independent RVs *)
let EXPECTATION_PRODUCT_INDEP = prove
 (`!p:A prob_space X Y.
    integrable p X /\ integrable p Y /\
    integrable p (\x. X x * Y x) /\
    indep_rv p X Y
    ==> expectation p (\x. X x * Y x) = expectation p X * expectation p Y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP INDEP_RV_IMP_RV) THEN
  (* Use truncation and EXPECTATION_PRODUCT_BOUNDED_INDEP *)
  (* Sn = max(min(X, n), -n), Tn = max(min(Y, n), -n) *)
  (* E[Sn * Tn] = E[Sn] * E[Tn] -> E[X] * E[Y] *)
  (* E[Sn * Tn] -> E[XY] by dominated convergence *)
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC `\n. expectation (p:A prob_space) (\x. max (min ((X:A->real) x) (&n)) (--(&n))) *
                  expectation p (\x. max (min ((Y:A->real) x) (&n)) (--(&n)))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
  [MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
   EXISTS_TAC `\n. expectation (p:A prob_space)
     (\x:A. max (min ((X:A->real) x) (&n)) (--(&n)) *
            max (min ((Y:A->real) x) (&n)) (--(&n)))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`;
      `\x:A. max (min ((X:A->real) x) (&n)) (--(&n))`;
      `\x:A. max (min ((Y:A->real) x) (&n)) (--(&n))`;
      `&n`; `&n`] EXPECTATION_PRODUCT_BOUNDED_INDEP) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN CONJ_TAC THENL
     [MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST];
      REWRITE_TAC[RANDOM_VARIABLE_CONST]];
     MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN CONJ_TAC THENL
     [MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST];
      REWRITE_TAC[RANDOM_VARIABLE_CONST]];
     GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
     GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
     MATCH_MP_TAC INDEP_RV_MAX_CONST THEN
     MATCH_MP_TAC INDEP_RV_MIN_CONST THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   (* Convergence of E[trunc(X)*trunc(Y)] to E[XY] *)
   MATCH_MP_TAC EXPECTATION_TRUNCATION_PRODUCT_LIMIT THEN
   ASM_REWRITE_TAC[];
   (* E[trunc(X)] * E[trunc(Y)] -> E[X] * E[Y] *)
   MATCH_MP_TAC REALLIM_MUL THEN CONJ_TAC THEN
   MATCH_MP_TAC EXPECTATION_TRUNCATION_LIMIT THEN ASM_REWRITE_TAC[]]);;

(* Covariance of independent integrable RVs is zero *)
let COVARIANCE_INDEP = prove
 (`!p:A prob_space X Y.
    integrable p X /\ integrable p Y /\
    integrable p (\x. X x * Y x) /\
    indep_rv p X Y
    ==> covariance p X Y = &0`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[COVARIANCE_ALT] THEN
  ASM_SIMP_TAC[EXPECTATION_PRODUCT_INDEP] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Part A: Core infrastructure for INTEGRABLE_CLT                            *)
(* ========================================================================= *)


(* INTEGRABLE_SUB, PROB_POINTWISE_TAIL_VANISHES, and
   BOUNDED_CONVERGENCE_EXPECTATION moved to expectation.ml *)


let ABS_MUL_BOUND = prove
 (`!a b. abs a <= &1 /\ abs b <= &1 ==> abs(a * b) <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * &1` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
   REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Helper lemmas for sequential continuity and truncation convergence        *)
(* ========================================================================= *)

(* Composing a continuous function with a convergent sequence *)
let REALLIM_CONTINUOUS_FUNCTION = prove
 (`!f s l. f real_continuous atreal l /\ (s ---> l) sequentially
           ==> ((\n. f(s n)) ---> f(l)) sequentially`,
  REWRITE_TAC[real_continuous_atreal; REALLIM_SEQUENTIALLY] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cont") (LABEL_TAC "seq")) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REMOVE_THEN "cont" (MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "seq" (MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` ASSUME_TAC) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(s:num->real) n`) THEN
  ANTS_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
   SIMP_TAC[]]);;

let REALLIM_COS = prove
 (`!s l. (s ---> l) sequentially
         ==> ((\n. cos(s n)) ---> cos(l)) sequentially`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REALLIM_CONTINUOUS_FUNCTION THEN
  ASM_REWRITE_TAC[REAL_CONTINUOUS_AT_COS]);;

let REALLIM_SIN = prove
 (`!s l. (s ---> l) sequentially
         ==> ((\n. sin(s n)) ---> sin(l)) sequentially`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REALLIM_CONTINUOUS_FUNCTION THEN
  ASM_REWRITE_TAC[REAL_CONTINUOUS_AT_SIN]);;

let REALLIM_TRUNCATION = prove
 (`!x:real. ((\M. max (min x (&M)) (-- &M)) ---> x) sequentially`,
  GEN_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `abs(x:real)` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `max (min x (&m)) (-- &m) = x` SUBST1_TAC THENL
  [REWRITE_TAC[real_max; real_min] THEN
   SUBGOAL_THEN `&N <= &m` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
   ASM_REAL_ARITH_TAC]);;

(* Product formula for expectations of composed simple independent RVs *)
let EXPECTATION_PRODUCT_COMPOSE_SIMPLE_INDEP = prove
 (`!p:A prob_space X Y (f:real->real).
    simple_rv p X /\ simple_rv p Y /\ indep_rv p X Y
    ==> expectation p (\x. f(X x) * f(Y x)) =
        expectation p (\x. f(X x)) * expectation p (\x. f(Y x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simple_rv p (\x:A. (f:real->real)((X:A->real) x))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] SIMPLE_RV_REAL_COMPOSE) THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv p (\x:A. (f:real->real)((Y:A->real) x))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] SIMPLE_RV_REAL_COMPOSE) THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv p (\x:A. (f:real->real)((X:A->real) x) *
    f((Y:A->real) x))` ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[EXPECTATION_SIMPLE_AGREE] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`;
    `Y:A->real`; `f:real->real`;
    `f:real->real`] SIMPLE_EXPECTATION_PRODUCT_COMPOSE_INDEP) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Gen char fn product formula for independent RVs (via truncation + nsfa)   *)
(* ========================================================================= *)

(* Product formula for gen char fns of independent RVs (real part).
   gen_char_fn_re p (X+Y) t = gen_char_fn_re p X t * gen_char_fn_re p Y t
                              - gen_char_fn_im p X t * gen_char_fn_im p Y t
   Proof: Truncate X,Y at +-M to get bounded independent approximations,
   shift to nonneg, use nsfa + INDEP_RV_NSFA for simple approximations,
   apply EXPECTATION_PRODUCT_COMPOSE_SIMPLE_INDEP, then bounded convergence. *)
let GEN_CHAR_FN_ADD_INDEP_RE = prove
 (`!p:A prob_space (X:A->real) (Y:A->real) t.
    random_variable p X /\ random_variable p Y /\ indep_rv p X Y
    ==> gen_char_fn_re p (\x. X x + Y x) t =
        gen_char_fn_re p X t * gen_char_fn_re p Y t -
        gen_char_fn_im p X t * gen_char_fn_im p Y t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[gen_char_fn_re; gen_char_fn_im] THEN BETA_TAC THEN
  (* Trig identity: cos(t*(X+Y)) = cos(tX)cos(tY) - sin(tX)sin(tY) *)
  SUBGOAL_THEN
    `!x:A. cos(t * ((X:A->real) x + (Y:A->real) x)) =
           cos(t * X x) * cos(t * Y x) - sin(t * X x) * sin(t * Y x)`
    (fun th -> REWRITE_TAC[th]) THENL
  [GEN_TAC THEN REWRITE_TAC[REAL_ADD_LDISTRIB; COS_ADD]; ALL_TAC] THEN
  (* E[cos*cos - sin*sin] = E[cos*cos] - E[sin*sin] by linearity *)
  SUBGOAL_THEN
    `expectation (p:A prob_space) (\x:A.
       cos(t * (X:A->real) x) * cos(t * (Y:A->real) x) -
       sin(t * X x) * sin(t * Y x)) =
     expectation p (\x. cos(t * X x) * cos(t * Y x)) -
     expectation p (\x. sin(t * X x) * sin(t * Y x))`
    SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_SUB THEN CONJ_TAC THEN
   MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `&1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_COS THEN
     MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC RANDOM_VARIABLE_COS THEN
     MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC ABS_MUL_BOUND THEN
    REWRITE_TAC[COS_BOUND];
    MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_SIN THEN
     MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC RANDOM_VARIABLE_SIN THEN
     MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC ABS_MUL_BOUND THEN
    REWRITE_TAC[SIN_BOUND]];
   ALL_TAC] THEN
  (* Now show E[f(tX)f(tY)] = E[f(tX)]E[f(tY)] for f = cos and f = sin *)
  SUBGOAL_THEN
    `expectation (p:A prob_space) (\x:A. cos(t * (X:A->real) x) * cos(t * (Y:A->real) x)) =
     expectation p (\x. cos(t * X x)) * expectation p (\x. cos(t * Y x)) /\
     expectation (p:A prob_space) (\x:A. sin(t * (X:A->real) x) * sin(t * (Y:A->real) x)) =
     expectation p (\x. sin(t * X x)) * expectation p (\x. sin(t * Y x))`
    (fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th] THEN REAL_ARITH_TAC) THEN
  (* Step 1: per-M truncated formula (both cos and sin, nsfa infrastructure shared) *)
  SUBGOAL_THEN `!M:num.
    expectation (p:A prob_space)
      (\x:A. cos(t * max (min ((X:A->real) x) (&M)) (-- &M)) *
             cos(t * max (min ((Y:A->real) x) (&M)) (-- &M))) =
    expectation p (\x. cos(t * max (min (X x) (&M)) (-- &M))) *
    expectation p (\x. cos(t * max (min (Y x) (&M)) (-- &M))) /\
    expectation (p:A prob_space)
      (\x:A. sin(t * max (min ((X:A->real) x) (&M)) (-- &M)) *
             sin(t * max (min ((Y:A->real) x) (&M)) (-- &M))) =
    expectation p (\x. sin(t * max (min (X x) (&M)) (-- &M))) *
    expectation p (\x. sin(t * max (min (Y x) (&M)) (-- &M)))`
    (LABEL_TAC "perM") THENL
  [GEN_TAC THEN
   (* Abbreviate the truncations *)
   ABBREV_TAC `XM = \x:A. max (min ((X:A->real) x) (&M)) (-- &M)` THEN
   ABBREV_TAC `YM = \x:A. max (min ((Y:A->real) x) (&M)) (-- &M)` THEN
   SUBGOAL_THEN `indep_rv p (XM:A->real) (YM:A->real)` ASSUME_TAC THENL
   [EXPAND_TAC "XM" THEN EXPAND_TAC "YM" THEN
    MATCH_MP_TAC INDEP_RV_MAX_CONST THEN
    MATCH_MP_TAC INDEP_RV_MIN_CONST THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `random_variable p (XM:A->real)` ASSUME_TAC THENL
   [EXPAND_TAC "XM" THEN MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN
    REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN
    MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
    ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST]; ALL_TAC] THEN
   SUBGOAL_THEN `random_variable p (YM:A->real)` ASSUME_TAC THENL
   [EXPAND_TAC "YM" THEN MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN
    REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN
    MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
    ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST]; ALL_TAC] THEN
   SUBGOAL_THEN `!x:A. x IN prob_carrier p ==> abs((XM:A->real) x) <= &M`
     ASSUME_TAC THENL
   [EXPAND_TAC "XM" THEN GEN_TAC THEN DISCH_TAC THEN
    BETA_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `!x:A. x IN prob_carrier p ==> abs((YM:A->real) x) <= &M`
     ASSUME_TAC THENL
   [EXPAND_TAC "YM" THEN GEN_TAC THEN DISCH_TAC THEN
    BETA_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
   (* Shift to nonneg: U = XM + &M, V = YM + &M *)
   ABBREV_TAC `U = \x:A. (XM:A->real) x + &M` THEN
   ABBREV_TAC `V = \x:A. (YM:A->real) x + &M` THEN
   SUBGOAL_THEN `indep_rv p (U:A->real) (V:A->real)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN EXPAND_TAC "V" THEN
    MATCH_MP_TAC INDEP_RV_SHIFT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `!x:A. x IN prob_carrier p ==> &0 <= (U:A->real) x`
     ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXPAND_TAC "U" THEN BETA_TAC THEN
    SUBGOAL_THEN `abs((XM:A->real) x) <= &M` MP_TAC THENL
    [ASM_SIMP_TAC[]; REAL_ARITH_TAC]; ALL_TAC] THEN
   SUBGOAL_THEN `!x:A. x IN prob_carrier p ==> &0 <= (V:A->real) x`
     ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXPAND_TAC "V" THEN BETA_TAC THEN
    SUBGOAL_THEN `abs((YM:A->real) x) <= &M` MP_TAC THENL
    [ASM_SIMP_TAC[]; REAL_ARITH_TAC]; ALL_TAC] THEN
   SUBGOAL_THEN `random_variable p (U:A->real)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN MATCH_MP_TAC RANDOM_VARIABLE_SHIFT THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `random_variable p (V:A->real)` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MATCH_MP_TAC RANDOM_VARIABLE_SHIFT THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   (* nsfa approximation: Wn -> XM, Zn -> YM pointwise *)
   ABBREV_TAC `Wn = \n:num (x:A).
     nonneg_simple_fn_approx p (U:A->real) n x - &M` THEN
   ABBREV_TAC `Zn = \n:num (x:A).
     nonneg_simple_fn_approx p (V:A->real) n x - &M` THEN
   SUBGOAL_THEN `!n. simple_rv p ((Wn:num->A->real) n)` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "Wn" THEN BETA_TAC THEN
    MATCH_MP_TAC SIMPLE_RV_SUB THEN CONJ_TAC THENL
    [REWRITE_TAC[ETA_AX] THEN
     MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_SIMPLE_RV THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[SIMPLE_RV_CONST]]; ALL_TAC] THEN
   SUBGOAL_THEN `!n. simple_rv p ((Zn:num->A->real) n)` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "Zn" THEN BETA_TAC THEN
    MATCH_MP_TAC SIMPLE_RV_SUB THEN CONJ_TAC THENL
    [REWRITE_TAC[ETA_AX] THEN
     MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_SIMPLE_RV THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[SIMPLE_RV_CONST]]; ALL_TAC] THEN
   SUBGOAL_THEN `!n. indep_rv p ((Wn:num->A->real) n) ((Zn:num->A->real) n)`
     ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "Wn" THEN EXPAND_TAC "Zn" THEN BETA_TAC THEN
    REWRITE_TAC[real_sub] THEN
    MATCH_MP_TAC INDEP_RV_SHIFT THEN REWRITE_TAC[REAL_NEG_NEG] THEN
    REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC INDEP_RV_NSFA THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `!x:A. x IN prob_carrier p ==>
     ((\n. (Wn:num->A->real) n x) ---> (XM:A->real) x) sequentially`
     ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXPAND_TAC "Wn" THEN
    BETA_TAC THEN
    SUBGOAL_THEN `(XM:A->real) x = (U:A->real) x - &M` SUBST1_TAC THENL
    [EXPAND_TAC "U" THEN BETA_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REALLIM_SUB THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_CONVERGES THEN ASM_SIMP_TAC[];
     REWRITE_TAC[REALLIM_CONST]]; ALL_TAC] THEN
   SUBGOAL_THEN `!x:A. x IN prob_carrier p ==>
     ((\n. (Zn:num->A->real) n x) ---> (YM:A->real) x) sequentially`
     ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXPAND_TAC "Zn" THEN
    BETA_TAC THEN
    SUBGOAL_THEN `(YM:A->real) x = (V:A->real) x - &M` SUBST1_TAC THENL
    [EXPAND_TAC "V" THEN BETA_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REALLIM_SUB THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_CONVERGES THEN ASM_SIMP_TAC[];
     REWRITE_TAC[REALLIM_CONST]]; ALL_TAC] THEN
   (* For each n: product formula for both cos and sin via
      EXPECTATION_PRODUCT_COMPOSE_SIMPLE_INDEP *)
   SUBGOAL_THEN `!n (f:real->real).
     expectation (p:A prob_space)
       (\x:A. f(t * (Wn:num->A->real) n x) * f(t * (Zn:num->A->real) n x)) =
     expectation p (\x. f(t * Wn n x)) *
     expectation p (\x. f(t * Zn n x))` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `(Wn:num->A->real) n`;
                    `(Zn:num->A->real) n`; `\y:real. (f:real->real)(t * y)`]
           EXPECTATION_PRODUCT_COMPOSE_SIMPLE_INDEP) THEN
    BETA_TAC THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]; ALL_TAC] THEN
   (* Pre-establish random_variable for Wn and Zn to avoid slow MESON *)
   SUBGOAL_THEN `!n. random_variable p ((Wn:num->A->real) n)` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(SPEC `n:num` (ASSUME `!n. simple_rv p ((Wn:num->A->real) n)`)) THEN
    REWRITE_TAC[simple_rv] THEN SIMP_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `!n. random_variable p ((Zn:num->A->real) n)` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(SPEC `n:num` (ASSUME `!n. simple_rv p ((Zn:num->A->real) n)`)) THEN
    REWRITE_TAC[simple_rv] THEN SIMP_TAC[]; ALL_TAC] THEN
   (* Take limit n -> infinity by BCT: prove both cos and sin at once *)
   CONJ_TAC THEN
   MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THENL
   [EXISTS_TAC `\n:num. expectation (p:A prob_space)
      (\x:A. cos(t * (Wn:num->A->real) n x) *
             cos(t * (Zn:num->A->real) n x))`;
    EXISTS_TAC `\n:num. expectation (p:A prob_space)
      (\x:A. sin(t * (Wn:num->A->real) n x) *
             sin(t * (Zn:num->A->real) n x))`] THEN
   (CONJ_TAC THENL [REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY]; ALL_TAC]) THEN
   (CONJ_TAC THENL
   [(* LHS: E[f(tWn)*f(tZn)] -> E[f(tXM)*f(tYM)] by BCT *)
    MATCH_MP_TAC BOUNDED_CONVERGENCE_EXPECTATION THEN
    EXISTS_TAC `&1` THEN REPEAT CONJ_TAC THENL
    [GEN_TAC THEN BETA_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN
     CONJ_TAC THEN
     FIRST [MATCH_MP_TAC RANDOM_VARIABLE_COS;
            MATCH_MP_TAC RANDOM_VARIABLE_SIN] THEN
     MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN
     REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN CONJ_TAC THEN
     FIRST [MATCH_MP_TAC RANDOM_VARIABLE_COS;
            MATCH_MP_TAC RANDOM_VARIABLE_SIN] THEN
     MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[];
     REPEAT STRIP_TAC THEN BETA_TAC THEN
     MATCH_MP_TAC ABS_MUL_BOUND THEN
     REWRITE_TAC[COS_BOUND; SIN_BOUND];
     REPEAT STRIP_TAC THEN BETA_TAC THEN
     MATCH_MP_TAC ABS_MUL_BOUND THEN
     REWRITE_TAC[COS_BOUND; SIN_BOUND];
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
     MATCH_MP_TAC REALLIM_MUL THEN CONJ_TAC THENL
     [FIRST [MATCH_MP_TAC REALLIM_COS; MATCH_MP_TAC REALLIM_SIN] THEN
      MATCH_MP_TAC REALLIM_LMUL THEN
      SUBGOAL_THEN `max (min ((X:A->real) x) (&M)) (-- &M) = (XM:A->real) x`
        (fun th -> REWRITE_TAC[th]) THENL
      [EXPAND_TAC "XM" THEN BETA_TAC THEN REFL_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[];
      FIRST [MATCH_MP_TAC REALLIM_COS; MATCH_MP_TAC REALLIM_SIN] THEN
      MATCH_MP_TAC REALLIM_LMUL THEN
      SUBGOAL_THEN `max (min ((Y:A->real) x) (&M)) (-- &M) = (YM:A->real) x`
        (fun th -> REWRITE_TAC[th]) THENL
      [EXPAND_TAC "YM" THEN BETA_TAC THEN REFL_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[]]];
    ALL_TAC]) THEN
   (* RHS: E[f(tWn)]*E[f(tZn)] -> E[f(tXM)]*E[f(tYM)] *)
   (ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REALLIM_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC BOUNDED_CONVERGENCE_EXPECTATION THEN
    EXISTS_TAC `&1` THEN REPEAT CONJ_TAC THENL
    [GEN_TAC THEN BETA_TAC THEN
     FIRST [MATCH_MP_TAC RANDOM_VARIABLE_COS;
            MATCH_MP_TAC RANDOM_VARIABLE_SIN] THEN
     MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN
     REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
     FIRST [MATCH_MP_TAC RANDOM_VARIABLE_COS;
            MATCH_MP_TAC RANDOM_VARIABLE_SIN] THEN
     MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[];
     REPEAT STRIP_TAC THEN BETA_TAC THEN
     REWRITE_TAC[COS_BOUND; SIN_BOUND];
     REPEAT STRIP_TAC THEN BETA_TAC THEN
     REWRITE_TAC[COS_BOUND; SIN_BOUND];
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
     FIRST [MATCH_MP_TAC REALLIM_COS; MATCH_MP_TAC REALLIM_SIN] THEN
     MATCH_MP_TAC REALLIM_LMUL THEN
     SUBGOAL_THEN `max (min ((X:A->real) x) (&M)) (-- &M) = (XM:A->real) x`
       (fun th -> REWRITE_TAC[th]) THENL
     [EXPAND_TAC "XM" THEN BETA_TAC THEN REFL_TAC; ALL_TAC] THEN
     ASM_SIMP_TAC[]];
    MATCH_MP_TAC BOUNDED_CONVERGENCE_EXPECTATION THEN
    EXISTS_TAC `&1` THEN REPEAT CONJ_TAC THENL
    [GEN_TAC THEN BETA_TAC THEN
     FIRST [MATCH_MP_TAC RANDOM_VARIABLE_COS;
            MATCH_MP_TAC RANDOM_VARIABLE_SIN] THEN
     MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN
     REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
     FIRST [MATCH_MP_TAC RANDOM_VARIABLE_COS;
            MATCH_MP_TAC RANDOM_VARIABLE_SIN] THEN
     MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[];
     REPEAT STRIP_TAC THEN BETA_TAC THEN
     REWRITE_TAC[COS_BOUND; SIN_BOUND];
     REPEAT STRIP_TAC THEN BETA_TAC THEN
     REWRITE_TAC[COS_BOUND; SIN_BOUND];
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
     FIRST [MATCH_MP_TAC REALLIM_COS; MATCH_MP_TAC REALLIM_SIN] THEN
     MATCH_MP_TAC REALLIM_LMUL THEN
     SUBGOAL_THEN `max (min ((Y:A->real) x) (&M)) (-- &M) = (YM:A->real) x`
       (fun th -> REWRITE_TAC[th]) THENL
     [EXPAND_TAC "YM" THEN BETA_TAC THEN REFL_TAC; ALL_TAC] THEN
     ASM_SIMP_TAC[]]]);
   ALL_TAC] THEN
  (* Step 2: outer BCT for both cos and sin *)
  CONJ_TAC THENL
  [(* cos*cos case *)
   MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
   EXISTS_TAC `\M:num. expectation (p:A prob_space)
     (\x:A. cos(t * max (min ((X:A->real) x) (&M)) (-- &M)) *
            cos(t * max (min ((Y:A->real) x) (&M)) (-- &M)))` THEN
   CONJ_TAC THENL [REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY]; ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC BOUNDED_CONVERGENCE_EXPECTATION THEN
    EXISTS_TAC `&1` THEN REPEAT CONJ_TAC THENL
    [GEN_TAC THEN BETA_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN
     CONJ_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_COS THEN
     MATCH_MP_TAC RANDOM_VARIABLE_CMUL THENL
     [MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN
      REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN
      MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
      ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST];
      MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN
      REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN
      MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
      ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST]];
     MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN CONJ_TAC THEN
     MATCH_MP_TAC RANDOM_VARIABLE_COS THEN
     MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[];
     REPEAT STRIP_TAC THEN BETA_TAC THEN
     MATCH_MP_TAC ABS_MUL_BOUND THEN
     REWRITE_TAC[COS_BOUND];
     REPEAT STRIP_TAC THEN BETA_TAC THEN
     MATCH_MP_TAC ABS_MUL_BOUND THEN
     REWRITE_TAC[COS_BOUND];
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
     MATCH_MP_TAC REALLIM_MUL THEN CONJ_TAC THEN
     MATCH_MP_TAC REALLIM_COS THEN
     MATCH_MP_TAC REALLIM_LMUL THEN
     REWRITE_TAC[REALLIM_TRUNCATION]];
    ALL_TAC] THEN
   USE_THEN "perM" (fun th -> REWRITE_TAC[th]) THEN
   MATCH_MP_TAC REALLIM_MUL THEN CONJ_TAC THEN
   MATCH_MP_TAC BOUNDED_CONVERGENCE_EXPECTATION THEN
   EXISTS_TAC `&1` THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_COS THEN
    MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN
    MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN
    REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN
    MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
    ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST];
    MATCH_MP_TAC RANDOM_VARIABLE_COS THEN
    MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[COS_BOUND];
    REPEAT STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[COS_BOUND];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REALLIM_COS THEN
    MATCH_MP_TAC REALLIM_LMUL THEN REWRITE_TAC[REALLIM_TRUNCATION];
    GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_COS THEN
    MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN
    MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN
    REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN
    MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
    ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST];
    MATCH_MP_TAC RANDOM_VARIABLE_COS THEN
    MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[COS_BOUND];
    REPEAT STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[COS_BOUND];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REALLIM_COS THEN
    MATCH_MP_TAC REALLIM_LMUL THEN REWRITE_TAC[REALLIM_TRUNCATION]]
  ;
   (* sin*sin case *)
   MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
   EXISTS_TAC `\M:num. expectation (p:A prob_space)
     (\x:A. sin(t * max (min ((X:A->real) x) (&M)) (-- &M)) *
            sin(t * max (min ((Y:A->real) x) (&M)) (-- &M)))` THEN
   CONJ_TAC THENL [REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY]; ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC BOUNDED_CONVERGENCE_EXPECTATION THEN
    EXISTS_TAC `&1` THEN REPEAT CONJ_TAC THENL
    [GEN_TAC THEN BETA_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN
     CONJ_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_SIN THEN
     MATCH_MP_TAC RANDOM_VARIABLE_CMUL THENL
     [MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN
      REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN
      MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
      ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST];
      MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN
      REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN
      MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
      ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST]];
     MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN CONJ_TAC THEN
     MATCH_MP_TAC RANDOM_VARIABLE_SIN THEN
     MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[];
     REPEAT STRIP_TAC THEN BETA_TAC THEN
     MATCH_MP_TAC ABS_MUL_BOUND THEN
     REWRITE_TAC[SIN_BOUND];
     REPEAT STRIP_TAC THEN BETA_TAC THEN
     MATCH_MP_TAC ABS_MUL_BOUND THEN
     REWRITE_TAC[SIN_BOUND];
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
     MATCH_MP_TAC REALLIM_MUL THEN CONJ_TAC THEN
     MATCH_MP_TAC REALLIM_SIN THEN
     MATCH_MP_TAC REALLIM_LMUL THEN
     REWRITE_TAC[REALLIM_TRUNCATION]];
    ALL_TAC] THEN
   USE_THEN "perM" (fun th -> REWRITE_TAC[th]) THEN
   MATCH_MP_TAC REALLIM_MUL THEN CONJ_TAC THEN
   MATCH_MP_TAC BOUNDED_CONVERGENCE_EXPECTATION THEN
   EXISTS_TAC `&1` THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_SIN THEN
    MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN
    MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN
    REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN
    MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
    ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST];
    MATCH_MP_TAC RANDOM_VARIABLE_SIN THEN
    MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[SIN_BOUND];
    REPEAT STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[SIN_BOUND];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REALLIM_SIN THEN
    MATCH_MP_TAC REALLIM_LMUL THEN REWRITE_TAC[REALLIM_TRUNCATION];
    GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_SIN THEN
    MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN
    MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN
    REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN
    MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
    ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST];
    MATCH_MP_TAC RANDOM_VARIABLE_SIN THEN
    MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[SIN_BOUND];
    REPEAT STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[SIN_BOUND];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REALLIM_SIN THEN
    MATCH_MP_TAC REALLIM_LMUL THEN REWRITE_TAC[REALLIM_TRUNCATION]]]);;

(* GEN_CHAR_FN_ADD_INDEP_IM for integrable (random_variable) RVs.
   Derived from GEN_CHAR_FN_ADD_INDEP_RE via a phase shift:
   sin(t(X+Y)) = cos(t(X+Y) - pi/2) = cos(tX + t(Y - pi/(2t)))
   Then apply the RE formula with Y' = Y - pi/(2t) and simplify. *)
let GEN_CHAR_FN_ADD_INDEP_IM = prove
 (`!p:A prob_space X Y t.
    random_variable p X /\ random_variable p Y /\ indep_rv p X Y
    ==> gen_char_fn_im p (\x. X x + Y x) t =
        gen_char_fn_re p X t * gen_char_fn_im p Y t +
        gen_char_fn_im p X t * gen_char_fn_re p Y t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `t = &0` THENL
  [ASM_REWRITE_TAC[gen_char_fn_im; gen_char_fn_re; REAL_MUL_LZERO;
                    SIN_0; COS_0; EXPECTATION_CONST] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Define c = -pi/(2*t) and Y' = \x. Y x + c *)
  ABBREV_TAC `c = --(pi / (&2 * t))` THEN
  ABBREV_TAC `Y' = \x:A. (Y:A->real) x + c` THEN
  (* Key trig identities: t * (y + c) = t*y - pi/2 *)
  SUBGOAL_THEN `!y:real. t * (y + c) = t * y - pi / &2` ASSUME_TAC THENL
  [X_GEN_TAC `y:real` THEN EXPAND_TAC "c" THEN
   UNDISCH_TAC `~(t = &0)` THEN CONV_TAC REAL_FIELD;
   ALL_TAC] THEN
  (* cos(t*y - pi/2) = sin(t*y) and sin(t*y - pi/2) = -cos(t*y) *)
  SUBGOAL_THEN `!y:real. cos(t * y - pi / &2) = sin(t * y)` ASSUME_TAC THENL
  [GEN_TAC THEN REWRITE_TAC[real_sub] THEN
   REWRITE_TAC[COS_ADD; COS_NEG; SIN_NEG] THEN
   REWRITE_TAC[COS_PI2; SIN_PI2] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `!y:real. sin(t * y - pi / &2) = --(cos(t * y))` ASSUME_TAC THENL
  [GEN_TAC THEN REWRITE_TAC[real_sub] THEN
   REWRITE_TAC[SIN_ADD; COS_NEG; SIN_NEG] THEN
   REWRITE_TAC[COS_PI2; SIN_PI2] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Y' is random_variable *)
  SUBGOAL_THEN `random_variable (p:A prob_space) (Y':A->real)` ASSUME_TAC THENL
  [EXPAND_TAC "Y'" THEN MATCH_MP_TAC RANDOM_VARIABLE_SHIFT THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* X and Y' are independent *)
  SUBGOAL_THEN `indep_rv (p:A prob_space) (X:A->real) (Y':A->real)` ASSUME_TAC THENL
  [EXPAND_TAC "Y'" THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `Y:A->real`;
                   `&0`; `c:real`] INDEP_RV_SHIFT) THEN
   ASM_REWRITE_TAC[REAL_ADD_RID; ETA_AX];
   ALL_TAC] THEN
  (* Apply GEN_CHAR_FN_ADD_INDEP_RE to X and Y' *)
  MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `Y':A->real`; `t:real`]
    GEN_CHAR_FN_ADD_INDEP_RE) THEN
  ASM_REWRITE_TAC[] THEN
  (* LHS: gen_char_fn_re p (\x. X x + Y' x) t *)
  SUBGOAL_THEN `(\x:A. (X:A->real) x + (Y':A->real) x) =
                (\x. X x + Y x + c)` SUBST1_TAC THENL
  [EXPAND_TAC "Y'" THEN REWRITE_TAC[FUN_EQ_THM] THEN
   GEN_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* gen_char_fn_re p (\x. X x + Y x + c) t = gen_char_fn_im p (\x. X x + Y x) t *)
  SUBGOAL_THEN `gen_char_fn_re (p:A prob_space) (\x:A. X x + Y x + c) t =
                gen_char_fn_im p (\x. X x + Y x) t` SUBST1_TAC THENL
  [REWRITE_TAC[gen_char_fn_re; gen_char_fn_im] THEN
   AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
   X_GEN_TAC `a:A` THEN
   SUBGOAL_THEN `t * ((X:A->real) a + (Y:A->real) a + c) =
                 t * (X a + Y a) + t * c` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `t * c = --(pi / &2)` SUBST1_TAC THENL
   [EXPAND_TAC "c" THEN UNDISCH_TAC `~(t = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
   REWRITE_TAC[GSYM real_sub] THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* RHS: gen_char_fn_re/im of Y' in terms of Y *)
  SUBGOAL_THEN `gen_char_fn_re (p:A prob_space) (Y':A->real) t =
                gen_char_fn_im p Y t` SUBST1_TAC THENL
  [REWRITE_TAC[gen_char_fn_re; gen_char_fn_im] THEN
   AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
   X_GEN_TAC `a:A` THEN EXPAND_TAC "Y'" THEN BETA_TAC THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `gen_char_fn_im (p:A prob_space) (Y':A->real) t =
                --(gen_char_fn_re p Y t)` SUBST1_TAC THENL
  [REWRITE_TAC[gen_char_fn_im; gen_char_fn_re] THEN
   SUBGOAL_THEN `(\x:A. sin(t * (Y':A->real) x)) =
                 (\x. --(cos(t * (Y:A->real) x)))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `a:A` THEN
    EXPAND_TAC "Y'" THEN BETA_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `!g:A->real. expectation (p:A prob_space) (\x. --(g x)) =
                 --(expectation p g)` (fun th -> REWRITE_TAC[th]) THEN
   GEN_TAC THEN REWRITE_TAC[expectation; REAL_NEG_NEG] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Phase 21: DCT and integrable CLT char fn convergence                      *)
(* ========================================================================= *)


(* |sin(x) - x| <= x^2 for all x *)
let SIN_MINUS_X_SQ_BOUND = prove
 (`!x:real. abs(sin x - x) <= x pow 2`,
  GEN_TAC THEN
  DISJ_CASES_TAC (REAL_ARITH `abs x <= &2 \/ &2 < abs x`) THENL
  [(* Case |x| <= 2: chain through |x|^3/2 *)
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `abs(x) pow 3 / &2` THEN
   REWRITE_TAC[SIN_APPROX_BOUND] THEN
   (* |x|^3/2 = |x|/2 * x^2, and |x|/2 <= 1 when |x| <= 2 *)
   SUBGOAL_THEN `abs(x) pow 3 / &2 = (abs x / &2) * x pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `3 = SUC 2`; real_pow; REAL_POW2_ABS] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
   SUBGOAL_THEN `x pow 2 = &1 * x pow 2` (fun th ->
     GEN_REWRITE_TAC (RAND_CONV) [th]) THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_MUL2 THEN
   REWRITE_TAC[REAL_LE_POW_2] THEN
   REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC;
   (* Case |x| > 2: |sin x - x| <= 1 + |x| <= x^2 *)
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `&1 + abs x` THEN CONJ_TAC THENL
   [MP_TAC(SPEC `x:real` SIN_BOUND) THEN REAL_ARITH_TAC;
    (* 1 + |x| <= x^2 when |x| > 2 *)
    SUBGOAL_THEN `x pow 2 = abs x * abs x`
      (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[GSYM REAL_POW_2; REAL_POW2_ABS]; ALL_TAC] THEN
    SUBGOAL_THEN `&2 * abs x <= abs x * abs x` ASSUME_TAC THENL
    [ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
     REWRITE_TAC[GSYM REAL_SUB_RDISTRIB] THEN
     MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
     ASM_REAL_ARITH_TAC]]]);;

(* 0 <= cos(x) - 1 + x^2/2 *)
let COS_TAYLOR_NONNEG = prove
 (`!x. &0 <= cos x - &1 + x pow 2 / &2`,
  GEN_TAC THEN MP_TAC(SPEC `x:real` COS_LOWER_BOUND) THEN
  REAL_ARITH_TAC);;

(* cos(x) - 1 + x^2/2 <= x^2/2 *)
let COS_TAYLOR_UPPER = prove
 (`!x. cos x - &1 + x pow 2 / &2 <= x pow 2 / &2`,
  GEN_TAC THEN MP_TAC(SPEC `x:real` COS_BOUNDS) THEN
  REAL_ARITH_TAC);;

(* cos(x) - 1 + x^2/2 <= x^4/6 (without abs, using non-negativity) *)
let COS_TAYLOR_BOUND_4 = prove
 (`!x:real. cos x - &1 + x pow 2 / &2 <= x pow 4 / &6`,
  GEN_TAC THEN
  MP_TAC(SPEC `x:real` COS_APPROX_BOUND) THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Phase 21b: CLT char fn convergence for integrable RVs                     *)
(* Key approach: Only need E[X^2] < inf (no higher moments) via DCT.         *)
(* Uses: |sin(z)-z| <= z^2, 0 <= cos(z)-1+z^2/2 <= z^4/6                     *)
(* ========================================================================= *)

(* inv(SUC n) --> 0 *)
let REALLIM_1_OVER_SUC = prove
 (`((\n. inv(&(SUC n))) ---> &0) sequentially`,
  SUBGOAL_THEN `(\n. inv(&(SUC n))) = (\n. inv(&n + &1))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; GSYM REAL_OF_NUM_SUC]; ALL_TAC] THEN
  REWRITE_TAC[REALLIM_1_OVER_N_OFFSET]);;

(* Key fact: (n+1)*|sin(ty/sqrt(n+1)) - ty/sqrt(n+1)| --> 0
   for each fixed t and y. Uses SIN_APPROX_BOUND: |sin(z)-z| <= |z|^3/2,
   giving bound |ty|^3/(2*sqrt(n+1)) --> 0. *)
let SIN_SCALED_ERROR_VANISHES = prove
 (`!t y:real.
     ((\n. &(SUC n) *
           abs(sin(t * y / sqrt(&(SUC n))) -
               t * y / sqrt(&(SUC n))))
      ---> &0) sequentially`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. abs(t * y) pow 3 / (&2 * sqrt(&(SUC n)))` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
   X_GEN_TAC `n:num` THEN DISCH_TAC THEN
   SUBGOAL_THEN `&0 < &(SUC n)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 < sqrt(&(SUC n))` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `~(sqrt(&(SUC n)) = &0)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM; REAL_ABS_ABS] THEN
   ABBREV_TAC `u = t * y / sqrt(&(SUC n))` THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `&(SUC n) * (abs u pow 3 / &2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MP_TAC(SPEC `u:real` SIN_APPROX_BOUND) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   MATCH_MP_TAC(REAL_ARITH `a:real = b ==> a <= b`) THEN
   EXPAND_TAC "u" THEN REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_MUL] THEN
   SUBGOAL_THEN `abs(sqrt(&(SUC n))) = sqrt(&(SUC n))` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC SQRT_POS_LE THEN
    REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
   REWRITE_TAC[real_div; REAL_POW_MUL; REAL_POW_INV] THEN
   SUBGOAL_THEN `sqrt(&(SUC n)) pow 3 = &(SUC n) * sqrt(&(SUC n))`
     SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[ARITH_RULE `3 = SUC 2`] THEN REWRITE_TAC[real_pow] THEN
    SUBGOAL_THEN `sqrt(&(SUC n)) pow 2 = &(SUC n)` SUBST1_TAC THENL
    [MATCH_MP_TAC SQRT_POW_2 THEN REWRITE_TAC[REAL_POS]; REAL_ARITH_TAC];
    ALL_TAC] THEN
   REWRITE_TAC[REAL_INV_MUL] THEN CONV_TAC REAL_FIELD;
   ALL_TAC] THEN
  (* |ty|^3/(2*sqrt(n+1)) --> 0 *)
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REALLIM_NULL_LMUL THEN
  SUBGOAL_THEN `(\n. inv (&2 * sqrt(&(SUC n)))) =
    (\n. inv(&2) * inv(sqrt(&(SUC n))))` SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; REAL_INV_MUL]; ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_NULL_LMUL THEN
  REWRITE_TAC[REALLIM_INV_SQRT_SUC]);;

(* Helper: The Taylor remainder has expectation matching the char fn expression *)
let TAYLOR_REMAINDER_EXPECTATION = prove
 (`!p:A prob_space (X:A->real) s.
     integrable p X /\ integrable p (\x. X x pow 2)
     ==> expectation p (\x. cos(s * X x) - &1 + s pow 2 * X x pow 2 / &2) =
         gen_char_fn_re p X s - &1 +
         s pow 2 * expectation p (\x. X x pow 2) / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `random_variable (p:A prob_space) (X:A->real)` ASSUME_TAC THENL
  [ASM_MESON_TAC[integrable]; ALL_TAC] THEN
  REWRITE_TAC[gen_char_fn_re] THEN
  (* Rewrite as cos(s*X) - (1 - s^2/2*X^2) *)
  SUBGOAL_THEN
    `(\x:A. cos(s * (X:A->real) x) - &1 + s pow 2 * X x pow 2 / &2) =
     (\x. cos(s * X x) - (&1 - s pow 2 / &2 * X x pow 2))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. cos(s * (X:A->real) x))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_COS_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space)
    (\x:A. &1 - s pow 2 / &2 * (X:A->real) x pow 2)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_SUB THEN
   REWRITE_TAC[INTEGRABLE_CONST] THEN
   MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* E[f - g] = E[f] - E[g] *)
  MP_TAC(ISPECL [`p:A prob_space`;
    `\x:A. cos(s * (X:A->real) x)`;
    `\x:A. &1 - s pow 2 / &2 * (X:A->real) x pow 2`]
    EXPECTATION_SUB) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
  (* E[1 - s^2/2*X^2] = 1 - s^2/2*E[X^2] *)
  MP_TAC(ISPECL [`p:A prob_space`;
    `\x:A. &1:real`;
    `\x:A. s pow 2 / &2 * (X:A->real) x pow 2`]
    EXPECTATION_SUB) THEN
  REWRITE_TAC[INTEGRABLE_CONST] THEN
  ANTS_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[EXPECTATION_CONST] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `s pow 2 / &2`;
    `\x:A. (X:A->real) x pow 2`] EXPECTATION_CMUL) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REAL_ARITH_TAC);;

(* Helper: integrability of the Taylor remainder *)
let INTEGRABLE_TAYLOR_REMAINDER = prove
 (`!p:A prob_space (X:A->real) s.
     integrable p X /\ integrable p (\x. X x pow 2)
     ==> integrable p (\x. cos(s * X x) - &1 + s pow 2 * X x pow 2 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `random_variable (p:A prob_space) (X:A->real)` ASSUME_TAC THENL
  [ASM_MESON_TAC[integrable]; ALL_TAC] THEN
  SUBGOAL_THEN
    `(\x:A. cos(s * (X:A->real) x) - &1 + s pow 2 * X x pow 2 / &2) =
     (\x. cos(s * X x) - (&1 - s pow 2 / &2 * X x pow 2))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_COS_CMUL THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC INTEGRABLE_SUB THEN
   REWRITE_TAC[INTEGRABLE_CONST] THEN
   MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]]);;

(* GEN_CLT_RE_PERTURBATION_VANISHES:
   The Taylor remainder of the real part of the char fn, scaled by (n+1),
   converges to 0. This is the key DCT step.
   Uses: 0 <= cos(z)-1+z^2/2 <= z^4/6, with dominator t^2*X^2/2 *)
let GEN_CLT_RE_PERTURBATION_VANISHES = prove
 (`!p:A prob_space (X:A->real) t.
     integrable p X /\ integrable p (\x. X x pow 2)
     ==> ((\n. &(SUC n) *
               (gen_char_fn_re p X (t / sqrt(&(SUC n))) - &1 +
                t pow 2 * expectation p (\x. X x pow 2) / (&2 * &(SUC n))))
          ---> &0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `random_variable (p:A prob_space) (X:A->real)` ASSUME_TAC THENL
  [ASM_MESON_TAC[integrable]; ALL_TAC] THEN
  ABBREV_TAC `sigma2 = expectation (p:A prob_space) (\x:A. (X:A->real) x pow 2)` THEN
  (* Step 1: Rewrite LHS(n) as expectation of scaled Taylor remainder *)
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\n. expectation (p:A prob_space)
    (\x:A. &(SUC n) * (cos(t / sqrt(&(SUC n)) * (X:A->real) x) - &1 +
            (t / sqrt(&(SUC n))) pow 2 * X x pow 2 / &2))` THEN
  CONJ_TAC THENL
  [(* Show eventually equal *)
   REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
   X_GEN_TAC `n:num` THEN DISCH_TAC THEN BETA_TAC THEN
   SUBGOAL_THEN `integrable (p:A prob_space)
     (\x:A. cos(t / sqrt(&(SUC n)) * (X:A->real) x) - &1 +
             (t / sqrt(&(SUC n))) pow 2 * X x pow 2 / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_TAYLOR_REMAINDER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `&(SUC n)`;
     `\x:A. cos(t / sqrt(&(SUC n)) * (X:A->real) x) - &1 +
             (t / sqrt(&(SUC n))) pow 2 * X x pow 2 / &2`]
     EXPECTATION_CMUL) THEN
   ASM_REWRITE_TAC[] THEN BETA_TAC THEN
   DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
   AP_TERM_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `t / sqrt(&(SUC n))`]
     TAYLOR_REMAINDER_EXPECTATION) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   EXPAND_TAC "sigma2" THEN AP_TERM_TAC THEN
   SUBGOAL_THEN `(t / sqrt(&(SUC n))) pow 2 = t pow 2 / &(SUC n)`
     SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_DIV] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SQRT_POW_2 THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
   SUBGOAL_THEN `~(&(SUC n) = &0)` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ; NOT_SUC]; ALL_TAC] THEN
   CONV_TAC REAL_FIELD;
   (* Step 2: Apply Dominated Convergence Theorem *)
   ALL_TAC] THEN
  MATCH_MP_TAC DOMINATED_CONVERGENCE_NULL THEN
  EXISTS_TAC `\x:A. (t pow 2 / &2) * (X:A->real) x pow 2` THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  (* Precompute useful facts *)
  SUBGOAL_THEN `!n. &0 < &(SUC n)` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!n. ~(&(SUC n) = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!n. sqrt(&(SUC n)) pow 2 = &(SUC n)` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC SQRT_POW_2 THEN REWRITE_TAC[REAL_POS];
   ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
  [(* random_variable p (f n) for each n *)
   GEN_TAC THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. &(SUC n) *
     (cos(t / sqrt(&(SUC n)) * (X:A->real) x) - &1 +
      (t / sqrt(&(SUC n))) pow 2 * X x pow 2 / &2))`
     (fun th -> ASM_MESON_TAC[th; integrable]) THEN
   MATCH_MP_TAC INTEGRABLE_CMUL THEN
   MATCH_MP_TAC INTEGRABLE_TAYLOR_REMAINDER THEN ASM_REWRITE_TAC[];
   (* random_variable p h *)
   SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. t pow 2 / &2 * (X:A->real) x pow 2)`
     (fun th -> ASM_MESON_TAC[th; integrable]) THEN
   MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
   (* integrable p h *)
   MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
   (* Bounds: 0 <= f_n(x) <= h(x) *)
   REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [(* 0 <= (n+1) * (cos(s*Xx) - 1 + s^2*Xx^2/2) *)
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
    [REWRITE_TAC[REAL_POS];
     MP_TAC(SPEC `t / sqrt(&(SUC n)) * (X:A->real) x` COS_TAYLOR_NONNEG) THEN
     REWRITE_TAC[REAL_POW_MUL; real_div; GSYM REAL_MUL_ASSOC]];
    (* (n+1) * (cos(s*Xx)-1+s^2*Xx^2/2) <= (t^2/2)*Xx^2 *)
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(SUC n) *
      ((t / sqrt(&(SUC n))) pow 2 * (X:A->real) x pow 2 / &2)` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_POS];
      MP_TAC(SPEC `t / sqrt(&(SUC n)) * (X:A->real) x` COS_TAYLOR_UPPER) THEN
      REWRITE_TAC[REAL_POW_MUL; real_div; GSYM REAL_MUL_ASSOC]];
     (* (n+1) * s^2 * Xx^2 / 2 = (t^2/2) * Xx^2 *)
     SUBGOAL_THEN `&(SUC n) *
       ((t / sqrt(&(SUC n))) pow 2 * (X:A->real) x pow 2 / &2) =
       (t pow 2 / &2) * X x pow 2`
       (fun th -> REWRITE_TAC[th; REAL_LE_REFL]) THEN
     REWRITE_TAC[REAL_POW_DIV] THEN ASM_REWRITE_TAC[] THEN
     CONV_TAC REAL_FIELD]];
   (* Pointwise convergence: f_n(x) --> 0 *)
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
   EXISTS_TAC `\n. t pow 4 * (X:A->real) x pow 4 / (&6 * &(SUC n))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    (* |f_n(x)| = f_n(x) since f_n >= 0 *)
    SUBGOAL_THEN `abs(&(SUC n) * (cos(t / sqrt(&(SUC n)) * (X:A->real) x) -
      &1 + (t / sqrt(&(SUC n))) pow 2 * X x pow 2 / &2)) =
      &(SUC n) * (cos(t / sqrt(&(SUC n)) * X x) - &1 +
      (t / sqrt(&(SUC n))) pow 2 * X x pow 2 / &2)` SUBST1_TAC THENL
    [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN AP_TERM_TAC THEN
     REWRITE_TAC[REAL_ABS_REFL] THEN
     MP_TAC(SPEC `t / sqrt(&(SUC n)) * (X:A->real) x` COS_TAYLOR_NONNEG) THEN
     REWRITE_TAC[REAL_POW_MUL; real_div; GSYM REAL_MUL_ASSOC];
     ALL_TAC] THEN
    (* Bound: f_n(x) <= (n+1) * (s*Xx)^4/6 = t^4*Xx^4/(6*(n+1)) *)
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(SUC n) *
      ((t / sqrt(&(SUC n)) * (X:A->real) x) pow 4 / &6)` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_POS];
      MP_TAC(SPEC `t / sqrt(&(SUC n)) * (X:A->real) x` COS_TAYLOR_BOUND_4) THEN
      REWRITE_TAC[REAL_POW_MUL; real_div; GSYM REAL_MUL_ASSOC]];
     (* (n+1) * (s*Xx)^4/6 = t^4*Xx^4/(6*(n+1)) *)
     MATCH_MP_TAC(REAL_ARITH `a:real = b ==> a <= b`) THEN
     REWRITE_TAC[REAL_POW_MUL; REAL_POW_DIV] THEN ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN `sqrt(&(SUC n)) pow 4 = &(SUC n) pow 2` SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC SQRT_POW_2 THEN REWRITE_TAC[REAL_POS];
      ALL_TAC] THEN
     SUBGOAL_THEN `&(SUC n) pow 2 = &(SUC n) * &(SUC n)` SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `2 = SUC 1`; real_pow; REAL_POW_1];
      ALL_TAC] THEN
     SUBGOAL_THEN `~(&(SUC n) = &0)` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ; NOT_SUC]; ALL_TAC] THEN
     CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
   (* t^4*Xx^4/(6*(n+1)) --> 0 *)
   REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
   MATCH_MP_TAC REALLIM_NULL_LMUL THEN
   SUBGOAL_THEN `(\n. inv (&6 * &(SUC n))) =
     (\n. inv(&6) * inv(&(SUC n)))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; REAL_INV_MUL]; ALL_TAC] THEN
   MATCH_MP_TAC REALLIM_NULL_LMUL THEN
   REWRITE_TAC[REALLIM_1_OVER_SUC]]);;

(* GEN_CLT_IM_ERROR_VANISHES:
   (n+1) * |gen_char_fn_im(t/sqrt(n+1))| --> 0 when E[X] = 0.
   Uses: |sin(z)-z| <= z^2, so |E[sin(sX)]| = |E[sin(sX)-sX]| <= s^2*E[X^2]
   With DCT: (n+1)|gen_char_fn_im(t/sqrt(n+1))| <= t^2*E[X^2] and --> 0 *)
let GEN_CLT_IM_ERROR_VANISHES = prove
 (`!p:A prob_space (X:A->real) t.
     integrable p X /\ integrable p (\x. X x pow 2) /\
     expectation p X = &0
     ==> ((\n. &(SUC n) *
               abs(gen_char_fn_im p X (t / sqrt(&(SUC n)))))
          ---> &0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `random_variable (p:A prob_space) (X:A->real)` ASSUME_TAC THENL
  [ASM_MESON_TAC[integrable]; ALL_TAC] THEN
  (* Compare with E[(n+1)*|sin(sX)-sX|] via REALLIM_NULL_COMPARISON *)
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. expectation (p:A prob_space)
    (\x:A. &(SUC n) * abs(sin(t / sqrt(&(SUC n)) * (X:A->real) x) -
                          t / sqrt(&(SUC n)) * X x))` THEN
  CONJ_TAC THENL
  [(* Bound: |a_n| <= b_n *)
   REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
   X_GEN_TAC `n:num` THEN DISCH_TAC THEN BETA_TAC THEN
   ABBREV_TAC `s = t / sqrt(&(SUC n))` THEN
   REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM; REAL_ABS_ABS] THEN
   REWRITE_TAC[gen_char_fn_im] THEN
   (* E[sin(sX)] = E[sin(sX)-sX] since E[sX] = s*E[X] = 0 *)
   SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. sin(s * (X:A->real) x))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SIN_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. s * (X:A->real) x)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space)
     (\x:A. sin(s * (X:A->real) x) - s * X x)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. sin(s * (X:A->real) x)) =
     expectation p (\x. sin(s * X x) - s * X x)` SUBST1_TAC THENL
   [SUBGOAL_THEN `(\x:A. sin(s * (X:A->real) x)) =
      (\x. (sin(s * X x) - s * X x) + s * X x)` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`p:A prob_space`;
      `\x:A. sin(s * (X:A->real) x) - s * X x`;
      `\x:A. s * (X:A->real) x`]
      EXPECTATION_ADD) THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `s:real`; `X:A->real`]
      EXPECTATION_CMUL) THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID];
    ALL_TAC] THEN
   (* (n+1)*|E[sin(sX)-sX]| <= (n+1)*E[|sin(sX)-sX|] = E[(n+1)*|sin(sX)-sX|] *)
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `&(SUC n) * expectation (p:A prob_space)
     (\x:A. abs(sin(s * (X:A->real) x) - s * X x))` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL
    [REWRITE_TAC[REAL_POS];
     MP_TAC(ISPECL [`p:A prob_space`;
       `\x:A. sin(s * (X:A->real) x) - s * X x`]
       EXPECTATION_ABS_LE) THEN
     ASM_REWRITE_TAC[] THEN BETA_TAC];
    ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `&(SUC n)`;
     `\x:A. abs(sin(s * (X:A->real) x) - s * X x)`]
     EXPECTATION_CMUL) THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ABS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   BETA_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
   EXPAND_TAC "s" THEN REWRITE_TAC[REAL_LE_REFL];
   (* Show E[(n+1)*|sin(sX)-sX|] --> 0 via DCT *)
   ALL_TAC] THEN
  MATCH_MP_TAC DOMINATED_CONVERGENCE_NULL THEN
  EXISTS_TAC `\x:A. t pow 2 * (X:A->real) x pow 2` THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  SUBGOAL_THEN `!n. &0 < &(SUC n)` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!n. ~(&(SUC n) = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!n. sqrt(&(SUC n)) pow 2 = &(SUC n)` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC SQRT_POW_2 THEN REWRITE_TAC[REAL_POS];
   ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
  [(* random_variable p (f n) *)
   GEN_TAC THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. &(SUC n) *
     abs(sin(t / sqrt(&(SUC n)) * (X:A->real) x) -
         t / sqrt(&(SUC n)) * X x))`
     (fun th -> ASM_MESON_TAC[th; integrable]) THEN
   MATCH_MP_TAC INTEGRABLE_CMUL THEN
   MATCH_MP_TAC INTEGRABLE_ABS THEN
   MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SIN_CMUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]];
   (* random_variable p h *)
   SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. t pow 2 * (X:A->real) x pow 2)`
     (fun th -> ASM_MESON_TAC[th; integrable]) THEN
   MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
   (* integrable p h *)
   MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
   (* Bounds: 0 <= f_n(x) <= h(x) *)
   REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [(* 0 <= (n+1)*|sin(sX)-sX| *)
    MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_POS; REAL_ABS_POS];
    (* (n+1)*|sin(sX)-sX| <= t^2*X^2 *)
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(SUC n) *
      (t / sqrt(&(SUC n)) * (X:A->real) x) pow 2` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_LMUL THEN
     CONJ_TAC THENL
     [REWRITE_TAC[REAL_POS]; REWRITE_TAC[SIN_MINUS_X_SQ_BOUND]];
     (* (n+1)*(s*X)^2 = t^2*X^2 *)
     SUBGOAL_THEN `&(SUC n) *
       (t / sqrt(&(SUC n)) * (X:A->real) x) pow 2 =
       t pow 2 * X x pow 2`
       (fun th -> REWRITE_TAC[th; REAL_LE_REFL]) THEN
     REWRITE_TAC[REAL_POW_MUL; REAL_POW_DIV] THEN ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN `~(&(SUC n) = &0)` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ; NOT_SUC]; ALL_TAC] THEN
     CONV_TAC REAL_FIELD]];
   (* Pointwise convergence: f_n(x) --> 0 *)
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   SUBGOAL_THEN `!n. t / sqrt(&(SUC n)) * (X:A->real) x =
     t * X x / sqrt(&(SUC n))` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   ACCEPT_TAC(ISPECL [`t:real`; `(X:A->real) x`]
     SIN_SCALED_ERROR_VANISHES)]);;

(* GEN_CHAR_FN_RE_POW_CONV_EXP:
   gen_char_fn_re(X, t/sqrt(n+1))^(n+1) --> exp(-t^2*sigma^2/2)
   Proof: write gen_char_fn_re(s) = 1 - (c + h(n))/(n+1) where c = t^2*sigma^2/2
   and h(n) = -r(n) --> 0 by GEN_CLT_RE_PERTURBATION_VANISHES.
   Apply REALLIM_POW_EXP_NEG_PERTURB. *)
let GEN_CHAR_FN_RE_POW_CONV_EXP = prove
 (`!p:A prob_space (X:A->real) t.
     integrable p X /\ integrable p (\x. X x pow 2) /\
     &0 < expectation p (\x. X x pow 2)
     ==> ((\n. gen_char_fn_re p X (t / sqrt(&(SUC n))) pow (SUC n))
          ---> exp(--(t pow 2 * expectation p (\x. X x pow 2) / &2)))
         sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `random_variable (p:A prob_space) (X:A->real)` ASSUME_TAC THENL
  [ASM_MESON_TAC[integrable]; ALL_TAC] THEN
  ABBREV_TAC `sigma2 = expectation (p:A prob_space)
    (\x:A. (X:A->real) x pow 2)` THEN
  (* Case t = 0: trivial *)
  ASM_CASES_TAC `t = &0` THENL
  [ASM_SIMP_TAC[real_div; REAL_MUL_LZERO; GEN_CHAR_FN_RE_ZERO;
                REAL_POW_ONE; REAL_POW_2; REAL_MUL_RZERO;
                REAL_NEG_0; REAL_EXP_0; REALLIM_CONST];
   ALL_TAC] THEN
  (* t <> 0: use REALLIM_POW_EXP_NEG_PERTURB *)
  ABBREV_TAC `c = t pow 2 * sigma2 / &2` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
  [EXPAND_TAC "c" THEN MATCH_MP_TAC REAL_LT_MUL THEN
   CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_POW_2];
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* Define perturbation h(n) = (n+1)*(1 - gen_char_fn_re(s)) - c *)
  ABBREV_TAC `h = \n:num. &(SUC n) *
    (&1 - gen_char_fn_re (p:A prob_space) (X:A->real)
      (t / sqrt(&(SUC n)))) - c` THEN
  (* Transform: gen_char_fn_re^(n+1) = (1-(c+h(n))/(n+1))^(n+1) *)
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\n. (&1 - (c + (h:num->real) n) / &(SUC n)) pow (SUC n)` THEN
  CONJ_TAC THENL
  [(* Algebraic identity: gen_char_fn_re(s) = 1 - (c+h(n))/(n+1) *)
   MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN BETA_TAC THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN
   EXPAND_TAC "h" THEN BETA_TAC THEN
   SUBGOAL_THEN `~(&(SUC n) = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `~(&(SUC n) = &0)` THEN CONV_TAC REAL_FIELD;
   ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_POW_EXP_NEG_PERTURB THEN
  ASM_REWRITE_TAC[] THEN
  (* Show h --> 0 using GEN_CLT_RE_PERTURBATION_VANISHES *)
  (* h(n) = -(perturbation sequence) *)
  EXPAND_TAC "h" THEN EXPAND_TAC "c" THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\n. --(&(SUC n) *
    (gen_char_fn_re (p:A prob_space) (X:A->real)
      (t / sqrt(&(SUC n))) - &1 +
     t pow 2 * sigma2 / (&2 * &(SUC n))))` THEN
  CONJ_TAC THENL
  [(* Algebraic identity: (n+1)*(1-f(s)) - c = -(n+1)*(f(s)-1+c/(n+1)) *)
   MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN BETA_TAC THEN
   EXPAND_TAC "sigma2" THEN
   SUBGOAL_THEN `~(&(SUC n) = &0)` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ; NOT_SUC]; ALL_TAC] THEN
   CONV_TAC REAL_FIELD;
   ALL_TAC] THEN
  (* (\n. --P(n)) --> --(&0) = &0 since P --> &0 *)
  ONCE_REWRITE_TAC[GSYM REAL_NEG_0] THEN
  MATCH_MP_TAC REALLIM_NEG THEN
  EXPAND_TAC "sigma2" THEN
  MATCH_MP_TAC GEN_CLT_RE_PERTURBATION_VANISHES THEN
  ASM_REWRITE_TAC[]);;


(* GEN_CHAR_FN_SUM_IID_RE_BOUND:
   |gen_char_fn_re(sum, t) - gen_char_fn_re(X_0, t)^(n+1)|
   <= (n+1) * |gen_char_fn_im(X_0, t)|
   Inductive: same structure as CHAR_FN_SUM_IID_RE_BOUND but using
   GEN_CHAR_FN_ADD_INDEP_RE/IM. *)
let GEN_CHAR_FN_SUM_IID_RE_BOUND = prove
 (`!p:A prob_space (X:num->A->real) n t.
     (!i. random_variable p (X i)) /\
     (!i t. gen_char_fn_re p (X i) t = gen_char_fn_re p (X 0) t /\
            gen_char_fn_im p (X i) t = gen_char_fn_im p (X 0) t) /\
     (!k. k < n ==> indep_rv p (\x. sum(0..k) (\i. X i x)) (X (SUC k)))
     ==> abs(gen_char_fn_re p (\x. sum(0..n) (\i. X i x)) t -
             gen_char_fn_re p (X 0) t pow (SUC n))
         <= &(SUC n) * abs(gen_char_fn_im p (X 0) t)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [(* Base case: n = 0 *)
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `(\x:A. sum(0..0) (\i. (X:num->A->real) i x)) = X 0`
     (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; SUM_SING_NUMSEG] THEN GEN_TAC THEN BETA_TAC THEN
    REFL_TAC; ALL_TAC] THEN
   REWRITE_TAC[real_pow; REAL_MUL_RID; REAL_SUB_REFL; REAL_ABS_NUM] THEN
   MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_ABS_POS];
   (* Step case: n -> SUC n *)
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `(\x:A. sum(0..SUC n) (\i. (X:num->A->real) i x)) =
                 (\x. sum(0..n) (\i. X i x) + X (SUC n) x)`
     (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:A` THEN BETA_TAC THEN
    SIMP_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN BETA_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `random_variable (p:A prob_space)
     (\x:A. sum(0..n) (\i. (X:num->A->real) i x))` ASSUME_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN
    GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `indep_rv (p:A prob_space)
     (\x:A. sum(0..n) (\i. (X:num->A->real) i x)) (X (SUC n))`
     ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `\x:A. sum(0..n) (\i. (X:num->A->real) i x)`;
     `(X:num->A->real) (SUC n)`; `t:real`]
     GEN_CHAR_FN_ADD_INDEP_RE) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   BETA_TAC THEN DISCH_TAC THEN
   ONCE_ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN
     `gen_char_fn_re (p:A prob_space) ((X:num->A->real) (SUC n)) t =
      gen_char_fn_re p (X 0) t /\
      gen_char_fn_im p (X (SUC n)) t = gen_char_fn_im p (X 0) t`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
   ONCE_ASM_REWRITE_TAC[] THEN
   ONCE_REWRITE_TAC[real_pow] THEN
   MATCH_MP_TAC CHAR_FN_SUM_IID_TRIANGLE THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC GEN_CHAR_FN_RE_BOUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC GEN_CHAR_FN_IM_BOUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

(* GEN_CLT_CHAR_FN_CONVERGENCE:
   Main assembly: gen_char_fn_re of standardized sum --> exp(-t^2*sigma^2/2)
   Combines: GEN_CHAR_FN_RE_POW_CONV_EXP, GEN_CHAR_FN_SUM_IID_RE_BOUND,
   GEN_CLT_IM_ERROR_VANISHES via REALLIM_TRANSFORM + comparison *)
let GEN_CLT_CHAR_FN_CONVERGENCE = prove
 (`!p:A prob_space (X:num->A->real) t.
     (!n. integrable p (X n)) /\
     (!n. integrable p (\x. X n x pow 2)) /\
     (!i. expectation p (X i) = &0) /\
     &0 < expectation p (\x. X 0 x pow 2) /\
     (!i. expectation p (\x. X i x pow 2) = expectation p (\x. X 0 x pow 2)) /\
     (!i t. gen_char_fn_re p (X i) t = gen_char_fn_re p (X 0) t /\
            gen_char_fn_im p (X i) t = gen_char_fn_im p (X 0) t) /\
     (!n k. k < n ==> indep_rv p (\x. sum(0..k) (\i. X i x)) (X (SUC k)))
     ==> ((\n. gen_char_fn_re p (\x. sum(0..n) (\i. X i x))
                             (t / sqrt(&(SUC n))))
          ---> exp(--(t pow 2 * expectation p (\x. X 0 x pow 2) / &2)))
         sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Step 1: Show the difference from the power vanishes *)
  MATCH_MP_TAC REALLIM_TRANSFORM THEN
  EXISTS_TAC `\n. gen_char_fn_re (p:A prob_space) ((X:num->A->real) 0)
                    (t / sqrt(&(SUC n))) pow (SUC n)` THEN
  CONJ_TAC THENL
  [(* The difference vanishes *)
   MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
   EXISTS_TAC `\n. &(SUC n) * abs(gen_char_fn_im (p:A prob_space)
                   ((X:num->A->real) 0) (t / sqrt(&(SUC n))))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
    REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
    MATCH_MP_TAC GEN_CHAR_FN_SUM_IID_RE_BOUND THEN
    ASM_MESON_TAC[integrable];
    (* (n+1)*|gen_char_fn_im(X_0, t/sqrt(n+1))| --> 0 *)
    MATCH_MP_TAC GEN_CLT_IM_ERROR_VANISHES THEN
    ASM_REWRITE_TAC[]];
   (* Step 2: The power converges *)
   MATCH_MP_TAC GEN_CHAR_FN_RE_POW_CONV_EXP THEN
   ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Phase 22: Integrable Levy continuity chain for INTEGRABLE_CLT             *)
(* ========================================================================= *)

(* gen_cdf is in [0,1] for any random variable *)
let GEN_CDF_BOUNDS = prove
 (`!p:A prob_space (X:A->real) x.
     random_variable p X
     ==> &0 <= gen_cdf p X x /\ gen_cdf p X x <= &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gen_cdf] THENL
  [MATCH_MP_TAC PROB_POSITIVE THEN
   FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [random_variable]) THEN
   DISCH_THEN(MP_TAC o SPEC `x:real`) THEN REWRITE_TAC[];
   MATCH_MP_TAC PROB_LE_1 THEN
   FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [random_variable]) THEN
   DISCH_THEN(MP_TAC o SPEC `x:real`) THEN REWRITE_TAC[]]);;

(* gen_char_fn under division by constant *)
let GEN_CHAR_FN_RE_DIV = prove
 (`!p:A prob_space (X:A->real) c t.
     gen_char_fn_re p (\x. X x / c) t = gen_char_fn_re p X (t / c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gen_char_fn_re; real_div] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  GEN_TAC THEN AP_TERM_TAC THEN CONV_TAC REAL_RING);;

let GEN_CHAR_FN_IM_DIV = prove
 (`!p:A prob_space (X:A->real) c t.
     gen_char_fn_im p (\x. X x / c) t = gen_char_fn_im p X (t / c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gen_char_fn_im; real_div] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  GEN_TAC THEN AP_TERM_TAC THEN CONV_TAC REAL_RING);;

(* E[g(X)] <= gen_cdf(X,x) when g(y) <= 1 for y<=x, g(y) <= 0 for y>x *)
(* Needs: random_variable composition for measurable g - will prove when needed *)
let EXPECTATION_LE_GEN_CDF = prove
 (`!p:A prob_space (X:A->real) (g:real->real) x.
     random_variable p X /\
     integrable p (\a. g(X a)) /\
     (!y. y <= x ==> g y <= &1) /\
     (!y. y > x ==> g y <= &0)
     ==> expectation p (\a. g(X a)) <= gen_cdf p X x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{a | a IN prob_carrier (p:A prob_space) /\
    (X:A->real) a <= x} IN prob_events p` ASSUME_TAC THENL
  [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [random_variable]) THEN
   DISCH_THEN(MP_TAC o SPEC `x:real`) THEN REWRITE_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[gen_cdf] THEN
  ASM_SIMP_TAC[GSYM EXPECTATION_INDICATOR] THEN
  MATCH_MP_TAC EXPECTATION_MONO THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_SIMPLE THEN
   MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  X_GEN_TAC `a:A` THEN DISCH_TAC THEN
  REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(X:A->real) a <= x` THENL
  [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
   ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* gen_cdf(X,x) <= E[g(X)] when g(y) >= 1 for y<=x, g(y) >= 0 for y>x *)
(* Needs: integrability of g o X as hypothesis *)
let GEN_CDF_LE_EXPECTATION = prove
 (`!p:A prob_space (X:A->real) (g:real->real) x.
     random_variable p X /\
     integrable p (\a. g(X a)) /\
     (!y. y <= x ==> &1 <= g y) /\
     (!y. y > x ==> &0 <= g y)
     ==> gen_cdf p X x <= expectation p (\a. g(X a))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{a | a IN prob_carrier (p:A prob_space) /\
    (X:A->real) a <= x} IN prob_events p` ASSUME_TAC THENL
  [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [random_variable]) THEN
   DISCH_THEN(MP_TAC o SPEC `x:real`) THEN REWRITE_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[gen_cdf] THEN
  ASM_SIMP_TAC[GSYM EXPECTATION_INDICATOR] THEN
  MATCH_MP_TAC EXPECTATION_MONO THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_SIMPLE THEN
   MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  X_GEN_TAC `a:A` THEN DISCH_TAC THEN
  REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(X:A->real) a <= x` THENL
  [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
   ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* Modulus identity for gen_char_fn of IID sums: |cf(sum)|^2 = |cf(X_0)|^{2(n+1)}
   Generalized from CHAR_FN_SUM_IID_MODULUS to use random_variable *)
let GEN_CHAR_FN_SUM_IID_MODULUS_RV = prove
 (`!p:A prob_space (X:num->A->real) n t.
     (!i. random_variable p (X i)) /\
     (!i t. gen_char_fn_re p (X i) t = gen_char_fn_re p (X 0) t /\
            gen_char_fn_im p (X i) t = gen_char_fn_im p (X 0) t) /\
     (!k. k < n ==> indep_rv p (\x. sum(0..k) (\i. X i x)) (X (SUC k)))
     ==> gen_char_fn_re p (\x. sum(0..n) (\i. X i x)) t pow 2 +
         gen_char_fn_im p (\x. sum(0..n) (\i. X i x)) t pow 2 =
         (gen_char_fn_re p (X 0) t pow 2 +
          gen_char_fn_im p (X 0) t pow 2) pow (SUC n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [(* Base case: n = 0 *)
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `(\x:A. sum(0..0) (\i. (X:num->A->real) i x)) = X 0`
     (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; SUM_SING_NUMSEG] THEN GEN_TAC THEN BETA_TAC THEN
    REFL_TAC; ALL_TAC] THEN
   REWRITE_TAC[real_pow; REAL_MUL_RID];
   (* Inductive case *)
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `(\x:A. sum(0..SUC n) (\i. (X:num->A->real) i x)) =
                 (\x. sum(0..n) (\i. X i x) + X (SUC n) x)`
     (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:A` THEN BETA_TAC THEN
    SIMP_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN BETA_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `random_variable (p:A prob_space)
     (\x:A. sum(0..n) (\i. (X:num->A->real) i x))` ASSUME_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN
    GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `indep_rv (p:A prob_space)
     (\x:A. sum(0..n) (\i. (X:num->A->real) i x)) (X (SUC n))`
     ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
   (* Use addition formulas *)
   MP_TAC(ISPECL [`p:A prob_space`;
     `\x:A. sum(0..n) (\i. (X:num->A->real) i x)`;
     `(X:num->A->real) (SUC n)`; `t:real`]
     GEN_CHAR_FN_ADD_INDEP_RE) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   BETA_TAC THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `\x:A. sum(0..n) (\i. (X:num->A->real) i x)`;
     `(X:num->A->real) (SUC n)`; `t:real`]
     GEN_CHAR_FN_ADD_INDEP_IM) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   BETA_TAC THEN DISCH_TAC THEN
   ABBREV_TAC `R = gen_char_fn_re (p:A prob_space)
     (\x:A. sum(0..n) (\i. (X:num->A->real) i x)) t` THEN
   ABBREV_TAC `S' = gen_char_fn_im (p:A prob_space)
     (\x:A. sum(0..n) (\i. (X:num->A->real) i x)) t` THEN
   ABBREV_TAC `r = gen_char_fn_re (p:A prob_space) ((X:num->A->real) 0) t` THEN
   ABBREV_TAC `s = gen_char_fn_im (p:A prob_space) ((X:num->A->real) 0) t` THEN
   SUBGOAL_THEN `gen_char_fn_re (p:A prob_space) ((X:num->A->real) (SUC n)) t = r /\
                 gen_char_fn_im p (X (SUC n)) t = s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
   (* IH: R^2 + S'^2 = (r^2+s^2)^(n+1) *)
   SUBGOAL_THEN `(R:real) pow 2 + S' pow 2 =
     ((r:real) pow 2 + s pow 2) pow (SUC n)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL
    [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_MESON_TAC[];
      GEN_TAC THEN DISCH_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
     ASM_REWRITE_TAC[]]; ALL_TAC] THEN
   (* Now goal: f(sum+X(SUC n))^2 + g(sum+X(SUC n))^2 = (r^2+s^2)^(SUC(SUC n)) *)
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `((R:real) * r - S' * s) pow 2 + (R * s + S' * r) pow 2 =
     (R pow 2 + S' pow 2) * (r pow 2 + s pow 2)` SUBST1_TAC THENL
   [CONV_TAC REAL_RING; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
   REWRITE_TAC[GSYM(CONJUNCT2 real_pow)]]);;

(* Modulus bound: |phi(t)|^2 <= 1 for gen_char_fn with random_variable *)
(* Proof via Jensen: 1 - E[cos]^2 - E[sin]^2 = E[(cos-c)^2+(sin-s)^2] >= 0 *)
let GEN_CHAR_FN_MODULUS_LE = prove
 (`!p:A prob_space (X:A->real) t.
     random_variable p X
     ==> gen_char_fn_re p X t pow 2 + gen_char_fn_im p X t pow 2 <= &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gen_char_fn_re; gen_char_fn_im] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. cos(t * (X:A->real) x))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_COS_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. sin(t * (X:A->real) x))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_SIN_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `c = expectation (p:A prob_space) (\x:A. cos(t * (X:A->real) x))` THEN
  ABBREV_TAC `s = expectation (p:A prob_space) (\x:A. sin(t * (X:A->real) x))` THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= &1 - c pow 2 - s pow 2
    ==> c pow 2 + s pow 2 <= &1`) THEN
  (* 1 - c^2 - s^2 = E[(cos-c)^2 + (sin-s)^2] *)
  SUBGOAL_THEN `&1 - c pow 2 - s pow 2 =
    expectation (p:A prob_space)
      (\x:A. (cos(t * (X:A->real) x) - c) pow 2 + (sin(t * X x) - s) pow 2)`
    SUBST1_TAC THENL
  [SUBGOAL_THEN
     `(\x:A. (cos(t * (X:A->real) x) - c) pow 2 + (sin(t * X x) - s) pow 2) =
      (\x. (\x. (&1 + c pow 2 + s pow 2) + (-- &2 * c) * cos(t * X x)) x +
           (\x. (-- &2 * s) * sin(t * X x)) x)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `a:A` THEN BETA_TAC THEN
    MP_TAC(SPEC `t * (X:A->real) a` SIN_CIRCLE) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN
     `expectation (p:A prob_space)
       (\x:A. (\x. (&1 + c pow 2 + s pow 2) + (-- &2 * c) * cos(t * (X:A->real) x)) x +
              (\x. (-- &2 * s) * sin(t * X x)) x) =
      expectation p (\x. (&1 + c pow 2 + s pow 2) + (-- &2 * c) * cos(t * X x)) +
      expectation p (\x. (-- &2 * s) * sin(t * X x))`
     SUBST1_TAC THENL
   [MATCH_MP_TAC EXPECTATION_ADD THEN CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
     [REWRITE_TAC[INTEGRABLE_CONST];
      MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]];
     MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
   SUBGOAL_THEN
     `expectation (p:A prob_space)
       (\x:A. (&1 + c pow 2 + s pow 2) + (-- &2 * c) * cos(t * (X:A->real) x)) =
      (&1 + c pow 2 + s pow 2) + (-- &2 * c) * c` SUBST1_TAC THENL
   [SUBGOAL_THEN
      `(\x:A. (&1 + c pow 2 + s pow 2) + (-- &2 * c) * cos(t * (X:A->real) x)) =
       (\x. (\x. &1 + c pow 2 + s pow 2) x + (\x. (-- &2 * c) * cos(t * X x)) x)`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN BETA_TAC THEN REFL_TAC;
     ALL_TAC] THEN
    SUBGOAL_THEN
      `expectation (p:A prob_space)
        (\x:A. (\x. &1 + c pow 2 + s pow 2) x + (\x. (-- &2 * c) * cos(t * (X:A->real) x)) x) =
       expectation p (\x. &1 + c pow 2 + s pow 2) +
       expectation p (\x. (-- &2 * c) * cos(t * X x))`
      SUBST1_TAC THENL
    [MATCH_MP_TAC EXPECTATION_ADD THEN CONJ_TAC THENL
     [REWRITE_TAC[INTEGRABLE_CONST];
      MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
    REWRITE_TAC[EXPECTATION_CONST] THEN
    SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. (-- &2 * c) * cos(t * (X:A->real) x)) =
      (-- &2 * c) * expectation p (\x. cos(t * X x))` SUBST1_TAC THENL
    [MATCH_MP_TAC EXPECTATION_CMUL THEN ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[]]; ALL_TAC] THEN
   SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. (-- &2 * s) * sin(t * (X:A->real) x)) =
     (-- &2 * s) * s` SUBST1_TAC THENL
   [SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. (-- &2 * s) * sin(t * (X:A->real) x)) =
      (-- &2 * s) * expectation p (\x. sin(t * X x))` SUBST1_TAC THENL
    [MATCH_MP_TAC EXPECTATION_CMUL THEN ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[]];
    REAL_ARITH_TAC]; ALL_TAC] THEN
  (* E[(cos-c)^2 + (sin-s)^2] >= 0 *)
  MATCH_MP_TAC EXPECTATION_POS THEN CONJ_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `&8` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
     MATCH_MP_TAC RANDOM_VARIABLE_SUB_CONST THEN
     MATCH_MP_TAC RANDOM_VARIABLE_COS THEN
     MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
     MATCH_MP_TAC RANDOM_VARIABLE_SUB_CONST THEN
     MATCH_MP_TAC RANDOM_VARIABLE_SIN THEN
     MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `a:A` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &8 ==> abs x <= &8`) THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN REWRITE_TAC[REAL_LE_POW_2];
     ALL_TAC] THEN
    SUBGOAL_THEN `abs c <= &1 /\ abs s <= &1` STRIP_ASSUME_TAC THENL
    [CONJ_TAC THENL
     [EXPAND_TAC "c" THEN
      MP_TAC(ISPECL [`p:A prob_space`; `(\x:A. cos(t * (X:A->real) x))`; `&1`]
        EXPECTATION_BOUND) THEN BETA_TAC THEN ANTS_TAC THENL
      [CONJ_TAC THENL
       [MATCH_MP_TAC RANDOM_VARIABLE_COS THEN
        MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[];
        REPEAT STRIP_TAC THEN REWRITE_TAC[COS_BOUND]];
       SIMP_TAC[]];
      EXPAND_TAC "s" THEN
      MP_TAC(ISPECL [`p:A prob_space`; `(\x:A. sin(t * (X:A->real) x))`; `&1`]
        EXPECTATION_BOUND) THEN BETA_TAC THEN ANTS_TAC THENL
      [CONJ_TAC THENL
       [MATCH_MP_TAC RANDOM_VARIABLE_SIN THEN
        MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[];
        REPEAT STRIP_TAC THEN REWRITE_TAC[SIN_BOUND]];
       SIMP_TAC[]]]; ALL_TAC] THEN
    SUBGOAL_THEN `(cos(t * (X:A->real) a) - c) pow 2 <= &4` ASSUME_TAC THENL
    [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
     SUBGOAL_THEN `&4 = &2 pow 2` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
     MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
     MATCH_MP_TAC(REAL_ARITH `abs a <= &1 /\ abs b <= &1
       ==> abs(a - b) <= &2`) THEN
     ASM_REWRITE_TAC[COS_BOUND]; ALL_TAC] THEN
    SUBGOAL_THEN `(sin(t * (X:A->real) a) - s) pow 2 <= &4` ASSUME_TAC THENL
    [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
     SUBGOAL_THEN `&4 = &2 pow 2` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
     MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
     MATCH_MP_TAC(REAL_ARITH `abs a <= &1 /\ abs b <= &1
       ==> abs(a - b) <= &2`) THEN
     ASM_REWRITE_TAC[SIN_BOUND]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC];
   X_GEN_TAC `a:A` THEN DISCH_TAC THEN BETA_TAC THEN
   MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN REWRITE_TAC[REAL_LE_POW_2]]);;

(* Im(sum)^2 bound for gen_char_fn with random_variable *)
let GEN_CHAR_FN_SUM_IID_IM_SQ_BOUND = prove
 (`!p:A prob_space (X:num->A->real) n t.
     (!i. random_variable p (X i)) /\
     (!i t. gen_char_fn_re p (X i) t = gen_char_fn_re p (X 0) t /\
            gen_char_fn_im p (X i) t = gen_char_fn_im p (X 0) t) /\
     (!k. k < n ==> indep_rv p (\x. sum(0..k) (\i. X i x)) (X (SUC k)))
     ==> gen_char_fn_im p (\x. sum(0..n) (\i. X i x)) t pow 2
         <= &3 * (&(SUC n) * abs(gen_char_fn_im p (X 0) t))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `r = gen_char_fn_re (p:A prob_space) ((X:num->A->real) 0) t` THEN
  ABBREV_TAC `s = gen_char_fn_im (p:A prob_space) ((X:num->A->real) 0) t` THEN
  ABBREV_TAC `R = gen_char_fn_re (p:A prob_space)
    (\x:A. sum(0..n) (\i. (X:num->A->real) i x)) t` THEN
  ABBREV_TAC `S' = gen_char_fn_im (p:A prob_space)
    (\x:A. sum(0..n) (\i. (X:num->A->real) i x)) t` THEN
  (* Step 1: R^2+S'^2 = (r^2+s^2)^(n+1) *)
  MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`; `n:num`; `t:real`]
    GEN_CHAR_FN_SUM_IID_MODULUS_RV) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* Step 2: |R-r^(n+1)| <= (n+1)|s| *)
  MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`; `n:num`; `t:real`]
    GEN_CHAR_FN_SUM_IID_RE_BOUND) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* Step 3: r^2+s^2 <= 1 *)
  SUBGOAL_THEN `r pow 2 + s pow 2 <= &1` ASSUME_TAC THENL
  [EXPAND_TAC "r" THEN EXPAND_TAC "s" THEN
   MATCH_MP_TAC GEN_CHAR_FN_MODULUS_LE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 4: |s| <= 1 *)
  SUBGOAL_THEN `abs s <= &1` ASSUME_TAC THENL
  [ASM_MESON_TAC[GEN_CHAR_FN_IM_BOUND]; ALL_TAC] THEN
  (* Step 5: |r| <= 1 *)
  SUBGOAL_THEN `abs r <= &1` ASSUME_TAC THENL
  [ASM_MESON_TAC[GEN_CHAR_FN_RE_BOUND]; ALL_TAC] THEN
  (* Step 5b: |r^(n+1)| <= 1 *)
  SUBGOAL_THEN `abs(r pow (SUC n)) <= &1` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_ABS_POW] THEN MATCH_MP_TAC REAL_POW_1_LE THEN
   ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  (* Step 6: |R| <= 1 *)
  SUBGOAL_THEN `abs R <= &1` ASSUME_TAC THENL
  [EXPAND_TAC "R" THEN MATCH_MP_TAC GEN_CHAR_FN_RE_BOUND THEN
   MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN
   GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Step 7: (r^2+s^2)^(n+1) - (r^2)^(n+1) <= (n+1)*s^2 *)
  SUBGOAL_THEN `(r pow 2 + s pow 2) pow (SUC n) - (r pow 2) pow (SUC n)
                <= &(SUC n) * s pow 2` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_POW_DIFF_BOUND THEN
   ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  (* Step 8: s^2 <= |s| *)
  SUBGOAL_THEN `s pow 2 <= abs s` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_SQ_LE_ABS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Step 9: first part <= (n+1)*|s| *)
  SUBGOAL_THEN `(r pow 2 + s pow 2) pow (SUC n) - (r pow 2) pow (SUC n)
                <= &(SUC n) * abs s` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `&(SUC n) * s pow 2` THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  (* Step 10: |second part| <= 2*(n+1)*|s| *)
  SUBGOAL_THEN `abs((r pow (SUC n)) pow 2 - R pow 2)
                <= &2 * (&(SUC n) * abs s)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_DIFF_SQ_BOUND THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Final: apply S_SQ_DECOMP_BOUND *)
  MATCH_MP_TAC S_SQ_DECOMP_BOUND THEN
  MAP_EVERY EXISTS_TAC [`R:real`; `r:real`] THEN
  ASM_REWRITE_TAC[]);;

(* Helper: sqrt(f_n) --> 0 when f_n --> 0 *)
let REALLIM_SQRT_NULL = prove
 (`!f. (f ---> &0) sequentially
       ==> ((\n. sqrt(f n)) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 = sqrt(&0)` SUBST1_TAC THENL
  [REWRITE_TAC[SQRT_0]; ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_REAL_CONTINUOUS_FUNCTION THEN
  REWRITE_TAC[REAL_CONTINUOUS_AT_SQRT] THEN ASM_REWRITE_TAC[]);;

(* CLT: Imaginary part of gen_char_fn of standardized sum --> 0 *)
let GEN_CLT_CHAR_FN_IM_CONVERGENCE = prove
 (`!p:A prob_space (X:num->A->real) t.
     (!n. integrable p (X n)) /\
     (!n. integrable p (\x. X n x pow 2)) /\
     (!i. expectation p (X i) = &0) /\
     &0 < expectation p (\x. X 0 x pow 2) /\
     (!i. expectation p (\x. X i x pow 2) = expectation p (\x. X 0 x pow 2)) /\
     (!i t. gen_char_fn_re p (X i) t = gen_char_fn_re p (X 0) t /\
            gen_char_fn_im p (X i) t = gen_char_fn_im p (X 0) t) /\
     (!n k. k < n ==> indep_rv p (\x. sum(0..k) (\i. X i x)) (X (SUC k)))
     ==> ((\n. gen_char_fn_im p (\x. sum(0..n) (\i. X i x))
                             (t / sqrt(&(SUC n))))
          ---> &0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i:num. random_variable (p:A prob_space)
    ((X:num->A->real) i)` ASSUME_TAC THENL
  [ASM_MESON_TAC[integrable]; ALL_TAC] THEN
  ABBREV_TAC `I_n = \n:num. gen_char_fn_im (p:A prob_space)
    (\x:A. sum(0..n) (\i. (X:num->A->real) i x)) (t / sqrt(&(SUC n)))` THEN
  (* Use: Im^2 <= 3*(n+1)*|Im(X_0, s)| where s = t/sqrt(n+1) *)
  ABBREV_TAC `C_n = \n:num. &3 * (&(SUC n) *
    abs(gen_char_fn_im (p:A prob_space) ((X:num->A->real) 0)
      (t / sqrt(&(SUC n)))))` THEN
  (* Step 1: I_n^2 <= C_n *)
  SUBGOAL_THEN `!n:num. (I_n:num->real) n pow 2 <= C_n n` ASSUME_TAC THENL
  [X_GEN_TAC `n:num` THEN EXPAND_TAC "I_n" THEN EXPAND_TAC "C_n" THEN
   BETA_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`; `n:num`;
     `t / sqrt(&(SUC n))`] GEN_CHAR_FN_SUM_IID_IM_SQ_BOUND) THEN
   ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]]; ALL_TAC] THEN
  (* Step 2: C_n --> 0 since (n+1)*|Im(X_0, t/sqrt(n+1))| --> 0 *)
  SUBGOAL_THEN `((C_n:num->real) ---> &0) sequentially` ASSUME_TAC THENL
  [EXPAND_TAC "C_n" THEN BETA_TAC THEN
   SUBGOAL_THEN `&0 = &3 * &0` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REALLIM_LMUL THEN
   MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) 0`; `t:real`]
     GEN_CLT_IM_ERROR_VANISHES) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REALLIM_TRANSFORM_EVENTUALLY) THEN
   MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN BETA_TAC THEN
   REFL_TAC; ALL_TAC] THEN
  (* Step 3: C_n >= 0 *)
  SUBGOAL_THEN `!n:num. &0 <= (C_n:num->real) n` ASSUME_TAC THENL
  [X_GEN_TAC `n:num` THEN EXPAND_TAC "C_n" THEN BETA_TAC THEN
   MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_ABS_POS];
   ALL_TAC] THEN
  (* Step 4: |I_n| <= sqrt(C_n) and sqrt(C_n) --> 0 *)
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n:num. sqrt((C_n:num->real) n)` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
   X_GEN_TAC `n:num` THEN DISCH_TAC THEN BETA_TAC THEN
   (* |I_n n| = sqrt(I_n n ^2) <= sqrt(C_n n) *)
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `sqrt(((I_n:num->real) n pow 2))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC[POW_2_SQRT_ABS; REAL_LE_REFL];
    MATCH_MP_TAC SQRT_MONO_LE THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2]];
   MATCH_MP_TAC REALLIM_SQRT_NULL THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Phase 23: Integrable weak convergence from char fn                        *)
(* Generalizes WEAK_CONVERGENCE_FROM_CHAR_FN and supporting lemmas          *)
(* from simple_rv to integrable (random_variable) setting.                   *)
(* ========================================================================= *)

(* GEN_TRIG_POLY_WEAK_CONVERGENCE:
   If gen_char_fn_re/im of integrable X_n converge to normal limits,
   then expectation of trig polynomials converges.
   Analogous to TRIG_POLY_WEAK_CONVERGENCE for simple_rv. *)
let GEN_TRIG_POLY_WEAK_CONVERGENCE = prove
 (`!p:A prob_space (X:num->A->real) m (a:num->real) (b:num->real) (freq:num->real).
     (!n. random_variable p (X n)) /\
     (!t. ((\n. gen_char_fn_re p (X n) t) ---> exp(--(t pow 2 / &2)))
          sequentially) /\
     (!t. ((\n. gen_char_fn_im p (X n) t) ---> &0) sequentially)
     ==> ((\n. expectation p
                (\x. sum(0..m) (\k. a k * cos(freq k * X n x) +
                                     b k * sin(freq k * X n x)))) --->
          sum(0..m) (\k. a k * exp(--(freq k pow 2 / &2))))
         sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Step 1: Decompose expectation of trig poly into char fn terms *)
  SUBGOAL_THEN
    `!n:num. expectation (p:A prob_space)
       (\x:A. sum(0..m) (\k. (a:num->real) k * cos((freq:num->real) k * (X:num->A->real) n x) +
                               (b:num->real) k * sin(freq k * X n x))) =
     sum(0..m) (\k. a k * gen_char_fn_re p (X n) (freq k) +
                     b k * gen_char_fn_im p (X n) (freq k))`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   (* Each summand is integrable *)
   SUBGOAL_THEN `!i:num. i <= m ==>
     integrable (p:A prob_space)
       (\x:A. (a:num->real) i * cos((freq:num->real) i * (X:num->A->real) n x) +
              (b:num->real) i * sin(freq i * X n x))` ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_CMUL THEN
     MATCH_MP_TAC INTEGRABLE_COS_CMUL THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC INTEGRABLE_CMUL THEN
     MATCH_MP_TAC INTEGRABLE_SIN_CMUL THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   (* Decompose using EXPECTATION_SUM *)
   SUBGOAL_THEN
     `expectation (p:A prob_space)
       (\x:A. sum(0..m) (\k. (a:num->real) k * cos((freq:num->real) k * (X:num->A->real) n x) +
                               (b:num->real) k * sin(freq k * X n x))) =
      sum(0..m) (\k. expectation p
        (\x. a k * cos(freq k * X n x) + b k * sin(freq k * X n x)))`
     SUBST1_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`;
     `\k:num. \x:A. (a:num->real) k * cos((freq:num->real) k * (X:num->A->real) n x) +
              (b:num->real) k * sin(freq k * X n x)`;
     `m:num`] EXPECTATION_SUM) THEN
    ANTS_TAC THENL
    [GEN_TAC THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[]];
    ALL_TAC] THEN
   (* Each term decomposes into a*E[cos] + b*E[sin] *)
   MATCH_MP_TAC SUM_EQ_NUMSEG THEN
   X_GEN_TAC `k:num` THEN STRIP_TAC THEN BETA_TAC THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. cos((freq:num->real) k * (X:num->A->real) n x))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_COS_CMUL THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. sin((freq:num->real) k * (X:num->A->real) n x))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SIN_CMUL THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN
     `expectation (p:A prob_space) (\x:A. (a:num->real) k * cos((freq:num->real) k * (X:num->A->real) n x) +
       (b:num->real) k * sin(freq k * X n x)) =
      a k * expectation p (\x. cos(freq k * X n x)) +
      b k * expectation p (\x. sin(freq k * X n x))`
     SUBST1_TAC THENL
   [SUBGOAL_THEN
      `expectation (p:A prob_space) (\x:A. (a:num->real) k * cos((freq:num->real) k * (X:num->A->real) n x) +
        (b:num->real) k * sin(freq k * X n x)) =
       expectation p (\x. a k * cos(freq k * X n x)) +
       expectation p (\x. b k * sin(freq k * X n x))`
      SUBST1_TAC THENL
    [MATCH_MP_TAC EXPECTATION_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
    BINOP_TAC THENL
    [MATCH_MP_TAC EXPECTATION_CMUL THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC EXPECTATION_CMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   REWRITE_TAC[gen_char_fn_re; gen_char_fn_im];
   ALL_TAC] THEN
  (* Step 2: Apply limit decomposition *)
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\n:num. sum(0..m) (\k. (a:num->real) k * gen_char_fn_re (p:A prob_space) ((X:num->A->real) n) ((freq:num->real) k) +
                                       (b:num->real) k * gen_char_fn_im p (X n) (freq k))` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
   EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 3: Sum of convergent sequences converges *)
  MATCH_MP_TAC REALLIM_SUM THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_NUMSEG] THEN DISCH_TAC THEN
  BETA_TAC THEN
  SUBGOAL_THEN `(a:num->real) k * exp (--((freq:num->real) k pow 2 / &2)) =
    a k * exp (--(freq k pow 2 / &2)) + (b:num->real) k * &0` SUBST1_TAC THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
  [MATCH_MP_TAC REALLIM_LMUL THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC REALLIM_LMUL THEN ASM_REWRITE_TAC[]]);;

(* GEN_STEP_C_BOUND:
   For integrable X_n with bounded second moments, bound the difference
   |E[g(X_n)] - E[T(X_n)]| where g,T are bounded functions.
   Analogous to STEP_C_BOUND for simple_rv. *)
let GEN_STEP_C_BOUND = prove
 (`!p:A prob_space (X:num->A->real) (g:real->real) (T':real->real) BB CC e M.
     (!n. integrable p (\a. g(X n a))) /\
     (!n. integrable p (\a. T'(X n a))) /\
     (!n. integrable p (\x. X n x pow 2)) /\
     &0 < CC /\
     (!n. expectation p (\x. X n x pow 2) <= CC) /\
     (!y. abs(g y) <= BB) /\
     (!y. abs(T' y) <= BB) /\
     &0 < BB /\ &0 < e /\ &0 < M /\
     (!y. abs y <= M ==> abs(g y - T' y) < e / &6)
     ==> !n:num. abs(expectation p (\a. g(X n a)) -
              expectation p (\a. T'(X n a))) <=
         e / &6 + &2 * BB * CC / M pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `n:num` THEN
  (* g(X_n) and T(X_n) are integrable (from hypotheses) *)
  SUBGOAL_THEN `integrable (p:A prob_space) (\a:A. (g:real->real)((X:num->A->real) n a))`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\a:A. (T':real->real)((X:num->A->real) n a))`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* E[g(X_n)] - E[T(X_n)] = E[g(X_n) - T(X_n)] *)
  SUBGOAL_THEN
    `expectation (p:A prob_space) (\a:A. (g:real->real)((X:num->A->real) n a)) -
     expectation p (\a. (T':real->real)(X n a)) =
     expectation p (\a. g(X n a) - T'(X n a))`
    SUBST1_TAC THENL
  [SUBGOAL_THEN `integrable (p:A prob_space) (\a:A. (g:real->real)((X:num->A->real) n a) - (T':real->real)(X n a))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `&2 * BB` THEN CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN CONJ_TAC THENL
     [ASM_MESON_TAC[integrable];
      ASM_MESON_TAC[integrable]];
     X_GEN_TAC `a:A` THEN DISCH_TAC THEN BETA_TAC THEN
     MATCH_MP_TAC(REAL_ARITH
       `abs(g) <= BB /\ abs(t) <= BB ==> abs(g - t) <= &2 * BB`) THEN
     ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   CONV_TAC SYM_CONV THEN
   SUBGOAL_THEN `(\a:A. (g:real->real)((X:num->A->real) n a) - (T':real->real)(X n a)) =
     (\a. (\a. g(X n a)) a + (\a. --(T'(X n a))) a)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
     `expectation (p:A prob_space) (\a:A. (\a. (g:real->real)((X:num->A->real) n a)) a +
       (\a. --((T':real->real)(X n a))) a) =
      expectation p (\a. g(X n a)) + expectation p (\a. --(T'(X n a)))`
     SUBST1_TAC THENL
   [MATCH_MP_TAC EXPECTATION_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INTEGRABLE_NEG THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `expectation (p:A prob_space) (\a:A. --((T':real->real)((X:num->A->real) n a))) =
     --(expectation p (\a. T'(X n a)))` SUBST1_TAC THENL
   [MATCH_MP_TAC EXPECTATION_NEG_INTEGRABLE THEN ASM_REWRITE_TAC[];
    REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* |E[g-T]| <= E[|g-T|] *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `expectation (p:A prob_space)
    (\a:A. abs((g:real->real)((X:num->A->real) n a) - (T':real->real)(X n a)))` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC EXPECTATION_ABS_BOUND THEN
   MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `&2 * BB` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN CONJ_TAC THENL
    [ASM_MESON_TAC[integrable];
     ASM_MESON_TAC[integrable]];
    X_GEN_TAC `a:A` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
      `abs(g) <= BB /\ abs(t) <= BB ==> abs(g - t) <= &2 * BB`) THEN
    ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* E[|g-T|] <= E[e/6 + 2*BB*X^2/M^2] *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `expectation (p:A prob_space)
    (\a:A. e / &6 + &2 * BB * (X:num->A->real) n a pow 2 / M pow 2)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC EXPECTATION_MONO THEN
   REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `&2 * BB` THEN CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN
     CONJ_TAC THENL
     [ASM_MESON_TAC[integrable];
      ASM_MESON_TAC[integrable]];
     X_GEN_TAC `a:A` THEN DISCH_TAC THEN BETA_TAC THEN
     REWRITE_TAC[REAL_ABS_ABS] THEN
     MATCH_MP_TAC(REAL_ARITH
       `abs(g) <= BB /\ abs(t) <= BB ==> abs(g - t) <= &2 * BB`) THEN
     ASM_REWRITE_TAC[]];
    MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
    [REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC] THEN
    SUBGOAL_THEN `(\a:A. &2 * BB * (X:num->A->real) n a pow 2 / M pow 2) =
      (\a. (&2 * BB / M pow 2) * (\a. X n a pow 2) a)` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN CONV_TAC REAL_RING;
     MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `a:A` THEN DISCH_TAC THEN BETA_TAC THEN
    ASM_CASES_TAC `abs((X:num->A->real) n (a:A)) <= M` THENL
    [MATCH_MP_TAC(REAL_ARITH `x < ep /\ &0 <= r ==> x <= ep + r`) THEN
     CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
     MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
      [UNDISCH_TAC `&0 < BB` THEN REAL_ARITH_TAC;
       MATCH_MP_TAC REAL_LE_DIV THEN
       REWRITE_TAC[REAL_LE_POW_2] THEN
       MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_SIMP_TAC[REAL_POW_LT]]];
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `&2 * BB * (X:num->A->real) n (a:A) pow 2 / M pow 2` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * BB` THEN CONJ_TAC THENL
      [MATCH_MP_TAC(REAL_ARITH
         `abs x <= B /\ abs y <= B ==> abs(x - y) <= &2 * B`) THEN
       ASM_REWRITE_TAC[];
       MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC;
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
        [UNDISCH_TAC `&0 < BB` THEN REAL_ARITH_TAC;
         ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT] THEN
         REWRITE_TAC[REAL_MUL_LID; GSYM REAL_LE_SQUARE_ABS] THEN
         UNDISCH_TAC `~(abs((X:num->A->real) n (a:A)) <= M)` THEN
         UNDISCH_TAC `&0 < M` THEN REAL_ARITH_TAC]]];
      UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC]]];
   ALL_TAC] THEN
  (* E[e/6 + 2*BB*X^2/M^2] = e/6 + 2*BB*E[X^2]/M^2 <= e/6 + 2*BB*CC/M^2 *)
  SUBGOAL_THEN
    `expectation (p:A prob_space)
      (\a:A. e / &6 + &2 * BB * (X:num->A->real) n a pow 2 / M pow 2) =
     e / &6 + &2 * BB * expectation p (\a. X n a pow 2) / M pow 2`
    SUBST1_TAC THENL
  [SUBGOAL_THEN `(\a:A. e / &6 + &2 * BB * (X:num->A->real) n a pow 2 / M pow 2) =
    (\a. (\a. e / &6) a + (\a. (&2 * BB / M pow 2) * (\a. X n a pow 2) a) a)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   BETA_TAC THEN
   SUBGOAL_THEN
     `expectation (p:A prob_space) (\a:A. e / &6 + (&2 * BB / M pow 2) * (X:num->A->real) n a pow 2) =
      expectation p (\a. e / &6) + expectation p (\a. (&2 * BB / M pow 2) * X n a pow 2)`
     SUBST1_TAC THENL
   [MATCH_MP_TAC EXPECTATION_ADD THEN CONJ_TAC THENL
    [REWRITE_TAC[INTEGRABLE_CONST];
     MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   SUBGOAL_THEN `expectation (p:A prob_space) (\a:A. e / &6) = e / &6` SUBST1_TAC THENL
   [REWRITE_TAC[EXPECTATION_CONST]; ALL_TAC] THEN
   SUBGOAL_THEN `expectation (p:A prob_space) (\a:A. (&2 * BB / M pow 2) * (X:num->A->real) n a pow 2) =
     (&2 * BB / M pow 2) * expectation p (\a. X n a pow 2)` SUBST1_TAC THENL
   [MATCH_MP_TAC EXPECTATION_CMUL THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN CONV_TAC REAL_RING];
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
  [REAL_ARITH_TAC;
   MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [UNDISCH_TAC `&0 < BB` THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [UNDISCH_TAC `&0 < BB` THEN REAL_ARITH_TAC;
     SUBGOAL_THEN `&0 < M pow 2` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
     ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN ASM_REWRITE_TAC[]]]]);;

(* GEN_WEAK_CONVERGENCE_FROM_CHAR_FN:
   If gen_char_fn of integrable X_n converges to normal limits,
   then for any bounded continuous g,
   E[g(X_n)] -> integral(g * normal_density).
   Analogous to WEAK_CONVERGENCE_FROM_CHAR_FN for simple_rv. *)
let GEN_WEAK_CONVERGENCE_FROM_CHAR_FN = prove
 (`!p:A prob_space (X:num->A->real) (g:real->real).
     (!n. random_variable p (X n)) /\
     (!n. integrable p (X n)) /\
     (!n. integrable p (\x. X n x pow 2)) /\
     (?C. &0 < C /\ !n. expectation p (\x. X n x pow 2) <= C) /\
     (!t. ((\n. gen_char_fn_re p (X n) t) ---> exp(--(t pow 2 / &2)))
          sequentially) /\
     (!t. ((\n. gen_char_fn_im p (X n) t) ---> &0) sequentially) /\
     (!y. g real_continuous atreal y) /\
     (?B. &0 < B /\ !y. abs(g y) <= B) /\
     (!n. integrable p (\a. g(X n a)))
     ==> ((\n. expectation p (\a:A. g(X n a))) --->
          real_integral (:real) (\y. g y * std_normal_density y))
         sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `CC:real` STRIP_ASSUME_TAC) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `BB:real` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `M = sqrt(&12 * BB * (CC + &1) / e) + &1` THEN
  SUBGOAL_THEN `&0 < M` ASSUME_TAC THENL
  [EXPAND_TAC "M" THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
   MATCH_MP_TAC SQRT_POS_LE THEN
   MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
    [UNDISCH_TAC `&0 < BB` THEN REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
     [UNDISCH_TAC `&0 < CC` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC]]]; ALL_TAC] THEN
  (* Key bound: 2*BB*(CC+1)/M^2 < e/6 *)
  SUBGOAL_THEN `&2 * BB * (CC + &1) / M pow 2 < e / &6` ASSUME_TAC THENL
  [SUBGOAL_THEN `~(e = &0) /\ ~(BB = &0) /\ ~(CC + &1 = &0)` STRIP_ASSUME_TAC
   THENL
   [UNDISCH_TAC `&0 < e` THEN UNDISCH_TAC `&0 < BB` THEN
    UNDISCH_TAC `&0 < CC` THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 < &12 * BB * (CC + &1) / e` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
    [REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [UNDISCH_TAC `&0 < BB` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&0 < CC` THEN REAL_ARITH_TAC]]; ALL_TAC] THEN
   SUBGOAL_THEN `&12 * BB * (CC + &1) / e < M pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= &12 * BB * (CC + &1) / e` ASSUME_TAC THENL
    [UNDISCH_TAC `&0 < &12 * BB * (CC + &1) / e` THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
    SUBGOAL_THEN `sqrt(&12 * BB * (CC + &1) / e) pow 2 =
                   &12 * BB * (CC + &1) / e` (SUBST1_TAC o GSYM) THENL
    [ASM_SIMP_TAC[SQRT_POW2]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= sqrt(&12 * BB * (CC + &1) / e)` ASSUME_TAC THENL
    [MATCH_MP_TAC SQRT_POS_LE THEN
     UNDISCH_TAC `&0 < &12 * BB * (CC + &1) / e` THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `sqrt (&12 * BB * (CC + &1) / e) + &1 = M` THEN
    UNDISCH_TAC `&0 <= sqrt(&12 * BB * (CC + &1) / e)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
   REWRITE_TAC[real_div] THEN
   SUBGOAL_THEN
     `e * inv(&6) = &2 * BB * (CC + &1) * inv(&12 * BB * (CC + &1) * inv e)`
     SUBST1_TAC THENL
   [UNDISCH_TAC `~(e = &0)` THEN UNDISCH_TAC `~(BB = &0)` THEN
    UNDISCH_TAC `~(CC + &1 = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_LT_MUL;
                REAL_ARITH `&0 < CC ==> &0 < CC + &1`;
                REAL_OF_NUM_LT; ARITH] THEN
   MATCH_MP_TAC REAL_LT_INV2 THEN
   ASM_REWRITE_TAC[GSYM real_div];
   ALL_TAC] THEN
  (* Apply BOUNDED_CONTINUOUS_TRIG_APPROX *)
  MP_TAC(SPECL [`g:real->real`; `BB:real`; `M:real`; `e / &6`]
    BOUNDED_CONTINUOUS_TRIG_APPROX) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH];
   ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `nn:num`
    (X_CHOOSE_THEN `aa:num->real`
      (X_CHOOSE_THEN `bb:num->real`
        (X_CHOOSE_THEN `ff:num->real` STRIP_ASSUME_TAC)))) THEN
  (* Step A: E[T(X_n)] -> L *)
  ABBREV_TAC `L = sum(0..nn)
    (\k. (aa:num->real) k * exp(--((ff:num->real) k pow 2 / &2)))` THEN
  SUBGOAL_THEN
    `((\n. expectation (p:A prob_space)
       (\x:A. sum(0..nn)
         (\k. (aa:num->real) k * cos((ff:num->real) k * (X:num->A->real) n x) +
              (bb:num->real) k * sin(ff k * X n x)))) --->
      L) sequentially`
    ASSUME_TAC THENL
  [EXPAND_TAC "L" THEN
   MATCH_MP_TAC GEN_TRIG_POLY_WEAK_CONVERGENCE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step B: L = integral of T times density *)
  SUBGOAL_THEN
    `L = real_integral (:real)
      (\y. sum(0..nn)
        (\k. (aa:num->real) k * cos((ff:num->real) k * y) +
             (bb:num->real) k * sin(ff k * y)) *
        std_normal_density y)`
    ASSUME_TAC THENL
  [EXPAND_TAC "L" THEN CONV_TAC SYM_CONV THEN
   MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
   REWRITE_TAC[GAUSSIAN_INTEGRAL_TRIG_POLY]; ALL_TAC] THEN
  (* Steps C and D: error bounds *)
  SUBGOAL_THEN
    `!n:num. abs(expectation (p:A prob_space)
       (\a:A. (g:real->real)((X:num->A->real) n a)) -
      expectation p
       (\a:A. sum(0..nn)
         (\k. (aa:num->real) k * cos((ff:num->real) k * X n a) +
              (bb:num->real) k * sin(ff k * X n a)))) <=
      e / &6 + &2 * BB * CC / M pow 2`
    ASSUME_TAC THENL
  [SUBGOAL_THEN `!n:num. integrable (p:A prob_space)
     (\a:A. sum(0..nn)
       (\k. (aa:num->real) k * cos((ff:num->real) k * (X:num->A->real) n a) +
            (bb:num->real) k * sin(ff k * X n a)))` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_SUM THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_CMUL THEN
     MATCH_MP_TAC INTEGRABLE_COS_CMUL THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC INTEGRABLE_CMUL THEN
     MATCH_MP_TAC INTEGRABLE_SIN_CMUL THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   MP_TAC(ISPECL
     [`p:A prob_space`; `X:num->A->real`; `g:real->real`;
      `\y:real. sum(0..nn)
        (\k. (aa:num->real) k * cos((ff:num->real) k * y) +
             (bb:num->real) k * sin(ff k * y))`;
      `BB:real`; `CC:real`; `e:real`; `M:real`] GEN_STEP_C_BOUND) THEN
   BETA_TAC THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN ACCEPT_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `abs(L - real_integral (:real)
      (\y. (g:real->real) y * std_normal_density y)) <=
      e / &6 + &2 * BB / M pow 2`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL
     [`g:real->real`;
      `\y:real. sum(0..nn)
        (\k. (aa:num->real) k * cos((ff:num->real) k * y) +
             (bb:num->real) k * sin(ff k * y))`;
      `BB:real`; `e:real`; `M:real`; `L:real`] STEP_D_BOUND) THEN
   BETA_TAC THEN ANTS_TAC THENL
   [EXPAND_TAC "L" THEN ASM_REWRITE_TAC[GAUSSIAN_INTEGRAL_TRIG_POLY];
    DISCH_THEN ACCEPT_TAC];
   ALL_TAC] THEN
  (* Step E: From convergence of E[T(X_n)] to L, get N *)
  FIRST_X_ASSUM(MP_TAC o
    GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY] o
    check (fun th -> free_in `nn:num` (concl th))) THEN
  DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `N:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  (* Step F1: |E[g(X_n)] - E[T(X_n)]| < e/3 *)
  SUBGOAL_THEN `abs(expectation (p:A prob_space)
    (\a:A. (g:real->real)((X:num->A->real) n a)) -
    expectation p
    (\a:A. sum(0..nn)
      (\k. (aa:num->real) k * cos((ff:num->real) k * X n a) +
           (bb:num->real) k * sin(ff k * X n a)))) < e / &3`
    ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `e / &6 + &2 * BB * CC / M pow 2` THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC(REAL_ARITH `x < e / &6 ==> e / &6 + x < e / &3`) THEN
   MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `&2 * BB * (CC + &1) / M pow 2` THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [UNDISCH_TAC `&0 < BB` THEN REAL_ARITH_TAC;
     ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_POW_LT] THEN
     REAL_ARITH_TAC]];
   ALL_TAC] THEN
  (* Step F2: |E[T(X_n)] - L| < e/3 *)
  SUBGOAL_THEN `abs(expectation (p:A prob_space)
    (\a:A. sum(0..nn)
      (\k. (aa:num->real) k * cos((ff:num->real) k * (X:num->A->real) n a) +
           (bb:num->real) k * sin(ff k * X n a))) -
    L) < e / &3`
    ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
   ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step F3: |L - int(g*density)| < e/3 *)
  SUBGOAL_THEN `abs(L - real_integral (:real)
    (\y. (g:real->real) y * std_normal_density y)) < e / &3`
    ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `e / &6 + &2 * BB / M pow 2` THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC(REAL_ARITH `x < e / &6 ==> e / &6 + x < e / &3`) THEN
   MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `&2 * BB * (CC + &1) / M pow 2` THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[real_div] THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [UNDISCH_TAC `&0 < BB` THEN REAL_ARITH_TAC;
     GEN_REWRITE_TAC (LAND_CONV) [GSYM REAL_MUL_LID] THEN
     MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [UNDISCH_TAC `&0 < CC` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN
      ASM_SIMP_TAC[REAL_POW_LT]]]];
   ALL_TAC] THEN
  ABBREV_TAC `eg = expectation (p:A prob_space)
    (\a:A. (g:real->real)((X:num->A->real) n a))` THEN
  ABBREV_TAC `et = expectation (p:A prob_space)
    (\a:A. sum(0..nn)
      (\k. (aa:num->real) k * cos((ff:num->real) k * (X:num->A->real) n a) +
           (bb:num->real) k * sin(ff k * X n a)))` THEN
  ABBREV_TAC `ig = real_integral (:real)
    (\y. (g:real->real) y * std_normal_density y)` THEN
  ASM_REAL_ARITH_TAC);;

(* GEN_CHAR_FN_DETERMINES_NORMAL_CDF_LIMIT:
   If gen_char_fn converges to normal and gen_cdf converges to l,
   then l = std_normal_cdf x. Uses sandwich argument with
   piecewise linear test functions and GEN_WEAK_CONVERGENCE_FROM_CHAR_FN. *)
let GEN_CHAR_FN_DETERMINES_NORMAL_CDF_LIMIT = prove
 (`!p:A prob_space (X:num->A->real) x l.
     (!n. random_variable p (X n)) /\
     (!n. integrable p (X n)) /\
     (!n. integrable p (\x. X n x pow 2)) /\
     (?C. &0 < C /\ !n. expectation p (\x. X n x pow 2) <= C) /\
     (!t. ((\n. gen_char_fn_re p (X n) t) ---> exp(--(t pow 2 / &2)))
          sequentially) /\
     (!t. ((\n. gen_char_fn_im p (X n) t) ---> &0) sequentially) /\
     ((\n. gen_cdf p (X n) x) ---> l) sequentially
     ==> l = std_normal_cdf x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_LIMIT_SANDWICH THEN
  REWRITE_TAC[STD_NORMAL_CDF_CONTINUOUS] THEN
  X_GEN_TAC `h:real` THEN DISCH_TAC THEN
  CONJ_TAC THENL
  [(* ---- Lower bound: std_normal_cdf(x - h) <= l ---- *)
   ABBREV_TAC
     `g_low = \y:real. max (&0) (min (&1) (&1 - (y - (x - h)) / h))` THEN
   (* Establish integrability of g_low(X n) *)
   SUBGOAL_THEN `!n:num. integrable (p:A prob_space)
     (\a:A. (g_low:real->real) ((X:num->A->real) n a))` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
    EXISTS_TAC `&1` THEN CONJ_TAC THENL
    [(* random_variable via closure properties *)
     EXPAND_TAC "g_low" THEN
     MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN
     REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN
     MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
     REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN
     MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN
     REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN
     REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
     MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN
     MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN
     REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST];
     (* bounded by 1 *)
     X_GEN_TAC `a:A` THEN DISCH_TAC THEN BETA_TAC THEN
     EXPAND_TAC "g_low" THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC
     `real_integral (:real)
        (\y:real. g_low y * std_normal_density y)` THEN
   CONJ_TAC THENL
   [(* Phi(x-h) <= int g_low*density *)
    MATCH_MP_TAC CDF_LE_INTEGRAL_BOUNDED THEN
    EXPAND_TAC "g_low" THEN CONJ_TAC THENL
    [GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
    [X_GEN_TAC `y:real` THEN DISCH_TAC THEN
     SUBGOAL_THEN `&1 <= &1 - (y - (x - h)) / h` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_ARITH `&1 <= &1 - z <=> z <= &0`;
                    REAL_LE_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
     GEN_TAC THEN
     MATCH_MP_TAC REAL_CONTINUOUS_MAX THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_CONTINUOUS_CONST];
      MATCH_MP_TAC REAL_CONTINUOUS_MIN THEN CONJ_TAC THENL
      [REWRITE_TAC[REAL_CONTINUOUS_CONST];
       MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_CONTINUOUS_CONST];
        MATCH_MP_TAC REAL_CONTINUOUS_DIV_ATREAL THEN CONJ_TAC THENL
        [MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN
         REWRITE_TAC[REAL_CONTINUOUS_AT_ID; REAL_CONTINUOUS_CONST];
         CONJ_TAC THENL
         [REWRITE_TAC[REAL_CONTINUOUS_CONST];
          ASM_REAL_ARITH_TAC]]]]]];
    ALL_TAC] THEN
   (* int g_low*density <= l: by limit comparison *)
   MP_TAC(ISPECL
     [`sequentially`;
      `\n:num. expectation (p:A prob_space)
        (\a:A. (g_low:real->real) ((X:num->A->real) n a))`;
      `\n:num. gen_cdf (p:A prob_space) ((X:num->A->real) n) x`;
      `real_integral (:real)
        (\y:real. (g_low:real->real) y * std_normal_density y)`;
      `l:real`]
     REALLIM_LE) THEN
   BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    CONJ_TAC THENL
    [(* E[g_low(X_n)] -> integral(g_low * density) *)
     MATCH_MP_TAC GEN_WEAK_CONVERGENCE_FROM_CHAR_FN THEN
     ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     CONJ_TAC THENL
     [(* g_low is continuous *)
      EXPAND_TAC "g_low" THEN GEN_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_MAX THEN CONJ_TAC THENL
      [REWRITE_TAC[REAL_CONTINUOUS_CONST];
       MATCH_MP_TAC REAL_CONTINUOUS_MIN THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_CONTINUOUS_CONST];
        MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN CONJ_TAC THENL
        [REWRITE_TAC[REAL_CONTINUOUS_CONST];
         MATCH_MP_TAC REAL_CONTINUOUS_DIV_ATREAL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN
          REWRITE_TAC[REAL_CONTINUOUS_AT_ID; REAL_CONTINUOUS_CONST];
          CONJ_TAC THENL
          [REWRITE_TAC[REAL_CONTINUOUS_CONST];
           ASM_REAL_ARITH_TAC]]]]];
      (* g_low is bounded *)
      EXISTS_TAC `&1` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      EXPAND_TAC "g_low" THEN GEN_TAC THEN REAL_ARITH_TAC];
     ALL_TAC] THEN
    (* eventually(E[g_low(X_n)] <= gen_cdf(X_n, x)) *)
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC EXPECTATION_LE_GEN_CDF THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
    [X_GEN_TAC `y:real` THEN EXPAND_TAC "g_low" THEN REAL_ARITH_TAC;
     X_GEN_TAC `y:real` THEN DISCH_TAC THEN EXPAND_TAC "g_low" THEN
     SUBGOAL_THEN `&1 - (y - (x - h)) / h <= &0` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_ARITH `&1 - z <= &0 <=> &1 <= z`;
                    REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]];
    SIMP_TAC[]];
   ALL_TAC] THEN
  (* ---- Upper bound: l <= std_normal_cdf(x + h) ---- *)
  ABBREV_TAC
    `g_high = \y:real. max (&0) (min (&1) (&1 - (y - x) / h))` THEN
  (* Establish integrability of g_high(X n) *)
  SUBGOAL_THEN `!n:num. integrable (p:A prob_space)
    (\a:A. (g_high:real->real) ((X:num->A->real) n a))` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
   EXISTS_TAC `&1` THEN CONJ_TAC THENL
   [(* random_variable via closure properties *)
    EXPAND_TAC "g_high" THEN
    MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN
    REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN
    MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
    REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN
    MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN
    REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN
    REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN
    MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN
    REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST];
    (* bounded by 1 *)
    X_GEN_TAC `a:A` THEN DISCH_TAC THEN BETA_TAC THEN
    EXPAND_TAC "g_high" THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `real_integral (:real)
       (\y:real. g_high y * std_normal_density y)` THEN
  CONJ_TAC THENL
  [ALL_TAC;
   (* int g_high*density <= Phi(x+h) *)
   MATCH_MP_TAC INTEGRAL_BOUNDED_LE_CDF THEN
   CONJ_TAC THENL [EXPAND_TAC "g_high" THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
   CONJ_TAC THENL
   [X_GEN_TAC `y:real` THEN DISCH_TAC THEN EXPAND_TAC "g_high" THEN
    SUBGOAL_THEN `&1 - (y - x) / h <= &0` MP_TAC THENL
    [ASM_SIMP_TAC[REAL_ARITH `&1 - z <= &0 <=> &1 <= z`;
                   REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
     REAL_ARITH_TAC];
    EXPAND_TAC "g_high" THEN GEN_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_MAX THEN CONJ_TAC THENL
    [REWRITE_TAC[REAL_CONTINUOUS_CONST];
     MATCH_MP_TAC REAL_CONTINUOUS_MIN THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_CONTINUOUS_CONST];
      MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN CONJ_TAC THENL
      [REWRITE_TAC[REAL_CONTINUOUS_CONST];
       MATCH_MP_TAC REAL_CONTINUOUS_DIV_ATREAL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN
        REWRITE_TAC[REAL_CONTINUOUS_AT_ID; REAL_CONTINUOUS_CONST];
        CONJ_TAC THENL
        [REWRITE_TAC[REAL_CONTINUOUS_CONST];
         ASM_REAL_ARITH_TAC]]]]]]] THEN
  (* l <= int g_high*density *)
  MP_TAC(ISPECL
    [`sequentially`;
     `\n:num. gen_cdf (p:A prob_space) ((X:num->A->real) n) x`;
     `\n:num. expectation (p:A prob_space)
       (\a:A. (g_high:real->real) ((X:num->A->real) n a))`;
     `l:real`;
     `real_integral (:real)
       (\y:real. (g_high:real->real) y * std_normal_density y)`]
    REALLIM_LE) THEN
  BETA_TAC THEN ANTS_TAC THENL
  [ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
   CONJ_TAC THENL
   [(* E[g_high(X_n)] -> integral(g_high * density) *)
    MATCH_MP_TAC GEN_WEAK_CONVERGENCE_FROM_CHAR_FN THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
    [(* g_high is continuous *)
     EXPAND_TAC "g_high" THEN GEN_TAC THEN
     MATCH_MP_TAC REAL_CONTINUOUS_MAX THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_CONTINUOUS_CONST];
      MATCH_MP_TAC REAL_CONTINUOUS_MIN THEN CONJ_TAC THENL
      [REWRITE_TAC[REAL_CONTINUOUS_CONST];
       MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_CONTINUOUS_CONST];
        MATCH_MP_TAC REAL_CONTINUOUS_DIV_ATREAL THEN CONJ_TAC THENL
        [MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN
         REWRITE_TAC[REAL_CONTINUOUS_AT_ID; REAL_CONTINUOUS_CONST];
         CONJ_TAC THENL
         [REWRITE_TAC[REAL_CONTINUOUS_CONST];
          ASM_REAL_ARITH_TAC]]]]];
     (* g_high is bounded *)
     EXISTS_TAC `&1` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
     EXPAND_TAC "g_high" THEN GEN_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
   (* eventually(gen_cdf(X_n,x) <= E[g_high(X_n)]) *)
   REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
   X_GEN_TAC `n:num` THEN DISCH_TAC THEN BETA_TAC THEN
   MATCH_MP_TAC GEN_CDF_LE_EXPECTATION THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL
   [X_GEN_TAC `y:real` THEN DISCH_TAC THEN EXPAND_TAC "g_high" THEN
    SUBGOAL_THEN `(y - x) / h <= &0` MP_TAC THENL
    [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
     REAL_ARITH_TAC];
    X_GEN_TAC `y:real` THEN DISCH_TAC THEN EXPAND_TAC "g_high" THEN
    REAL_ARITH_TAC];
   SIMP_TAC[]]);;

(* Levy continuity theorem for integrable RVs (CLT version) *)
(* This is the key bridge from char fn convergence to CDF convergence.
   The proof follows the same structure as SIMPLE_LEVY_CONTINUITY_CLT but uses
   general (integrable) versions of expectations and char fns. *)
let LEVY_CONTINUITY_CLT = prove
 (`!p:A prob_space (X:num->A->real).
    (!n. random_variable p (X n)) /\
    (?C. &0 < C /\
         !n. expectation p (\x. (X:num->A->real) n x pow 2) <= C) /\
    (!n. integrable p (X n)) /\
    (!n. integrable p (\x. X n x pow 2)) /\
    (!t. ((\n. gen_char_fn_re p (X n) t) ---> exp(--(t pow 2 / &2)))
         sequentially) /\
    (!t. ((\n. gen_char_fn_im p (X n) t) ---> &0) sequentially)
    ==> !x. ((\n. gen_cdf p (X n) x) ---> std_normal_cdf x) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real` THEN
  REWRITE_TAC[GEN_CDF_SIMPLE_AGREE] THEN
  (* Step 1: Tightness from bounded second moments *)
  SUBGOAL_THEN
    `!e. &0 < e ==>
     ?M. &0 < M /\
     ?N:num. !n. N <= n ==>
       prob (p:A prob_space) {a | a IN prob_carrier p /\
                                   abs((X:num->A->real) n a) >= M} < e`
    ASSUME_TAC THENL
  [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`; `C:real`]
     TIGHTNESS_FROM_SECOND_MOMENTS) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
   STRIP_TAC THEN EXISTS_TAC `M:real` THEN ASM_REWRITE_TAC[] THEN
   EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 2: Use subsequence convergence principle *)
  MATCH_MP_TAC(ISPECL
    [`\n:num. simple_cdf (p:A prob_space) ((X:num->A->real) n) x`;
     `std_normal_cdf x`; `&1`] REALLIM_SUBSEQ_SAME_LIMIT) THEN
  BETA_TAC THEN CONJ_TAC THENL
  [GEN_TAC THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a <= &1 ==> abs a <= &1`) THEN
   REWRITE_TAC[GSYM GEN_CDF_SIMPLE_AGREE] THEN
   MATCH_MP_TAC GEN_CDF_BOUNDS THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  X_GEN_TAC `r:num->num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL
    [`\k:num. simple_cdf (p:A prob_space) ((X:num->A->real) ((r:num->num) k)) x`;
     `&1`] BOUNDED_REAL_SEQ_HAS_CONVERGENT_SUBSEQ) THEN
  BETA_TAC THEN ANTS_TAC THENL
  [GEN_TAC THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a <= &1 ==> abs a <= &1`) THEN
   REWRITE_TAC[GSYM GEN_CDF_SIMPLE_AGREE] THEN
   MATCH_MP_TAC GEN_CDF_BOUNDS THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real`
    (X_CHOOSE_THEN `s:num->num` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `s:num->num` THEN ASM_REWRITE_TAC[] THEN
  (* The limit must be std_normal_cdf x *)
  SUBGOAL_THEN `l:real = std_normal_cdf x` SUBST_ALL_TAC THENL
  [MP_TAC(ISPECL
     [`p:A prob_space`;
      `\k:num. (X:num->A->real) ((r:num->num) ((s:num->num) k))`;
      `x:real`; `l:real`]
     GEN_CHAR_FN_DETERMINES_NORMAL_CDF_LIMIT) THEN
   BETA_TAC THEN ANTS_TAC THENL
   [CONJ_TAC THENL
    [GEN_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
    [GEN_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
    [GEN_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
    [EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
    [(* gen_char_fn_re convergence along r o s *)
     X_GEN_TAC `t:real` THEN
     MP_TAC(ISPECL
       [`\n:num. gen_char_fn_re (p:A prob_space) ((X:num->A->real) n) t`;
        `exp(--(t pow 2 / &2))`;
        `\k:num. (r:num->num) ((s:num->num) k)`]
       REALLIM_SUBSEQUENCE) THEN
     BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
     ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN
     FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    CONJ_TAC THENL
    [(* gen_char_fn_im convergence along r o s *)
     X_GEN_TAC `t:real` THEN
     MP_TAC(ISPECL
       [`\n:num. gen_char_fn_im (p:A prob_space) ((X:num->A->real) n) t`;
        `&0`;
        `\k:num. (r:num->num) ((s:num->num) k)`]
       REALLIM_SUBSEQUENCE) THEN
     BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
     ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN
     FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    ASM_REWRITE_TAC[GEN_CDF_SIMPLE_AGREE];
    DISCH_TAC THEN ASM_REWRITE_TAC[]];
   ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* INTEGRABLE_CLT: The Central Limit Theorem for integrable random vars      *)
(* ========================================================================= *)

let INTEGRABLE_CLT = prove
 (`!p:A prob_space (X:num->A->real).
    (!n. integrable p (X n)) /\
    (!n. integrable p (\x. X n x pow 2)) /\
    (!i. expectation p (X i) = &0) /\
    &0 < variance p (X 0) /\
    (!i. variance p (X i) = variance p (X 0)) /\
    (!i j:num. ~(i = j) ==> indep_rv p (X i) (X j)) /\
    (!i t. gen_char_fn_re p (X i) t = gen_char_fn_re p (X 0) t /\
           gen_char_fn_im p (X i) t = gen_char_fn_im p (X 0) t) /\
    (!n k. k < n ==> indep_rv p (\x. sum(0..k) (\i. X i x)) (X (SUC k)))
    ==> !x:real. ((\n. gen_cdf p
                (\a. sum(0..n) (\i. X i a) /
                     (sqrt(variance p (X 0)) * sqrt(&(SUC n)))) x)
             ---> std_normal_cdf x) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `sigma2 = variance (p:A prob_space) ((X:num->A->real) 0)` THEN
  SUBGOAL_THEN `&0 < sigma2` ASSUME_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!i:num. random_variable (p:A prob_space)
    ((X:num->A->real) i)` ASSUME_TAC THENL
  [ASM_MESON_TAC[integrable]; ALL_TAC] THEN
  (* Define standardized sums Y_n *)
  ABBREV_TAC `Y = \n:num. \a:A. sum(0..n) (\i. (X:num->A->real) i a) /
    (sqrt sigma2 * sqrt(&(SUC n)))` THEN
  SUBGOAL_THEN `!n:num. random_variable (p:A prob_space)
    ((Y:num->A->real) n)` ASSUME_TAC THENL
  [X_GEN_TAC `n:num` THEN EXPAND_TAC "Y" THEN BETA_TAC THEN
   SUBGOAL_THEN `(\a:A. sum(0..n) (\i. (X:num->A->real) i a) /
     (sqrt sigma2 * sqrt(&(SUC n)))) =
     (\a. inv(sqrt sigma2 * sqrt(&(SUC n))) *
       sum(0..n) (\i. X i a))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; real_div] THEN GEN_TAC THEN REAL_ARITH_TAC;
    MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN
    MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN
    GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* Apply LEVY_CONTINUITY_CLT to Y_n *)
  SUBGOAL_THEN `!n x:real. gen_cdf (p:A prob_space) ((Y:num->A->real) n) x =
    gen_cdf p (\a. sum(0..n) (\i. (X:num->A->real) i a) /
      (sqrt sigma2 * sqrt(&(SUC n)))) x` ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   EXPAND_TAC "Y" THEN REFL_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!x:real. ((\n. gen_cdf (p:A prob_space) ((Y:num->A->real) n) x) --->
               std_normal_cdf x) sequentially`
    MP_TAC THENL
  [ALL_TAC;
   DISCH_TAC THEN X_GEN_TAC `xx:real` THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `xx:real`) THEN
   MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REALLIM_TRANSFORM_EVENTUALLY) THEN
   MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN BETA_TAC THEN
   ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC LEVY_CONTINUITY_CLT THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < sqrt sigma2` ASSUME_TAC THENL
  [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. &0 < sqrt(&(SUC n))` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN
   REWRITE_TAC[REAL_OF_NUM_LT; LT_0]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. ~(sqrt sigma2 * sqrt(&(SUC n)) = &0)` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN
   MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* E[X_0^2] = sigma2 when E[X]=0 *)
  SUBGOAL_THEN `expectation (p:A prob_space)
    (\x:A. (X:num->A->real) 0 x pow 2) = sigma2` ASSUME_TAC THENL
  [EXPAND_TAC "sigma2" THEN
   MATCH_MP_TAC VARIANCE_MEAN_ZERO THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
  [(* Bounded second moments: E[Y_n^2] <= 2 *)
   EXISTS_TAC `&2` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
   X_GEN_TAC `n:num` THEN
   (* E[Y_n^2] = E[(sum/denom)^2] = E[sum^2]/denom^2 = (n+1)*sigma2 / ((sigma2)*(n+1)) = 1 *)
   SUBGOAL_THEN `integrable (p:A prob_space) ((Y:num->A->real) n)` ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN BETA_TAC THEN
    REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    MATCH_MP_TAC INTEGRABLE_CMUL THEN
    MATCH_MP_TAC INTEGRABLE_SUM THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space)
     (\x:A. (Y:num->A->real) n x pow 2)` ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN BETA_TAC THEN
    REWRITE_TAC[REAL_POW_DIV; real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    MATCH_MP_TAC INTEGRABLE_CMUL THEN
    MATCH_MP_TAC INTEGRABLE_SUM_SQUARE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
   (* E[Y_n^2] = E[sum^2] / denom^2 = (n+1)*sigma2 / (sigma2*(n+1)) = 1 <= 2 *)
   SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. (Y:num->A->real) n x pow 2) =
     expectation p (\x. sum(0..n) (\i. (X:num->A->real) i x) pow 2) /
     (sqrt sigma2 * sqrt(&(SUC n))) pow 2` ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN BETA_TAC THEN
    REWRITE_TAC[REAL_POW_DIV; real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    MATCH_MP_TAC EXPECTATION_CMUL THEN
    MATCH_MP_TAC INTEGRABLE_SUM_SQUARE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
   (* denom^2 = sigma2 * (n+1) *)
   SUBGOAL_THEN `(sqrt sigma2 * sqrt(&(SUC n))) pow 2 = sigma2 * &(SUC n)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_MUL] THEN
    SUBGOAL_THEN `sqrt sigma2 pow 2 = sigma2` SUBST1_TAC THENL
    [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `sqrt (&(SUC n)) pow 2 = &(SUC n)` SUBST1_TAC THENL
    [MATCH_MP_TAC SQRT_POW_2 THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    REFL_TAC;
    ALL_TAC] THEN
   (* E[sum^2] = (n+1)*sigma2 (by variance of IID sum with mean 0) *)
   SUBGOAL_THEN `expectation (p:A prob_space)
     (\x:A. sum(0..n) (\i. (X:num->A->real) i x) pow 2) =
     &(SUC n) * sigma2` ASSUME_TAC THENL
   [(* E[sum^2] = variance(sum) since E[sum]=0 *)
    SUBGOAL_THEN `expectation (p:A prob_space)
      (\x:A. sum(0..n) (\i. (X:num->A->real) i x)) = &0` ASSUME_TAC THENL
    [ASM_SIMP_TAC[EXPECTATION_SUM] THEN
     ASM_REWRITE_TAC[SUM_0]; ALL_TAC] THEN
    SUBGOAL_THEN `expectation (p:A prob_space)
      (\x:A. sum(0..n) (\i. (X:num->A->real) i x) pow 2) =
      variance p (\x. sum(0..n) (\i. X i x))` ASSUME_TAC THENL
    [MATCH_MP_TAC VARIANCE_MEAN_ZERO THEN
     ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_SUM THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC INTEGRABLE_SUM_SQUARE THEN ASM_SIMP_TAC[]];
     ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    (* variance(sum) = sum(variance(X_i)) by uncorrelatedness *)
    SUBGOAL_THEN `variance (p:A prob_space) (\x:A. sum(0..n) (\i. (X:num->A->real) i x)) =
      sum(0..n) (\i. variance p (X i))` ASSUME_TAC THENL
    [MATCH_MP_TAC VARIANCE_SUM_UNCORRELATED THEN
     ASM_SIMP_TAC[] THEN
     REPEAT STRIP_TAC THEN MATCH_MP_TAC COVARIANCE_INDEP THEN
     ASM_SIMP_TAC[] THEN
     MATCH_MP_TAC INTEGRABLE_MUL_SQUARE THEN
     REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    (* Each variance(X_i) = sigma2 *)
    SUBGOAL_THEN `!i:num. variance (p:A prob_space) ((X:num->A->real) i) = sigma2`
      ASSUME_TAC THENL
    [GEN_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0; ADD1];
    ALL_TAC] THEN
   (* E[Y_n^2] = (n+1)*sigma2 / (sigma2*(n+1)) = 1 <= 2 *)
   ASM_REWRITE_TAC[] THEN
   GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
   SUBGOAL_THEN `~(&(SUC n) * sigma2 = &0)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
    [REWRITE_TAC[REAL_OF_NUM_LT; LT_0]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_DIV_REFL] THEN REAL_ARITH_TAC;
   (* integrability of Y_n *)
   GEN_TAC THEN EXPAND_TAC "Y" THEN BETA_TAC THEN
   REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
   MATCH_MP_TAC INTEGRABLE_CMUL THEN
   MATCH_MP_TAC INTEGRABLE_SUM THEN ASM_SIMP_TAC[];
   (* integrability of Y_n^2 *)
   GEN_TAC THEN EXPAND_TAC "Y" THEN BETA_TAC THEN
   REWRITE_TAC[REAL_POW_DIV; real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
   MATCH_MP_TAC INTEGRABLE_CMUL THEN
   MATCH_MP_TAC INTEGRABLE_SUM_SQUARE THEN ASM_SIMP_TAC[];
   (* gen_char_fn_re convergence *)
   X_GEN_TAC `t:real` THEN EXPAND_TAC "Y" THEN BETA_TAC THEN
   REWRITE_TAC[GEN_CHAR_FN_RE_DIV] THEN
   (* gen_char_fn_re p (\x. sum(...)) (t/(sigma*sqrt(n+1))) *)
   (* = gen_char_fn_re p (\x. sum(...)) ((t/sigma)/sqrt(n+1)) *)
   SUBGOAL_THEN `!n:num. gen_char_fn_re (p:A prob_space)
     (\x:A. sum(0..n) (\i. (X:num->A->real) i x))
     (t / (sqrt sigma2 * sqrt (&(SUC n)))) =
     gen_char_fn_re p (\x. sum(0..n) (\i. X i x))
     (t / sqrt sigma2 / sqrt (&(SUC n)))` ASSUME_TAC THENL
   [GEN_TAC THEN AP_TERM_TAC THEN CONV_TAC REAL_FIELD;
    ASM_REWRITE_TAC[]] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`; `t / sqrt sigma2`]
     GEN_CLT_CHAR_FN_CONVERGENCE) THEN
   ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[];
     X_GEN_TAC `jj:num` THEN
     SUBGOAL_THEN `expectation (p:A prob_space)
       (\x:A. (X:num->A->real) jj x pow 2) = variance p (X jj)` SUBST1_TAC THENL
     [MATCH_MP_TAC VARIANCE_MEAN_ZERO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     ASM_REWRITE_TAC[];
     FIRST_ASSUM MATCH_ACCEPT_TAC;
     FIRST_ASSUM MATCH_ACCEPT_TAC];
    ALL_TAC] THEN
   (* Establish limit equality: (t/sqrt sigma2)^2 * sigma2 / 2 = t^2 / 2 *)
   SUBGOAL_THEN `exp(--((t / sqrt sigma2) pow 2 * sigma2 / &2)) =
     exp(--(t pow 2 / &2))` ASSUME_TAC THENL
   [AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_POW_DIV] THEN
    SUBGOAL_THEN `sqrt sigma2 pow 2 = sigma2` SUBST1_TAC THENL
    [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(sigma2 = &0)` MP_TAC THENL
    [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
   ASM_REWRITE_TAC[];
   (* gen_char_fn_im convergence *)
   X_GEN_TAC `t:real` THEN EXPAND_TAC "Y" THEN BETA_TAC THEN
   REWRITE_TAC[GEN_CHAR_FN_IM_DIV] THEN
   SUBGOAL_THEN `!n:num. gen_char_fn_im (p:A prob_space)
     (\x:A. sum(0..n) (\i. (X:num->A->real) i x))
     (t / (sqrt sigma2 * sqrt (&(SUC n)))) =
     gen_char_fn_im p (\x. sum(0..n) (\i. X i x))
     (t / sqrt sigma2 / sqrt (&(SUC n)))` ASSUME_TAC THENL
   [GEN_TAC THEN AP_TERM_TAC THEN CONV_TAC REAL_FIELD;
    ASM_REWRITE_TAC[]] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`; `t / sqrt sigma2`]
     GEN_CLT_CHAR_FN_IM_CONVERGENCE) THEN
   ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[];
     X_GEN_TAC `jj:num` THEN
     SUBGOAL_THEN `expectation (p:A prob_space)
       (\x:A. (X:num->A->real) jj x pow 2) = variance p (X jj)` SUBST1_TAC THENL
     [MATCH_MP_TAC VARIANCE_MEAN_ZERO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     ASM_REWRITE_TAC[];
     FIRST_ASSUM MATCH_ACCEPT_TAC;
     FIRST_ASSUM MATCH_ACCEPT_TAC];
    ALL_TAC] THEN
   SIMP_TAC[]]);;

let _ = let oc = open_out "/tmp/hol_compile_ok" in
        output_string oc "OK\n"; close_out oc;;

(* End of probability theory development *)
