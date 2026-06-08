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
(* Convergence in probability implies convergence in distribution            *)
(* ========================================================================= *)

let IN_PROB_IMP_IN_DIST = prove
 (`!(p:A prob_space) (X:num->A->real) (L:A->real).
     (!n:num. random_variable p (X n)) /\
     random_variable p L /\
     converges_in_prob p X L
     ==> !x:real.
           (\y. cdf p L y) real_continuous atreal x
           ==> ((\n. cdf p (X n) x) ---> cdf p L x)
               sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `x:real` THEN
  REWRITE_TAC[real_continuous_atreal] THEN DISCH_TAC THEN
  REWRITE_TAC[tendsto_real; EVENTUALLY_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(e:real) / &2`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `d = (d0:real) / &2` THEN
  (SUBGOAL_THEN `&0 < (d:real) /\ d < d0`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN
    `abs(cdf (p:A prob_space) (L:A->real) (x + d) -
         cdf p L x) < e / &2 /\
     abs(cdf p L (x - d) - cdf p L x) < e / &2`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o SPEC `(x:real) + d`) THEN
     MATCH_MP_TAC(TAUT `a ==> (a ==> b) ==> b`) THEN
     ASM_REAL_ARITH_TAC;
     FIRST_X_ASSUM(MP_TAC o SPEC `(x:real) - d`) THEN
     MATCH_MP_TAC(TAUT `a ==> (a ==> b) ==> b`) THEN
     ASM_REAL_ARITH_TAC];
    ALL_TAC]) THEN
  FIRST_X_ASSUM
    (MP_TAC o GEN_REWRITE_RULE I [converges_in_prob]) THEN
  DISCH_THEN(MP_TAC o SPEC `d:real`) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[tendsto_real; EVENTUALLY_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `(e:real) / &2`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `N:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  (* sg4: {a | abs(Xn a - L a) >= d} is an event *)
  (SUBGOAL_THEN
    `{a:A | a IN prob_carrier p /\
       abs((X:num->A->real) n a - (L:A->real) a) >= d}
     IN prob_events p`
    ASSUME_TAC THENL
   [MATCH_MP_TAC ABS_GE_IN_EVENTS THEN
    MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN
    CONJ_TAC THENL
    [REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[]];
    ALL_TAC]) THEN
  (* pn_bounds: establish before sg1/sg2 so FIRST_X_ASSUM *)
  (* picks the convergence bound, not sg2 which is !m:num *)
  ABBREV_TAC
    `pn = prob (p:A prob_space)
      {a:A | a IN prob_carrier p /\
        abs((X:num->A->real) n a -
            (L:A->real) a) >= d}` THEN
  (SUBGOAL_THEN `&0 <= (pn:real) /\ pn < e / &2`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [ASM_MESON_TAC[PROB_POSITIVE]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
    ASM_MESON_TAC[REAL_LET_TRANS;
      REAL_ARITH `abs x < e ==> x < e`];
    ALL_TAC]) THEN
  (* Establish measurability *)
  (SUBGOAL_THEN
    `!y. {a:A | a IN prob_carrier p /\
            (L:A->real) a <= y}
         IN prob_events p`
    ASSUME_TAC THENL
   [REWRITE_TAC[GSYM random_variable] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN
    `!m:num.
       {a:A | a IN prob_carrier p /\
              (X:num->A->real) m a <= x}
       IN prob_events p`
    ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(REWRITE_RULE[random_variable; ETA_AX]
      (SPEC `m:num`
        (ASSUME `!n:num. random_variable (p:A prob_space)
                   ((X:num->A->real) n)`))) THEN
    DISCH_THEN(MP_TAC o SPEC `x:real`) THEN
    REWRITE_TAC[];
    ALL_TAC]) THEN
  (* sg5: cdf(Xn,x) <= cdf(L,x+d) + pn *)
  (SUBGOAL_THEN
    `cdf (p:A prob_space) ((X:num->A->real) n) x <=
     cdf p (L:A->real) (x + d) + pn`
    ASSUME_TAC THENL
   [REWRITE_TAC[cdf] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
      `prob (p:A prob_space)
        ({a:A | a IN prob_carrier p /\
                (L:A->real) a <= x + d} UNION
         {a | a IN prob_carrier p /\
           abs((X:num->A->real) n a -
               L a) >= d})` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC PROB_MONO THEN
     CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC PROB_UNION_IN_EVENTS THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN
      X_GEN_TAC `a:A` THEN STRIP_TAC THEN
      ASM_CASES_TAC
        `abs((X:num->A->real) n a -
             (L:A->real) a) >= d` THENL
      [DISJ2_TAC THEN ASM_REWRITE_TAC[];
       DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
       ASM_REAL_ARITH_TAC]];
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC
       `prob (p:A prob_space)
         {a:A | a IN prob_carrier p /\
                (L:A->real) a <= x + d} +
        prob p
         {a | a IN prob_carrier p /\
           abs((X:num->A->real) n a -
               L a) >= d}` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC PROB_SUBADDITIVE THEN
      ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[REAL_LE_REFL]]];
    ALL_TAC]) THEN
  (* sg6: cdf(L,x-d) - pn <= cdf(Xn,x) *)
  (SUBGOAL_THEN
    `cdf (p:A prob_space) (L:A->real) (x - d) - pn <=
     cdf p ((X:num->A->real) n) x`
    ASSUME_TAC THENL
   [REWRITE_TAC[cdf] THEN
    REWRITE_TAC[REAL_ARITH `a - b <= c <=> a <= c + b`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
      `prob (p:A prob_space)
        ({a:A | a IN prob_carrier p /\
                (X:num->A->real) n a <= x} UNION
         {a | a IN prob_carrier p /\
           abs(X n a -
               (L:A->real) a) >= d})` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC PROB_MONO THEN
     CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC PROB_UNION_IN_EVENTS THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN
      X_GEN_TAC `a:A` THEN STRIP_TAC THEN
      ASM_CASES_TAC
        `abs((X:num->A->real) n a -
             (L:A->real) a) >= d` THENL
      [DISJ2_TAC THEN ASM_REWRITE_TAC[];
       DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
       ASM_REAL_ARITH_TAC]];
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC
       `prob (p:A prob_space)
         {a:A | a IN prob_carrier p /\
                (X:num->A->real) n a <= x} +
        prob p
         {a | a IN prob_carrier p /\
           abs(X n a -
               (L:A->real) a) >= d}` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC PROB_SUBADDITIVE THEN
      ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[REAL_LE_REFL]]];
    ALL_TAC]) THEN
  (* Final: combine sg3, sg5, sg6, pn_bounds *)
  UNDISCH_TAC
    `cdf (p:A prob_space) ((X:num->A->real) n) x <=
     cdf p (L:A->real) (x + d) + pn` THEN
  UNDISCH_TAC
    `cdf (p:A prob_space) (L:A->real) (x - d) - pn <=
     cdf p ((X:num->A->real) n) x` THEN
  UNDISCH_TAC
    `abs(cdf (p:A prob_space) (L:A->real) (x + d) -
         cdf p L x) < e / &2` THEN
  UNDISCH_TAC
    `abs(cdf (p:A prob_space) (L:A->real) (x - d) -
         cdf p L x) < e / &2` THEN
  UNDISCH_TAC `(pn:real) < e / &2` THEN
  REAL_ARITH_TAC);;

(* Almost sure convergence implies convergence in probability
   (clean version with random_variable hypotheses only) *)
let AS_IMP_IN_PROB = prove
 (`!p:A prob_space (X:num->A->real) (L:A->real).
     (!n. random_variable p (X n)) /\
     random_variable p L /\
     converges_as p X L
     ==> converges_in_prob p X L`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ALMOST_SURE_IMP_IN_PROB THEN
  REPEAT CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC RV_PREIMAGE_GE THEN
   MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN
   MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN
   ASM_REWRITE_TAC[ETA_AX];
   MATCH_MP_TAC CONVERGENCE_SET_IN_EVENTS THEN
   ASM_REWRITE_TAC[];
   ASM_REWRITE_TAC[]]);;

(* L2 convergence implies convergence in distribution *)
let L2_IMP_IN_DIST = prove
 (`!p:A prob_space (X:num->A->real) (L:A->real).
     (!n. random_variable p (X n)) /\
     random_variable p L /\
     (!n. integrable p (\x. (X n x - L x) pow 2)) /\
     converges_L2 p X L
     ==> converges_in_distribution p X (cdf p L)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[converges_in_distribution] THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `converges_in_prob (p:A prob_space) (X:num->A->real) (L:A->real)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC CONVERGES_L2_IMP_IN_PROB THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`; `L:A->real`]
    IN_PROB_IMP_IN_DIST) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real`) THEN
  REWRITE_TAC[ETA_AX] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Almost sure convergence implies convergence in distribution *)
let AS_IMP_IN_DIST = prove
 (`!p:A prob_space (X:num->A->real) (L:A->real).
     (!n. random_variable p (X n)) /\
     random_variable p L /\
     converges_as p X L
     ==> converges_in_distribution p X (cdf p L)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[converges_in_distribution] THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `converges_in_prob (p:A prob_space) (X:num->A->real) (L:A->real)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC AS_IMP_IN_PROB THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`; `L:A->real`]
    IN_PROB_IMP_IN_DIST) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real`) THEN
  REWRITE_TAC[ETA_AX] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

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

(* CHAR_FN_RE_LOWER_BOUND: E[cos(tX)] >= 1 - t^2 * E[X^2] / 2 *)
let CHAR_FN_RE_LOWER_BOUND = prove
 (`!p:A prob_space X t.
     integrable p X /\ integrable p (\x. X x pow 2)
     ==> &1 - t pow 2 * expectation p (\x. X x pow 2) / &2
         <= char_fn_re p X t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[char_fn_re] THEN
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

(* CHAR_FN_RE_UPPER_BOUND: char_fn_re p X t <= 1 *)
let CHAR_FN_RE_UPPER_BOUND = prove
 (`!p:A prob_space X t.
     integrable p X /\ integrable p (\x. X x pow 2)
     ==> char_fn_re p X t <= &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[char_fn_re] THEN
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
   [SET_TAC[REAL_ARITH
      `!x t:real. abs x >= t <=> x >= t \/ --x >= t`];
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
   Uses PROB_STRICT_INEQ_LIMIT and REALLIM_UNIQUE. *)
let INDEP_RV_STRICT_INEQ = prove
 (`!p:A prob_space (X:A->real) (Y:A->real) a b.
       indep_rv p X Y
       ==> prob p {x | x IN prob_carrier p /\ X x < a /\ Y x < b} =
           prob p {x | x IN prob_carrier p /\ X x < a} *
           prob p {x | x IN prob_carrier p /\ Y x < b}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[indep_rv] THEN STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC `\n:num. prob (p:A prob_space)
    {x:A | x IN prob_carrier p /\ (X:A->real) x <= a - &1 / &(SUC n)} *
    prob p {x | x IN prob_carrier p /\ (Y:A->real) x <= b - &1 / &(SUC n)}` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
  [SUBGOAL_THEN `(\n. prob (p:A prob_space) {x:A | x IN prob_carrier p /\
     (X:A->real) x <= a - &1 / &(SUC n)} * prob p {x | x IN prob_carrier p /\
     (Y:A->real) x <= b - &1 / &(SUC n)}) = (\n. prob p {x | x IN
     prob_carrier p /\ X x <= a - &1 / &(SUC n) /\ Y x <= b - &1 / &(SUC n)})`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN CONV_TAC SYM_CONV THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`p:A prob_space`;
      `\n:num. {x:A | x IN prob_carrier p /\ (X:A->real) x <= a - &1 / &(SUC n)
         /\ (Y:A->real) x <= b - &1 / &(SUC n)}`]
      PROB_CONTINUITY_FROM_BELOW) THEN
    BETA_TAC THEN ANTS_TAC THENL
    [CONJ_TAC THENL
     [GEN_TAC THEN
      SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ (X:A->real) x <=
        a - &1 / &(SUC n) /\ (Y:A->real) x <= b - &1 / &(SUC n)} =
        {x | x IN prob_carrier p /\ X x <= a - &1 / &(SUC n)} INTER
        {x | x IN prob_carrier p /\ Y x <= b - &1 / &(SUC n)}` SUBST1_TAC THENL
      [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN MESON_TAC[];
       MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN ASM_MESON_TAC[random_variable]];
      GEN_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THENL
      [EXISTS_TAC `a - &1 / &(SUC n)`; EXISTS_TAC `b - &1 / &(SUC n)`] THEN
      ASM_REWRITE_TAC[REAL_ARITH `a - x <= a - y <=> y <= x`] THEN
      REWRITE_TAC[real_div; REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ARITH_TAC];
     SUBGOAL_THEN
       `UNIONS {{x:A | x IN prob_carrier p /\ (X:A->real) x <=
          a - &1 / &(SUC n) /\ (Y:A->real) x <= b - &1 / &(SUC n)} |
          n IN (:num)} =
        {x | x IN prob_carrier p /\ X x < a /\ Y x < b}`
       (fun th -> REWRITE_TAC[th]) THEN
     REWRITE_TAC[UNIONS_GSPEC; IN_UNIV; EXTENSION; IN_ELIM_THM] THEN
     GEN_TAC THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
      (SUBGOAL_THEN `&0 < &1 / &(SUC n)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
        ARITH_TAC; ASM_REAL_ARITH_TAC]);
      STRIP_TAC THEN
      MP_TAC(SPEC `a - (X:A->real) x` REAL_ARCH_INV) THEN
      MP_TAC(SPEC `b - (Y:A->real) x` REAL_ARCH_INV) THEN
      ASM_SIMP_TAC[REAL_SUB_LT] THEN
      DISCH_THEN(X_CHOOSE_THEN `m2:num` STRIP_ASSUME_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN `m1:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `m1 + m2:num` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THENL
      [EXISTS_TAC `a - inv(&m1)`; EXISTS_TAC `b - inv(&m2)`] THEN
      (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
      REWRITE_TAC[REAL_ARITH `a - x <= a - y <=> y <= x`;
        real_div; REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC]]];
   MATCH_MP_TAC REALLIM_MUL THEN CONJ_TAC THEN
   MATCH_MP_TAC PROB_STRICT_INEQ_LIMIT THEN ASM_REWRITE_TAC[]]);;

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

(* SIMPLE_RV_ABS_BOUNDED relocated to martingale_convergence.ml (used by the   *)
(* simple-multiplier take-out); available here via the earlier load.            *)

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
    MCT_NN_EXPECTATION_INTEGRABLE) THEN
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
   char_fn_re p (X+Y) t = char_fn_re p X t * char_fn_re p Y t
                              - char_fn_im p X t * char_fn_im p Y t
   Proof: Truncate X,Y at +-M to get bounded independent approximations,
   shift to nonneg, use nsfa + INDEP_RV_NSFA for simple approximations,
   apply EXPECTATION_PRODUCT_COMPOSE_SIMPLE_INDEP, then bounded convergence. *)
let CHAR_FN_ADD_INDEP_RE = prove
 (`!p:A prob_space (X:A->real) (Y:A->real) t.
    random_variable p X /\ random_variable p Y /\ indep_rv p X Y
    ==> char_fn_re p (\x. X x + Y x) t =
        char_fn_re p X t * char_fn_re p Y t -
        char_fn_im p X t * char_fn_im p Y t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[char_fn_re; char_fn_im] THEN BETA_TAC THEN
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

(* CHAR_FN_ADD_INDEP_IM for integrable (random_variable) RVs.
   Derived from CHAR_FN_ADD_INDEP_RE via a phase shift:
   sin(t(X+Y)) = cos(t(X+Y) - pi/2) = cos(tX + t(Y - pi/(2t)))
   Then apply the RE formula with Y' = Y - pi/(2t) and simplify. *)
let CHAR_FN_ADD_INDEP_IM = prove
 (`!p:A prob_space X Y t.
    random_variable p X /\ random_variable p Y /\ indep_rv p X Y
    ==> char_fn_im p (\x. X x + Y x) t =
        char_fn_re p X t * char_fn_im p Y t +
        char_fn_im p X t * char_fn_re p Y t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `t = &0` THENL
  [ASM_REWRITE_TAC[char_fn_im; char_fn_re; REAL_MUL_LZERO;
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
  (* Apply CHAR_FN_ADD_INDEP_RE to X and Y' *)
  MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `Y':A->real`; `t:real`]
    CHAR_FN_ADD_INDEP_RE) THEN
  ASM_REWRITE_TAC[] THEN
  (* LHS: char_fn_re p (\x. X x + Y' x) t *)
  SUBGOAL_THEN `(\x:A. (X:A->real) x + (Y':A->real) x) =
                (\x. X x + Y x + c)` SUBST1_TAC THENL
  [EXPAND_TAC "Y'" THEN REWRITE_TAC[FUN_EQ_THM] THEN
   GEN_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* char_fn_re p (\x. X x + Y x + c) t = char_fn_im p (\x. X x + Y x) t *)
  SUBGOAL_THEN `char_fn_re (p:A prob_space) (\x:A. X x + Y x + c) t =
                char_fn_im p (\x. X x + Y x) t` SUBST1_TAC THENL
  [REWRITE_TAC[char_fn_re; char_fn_im] THEN
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
  (* RHS: char_fn_re/im of Y' in terms of Y *)
  SUBGOAL_THEN `char_fn_re (p:A prob_space) (Y':A->real) t =
                char_fn_im p Y t` SUBST1_TAC THENL
  [REWRITE_TAC[char_fn_re; char_fn_im] THEN
   AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
   X_GEN_TAC `a:A` THEN EXPAND_TAC "Y'" THEN BETA_TAC THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `char_fn_im (p:A prob_space) (Y':A->real) t =
                --(char_fn_re p Y t)` SUBST1_TAC THENL
  [REWRITE_TAC[char_fn_im; char_fn_re] THEN
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

(* COS_APPROX_BOUND: defined in characteristic_functions.ml *)

(* Corollary: cos(x) - 1 + x^2/2 <= x^4/6 (without abs, using non-negativity) *)
let COS_TAYLOR_BOUND_4 = prove
 (`!x:real. cos x - &1 + x pow 2 / &2 <= x pow 4 / &6`,
  GEN_TAC THEN
  MP_TAC(SPEC `x:real` COS_APPROX_BOUND) THEN REAL_ARITH_TAC);;


(* DOMINATED_CONVERGENCE_NULL moved to expectation.ml *)



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
         char_fn_re p X s - &1 +
         s pow 2 * expectation p (\x. X x pow 2) / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `random_variable (p:A prob_space) (X:A->real)` ASSUME_TAC THENL
  [ASM_MESON_TAC[integrable]; ALL_TAC] THEN
  REWRITE_TAC[char_fn_re] THEN
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

(* CLT_RE_PERTURBATION_VANISHES:
   The Taylor remainder of the real part of the char fn, scaled by (n+1),
   converges to 0. This is the key DCT step.
   Uses: 0 <= cos(z)-1+z^2/2 <= z^4/6, with dominator t^2*X^2/2 *)
let CLT_RE_PERTURBATION_VANISHES = prove
 (`!p:A prob_space (X:A->real) t.
     integrable p X /\ integrable p (\x. X x pow 2)
     ==> ((\n. &(SUC n) *
               (char_fn_re p X (t / sqrt(&(SUC n))) - &1 +
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

(* CLT_IM_ERROR_VANISHES:
   (n+1) * |char_fn_im(t/sqrt(n+1))| --> 0 when E[X] = 0.
   Uses: |sin(z)-z| <= z^2, so |E[sin(sX)]| = |E[sin(sX)-sX]| <= s^2*E[X^2]
   With DCT: (n+1)|char_fn_im(t/sqrt(n+1))| <= t^2*E[X^2] and --> 0 *)
let CLT_IM_ERROR_VANISHES = prove
 (`!p:A prob_space (X:A->real) t.
     integrable p X /\ integrable p (\x. X x pow 2) /\
     expectation p X = &0
     ==> ((\n. &(SUC n) *
               abs(char_fn_im p X (t / sqrt(&(SUC n)))))
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
   REWRITE_TAC[char_fn_im] THEN
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

(* CHAR_FN_RE_POW_CONV_EXP:
   char_fn_re(X, t/sqrt(n+1))^(n+1) --> exp(-t^2*sigma^2/2)
   Proof: write char_fn_re(s) = 1 - (c + h(n))/(n+1) where c = t^2*sigma^2/2
   and h(n) = -r(n) --> 0 by CLT_RE_PERTURBATION_VANISHES.
   Apply REALLIM_POW_EXP_NEG_PERTURB. *)
let CHAR_FN_RE_POW_CONV_EXP = prove
 (`!p:A prob_space (X:A->real) t.
     integrable p X /\ integrable p (\x. X x pow 2) /\
     &0 < expectation p (\x. X x pow 2)
     ==> ((\n. char_fn_re p X (t / sqrt(&(SUC n))) pow (SUC n))
          ---> exp(--(t pow 2 * expectation p (\x. X x pow 2) / &2)))
         sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `random_variable (p:A prob_space) (X:A->real)` ASSUME_TAC THENL
  [ASM_MESON_TAC[integrable]; ALL_TAC] THEN
  ABBREV_TAC `sigma2 = expectation (p:A prob_space)
    (\x:A. (X:A->real) x pow 2)` THEN
  (* Case t = 0: trivial *)
  ASM_CASES_TAC `t = &0` THENL
  [ASM_SIMP_TAC[real_div; REAL_MUL_LZERO; CHAR_FN_RE_ZERO;
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
  (* Define perturbation h(n) = (n+1)*(1 - char_fn_re(s)) - c *)
  ABBREV_TAC `h = \n:num. &(SUC n) *
    (&1 - char_fn_re (p:A prob_space) (X:A->real)
      (t / sqrt(&(SUC n)))) - c` THEN
  (* Transform: char_fn_re^(n+1) = (1-(c+h(n))/(n+1))^(n+1) *)
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\n. (&1 - (c + (h:num->real) n) / &(SUC n)) pow (SUC n)` THEN
  CONJ_TAC THENL
  [(* Algebraic identity: char_fn_re(s) = 1 - (c+h(n))/(n+1) *)
   MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN BETA_TAC THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN
   EXPAND_TAC "h" THEN BETA_TAC THEN
   SUBGOAL_THEN `~(&(SUC n) = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `~(&(SUC n) = &0)` THEN CONV_TAC REAL_FIELD;
   ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_POW_EXP_NEG_PERTURB THEN
  ASM_REWRITE_TAC[] THEN
  (* Show h --> 0 using CLT_RE_PERTURBATION_VANISHES *)
  (* h(n) = -(perturbation sequence) *)
  EXPAND_TAC "h" THEN EXPAND_TAC "c" THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\n. --(&(SUC n) *
    (char_fn_re (p:A prob_space) (X:A->real)
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
  MATCH_MP_TAC CLT_RE_PERTURBATION_VANISHES THEN
  ASM_REWRITE_TAC[]);;


(* CHAR_FN_SUM_IID_RE_BOUND:
   |char_fn_re(sum, t) - char_fn_re(X_0, t)^(n+1)|
   <= (n+1) * |char_fn_im(X_0, t)|
   Inductive: same structure as SIMPLE_CHAR_FN_SUM_IID_RE_BOUND but using
   CHAR_FN_ADD_INDEP_RE/IM. *)
let CHAR_FN_SUM_IID_RE_BOUND = prove
 (`!p:A prob_space (X:num->A->real) n t.
     (!i. random_variable p (X i)) /\
     (!i t. char_fn_re p (X i) t = char_fn_re p (X 0) t /\
            char_fn_im p (X i) t = char_fn_im p (X 0) t) /\
     (!k. k < n ==> indep_rv p (\x. sum(0..k) (\i. X i x)) (X (SUC k)))
     ==> abs(char_fn_re p (\x. sum(0..n) (\i. X i x)) t -
             char_fn_re p (X 0) t pow (SUC n))
         <= &(SUC n) * abs(char_fn_im p (X 0) t)`,
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
     CHAR_FN_ADD_INDEP_RE) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   BETA_TAC THEN DISCH_TAC THEN
   ONCE_ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN
     `char_fn_re (p:A prob_space) ((X:num->A->real) (SUC n)) t =
      char_fn_re p (X 0) t /\
      char_fn_im p (X (SUC n)) t = char_fn_im p (X 0) t`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
   ONCE_ASM_REWRITE_TAC[] THEN
   ONCE_REWRITE_TAC[real_pow] THEN
   MATCH_MP_TAC SIMPLE_CHAR_FN_SUM_IID_TRIANGLE THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC CHAR_FN_RE_BOUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC CHAR_FN_IM_BOUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

(* CLT_CHAR_FN_CONVERGENCE:
   Main assembly: char_fn_re of standardized sum --> exp(-t^2*sigma^2/2)
   Combines: CHAR_FN_RE_POW_CONV_EXP, CHAR_FN_SUM_IID_RE_BOUND,
   CLT_IM_ERROR_VANISHES via REALLIM_TRANSFORM + comparison *)
let CLT_CHAR_FN_CONVERGENCE = prove
 (`!p:A prob_space (X:num->A->real) t.
     (!n. integrable p (X n)) /\
     (!n. integrable p (\x. X n x pow 2)) /\
     (!i. expectation p (X i) = &0) /\
     &0 < expectation p (\x. X 0 x pow 2) /\
     (!i. expectation p (\x. X i x pow 2) = expectation p (\x. X 0 x pow 2)) /\
     (!i t. char_fn_re p (X i) t = char_fn_re p (X 0) t /\
            char_fn_im p (X i) t = char_fn_im p (X 0) t) /\
     (!n k. k < n ==> indep_rv p (\x. sum(0..k) (\i. X i x)) (X (SUC k)))
     ==> ((\n. char_fn_re p (\x. sum(0..n) (\i. X i x))
                             (t / sqrt(&(SUC n))))
          ---> exp(--(t pow 2 * expectation p (\x. X 0 x pow 2) / &2)))
         sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Step 1: Show the difference from the power vanishes *)
  MATCH_MP_TAC REALLIM_TRANSFORM THEN
  EXISTS_TAC `\n. char_fn_re (p:A prob_space) ((X:num->A->real) 0)
                    (t / sqrt(&(SUC n))) pow (SUC n)` THEN
  CONJ_TAC THENL
  [(* The difference vanishes *)
   MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
   EXISTS_TAC `\n. &(SUC n) * abs(char_fn_im (p:A prob_space)
                   ((X:num->A->real) 0) (t / sqrt(&(SUC n))))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
    REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
    MATCH_MP_TAC CHAR_FN_SUM_IID_RE_BOUND THEN
    ASM_MESON_TAC[integrable];
    (* (n+1)*|char_fn_im(X_0, t/sqrt(n+1))| --> 0 *)
    MATCH_MP_TAC CLT_IM_ERROR_VANISHES THEN
    ASM_REWRITE_TAC[]];
   (* Step 2: The power converges *)
   MATCH_MP_TAC CHAR_FN_RE_POW_CONV_EXP THEN
   ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Phase 22: Integrable Levy continuity chain for INTEGRABLE_CLT             *)
(* ========================================================================= *)

(* cdf is in [0,1] for any random variable *)
let CDF_BOUNDS = prove
 (`!p:A prob_space (X:A->real) x.
     random_variable p X
     ==> &0 <= cdf p X x /\ cdf p X x <= &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cdf] THENL
  [MATCH_MP_TAC PROB_POSITIVE THEN
   FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [random_variable]) THEN
   DISCH_THEN(MP_TAC o SPEC `x:real`) THEN REWRITE_TAC[];
   MATCH_MP_TAC PROB_LE_1 THEN
   FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [random_variable]) THEN
   DISCH_THEN(MP_TAC o SPEC `x:real`) THEN REWRITE_TAC[]]);;

(* char_fn under division by constant *)
let CHAR_FN_RE_DIV = prove
 (`!p:A prob_space (X:A->real) c t.
     char_fn_re p (\x. X x / c) t = char_fn_re p X (t / c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[char_fn_re; real_div] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  GEN_TAC THEN AP_TERM_TAC THEN CONV_TAC REAL_RING);;

let CHAR_FN_IM_DIV = prove
 (`!p:A prob_space (X:A->real) c t.
     char_fn_im p (\x. X x / c) t = char_fn_im p X (t / c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[char_fn_im; real_div] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  GEN_TAC THEN AP_TERM_TAC THEN CONV_TAC REAL_RING);;

(* E[g(X)] <= cdf(X,x) when g(y) <= 1 for y<=x, g(y) <= 0 for y>x *)
(* Needs: random_variable composition for measurable g - will prove when needed *)
let EXPECTATION_LE_CDF = prove
 (`!p:A prob_space (X:A->real) (g:real->real) x.
     random_variable p X /\
     integrable p (\a. g(X a)) /\
     (!y. y <= x ==> g y <= &1) /\
     (!y. y > x ==> g y <= &0)
     ==> expectation p (\a. g(X a)) <= cdf p X x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{a | a IN prob_carrier (p:A prob_space) /\
    (X:A->real) a <= x} IN prob_events p` ASSUME_TAC THENL
  [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [random_variable]) THEN
   DISCH_THEN(MP_TAC o SPEC `x:real`) THEN REWRITE_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[cdf] THEN
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

(* cdf(X,x) <= E[g(X)] when g(y) >= 1 for y<=x, g(y) >= 0 for y>x *)
(* Needs: integrability of g o X as hypothesis *)
let CDF_LE_EXPECTATION = prove
 (`!p:A prob_space (X:A->real) (g:real->real) x.
     random_variable p X /\
     integrable p (\a. g(X a)) /\
     (!y. y <= x ==> &1 <= g y) /\
     (!y. y > x ==> &0 <= g y)
     ==> cdf p X x <= expectation p (\a. g(X a))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{a | a IN prob_carrier (p:A prob_space) /\
    (X:A->real) a <= x} IN prob_events p` ASSUME_TAC THENL
  [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [random_variable]) THEN
   DISCH_THEN(MP_TAC o SPEC `x:real`) THEN REWRITE_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[cdf] THEN
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

(* Modulus identity for char_fn of IID sums: |cf(sum)|^2 = |cf(X_0)|^{2(n+1)}
   Generalized from SIMPLE_CHAR_FN_SUM_IID_MODULUS to use random_variable *)
let CHAR_FN_SUM_IID_MODULUS_RV = prove
 (`!p:A prob_space (X:num->A->real) n t.
     (!i. random_variable p (X i)) /\
     (!i t. char_fn_re p (X i) t = char_fn_re p (X 0) t /\
            char_fn_im p (X i) t = char_fn_im p (X 0) t) /\
     (!k. k < n ==> indep_rv p (\x. sum(0..k) (\i. X i x)) (X (SUC k)))
     ==> char_fn_re p (\x. sum(0..n) (\i. X i x)) t pow 2 +
         char_fn_im p (\x. sum(0..n) (\i. X i x)) t pow 2 =
         (char_fn_re p (X 0) t pow 2 +
          char_fn_im p (X 0) t pow 2) pow (SUC n)`,
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
     CHAR_FN_ADD_INDEP_RE) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   BETA_TAC THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `\x:A. sum(0..n) (\i. (X:num->A->real) i x)`;
     `(X:num->A->real) (SUC n)`; `t:real`]
     CHAR_FN_ADD_INDEP_IM) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   BETA_TAC THEN DISCH_TAC THEN
   ABBREV_TAC `R = char_fn_re (p:A prob_space)
     (\x:A. sum(0..n) (\i. (X:num->A->real) i x)) t` THEN
   ABBREV_TAC `S' = char_fn_im (p:A prob_space)
     (\x:A. sum(0..n) (\i. (X:num->A->real) i x)) t` THEN
   ABBREV_TAC `r = char_fn_re (p:A prob_space) ((X:num->A->real) 0) t` THEN
   ABBREV_TAC `s = char_fn_im (p:A prob_space) ((X:num->A->real) 0) t` THEN
   SUBGOAL_THEN `char_fn_re (p:A prob_space) ((X:num->A->real) (SUC n)) t = r /\
                 char_fn_im p (X (SUC n)) t = s` STRIP_ASSUME_TAC THENL
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

(* Modulus bound: |phi(t)|^2 <= 1 for char_fn with random_variable *)
(* Proof via Jensen: 1 - E[cos]^2 - E[sin]^2 = E[(cos-c)^2+(sin-s)^2] >= 0 *)
let CHAR_FN_MODULUS_LE = prove
 (`!p:A prob_space (X:A->real) t.
     random_variable p X
     ==> char_fn_re p X t pow 2 + char_fn_im p X t pow 2 <= &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[char_fn_re; char_fn_im] THEN
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

(* Im(sum)^2 bound for char_fn with random_variable *)
let CHAR_FN_SUM_IID_IM_SQ_BOUND = prove
 (`!p:A prob_space (X:num->A->real) n t.
     (!i. random_variable p (X i)) /\
     (!i t. char_fn_re p (X i) t = char_fn_re p (X 0) t /\
            char_fn_im p (X i) t = char_fn_im p (X 0) t) /\
     (!k. k < n ==> indep_rv p (\x. sum(0..k) (\i. X i x)) (X (SUC k)))
     ==> char_fn_im p (\x. sum(0..n) (\i. X i x)) t pow 2
         <= &3 * (&(SUC n) * abs(char_fn_im p (X 0) t))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `r = char_fn_re (p:A prob_space) ((X:num->A->real) 0) t` THEN
  ABBREV_TAC `s = char_fn_im (p:A prob_space) ((X:num->A->real) 0) t` THEN
  ABBREV_TAC `R = char_fn_re (p:A prob_space)
    (\x:A. sum(0..n) (\i. (X:num->A->real) i x)) t` THEN
  ABBREV_TAC `S' = char_fn_im (p:A prob_space)
    (\x:A. sum(0..n) (\i. (X:num->A->real) i x)) t` THEN
  (* Step 1: R^2+S'^2 = (r^2+s^2)^(n+1) *)
  MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`; `n:num`; `t:real`]
    CHAR_FN_SUM_IID_MODULUS_RV) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* Step 2: |R-r^(n+1)| <= (n+1)|s| *)
  MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`; `n:num`; `t:real`]
    CHAR_FN_SUM_IID_RE_BOUND) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* Step 3: r^2+s^2 <= 1 *)
  SUBGOAL_THEN `r pow 2 + s pow 2 <= &1` ASSUME_TAC THENL
  [EXPAND_TAC "r" THEN EXPAND_TAC "s" THEN
   MATCH_MP_TAC CHAR_FN_MODULUS_LE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 4: |s| <= 1 *)
  SUBGOAL_THEN `abs s <= &1` ASSUME_TAC THENL
  [ASM_MESON_TAC[CHAR_FN_IM_BOUND]; ALL_TAC] THEN
  (* Step 5: |r| <= 1 *)
  SUBGOAL_THEN `abs r <= &1` ASSUME_TAC THENL
  [ASM_MESON_TAC[CHAR_FN_RE_BOUND]; ALL_TAC] THEN
  (* Step 5b: |r^(n+1)| <= 1 *)
  SUBGOAL_THEN `abs(r pow (SUC n)) <= &1` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_ABS_POW] THEN MATCH_MP_TAC REAL_POW_1_LE THEN
   ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  (* Step 6: |R| <= 1 *)
  SUBGOAL_THEN `abs R <= &1` ASSUME_TAC THENL
  [EXPAND_TAC "R" THEN MATCH_MP_TAC CHAR_FN_RE_BOUND THEN
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

(* CLT: Imaginary part of char_fn of standardized sum --> 0 *)
let CLT_CHAR_FN_IM_CONVERGENCE = prove
 (`!p:A prob_space (X:num->A->real) t.
     (!n. integrable p (X n)) /\
     (!n. integrable p (\x. X n x pow 2)) /\
     (!i. expectation p (X i) = &0) /\
     &0 < expectation p (\x. X 0 x pow 2) /\
     (!i. expectation p (\x. X i x pow 2) = expectation p (\x. X 0 x pow 2)) /\
     (!i t. char_fn_re p (X i) t = char_fn_re p (X 0) t /\
            char_fn_im p (X i) t = char_fn_im p (X 0) t) /\
     (!n k. k < n ==> indep_rv p (\x. sum(0..k) (\i. X i x)) (X (SUC k)))
     ==> ((\n. char_fn_im p (\x. sum(0..n) (\i. X i x))
                             (t / sqrt(&(SUC n))))
          ---> &0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i:num. random_variable (p:A prob_space)
    ((X:num->A->real) i)` ASSUME_TAC THENL
  [ASM_MESON_TAC[integrable]; ALL_TAC] THEN
  ABBREV_TAC `I_n = \n:num. char_fn_im (p:A prob_space)
    (\x:A. sum(0..n) (\i. (X:num->A->real) i x)) (t / sqrt(&(SUC n)))` THEN
  (* Use: Im^2 <= 3*(n+1)*|Im(X_0, s)| where s = t/sqrt(n+1) *)
  ABBREV_TAC `C_n = \n:num. &3 * (&(SUC n) *
    abs(char_fn_im (p:A prob_space) ((X:num->A->real) 0)
      (t / sqrt(&(SUC n)))))` THEN
  (* Step 1: I_n^2 <= C_n *)
  SUBGOAL_THEN `!n:num. (I_n:num->real) n pow 2 <= C_n n` ASSUME_TAC THENL
  [X_GEN_TAC `n:num` THEN EXPAND_TAC "I_n" THEN EXPAND_TAC "C_n" THEN
   BETA_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`; `n:num`;
     `t / sqrt(&(SUC n))`] CHAR_FN_SUM_IID_IM_SQ_BOUND) THEN
   ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]]; ALL_TAC] THEN
  (* Step 2: C_n --> 0 since (n+1)*|Im(X_0, t/sqrt(n+1))| --> 0 *)
  SUBGOAL_THEN `((C_n:num->real) ---> &0) sequentially` ASSUME_TAC THENL
  [EXPAND_TAC "C_n" THEN BETA_TAC THEN
   SUBGOAL_THEN `&0 = &3 * &0` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REALLIM_LMUL THEN
   MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) 0`; `t:real`]
     CLT_IM_ERROR_VANISHES) THEN
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
(* Generalizes SIMPLE_WEAK_CONVERGENCE_FROM_CHAR_FN and supporting lemmas          *)
(* from simple_rv to integrable (random_variable) setting.                   *)
(* ========================================================================= *)

(* TRIG_POLY_WEAK_CONVERGENCE:
   If char_fn_re/im of integrable X_n converge to normal limits,
   then expectation of trig polynomials converges.
   Analogous to SIMPLE_TRIG_POLY_WEAK_CONVERGENCE for simple_rv. *)
let TRIG_POLY_WEAK_CONVERGENCE = prove
 (`!p:A prob_space (X:num->A->real) m (a:num->real) (b:num->real) (freq:num->real).
     (!n. random_variable p (X n)) /\
     (!t. ((\n. char_fn_re p (X n) t) ---> exp(--(t pow 2 / &2)))
          sequentially) /\
     (!t. ((\n. char_fn_im p (X n) t) ---> &0) sequentially)
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
     sum(0..m) (\k. a k * char_fn_re p (X n) (freq k) +
                     b k * char_fn_im p (X n) (freq k))`
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
   REWRITE_TAC[char_fn_re; char_fn_im];
   ALL_TAC] THEN
  (* Step 2: Apply limit decomposition *)
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\n:num. sum(0..m) (\k. (a:num->real) k * char_fn_re (p:A prob_space) ((X:num->A->real) n) ((freq:num->real) k) +
                                       (b:num->real) k * char_fn_im p (X n) (freq k))` THEN
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

(* STEP_C_BOUND:
   For integrable X_n with bounded second moments, bound the difference
   |E[g(X_n)] - E[T(X_n)]| where g,T are bounded functions.
   Analogous to SIMPLE_STEP_C_BOUND for simple_rv. *)
let STEP_C_BOUND = prove
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

(* WEAK_CONVERGENCE_FROM_CHAR_FN:
   If char_fn of integrable X_n converges to normal limits,
   then for any bounded continuous g,
   E[g(X_n)] -> integral(g * normal_density).
   Analogous to SIMPLE_WEAK_CONVERGENCE_FROM_CHAR_FN for simple_rv. *)
let WEAK_CONVERGENCE_FROM_CHAR_FN = prove
 (`!p:A prob_space (X:num->A->real) (g:real->real).
     (!n. random_variable p (X n)) /\
     (!n. integrable p (X n)) /\
     (!n. integrable p (\x. X n x pow 2)) /\
     (?C. &0 < C /\ !n. expectation p (\x. X n x pow 2) <= C) /\
     (!t. ((\n. char_fn_re p (X n) t) ---> exp(--(t pow 2 / &2)))
          sequentially) /\
     (!t. ((\n. char_fn_im p (X n) t) ---> &0) sequentially) /\
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
   MATCH_MP_TAC TRIG_POLY_WEAK_CONVERGENCE THEN ASM_REWRITE_TAC[];
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
      `BB:real`; `CC:real`; `e:real`; `M:real`] STEP_C_BOUND) THEN
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

(* CHAR_FN_DETERMINES_NORMAL_CDF_LIMIT:
   If char_fn converges to normal and cdf converges to l,
   then l = std_normal_cdf x. Uses sandwich argument with
   piecewise linear test functions and WEAK_CONVERGENCE_FROM_CHAR_FN. *)
let CHAR_FN_DETERMINES_NORMAL_CDF_LIMIT = prove
 (`!p:A prob_space (X:num->A->real) x l.
     (!n. random_variable p (X n)) /\
     (!n. integrable p (X n)) /\
     (!n. integrable p (\x. X n x pow 2)) /\
     (?C. &0 < C /\ !n. expectation p (\x. X n x pow 2) <= C) /\
     (!t. ((\n. char_fn_re p (X n) t) ---> exp(--(t pow 2 / &2)))
          sequentially) /\
     (!t. ((\n. char_fn_im p (X n) t) ---> &0) sequentially) /\
     ((\n. cdf p (X n) x) ---> l) sequentially
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
      `\n:num. cdf (p:A prob_space) ((X:num->A->real) n) x`;
      `real_integral (:real)
        (\y:real. (g_low:real->real) y * std_normal_density y)`;
      `l:real`]
     REALLIM_LE) THEN
   BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    CONJ_TAC THENL
    [(* E[g_low(X_n)] -> integral(g_low * density) *)
     MATCH_MP_TAC WEAK_CONVERGENCE_FROM_CHAR_FN THEN
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
    (* eventually(E[g_low(X_n)] <= cdf(X_n, x)) *)
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC EXPECTATION_LE_CDF THEN ASM_REWRITE_TAC[] THEN
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
     `\n:num. cdf (p:A prob_space) ((X:num->A->real) n) x`;
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
    MATCH_MP_TAC WEAK_CONVERGENCE_FROM_CHAR_FN THEN
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
   (* eventually(cdf(X_n,x) <= E[g_high(X_n)]) *)
   REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
   X_GEN_TAC `n:num` THEN DISCH_TAC THEN BETA_TAC THEN
   MATCH_MP_TAC CDF_LE_EXPECTATION THEN ASM_REWRITE_TAC[] THEN
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
    (!t. ((\n. char_fn_re p (X n) t) ---> exp(--(t pow 2 / &2)))
         sequentially) /\
    (!t. ((\n. char_fn_im p (X n) t) ---> &0) sequentially)
    ==> !x. ((\n. cdf p (X n) x) ---> std_normal_cdf x) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real` THEN
  REWRITE_TAC[CDF_SIMPLE_AGREE] THEN
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
   REWRITE_TAC[GSYM CDF_SIMPLE_AGREE] THEN
   MATCH_MP_TAC CDF_BOUNDS THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  X_GEN_TAC `r:num->num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL
    [`\k:num. simple_cdf (p:A prob_space) ((X:num->A->real) ((r:num->num) k)) x`;
     `&1`] BOUNDED_REAL_SEQ_HAS_CONVERGENT_SUBSEQ) THEN
  BETA_TAC THEN ANTS_TAC THENL
  [GEN_TAC THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a <= &1 ==> abs a <= &1`) THEN
   REWRITE_TAC[GSYM CDF_SIMPLE_AGREE] THEN
   MATCH_MP_TAC CDF_BOUNDS THEN ASM_REWRITE_TAC[];
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
     CHAR_FN_DETERMINES_NORMAL_CDF_LIMIT) THEN
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
    [(* char_fn_re convergence along r o s *)
     X_GEN_TAC `t:real` THEN
     MP_TAC(ISPECL
       [`\n:num. char_fn_re (p:A prob_space) ((X:num->A->real) n) t`;
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
    [(* char_fn_im convergence along r o s *)
     X_GEN_TAC `t:real` THEN
     MP_TAC(ISPECL
       [`\n:num. char_fn_im (p:A prob_space) ((X:num->A->real) n) t`;
        `&0`;
        `\k:num. (r:num->num) ((s:num->num) k)`]
       REALLIM_SUBSEQUENCE) THEN
     BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
     ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN
     FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    ASM_REWRITE_TAC[CDF_SIMPLE_AGREE];
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
    (!i t. char_fn_re p (X i) t = char_fn_re p (X 0) t /\
           char_fn_im p (X i) t = char_fn_im p (X 0) t) /\
    (!n k. k < n ==> indep_rv p (\x. sum(0..k) (\i. X i x)) (X (SUC k)))
    ==> !x:real. ((\n. cdf p
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
  SUBGOAL_THEN `!n x:real. cdf (p:A prob_space) ((Y:num->A->real) n) x =
    cdf p (\a. sum(0..n) (\i. (X:num->A->real) i a) /
      (sqrt sigma2 * sqrt(&(SUC n)))) x` ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   EXPAND_TAC "Y" THEN REFL_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!x:real. ((\n. cdf (p:A prob_space) ((Y:num->A->real) n) x) --->
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
    [MATCH_MP_TAC SQRT_POW_2 THEN ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
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
   (* char_fn_re convergence *)
   X_GEN_TAC `t:real` THEN EXPAND_TAC "Y" THEN BETA_TAC THEN
   REWRITE_TAC[CHAR_FN_RE_DIV] THEN
   (* char_fn_re p (\x. sum(...)) (t/(sigma*sqrt(n+1))) *)
   (* = char_fn_re p (\x. sum(...)) ((t/sigma)/sqrt(n+1)) *)
   SUBGOAL_THEN `!n:num. char_fn_re (p:A prob_space)
     (\x:A. sum(0..n) (\i. (X:num->A->real) i x))
     (t / (sqrt sigma2 * sqrt (&(SUC n)))) =
     char_fn_re p (\x. sum(0..n) (\i. X i x))
     (t / sqrt sigma2 / sqrt (&(SUC n)))` ASSUME_TAC THENL
   [GEN_TAC THEN AP_TERM_TAC THEN CONV_TAC REAL_FIELD;
    ASM_REWRITE_TAC[]] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`; `t / sqrt sigma2`]
     CLT_CHAR_FN_CONVERGENCE) THEN
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
    [MATCH_MP_TAC SQRT_POW_2 THEN ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `~(sigma2 = &0)` MP_TAC THENL
    [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
   ASM_REWRITE_TAC[];
   (* char_fn_im convergence *)
   X_GEN_TAC `t:real` THEN EXPAND_TAC "Y" THEN BETA_TAC THEN
   REWRITE_TAC[CHAR_FN_IM_DIV] THEN
   SUBGOAL_THEN `!n:num. char_fn_im (p:A prob_space)
     (\x:A. sum(0..n) (\i. (X:num->A->real) i x))
     (t / (sqrt sigma2 * sqrt (&(SUC n)))) =
     char_fn_im p (\x. sum(0..n) (\i. X i x))
     (t / sqrt sigma2 / sqrt (&(SUC n)))` ASSUME_TAC THENL
   [GEN_TAC THEN AP_TERM_TAC THEN CONV_TAC REAL_FIELD;
    ASM_REWRITE_TAC[]] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`; `t / sqrt sigma2`]
     CLT_CHAR_FN_IM_CONVERGENCE) THEN
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

(* ================================================================== *)
(* Kolmogorov Strong Law of Large Numbers                             *)
(* Removes nonnegativity assumption from NONNEG_SLLN via X = X+ - X- *)
(* ================================================================== *)



(* Negation preserves pairwise independence *)
let INDEP_RV_NEG = prove
 (`!p:A prob_space X Y.
    indep_rv p X Y ==> indep_rv p (\x. --(X x)) (\x. --(Y x))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP INDEP_RV_IMP_RV) THEN
  REWRITE_TAC[indep_rv] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_NEG THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RANDOM_VARIABLE_NEG THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  (* {-X <= a} = {X >= -a}, convert to complements of strict ineq sets *)
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ --(X x) <= a /\ --(Y x) <= b} =
    prob_carrier p DIFF
    ({x | x IN prob_carrier p /\ X x < --a} UNION
     {x | x IN prob_carrier p /\ Y x < --b})`
    SUBST1_TAC THENL
   [SET_TAC[REAL_ARITH
      `!x a:real. --x <= a <=> ~(x < --a)`]; ALL_TAC] THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ --(X x) <= a} =
    prob_carrier p DIFF {x | x IN prob_carrier p /\ X x < --a}`
    SUBST1_TAC THENL
   [SET_TAC[REAL_ARITH `!x a:real. --x <= a <=> ~(x < --a)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ --(Y x) <= b} =
    prob_carrier p DIFF {x | x IN prob_carrier p /\ Y x < --b}`
    SUBST1_TAC THENL
   [SET_TAC[REAL_ARITH `!x b:real. --x <= b <=> ~(x < --b)`];
    ALL_TAC] THEN
  (* Get strict inequality independence *)
  MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `Y:A->real`]
    INDEP_RV_STRICT_INEQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `pXa = prob (p:A prob_space)
    {x:A | x IN prob_carrier p /\ X x < --a}` THEN
  ABBREV_TAC `pYb = prob (p:A prob_space)
    {x:A | x IN prob_carrier p /\ Y x < --b}` THEN
  (* Events membership for strict inequality sets *)
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ X x < --a} IN prob_events p`
    ASSUME_TAC THENL
   [MATCH_MP_TAC RV_PREIMAGE_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ Y x < --b} IN prob_events p`
    ASSUME_TAC THENL
   [MATCH_MP_TAC RV_PREIMAGE_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* Use PROB_COMPL and PROB_UNION *)
  SUBGOAL_THEN `prob (p:A prob_space) (prob_carrier p DIFF
    ({x:A | x IN prob_carrier p /\ X x < --a} UNION
     {x | x IN prob_carrier p /\ Y x < --b})) =
    &1 - prob p ({x | x IN prob_carrier p /\ X x < --a} UNION
                 {x | x IN prob_carrier p /\ Y x < --b})` SUBST1_TAC THENL
   [MATCH_MP_TAC PROB_COMPL THEN
    MATCH_MP_TAC PROB_UNION_IN_EVENTS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `prob (p:A prob_space) (prob_carrier p DIFF
    {x:A | x IN prob_carrier p /\ X x < --a}) = &1 - pXa` SUBST1_TAC THENL
   [EXPAND_TAC "pXa" THEN MATCH_MP_TAC PROB_COMPL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `prob (p:A prob_space) (prob_carrier p DIFF
    {x:A | x IN prob_carrier p /\ Y x < --b}) = &1 - pYb` SUBST1_TAC THENL
   [EXPAND_TAC "pYb" THEN MATCH_MP_TAC PROB_COMPL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* Inclusion-exclusion for the union *)
  SUBGOAL_THEN `prob (p:A prob_space)
    ({x:A | x IN prob_carrier p /\ X x < --a} UNION
     {x | x IN prob_carrier p /\ Y x < --b}) =
    pXa + pYb - prob p ({x | x IN prob_carrier p /\ X x < --a} INTER
                        {x | x IN prob_carrier p /\ Y x < --b})` SUBST1_TAC THENL
   [EXPAND_TAC "pXa" THEN EXPAND_TAC "pYb" THEN
    MATCH_MP_TAC PROB_UNION THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* Simplify the intersection *)
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ X x < --a} INTER
    {x | x IN prob_carrier p /\ Y x < --b} =
    {x | x IN prob_carrier p /\ X x < --a /\ Y x < --b}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* Apply strict inequality independence *)
  FIRST_X_ASSUM(MP_TAC o SPECL [`--a:real`; `--b:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB; REAL_SUB_RDISTRIB;
              REAL_MUL_LID; REAL_MUL_RID] THEN
  REAL_ARITH_TAC);;

(* Integrability of max(f, 0)^2 given integrability of f and f^2 *)
let INTEGRABLE_MAX_ZERO_POW2 = prove
 (`!p:A prob_space f.
    integrable p f /\ integrable p (\x. f x pow 2)
    ==> integrable p (\x. max (f x) (&0) pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC INTEGRABLE_DOMINATED THEN
  EXISTS_TAC `\x:A. (f:A->real) x pow 2` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
    MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[ETA_AX];
      REWRITE_TAC[RANDOM_VARIABLE_CONST]];
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_ABS_POW] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN
  REWRITE_TAC[ARITH; REAL_ABS_POS] THEN
  REWRITE_TAC[real_max] THEN
  COND_CASES_TAC THEN REAL_ARITH_TAC);;

(* Variance of max(f, 0) bounded by E[f^2] *)
let VARIANCE_MAX_ZERO_BOUND = prove
 (`!p:A prob_space f.
    integrable p f /\ integrable p (\x. f x pow 2)
    ==> variance p (\x. max (f x) (&0)) <= expectation p (\x. f x pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `expectation (p:A prob_space)
    (\x:A. max ((f:A->real) x) (&0) pow 2)` THEN
  CONJ_TAC THENL
   [(* variance(g) = E[g^2] - (Eg)^2 <= E[g^2] *)
    SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. max ((f:A->real) x) (&0))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_MAX THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[ETA_AX]; REWRITE_TAC[INTEGRABLE_CONST]];
      ALL_TAC] THEN
    SUBGOAL_THEN `integrable (p:A prob_space)
      (\x:A. max ((f:A->real) x) (&0) pow 2)` ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_MAX_ZERO_POW2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`p:A prob_space`; `\x:A. max ((f:A->real) x) (&0)`]
      VARIANCE_ALT) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_ARITH `a - b <= a <=> &0 <= b`; REAL_LE_POW_2];
    (* E[max(f,0)^2] <= E[f^2] by pointwise bound *)
    MATCH_MP_TAC EXPECTATION_MONO THEN REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_MAX_ZERO_POW2 THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[ETA_AX];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      REWRITE_TAC[real_max] THEN COND_CASES_TAC THENL
       [REWRITE_TAC[REAL_POW_ZERO; ARITH; REAL_LE_POW_2];
        REWRITE_TAC[REAL_LE_REFL]]]]);;

(* Variance is invariant under negation *)
let VARIANCE_NEG = prove
 (`!p:A prob_space f. random_variable p f ==>
    variance p (\x. --(f x)) = variance p f`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[variance] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (\x. --((f:A->real) x)) =
    --expectation p f` SUBST1_TAC THENL
   [MATCH_MP_TAC EXPECTATION_NEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  REWRITE_TAC[REAL_NEG_SUB] THEN
  SUBGOAL_THEN `(expectation (p:A prob_space) (f:A->real) - f x) pow 2 =
    (f x - expectation p f) pow 2`
    (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

(* Summable variance transfer: Var(X_n)/(n+1)^2 summable implies
   Var(max(X_n, 0))/(n+1)^2 summable *)
let SUMMABLE_VARIANCE_MAX_ZERO = prove
 (`!p:A prob_space (X:num->A->real) mu.
    (!n. integrable p (X n)) /\
    (!n. integrable p (\x. X n x pow 2)) /\
    (!n. expectation p (X n) = mu) /\
    real_summable (from 0) (\n. variance p (X n) / &(SUC n) pow 2)
    ==> real_summable (from 0)
          (\n. variance p (\x. max (X n x) (&0)) / &(SUC n) pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
  EXISTS_TAC `\n:num. (variance (p:A prob_space) ((X:num->A->real) n) +
    mu pow 2) / &(SUC n) pow 2` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
      `variance (p:A prob_space) (\x. max ((X:num->A->real) n x) (&0)) <=
       variance p (X n) + mu pow 2` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) n`]
        VARIANCE_MAX_ZERO_BOUND) THEN
      ANTS_TAC THENL
       [CONJ_TAC THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) n`] VARIANCE_ALT) THEN
      ANTS_TAC THENL
       [CONJ_TAC THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      ASM_REWRITE_TAC[ETA_AX] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= variance (p:A prob_space)
      (\x. max ((X:num->A->real) n x) (&0))` ASSUME_TAC THENL
     [MATCH_MP_TAC VARIANCE_NONNEG THEN
      SUBGOAL_THEN `integrable (p:A prob_space)
        (\x. max ((X:num->A->real) n x) (&0))` ASSUME_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_MAX THEN
        CONJ_TAC THENL
         [REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[INTEGRABLE_CONST]]; ALL_TAC] THEN
      SUBGOAL_THEN `integrable (p:A prob_space)
        (\x. max ((X:num->A->real) n x) (&0) pow 2)` ASSUME_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_MAX_ZERO_POW2 THEN
        CONJ_TAC THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[BETA_THM] THEN
      ABBREV_TAC `c = expectation (p:A prob_space)
        (\x:A. max ((X:num->A->real) n x) (&0))` THEN
      SUBGOAL_THEN `(\x:A. (max ((X:num->A->real) n x) (&0) - c) pow 2) =
        (\x. (max (X n x) (&0) pow 2 - &2 * c * max (X n x) (&0)) + c pow 2)`
        SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
        MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
         [MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
           [ASM_REWRITE_TAC[];
            MATCH_MP_TAC INTEGRABLE_CMUL THEN
            MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]];
          REWRITE_TAC[INTEGRABLE_CONST]]]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &(SUC n) pow 2` ASSUME_TAC THENL
     [SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; LT_0]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= variance (p:A prob_space)
      (\x. max ((X:num->A->real) n x) (&0)) / &(SUC n) pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    ASM_MESON_TAC[REAL_ABS_REFL; REAL_LE_DIV2_EQ]] THEN
  REWRITE_TAC[real_div; REAL_ADD_RDISTRIB] THEN
  MATCH_MP_TAC REAL_SUMMABLE_ADD THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[GSYM real_div]; ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_SUMMABLE_LMUL THEN
  MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
  EXISTS_TAC `\n:num. inv(&n pow 2)` THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`0`; `2`] REAL_SUMMABLE_ZETA_INTEGER) THEN
    REWRITE_TAC[ARITH_RULE `2 <= 2 <=> T`];
    EXISTS_TAC `1` THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[GE; IN_FROM; LE_0] THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN
      REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN
      REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN ARITH_TAC]]);;

(* Kolmogorov Strong Law of Large Numbers: pairwise independent random
   variables with common mean, common positive-part mean, and summable
   variance/(n+1)^2 satisfy the SLLN. Generalizes NONNEG_SLLN by
   removing the nonnegativity assumption via X = X+ - X- decomposition. *)
let KOLMOGOROV_SLLN = prove
 (`!p:A prob_space (X:num->A->real) mu mu_plus.
    (!n. integrable p (X n)) /\
    (!n. integrable p (\x. X n x pow 2)) /\
    (!n. expectation p (X n) = mu) /\
    (!n. expectation p (\x. max (X n x) (&0)) = mu_plus) /\
    (!i j. ~(i = j) ==> indep_rv p (X i) (X j)) /\
    real_summable (from 0) (\n. variance p (X n) / &(SUC n) pow 2)
    ==> almost_surely p
          {x | ((\n. inv(&(SUC n)) * sum(0..n) (\i. X i x)) ---> mu) sequentially}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Step 1: Apply NONNEG_SLLN to positive parts X^+ = max(X, 0) *)
  SUBGOAL_THEN
    `almost_surely (p:A prob_space)
      {x | ((\n. inv(&(SUC n)) * sum(0..n)
        (\i. max ((X:num->A->real) i x) (&0))) ---> mu_plus) sequentially}`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`;
      `\n (x:A). max ((X:num->A->real) n x) (&0)`;
      `mu_plus:real`] NONNEG_SLLN) THEN
   REWRITE_TAC[] THEN ANTS_TAC THENL
    [REPEAT CONJ_TAC THENL
      [(* integrable max(X n, 0) *)
       GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_MAX THEN
       CONJ_TAC THENL
        [REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
         REWRITE_TAC[INTEGRABLE_CONST]];
       (* integrable max(X n, 0)^2 *)
       GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_MAX_ZERO_POW2 THEN
       CONJ_TAC THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
       (* nonneg *)
       REPEAT GEN_TAC THEN DISCH_TAC THEN
       REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL];
       (* expectation = mu_plus *)
       ASM_REWRITE_TAC[];
       (* covariance max(X i, 0), max(X j, 0) = 0 *)
       REPEAT GEN_TAC THEN DISCH_TAC THEN
       MATCH_MP_TAC COVARIANCE_INDEP THEN REWRITE_TAC[BETA_THM] THEN
       REPEAT CONJ_TAC THENL
        [MATCH_MP_TAC INTEGRABLE_MAX THEN
         CONJ_TAC THENL
          [REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
           REWRITE_TAC[INTEGRABLE_CONST]];
         MATCH_MP_TAC INTEGRABLE_MAX THEN
         CONJ_TAC THENL
          [REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
           REWRITE_TAC[INTEGRABLE_CONST]];
         MATCH_MP_TAC INTEGRABLE_MUL_SQUARE THEN
         REPEAT CONJ_TAC THENL
          [MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
           MATCH_MP_TAC INTEGRABLE_MAX THEN
           CONJ_TAC THENL
            [REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
             REWRITE_TAC[INTEGRABLE_CONST]];
           MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
           MATCH_MP_TAC INTEGRABLE_MAX THEN
           CONJ_TAC THENL
            [REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
             REWRITE_TAC[INTEGRABLE_CONST]];
           MATCH_MP_TAC INTEGRABLE_MAX_ZERO_POW2 THEN
           CONJ_TAC THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
           MATCH_MP_TAC INTEGRABLE_MAX_ZERO_POW2 THEN
           CONJ_TAC THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]];
         MATCH_MP_TAC INDEP_RV_MAX_CONST THEN
         CONV_TAC(DEPTH_CONV ETA_CONV) THEN ASM_SIMP_TAC[]];
       (* summable variance *)
       MATCH_MP_TAC SUMMABLE_VARIANCE_MAX_ZERO THEN
       EXISTS_TAC `mu:real` THEN ASM_REWRITE_TAC[]];
     REWRITE_TAC[]]; ALL_TAC] THEN
  (* Step 2: Apply NONNEG_SLLN to negative parts X^- = max(-X, 0) *)
  SUBGOAL_THEN
    `almost_surely (p:A prob_space)
      {x | ((\n. inv(&(SUC n)) * sum(0..n)
        (\i. max (--((X:num->A->real) i x)) (&0))) ---> (mu_plus - mu)) sequentially}`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`;
      `\n (x:A). max (--((X:num->A->real) n x)) (&0)`;
      `mu_plus - mu:real`] NONNEG_SLLN) THEN
   REWRITE_TAC[] THEN ANTS_TAC THENL
    [REPEAT CONJ_TAC THENL
      [(* integrable max(-X n, 0) *)
       GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_MAX THEN
       CONJ_TAC THENL
        [MATCH_MP_TAC INTEGRABLE_NEG THEN
         REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
         REWRITE_TAC[INTEGRABLE_CONST]];
       (* integrable max(-X n, 0)^2 *)
       GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_MAX_ZERO_POW2 THEN
       CONJ_TAC THENL
        [MATCH_MP_TAC INTEGRABLE_NEG THEN
         REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
         SUBGOAL_THEN `(\x:A. --((X:num->A->real) n x) pow 2) =
           (\x. X n x pow 2)` SUBST1_TAC THENL
          [REWRITE_TAC[FUN_EQ_THM; REAL_POW_NEG; ARITH] THEN REAL_ARITH_TAC;
           REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]]];
       (* nonneg *)
       REPEAT GEN_TAC THEN DISCH_TAC THEN
       REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL];
       (* E[max(-X n, 0)] = mu_plus - mu *)
       GEN_TAC THEN
       SUBGOAL_THEN `(\x:A. max (--((X:num->A->real) n x)) (&0)) =
         (\x. max (X n x) (&0) - X n x)` SUBST1_TAC THENL
        [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
         REWRITE_TAC[real_max] THEN
         COND_CASES_TAC THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
         ALL_TAC] THEN
       SUBGOAL_THEN `expectation (p:A prob_space)
         (\x. max ((X:num->A->real) n x) (&0) - X n x) =
         expectation p (\x. max (X n x) (&0)) - expectation p (X n)`
         SUBST1_TAC THENL
        [MATCH_MP_TAC EXPECTATION_SUB THEN
         CONJ_TAC THENL
          [MATCH_MP_TAC INTEGRABLE_MAX THEN
           CONJ_TAC THENL
            [REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
             REWRITE_TAC[INTEGRABLE_CONST]];
           REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]];
         ASM_REWRITE_TAC[]];
       (* covariance max(-X i, 0), max(-X j, 0) = 0 *)
       REPEAT GEN_TAC THEN DISCH_TAC THEN
       MATCH_MP_TAC COVARIANCE_INDEP THEN REWRITE_TAC[BETA_THM] THEN
       REPEAT CONJ_TAC THENL
        [MATCH_MP_TAC INTEGRABLE_MAX THEN
         CONJ_TAC THENL
          [MATCH_MP_TAC INTEGRABLE_NEG THEN
           REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
           REWRITE_TAC[INTEGRABLE_CONST]];
         MATCH_MP_TAC INTEGRABLE_MAX THEN
         CONJ_TAC THENL
          [MATCH_MP_TAC INTEGRABLE_NEG THEN
           REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
           REWRITE_TAC[INTEGRABLE_CONST]];
         MATCH_MP_TAC INTEGRABLE_MUL_SQUARE THEN
         REPEAT CONJ_TAC THENL
          [MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
           MATCH_MP_TAC INTEGRABLE_MAX THEN
           CONJ_TAC THENL
            [MATCH_MP_TAC INTEGRABLE_NEG THEN
             REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
             REWRITE_TAC[INTEGRABLE_CONST]];
           MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
           MATCH_MP_TAC INTEGRABLE_MAX THEN
           CONJ_TAC THENL
            [MATCH_MP_TAC INTEGRABLE_NEG THEN
             REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
             REWRITE_TAC[INTEGRABLE_CONST]];
           MATCH_MP_TAC INTEGRABLE_MAX_ZERO_POW2 THEN
           CONJ_TAC THENL
            [MATCH_MP_TAC INTEGRABLE_NEG THEN
             REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
             SUBGOAL_THEN `(\x:A. --((X:num->A->real) i x) pow 2) =
               (\x. X i x pow 2)` SUBST1_TAC THENL
              [REWRITE_TAC[FUN_EQ_THM; REAL_POW_NEG; ARITH] THEN
               REAL_ARITH_TAC;
               REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]]];
           MATCH_MP_TAC INTEGRABLE_MAX_ZERO_POW2 THEN
           CONJ_TAC THENL
            [MATCH_MP_TAC INTEGRABLE_NEG THEN
             REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
             SUBGOAL_THEN `(\x:A. --((X:num->A->real) j x) pow 2) =
               (\x. X j x pow 2)` SUBST1_TAC THENL
              [REWRITE_TAC[FUN_EQ_THM; REAL_POW_NEG; ARITH] THEN
               REAL_ARITH_TAC;
               REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]]]];
         MATCH_MP_TAC INDEP_RV_MAX_CONST THEN
         MATCH_MP_TAC INDEP_RV_NEG THEN
         CONV_TAC(DEPTH_CONV ETA_CONV) THEN ASM_SIMP_TAC[]];
       (* summable Var(max(-X n, 0))/(n+1)^2 *)
       MP_TAC(ISPECL [`p:A prob_space`;
         `\n (x:A). --((X:num->A->real) n x)`; `--mu:real`]
         SUMMABLE_VARIANCE_MAX_ZERO) THEN
       REWRITE_TAC[] THEN ANTS_TAC THENL
        [REPEAT CONJ_TAC THENL
          [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_NEG THEN
           REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
           GEN_TAC THEN
           SUBGOAL_THEN `(\x:A. --((X:num->A->real) n x) pow 2) =
             (\x. X n x pow 2)` SUBST1_TAC THENL
            [REWRITE_TAC[FUN_EQ_THM; REAL_POW_NEG; ARITH] THEN
             REAL_ARITH_TAC;
             REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]];
           GEN_TAC THEN
           SUBGOAL_THEN `expectation (p:A prob_space)
             (\x. --((X:num->A->real) n x)) = --(expectation p (X n))`
             SUBST1_TAC THENL
            [MATCH_MP_TAC EXPECTATION_NEG THEN
             MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
             REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
             ASM_REWRITE_TAC[]];
           SUBGOAL_THEN `(\n. variance (p:A prob_space)
             (\x. --((X:num->A->real) n x)) / &(SUC n) pow 2) =
             (\n. variance p (X n) / &(SUC n) pow 2)` SUBST1_TAC THENL
            [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
             AP_THM_TAC THEN AP_TERM_TAC THEN
             MATCH_MP_TAC VARIANCE_NEG THEN
             MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
             REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
             ASM_REWRITE_TAC[]]];
         REWRITE_TAC[]]];
     REWRITE_TAC[]]; ALL_TAC] THEN
  (* Step 3: Combine via X = X+ - X- and limit subtraction *)
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC `{x:A | ((\n. inv(&(SUC n)) * sum(0..n)
    (\i. max ((X:num->A->real) i x) (&0))) ---> mu_plus) sequentially} INTER
    {x | ((\n. inv(&(SUC n)) * sum(0..n)
    (\i. max (--(X i x)) (&0))) ---> (mu_plus - mu)) sequentially}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ALMOST_SURELY_INTER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
  (* Establish: sum(X i x) = sum(max(X i x, 0)) - sum(max(-X i x, 0)) *)
  SUBGOAL_THEN
    `!n:num. sum(0..n) (\i. (X:num->A->real) i (x:A)) =
      sum(0..n) (\i. max (X i x) (&0)) -
      sum(0..n) (\i. max (--(X i x)) (&0))`
    ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[real_max] THEN
    COND_CASES_TAC THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
    `(\n:num. inv(&(SUC n)) * sum(0..n)
      (\i. (X:num->A->real) i (x:A))) =
     (\n. inv(&(SUC n)) * sum(0..n) (\i. max (X i x) (&0)) -
          inv(&(SUC n)) * sum(0..n) (\i. max (--(X i x)) (&0)))`
    SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; BETA_THM] THEN X_GEN_TAC `nn:num` THEN
    ASM_REWRITE_TAC[REAL_SUB_LDISTRIB]; ALL_TAC] THEN
  SUBGOAL_THEN `mu:real = mu_plus - (mu_plus - mu)` SUBST1_TAC THENL
   [REAL_ARITH_TAC;
    MATCH_MP_TAC REALLIM_SUB THEN ASM_REWRITE_TAC[]]);;

(* KOLMOGOROV_SLLN without explicit mu_plus parameter *)
let KOLMOGOROV_SLLN' = prove
 (`!p:A prob_space (X:num->A->real) mu.
    (!n. integrable p (X n)) /\
    (!n. integrable p (\x. X n x pow 2)) /\
    (!n. expectation p (X n) = mu) /\
    (!n. expectation p (\x. max (X n x) (&0)) =
         expectation p (\x. max (X 0 x) (&0))) /\
    (!i j. ~(i = j) ==> indep_rv p (X i) (X j)) /\
    real_summable (from 0) (\n. variance p (X n) / &(SUC n) pow 2)
    ==> almost_surely p
          {x | ((\n. inv(&(SUC n)) * sum(0..n) (\i. X i x)) ---> mu)
               sequentially}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`; `mu:real`;
    `expectation (p:A prob_space) (\x. max ((X:num->A->real) 0 x) (&0))`]
    KOLMOGOROV_SLLN) THEN
  ASM_MESON_TAC[]);;

(* ===================================================================== *)
(* IID STRONG LAW OF LARGE NUMBERS (finite first moment only)            *)
(* ===================================================================== *)

(* Independence preserved under min with DIFFERENT constants *)
let INDEP_RV_MIN_DIFF_CONST = prove
 (`!p:A prob_space X Y c d.
    indep_rv p X Y
    ==> indep_rv p (\x. min (X x) c) (\x. min (Y x) d)`,
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
     min ((Y:A->real) x) d <= b} =
     {x | x IN prob_carrier p /\ min (Y x) d <= b}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   REWRITE_TAC[PROB_SPACE; REAL_MUL_LID];
   ALL_TAC] THEN
  ASM_CASES_TAC `d <= b` THENL
  [SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ min ((Y:A->real) x) d <= b} =
    prob_carrier p` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN] THEN GEN_TAC THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ min ((X:A->real) x) c <= a /\
     min ((Y:A->real) x) d <= b} =
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
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ min ((Y:A->real) x) d <= b} =
    {x | x IN prob_carrier p /\ Y x <= b}` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
   ASM_CASES_TAC `x:A IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ min ((X:A->real) x) c <= a /\
    min ((Y:A->real) x) d <= b} =
    {x | x IN prob_carrier p /\ X x <= a /\ Y x <= b}` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
   ASM_CASES_TAC `x:A IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

(* Equal CDFs imply equal tail probabilities *)
let EQUIDIST_TAIL_PROB_GT = prove
 (`!p:A prob_space X Y c.
    random_variable p X /\ random_variable p Y /\
    (!a. distribution_fn p X a = distribution_fn p Y a)
    ==> prob p {x | x IN prob_carrier p /\ X x > c} =
        prob p {x | x IN prob_carrier p /\ Y x > c}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ X x > c} =
     prob_carrier p DIFF {x | x IN prob_carrier p /\ X x <= c}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF] THEN
   GEN_TAC THEN ASM_CASES_TAC `x:A IN prob_carrier p` THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ Y x > c} =
     prob_carrier p DIFF {x | x IN prob_carrier p /\ Y x <= c}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF] THEN
   GEN_TAC THEN ASM_CASES_TAC `x:A IN prob_carrier p` THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ X x <= c} IN prob_events p /\
     {x:A | x IN prob_carrier p /\ Y x <= c} IN prob_events p`
    STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN FIRST_ASSUM(fun th ->
     ACCEPT_TAC(SPEC `c:real` (REWRITE_RULE[random_variable] th)));
   ALL_TAC] THEN
  ASM_SIMP_TAC[PROB_COMPL] THEN
  REWRITE_TAC[GSYM distribution_fn] THEN ASM_REWRITE_TAC[]);;

(* Riemann sum lower bound for min(x, c): pointwise real inequality *)
(* Proof: telescoping comparison with min(z, k*c/N) *)
let RIEMANN_LOWER_MIN = prove
 (`!z c N. &0 <= z /\ &0 < c /\ ~(N = 0) ==>
   sum(1..N) (\k. if z > &k * c / &N then c / &N else &0) <= min z c /\
   min z c <= sum(1..N) (\k. if z > &k * c / &N then c / &N else &0) + c / &N`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &N /\ ~(&N = &0)` STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c / &N` ASSUME_TAC THENL
  [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  SUBGOAL_THEN `1 <= N` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `0 <= N - 1` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  (* Shift index: sum(1..N)(f) = sum(0..N-1)(f(i+1)) *)
  SUBGOAL_THEN
    `sum(1..N) (\k. if z > &k * c / &N then c / &N else &0) =
     sum(0..N-1) (\i. if z > &(i + 1) * c / &N then c / &N else &0)`
    ASSUME_TAC THENL
  [ASM_SIMP_TAC[SUM_OFFSET_0] THEN
   MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[ADD_CLAUSES];
   ALL_TAC] THEN
  (* Helper: &(i+1)*c/N - &i*c/N = c/N *)
  SUBGOAL_THEN `!i:num. &(i + 1) * c / &N - &i * c / &N = c / &N`
    ASSUME_TAC THENL
  [GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
   REWRITE_TAC[REAL_ARITH `(&i + &1) * c / n - &i * c / n = c / n`];
   ALL_TAC] THEN
  (* Telescoping: sum(0..N-1)(min z ((k+1)*c/N) - min z (k*c/N)) = min z c *)
  SUBGOAL_THEN
    `sum(0..N-1) (\k. min z (&(k + 1) * c / &N) - min z (&k * c / &N)) =
     min z c`
    ASSUME_TAC THENL
  [MP_TAC(CONV_RULE(ONCE_DEPTH_CONV BETA_CONV)
    (INST [`\k:num. min z (&k * c / &N)`, `f:num->real`]
     (SPECL [`0`; `N - 1`] SUM_DIFFS_ALT))) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   SUBGOAL_THEN `N - 1 + 1 = N` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_MUL_LZERO; real_div; REAL_MUL_LZERO] THEN
   SUBGOAL_THEN `&N * c * inv(&N) = c` SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_FIELD `~(n = &0) ==> n * c * inv n = c`) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `min z (&0) = &0` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 <= z` THEN REAL_ARITH_TAC; ALL_TAC] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Telescoping for left endpoint *)
  SUBGOAL_THEN
    `sum(0..N-1) (\k. (if z > &(k + 1) * c / &N then c / &N else &0) -
                       (if z > &k * c / &N then c / &N else &0)) =
     (if z > &N * c / &N then c / &N else &0) -
     (if z > &0 * c / &N then c / &N else &0)`
    ASSUME_TAC THENL
  [MP_TAC(CONV_RULE(ONCE_DEPTH_CONV BETA_CONV)
    (INST [`\k:num. if z > &k * c / &N then c / &N else &0`, `f:num->real`]
     (SPECL [`0`; `N - 1`] SUM_DIFFS_ALT))) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   SUBGOAL_THEN `N - 1 + 1 = N` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   REFL_TAC;
   ALL_TAC] THEN
  (* sum(left) - sum(right) = left(0) - left(N) *)
  SUBGOAL_THEN
    `sum(0..N-1) (\i. if z > &i * c / &N then c / &N else &0) -
     sum(0..N-1) (\i. if z > &(i + 1) * c / &N then c / &N else &0) =
     (if z > &0 * c / &N then c / &N else &0) -
     (if z > &N * c / &N then c / &N else &0)`
    ASSUME_TAC THENL
  [REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN
   ONCE_REWRITE_TAC[REAL_ARITH `(a:real) - b = --(b - a)`] THEN
   REWRITE_TAC[SUM_NEG] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [
    (* === Lower bound: sum(0..N-1)(right) <= min z c === *)
    FIRST_X_ASSUM(fun tele ->
      GEN_REWRITE_TAC RAND_CONV [GSYM tele]) THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THENL
    [(* z > (i+1)*c/N: c/N <= min z ((i+1)*c/N) - min z (i*c/N) *)
     SUBGOAL_THEN `min z (&(i + 1) * c / &N) = &(i + 1) * c / &N`
       SUBST1_TAC THENL
     [UNDISCH_TAC `z > &(i + 1) * c / &N` THEN REAL_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `min z (&i * c / &N) = &i * c / &N`
       SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
      UNDISCH_TAC `z > &(i + 1) * c / &N` THEN
      UNDISCH_TAC `&0 < c / &N` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
     ASM_REWRITE_TAC[REAL_LE_REFL];
     (* ~(z > (i+1)*c/N): 0 <= min z ((i+1)*c/N) - min z (i*c/N) *)
     FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
     UNDISCH_TAC `~(z > &(i + 1) * c / &N)` THEN
     UNDISCH_TAC `&0 < c / &N` THEN REAL_ARITH_TAC
    ];
    (* === Upper bound: min z c <= sum(0..N-1)(right) + c/N === *)
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..N-1) (\i. if z > &i * c / &N then c / &N else &0)` THEN
    CONJ_TAC THENL
    [
      (* min z c <= left endpoint sum *)
      FIRST_X_ASSUM(fun tele ->
        GEN_REWRITE_TAC LAND_CONV [GSYM tele]) THEN
      MATCH_MP_TAC SUM_LE_NUMSEG THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THENL
      [(* z > i*c/N: diff <= c/N *)
       SUBGOAL_THEN `min z (&i * c / &N) = &i * c / &N`
         SUBST1_TAC THENL
       [UNDISCH_TAC `z > &i * c / &N` THEN REAL_ARITH_TAC; ALL_TAC] THEN
       SUBGOAL_THEN `min z (&(i + 1) * c / &N) <= &(i + 1) * c / &N`
         MP_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN REAL_ARITH_TAC;
       (* ~(z > i*c/N): diff <= 0 *)
       FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
       UNDISCH_TAC `~(z > &i * c / &N)` THEN
       UNDISCH_TAC `&0 < c / &N` THEN REAL_ARITH_TAC
      ];
      (* left endpoint sum <= right endpoint sum + c/N *)
      MATCH_MP_TAC(REAL_ARITH `s1 - s2 <= h ==> s1 <= s2 + h`) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_ARITH `&0 / x = &0`;
                   REAL_ARITH `z > &0 <=> &0 < z`] THEN
      REPEAT COND_CASES_TAC THEN
      UNDISCH_TAC `&0 < c / &N` THEN REAL_ARITH_TAC
    ]
  ]);;

(* E[if X > t then a else 0] = a * P(X > t) for random variable X *)
let EXPECTATION_IF_GT = prove
 (`!p:A prob_space (X:A->real) t a.
    random_variable p X /\ &0 <= a
    ==> integrable p (\x. if X x > t then a else &0) /\
        expectation p (\x. if X x > t then a else &0) =
        a * prob p {x | x IN prob_carrier p /\ X x > t}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ X x > t} IN prob_events p`
    ASSUME_TAC THENL
  [MATCH_MP_TAC RV_LEVEL_GT_IN_EVENTS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `integrable p (\x:A. a * indicator_fn {x | x IN prob_carrier p /\ X x > t} x)`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `a:real`;
     `indicator_fn {x:A | x IN prob_carrier p /\ X x > t}`] INTEGRABLE_CMUL) THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `!x:A. x IN prob_carrier p ==>
      (if X x > t then a else &0) =
      a * indicator_fn {x | x IN prob_carrier p /\ X x > t} x`
    ASSUME_TAC THENL
  [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
   ASM_REWRITE_TAC[] THEN
   COND_CASES_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `random_variable p (\x:A. if X x > t then a else &0)`
    ASSUME_TAC THENL
  [REWRITE_TAC[random_variable] THEN X_GEN_TAC `c:real` THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ (if X x > t then a else &0) <= c} =
      {x | x IN prob_carrier p /\
       a * indicator_fn {x | x IN prob_carrier p /\ X x > t} x <= c}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
    ASM_CASES_TAC `x:A IN prob_carrier p` THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[]; ALL_TAC] THEN
   MP_TAC(MATCH_MP INTEGRABLE_IMP_RANDOM_VARIABLE
     (ASSUME `integrable p
       (\x:A. a * indicator_fn {x | x IN prob_carrier p /\ X x > t} x)`)) THEN
   REWRITE_TAC[random_variable] THEN
   DISCH_THEN(fun th -> ACCEPT_TAC(SPEC `c:real` th)); ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (\x:A. if X x > t then a else &0)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `a:real` THEN
   ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   UNDISCH_TAC `&0 <= a` THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
    `expectation p (\x:A. if X x > t then a else &0) =
     expectation p (\x. a * indicator_fn {x | x IN prob_carrier p /\ X x > t} x)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_EXT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `a:real`;
    `indicator_fn {x:A | x IN prob_carrier p /\ X x > t}`] EXPECTATION_CMUL) THEN
  ANTS_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN
  MATCH_MP_TAC EXPECTATION_INDICATOR THEN ASM_REWRITE_TAC[]);;

(* Squeeze lemma: if |a - b| <= c/N for all N >= 1 then a = b *)
let REAL_EQ_SQUEEZE_DIV = prove
 (`!a b c. &0 < c /\ (!N. ~(N = 0) ==> abs(a - b) <= c / &N) ==> a = b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `(~(a:real = b) ==> F) ==> a = b`) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < abs(a - b:real)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `abs(a - b:real)` REAL_ARCH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `c:real`) THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
  [DISCH_TAC THEN UNDISCH_TAC `c < &n * abs(a - b:real)` THEN
   ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(a - b:real) * &n <= c` MP_TAC THENL
  [SUBGOAL_THEN `abs(a - b:real) <= c / &n <=> abs(a - b) * &n <= c`
     MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RDIV_EQ THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  UNDISCH_TAC `c < &n * abs(a - b:real)` THEN
  REWRITE_TAC[REAL_MUL_SYM] THEN REAL_ARITH_TAC);;

(* For equidistributed nonneg RVs, expectations of min-truncation are equal *)
(* Proof: Riemann sum squeeze -- both E[min(X,c)] and E[min(Y,c)] are within *)
(* c/N of E[sum(1..N)(if f > k*c/N then c/N else 0)], and the latter is the *)
(* same for X and Y by EQUIDIST_TAIL_PROB_GT. *)
let EQUIDIST_NONNEG_MIN_EXPECTATION = prove
 (`!p:A prob_space X Y c.
    random_variable p X /\ random_variable p Y /\
    (!x. x IN prob_carrier p ==> &0 <= X x) /\
    (!x. x IN prob_carrier p ==> &0 <= Y x) /\
    (!a. distribution_fn p X a = distribution_fn p Y a) /\
    &0 < c
    ==> expectation p (\x. min (X x) c) = expectation p (\x. min (Y x) c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_EQ_SQUEEZE_DIV THEN EXISTS_TAC `c:real` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  (* Integrability of min(X,c) *)
  SUBGOAL_THEN `integrable p (\x:A. min (X x) c)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `c:real` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
    ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o
      check (fun th -> free_in `X:A->real` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* Integrability of min(Y,c) *)
  SUBGOAL_THEN `integrable p (\x:A. min (Y x) c)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `c:real` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
    ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o
      check (fun th -> free_in `Y:A->real` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* Integrability of each Riemann sum term *)
  SUBGOAL_THEN
    `!k. integrable p (\x:A. if X x > &k * c / &N then c / &N else &0)`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `&k * c / &N`; `c / &N`]
     EXPECTATION_IF_GT) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; LE_1];
    SIMP_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN
    `!k. integrable p (\x:A. if Y x > &k * c / &N then c / &N else &0)`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `Y:A->real`; `&k * c / &N`; `c / &N`]
     EXPECTATION_IF_GT) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; LE_1];
    SIMP_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `1 <= N` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  (* Integrability of X Riemann sum *)
  SUBGOAL_THEN
    `integrable p
      (\x:A. sum(1..N) (\k. if X x > &k * c / &N then c / &N else &0))`
    ASSUME_TAC THENL
  [SUBGOAL_THEN
    `(\x:A. sum(1..N) (\k. if X x > &k * c / &N then c / &N else &0)) =
     (\x. sum(0..N-1)
       (\i. (\j x. if X x > &j * c / &N then c / &N else &0) (i+1) x))`
    SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:A` THEN
    ASM_SIMP_TAC[SUM_OFFSET_0] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[ADD_CLAUSES]; ALL_TAC] THEN
   MATCH_MP_TAC INTEGRABLE_SUM THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   REWRITE_TAC[] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Integrability of Y Riemann sum *)
  SUBGOAL_THEN
    `integrable p
      (\x:A. sum(1..N) (\k. if Y x > &k * c / &N then c / &N else &0))`
    ASSUME_TAC THENL
  [SUBGOAL_THEN
    `(\x:A. sum(1..N) (\k. if Y x > &k * c / &N then c / &N else &0)) =
     (\x. sum(0..N-1)
       (\i. (\j x. if Y x > &j * c / &N then c / &N else &0) (i+1) x))`
    SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:A` THEN
    ASM_SIMP_TAC[SUM_OFFSET_0] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[ADD_CLAUSES]; ALL_TAC] THEN
   MATCH_MP_TAC INTEGRABLE_SUM THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   REWRITE_TAC[] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Reduce to 5 subgoals via real arithmetic *)
  SUBGOAL_THEN
    `expectation p
      (\x:A. sum(1..N) (\k. if X x > &k * c / &N then c / &N else &0)) <=
     expectation p (\x. min (X x) c) /\
     expectation p (\x. min (X x) c) <=
     expectation p
      (\x:A. sum(1..N) (\k. if X x > &k * c / &N then c / &N else &0)) +
     c / &N /\
     expectation p
      (\x:A. sum(1..N) (\k. if Y x > &k * c / &N then c / &N else &0)) <=
     expectation p (\x. min (Y x) c) /\
     expectation p (\x. min (Y x) c) <=
     expectation p
      (\x:A. sum(1..N) (\k. if Y x > &k * c / &N then c / &N else &0)) +
     c / &N /\
     expectation p
      (\x:A. sum(1..N) (\k. if X x > &k * c / &N then c / &N else &0)) =
     expectation p
      (\x:A. sum(1..N) (\k. if Y x > &k * c / &N then c / &N else &0))`
    MP_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  (* Lower bound X: E[rsum_X] <= E[min(X,c)] via RIEMANN_LOWER_MIN *)
  CONJ_TAC THENL
  [MATCH_MP_TAC EXPECTATION_MONO THEN ASM_REWRITE_TAC[] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`(X:A->real) x`; `c:real`; `N:num`] RIEMANN_LOWER_MIN) THEN
   ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]]; ALL_TAC] THEN
  (* Upper bound X: E[min(X,c)] <= E[rsum_X] + c/N *)
  CONJ_TAC THENL
  [SUBGOAL_THEN
    `expectation p
      (\x:A. sum(1..N) (\k. if X x > &k * c / &N then c / &N else &0)) +
     c / &N =
     expectation p
      (\x. sum(1..N) (\k. if X x > &k * c / &N then c / &N else &0) +
           c / &N)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`p:A prob_space`;
      `\x:A. sum(1..N) (\k. if X x > &k * c / &N then c / &N else &0)`;
      `\x:A. c / &N`] EXPECTATION_ADD) THEN
    ASM_REWRITE_TAC[INTEGRABLE_CONST; EXPECTATION_CONST]; ALL_TAC] THEN
   MATCH_MP_TAC EXPECTATION_MONO THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[INTEGRABLE_CONST];
    ALL_TAC] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`(X:A->real) x`; `c:real`; `N:num`] RIEMANN_LOWER_MIN) THEN
   ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]]; ALL_TAC] THEN
  (* Lower bound Y *)
  CONJ_TAC THENL
  [MATCH_MP_TAC EXPECTATION_MONO THEN ASM_REWRITE_TAC[] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`(Y:A->real) x`; `c:real`; `N:num`] RIEMANN_LOWER_MIN) THEN
   ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]]; ALL_TAC] THEN
  (* Upper bound Y *)
  CONJ_TAC THENL
  [SUBGOAL_THEN
    `expectation p
      (\x:A. sum(1..N) (\k. if Y x > &k * c / &N then c / &N else &0)) +
     c / &N =
     expectation p
      (\x. sum(1..N) (\k. if Y x > &k * c / &N then c / &N else &0) +
           c / &N)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`p:A prob_space`;
      `\x:A. sum(1..N) (\k. if Y x > &k * c / &N then c / &N else &0)`;
      `\x:A. c / &N`] EXPECTATION_ADD) THEN
    ASM_REWRITE_TAC[INTEGRABLE_CONST; EXPECTATION_CONST]; ALL_TAC] THEN
   MATCH_MP_TAC EXPECTATION_MONO THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[INTEGRABLE_CONST];
    ALL_TAC] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`(Y:A->real) x`; `c:real`; `N:num`] RIEMANN_LOWER_MIN) THEN
   ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]]; ALL_TAC] THEN
  (* Equality E[rsum_X] = E[rsum_Y] via tail probability equality *)
  (* Convert E[sum(1..N)(...)] to sum(1..N)(E[...]) for both X and Y *)
  SUBGOAL_THEN
    `expectation p
      (\x:A. sum(1..N) (\k. if X x > &k * c / &N then c / &N else &0)) =
     sum(1..N)
      (\k. expectation p (\x. if X x > &k * c / &N then c / &N else &0))`
    SUBST1_TAC THENL
  [SUBGOAL_THEN
    `(\x:A. sum(1..N) (\k. if X x > &k * c / &N then c / &N else &0)) =
     (\x. sum(0..N-1)
       (\i. (\x. if X x > &(i + 1) * c / &N then c / &N else &0) x))`
    SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:A` THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[SUM_OFFSET_0] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[ADD_CLAUSES]; ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `\i:num. (\x:A. if X x > &(i+1) * c / &N then c / &N else &0)`;
     `N - 1`] EXPECTATION_SUM) THEN
   REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[GSYM SUM_OFFSET_0] THEN
   MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[ADD_CLAUSES]; ALL_TAC] THEN
  SUBGOAL_THEN
    `expectation p
      (\x:A. sum(1..N) (\k. if Y x > &k * c / &N then c / &N else &0)) =
     sum(1..N)
      (\k. expectation p (\x. if Y x > &k * c / &N then c / &N else &0))`
    SUBST1_TAC THENL
  [SUBGOAL_THEN
    `(\x:A. sum(1..N) (\k. if Y x > &k * c / &N then c / &N else &0)) =
     (\x. sum(0..N-1)
       (\i. (\x. if Y x > &(i + 1) * c / &N then c / &N else &0) x))`
    SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:A` THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[SUM_OFFSET_0] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[ADD_CLAUSES]; ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `\i:num. (\x:A. if Y x > &(i+1) * c / &N then c / &N else &0)`;
     `N - 1`] EXPECTATION_SUM) THEN
   REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[GSYM SUM_OFFSET_0] THEN
   MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[ADD_CLAUSES]; ALL_TAC] THEN
  (* Each term is equal by EXPECTATION_IF_GT + EQUIDIST_TAIL_PROB_GT *)
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= c / &N` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_IMP_LE THEN
   ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; LE_1]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `&k * c / &N`; `c / &N`]
    EXPECTATION_IF_GT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `Y:A->real`; `&k * c / &N`; `c / &N`]
    EXPECTATION_IF_GT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC EQUIDIST_TAIL_PROB_GT THEN ASM_REWRITE_TAC[]);;

(* Equidistributed expectations of min-squared-truncation *)
let EQUIDIST_NONNEG_MIN_SQ_EXPECTATION = prove
 (`!p:A prob_space X Y c.
    random_variable p X /\ random_variable p Y /\
    (!x. x IN prob_carrier p ==> &0 <= X x) /\
    (!x. x IN prob_carrier p ==> &0 <= Y x) /\
    (!a. distribution_fn p X a = distribution_fn p Y a) /\
    &0 < c
    ==> expectation p (\x. min (X x) c pow 2) =
        expectation p (\x. min (Y x) c pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Key identity: min z c pow 2 = min (z^2) (c^2) for nonneg z *)
  SUBGOAL_THEN `!z. &0 <= z ==> min z c pow 2 = min (z pow 2) (c pow 2)`
    ASSUME_TAC THENL
  [X_GEN_TAC `z:real` THEN DISCH_TAC THEN
   REWRITE_TAC[real_min] THEN
   COND_CASES_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THENL
   [SUBGOAL_THEN `z pow 2 <= c pow 2` MP_TAC THENL
    [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_ARITH_TAC;
     ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `c pow 2 <= z pow 2` MP_TAC THENL
    [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_ARITH_TAC;
     ASM_ARITH_TAC]];
   ALL_TAC] THEN
  (* Rewrite LHS: E[min(X,c)^2] = E[min(X^2,c^2)] *)
  SUBGOAL_THEN
    `expectation p (\x:A. min (X x) c pow 2) =
     expectation p (\x. min (X x pow 2) (c pow 2))`
    SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_EXT THEN X_GEN_TAC `x:A` THEN
   DISCH_TAC THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  (* Rewrite RHS: E[min(Y,c)^2] = E[min(Y^2,c^2)] *)
  SUBGOAL_THEN
    `expectation p (\x:A. min (Y x) c pow 2) =
     expectation p (\x. min (Y x pow 2) (c pow 2))`
    SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_EXT THEN X_GEN_TAC `x:A` THEN
   DISCH_TAC THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  (* Apply EQUIDIST_NONNEG_MIN_EXPECTATION to X^2, Y^2 with constant c^2 *)
  MATCH_MP_TAC EQUIDIST_NONNEG_MIN_EXPECTATION THEN
  REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_SQUARE THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC RANDOM_VARIABLE_SQUARE THEN ASM_REWRITE_TAC[];
   GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_LE_POW_2];
   GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_LE_POW_2];
   (* CDF equality for squared functions *)
   X_GEN_TAC `a':real` THEN REWRITE_TAC[distribution_fn] THEN
   ASM_CASES_TAC `a' < &0` THENL
   [SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ X x pow 2 <= a'} = {}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
     GEN_TAC THEN STRIP_TAC THEN
     MP_TAC(SPEC `(X:A->real) x` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
     ALL_TAC] THEN
    SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ Y x pow 2 <= a'} = {}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
     GEN_TAC THEN STRIP_TAC THEN
     MP_TAC(SPEC `(Y:A->real) x` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
     ALL_TAC] THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= a'` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   (* For nonneg X: {X^2 <= a'} = {X <= sqrt(a')} *)
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ X x pow 2 <= a'} =
     {x | x IN prob_carrier p /\ X x <= sqrt a'}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
    [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[];
     SUBGOAL_THEN `&0 <= (X:A->real) x` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
     MP_TAC(ISPECL [`2`; `(X:A->real) x`; `sqrt a'`] REAL_POW_LE2) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     ASM_SIMP_TAC[SQRT_POW_2]];
    ALL_TAC] THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ Y x pow 2 <= a'} =
     {x | x IN prob_carrier p /\ Y x <= sqrt a'}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
    [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[];
     SUBGOAL_THEN `&0 <= (Y:A->real) x` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
     MP_TAC(ISPECL [`2`; `(Y:A->real) x`; `sqrt a'`] REAL_POW_LE2) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     ASM_SIMP_TAC[SQRT_POW_2]];
    ALL_TAC] THEN
   ASM_REWRITE_TAC[GSYM distribution_fn];
   (* &0 < c pow 2 *)
   MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]]);;

(* Equidistributed max-zero preserves CDF equality *)
let EQUIDIST_MAX_ZERO = prove
 (`!p:A prob_space X Y.
    random_variable p X /\ random_variable p Y /\
    (!a. distribution_fn p X a = distribution_fn p Y a)
    ==> !a. distribution_fn p (\x. max (X x) (&0)) a =
            distribution_fn p (\x. max (Y x) (&0)) a`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[distribution_fn] THEN
  ASM_CASES_TAC `a < &0` THENL
  [SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ max (X x) (&0) <= a} = {}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ max (Y x) (&0) <= a} = {}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ max (X x) (&0) <= a} =
    {x | x IN prob_carrier p /\ X x <= a}` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
   EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ max (Y x) (&0) <= a} =
    {x | x IN prob_carrier p /\ Y x <= a}` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
   EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM distribution_fn]);;

(* Equidistributed strict inequality probability *)
let EQUIDIST_PROB_LT = prove
 (`!p:A prob_space X Y c.
    random_variable p X /\ random_variable p Y /\
    (!a. distribution_fn p X a = distribution_fn p Y a)
    ==> prob p {x | x IN prob_carrier p /\ X x < c} =
        prob p {x | x IN prob_carrier p /\ Y x < c}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`sequentially`;
    `\n:num. prob (p:A prob_space)
      {x:A | x IN prob_carrier p /\ (X:A->real) x <= c - &1 / &(SUC n)}`;
    `prob (p:A prob_space) {x:A | x IN prob_carrier p /\ X x < c}`;
    `prob (p:A prob_space) {x:A | x IN prob_carrier p /\ Y x < c}`]
    REALLIM_UNIQUE) THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC PROB_STRICT_INEQ_LIMIT THEN ASM_REWRITE_TAC[];
   SUBGOAL_THEN
     `(\n. prob (p:A prob_space) {x:A | x IN prob_carrier p /\
       (X:A->real) x <= c - &1 / &(SUC n)}) =
      (\n. prob p {x | x IN prob_carrier p /\
       (Y:A->real) x <= c - &1 / &(SUC n)})` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    ASM_REWRITE_TAC[GSYM distribution_fn];
    MATCH_MP_TAC PROB_STRICT_INEQ_LIMIT THEN ASM_REWRITE_TAC[]]]);;

(* Equidist neg-max-zero: distribution_fn of max(-X, 0) *)
let EQUIDIST_NEG_MAX_ZERO = prove
 (`!p:A prob_space X Y.
    random_variable p X /\ random_variable p Y /\
    (!a. distribution_fn p X a = distribution_fn p Y a)
    ==> !a. distribution_fn p (\x. max (--(X x)) (&0)) a =
            distribution_fn p (\x. max (--(Y x)) (&0)) a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[distribution_fn] THEN
  ASM_CASES_TAC `a < &0` THENL
  [SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ max (--(X x)) (&0) <= a} = {}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ max (--(Y x)) (&0) <= a} = {}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ max (--(X x)) (&0) <= a} =
    {x | x IN prob_carrier p /\ X x >= --a}` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
   EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ max (--(Y x)) (&0) <= a} =
    {x | x IN prob_carrier p /\ Y x >= --a}` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
   EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ X x >= --a} =
    prob_carrier p DIFF {x | x IN prob_carrier p /\ X x < --a}` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF] THEN GEN_TAC THEN
   ASM_CASES_TAC `x:A IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ Y x >= --a} =
    prob_carrier p DIFF {x | x IN prob_carrier p /\ Y x < --a}` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF] THEN GEN_TAC THEN
   ASM_CASES_TAC `x:A IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ X x < --a} IN prob_events p /\
     {x:A | x IN prob_carrier p /\ Y x < --a} IN prob_events p`
    STRIP_ASSUME_TAC THENL
  [CONJ_TAC THENL
   [SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\ X x < --a} =
       prob_carrier p DIFF {x | x IN prob_carrier p /\ X x >= --a}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF] THEN GEN_TAC THEN
     ASM_CASES_TAC `x:A IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
     REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC PROB_COMPL_IN_EVENTS THEN
    MATCH_MP_TAC RV_LEVEL_GE_IN_EVENTS THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\ Y x < --a} =
       prob_carrier p DIFF {x | x IN prob_carrier p /\ Y x >= --a}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF] THEN GEN_TAC THEN
     ASM_CASES_TAC `x:A IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
     REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC PROB_COMPL_IN_EVENTS THEN
    MATCH_MP_TAC RV_LEVEL_GE_IN_EVENTS THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  ASM_SIMP_TAC[PROB_COMPL] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC EQUIDIST_PROB_LT THEN ASM_REWRITE_TAC[]);;

(* Nonneg equidistributed integrable functions have equal expectations *)
let EQUIDIST_NONNEG_EXPECTATION = prove
 (`!p:A prob_space f g.
    integrable p f /\ integrable p g /\
    (!x. x IN prob_carrier p ==> &0 <= f x) /\
    (!x. x IN prob_carrier p ==> &0 <= g x) /\
    (!a. distribution_fn p f a = distribution_fn p g a)
    ==> expectation p f = expectation p g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((\n. expectation (p:A prob_space)
    (\x. min ((f:A->real) x) (&n))) ---> expectation p f) sequentially`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `f:A->real`] EXPECTATION_MIN_ABS_LIMIT) THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `expectation (p:A prob_space) (\x. abs ((f:A->real) x)) =
     expectation p f` SUBST1_TAC THENL
   [MATCH_MP_TAC EXPECTATION_EXT THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN
    ASM_SIMP_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `!n. expectation (p:A prob_space)
     (\x. min (abs ((f:A->real) x)) (&n)) =
     expectation p (\x. min (f x) (&n))` (fun th -> REWRITE_TAC[th]) THEN
   GEN_TAC THEN MATCH_MP_TAC EXPECTATION_EXT THEN X_GEN_TAC `z:A` THEN
   DISCH_TAC THEN BETA_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `((\n. expectation (p:A prob_space)
    (\x. min ((g:A->real) x) (&n))) ---> expectation p g) sequentially`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `g:A->real`] EXPECTATION_MIN_ABS_LIMIT) THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `expectation (p:A prob_space) (\x. abs ((g:A->real) x)) =
     expectation p g` SUBST1_TAC THENL
   [MATCH_MP_TAC EXPECTATION_EXT THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN
    ASM_SIMP_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `!n. expectation (p:A prob_space)
     (\x. min (abs ((g:A->real) x)) (&n)) =
     expectation p (\x. min (g x) (&n))` (fun th -> REWRITE_TAC[th]) THEN
   GEN_TAC THEN MATCH_MP_TAC EXPECTATION_EXT THEN X_GEN_TAC `z:A` THEN
   DISCH_TAC THEN BETA_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  MP_TAC(ISPECL [`sequentially`;
    `\n. expectation (p:A prob_space) (\x. min ((f:A->real) x) (&n))`;
    `expectation (p:A prob_space) (f:A->real)`;
    `expectation (p:A prob_space) (g:A->real)`] REALLIM_UNIQUE) THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\n. expectation (p:A prob_space)
    (\x. min ((f:A->real) x) (&n))) =
    (\n. expectation p (\x. min ((g:A->real) x) (&n)))` SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
   ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC EXPECTATION_EXT THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    BETA_TAC THEN
    SUBGOAL_THEN `&0 <= (f:A->real) z /\ &0 <= (g:A->real) z`
      STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
     ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
   MATCH_MP_TAC EQUIDIST_NONNEG_MIN_EXPECTATION THEN
   ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
   ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY] o
    check (fun th -> free_in `g:A->real` (concl th) &&
                     not(free_in `f:A->real` (concl th)))) THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `MAX N 1` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (\x. min ((f:A->real) x) (&n)) =
    expectation p (\x. min ((g:A->real) x) (&n))` SUBST1_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* ================================================================= *)
(* IID SLLN for nonneg RVs with finite first moment                  *)
(* ================================================================= *)

let IID_SLLN_NONNEG = prove
 (`!p:A prob_space (X:num->A->real) mu.
    (!n. integrable p (X n)) /\
    (!n x. x IN prob_carrier p ==> &0 <= X n x) /\
    (!n. expectation p (X n) = mu) /\
    (!i j. ~(i = j) ==> indep_rv p (X i) (X j)) /\
    (!n a. distribution_fn p (X n) a = distribution_fn p (X 0) a)
    ==> almost_surely p
          {x | ((\n. inv(&(SUC n)) * sum(0..n) (\i. X i x)) ---> mu)
               sequentially}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* mu >= 0 from nonnegativity *)
  SUBGOAL_THEN `&0 <= mu` ASSUME_TAC THENL
  [SUBGOAL_THEN `mu = expectation p ((X:num->A->real) 0)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC EXPECTATION_POS THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Decompose: S_n/(n+1) = S'_n/(n+1) + error/(n+1) *)
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC
    `{x:A | ((\n. inv(&(SUC n)) * sum(0..n)
                  (\i. min ((X:num->A->real) i x) (&(SUC i)))) ---> mu)
             sequentially} INTER
     {x | ((\n. inv(&(SUC n)) * sum(0..n)
                  (\i. X i x - min (X i x) (&(SUC i)))) ---> &0)
           sequentially}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC ALMOST_SURELY_INTER THEN CONJ_TAC THENL
   [(* Part 1: truncated averages -> mu *)
    (* Asm 6: !n. random_variable p (X n) *)
    SUBGOAL_THEN `!n. random_variable (p:A prob_space) ((X:num->A->real) n)`
      ASSUME_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    (* Asm 7: !n. integrable p (\x. min (X n x) (&(SUC n))) *)
    SUBGOAL_THEN `!n. integrable (p:A prob_space)
      (\x. min ((X:num->A->real) n x) (&(SUC n)))` ASSUME_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_MIN THEN
     CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
     ASM_REWRITE_TAC[INTEGRABLE_CONST];
     ALL_TAC] THEN
    (* Asm 8: !n x. x IN carrier ==> 0 <= min(X n x, SUC n) *)
    SUBGOAL_THEN `!n (y:A). y IN prob_carrier p ==>
      &0 <= min ((X:num->A->real) n y) (&(SUC n))` ASSUME_TAC THENL
    [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_MIN] THEN
     CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_POS]];
     ALL_TAC] THEN
    (* Asm 9: !n. integrable p (\x. min(X n x, SUC n) pow 2) *)
    SUBGOAL_THEN `!n. integrable (p:A prob_space)
      (\x. min ((X:num->A->real) n x) (&(SUC n)) pow 2)` ASSUME_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
     EXISTS_TAC `&(SUC n) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RANDOM_VARIABLE_SQUARE THEN
      MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
      CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
      ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST];
      ALL_TAC] THEN
     X_GEN_TAC `y:A` THEN DISCH_TAC THEN BETA_TAC THEN
     REWRITE_TAC[REAL_ABS_POW] THEN
     MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
     MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= a ==> abs x <= a`) THEN
     CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_MIN] THEN CONJ_TAC THENL
      [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
       REWRITE_TAC[REAL_POS]];
      MP_TAC(ISPECL [`(X:num->A->real) n y`; `&(SUC n)`] REAL_MIN_MIN) THEN
      REAL_ARITH_TAC];
     ALL_TAC] THEN
    (* Asm 10: (\n. E[min(X 0, SUC n)]) -> mu *)
    SUBGOAL_THEN `((\n. expectation (p:A prob_space)
      (\x. min ((X:num->A->real) 0 x) (&(SUC n)))) ---> mu) sequentially`
      ASSUME_TAC THENL
    [SUBGOAL_THEN `((\n. expectation (p:A prob_space)
      (\x. min ((X:num->A->real) 0 x) (&n))) ---> mu) sequentially`
      MP_TAC THENL
     [MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) 0`]
        EXPECTATION_MIN_ABS_LIMIT) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `expectation (p:A prob_space)
        (\x. abs ((X:num->A->real) 0 x)) = mu` SUBST1_TAC THENL
      [SUBGOAL_THEN `expectation (p:A prob_space)
         (\x. abs ((X:num->A->real) 0 x)) =
        expectation p (X 0)` SUBST1_TAC THENL
       [MATCH_MP_TAC EXPECTATION_EXT THEN X_GEN_TAC `z:A` THEN
        DISCH_TAC THEN BETA_TAC THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN
        SUBGOAL_THEN `&0 <= (X:num->A->real) 0 z`
          (fun th -> REWRITE_TAC[th]) THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
       ALL_TAC] THEN
      DISCH_THEN(fun th -> MP_TAC th) THEN
      SUBGOAL_THEN `!n. expectation (p:A prob_space)
        (\x. min (abs ((X:num->A->real) 0 x)) (&n)) =
        expectation p (\x. min (X 0 x) (&n))`
        (fun th -> REWRITE_TAC[th]) THEN
      GEN_TAC THEN MATCH_MP_TAC EXPECTATION_EXT THEN
      X_GEN_TAC `z:A` THEN DISCH_TAC THEN
      BETA_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN
      SUBGOAL_THEN `&0 <= (X:num->A->real) 0 z`
        (fun th -> REWRITE_TAC[th]) THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
     REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
     DISCH_THEN(fun th -> X_GEN_TAC `e:real` THEN DISCH_TAC THEN
       MP_TAC(SPEC `e:real` th)) THEN
     ASM_REWRITE_TAC[] THEN
     DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
     EXISTS_TAC `N:num` THEN REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `SUC n`) THEN
     ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]];
     ALL_TAC] THEN
    (* Asm 11: !n. E[min(X n, SUC n)] = E[min(X 0, SUC n)] *)
    SUBGOAL_THEN `!n. expectation (p:A prob_space)
      (\x. min ((X:num->A->real) n x) (&(SUC n))) =
      expectation p (\x. min (X 0 x) (&(SUC n)))` ASSUME_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC EQUIDIST_NONNEG_MIN_EXPECTATION THEN
     CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
     CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     CONJ_TAC THENL
     [GEN_TAC THEN FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `a:real`]) THEN
      REWRITE_TAC[];
      REWRITE_TAC[REAL_OF_NUM_LT; LT_0]];
     ALL_TAC] THEN
    (* Asm 12: !n. E[min(X n, SUC n)^2] = E[min(X 0, SUC n)^2] *)
    SUBGOAL_THEN `!n. expectation (p:A prob_space)
      (\x. min ((X:num->A->real) n x) (&(SUC n)) pow 2) =
      expectation p (\x. min (X 0 x) (&(SUC n)) pow 2)` ASSUME_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC EQUIDIST_NONNEG_MIN_SQ_EXPECTATION THEN
     CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
     CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     CONJ_TAC THENL
     [GEN_TAC THEN FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `a:real`]) THEN
      REWRITE_TAC[];
      REWRITE_TAC[REAL_OF_NUM_LT; LT_0]];
     ALL_TAC] THEN
    (* Asm 13: !n. 0 <= Var(Y_n) *)
    SUBGOAL_THEN `!n. &0 <= variance (p:A prob_space)
      (\x. min ((X:num->A->real) n x) (&(SUC n)))` ASSUME_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC VARIANCE_NONNEG THEN BETA_TAC THEN
     ABBREV_TAC `c = expectation (p:A prob_space)
       (\x. min ((X:num->A->real) n x) (&(SUC n)))` THEN
     SUBGOAL_THEN `(\x:A. (min ((X:num->A->real) n x) (&(SUC n)) - c) pow 2) =
       (\x. min (X n x) (&(SUC n)) pow 2 +
         (--(&2 * c) * min (X n x) (&(SUC n)) + c pow 2))`
       SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
      MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
      [ASM_REWRITE_TAC[];
       MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[INTEGRABLE_CONST]]]];
     ALL_TAC] THEN
    (* Asm 14: variance summability *)
    SUBGOAL_THEN `real_summable (from 0)
      (\n. variance (p:A prob_space)
        (\x. min ((X:num->A->real) n x) (&(SUC n))) / &(SUC n) pow 2)`
      ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
     EXISTS_TAC `\n. expectation (p:A prob_space)
       (\x. min ((X:num->A->real) 0 x) (&(SUC n)) pow 2) /
       &(SUC n) pow 2` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC TRUNCATED_VARIANCE_SUMMABLE THEN
      CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
     EXISTS_TAC `0` THEN REWRITE_TAC[IN_FROM; GE] THEN
     GEN_TAC THEN DISCH_TAC THEN
     MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_REWRITE_TAC[REAL_LE_POW_2];
      ALL_TAC] THEN
     SUBGOAL_THEN `&0 < &(SUC n) pow 2` ASSUME_TAC THENL
     [SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; LT_0]; ALL_TAC] THEN
     ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `expectation (p:A prob_space)
       (\x. min ((X:num->A->real) n x) (&(SUC n)) pow 2)` THEN
     CONJ_TAC THENL
     [MP_TAC(ISPECL [`p:A prob_space`;
       `\x. min ((X:num->A->real) n x) (&(SUC n))`] VARIANCE_ALT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[REAL_ARITH `a - b <= a <=> &0 <= b`; REAL_LE_POW_2];
      ASM_REWRITE_TAC[REAL_LE_REFL]];
     ALL_TAC] THEN
    (* Main: reduce to convergence along all gseq b *)
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC
      `INTERS
        {(\b:num. {x:A |
           ((\k. inv(&(gseq b k)) *
             sum(0..gseq b k - 1)
               (\i. min ((X:num->A->real) i x) (&(SUC i)) -
                 expectation p (\y. min (X i y) (&(SUC i)))))
             ---> &0) sequentially}) b | b IN (:num)}` THEN
    CONJ_TAC THENL
    [(* Almost sure convergence along gseq for all b *)
     MATCH_MP_TAC ALMOST_SURELY_COUNTABLE_INTER THEN
     BETA_TAC THEN GEN_TAC THEN
     MP_TAC(ISPECL [`p:A prob_space`;
         `\n (x:A). min ((X:num->A->real) n x) (&(SUC n)) -
           expectation p (\y. min (X n y) (&(SUC n)))`;
         `b:num`] SLLN_SUBSEQ_GSEQ) THEN
     BETA_TAC THEN
     DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [(* integrable (\x. min(X n x, SUC n) - E[...]) *)
      GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
      ASM_REWRITE_TAC[INTEGRABLE_CONST];
      (* integrable (\x. (min(X n x, SUC n) - E[...]) pow 2) *)
      GEN_TAC THEN
      ABBREV_TAC `c = expectation (p:A prob_space)
        (\x. min ((X:num->A->real) n x) (&(SUC n)))` THEN
      SUBGOAL_THEN
        `(\x:A. (min ((X:num->A->real) n x) (&(SUC n)) - c) pow 2) =
        (\x. min (X n x) (&(SUC n)) pow 2 +
          (--(&2 * c) * min (X n x) (&(SUC n)) + c pow 2))`
        SUBST1_TAC THENL
      [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
       MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
        [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
         REWRITE_TAC[INTEGRABLE_CONST]]]];
      (* expectation (\x. min(X n x, SUC n) - E[...]) = 0 *)
      GEN_TAC THEN
      W(MP_TAC o PART_MATCH (lhand o rand) EXPECTATION_SUB o
        lhand o snd) THEN
      ANTS_TAC THENL
      [ASM_REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[EXPECTATION_CONST] THEN
      REWRITE_TAC[REAL_SUB_REFL];
      (* covariance = 0 *)
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `covariance (p:A prob_space)
        (\x. min ((X:num->A->real) i x) (&(SUC i)) -
          expectation p (\y. min (X i y) (&(SUC i))))
        (\x. min (X j x) (&(SUC j)) -
          expectation p (\y. min (X j y) (&(SUC j)))) =
        covariance p (\x. min (X i x) (&(SUC i)))
          (\x. min (X j x) (&(SUC j)))` SUBST1_TAC THENL
      [MATCH_MP_TAC COVARIANCE_SHIFT THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
      MATCH_MP_TAC COVARIANCE_INDEP THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC INTEGRABLE_MUL_SQUARE THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
        CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
        ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST]; ALL_TAC] THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
        CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
        ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST]; ALL_TAC] THEN
       ASM_REWRITE_TAC[];
       ALL_TAC] THEN
      MATCH_MP_TAC INDEP_RV_MIN_DIFF_CONST THEN
      CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      (* summable variance *)
      MATCH_MP_TAC REAL_SUMMABLE_EQ THEN
      EXISTS_TAC `\n. variance (p:A prob_space)
        (\x. min ((X:num->A->real) n x) (&(SUC n))) /
        &(SUC n) pow 2` THEN
      CONJ_TAC THENL
      [REWRITE_TAC[IN_FROM] THEN
       GEN_TAC THEN DISCH_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
       CONV_TAC SYM_CONV THEN
       SUBGOAL_THEN
         `(\x':A. min ((X:num->A->real) x x') (&(SUC x)) -
           expectation p (\y. min (X x y) (&(SUC x)))) =
          (\x'. min (X x x') (&(SUC x)) +
            --(expectation p (\y. min (X x y) (&(SUC x)))))` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
       MATCH_MP_TAC VARIANCE_SHIFT THEN ASM_REWRITE_TAC[];
       ASM_REWRITE_TAC[]]];
     ALL_TAC] THEN
    (* On the a.s. set, apply NONDECREASING_CONVERGENCE_GSEQ *)
    REWRITE_TAC[INTERS_GSPEC; IN_UNIV; IN_ELIM_THM] THEN
    BETA_TAC THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN DISCH_TAC THEN
    MP_TAC(SPECL
      [`\n. sum(0..n) (\i. min ((X:num->A->real) i x) (&(SUC i)))`;
       `mu:real`]
      NONDECREASING_CONVERGENCE_GSEQ) THEN
    BETA_TAC THEN
    ANTS_TAC THENL
    [REPEAT CONJ_TAC THENL
     [(* nondecreasing *)
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      REWRITE_TAC[FINITE_NUMSEG] THEN CONJ_TAC THENL
      [REWRITE_TAC[SUBSET; IN_NUMSEG] THEN ASM_ARITH_TAC;
       REWRITE_TAC[IN_DIFF; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
       REWRITE_TAC[REAL_LE_MIN] THEN CONJ_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[REAL_POS]]];
      (* nonneg *)
      GEN_TAC THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_MIN] THEN CONJ_TAC THENL
      [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
       REWRITE_TAC[REAL_POS]];
      (* 0 <= mu *)
      ASM_REWRITE_TAC[];
      (* convergence along gseq *)
      GEN_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `b:num`) THEN
      SUBGOAL_THEN `!k. inv(&(gseq b k)) *
        sum (0..gseq b k - 1)
          (\i. min ((X:num->A->real) i x) (&(SUC i)) -
            expectation p (\y. min (X i y) (&(SUC i)))) =
        sum(0..gseq b k - 1) (\i. min (X i x) (&(SUC i))) /
          &(gseq b k) -
        inv(&(gseq b k)) * sum(0..gseq b k - 1)
          (\i. expectation p (\y. min (X i y) (&(SUC i))))`
        (fun th -> REWRITE_TAC[th]) THENL
      [GEN_TAC THEN REWRITE_TAC[SUM_SUB_NUMSEG; real_div] THEN
       REWRITE_TAC[REAL_SUB_RDISTRIB] THEN REAL_ARITH_TAC;
       ALL_TAC] THEN
      DISCH_TAC THEN
      (* Cesaro mean of expectations -> mu *)
      SUBGOAL_THEN
        `((\k. inv(&(gseq b k)) * sum(0..gseq b k - 1)
            (\i. expectation p
              (\y. min ((X:num->A->real) i y) (&(SUC i))))) --->
          mu) sequentially`
        ASSUME_TAC THENL
      [SUBGOAL_THEN `!k. sum (0..gseq b k - 1)
         (\i. expectation (p:A prob_space)
           (\y. min ((X:num->A->real) i y) (&(SUC i)))) =
         sum (0..gseq b k - 1)
         (\i. expectation p (\y. min (X 0 y) (&(SUC i))))`
         (fun th -> REWRITE_TAC[th]) THENL
       [GEN_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
       SUBGOAL_THEN `!k:num. gseq b k = SUC(gseq b k - 1)`
         ASSUME_TAC THENL
       [GEN_TAC THEN MP_TAC(SPECL [`b:num`; `k:num`] GSEQ_POS) THEN
        ARITH_TAC;
        ALL_TAC] THEN
       ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUC_SUB1] THEN
       MP_TAC(ISPECL [
         `\n. inv(&(SUC n)) * sum(0..n)
           (\i. expectation (p:A prob_space)
             (\y. min ((X:num->A->real) 0 y) (&(SUC i))))`;
         `mu:real`;
         `\k:num. gseq b k - 1`] REALLIM_SUBSEQUENCE) THEN
       BETA_TAC THEN DISCH_THEN(fun th -> MATCH_MP_TAC th) THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CESARO_MEAN THEN ASM_REWRITE_TAC[];
        REPEAT STRIP_TAC THEN
        SUBGOAL_THEN `gseq b m < gseq b n` ASSUME_TAC THENL
        [MATCH_MP_TAC LTE_TRANS THEN
         EXISTS_TAC `gseq b (SUC m)` THEN
         CONJ_TAC THENL
         [REWRITE_TAC[GSEQ_SUC_GT];
          MATCH_MP_TAC GSEQ_MONOTONE THEN ASM_ARITH_TAC];
         ALL_TAC] THEN
        MP_TAC(SPECL [`b:num`; `m:num`] GSEQ_POS) THEN
        MP_TAC(SPECL [`b:num`; `n:num`] GSEQ_POS) THEN
        ASM_ARITH_TAC];
       ALL_TAC] THEN
      (* Combine: a_k = (a_k - b_k) + b_k *)
      SUBGOAL_THEN
        `(\k. sum(0..gseq b k - 1)
           (\i. min ((X:num->A->real) i x) (&(SUC i))) /
          &(gseq b k)) =
         (\k. (sum(0..gseq b k - 1)
           (\i. min (X i x) (&(SUC i))) / &(gseq b k) -
           inv(&(gseq b k)) * sum(0..gseq b k - 1)
             (\i. expectation p
               (\y. min (X i y) (&(SUC i))))) +
           inv(&(gseq b k)) * sum(0..gseq b k - 1)
             (\i. expectation p
               (\y. min (X i y) (&(SUC i)))))`
        SUBST1_TAC THENL
      [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
       ALL_TAC] THEN
      SUBGOAL_THEN `mu = &0 + mu` SUBST1_TAC THENL
      [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REALLIM_ADD THEN ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
    (* f(n)/SUC(n) -> mu gives inv(SUC n)*sum -> mu *)
    SUBGOAL_THEN `(\n. inv(&(SUC n)) *
      sum(0..n) (\i. min ((X:num->A->real) i x) (&(SUC i)))) =
      (\n. sum(0..n) (\i. min (X i x) (&(SUC i))) / &(SUC n))`
      (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[FUN_EQ_THM; real_div] THEN GEN_TAC THEN REAL_ARITH_TAC;
    (* Part 2: truncation error -> 0 via Borel-Cantelli *)
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC
      `prob_carrier (p:A prob_space) DIFF
       limsup_events
         (\n. {x:A | x IN prob_carrier p /\ X n x > &(SUC n)})` THEN
    CONJ_TAC THENL
    [REWRITE_TAC[almost_surely] THEN
     EXISTS_TAC
       `limsup_events
         (\n. {x:A | x IN prob_carrier p /\ X n x > &(SUC n)})` THEN
     SUBGOAL_THEN `!n. random_variable (p:A prob_space) ((X:num->A->real) n)`
       ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
     SUBGOAL_THEN `!n. {x:A | x IN prob_carrier p /\ X n x > &(SUC n)} IN
                       prob_events p` ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC RV_LEVEL_GT_IN_EVENTS THEN
      CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
     CONJ_TAC THENL
     [REWRITE_TAC[null_event] THEN CONJ_TAC THENL
      [MATCH_MP_TAC LIMSUP_EVENTS_IN_EVENTS THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC FIRST_BOREL_CANTELLI THEN ASM_REWRITE_TAC[] THEN
       MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
       EXISTS_TAC
         `\k. prob p {x:A | x IN prob_carrier p /\ X 0 x >= &(k + 1)}` THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC TAIL_PROB_SUMMABLE THEN
        CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `0` THEN REWRITE_TAC[IN_FROM] THEN
        X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[ADD1] THEN
        SUBGOAL_THEN
          `&0 <= prob p {x:A | x IN prob_carrier p /\ X n x > &(n + 1)}`
          (fun th -> REWRITE_TAC[real_abs; th]) THENL
        [MATCH_MP_TAC PROB_POSITIVE THEN REWRITE_TAC[GSYM ADD1] THEN
         ASM_REWRITE_TAC[];
         ALL_TAC] THEN
        SUBGOAL_THEN
          `prob p {x:A | x IN prob_carrier p /\ X n x > &(n + 1)} =
           prob p {x | x IN prob_carrier p /\ X 0 x > &(n + 1)}`
          SUBST1_TAC THENL
        [MATCH_MP_TAC EQUIDIST_TAIL_PROB_GT THEN
         CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
         CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
         CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
         GEN_TAC THEN
         FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `a:real`]) THEN
         REWRITE_TAC[];
         ALL_TAC] THEN
        MATCH_MP_TAC PROB_MONO THEN CONJ_TAC THENL
        [MATCH_MP_TAC RV_LEVEL_GT_IN_EVENTS THEN
         CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[];
         CONJ_TAC THENL
         [MATCH_MP_TAC RV_LEVEL_GE_IN_EVENTS THEN
          CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
          MESON_TAC[REAL_ARITH `x > a ==> x >= a`]]]]];
      SET_TAC[]];
     (* Deterministic: outside limsup, error -> 0 *)
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN
     REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN DISCH_TAC THEN
     SUBGOAL_THEN `?M:num. !n. n >= M ==> ~((X:num->A->real) n x > &(SUC n))`
       MP_TAC THENL
     [POP_ASSUM(MP_TAC o CONJUNCT2) THEN
      REWRITE_TAC[limsup_events; IN_INTERS] THEN
      REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
      POP_ASSUM MP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_ELIM_THM]) THEN
      REWRITE_TAC[IN_UNIV] THEN
      DISCH_THEN(X_CHOOSE_THEN `M:num` SUBST_ALL_TAC) THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
      DISCH_TAC THEN EXISTS_TAC `M:num` THEN
      X_GEN_TAC `nn:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC
        `{x:A | x IN prob_carrier p /\ X nn x > &(SUC nn)}`) THEN
      REWRITE_TAC[IN_ELIM_THM; DE_MORGAN_THM] THEN
      DISCH_THEN DISJ_CASES_TAC THENL
      [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
       DISCH_THEN(MP_TAC o SPEC `nn:num`) THEN ASM_REWRITE_TAC[];
       ASM_MESON_TAC[]];
      ALL_TAC] THEN
     DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
     SUBGOAL_THEN
       `!n. n >= M
            ==> (X:num->A->real) n x - min (X n x) (&(SUC n)) = &0`
       ASSUME_TAC THENL
     [X_GEN_TAC `nn:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `nn:num`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[real_gt; REAL_NOT_LT] THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `min x y = x ==> x - min x y = &0`) THEN
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> min x y = x`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
     ABBREV_TAC
       `C = sum(0..M)
              (\i. (X:num->A->real) i x - min (X i x) (&(SUC i)))` THEN
     SUBGOAL_THEN
       `!n. n >= M ==>
            sum(0..n)
              (\i. (X:num->A->real) i x - min (X i x) (&(SUC i))) = C`
       ASSUME_TAC THENL
     [INDUCT_TAC THENL
      [DISCH_TAC THEN
       SUBGOAL_THEN `M = 0` SUBST_ALL_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
       ASM_REWRITE_TAC[];
       DISCH_TAC THEN ASM_CASES_TAC `n >= M:num` THENL
       [ASM_SIMP_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `SUC n`) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
        ASM_REWRITE_TAC[REAL_ADD_RID];
        SUBGOAL_THEN `SUC n = M` (fun th -> ASM_REWRITE_TAC[th]) THEN
        ASM_ARITH_TAC]];
      ALL_TAC] THEN
     MATCH_MP_TAC(ISPEC `sequentially` REALLIM_TRANSFORM_EVENTUALLY) THEN
     EXISTS_TAC `\n. inv(&(SUC n)) * C` THEN CONJ_TAC THENL
     [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      EXISTS_TAC `M:num` THEN X_GEN_TAC `nn:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
      FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[GE]) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      MP_TAC(SPEC `abs C / e` REAL_ARCH_SIMPLE) THEN
      DISCH_THEN(X_CHOOSE_TAC `K:num`) THEN
      EXISTS_TAC `K:num` THEN X_GEN_TAC `nn:num` THEN DISCH_TAC THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NUM] THEN
      SUBGOAL_THEN `abs C <= &K * e` ASSUME_TAC THENL
      [ASM_MESON_TAC[REAL_LE_LDIV_EQ]; ALL_TAC] THEN
      SUBGOAL_THEN `abs C < e * &(SUC nn)` ASSUME_TAC THENL
      [MATCH_MP_TAC REAL_LET_TRANS THEN
       EXISTS_TAC `e * &nn` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&K * e` THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[REAL_ARITH `a * e <= e * b <=> e * a <= e * b`] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC];
       ALL_TAC] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      REWRITE_TAC[GSYM real_div] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; LT_0]]]];
   (* On the intersection, sum X/(n+1) = sum Y/(n+1) + error/(n+1) -> mu+0 *)
   REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN
     `(\n. inv(&(SUC n)) * sum(0..n) (\i. (X:num->A->real) i x)) =
      (\n. inv(&(SUC n)) * sum(0..n) (\i. min (X i x) (&(SUC i))) +
           inv(&(SUC n)) * sum(0..n)
             (\i. X i x - min (X i x) (&(SUC i))))`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    REWRITE_TAC[GSYM REAL_ADD_LDISTRIB; GSYM SUM_ADD_NUMSEG] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `mu = mu + &0` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REALLIM_ADD THEN ASM_REWRITE_TAC[]]
  );;

(* ================================================================= *)
(* IID SLLN -- general signed case                                   *)
(* ================================================================= *)

let IID_SLLN = prove
 (`!p:A prob_space (X:num->A->real) mu.
    (!n. integrable p (X n)) /\
    (!n. expectation p (X n) = mu) /\
    (!i j. ~(i = j) ==> indep_rv p (X i) (X j)) /\
    (!n a. distribution_fn p (X n) a = distribution_fn p (X 0) a)
    ==> almost_surely p
          {x | ((\n. inv(&(SUC n)) * sum(0..n) (\i. X i x)) ---> mu)
               sequentially}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `mu_plus = expectation (p:A prob_space)
    (\x. max ((X:num->A->real) 0 x) (&0))` THEN
  SUBGOAL_THEN `!n. random_variable (p:A prob_space) ((X:num->A->real) n)`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Step 1: Apply IID_SLLN_NONNEG to positive parts max(X, 0) *)
  SUBGOAL_THEN
    `almost_surely (p:A prob_space)
      {x | ((\n. inv(&(SUC n)) * sum(0..n)
        (\i. max ((X:num->A->real) i x) (&0))) ---> mu_plus) sequentially}`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`;
      `\n (x:A). max ((X:num->A->real) n x) (&0)`;
      `mu_plus:real`] IID_SLLN_NONNEG) THEN
   REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
    [(* integrable max(X n, 0) *)
     GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_MAX THEN
     CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
     ASM_REWRITE_TAC[INTEGRABLE_CONST];
     (* nonneg *)
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL];
     (* E[max(X n, 0)] = mu_plus *)
     GEN_TAC THEN
     SUBGOAL_THEN `expectation (p:A prob_space)
       (\x. max ((X:num->A->real) n x) (&0)) =
       expectation p (\x. max (X 0 x) (&0))` SUBST1_TAC THENL
     [MATCH_MP_TAC EQUIDIST_NONNEG_EXPECTATION THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC INTEGRABLE_MAX THEN
       CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
       ASM_REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC] THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC INTEGRABLE_MAX THEN
       CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
       ASM_REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC] THEN
      CONJ_TAC THENL
      [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL];
       ALL_TAC] THEN
      CONJ_TAC THENL
      [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL];
       ALL_TAC] THEN
      SUBGOAL_THEN `!a. distribution_fn (p:A prob_space)
        (\x. max ((X:num->A->real) n x) (&0)) a =
        distribution_fn p (\x. max (X 0 x) (&0)) a`
        (fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC EQUIDIST_MAX_ZERO THEN
      CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      GEN_TAC THEN
      FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `a:real`]) THEN REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
     (* indep_rv max(X_i, 0) max(X_j, 0) *)
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     MATCH_MP_TAC INDEP_RV_MAX_CONST THEN
     CONV_TAC(DEPTH_CONV ETA_CONV) THEN ASM_SIMP_TAC[];
     (* equidist max(X n, 0) *)
     GEN_TAC THEN
     MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) n`;
       `(X:num->A->real) 0`] EQUIDIST_MAX_ZERO) THEN
     ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      GEN_TAC THEN
      FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `a:real`]) THEN REWRITE_TAC[];
      REWRITE_TAC[]]];
    REWRITE_TAC[]]; ALL_TAC] THEN
  (* Step 2: Apply IID_SLLN_NONNEG to negative parts max(-X, 0) *)
  SUBGOAL_THEN
    `almost_surely (p:A prob_space)
      {x | ((\n. inv(&(SUC n)) * sum(0..n)
        (\i. max (--((X:num->A->real) i x)) (&0))) --->
        (mu_plus - mu)) sequentially}`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`;
      `\n (x:A). max (--((X:num->A->real) n x)) (&0)`;
      `mu_plus - mu:real`] IID_SLLN_NONNEG) THEN
   REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
    [(* integrable max(-X n, 0) *)
     GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_MAX THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_NEG THEN
      CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[INTEGRABLE_CONST]];
     (* nonneg *)
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL];
     (* E[max(-X n, 0)] = mu_plus - mu *)
     GEN_TAC THEN
     SUBGOAL_THEN `(\x:A. max (--((X:num->A->real) n x)) (&0)) =
       (\x. max (X n x) (&0) - X n x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
      REWRITE_TAC[real_max] THEN
      COND_CASES_TAC THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
     SUBGOAL_THEN `expectation (p:A prob_space)
       (\x. max ((X:num->A->real) n x) (&0) - X n x) =
       expectation p (\x. max (X n x) (&0)) - expectation p (X n)`
       SUBST1_TAC THENL
     [MATCH_MP_TAC EXPECTATION_SUB THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC INTEGRABLE_MAX THEN
       CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
       ASM_REWRITE_TAC[INTEGRABLE_CONST];
       CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
     SUBGOAL_THEN `expectation (p:A prob_space)
       (\x. max ((X:num->A->real) n x) (&0)) = mu_plus` SUBST1_TAC THENL
     [SUBGOAL_THEN `expectation (p:A prob_space)
        (\x. max ((X:num->A->real) n x) (&0)) =
        expectation p (\x. max (X 0 x) (&0))` SUBST1_TAC THENL
      [MATCH_MP_TAC EQUIDIST_NONNEG_EXPECTATION THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_MAX THEN
        CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
        ASM_REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC] THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_MAX THEN
        CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
        ASM_REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC] THEN
       CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL];
        ALL_TAC] THEN
       CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL];
        ALL_TAC] THEN
       SUBGOAL_THEN `!a. distribution_fn (p:A prob_space)
         (\x. max ((X:num->A->real) n x) (&0)) a =
         distribution_fn p (\x. max (X 0 x) (&0)) a`
         (fun th -> REWRITE_TAC[th]) THEN
       MATCH_MP_TAC EQUIDIST_MAX_ZERO THEN
       CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
       CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
       CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
       GEN_TAC THEN
       FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `a:real`]) THEN REWRITE_TAC[];
       ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[]];
     (* indep_rv max(-X_i, 0) max(-X_j, 0) *)
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     MATCH_MP_TAC INDEP_RV_MAX_CONST THEN
     MATCH_MP_TAC INDEP_RV_NEG THEN
     CONV_TAC(DEPTH_CONV ETA_CONV) THEN ASM_SIMP_TAC[];
     (* equidist max(-X n, 0) *)
     GEN_TAC THEN
     MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) n`;
       `(X:num->A->real) 0`] EQUIDIST_NEG_MAX_ZERO) THEN
     ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      GEN_TAC THEN
      FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `a:real`]) THEN REWRITE_TAC[];
      REWRITE_TAC[]]];
    REWRITE_TAC[]]; ALL_TAC] THEN
  (* Step 3: Combine via X = max(X,0) - max(-X,0) and REALLIM_SUB *)
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC `{x:A | ((\n. inv(&(SUC n)) * sum(0..n)
    (\i. max ((X:num->A->real) i x) (&0))) ---> mu_plus) sequentially} INTER
    {x | ((\n. inv(&(SUC n)) * sum(0..n)
    (\i. max (--(X i x)) (&0))) ---> (mu_plus - mu)) sequentially}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC ALMOST_SURELY_INTER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `!n:num. sum(0..n) (\i. (X:num->A->real) i (x:A)) =
      sum(0..n) (\i. max (X i x) (&0)) -
      sum(0..n) (\i. max (--(X i x)) (&0))`
    ASSUME_TAC THENL
  [GEN_TAC THEN REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN
   MATCH_MP_TAC SUM_EQ_NUMSEG THEN
   REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[real_max] THEN
   COND_CASES_TAC THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `(\n:num. inv(&(SUC n)) * sum(0..n)
      (\i. (X:num->A->real) i (x:A))) =
     (\n. inv(&(SUC n)) * sum(0..n) (\i. max (X i x) (&0)) -
          inv(&(SUC n)) * sum(0..n) (\i. max (--(X i x)) (&0)))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; BETA_THM] THEN X_GEN_TAC `nn:num` THEN
   ASM_REWRITE_TAC[REAL_SUB_LDISTRIB]; ALL_TAC] THEN
  SUBGOAL_THEN `mu:real = mu_plus - (mu_plus - mu)` SUBST1_TAC THENL
  [REAL_ARITH_TAC;
   MATCH_MP_TAC REALLIM_SUB THEN ASM_REWRITE_TAC[]]);;

(* ================================================================== *)
(* Kolmogorov Three-Series Theorem (Sufficiency)                       *)
(* ================================================================== *)

(* Helper: tail of a nonneg summable series goes to 0 *)
let REAL_SUMMABLE_TAIL_BOUND = prove
 (`!f:num->real. (!n. &0 <= f n) /\ real_summable (from 0) f
    ==> !e. &0 < e ==> ?a. !N. sum(a..a+N) f < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [real_summable]) THEN
  DISCH_THEN(X_CHOOSE_TAC `V:real`) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [real_sums]) THEN
  REWRITE_TAC[FROM_INTER_NUMSEG_MAX; ARITH_RULE `MAX 0 n = n`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!n. sum(0..n) (f:num->real) <= V` ASSUME_TAC THENL
  [GEN_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   ABBREV_TAC `d = sum(0..n) (f:num->real) - V` THEN
   SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `((\n. sum (0..n) (f:num->real)) ---> V) sequentially` THEN
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   DISCH_THEN(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `n + N:num`) THEN
   ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `sum(0..n) (f:num->real) <= sum(0..n + N) f` MP_TAC THENL
   [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    CONJ_TAC THENL
    [REWRITE_TAC[SUBSET; IN_NUMSEG] THEN ARITH_TAC;
     REWRITE_TAC[IN_DIFF; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
     ASM_MESON_TAC[]];
    ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `((\n. sum (0..n) (f:num->real)) ---> V) sequentially` THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
  EXISTS_TAC `SUC M` THEN X_GEN_TAC `N:num` THEN
  SUBGOAL_THEN `sum(SUC M..SUC M + N) (f:num->real) =
    sum(0..SUC M + N) f - sum(0..M) f` SUBST1_TAC THENL
  [MP_TAC(ISPECL [`f:num->real`; `0`; `M:num`; `SUC M + N`] SUM_COMBINE_R) THEN
   REWRITE_TAC[ARITH_RULE `M + 1 = SUC M`] THEN
   ANTS_TAC THENL [ARITH_TAC; REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `V - sum(0..M) (f:num->real) < e` MP_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `M:num`) THEN
   ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPEC `M:num` (ASSUME `!n. sum(0..n) (f:num->real) <= V`)) THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  MP_TAC(SPEC `SUC M + N` (ASSUME `!n. sum(0..n) (f:num->real) <= V`)) THEN
  REAL_ARITH_TAC);;

(* Helper: shift universal quantifier index range *)
let FORALL_SHIFT_INDEX = prove
 (`!a k (P:num->bool).
    (!j. a <= j /\ j < a + k ==> P j) <=>
    (!j. j < k ==> P (a + j))`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `a + j:num`) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]];
   FIRST_X_ASSUM(MP_TAC o SPEC `j - a:num`) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `a + (j - a):num = j` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[]]]);;

(* Helper: reindex sum(a..a+k) to sum(0..k) with shifted indices *)
let SUM_REINDEX_SHIFT = prove
 (`!a k (f:num->real). sum(a..a+k) f = sum(0..k) (\i. f(a+i))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`a:num`; `f:num->real`; `0`; `k:num`] SUM_OFFSET) THEN
  REWRITE_TAC[ADD_CLAUSES; ADD_SYM]);;

(* Helper: from 0 INTER (m..n) = m..n *)
let FROM_0_INTER_NUMSEG = prove
 (`!m n. from 0 INTER (m..n) = m..n`,
  REWRITE_TAC[EXTENSION; from; IN_INTER; IN_ELIM_THM; IN_NUMSEG] THEN
  ARITH_TAC);;

(* Kolmogorov Convergence Criterion:
   Independent mean-zero variables with summable variance and
   first-crossing hypothesis => series converges a.s. *)
let KOLMOGOROV_CONVERGENCE_CRITERION = prove
 (`!p:A prob_space (X:num->A->real).
    (!n. integrable p (X n)) /\
    (!n. integrable p (\x. X n x pow 2)) /\
    (!n. expectation p (X n) = &0) /\
    (!i j. ~(i = j) ==> covariance p (X i) (X j) = &0) /\
    (!a b k t. a <= k /\ k < b /\ &0 < t ==>
      expectation p (\x. sum(a..k) (\i. X i x) *
        sum(SUC k..b) (\i. X i x) *
        indicator_fn {y:A | y IN prob_carrier p /\
          (!j. a <= j /\ j < k ==> abs(sum(a..j) (\i. X i y)) < t) /\
          abs(sum(a..k) (\i. X i y)) >= t} x) = &0) /\
    real_summable (from 0) (\n. variance p (X n))
    ==> almost_surely p
      {x | (?L. ((\n. sum(0..n) (\i. X i x)) ---> L) sequentially)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Nonneg variance *)
  SUBGOAL_THEN `!n. &0 <= variance (p:A prob_space) ((X:num->A->real) n)`
    (LABEL_TAC "Vnn") THENL
  [GEN_TAC THEN MATCH_MP_TAC VARIANCE_NONNEG THEN
   SUBGOAL_THEN `expectation (p:A prob_space) ((X:num->A->real) n) = &0`
     SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[REAL_SUB_RZERO] THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Tail bound: for any eps, exists a s.t. tail variance < eps *)
  SUBGOAL_THEN `!e. &0 < e ==>
    ?a. !N. sum(a..a+N) (\n. variance (p:A prob_space) ((X:num->A->real) n)) < e`
    (LABEL_TAC "TB") THENL
  [MATCH_MP_TAC REAL_SUMMABLE_TAIL_BOUND THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC `INTERS {(\m:num. {x:A |
    ?a. !k. abs(sum(a..a+k) (\i. (X:num->A->real) i x)) <
      inv(&(SUC m))}) m | m IN (:num)}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC ALMOST_SURELY_COUNTABLE_INTER THEN
   BETA_TAC THEN X_GEN_TAC `m:num` THEN
   REWRITE_TAC[almost_surely] THEN
   ABBREV_TAC `eps = inv(&(SUC m))` THEN
   SUBGOAL_THEN `&0 < eps` (LABEL_TAC "eps_pos") THENL
   [EXPAND_TAC "eps" THEN MATCH_MP_TAC REAL_LT_INV THEN
    REWRITE_TAC[REAL_OF_NUM_LT; LT_0];
    ALL_TAC] THEN
   ABBREV_TAC `D = \a N. {x:A | x IN prob_carrier p /\
     ?k. k <= N /\ abs(sum(a..a+k) (\i. (X:num->A->real) i x)) >= eps}` THEN
   (* D(a,N) is a measurable event *)
   SUBGOAL_THEN `!a N. (D:num->num->A->bool) a N IN prob_events p`
     (LABEL_TAC "Dev") THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "D" THEN
    SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
      (?k. k <= N /\ abs(sum(a..a+k) (\i. (X:num->A->real) i x)) >= eps)} =
      UNIONS(IMAGE (\k. {x:A | x IN prob_carrier p /\
        abs(sum(a..a+k) (\i. X i x)) >= eps}) {k | k <= N})`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; UNIONS_IMAGE; IN_ELIM_THM] THEN
     GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
     ALL_TAC] THEN
    MATCH_MP_TAC PROB_FINITE_UNION_IN_EVENTS THEN CONJ_TAC THENL
    [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
     X_GEN_TAC `k:num` THEN DISCH_TAC THEN
     MATCH_MP_TAC RV_PREIMAGE_GE THEN
     MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN
     SUBGOAL_THEN `(\x:A. sum(a..a+k) (\i. (X:num->A->real) i x)) =
       (\x. sum(0..k) (\i. X (a + i) x))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; SUM_REINDEX_SHIFT]; ALL_TAC] THEN
     MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN REPEAT STRIP_TAC THEN
     MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
     REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC FINITE_IMAGE THEN
     MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..N:num` THEN
     REWRITE_TAC[FINITE_NUMSEG] THEN
     REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN ARITH_TAC];
    ALL_TAC] THEN
   (* D(a,N) SUBSET D(a,SUC N) *)
   SUBGOAL_THEN `!a N. (D:num->num->A->bool) a N SUBSET D a (SUC N)`
     (LABEL_TAC "Dinc") THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "D" THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
   (* Index translation: absolute-index set = relative-index set *)
   SUBGOAL_THEN `!a k. {y:A | y IN prob_carrier p /\
     (!j. a <= j /\ j < a + k ==>
       abs(sum(a..j) (\i. (X:num->A->real) i y)) < eps) /\
     abs(sum(a..a+k) (\i. X i y)) >= eps} =
     {y | y IN prob_carrier p /\
     (!j. j < k ==> abs(sum(a..a+j) (\i. X i y)) < eps) /\
     abs(sum(a..a+k) (\i. X i y)) >= eps}` (LABEL_TAC "Idx") THENL
   [REWRITE_TAC[FORALL_SHIFT_INDEX]; ALL_TAC] THEN
   (* Probability bound: P(D(a,N)) <= sum Var / eps^2 *)
   SUBGOAL_THEN `!a N. prob (p:A prob_space) ((D:num->num->A->bool) a N) <=
     sum(a..a+N) (\n. variance p ((X:num->A->real) n)) / eps pow 2`
     (LABEL_TAC "Dbd") THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "D" THEN
    MATCH_MP_TAC KOLMOGOROV_MAXIMAL_INEQ_SHIFTED THEN
    REPEAT CONJ_TAC THENL
    [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
     REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
     REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
     ASM_MESON_TAC[];
     X_GEN_TAC `k':num` THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPECL
       [`a:num`; `a + N:num`; `a + k':num`; `eps:real`]) THEN
     ANTS_TAC THENL
     [CONJ_TAC THENL [ARITH_TAC; CONJ_TAC THENL
       [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
     REWRITE_TAC[ADD1; FORALL_SHIFT_INDEX] THEN
     MATCH_MP_TAC(MESON[] `(P = Q) ==> P ==> Q`) THEN
     REWRITE_TAC[GSYM ADD_ASSOC];
     ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   (* UNIONS {D(a,N) | N} is an event for each a *)
   SUBGOAL_THEN `!a. UNIONS {(D:num->num->A->bool) a N | N IN (:num)}
     IN prob_events p` (LABEL_TAC "Uev") THENL
   [GEN_TAC THEN MATCH_MP_TAC PROB_COUNTABLE_UNION_IN_EVENTS THEN
    CONJ_TAC THENL
    [REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN
     USE_THEN "Dev" (fun th -> REWRITE_TAC[th]);
     REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC COUNTABLE_IMAGE THEN
     REWRITE_TAC[NUM_COUNTABLE]];
    ALL_TAC] THEN
   (* INTERS {UNIONS {D(a,N) | N} | a} is an event *)
   SUBGOAL_THEN `INTERS {UNIONS {(D:num->num->A->bool) a N |
     N IN (:num)} | a IN (:num)} IN prob_events p` (LABEL_TAC "Iev") THENL
   [MATCH_MP_TAC PROB_COUNTABLE_INTERS_IN_EVENTS THEN REPEAT CONJ_TAC THENL
    [REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
     GEN_TAC THEN DISCH_TAC THEN USE_THEN "Uev" (fun th -> REWRITE_TAC[th]);
     REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC COUNTABLE_IMAGE THEN
     REWRITE_TAC[NUM_COUNTABLE];
     REWRITE_TAC[SIMPLE_IMAGE; IMAGE_EQ_EMPTY; UNIV_NOT_EMPTY]];
    ALL_TAC] THEN
   EXISTS_TAC `INTERS {UNIONS {(D:num->num->A->bool) a N |
     N IN (:num)} | a IN (:num)}` THEN
   CONJ_TAC THENL
   [REWRITE_TAC[null_event] THEN CONJ_TAC THENL
    [USE_THEN "Iev" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
    MATCH_MP_TAC(prove(`!x:real. &0 <= x /\ (!d. &0 < d ==> x <= d)
      ==> x = &0`,
      GEN_TAC THEN STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(&0 < x) ==> x = &0`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x / &2`) THEN ASM_REAL_ARITH_TAC)) THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC PROB_POSITIVE THEN
     USE_THEN "Iev" (fun th -> REWRITE_TAC[th]);
     ALL_TAC] THEN
    X_GEN_TAC `d:real` THEN DISCH_TAC THEN
    REMOVE_THEN "TB" (MP_TAC o SPEC `d * (eps:real) pow 2`) THEN
    ANTS_TAC THENL
    [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `a:num`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `prob (p:A prob_space)
      (UNIONS {(D:num->num->A->bool) a N | N IN (:num)})` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC PROB_MONO THEN
     CONJ_TAC THENL
      [USE_THEN "Iev" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
     CONJ_TAC THENL
      [USE_THEN "Uev" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
     REWRITE_TAC[SUBSET; INTERS_GSPEC; IN_UNIV; IN_ELIM_THM] THEN
     GEN_TAC THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `a:num`) THEN REWRITE_TAC[];
     ALL_TAC] THEN
    MP_TAC(ISPECL [`p:A prob_space`;
      `(D:num->num->A->bool) a`] PROB_CONTINUITY_FROM_BELOW) THEN
    ANTS_TAC THENL
    [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
    EXISTS_TAC `\N. prob (p:A prob_space) ((D:num->num->A->bool) a N)` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    CONJ_TAC THENL
    [FIRST_X_ASSUM(fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `0` THEN X_GEN_TAC `nn:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(a..a+nn) (\n. variance (p:A prob_space)
      ((X:num->A->real) n)) / eps pow 2` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   EXPAND_TAC "D" THEN
   REWRITE_TAC[SUBSET; INTERS_GSPEC; UNIONS_GSPEC; IN_UNIV; IN_ELIM_THM] THEN
   BETA_TAC THEN X_GEN_TAC `y:A` THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   REWRITE_TAC[NOT_EXISTS_THM; NOT_FORALL_THM; REAL_NOT_LT; GSYM real_ge] THEN
   DISCH_TAC THEN X_GEN_TAC `aa:num` THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `aa:num`) THEN
   DISCH_THEN(X_CHOOSE_TAC `kk:num`) THEN
   EXISTS_TAC `kk:num` THEN ASM_REWRITE_TAC[] THEN
   EXISTS_TAC `kk:num` THEN ASM_REWRITE_TAC[LE_REFL];
   (* Branch 2: INTERS {x | sums < inv(SUC m)} SUBSET {x | series converges} *)
   REWRITE_TAC[SUBSET; INTERS_GSPEC; IN_UNIV; IN_ELIM_THM] THEN BETA_TAC THEN
  GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_SERIES_FROM; GSYM real_summable;
              REAL_SUMMABLE_CAUCHY; FROM_0_INTER_NUMSEG] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?n. ~(n = 0) /\ &0 < inv(&n:real) /\ inv(&n) < e / &2`
    (X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THENL
  [REWRITE_TAC[GSYM REAL_ARCH_INV] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:num`) THEN
  EXISTS_TAC `a:num` THEN
  SUBGOAL_THEN `inv(&(SUC m)) < e / &2` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `inv(&m:real)` THEN
   ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
   REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `n:num < m'` THENL
  [ASM_SIMP_TAC[SUM_TRIV_NUMSEG; LT_IMP_LE; REAL_ABS_NUM]; ALL_TAC] THEN
  SUBGOAL_THEN `m':num <= n` ASSUME_TAC THENL
  [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a:num <= m'` ASSUME_TAC THENL
  [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `m' = a:num` THENL
  [ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `n - a:num`) THEN
   SUBGOAL_THEN `a + (n - a) = n:num` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[GSYM real_ge; REAL_NOT_LE] THEN
    DISCH_TAC THEN ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `a:num < m'` ASSUME_TAC THENL
  [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sum(m'..n) (\i. (X:num->A->real) i x) =
    sum(a..n) (\i. X i x) - sum(a..m' - 1) (\i. X i x)`
    SUBST1_TAC THENL
  [MP_TAC(ISPECL [`\i. (X:num->A->real) i x`; `a:num`; `m' - 1`;
    `n:num`] SUM_COMBINE_R) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `m' - 1 + 1 = m':num` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `abs(sum(a..n) (\i. (X:num->A->real) i x)) < inv(&(SUC m))`
    ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `n - a:num`) THEN
   SUBGOAL_THEN `a + (n - a) = n:num` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[GSYM real_ge; REAL_NOT_LE]];
   ALL_TAC] THEN
  SUBGOAL_THEN `abs(sum(a..m' - 1) (\i. (X:num->A->real) i x)) < inv(&(SUC m))`
    ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `m' - 1 - a:num`) THEN
   SUBGOAL_THEN `a + (m' - 1 - a) = m' - 1:num` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[GSYM real_ge; REAL_NOT_LE]];
   ALL_TAC] THEN
  ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Truncation (clamping) infrastructure for Three-Series Theorem            *)
(* ========================================================================= *)

(* Clamp bound: |min(max(x, -c), c)| <= c for c > 0 *)
let CLAMP_BOUND = prove
 (`!x c. &0 < c ==> abs(min (max x (--c)) c) <= c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_min; real_max] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_REAL_ARITH_TAC);;

(* Clamped function is integrable *)
let INTEGRABLE_CLAMP = prove
 (`!p:A prob_space f c. integrable p f
    ==> integrable p (\x. min (max (f x) (--c)) c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_MIN THEN CONJ_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_MAX THEN
   ASM_REWRITE_TAC[INTEGRABLE_CONST];
   REWRITE_TAC[INTEGRABLE_CONST]]);;

(* Square of clamped function is integrable *)
let INTEGRABLE_CLAMP_POW2 = prove
 (`!p:A prob_space f c. &0 < c /\ integrable p f
    ==> integrable p (\x. min (max (f x) (--c)) c pow 2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
  EXISTS_TAC `(c:real) pow 2` THEN CONJ_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
   MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN CONJ_TAC THENL
    [ASM_MESON_TAC[integrable]; REWRITE_TAC[RANDOM_VARIABLE_CONST]];
    REWRITE_TAC[RANDOM_VARIABLE_CONST]];
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   REWRITE_TAC[REAL_ABS_POW] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
   REWRITE_TAC[REAL_ABS_POS] THEN
   MATCH_MP_TAC CLAMP_BOUND THEN ASM_REWRITE_TAC[]]);;

(* Clamped function is a random variable *)
let RANDOM_VARIABLE_CLAMP = prove
 (`!p:A prob_space f c. random_variable p f
    ==> random_variable p (\x. min (max (f x) (--c)) c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN CONJ_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN
   ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST];
   REWRITE_TAC[RANDOM_VARIABLE_CONST]]);;

(* Independence of clamped variables *)
let INDEP_RV_CLAMP = prove
 (`!p:A prob_space X Y c.
    indep_rv p X Y
    ==> indep_rv p (\x. min (max (X x) (--c)) c)
                    (\x. min (max (Y x) (--c)) c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INDEP_RV_MIN_CONST THEN
  MATCH_MP_TAC INDEP_RV_MAX_CONST THEN ASM_REWRITE_TAC[]);;

(* Bound on expectation of clamped function *)
let CLAMP_EXPECTATION_BOUND = prove
 (`!p:A prob_space f c.
     integrable p f /\ &0 < c
     ==> abs(expectation p (\x. min (max (f x) (--c)) c)) <= c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `expectation (p:A prob_space) (\x. abs(min (max (f x) (--c)) c))` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC EXPECTATION_ABS_BOUND THEN
   MATCH_MP_TAC INTEGRABLE_CLAMP THEN ASM_REWRITE_TAC[];
   SUBGOAL_THEN `!x:A. x IN prob_carrier p
      ==> abs(min (max (f x) (--c)) c) <= c` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CLAMP_BOUND THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `\x:A. abs(min (max ((f:A->real) x) (--c)) c)`;
     `(\x:A. c:real)`] EXPECTATION_MONO) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_ABS THEN
     MATCH_MP_TAC INTEGRABLE_CLAMP THEN ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[INTEGRABLE_CONST]];
    REWRITE_TAC[EXPECTATION_CONST; PROB_SPACE] THEN ASM_REAL_ARITH_TAC]]);;

(* Expectation of f - c equals expectation of f minus c *)
let EXPECTATION_SUB_CONST = prove
 (`!p:A prob_space f c.
     integrable p f
     ==> expectation p (\x. f x - c) = expectation p f - c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `f:A->real`; `(\x:A. c:real)`]
    EXPECTATION_SUB) THEN
  ASM_REWRITE_TAC[INTEGRABLE_CONST; EXPECTATION_CONST; PROB_SPACE;
                   REAL_MUL_LID]);;

(* Variance is invariant under constant shift -- corollary of VARIANCE_SHIFT *)
let VARIANCE_SUB_CONST = prove
 (`!p:A prob_space f c.
     integrable p f
     ==> variance p (\x. f x - c) = variance p f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:A. (f:A->real) x - c) = (\x. f x + --c)` SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; real_sub]; ALL_TAC] THEN
  ASM_SIMP_TAC[VARIANCE_SHIFT]);;

(* Bound on centered clamped function *)
let CLAMP_CENTERED_BOUND = prove
 (`!p:A prob_space f c x.
     integrable p f /\ &0 < c /\ x IN prob_carrier p
     ==> abs(min (max (f x) (--c)) c -
             expectation p (\y. min (max (f y) (--c)) c)) <= &2 * c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs(min (max ((f:A->real) x) (--c)) c) <= c`
    ASSUME_TAC THENL
  [MATCH_MP_TAC CLAMP_BOUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `abs(expectation (p:A prob_space) (\y. min (max (f y) (--c)) c)) <= c`
    ASSUME_TAC THENL
  [MATCH_MP_TAC CLAMP_EXPECTATION_BOUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Centered clamped function is integrable *)
let INTEGRABLE_CLAMP_CENTERED = prove
 (`!p:A prob_space f c.
     integrable p f
     ==> integrable p (\x. min (max (f x) (--c)) c -
                             expectation p (\y. min (max (f y) (--c)) c))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_CLAMP THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[INTEGRABLE_CONST]]);;

(* Square of centered clamped function is integrable *)
let INTEGRABLE_CLAMP_CENTERED_POW2 = prove
 (`!p:A prob_space f c.
     integrable p f /\ &0 < c
     ==> integrable p (\x. (min (max (f x) (--c)) c -
                             expectation p (\y. min (max (f y) (--c)) c)) pow 2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
  EXISTS_TAC `(&2 * c) pow 2` THEN CONJ_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
   MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_CLAMP THEN
    ASM_MESON_TAC[integrable];
    REWRITE_TAC[RANDOM_VARIABLE_CONST]];
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   REWRITE_TAC[REAL_ABS_POW] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
   REWRITE_TAC[REAL_ABS_POS] THEN
   MATCH_MP_TAC CLAMP_CENTERED_BOUND THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Borel-Cantelli to almost_surely bridge                                    *)
(* ========================================================================= *)

(* First Borel-Cantelli gives a.s. eventually not in B_n *)
let BOREL_CANTELLI_ALMOST_SURELY = prove
 (`!p:A prob_space B.
     (!n. B n IN prob_events p) /\
     real_summable (from 0) (\n. prob p (B n))
     ==> almost_surely p {x | ?N. !n. N <= n ==> ~(x IN B n)}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[almost_surely] THEN
  EXISTS_TAC `limsup_events (B:num->A->bool)` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[null_event] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LIMSUP_EVENTS_IN_EVENTS THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FIRST_BOREL_CANTELLI THEN ASM_REWRITE_TAC[]];
   REWRITE_TAC[SUBSET; IN_ELIM_THM; limsup_events; IN_INTERS; IN_ELIM_THM;
               NOT_EXISTS_THM] THEN
   X_GEN_TAC `x:A` THEN STRIP_TAC THEN
   X_GEN_TAC `t:A->bool` THEN
   REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
   DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
   REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
   REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; GSYM GE] THEN
   DISCH_THEN(X_CHOOSE_THEN `nn:num` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `(B:num->A->bool) nn` THEN
   ASM_REWRITE_TAC[] THEN
   EXISTS_TAC `nn:num` THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Tail equivalence for series convergence                                   *)
(* ========================================================================= *)

(* If a.s. eventually X_n = Y_n and sum Y_n converges a.s.,
   then sum X_n converges a.s. *)
let TAIL_EQUIVALENCE_CONVERGENCE = prove
 (`!p:A prob_space X Y.
     almost_surely p {x | ?N. !n. N <= n ==> X n x = Y n x} /\
     almost_surely p {x | ?L. ((\n. sum(0..n) (\i. Y i x)) ---> L) sequentially}
     ==> almost_surely p {x | ?L. ((\n. sum(0..n) (\i. X i x)) ---> L) sequentially}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `p:A prob_space` ALMOST_SURELY_SUBSET) THEN
  EXISTS_TAC `{x:A | ?N. !n. N <= n ==> (X:num->A->real) n x = Y n x} INTER
              {x | ?L. ((\n. sum(0..n) (\i. Y i x)) ---> L) sequentially}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC ALMOST_SURELY_INTER THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN REPEAT STRIP_TAC] THEN
  EXISTS_TAC `L + sum(0..N) (\i. (X:num->A->real) i x - Y i x)` THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\n. sum(0..n) (\i. (Y:num->A->real) i x) +
                   sum(0..N) (\i. X i x - Y i x)` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
   EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`\i. (X:num->A->real) i x`; `0`; `N:num`; `n:num`]
     SUM_COMBINE_R) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(ISPECL [`\i. (Y:num->A->real) i x`; `0`; `N:num`; `n:num`]
     SUM_COMBINE_R) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `sum(N + 1..n) (\i. (X:num->A->real) i x) =
                 sum(N + 1..n) (\i. Y i x)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
   REWRITE_TAC[SUM_SUB_NUMSEG] THEN ASM_REAL_ARITH_TAC;
   MATCH_MP_TAC REALLIM_ADD THEN
   CONJ_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[REALLIM_CONST]]]);;

(* ========================================================================= *)
(* Kolmogorov Three-Series Theorem (Sufficiency)                             *)
(* ========================================================================= *)

(* The sufficiency direction of Kolmogorov's Three-Series Theorem:
   If the three series conditions hold (tail probabilities, expectations,
   and variances of truncated variables), plus the centered truncations
   are uncorrelated and satisfy the Kolmogorov cross-term condition,
   then the original series converges almost surely.

   The uncorrelated and cross-term conditions follow from mutual independence
   of the X_n; they are stated as hypotheses here because the formalization
   works with pairwise indep_rv rather than mutually_indep_rv. *)
let THREE_SERIES_SUFFICIENCY = prove
 (`!p:A prob_space X c.
     &0 < c /\
     (!n. integrable p (X n)) /\
     real_summable (from 0)
       (\n. prob p {x | x IN prob_carrier p /\ abs(X n x) > c}) /\
     real_summable (from 0)
       (\n. expectation p (\x. min (max (X n x) (--c)) c)) /\
     real_summable (from 0)
       (\n. variance p (\x. min (max (X n x) (--c)) c)) /\
     (!i j. ~(i = j)
       ==> covariance p
             (\x. min (max (X i x) (--c)) c -
                  expectation p (\y. min (max (X i y) (--c)) c))
             (\x. min (max (X j x) (--c)) c -
                  expectation p (\y. min (max (X j y) (--c)) c)) = &0) /\
     (!a b k t.
        a <= k /\ k < b /\ &0 < t
        ==> expectation p
            (\x. sum(a..k)
                   (\i. min (max (X i x) (--c)) c -
                        expectation p (\y. min (max (X i y) (--c)) c)) *
                 sum(SUC k..b)
                   (\i. min (max (X i x) (--c)) c -
                        expectation p (\y. min (max (X i y) (--c)) c)) *
                 indicator_fn
                   {z | z IN prob_carrier p /\
                        (!j. a <= j /\ j < k
                          ==> abs(sum(a..j)
                                (\i. min (max (X i z) (--c)) c -
                                     expectation p (\y. min (max (X i y) (--c)) c))) < t) /\
                        abs(sum(a..k)
                              (\i. min (max (X i z) (--c)) c -
                                   expectation p (\y. min (max (X i y) (--c)) c))) >= t} x) = &0)
     ==> almost_surely p
         {x | ?L. ((\n. sum(0..n) (\i. X i x)) ---> L) sequentially}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "tail_prob") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "exp_sum") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "var_sum") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "uncorr") (LABEL_TAC "cross")) THEN
  (* Step 1: Reduce to sum of clamped variables via tail equivalence *)
  MATCH_MP_TAC(ISPEC `p:A prob_space` TAIL_EQUIVALENCE_CONVERGENCE) THEN
  EXISTS_TAC `\n x. min (max ((X:num->A->real) n x) (--c)) c` THEN
  CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN CONJ_TAC THENL
  [(* Step 1a: a.s. eventually X_n = clamp(X_n) via Borel-Cantelli *)
   MATCH_MP_TAC(ISPEC `p:A prob_space` ALMOST_SURELY_SUBSET) THEN
   EXISTS_TAC `{x:A | ?N. !n. N <= n
     ==> ~(x IN {y | y IN prob_carrier p /\ abs((X:num->A->real) n y) > c})}` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC BOREL_CANTELLI_ALMOST_SURELY THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN
    SUBGOAL_THEN `{y:A | y IN prob_carrier p /\ abs(X (n:num) y) > c} =
                  {y | y IN prob_carrier p /\ (\y. abs((X:num->A->real) n y)) y > c}`
      SUBST1_TAC THENL
    [REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC RV_LEVEL_GT_IN_EVENTS THEN
    MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN
    MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
    CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `nn:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `nn:num`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_gt; REAL_NOT_LT] THEN DISCH_TAC THEN
    REWRITE_TAC[real_min; real_max] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* Step 2: Reduce sum(clamp) to sum(centered clamp) + sum(expectations) *)
  CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
  MATCH_MP_TAC(ISPEC `p:A prob_space` ALMOST_SURELY_SUBSET) THEN
  EXISTS_TAC
    `{x:A | ?L. ((\n. sum(0..n) (\i. min (max ((X:num->A->real) i x) (--c)) c -
                 expectation p (\y. min (max (X i y) (--c)) c))) ---> L)
                sequentially}` THEN
  CONJ_TAC THENL
  [(* Step 2a: sum(centered clamp) converges a.s. via Kolmogorov criterion *)
   MATCH_MP_TAC KOLMOGOROV_CONVERGENCE_CRITERION THEN
   CONV_TAC(DEPTH_CONV BETA_CONV) THEN
   (* Condition 1: centered clamp is integrable *)
   CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_CLAMP_CENTERED THEN
    CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* Condition 2: square of centered clamp is integrable *)
   CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_CLAMP_CENTERED_POW2 THEN
    CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* Condition 3: E[centered clamp] = 0 *)
   CONJ_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN
      `expectation (p:A prob_space)
        (\x. min (max ((X:num->A->real) n x) (--c)) c -
             expectation p (\y. min (max (X n y) (--c)) c)) =
       expectation p (\x. min (max (X n x) (--c)) c) -
       expectation p (\y. min (max (X n y) (--c)) c)`
      SUBST1_TAC THENL
    [MATCH_MP_TAC EXPECTATION_SUB_CONST THEN
     MATCH_MP_TAC INTEGRABLE_CLAMP THEN
     CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC(REAL_ARITH `a = b ==> a - b = &0`) THEN
     AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM]];
    ALL_TAC] THEN
   (* Condition 4: uncorrelated *)
   CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   (* Condition 5: cross-term *)
   CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   (* Condition 6: summable variance *)
   SUBGOAL_THEN
     `!n. variance (p:A prob_space)
            (\x. min (max ((X:num->A->real) n x) (--c)) c -
                 expectation p (\y. min (max (X n y) (--c)) c)) =
          variance p (\x. min (max (X n x) (--c)) c)`
     (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC VARIANCE_SUB_CONST THEN
    MATCH_MP_TAC INTEGRABLE_CLAMP THEN
    CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]];
   (* Step 2b: convergence of sum(Z_n) implies convergence of sum(clamp) *)
   REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN
     `?M. ((\n. sum(0..n)
       (\i. expectation (p:A prob_space) (\y. min(max((X:num->A->real) i y)(--c)) c))) ---> M)
      sequentially` STRIP_ASSUME_TAC THENL
   [USE_THEN "exp_sum" MP_TAC THEN
    REWRITE_TAC[real_summable; real_sums; FROM_INTER_NUMSEG] THEN
    MESON_TAC[];
    ALL_TAC] THEN
   EXISTS_TAC `L + M:real` THEN
   MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
   EXISTS_TAC `\n. sum(0..n)
     (\i. min (max ((X:num->A->real) i x) (--c)) c -
          expectation p (\y. min (max (X i y) (--c)) c)) +
     sum(0..n) (\i. expectation p (\y. min (max (X i y) (--c)) c))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REALLIM_ADD THEN ASM_REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* Kolmogorov Three-Series Theorem (Necessity): Supporting Lemmas            *)
(* ========================================================================= *)

(* Convergent series have terms that eventually vanish *)
let CONVERGENT_SERIES_TERMS_VANISH = prove
 (`!p:A prob_space (X:num->A->real) c.
    &0 < c /\
    almost_surely p {x | ?L. ((\n. sum(0..n) (\i. X i x)) ---> L) sequentially}
    ==> almost_surely p {x | ?N. !n. N <= n ==> abs(X n x) <= c}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `p:A prob_space` ALMOST_SURELY_SUBSET) THEN
  EXISTS_TAC `{x:A | ?L. ((\n. sum(0..n) (\i. (X:num->A->real) i x)) ---> L)
              sequentially}` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  DISCH_THEN(X_CHOOSE_TAC `L:real`) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `c / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N + 1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(X:num->A->real) n x =
    sum(0..n) (\i. X i x) - sum(0..PRE n) (\i. X i x)` SUBST1_TAC THENL
  [MP_TAC(ISPECL [`\i. (X:num->A->real) i x`; `0`; `PRE n`; `n:num`]
     SUM_COMBINE_R) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `PRE n + 1 = n` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[NUMSEG_SING; SUM_SING] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `abs(sum(0..n) (\i. (X:num->A->real) i x) - L) < c / &2`
    ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `abs(sum(0..PRE n) (\i. (X:num->A->real) i x) - L) < c / &2`
    ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `PRE n`) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]];
   ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Utility: almost_surely events are nonempty (contain some x in prob_carrier) *)
let ALMOST_SURELY_NONEMPTY = prove
 (`!p:A prob_space s.
    almost_surely p s
    ==> ?x. x IN prob_carrier p /\ x IN s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[almost_surely; null_event] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `prob_carrier (p:A prob_space) SUBSET (n:A->bool)` ASSUME_TAC THENL
  [MATCH_MP_TAC SUBSET_TRANS THEN
   EXISTS_TAC `{x:A | x IN prob_carrier p /\ ~(x IN s)}` THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
   DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `prob_carrier (p:A prob_space)`; `n:A->bool`]
    PROB_MONO) THEN
  ASM_REWRITE_TAC[PROB_SPACE; PROB_CARRIER_IN_EVENTS] THEN
  ASM_REAL_ARITH_TAC);;

(* Reduction to bounded case: First BC gives Y_n = X_n eventually,
   then tail equivalence gives sum Y_n converges a.s. *)
let THREE_SERIES_REDUCTION = prove
 (`!p:A prob_space (X:num->A->real) c.
    &0 < c /\
    (!n. integrable p (X n)) /\
    real_summable (from 0)
      (\n. prob p {x | x IN prob_carrier p /\ abs(X n x) > c}) /\
    almost_surely p {x | ?L. ((\n. sum(0..n) (\i. X i x)) ---> L) sequentially}
    ==> almost_surely p
      {x | ?L. ((\n. sum(0..n) (\i. min(max(X i x) (--c)) c)) ---> L)
               sequentially}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `\n. {x:A | x IN prob_carrier p /\ abs((X:num->A->real) n x) > c}`]
    BOREL_CANTELLI_ALMOST_SURELY) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [GEN_TAC THEN CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
    MATCH_MP_TAC RV_LEVEL_GT_IN_EVENTS THEN
    MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN
    MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
    CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `\i:num. \x:A. min (max ((X:num->A->real) i x) (--c)) c`;
    `X:num->A->real`]
    TAIL_EQUIVALENCE_CONVERGENCE) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN(fun th -> MATCH_MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ISPEC `p:A prob_space` ALMOST_SURELY_SUBSET) THEN
  EXISTS_TAC `{x:A | ?N. !n. N <= n
    ==> ~(x IN {x | x IN prob_carrier p /\ abs((X:num->A->real) n x) > c})}` THEN
  ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[real_gt; REAL_NOT_LT; DE_MORGAN_THM] THEN
  STRIP_TAC THEN REWRITE_TAC[real_min; real_max] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_REAL_ARITH_TAC);;

(* Cauchy-Schwarz inequality for expectations:
   E[XY]^2 <= E[X^2] * E[Y^2] *)
let EXPECTATION_CAUCHY_SCHWARZ = prove
 (`!p:A prob_space X Y.
     integrable p X /\ integrable p Y /\
     integrable p (\x. X x pow 2) /\ integrable p (\x. Y x pow 2) /\
     integrable p (\x. X x * Y x)
     ==> expectation p (\x. X x * Y x) pow 2 <=
         expectation p (\x. X x pow 2) * expectation p (\x. Y x pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `a = expectation p (\x:A. (X:A->real) x pow 2)` THEN
  ABBREV_TAC `b = expectation p (\x:A. (X:A->real) x * (Y:A->real) x)` THEN
  ABBREV_TAC `cc = expectation p (\x:A. (Y:A->real) x pow 2)` THEN
  SUBGOAL_THEN `!t:real. &0 <= a - &2 * b * t + cc * t pow 2` ASSUME_TAC THENL
  [X_GEN_TAC `t:real` THEN
   SUBGOAL_THEN `a - &2 * b * t + cc * t pow 2 =
     expectation (p:A prob_space) (\x. ((X:A->real) x - t * (Y:A->real) x) pow 2)`
     SUBST1_TAC THENL
   [SUBGOAL_THEN
      `(\x:A. ((X:A->real) x - t * (Y:A->real) x) pow 2) =
       (\x. X x pow 2 + (t pow 2 * Y x pow 2 - &2 * t * X x * Y x))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `integrable (p:A prob_space)
      (\x. t pow 2 * (Y:A->real) x pow 2 - &2 * t * (X:A->real) x * Y x)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `(\x:A. &2 * t * (X:A->real) x * (Y:A->real) x) =
          (\x. (&2 * t) * (X x * Y x))` SUBST1_TAC THENL
          [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC;
           MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`p:A prob_space`; `\x:A. (X:A->real) x pow 2`;
      `\x:A. t pow 2 * (Y:A->real) x pow 2 - &2 * t * (X:A->real) x * Y x`]
      EXPECTATION_ADD) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `\x:A. t pow 2 * (Y:A->real) x pow 2`;
      `\x:A. &2 * t * (X:A->real) x * (Y:A->real) x`] EXPECTATION_SUB) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `(\x:A. &2 * t * (X:A->real) x * (Y:A->real) x) =
          (\x. (&2 * t) * (X x * Y x))` SUBST1_TAC THENL
          [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC;
           MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `expectation (p:A prob_space) (\x. t pow 2 * (Y:A->real) x pow 2) =
      t pow 2 * cc` SUBST1_TAC THENL
     [TRANS_TAC EQ_TRANS
        `(t pow 2) * expectation (p:A prob_space) (\x:A. (Y:A->real) x pow 2)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC EXPECTATION_CMUL THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `expectation (p:A prob_space)
      (\x. &2 * t * (X:A->real) x * (Y:A->real) x) = &2 * t * b` SUBST1_TAC THENL
     [SUBGOAL_THEN `(\x:A. &2 * t * (X:A->real) x * (Y:A->real) x) =
        (\x. (&2 * t) * (X x * Y x))` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC;
        TRANS_TAC EQ_TRANS
          `(&2 * t) * expectation (p:A prob_space) (\x:A. (X:A->real) x * (Y:A->real) x)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC EXPECTATION_CMUL THEN ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]];
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    MATCH_MP_TAC EXPECTATION_POS THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\x:A. ((X:A->real) x - t * (Y:A->real) x) pow 2) =
        (\x. X x pow 2 + (t pow 2 * Y x pow 2 - &2 * t * X x * Y x))` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
         [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
          SUBGOAL_THEN `(\x:A. &2 * t * (X:A->real) x * (Y:A->real) x) =
            (\x. (&2 * t) * (X x * Y x))` SUBST1_TAC THENL
            [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC;
             MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]]]];
      GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_LE_POW_2]]];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= a /\ &0 <= cc` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THENL
    [EXPAND_TAC "a" THEN MATCH_MP_TAC EXPECTATION_POS THEN ASM_REWRITE_TAC[] THEN
     GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_LE_POW_2];
     EXPAND_TAC "cc" THEN MATCH_MP_TAC EXPECTATION_POS THEN ASM_REWRITE_TAC[] THEN
     GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_LE_POW_2]];
   ALL_TAC] THEN
  ASM_CASES_TAC `cc = &0` THENL
  [SUBGOAL_THEN `b = &0` SUBST1_TAC THENL
    [MATCH_MP_TAC(REAL_ARITH `~(&0 < b) /\ ~(b < &0) ==> b = &0`) THEN
     CONJ_TAC THEN DISCH_TAC THENL
      [MP_TAC(SPEC `&2 * b` REAL_ARCH) THEN
       ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
       DISCH_THEN(MP_TAC o SPEC `a:real`) THEN
       DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `&n`) THEN
       ASM_REWRITE_TAC[REAL_POW_2; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID] THEN
       UNDISCH_TAC `a < &n * (&2 * b)` THEN REAL_ARITH_TAC;
       MP_TAC(SPEC `&2 * --b` REAL_ARCH) THEN
       ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
       DISCH_THEN(MP_TAC o SPEC `a:real`) THEN
       DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `-- &n`) THEN
       ASM_REWRITE_TAC[REAL_POW_2; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID] THEN
       UNDISCH_TAC `a < &n * (&2 * --b)` THEN REAL_ARITH_TAC];
    ASM_REWRITE_TAC[REAL_POW_2; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LE_REFL]];
   SUBGOAL_THEN `&0 < cc` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `!t:real. &0 <= a - &2 * b * t + cc * t pow 2` THEN
   DISCH_THEN(MP_TAC o SPEC `(b:real) / cc`) THEN
   SUBGOAL_THEN `a - &2 * b * b / cc + cc * (b / cc) pow 2 =
     (a * cc - b pow 2) / cc` SUBST1_TAC THENL
    [UNDISCH_TAC `~(cc = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
   DISCH_TAC THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= a * cc - b pow 2 ==> b pow 2 <= a * cc`) THEN
   SUBGOAL_THEN `&0 * cc <= a * cc - b pow 2` MP_TAC THENL
    [ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_MUL_LZERO] THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[REAL_MUL_LZERO]]]);;

(* Expectation split over an event: E[f] = E[f*1_A] + E[f*1_{A^c}] *)
let EXPECTATION_SPLIT = prove
 (`!p:A prob_space f (a:A->bool).
     integrable p f /\ a IN prob_events p
     ==> expectation p f = expectation p (\x. f x * indicator_fn a x) +
         expectation p (\x. f x * indicator_fn (prob_carrier p DIFF a) x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x. (f:A->real) x * indicator_fn a x)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(prob_carrier (p:A prob_space) DIFF a) IN prob_events p` ASSUME_TAC THENL
  [MATCH_MP_TAC PROB_COMPL_IN_EVENTS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x. (f:A->real) x * indicator_fn (prob_carrier p DIFF a) x)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (\x. (f:A->real) x * indicator_fn a x) +
    expectation p (\x. f x * indicator_fn (prob_carrier p DIFF a) x) =
    expectation p (\x. f x * indicator_fn a x + f x * indicator_fn (prob_carrier p DIFF a) x)` SUBST1_TAC THENL
  [CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXPECTATION_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EXPECTATION_EXT THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  REWRITE_TAC[indicator_fn; IN_DIFF] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(x:A) IN a` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Paley-Zygmund inequality:
   If X >= 0 and E[X] > 0 then for 0 <= theta < 1,
   (1-theta)^2 * E[X]^2 <= E[X^2] * P(X >= theta*E[X]) *)
let PALEY_ZYGMUND = prove
 (`!p:A prob_space X theta.
     integrable p X /\
     integrable p (\x. X x pow 2) /\
     (!x. x IN prob_carrier p ==> &0 <= X x) /\
     &0 < expectation p X /\
     &0 <= theta /\ theta < &1
     ==> ((&1 - theta) pow 2) * (expectation p X) pow 2 <=
         expectation p (\x. X x pow 2) *
         prob p {x | x IN prob_carrier p /\ X x >= theta * expectation p X}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `mu = expectation (p:A prob_space) (X:A->real)` THEN
  ABBREV_TAC `a:A->bool = {x | x IN prob_carrier (p:A prob_space) /\ (X:A->real) x >= theta * mu}` THEN
  SUBGOAL_THEN `(a:A->bool) IN prob_events (p:A prob_space)` ASSUME_TAC THENL
  [EXPAND_TAC "a" THEN MATCH_MP_TAC RV_LEVEL_GE_IN_EVENTS THEN
   MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x. (X:A->real) x * indicator_fn (a:A->bool) x)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(prob_carrier (p:A prob_space) DIFF a) IN prob_events p` ASSUME_TAC THENL
  [MATCH_MP_TAC PROB_COMPL_IN_EVENTS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x. (X:A->real) x * indicator_fn (prob_carrier p DIFF a) x)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Pointwise bound: on carrier, X*1_{A^c} <= theta*mu *)
  SUBGOAL_THEN `!x:A. x IN prob_carrier (p:A prob_space)
    ==> (X:A->real) x * indicator_fn (prob_carrier p DIFF a) x <= theta * mu`
    ASSUME_TAC THENL
  [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   REWRITE_TAC[indicator_fn; IN_DIFF] THEN ASM_REWRITE_TAC[] THEN
   COND_CASES_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
     EXPAND_TAC "a" THEN REWRITE_TAC[IN_ELIM_THM] THEN
     ASM_REWRITE_TAC[real_ge; REAL_NOT_LE] THEN
     DISCH_TAC THEN REWRITE_TAC[REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
     REWRITE_TAC[REAL_MUL_RZERO] THEN
     MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (\x. (X:A->real) x * indicator_fn (prob_carrier p DIFF a) x) <=
    theta * mu` ASSUME_TAC THENL
  [TRANS_TAC REAL_LE_TRANS `expectation (p:A prob_space) (\x:A. theta * mu)` THEN
   CONJ_TAC THENL
    [MATCH_MP_TAC EXPECTATION_MONO THEN ASM_REWRITE_TAC[INTEGRABLE_CONST];
     REWRITE_TAC[EXPECTATION_CONST; REAL_LE_REFL]];
   ALL_TAC] THEN
  (* Step 1: (1-theta)*mu <= E[X*1_A] *)
  SUBGOAL_THEN `(&1 - theta) * mu <=
    expectation (p:A prob_space) (\x. (X:A->real) x * indicator_fn (a:A->bool) x)` ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `a:A->bool`] EXPECTATION_SPLIT) THEN
   ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `expectation (p:A prob_space) (\x. (X:A->real) x * indicator_fn (prob_carrier p DIFF a) x) <= theta * mu` THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Step 2: E[X*1_A]^2 <= E[X^2]*P(A) by Cauchy-Schwarz *)
  SUBGOAL_THEN `expectation (p:A prob_space) (\x. (X:A->real) x * indicator_fn (a:A->bool) x) pow 2 <=
    expectation p (\x. X x pow 2) * prob p a` ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `indicator_fn (a:A->bool)`]
     EXPECTATION_CAUCHY_SCHWARZ) THEN
   CONV_TAC(DEPTH_CONV BETA_CONV) THEN
   SUBGOAL_THEN `(\x:A. indicator_fn (a:A->bool) x pow 2) = indicator_fn a`
     (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[FUN_EQ_THM; indicator_fn] THEN GEN_TAC THEN
     COND_CASES_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[EXPECTATION_INDICATOR] THEN
   DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Combine: (1-theta)^2*mu^2 <= E[X*1_A]^2 <= E[X^2]*P(A) *)
  TRANS_TAC REAL_LE_TRANS
    `expectation (p:A prob_space) (\x. (X:A->real) x * indicator_fn (a:A->bool) x) pow 2` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_POW_MUL] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;

(* Nonneg divergent series has unbounded partial sums *)
let NONNEG_DIVERGENT_UNBOUNDED = prove
 (`!f. (!n. &0 <= f n) /\ ~real_summable (from 0) f
    ==> !B. ?N. B < sum(0..N) f`,
  REPEAT STRIP_TAC THEN
  (* Contrapositive: if partial sums bounded, then convergent by
     monotone bounded convergence *)
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
  REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `~real_summable (from 0) (f:num->real)` THEN
  REWRITE_TAC[real_summable; real_sums; FROM_INTER_NUMSEG] THEN
  (* Partial sums are monotone increasing and bounded *)
  SUBGOAL_THEN `!n:num. sum(0..n) (f:num->real) <= sum(0..SUC n) f`
    ASSUME_TAC THENL
  [GEN_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x <= x + y`) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Use monotone bounded convergence *)
  MP_TAC(ISPEC `\n:num. sum(0..n) (f:num->real)` CONVERGENT_REAL_BOUNDED_MONOTONE) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [REWRITE_TAC[real_bounded; FORALL_IN_IMAGE; IN_UNIV] THEN
    EXISTS_TAC `abs(B:real) + &1` THEN
    GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= B ==> abs x <= abs B + &1`) THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[]];
    DISJ1_TAC THEN ASM_REWRITE_TAC[]];
   DISCH_THEN(X_CHOOSE_TAC `L:real`) THEN
   EXISTS_TAC `L:real` THEN ASM_REWRITE_TAC[]]);;

(* A finite sequence of reals is bounded *)
let FINITE_REAL_SEQUENCE_BOUNDED = prove
 (`!(f:num->real) N. ?B:real. !n. n < N ==> abs(f n) <= B`,
  GEN_TAC THEN INDUCT_TAC THENL
  [EXISTS_TAC `&0` THEN REWRITE_TAC[LT];
   FIRST_X_ASSUM(X_CHOOSE_TAC `B0:real`) THEN
   EXISTS_TAC `max B0 (abs((f:num->real) N))` THEN
   X_GEN_TAC `m:num` THEN REWRITE_TAC[LT] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `x <= a ==> x <= max a b`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* A convergent real sequence is bounded by a natural number *)
let REALLIM_IMP_BOUNDED_NUM = prove
 (`!f:num->real L.
     (f ---> L) sequentially ==> ?K:num. !n. abs(f n) <= &K`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  MP_TAC(SPECL [`f:num->real`; `N:num`] FINITE_REAL_SEQUENCE_BOUNDED) THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  MP_TAC(SPEC `abs(B) + abs(L:real) + &1` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `K:num`) THEN
  EXISTS_TAC `K:num` THEN X_GEN_TAC `n:num` THEN
  ASM_CASES_TAC `n:num < N` THENL
  [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B:real` THEN
   CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
   MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(L:real) + &1` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `abs(x - l) < &1 ==> abs x <= abs l + &1`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ASM_REAL_ARITH_TAC]]);;

(* Helper: Paley-Zygmund gives a lower bound on P(S_n^2 >= E[S_n^2]/2) *)
let PALEY_ZYGMUND_LOWER_BOUND = prove
 (`!p:A prob_space (Z:num->A->real) C n.
    &0 < C /\
    integrable p (\x. sum(0..n) (\i. Z i x) pow 2) /\
    integrable p (\x. sum(0..n) (\i. Z i x) pow 4) /\
    expectation p (\x. sum(0..n) (\i. Z i x) pow 4) <=
      C * expectation p (\x. sum(0..n) (\i. Z i x) pow 2) pow 2 /\
    &0 < expectation p (\x. sum(0..n) (\i. Z i x) pow 2)
    ==> inv(&4 * C) <=
        prob p {x | x IN prob_carrier p /\
          sum(0..n) (\i. Z i x) pow 2 >=
          inv(&2) * expectation p (\x. sum(0..n) (\i. Z i x) pow 2)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `\x:A. sum(0..n) (\i. (Z:num->A->real) i x) pow 2`;
    `inv(&2)`] PALEY_ZYGMUND) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV THEN REAL_ARITH_TAC;
    CONV_TAC REAL_RAT_REDUCE_CONV];
   ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - inv(&2)) pow 2 = inv(&4)` SUBST1_TAC THENL
  [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[REAL_INV_MUL] THEN DISCH_TAC THEN
  ABBREV_TAC `E1 = expectation (p:A prob_space)
    (\x:A. sum(0..n) (\i. (Z:num->A->real) i x) pow 2)` THEN
  ABBREV_TAC `E4 = expectation (p:A prob_space)
    (\x:A. sum(0..n) (\i. (Z:num->A->real) i x) pow 4)` THEN
  ABBREV_TAC `P0 = prob (p:A prob_space)
    {x | x IN prob_carrier p /\
     sum(0..n) (\i. (Z:num->A->real) i x) pow 2 >=
     inv(&2) * E1}` THEN
  SUBGOAL_THEN `&0 <= P0` ASSUME_TAC THENL
  [EXPAND_TAC "P0" THEN MATCH_MP_TAC PROB_POSITIVE THEN
   MATCH_MP_TAC RV_LEVEL_GE_IN_EVENTS THEN
   MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `inv(&4) <= C * P0` ASSUME_TAC THENL
  [SUBGOAL_THEN `inv(&4) * E1 pow 2 <= (C * P0) * E1 pow 2`
     MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(E4:real) * P0` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(C * P0) * E1 pow 2 = (C * E1 pow 2) * (P0:real)`
      SUBST1_TAC THENL
    [REWRITE_TAC[REAL_MUL_AC]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ; REAL_POW_LT]];
   ALL_TAC] THEN
  REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[]);;

(* Helper: {x | ?n. S_n(x)^2 > &K} is an event *)
let PROB_INDEXED_UNION_EVENTS_LEMMA = prove
 (`!p:A prob_space (Z:num->A->real) K.
    (!n. integrable p (\x. sum(0..n) (\i. Z i x) pow 2))
    ==> {x | x IN prob_carrier p /\
         ?n:num. sum(0..n) (\i. Z i x) pow 2 > &K} IN prob_events p`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!n:num t. {x:A | x IN prob_carrier p /\
    sum(0..n) (\i. (Z:num->A->real) i x) pow 2 > t} IN prob_events p`
    ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN MATCH_MP_TAC RV_LEVEL_GT_IN_EVENTS THEN
   MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\
      ?n:num. sum(0..n) (\i. (Z:num->A->real) i x) pow 2 > &K} =
     UNIONS {(\n. {x | x IN prob_carrier p /\
       sum(0..n) (\i. Z i x) pow 2 > &K}) n | n IN (:num)}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIONS] THEN
   X_GEN_TAC `y:A` THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `m:num`)) THEN
    EXISTS_TAC `{x:A | x IN prob_carrier p /\
      sum(0..m) (\i. (Z:num->A->real) i x) pow 2 > &K}` THEN
    CONJ_TAC THENL
    [EXISTS_TAC `m:num` THEN REWRITE_TAC[IN_UNIV] THEN
     GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM];
     REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]];
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]];
   MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN
   REWRITE_TAC[] THEN ASM_REWRITE_TAC[]]);;

(* Helper: convergent partial sums implies y in INTERS is in null event *)
let PARTIAL_SUM_INTERS_SUBSET_NULL = prove
 (`!p:A prob_space (Z:num->A->real) ne.
    (!n. integrable p (\x. sum(0..n) (\i. Z i x) pow 2)) /\
    null_event p ne /\
    {x | x IN prob_carrier p /\
      ~(x IN {x | ?L. ((\n. sum(0..n) (\i. Z i x)) ---> L) sequentially})}
      SUBSET ne /\
    (!K. {x | x IN prob_carrier p /\
         ?n:num. sum(0..n) (\i. Z i x) pow 2 > &K} IN prob_events p)
    ==> INTERS {{x | x IN prob_carrier p /\
          ?n':num. sum(0..n') (\i. Z i x) pow 2 > &n} |
          n IN (:num)} SUBSET ne`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; IN_INTERS; IN_ELIM_THM; IN_UNIV] THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `y:A IN prob_carrier p` ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC
     `{x:A | x IN prob_carrier p /\
       ?n':num. sum(0..n') (\i. (Z:num->A->real) i x) pow 2 > &0}`) THEN
   ANTS_TAC THENL
   [EXISTS_TAC `0` THEN REFL_TAC;
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `y:A IN {x:A | x IN prob_carrier p /\
    ~(x IN {x | ?L. ((\n. sum(0..n) (\i. (Z:num->A->real) i x)) ---> L)
      sequentially})}` MP_TAC THENL
  [ALL_TAC; ASM SET_TAC[]] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `L:real`) THEN
  MP_TAC(SPECL [`\n:num. sum(0..n)
    (\i. (Z:num->A->real) i (y:A))`; `L:real`]
    REALLIM_IMP_BOUNDED_NUM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `K:num`) THEN
  UNDISCH_TAC `!t:A->bool. (?n. t = {x | x IN prob_carrier p /\
    (?n'. sum (0..n') (\i. (Z:num->A->real) i x) pow 2 > &n)})
    ==> y IN t` THEN
  DISCH_THEN(MP_TAC o SPEC `{x:A | x IN prob_carrier p /\
    (?n':num. sum (0..n') (\i. (Z:num->A->real) i x) pow 2 >
      &(K * K + 1))}`) THEN
  ANTS_TAC THENL
  [EXISTS_TAC `K * K + 1` THEN REFL_TAC; ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_TAC `m:num`)) THEN
  SUBGOAL_THEN `sum (0..m) (\i. (Z:num->A->real) i (y:A)) pow 2
    <= (&K) pow 2` MP_TAC THENL
  [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
   MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
   ASM_SIMP_TAC[REAL_ARITH `abs(&K) = &K`]; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN
  UNDISCH_TAC `sum (0..m) (\i. (Z:num->A->real) i (y:A)) pow 2 >
    &(K * K + 1)` THEN
  REWRITE_TAC[REAL_POW_2; GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
  REAL_ARITH_TAC);;

(* Helper: a.s. convergence implies P(S_n^2 > K) -> 0 *)
let PARTIAL_SUM_LEVEL_PROB_VANISHES = prove
 (`!p:A prob_space (Z:num->A->real).
    (!n. integrable p (\x. sum(0..n) (\i. Z i x) pow 2)) /\
    almost_surely p
      {x | ?L. ((\n. sum(0..n) (\i. Z i x)) ---> L) sequentially}
    ==> ((\K. prob p {x | x IN prob_carrier p /\
              ?n:num. sum(0..n) (\i. Z i x) pow 2 > &K})
         ---> &0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [almost_surely]) THEN
  DISCH_THEN(X_CHOOSE_THEN `ne:A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!K. {x:A | x IN prob_carrier p /\
    ?n:num. sum(0..n) (\i. (Z:num->A->real) i x) pow 2 > &K}
    IN prob_events p` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC PROB_INDEXED_UNION_EVENTS_LEMMA THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!K. {x:A | x IN prob_carrier p /\
    ?n:num. sum(0..n) (\i. (Z:num->A->real) i x) pow 2 > &(SUC K)}
    SUBSET
    {x | x IN prob_carrier p /\
    ?n. sum(0..n) (\i. Z i x) pow 2 > &K}` ASSUME_TAC THENL
  [GEN_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
   X_GEN_TAC `y:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   EXISTS_TAC `n:num` THEN
   UNDISCH_TAC
     `sum(0..n) (\i. (Z:num->A->real) i (y:A)) pow 2 > &(SUC K)` THEN
   REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  MP_TAC(ISPEC `p:A prob_space` PROB_CONTINUITY_FROM_ABOVE) THEN
  DISCH_THEN(MP_TAC o SPEC
    `\K:num. {x:A | x IN prob_carrier p /\
      ?n:num. sum(0..n) (\i. (Z:num->A->real) i x) pow 2 > &K}`) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `prob (p:A prob_space)
    (INTERS {{x:A | x IN prob_carrier p /\
      ?n':num. sum(0..n') (\i. (Z:num->A->real) i x) pow 2 > &n} |
      n IN (:num)}) = &0` ASSUME_TAC THENL
  [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC PROB_POSITIVE THEN
    MATCH_MP_TAC PROB_INDEXED_INTER_IN_EVENTS THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `prob (p:A prob_space) (ne:A->bool)` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC PROB_MONO THEN CONJ_TAC THENL
     [MATCH_MP_TAC PROB_INDEXED_INTER_IN_EVENTS THEN ASM_REWRITE_TAC[];
      CONJ_TAC THENL
      [UNDISCH_TAC `null_event (p:A prob_space) (ne:A->bool)` THEN
       REWRITE_TAC[null_event] THEN MESON_TAC[];
       MATCH_MP_TAC PARTIAL_SUM_INTERS_SUBSET_NULL THEN
       ASM_REWRITE_TAC[]]];
     UNDISCH_TAC `null_event (p:A prob_space) (ne:A->bool)` THEN
     REWRITE_TAC[null_event] THEN REAL_ARITH_TAC]];
   ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]);;

(* Key lemma: If second moments of partial sums are unbounded and
   fourth moments satisfy E[S^4] <= C * E[S^2]^2, then partial sums
   cannot converge a.s.  Uses helpers: PALEY_ZYGMUND_LOWER_BOUND for
   the PZ step and PARTIAL_SUM_LEVEL_PROB_VANISHES for the a.s.
   convergence => prob vanishes argument. *)
let BOUNDED_INDEP_DIVERGENT_VARIANCE_DIVERGES = prove
 (`!p:A prob_space (Z:num->A->real) C.
    &1 <= C /\
    (!n. integrable p (\x. sum(0..n) (\i. Z i x) pow 2)) /\
    (!n. integrable p (\x. sum(0..n) (\i. Z i x) pow 4)) /\
    (!n. expectation p (\x. sum(0..n) (\i. Z i x) pow 4) <=
         C * expectation p (\x. sum(0..n) (\i. Z i x) pow 2) pow 2) /\
    (!B. ?N. B < expectation p (\x. sum(0..N) (\i. Z i x) pow 2))
    ==> ~almost_surely p
          {x | ?L. ((\n. sum(0..n) (\i. Z i x)) ---> L) sequentially}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `Z:num->A->real`]
    PARTIAL_SUM_LEVEL_PROB_VANISHES) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(&4 * C)`) THEN
  SUBGOAL_THEN `&0 < C` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&4 * C)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
   CONJ_TAC THENL [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K0:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `prob (p:A prob_space) {x:A | x IN prob_carrier p /\
    (?n:num. sum(0..n) (\i. (Z:num->A->real) i x) pow 2 > &K0)}
    < inv(&4 * C)` ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `K0:num`) THEN
   REWRITE_TAC[LE_REFL; REAL_SUB_RZERO] THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x < d ==> x < d`) THEN
   MATCH_MP_TAC PROB_POSITIVE THEN
   MATCH_MP_TAC PROB_INDEXED_UNION_EVENTS_LEMMA THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  UNDISCH_TAC `!B. ?N:num. B < expectation (p:A prob_space)
    (\x:A. sum(0..N) (\i. (Z:num->A->real) i x) pow 2)` THEN
  DISCH_THEN(MP_TAC o SPEC `&2 * &K0 + &2`) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  SUBGOAL_THEN `&0 < expectation (p:A prob_space)
    (\x:A. sum(0..N) (\i. (Z:num->A->real) i x) pow 2)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `Z:num->A->real`; `C:real`; `N:num`]
    PALEY_ZYGMUND_LOWER_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\
      sum(0..N) (\i. (Z:num->A->real) i x) pow 2 >=
        inv(&2) * expectation p (\x. sum(0..N) (\i. Z i x) pow 2)}
     SUBSET
     {x | x IN prob_carrier p /\
      ?n':num. sum(0..n') (\i. Z i x) pow 2 > &K0}`
    ASSUME_TAC THENL
  [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
   X_GEN_TAC `y:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   EXISTS_TAC `N:num` THEN
   SUBGOAL_THEN `&K0 < inv(&2) * expectation (p:A prob_space)
     (\x:A. sum(0..N) (\i. (Z:num->A->real) i x) pow 2)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `prob (p:A prob_space) {x:A | x IN prob_carrier p /\
    sum(0..N) (\i. (Z:num->A->real) i x) pow 2 >=
      inv(&2) * expectation p (\x. sum(0..N) (\i. Z i x) pow 2)}
    <= prob p {x | x IN prob_carrier p /\
      ?n':num. sum(0..n') (\i. Z i x) pow 2 > &K0}` MP_TAC THENL
  [MATCH_MP_TAC PROB_MONO THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC RV_LEVEL_GE_IN_EVENTS THEN
    MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PROB_INDEXED_UNION_EVENTS_LEMMA THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  ABBREV_TAC `p1 = prob (p:A prob_space) {x:A | x IN prob_carrier p /\
    sum(0..N) (\i. (Z:num->A->real) i x) pow 2 >=
      inv(&2) * expectation p (\x. sum(0..N) (\i. Z i x) pow 2)}` THEN
  ABBREV_TAC `p2 = prob (p:A prob_space) {x:A | x IN prob_carrier p /\
    ?n':num. sum(0..n') (\i. (Z:num->A->real) i x) pow 2 > &K0}` THEN
  ASM_REAL_ARITH_TAC);;

(* Three-Series Necessity: Condition (3)
   If sum Y_n converges a.s. (where Y_n bounded, mean-zero centered Z_n
   uncorrelated, with fourth moment bound on partial sums and sum E[Y_n]
   convergent), then sum Var(Y_n) < infinity.
   Additional hypotheses: C >= 1, fourth moment bound E[S^4] <= C*E[S^2]^2,
   and real_summable E[Y_n]. These follow from independence of X_n but are
   stated abstractly here. The main THREE_SERIES_NECESSITY will provide them. *)
let THREE_SERIES_CONDITION3 = prove
 (`!p:A prob_space (X:num->A->real) c C.
    &0 < c /\ &1 <= C /\
    (!n. integrable p (X n)) /\
    (!n. integrable p (\x. X n x pow 2)) /\
    (!i j. ~(i = j) ==> covariance p
      (\x. min(max(X i x) (--c)) c - expectation p (\y. min(max(X i y) (--c)) c))
      (\x. min(max(X j x) (--c)) c - expectation p (\y. min(max(X j y) (--c)) c))
      = &0) /\
    (!n x. x IN prob_carrier p ==> abs(min(max(X n x) (--c)) c -
      expectation p (\y. min(max(X n y) (--c)) c)) <= &2 * c) /\
    (!n. expectation p (\x. sum(0..n) (\i. min(max(X i x) (--c)) c -
      expectation p (\y. min(max(X i y) (--c)) c)) pow 4) <=
      C * expectation p (\x. sum(0..n) (\i. min(max(X i x) (--c)) c -
          expectation p (\y. min(max(X i y) (--c)) c)) pow 2) pow 2) /\
    real_summable (from 0) (\n. expectation p (\x. min(max(X n x) (--c)) c)) /\
    almost_surely p
      {x | ?L. ((\n. sum(0..n) (\i. min(max(X i x) (--c)) c)) ---> L)
               sequentially}
    ==> real_summable (from 0) (\n. variance p (\x. min(max(X n x) (--c)) c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Y = \n (x:A). min(max((X:num->A->real) n x) (--c)) c` THEN
  ABBREV_TAC `Z = \n (x:A). (Y:num->A->real) n x -
    expectation (p:A prob_space) (\y:A. Y n y)` THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  (* Z_n integrable *)
  SUBGOAL_THEN `!n. integrable (p:A prob_space) ((Z:num->A->real) n)`
    ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "Z" THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
   MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
    [EXPAND_TAC "Y" THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     MATCH_MP_TAC INTEGRABLE_CLAMP THEN
     CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[INTEGRABLE_CONST]];
   ALL_TAC] THEN
  (* Z_n^2 integrable *)
  SUBGOAL_THEN `!n. integrable (p:A prob_space)
    (\x. (Z:num->A->real) n x pow 2)` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
   EXISTS_TAC `(&2 * c) pow 2` THEN CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
     MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
     CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[];
     GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
     MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
     EXPAND_TAC "Z" THEN EXPAND_TAC "Y" THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  (* E[Z_n] = 0 *)
  SUBGOAL_THEN `!n. expectation (p:A prob_space) ((Z:num->A->real) n) = &0`
    ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "Z" THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
   MP_TAC(ISPECL [`p:A prob_space`; `(Y:num->A->real) n`;
     `\x:A. expectation (p:A prob_space) (\y:A. (Y:num->A->real) n y)`]
     EXPECTATION_SUB) THEN
   ANTS_TAC THENL
    [CONJ_TAC THENL
      [EXPAND_TAC "Y" THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
       MATCH_MP_TAC INTEGRABLE_CLAMP THEN
       CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[];
       REWRITE_TAC[INTEGRABLE_CONST]];
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC[EXPECTATION_CONST; ETA_AX] THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* Var(Z_n) = Var(Y_n) *)
  SUBGOAL_THEN `!n. variance (p:A prob_space) ((Z:num->A->real) n) =
    variance p ((Y:num->A->real) n)` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "Z" THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
   SUBGOAL_THEN `(\x:A. (Y:num->A->real) n x -
     expectation (p:A prob_space) (\y:A. Y n y)) =
     (\x. Y n x + (-- expectation p (\y. Y n y)))`
     (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC VARIANCE_SHIFT THEN
   EXPAND_TAC "Y" THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
   MATCH_MP_TAC INTEGRABLE_CLAMP THEN
   CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* ~summable Var(Z) *)
  SUBGOAL_THEN `~real_summable (from 0)
    (\n. variance (p:A prob_space) ((Z:num->A->real) n))` ASSUME_TAC THENL
  [UNDISCH_TAC `~real_summable (from 0)
     (\n. variance p (\x:A. min(max((X:num->A->real) n x) (--c)) c))` THEN
   MATCH_MP_TAC(TAUT `(p ==> q) ==> ~q ==> ~p`) THEN
   MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_SUMMABLE_EQ) THEN
   REWRITE_TAC[IN_FROM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   EXPAND_TAC "Y" THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[];
   ALL_TAC] THEN
  (* Var(Z) >= 0 *)
  SUBGOAL_THEN `!n. &0 <= variance (p:A prob_space) ((Z:num->A->real) n)`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC VARIANCE_NONNEG THEN
   MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `(&2 * c) pow 2` THEN
   CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
     MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN CONJ_TAC THENL
      [MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
       CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[];
       REWRITE_TAC[RANDOM_VARIABLE_CONST]];
     GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
     MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
     SUBGOAL_THEN `(Z:num->A->real) n (x:A) -
       expectation (p:A prob_space) (Z n) = Z n x`
       (fun th -> REWRITE_TAC[th]) THENL
      [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
     EXPAND_TAC "Z" THEN EXPAND_TAC "Y" THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  (* Uncorrelation of Z *)
  SUBGOAL_THEN `!i j. ~(i = j) ==> covariance (p:A prob_space)
    ((Z:num->A->real) i) (Z j) = &0` ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `(Z:num->A->real) = (\k (x:A).
     min(max((X:num->A->real) k x) (--c)) c -
     expectation (p:A prob_space) (\y. min(max(X k y) (--c)) c))`
     SUBST1_TAC THENL
    [EXPAND_TAC "Z" THEN EXPAND_TAC "Y" THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[];
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  (* Integrability of partial sums^2 *)
  SUBGOAL_THEN `!n. integrable (p:A prob_space)
    (\x. sum(0..n) (\i. (Z:num->A->real) i x) pow 2)` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
   EXISTS_TAC `((&(n + 1)) * (&2 * c)) pow 2` THEN CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
     MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN
     REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
     CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[];
     GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
     REWRITE_TAC[REAL_ABS_POW] THEN
     MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `sum(0..n) (\i. abs((Z:num->A->real) i (x:A)))` THEN
     CONJ_TAC THENL
      [REWRITE_TAC[SUM_ABS_NUMSEG]; ALL_TAC] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `sum(0..n) (\i:num. &2 * c)` THEN CONJ_TAC THENL
      [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
       BETA_TAC THEN
       EXPAND_TAC "Z" THEN EXPAND_TAC "Y" THEN
       CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_SIMP_TAC[];
       REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0] THEN
       REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_SUC] THEN
       REWRITE_TAC[ADD1] THEN REAL_ARITH_TAC]];
   ALL_TAC] THEN
  (* Integrability of partial sums^4 *)
  SUBGOAL_THEN `!n. integrable (p:A prob_space)
    (\x. sum(0..n) (\i. (Z:num->A->real) i x) pow 4)` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
   EXISTS_TAC `((&(n + 1)) * (&2 * c)) pow 4` THEN CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
     MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN
     REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
     CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[];
     GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
     REWRITE_TAC[REAL_ABS_POW] THEN
     MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `sum(0..n) (\i. abs((Z:num->A->real) i (x:A)))` THEN
     CONJ_TAC THENL
      [REWRITE_TAC[SUM_ABS_NUMSEG]; ALL_TAC] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `sum(0..n) (\i:num. &2 * c)` THEN CONJ_TAC THENL
      [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
       BETA_TAC THEN
       EXPAND_TAC "Z" THEN EXPAND_TAC "Y" THEN
       CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_SIMP_TAC[];
       REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0] THEN
       REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_SUC] THEN
       REWRITE_TAC[ADD1] THEN REAL_ARITH_TAC]];
   ALL_TAC] THEN
  (* Fourth moment bound for Z partial sums *)
  SUBGOAL_THEN `!n. expectation (p:A prob_space)
    (\x. sum(0..n) (\i. (Z:num->A->real) i x) pow 4) <=
    C * expectation p (\x. sum(0..n) (\i. Z i x) pow 2) pow 2`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   SUBGOAL_THEN `(Z:num->A->real) = (\k (x:A).
     min(max((X:num->A->real) k x) (--c)) c -
     expectation (p:A prob_space) (\y. min(max(X k y) (--c)) c))`
     SUBST1_TAC THENL
    [EXPAND_TAC "Z" THEN EXPAND_TAC "Y" THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[];
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* E[S_n^2] = sum(0..n) Var(Z_i) *)
  SUBGOAL_THEN `!n. expectation (p:A prob_space)
    (\x. sum(0..n) (\i. (Z:num->A->real) i x) pow 2) =
    sum(0..n) (\i. variance p (Z i))` ASSUME_TAC THENL
  [GEN_TAC THEN
   SUBGOAL_THEN `variance (p:A prob_space)
     (\x. sum(0..n) (\i. (Z:num->A->real) i x)) =
     sum(0..n) (\i. variance p (Z i))` ASSUME_TAC THENL
    [MATCH_MP_TAC VARIANCE_SUM_UNCORRELATED THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `expectation (p:A prob_space)
     (\x. sum(0..n) (\i. (Z:num->A->real) i x)) = &0` ASSUME_TAC THENL
    [MP_TAC(ISPECL [`p:A prob_space`; `Z:num->A->real`; `n:num`]
       EXPECTATION_SUM) THEN
     ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
     MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
   REWRITE_TAC[variance] THEN AP_TERM_TAC THEN
   REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Divergence: !B. ?N. B < E[S_N^2] *)
  SUBGOAL_THEN `!B. ?N:num. B < expectation (p:A prob_space)
    (\x. sum(0..N) (\i. (Z:num->A->real) i x) pow 2)` ASSUME_TAC THENL
  [GEN_TAC THEN
   MP_TAC(SPEC `\i. variance (p:A prob_space) ((Z:num->A->real) i)`
     NONNEG_PARTIAL_SUMS_UNBOUNDED) THEN
   ANTS_TAC THENL
    [CONJ_TAC THENL [BETA_TAC THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
   BETA_TAC THEN DISCH_THEN(MP_TAC o SPEC `B + &1`) THEN
   DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
   UNDISCH_TAC `!n:num. expectation (p:A prob_space)
     (\x:A. sum(0..n) (\i. (Z:num->A->real) i x) pow 2) =
     sum(0..n) (\i. variance p (Z i))` THEN
   DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
   UNDISCH_TAC `B + &1 <= sum(0..N)
     (\i. variance (p:A prob_space) ((Z:num->A->real) i))` THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Apply BOUNDED_INDEP to get ~almost_surely {sum Z converges} *)
  MP_TAC(ISPECL [`p:A prob_space`; `Z:num->A->real`; `C:real`]
    BOUNDED_INDEP_DIVERGENT_VARIANCE_DIVERGES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  (* Show almost_surely p {sum Z converges} *)
  SUBGOAL_THEN `almost_surely (p:A prob_space)
    {x:A | ?L. ((\n. sum(0..n) (\i. (Z:num->A->real) i x)) ---> L)
               sequentially}` ASSUME_TAC THENL
  [MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
   EXISTS_TAC `{x:A | ?L. ((\n. sum(0..n)
     (\i. (Y:num->A->real) i x)) ---> L) sequentially}` THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [UNDISCH_TAC `almost_surely (p:A prob_space)
       {x:A | ?L. ((\n. sum(0..n)
       (\i. min(max((X:num->A->real) i x) (--c)) c)) ---> L)
       sequentially}` THEN
     SUBGOAL_THEN `{x:A | ?L. ((\n. sum(0..n)
       (\i. min(max((X:num->A->real) i x) (--c)) c)) ---> L)
       sequentially} =
       {x | ?L. ((\n. sum(0..n) (\i. (Y:num->A->real) i x)) ---> L)
       sequentially}` ASSUME_TAC THENL
      [EXPAND_TAC "Y" THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN REFL_TAC;
       ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[]];
     REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
     DISCH_TAC THEN DISCH_THEN(X_CHOOSE_TAC `LY:real`) THEN
     (* sum Y converges to LY, sum E[Y] converges (real_summable) *)
     (* sum Z = sum Y - sum E[Y] converges *)
     SUBGOAL_THEN `?LE. ((\n. sum(0..n) (\i. expectation (p:A prob_space)
       (\y:A. (Y:num->A->real) i y))) ---> LE) sequentially`
       (X_CHOOSE_TAC `LE:real`) THENL
      [UNDISCH_TAC `real_summable (from 0)
         (\n. expectation (p:A prob_space) (\x:A. min(max((X:num->A->real) n x) (--c)) c))` THEN
       REWRITE_TAC[real_summable; real_sums; FROM_INTER_NUMSEG] THEN
       MATCH_MP_TAC(MESON[] `(f:num->real) = g ==> (?l. (f ---> l) sequentially) ==> (?l. (g ---> l) sequentially)`) THEN
       REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
       MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
       EXPAND_TAC "Y" THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[];
       ALL_TAC] THEN
     EXISTS_TAC `LY - LE:real` THEN
     MP_TAC(ISPECL [`sequentially`;
       `\n. sum(0..n) (\i. (Y:num->A->real) i (x:A))`;
       `\n. sum(0..n) (\i. expectation (p:A prob_space) (\y:A. Y i y))`;
       `LY:real`; `LE:real`] REALLIM_SUB) THEN
     ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REALLIM_TRANSFORM) THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     EXPAND_TAC "Z" THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN
     SIMP_TAC[REAL_ARITH `a - b - (a - b) = &0`; SUM_0] THEN
     REWRITE_TAC[REALLIM_CONST]];
   ASM_MESON_TAC[]]);;


(* Three-Series Necessity: Condition (2)
   sum E[Y_n] converges. Uses Condition (3) + Kolmogorov convergence criterion.
   Proof: Apply KCC to Z_n = Y_n - E[Y_n] to get sum Z_n converges a.s.
   Then sum E[Y_n] = sum Y_n - sum Z_n converges at any point where both converge. *)
let THREE_SERIES_CONDITION2 = prove
 (`!p:A prob_space (X:num->A->real) c.
    &0 < c /\
    (!n. integrable p (X n)) /\
    (!n. integrable p (\x. X n x pow 2)) /\
    (!i j. ~(i = j) ==> covariance p
      (\x. min(max(X i x) (--c)) c - expectation p (\y. min(max(X i y) (--c)) c))
      (\x. min(max(X j x) (--c)) c - expectation p (\y. min(max(X j y) (--c)) c))
      = &0) /\
    (!n x. x IN prob_carrier p ==> abs(min(max(X n x) (--c)) c -
      expectation p (\y. min(max(X n y) (--c)) c)) <= &2 * c) /\
    (!a b k t.
        a <= k /\ k < b /\ &0 < t
        ==> expectation p
            (\x. sum(a..k)
                   (\i. min (max (X i x) (--c)) c -
                        expectation p (\y. min (max (X i y) (--c)) c)) *
                 sum(SUC k..b)
                   (\i. min (max (X i x) (--c)) c -
                        expectation p (\y. min (max (X i y) (--c)) c)) *
                 indicator_fn
                   {z | z IN prob_carrier p /\
                        (!j. a <= j /\ j < k
                          ==> abs(sum(a..j)
                                (\i. min (max (X i z) (--c)) c -
                                     expectation p (\y. min (max (X i y) (--c)) c))) < t) /\
                        abs(sum(a..k)
                              (\i. min (max (X i z) (--c)) c -
                                   expectation p (\y. min (max (X i y) (--c)) c))) >= t} x) = &0) /\
    real_summable (from 0) (\n. variance p (\x. min(max(X n x) (--c)) c)) /\
    almost_surely p
      {x | ?L. ((\n. sum(0..n) (\i. min(max(X i x) (--c)) c)) ---> L)
               sequentially}
    ==> real_summable (from 0) (\n. expectation p (\x. min(max(X n x) (--c)) c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Y = \n (x:A). min(max((X:num->A->real) n x) (--c)) c` THEN
  ABBREV_TAC `Z = \n (x:A). (Y:num->A->real) n x -
    expectation (p:A prob_space) (\y:A. Y n y)` THEN
  (* Step 1: Establish Z_n properties for KOLMOGOROV_CONVERGENCE_CRITERION *)
  SUBGOAL_THEN `!n. integrable (p:A prob_space) ((Z:num->A->real) n)` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "Z" THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
   MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
    [EXPAND_TAC "Y" THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     MATCH_MP_TAC INTEGRABLE_CLAMP THEN
     CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[INTEGRABLE_CONST]];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n. integrable (p:A prob_space) (\x. (Z:num->A->real) n x pow 2)` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
   EXISTS_TAC `(&2 * c) pow 2` THEN CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
     MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
     CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[];
     GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
     MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
     EXPAND_TAC "Z" THEN EXPAND_TAC "Y" THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n. expectation (p:A prob_space) ((Z:num->A->real) n) = &0` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "Z" THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
   MP_TAC(ISPECL [`p:A prob_space`; `(Y:num->A->real) n`;
     `\x:A. expectation (p:A prob_space) (\y:A. (Y:num->A->real) n y)`]
     EXPECTATION_SUB) THEN
   ANTS_TAC THENL
    [CONJ_TAC THENL
      [EXPAND_TAC "Y" THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
       MATCH_MP_TAC INTEGRABLE_CLAMP THEN
       CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[];
       REWRITE_TAC[INTEGRABLE_CONST]];
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC[EXPECTATION_CONST; ETA_AX] THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* Variance identity: Var(Z_n) = Var(Y_n) *)
  SUBGOAL_THEN `!n. variance (p:A prob_space) ((Z:num->A->real) n) =
    variance p ((Y:num->A->real) n)` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "Z" THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
   SUBGOAL_THEN `(\x:A. (Y:num->A->real) n x - expectation (p:A prob_space) (\y:A. Y n y)) =
     (\x. Y n x + (-- expectation p (\y. Y n y)))` (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC VARIANCE_SHIFT THEN
   EXPAND_TAC "Y" THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
   MATCH_MP_TAC INTEGRABLE_CLAMP THEN
   CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 2: Apply KOLMOGOROV_CONVERGENCE_CRITERION to get sum Z_n converges a.s. *)
  SUBGOAL_THEN `almost_surely (p:A prob_space)
    {x:A | ?L. ((\n. sum(0..n) (\i. (Z:num->A->real) i x)) ---> L) sequentially}`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `Z:num->A->real`] KOLMOGOROV_CONVERGENCE_CRITERION) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
      [REPEAT GEN_TAC THEN DISCH_TAC THEN
       EXPAND_TAC "Z" THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
       EXPAND_TAC "Y" THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
       ASM_SIMP_TAC[];
       ALL_TAC] THEN
     CONJ_TAC THENL
      [(* Cross-term condition: Z_i = Y_i - E[Y_i], same as hypothesis *)
       REPEAT STRIP_TAC THEN
       SUBGOAL_THEN `!i (x:A). (Z:num->A->real) i x =
         min(max((X:num->A->real) i x) (--c)) c -
         expectation (p:A prob_space) (\y. min(max(X i y) (--c)) c)` ASSUME_TAC THENL
        [REPEAT GEN_TAC THEN EXPAND_TAC "Z" THEN EXPAND_TAC "Y" THEN
         CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[];
         ALL_TAC] THEN
       ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
       (* Summable variance: ASM_REWRITE_TAC above rewrites Z to Y via asm 13 *)
       EXPAND_TAC "Y" THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
       ASM_REWRITE_TAC[]];
     DISCH_TAC THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* Step 3: Intersect the two a.s. events, extract a point *)
  MP_TAC(ISPECL [`p:A prob_space`;
    `{x:A | ?L. ((\n. sum(0..n) (\i. min(max((X:num->A->real) i x) (--c)) c)) ---> L) sequentially}`;
    `{x:A | ?L. ((\n. sum(0..n) (\i. (Z:num->A->real) i x)) ---> L) sequentially}`]
    ALMOST_SURELY_INTER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `{x:A | ?L. ((\n. sum(0..n) (\i. min(max((X:num->A->real) i x) (--c)) c)) ---> L) sequentially} INTER
     {x:A | ?L. ((\n. sum(0..n) (\i. (Z:num->A->real) i x)) ---> L) sequentially}`]
    ALMOST_SURELY_NONEMPTY) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:A` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `LY:real`) (X_CHOOSE_TAC `LZ:real`)) THEN
  (* Step 4: Show the deterministic series converges *)
  REWRITE_TAC[real_summable; real_sums; FROM_INTER_NUMSEG] THEN
  EXISTS_TAC `(LY:real) - (LZ:real)` THEN
  SUBGOAL_THEN `(\n. sum (0..n)
    (\i. expectation (p:A prob_space) (\x. min(max((X:num->A->real) i x) (--c)) c))) =
    (\n. sum(0..n) (\i. min(max(X i (x0:A)) (--c)) c) -
         sum(0..n) (\i. (Z:num->A->real) i x0))` SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
   REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN
   MATCH_MP_TAC SUM_EQ_NUMSEG THEN
   REPEAT STRIP_TAC THEN EXPAND_TAC "Z" THEN
   CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
   EXPAND_TAC "Y" THEN
   CONV_TAC(DEPTH_CONV BETA_CONV) THEN REAL_ARITH_TAC;
   MATCH_MP_TAC REALLIM_SUB THEN ASM_REWRITE_TAC[]]);;

(* Break circular dependency between CONDITION2 and CONDITION3:
   Prove summable Var directly from a.s. convergence + BIDVD contrapositive.
   Key insight: BIDVD works for non-centered Y_n, needing only
   E[S_n^2] unbounded + fourth moment bound. If ~summable Var, then
   Var(S_n) = sum Var(Y_k) -> infinity (by uncorrelation), hence
   E[S_n^2] >= Var(S_n) -> infinity, so BIDVD gives ~a.s. convergence. *)
let SUMMABLE_VARIANCE_FROM_CONVERGENCE = prove
 (`!p:A prob_space (Y:num->A->real) C.
    &1 <= C /\
    (!n. integrable p (Y n)) /\
    (!n. integrable p (\x. Y n x pow 2)) /\
    (!i j. ~(i = j) ==> covariance p (Y i) (Y j) = &0) /\
    (!n. integrable p (\x. sum(0..n) (\i. Y i x) pow 2)) /\
    (!n. integrable p (\x. sum(0..n) (\i. Y i x) pow 4)) /\
    (!n. expectation p (\x. sum(0..n) (\i. Y i x) pow 4) <=
         C * expectation p (\x. sum(0..n) (\i. Y i x) pow 2) pow 2) /\
    almost_surely p
      {x | ?L. ((\n. sum(0..n) (\i. Y i x)) ---> L) sequentially}
    ==> real_summable (from 0) (\n. variance p (Y n))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  (* Var(Y n) >= 0 *)
  SUBGOAL_THEN `!n. &0 <= variance (p:A prob_space) ((Y:num->A->real) n)`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC VARIANCE_NONNEG THEN
   REWRITE_TAC[REAL_ARITH `(a - b:real) pow 2 = a pow 2 - &2 * b * a + b pow 2`] THEN
   MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     SUBGOAL_THEN `(\x:A. &2 * expectation (p:A prob_space) ((Y:num->A->real) n) * Y n x) =
       (\x. (&2 * expectation p (Y n)) * Y n x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; REAL_MUL_ASSOC]; ALL_TAC] THEN
     MATCH_MP_TAC INTEGRABLE_CMUL THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[INTEGRABLE_CONST]];
   ALL_TAC] THEN
  (* E[S_n^2] is unbounded *)
  SUBGOAL_THEN `!B. ?N:num. B < expectation (p:A prob_space)
      (\x:A. sum(0..N) (\i. (Y:num->A->real) i x) pow 2)` ASSUME_TAC THENL
  [X_GEN_TAC `B:real` THEN
   MP_TAC(SPEC `\n:num. variance (p:A prob_space) ((Y:num->A->real) n)`
     NONNEG_PARTIAL_SUMS_UNBOUNDED) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPEC `B + &1`) THEN
   DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
   EXISTS_TAC `N:num` THEN
   (* Var(S_N) <= E[S_N^2] *)
   SUBGOAL_THEN `variance (p:A prob_space) (\x:A. sum(0..N) (\i. (Y:num->A->real) i x)) <=
       expectation p (\x. sum(0..N) (\i. Y i x) pow 2)` ASSUME_TAC THENL
   [SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. sum(0..N) (\i. (Y:num->A->real) i x))`
       ASSUME_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_SUM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`p:A prob_space`; `\x:A. sum(0..N) (\i. (Y:num->A->real) i x)`]
      VARIANCE_ALT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_ARITH `a - b <= a <=> &0 <= b`; REAL_LE_POW_2];
    ALL_TAC] THEN
   (* sum Var(Y_k) = Var(S_N) *)
   SUBGOAL_THEN `sum(0..N) (\n:num. variance (p:A prob_space) ((Y:num->A->real) n)) =
       variance p (\x. sum(0..N) (\i. Y i x))` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN MATCH_MP_TAC VARIANCE_SUM_UNCORRELATED THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* Apply BIDVD: ~a.s. convergence, contradicting hypothesis *)
  MP_TAC(ISPECL [`p:A prob_space`; `Y:num->A->real`; `C:real`]
    BOUNDED_INDEP_DIVERGENT_VARIANCE_DIVERGES) THEN
  ASM_REWRITE_TAC[]);;

(* Helper: an unbounded sequence exceeds any threshold beyond any index *)
let UNBOUNDED_EVENTUALLY = prove
 (`!f:num->real. (!B. ?N. B < f N) ==> (!B N0. ?N. N0 <= N /\ B < f N)`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?M:real. !n:num. n < N0 ==> (f:num->real) n <= M`
    STRIP_ASSUME_TAC THENL
  [SPEC_TAC(`N0:num`,`m:num`) THEN INDUCT_TAC THENL
   [EXISTS_TAC `&0` THEN ARITH_TAC;
    FIRST_X_ASSUM(X_CHOOSE_TAC `M:real`) THEN
    EXISTS_TAC `max M ((f:num->real) m)` THEN
    GEN_TAC THEN REWRITE_TAC[LT] THEN STRIP_TAC THENL
    [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
     MATCH_MP_TAC(REAL_ARITH `x <= M ==> x <= max M y`) THEN
     ASM_SIMP_TAC[]]];
   ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `max B M`) THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  EXISTS_TAC `N1:num` THEN CONJ_TAC THENL
  [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `N1:num`) THEN ASM_REWRITE_TAC[] THEN
   ASM_REAL_ARITH_TAC;
   ASM_REAL_ARITH_TAC]);;

(* Weakened BIDVD: fourth moment bound only needed eventually (for n >= N0).
   Proof is same as BIDVD but picks N >= max(N0, threshold) using
   UNBOUNDED_EVENTUALLY. *)
let BIDVD_EVENTUALLY = prove
 (`!p:A prob_space (Z:num->A->real) C.
    &1 <= C /\
    (!n. integrable p (\x. sum(0..n) (\i. Z i x) pow 2)) /\
    (!n. integrable p (\x. sum(0..n) (\i. Z i x) pow 4)) /\
    (?N0. !n. N0 <= n ==>
      expectation p (\x. sum(0..n) (\i. Z i x) pow 4) <=
      C * expectation p (\x. sum(0..n) (\i. Z i x) pow 2) pow 2) /\
    (!B. ?N. B < expectation p (\x. sum(0..N) (\i. Z i x) pow 2))
    ==> ~almost_surely p
          {x | ?L. ((\n. sum(0..n) (\i. Z i x)) ---> L) sequentially}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `N0:num`) ASSUME_TAC) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `Z:num->A->real`]
    PARTIAL_SUM_LEVEL_PROB_VANISHES) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(&4 * C)`) THEN
  SUBGOAL_THEN `&0 < C` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&4 * C)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
   CONJ_TAC THENL [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K0:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `prob (p:A prob_space) {x:A | x IN prob_carrier p /\
    (?n:num. sum(0..n) (\i. (Z:num->A->real) i x) pow 2 > &K0)}
    < inv(&4 * C)` ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `K0:num`) THEN
   REWRITE_TAC[LE_REFL; REAL_SUB_RZERO] THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x < d ==> x < d`) THEN
   MATCH_MP_TAC PROB_POSITIVE THEN
   MATCH_MP_TAC PROB_INDEXED_UNION_EVENTS_LEMMA THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Key change: use UNBOUNDED_EVENTUALLY to pick N >= N0 *)
  MP_TAC(ISPEC `\n:num. expectation (p:A prob_space)
    (\x:A. sum(0..n) (\i. (Z:num->A->real) i x) pow 2)`
    UNBOUNDED_EVENTUALLY) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN(MP_TAC o SPECL [`&2 * &K0 + &2`; `N0:num`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < expectation (p:A prob_space)
    (\x:A. sum(0..N) (\i. (Z:num->A->real) i x) pow 2)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `expectation (p:A prob_space)
    (\x:A. sum(0..N) (\i. (Z:num->A->real) i x) pow 4) <=
    C * expectation p (\x. sum(0..N) (\i. Z i x) pow 2) pow 2`
    ASSUME_TAC THENL
  [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_CONJ]) THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `Z:num->A->real`; `C:real`; `N:num`]
    PALEY_ZYGMUND_LOWER_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\
      sum(0..N) (\i. (Z:num->A->real) i x) pow 2 >=
        inv(&2) * expectation p (\x. sum(0..N) (\i. Z i x) pow 2)}
     SUBSET
     {x | x IN prob_carrier p /\
      ?n':num. sum(0..n') (\i. Z i x) pow 2 > &K0}`
    ASSUME_TAC THENL
  [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
   X_GEN_TAC `y:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   EXISTS_TAC `N:num` THEN
   SUBGOAL_THEN `&K0 < inv(&2) * expectation (p:A prob_space)
     (\x:A. sum(0..N) (\i. (Z:num->A->real) i x) pow 2)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `prob (p:A prob_space) {x:A | x IN prob_carrier p /\
    sum(0..N) (\i. (Z:num->A->real) i x) pow 2 >=
      inv(&2) * expectation p (\x. sum(0..N) (\i. Z i x) pow 2)}
    <= prob p {x | x IN prob_carrier p /\
      ?n':num. sum(0..n') (\i. Z i x) pow 2 > &K0}` MP_TAC THENL
  [MATCH_MP_TAC PROB_MONO THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC RV_LEVEL_GE_IN_EVENTS THEN
    MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PROB_INDEXED_UNION_EVENTS_LEMMA THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  ABBREV_TAC `p1 = prob (p:A prob_space) {x:A | x IN prob_carrier p /\
    sum(0..N) (\i. (Z:num->A->real) i x) pow 2 >=
      inv(&2) * expectation p (\x. sum(0..N) (\i. Z i x) pow 2)}` THEN
  ABBREV_TAC `p2 = prob (p:A prob_space) {x:A | x IN prob_carrier p /\
    ?n':num. sum(0..n') (\i. (Z:num->A->real) i x) pow 2 > &K0}` THEN
  ASM_REAL_ARITH_TAC);;

(* Summable variance from a.s. convergence -- eventually version.
   Same as SUMMABLE_VARIANCE_FROM_CONVERGENCE but fourth moment bound
   only required for n >= N0, using BIDVD_EVENTUALLY. *)
let SUMMABLE_VARIANCE_FROM_CONVERGENCE_V2 = prove
 (`!p:A prob_space (Y:num->A->real) C.
     &1 <= C /\
     (!n. integrable p (Y n)) /\
     (!n. integrable p (\x. Y n x pow 2)) /\
     (!i j. ~(i = j) ==> covariance p (Y i) (Y j) = &0) /\
     (!n. integrable p (\x. sum(0..n) (\i. Y i x) pow 2)) /\
     (!n. integrable p (\x. sum(0..n) (\i. Y i x) pow 4)) /\
     (?N0. !n. N0 <= n ==>
       expectation p (\x. sum(0..n) (\i. Y i x) pow 4) <=
       C * expectation p (\x. sum(0..n) (\i. Y i x) pow 2) pow 2) /\
     almost_surely p
       {x | ?L. ((\n. sum(0..n) (\i. Y i x)) ---> L) sequentially}
     ==> real_summable (from 0) (\n. variance p (Y n))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `!n. &0 <= variance (p:A prob_space) ((Y:num->A->real) n)`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC VARIANCE_NONNEG THEN
   REWRITE_TAC[REAL_ARITH `(a - b:real) pow 2 = a pow 2 - &2 * b * a + b pow 2`] THEN
   MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     SUBGOAL_THEN `(\x:A. &2 * expectation (p:A prob_space) ((Y:num->A->real) n) * Y n x) =
       (\x. (&2 * expectation p (Y n)) * Y n x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; REAL_MUL_ASSOC]; ALL_TAC] THEN
     MATCH_MP_TAC INTEGRABLE_CMUL THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[INTEGRABLE_CONST]];
   ALL_TAC] THEN
  SUBGOAL_THEN `!B. ?N:num. B < expectation (p:A prob_space)
      (\x:A. sum(0..N) (\i. (Y:num->A->real) i x) pow 2)` ASSUME_TAC THENL
  [X_GEN_TAC `B:real` THEN
   MP_TAC(SPEC `\n:num. variance (p:A prob_space) ((Y:num->A->real) n)`
     NONNEG_PARTIAL_SUMS_UNBOUNDED) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPEC `B + &1`) THEN
   DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
   EXISTS_TAC `N:num` THEN
   SUBGOAL_THEN `variance (p:A prob_space) (\x:A. sum(0..N) (\i. (Y:num->A->real) i x)) <=
       expectation p (\x. sum(0..N) (\i. Y i x) pow 2)` ASSUME_TAC THENL
   [SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. sum(0..N) (\i. (Y:num->A->real) i x))`
       ASSUME_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_SUM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`p:A prob_space`; `\x:A. sum(0..N) (\i. (Y:num->A->real) i x)`]
      VARIANCE_ALT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_ARITH `a - b <= a <=> &0 <= b`; REAL_LE_POW_2];
    ALL_TAC] THEN
   SUBGOAL_THEN `sum(0..N) (\n:num. variance (p:A prob_space) ((Y:num->A->real) n)) =
       variance p (\x. sum(0..N) (\i. Y i x))` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN MATCH_MP_TAC VARIANCE_SUM_UNCORRELATED THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `Y:num->A->real`; `C:real`]
    BIDVD_EVENTUALLY) THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `N0:num` THEN ASM_REWRITE_TAC[]);;

(* E[X^m * Y^k] = E[X^m] * E[Y^k] for bounded independent X, Y *)
let EXPECTATION_PRODUCT_POW_BOUNDED_INDEP = prove
 (`!p:A prob_space (X:A->real) (Y:A->real) m k B_X B_Y.
    random_variable p X /\ random_variable p Y /\
    (!x. x IN prob_carrier p ==> abs(X x) <= B_X) /\
    (!x. x IN prob_carrier p ==> abs(Y x) <= B_Y) /\
    indep_rv p X Y
    ==> expectation p (\x. X x pow m * Y x pow k) =
        expectation p (\x. X x pow m) * expectation p (\x. Y x pow k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* prob_carrier nonempty, B_X >= 0, B_Y >= 0 *)
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
  (* Shift to nonneg: U = X + B_X, V = Y + B_Y *)
  ABBREV_TAC `U = \x:A. (X:A->real) x + B_X` THEN
  ABBREV_TAC `V = \x:A. (Y:A->real) x + B_Y` THEN
  SUBGOAL_THEN `indep_rv (p:A prob_space) U V` ASSUME_TAC THENL
  [EXPAND_TAC "U" THEN EXPAND_TAC "V" THEN
   MATCH_MP_TAC INDEP_RV_SHIFT THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `random_variable (p:A prob_space) U /\
                random_variable p V` STRIP_ASSUME_TAC THENL
  [EXPAND_TAC "U" THEN EXPAND_TAC "V" THEN
   CONJ_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_SHIFT THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN prob_carrier p ==> &0 <= U x` ASSUME_TAC THENL
  [EXPAND_TAC "U" THEN X_GEN_TAC `w:A` THEN DISCH_TAC THEN
   SUBGOAL_THEN `abs((X:A->real) w) <= B_X` MP_TAC THENL
   [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN prob_carrier p ==> &0 <= V x` ASSUME_TAC THENL
  [EXPAND_TAC "V" THEN X_GEN_TAC `w:A` THEN DISCH_TAC THEN
   SUBGOAL_THEN `abs((Y:A->real) w) <= B_Y` MP_TAC THENL
   [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* nsfa approx shifted back: Wn = nsfa(U) - B_X, Zn = nsfa(V) - B_Y *)
  ABBREV_TAC `Wn = \n:num. \x:A. nonneg_simple_fn_approx p U n x - B_X` THEN
  ABBREV_TAC `Zn = \n:num. \x:A. nonneg_simple_fn_approx p V n x - B_Y` THEN
  (* simple_rv for Wn, Zn *)
  SUBGOAL_THEN `!n:num. simple_rv (p:A prob_space) ((Wn:num->A->real) n)`
    ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "Wn" THEN BETA_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `nonneg_simple_fn_approx (p:A prob_space) (U:A->real) n`;
     `\t:real. t - B_X`] SIMPLE_RV_REAL_COMPOSE) THEN
   BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
   MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_SIMPLE_RV THEN
   ASM_REWRITE_TAC[ETA_AX];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n:num. simple_rv (p:A prob_space) ((Zn:num->A->real) n)`
    ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "Zn" THEN BETA_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `nonneg_simple_fn_approx (p:A prob_space) (V:A->real) n`;
     `\t:real. t - B_Y`] SIMPLE_RV_REAL_COMPOSE) THEN
   BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
   MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_SIMPLE_RV THEN
   ASM_REWRITE_TAC[ETA_AX];
   ALL_TAC] THEN
  (* indep_rv for Wn, Zn *)
  SUBGOAL_THEN `!n:num. indep_rv (p:A prob_space) ((Wn:num->A->real) n)
                                                    ((Zn:num->A->real) n)`
    ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "Wn" THEN EXPAND_TAC "Zn" THEN BETA_TAC THEN
   REWRITE_TAC[real_sub] THEN MATCH_MP_TAC INDEP_RV_SHIFT THEN
   REWRITE_TAC[ETA_AX] THEN
   MATCH_MP_TAC INDEP_RV_NSFA THEN ASM_REWRITE_TAC[ETA_AX];
   ALL_TAC] THEN
  (* Pointwise convergence: Wn -> X, Zn -> Y *)
  SUBGOAL_THEN `!x:A. x IN prob_carrier p
    ==> ((\n. (Wn:num->A->real) n x) ---> (X:A->real) x) sequentially`
    ASSUME_TAC THENL
  [X_GEN_TAC `w:A` THEN DISCH_TAC THEN EXPAND_TAC "Wn" THEN BETA_TAC THEN
   SUBGOAL_THEN `(X:A->real) w = U w - B_X` SUBST1_TAC THENL
   [EXPAND_TAC "U" THEN REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REALLIM_SUB THEN REWRITE_TAC[REALLIM_CONST] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `U:A->real`; `w:A`]
     NONNEG_SIMPLE_FN_APPROX_CONVERGES) THEN
   ASM_SIMP_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN prob_carrier p
    ==> ((\n. (Zn:num->A->real) n x) ---> (Y:A->real) x) sequentially`
    ASSUME_TAC THENL
  [X_GEN_TAC `w:A` THEN DISCH_TAC THEN EXPAND_TAC "Zn" THEN BETA_TAC THEN
   SUBGOAL_THEN `(Y:A->real) w = V w - B_Y` SUBST1_TAC THENL
   [EXPAND_TAC "V" THEN REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REALLIM_SUB THEN REWRITE_TAC[REALLIM_CONST] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `V:A->real`; `w:A`]
     NONNEG_SIMPLE_FN_APPROX_CONVERGES) THEN
   ASM_SIMP_TAC[];
   ALL_TAC] THEN
  (* Bounds: |Wn| <= B_X, |Zn| <= B_Y *)
  SUBGOAL_THEN `!n w:A. w IN prob_carrier p
    ==> abs((Wn:num->A->real) n w) <= B_X` ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "Wn" THEN BETA_TAC THEN
   SUBGOAL_THEN `nonneg_simple_fn_approx (p:A prob_space) U n w <= U w`
     ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `U:A->real`; `n:num`; `w:A`]
      NONNEG_SIMPLE_FN_APPROX_LE) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= nonneg_simple_fn_approx (p:A prob_space) U n w`
     ASSUME_TAC THENL
   [REWRITE_TAC[NONNEG_SIMPLE_FN_APPROX_NONNEG]; ALL_TAC] THEN
   SUBGOAL_THEN `(U:A->real) w <= &2 * B_X` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN
    SUBGOAL_THEN `abs((X:A->real) w) <= B_X` MP_TAC THENL
    [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n w:A. w IN prob_carrier p
    ==> abs((Zn:num->A->real) n w) <= B_Y` ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "Zn" THEN BETA_TAC THEN
   SUBGOAL_THEN `nonneg_simple_fn_approx (p:A prob_space) V n w <= V w`
     ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `V:A->real`; `n:num`; `w:A`]
      NONNEG_SIMPLE_FN_APPROX_LE) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= nonneg_simple_fn_approx (p:A prob_space) V n w`
     ASSUME_TAC THENL
   [REWRITE_TAC[NONNEG_SIMPLE_FN_APPROX_NONNEG]; ALL_TAC] THEN
   SUBGOAL_THEN `(V:A->real) w <= &2 * B_Y` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN
    SUBGOAL_THEN `abs((Y:A->real) w) <= B_Y` MP_TAC THENL
    [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* Per-step formula: E[Wn^m * Zn^k] = E[Wn^m] * E[Zn^k] *)
  SUBGOAL_THEN `!n:num. expectation (p:A prob_space)
    (\x. (Wn:num->A->real) n x pow m * (Zn:num->A->real) n x pow k) =
    expectation p (\x. Wn n x pow m) * expectation p (\x. Zn n x pow k)`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. (Wn:num->A->real) n x pow m)`
     ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `(Wn:num->A->real) n`;
      `\t:real. t pow m`] SIMPLE_RV_REAL_COMPOSE) THEN
    BETA_TAC THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
   SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. (Zn:num->A->real) n x pow k)`
     ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `(Zn:num->A->real) n`;
      `\t:real. t pow k`] SIMPLE_RV_REAL_COMPOSE) THEN
    BETA_TAC THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
   SUBGOAL_THEN `simple_rv (p:A prob_space)
     (\x:A. (Wn:num->A->real) n x pow m * (Zn:num->A->real) n x pow k)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_SIMP_TAC[EXPECTATION_SIMPLE_AGREE] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `(Wn:num->A->real) n`;
      `(Zn:num->A->real) n`; `\t:real. t pow m`; `\t:real. t pow k`]
      SIMPLE_EXPECTATION_PRODUCT_COMPOSE_INDEP) THEN
   BETA_TAC THEN ASM_REWRITE_TAC[ETA_AX];
   ALL_TAC] THEN
  (* Main argument: REALLIM_UNIQUE with BCT *)
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC `\n:num. expectation (p:A prob_space) (\x:A.
    (Wn:num->A->real) n x pow m * (Zn:num->A->real) n x pow k)` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
  [(* LHS: E[Wn^m * Zn^k] -> E[X^m * Y^k] by BCT *)
   MATCH_MP_TAC BOUNDED_CONVERGENCE_EXPECTATION THEN
   EXISTS_TAC `(B_X:real) pow m * (B_Y:real) pow k` THEN
   REPEAT CONJ_TAC THENL
   [(* rv: Wn^m * Zn^k *)
    GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN CONJ_TAC THEN
    MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
    MP_TAC(SPEC `n:num` (ASSUME `!n. indep_rv (p:A prob_space)
      ((Wn:num->A->real) n) ((Zn:num->A->real) n)`)) THEN
    REWRITE_TAC[indep_rv] THEN STRIP_TAC THEN ASM_REWRITE_TAC[ETA_AX];
    (* rv: X^m * Y^k *)
    MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN CONJ_TAC THEN
    MATCH_MP_TAC RANDOM_VARIABLE_POW THEN ASM_REWRITE_TAC[];
    (* bound: |Wn^m * Zn^k| <= B_X^m * B_Y^k *)
    REPEAT STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW] THEN
    SUBGOAL_THEN `abs((Wn:num->A->real) n x) pow m <= B_X pow m /\
                   abs((Zn:num->A->real) n x) pow k <= B_Y pow k`
      STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN
     REWRITE_TAC[REAL_ABS_POS] THEN ASM_SIMP_TAC[];
     MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
     CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_ABS_POS]];
    (* bound: |X^m * Y^k| <= B_X^m * B_Y^k *)
    REPEAT STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW] THEN
    SUBGOAL_THEN `abs((X:A->real) x) pow m <= B_X pow m /\
                   abs((Y:A->real) x) pow k <= B_Y pow k`
      STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN
     REWRITE_TAC[REAL_ABS_POS] THEN ASM_SIMP_TAC[];
     MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
     CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_ABS_POS]];
    (* conv: Wn^m * Zn^k -> X^m * Y^k *)
    REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REALLIM_MUL THEN CONJ_TAC THEN
    MATCH_MP_TAC REALLIM_POW THEN ASM_SIMP_TAC[]];
   (* RHS: E[Wn^m] * E[Zn^k] -> E[X^m] * E[Y^k] *)
   ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REALLIM_MUL THEN CONJ_TAC THENL
   [(* X factor: E[Wn^m] -> E[X^m] *)
    MATCH_MP_TAC BOUNDED_CONVERGENCE_EXPECTATION THEN
    EXISTS_TAC `(B_X:real) pow m` THEN REPEAT CONJ_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
     MP_TAC(SPEC `n:num` (ASSUME `!n. indep_rv (p:A prob_space)
       ((Wn:num->A->real) n) ((Zn:num->A->real) n)`)) THEN
     REWRITE_TAC[indep_rv] THEN STRIP_TAC THEN ASM_REWRITE_TAC[ETA_AX];
     MATCH_MP_TAC RANDOM_VARIABLE_POW THEN ASM_REWRITE_TAC[];
     REPEAT STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
     MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
     ASM_SIMP_TAC[];
     REPEAT STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
     MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
     ASM_SIMP_TAC[];
     REPEAT STRIP_TAC THEN BETA_TAC THEN
     MATCH_MP_TAC REALLIM_POW THEN ASM_SIMP_TAC[]];
    (* Y factor: E[Zn^k] -> E[Y^k] *)
    MATCH_MP_TAC BOUNDED_CONVERGENCE_EXPECTATION THEN
    EXISTS_TAC `(B_Y:real) pow k` THEN REPEAT CONJ_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
     MP_TAC(SPEC `n:num` (ASSUME `!n. indep_rv (p:A prob_space)
       ((Wn:num->A->real) n) ((Zn:num->A->real) n)`)) THEN
     REWRITE_TAC[indep_rv] THEN STRIP_TAC THEN ASM_REWRITE_TAC[ETA_AX];
     MATCH_MP_TAC RANDOM_VARIABLE_POW THEN ASM_REWRITE_TAC[];
     REPEAT STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
     MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
     ASM_SIMP_TAC[];
     REPEAT STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
     MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
     ASM_SIMP_TAC[];
     REPEAT STRIP_TAC THEN BETA_TAC THEN
     MATCH_MP_TAC REALLIM_POW THEN ASM_SIMP_TAC[]]]]);;

(* ------------------------------------------------------------------------- *)
(* THREE_SERIES_CONDITION1: tail probability summability from a.s.           *)
(* convergence + independence of tail events.                                *)
(* Proof: By contradiction via Second Borel-Cantelli. If not summable,       *)
(* P(limsup) = 1 by 2nd B-C. But a.s. convergence => sum converges a.e.     *)
(* => X_n -> 0 a.e. => limsup subset of null set => P(limsup) = 0.          *)
(* Contradiction.                                                            *)
(* ------------------------------------------------------------------------- *)

let THREE_SERIES_CONDITION1 = prove
  (`!p:A prob_space (X:num->A->real) c.
      &0 < c /\
      (!n. random_variable p (X n)) /\
      indep_events_seq p
        (\n. {x | x IN prob_carrier p /\ abs(X n x) > c}) /\
      almost_surely p
        {x | ?L. ((\n. sum(0..n) (\i. X i x)) ---> L) sequentially}
      ==> real_summable (from 0)
            (\n. prob p {x | x IN prob_carrier p /\ abs(X n x) > c})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* By contradiction *)
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  (* Extract events membership from indep_events_seq *)
  SUBGOAL_THEN
    `!n. {x:A | x IN prob_carrier p /\ abs((X:num->A->real) n x) > c}
         IN prob_events p`
    ASSUME_TAC THENL
  [UNDISCH_TAC `indep_events_seq (p:A prob_space)
     (\n. {x | x IN prob_carrier p /\ abs((X:num->A->real) n x) > c})` THEN
   REWRITE_TAC[indep_events_seq] THEN SIMP_TAC[];
   ALL_TAC] THEN
  (* 2nd Borel-Cantelli: P(limsup) = 1 *)
  MP_TAC(ISPECL
    [`p:A prob_space`;
     `\n. {x:A | x IN prob_carrier p /\ abs((X:num->A->real) n x) > c}`]
    SECOND_BOREL_CANTELLI) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* almost_surely gives null set n *)
  UNDISCH_TAC `almost_surely (p:A prob_space)
    {x | ?L. ((\n. sum(0..n) (\i. (X:num->A->real) i x)) ---> L) sequentially}` THEN
  REWRITE_TAC[almost_surely] THEN STRIP_TAC THEN
  (* Show limsup subset n *)
  SUBGOAL_THEN
    `limsup_events
       (\k. {x:A | x IN prob_carrier p /\ abs((X:num->A->real) k x) > c})
     SUBSET n`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SUBSET_TRANS THEN
   EXISTS_TAC `{x:A | x IN prob_carrier p /\
     ~(x IN {x | ?L. ((\n. sum(0..n) (\i. (X:num->A->real) i x)) ---> L)
                      sequentially})}` THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[LIMSUP_EVENTS_ALT; SUBSET; IN_ELIM_THM] THEN
   X_GEN_TAC `x:A` THEN STRIP_TAC THEN
   CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
    DISCH_THEN(X_CHOOSE_THEN `nn:num` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* Show x not in convergence set: X_n(x) doesn't tend to 0 *)
   DISCH_THEN(X_CHOOSE_THEN `L:real` ASSUME_TAC) THEN
   (* X_n -> 0 from convergent series *)
   SUBGOAL_THEN `((\k. (X:num->A->real) k x) ---> &0) sequentially`
     ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPEC `\i:num. (X:num->A->real) i x`
      REAL_SERIES_TERMS_TOZERO) THEN
    EXISTS_TAC `L:real` THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[real_sums; FROM_INTER_NUMSEG] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* Contradiction: X_n -> 0 but infinitely many |X_n| > c *)
   FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[REALLIM_SEQUENTIALLY]) THEN
   DISCH_THEN(MP_TAC o SPEC `c:real`) THEN
   ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
   DISCH_THEN(X_CHOOSE_THEN `N1:num` ASSUME_TAC) THEN
   UNDISCH_TAC `!m:num. ?n:num. n >= m /\ (x:A) IN prob_carrier p /\
     abs((X:num->A->real) n x) > c` THEN
   DISCH_THEN(MP_TAC o SPEC `N1:num`) THEN
   DISCH_THEN(X_CHOOSE_THEN `n1:num` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `n1:num`) THEN
   UNDISCH_TAC `n1:num >= N1` THEN REWRITE_TAC[GE] THEN
   DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `abs((X:num->A->real) n1 x) > c` THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* prob(limsup) = 0 from limsup subset null *)
  SUBGOAL_THEN
    `limsup_events
       (\n. {x:A | x IN prob_carrier p /\ abs((X:num->A->real) n x) > c})
     IN prob_events p`
    ASSUME_TAC THENL
  [MATCH_MP_TAC LIMSUP_EVENTS_IN_EVENTS THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  UNDISCH_TAC `null_event (p:A prob_space) (n:A->bool)` THEN
  REWRITE_TAC[null_event] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `limsup_events
       (\n. {x:A | x IN prob_carrier p /\ abs((X:num->A->real) n x) > c})`;
    `n:A->bool`] PROB_MONO) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `limsup_events
       (\n. {x:A | x IN prob_carrier p /\ abs((X:num->A->real) n x) > c})`]
    PROB_POSITIVE) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Zero covariance from bounded independence.                                *)
(* covariance(X,Y) = E[XY] - E[X]E[Y] = 0 for independent bounded X, Y.   *)
(* ------------------------------------------------------------------------- *)

let COVARIANCE_BOUNDED_INDEP = prove
  (`!p:A prob_space X Y B_X B_Y.
      random_variable p X /\ random_variable p Y /\
      (!x. x IN prob_carrier p ==> abs(X x) <= B_X) /\
      (!x. x IN prob_carrier p ==> abs(Y x) <= B_Y) /\
      indep_rv p X Y
      ==> covariance p X Y = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (X:A->real)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
   EXISTS_TAC `B_X:real` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (Y:A->real)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
   EXISTS_TAC `B_Y:real` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x. (X:A->real) x * (Y:A->real) x)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
   EXISTS_TAC `B_X * B_Y:real` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_ABS_POS]];
   ALL_TAC] THEN
  ASM_SIMP_TAC[COVARIANCE_ALT] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `Y:A->real`;
    `B_X:real`; `B_Y:real`] EXPECTATION_PRODUCT_BOUNDED_INDEP) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Truncation helper: clamp is identity when value is within bounds *)
let CLAMP_EQ_WHEN_BOUNDED = prove
  (`!x c. &0 < c /\ abs x <= c ==> min (max x (--c)) c = x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_min; real_max] THEN REAL_ARITH_TAC);;

(* Truncated partial sums converge when the original series converges *)
(* and eventually all terms are bounded by c                          *)
let AS_CONVERGENCE_TRUNCATED = prove
  (`!X c L (N:num).
      &0 < c /\
      (!n. n >= N ==> abs(X n) <= c) /\
      ((\n. sum(0..n) (\i. X i)) ---> L) sequentially
      ==> ?L2. ((\n. sum(0..n) (\i. min (max (X i) (--c)) c)) ---> L2)
               sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EXISTS_TAC `L + sum(0..N-1)
    (\i. min(max((X:num->real) i) (--c)) c - X i)` THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_TRANSFORM_EVENTUALLY) THEN
  EXISTS_TAC `\n. sum(0..n) (\i. (X:num->real) i) +
    sum(0..N-1) (\i. min(max(X i) (--c)) c - X i)` THEN
  REWRITE_TAC[BETA_THM] THEN CONJ_TAC THENL
  [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `N:num` THEN
   X_GEN_TAC `m:num` THEN DISCH_TAC THEN
   ONCE_REWRITE_TAC[REAL_ARITH `a + b = c <=> c - a = b:real`] THEN
   REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN
   SUBGOAL_THEN `!i:num. i >= N ==>
     min (max ((X:num->real) i) (--c)) c - X i = &0` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `min (max ((X:num->real) i) (--c)) c = X i`
      (fun th -> REWRITE_TAC[th] THEN REAL_ARITH_TAC) THEN
    MATCH_MP_TAC CLAMP_EQ_WHEN_BOUNDED THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
   ASM_CASES_TAC `N = 0` THENL
   [SUBGOAL_THEN `!i:num. min (max ((X:num->real) i) (--c)) c - X i = &0`
      (fun th -> REWRITE_TAC[th; SUM_0]) THEN
    GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `sum(0..m) (\i. min (max ((X:num->real) i) (--c)) c - X i) =
     sum(0..N-1) (\i. min (max (X i) (--c)) c - X i) +
     sum(N..m) (\i. min (max (X i) (--c)) c - X i)` SUBST1_TAC THENL
   [MATCH_MP_TAC(GSYM SUM_COMBINE_L) THEN ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `sum(N..m)
     (\i. min (max ((X:num->real) i) (--c)) c - X i) = &0`
     (fun th -> REWRITE_TAC[th] THEN REAL_ARITH_TAC) THEN
   MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN REPEAT STRIP_TAC THEN
   UNDISCH_TAC `!i:num. i >= N ==>
     min (max ((X:num->real) i) (--c)) c - X i = &0` THEN
   DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
   MATCH_MP_TAC REALLIM_ADD THEN ASM_REWRITE_TAC[REALLIM_CONST; ETA_AX]]);;

(* ========================================================================= *)
(* A1: Weaken INTEGRABLE_CLT -- replace char_fn identity with same CDF       *)
(* ========================================================================= *)

(* Same CDF implies same CDF of clamped versions *)
let CLAMP_DISTRIBUTION_EQ = prove
 (`!p:A prob_space (X:A->real) (Y:A->real) c.
    random_variable p X /\ random_variable p Y /\ &0 < c /\
    (!x. distribution_fn p X x = distribution_fn p Y x)
    ==> !x. distribution_fn p (\a. min (max (X a) (--c)) c) x =
            distribution_fn p (\a. min (max (Y a) (--c)) c) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real` THEN
  REWRITE_TAC[distribution_fn] THEN
  ASM_CASES_TAC `x < --c` THENL
  [SUBGOAL_THEN `{a:A | a IN prob_carrier p /\
    min (max ((X:A->real) a) (--c)) c <= x} = {}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `a:A` THEN STRIP_TAC THEN
    UNDISCH_TAC `x < --c` THEN REWRITE_TAC[REAL_NOT_LT; real_min; real_max] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `{a:A | a IN prob_carrier p /\
    min (max ((Y:A->real) a) (--c)) c <= x} = {}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `a:A` THEN STRIP_TAC THEN
    UNDISCH_TAC `x < --c` THEN REWRITE_TAC[REAL_NOT_LT; real_min; real_max] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_REAL_ARITH_TAC;
    REFL_TAC];
   ALL_TAC] THEN
  ASM_CASES_TAC `x >= c` THENL
  [SUBGOAL_THEN `{a:A | a IN prob_carrier p /\
    min (max ((X:A->real) a) (--c)) c <= x} = prob_carrier p` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `a:A` THEN
    EQ_TAC THENL [SIMP_TAC[];
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_min; real_max] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
   SUBGOAL_THEN `{a:A | a IN prob_carrier p /\
    min (max ((Y:A->real) a) (--c)) c <= x} = prob_carrier p` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `a:A` THEN
    EQ_TAC THENL [SIMP_TAC[];
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_min; real_max] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_REAL_ARITH_TAC];
    REFL_TAC];
   ALL_TAC] THEN
  (* Middle case: --c <= x < c. Both sets = {a | X/Y a <= x} *)
  SUBGOAL_THEN `--c <= x /\ x < c` STRIP_ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `{a:A | a IN prob_carrier p /\
    min (max ((X:A->real) a) (--c)) c <= x} =
    {a | a IN prob_carrier p /\ X a <= x}` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `a:A` THEN
   EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [UNDISCH_TAC `min (max ((X:A->real) a) (--c)) c <= x` THEN
    REWRITE_TAC[real_min; real_max] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[real_min; real_max] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `{a:A | a IN prob_carrier p /\
    min (max ((Y:A->real) a) (--c)) c <= x} =
    {a | a IN prob_carrier p /\ Y a <= x}` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `a:A` THEN
   EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [UNDISCH_TAC `min (max ((Y:A->real) a) (--c)) c <= x` THEN
    REWRITE_TAC[real_min; real_max] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[real_min; real_max] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_REAL_ARITH_TAC];
   ASM_MESON_TAC[distribution_fn]]);;

(* Partition existence for step function approximation *)
let PARTITION_EXISTENCE = prove
 (`!N u. ~(N = 0) /\ &0 <= u /\ u <= &N ==>
    ?j. j < N /\ &j <= u /\ u <= &(j + 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\k:num. u <= &k` num_WOP) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `?n:num. u <= &n` (fun th -> REWRITE_TAC[th]) THENL
  [EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(k:num) <= N` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
   FIRST_ASSUM(MP_TAC o SPEC `N:num`) THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  ASM_CASES_TAC `k = 0` THENL
  [SUBGOAL_THEN `u = &0` ASSUME_TAC THENL
   [UNDISCH_TAC `u <= &k` THEN UNDISCH_TAC `&0 <= u` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   EXISTS_TAC `0` THEN ASM_SIMP_TAC[LT_NZ] THEN
   ASM_REWRITE_TAC[REAL_LE_REFL; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
   ARITH_TAC;
   ALL_TAC] THEN
  EXISTS_TAC `k - 1` THEN
  SUBGOAL_THEN `k = (k - 1) + 1` ASSUME_TAC THENL
  [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
  [UNDISCH_TAC `(k:num) <= N` THEN UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
   SUBGOAL_THEN `k - 1 < k` ASSUME_TAC THENL
   [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; ALL_TAC] THEN
   FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP
     (ASSUME `!m:num. m < k ==> ~(u <= &m)`) th)) THEN
   REWRITE_TAC[REAL_NOT_LE] THEN REAL_ARITH_TAC;
   SUBGOAL_THEN `&(k - 1 + 1) = &k` (fun th -> ASM_REWRITE_TAC[th]) THEN
   REWRITE_TAC[REAL_OF_NUM_EQ] THEN
   UNDISCH_TAC `k = k - 1 + 1` THEN ARITH_TAC]);;

(* Bounded equidistributed RVs have same expectation of Lipschitz functions *)
let EQUIDIST_BOUNDED_LIPSCHITZ = prove
 (`!p:A prob_space X Y (g:real->real) L c.
    random_variable p X /\ random_variable p Y /\
    (!x. x IN prob_carrier p ==> abs(X x) <= c) /\
    (!x. x IN prob_carrier p ==> abs(Y x) <= c) /\
    (!a. distribution_fn p X a = distribution_fn p Y a) /\
    &0 < c /\ &0 < L /\
    (!a b. abs(g a - g b) <= L * abs(a - b)) /\
    integrable p (\x. g(X x)) /\ integrable p (\x. g(Y x))
    ==> expectation p (\x. g(X x)) = expectation p (\x. g(Y x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`expectation (p:A prob_space) (\x:A. (g:real->real) ((X:A->real) x))`;
                 `expectation (p:A prob_space) (\x:A. (g:real->real) ((Y:A->real) x))`;
                 `&4 * L * c`] REAL_EQ_SQUEEZE_DIV) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  CONJ_TAC THENL
  [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `1 <= N` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  (* Abbreviate partition point function *)
  ABBREV_TAC `ak = \k:num. --c + &(2 * k) * c / &N` THEN
  (* Indicator integrability for any random_variable Z *)
  SUBGOAL_THEN `!Z:A->real k. random_variable p Z ==>
    integrable p (\x:A. if Z x > (ak:num->real) k then &1 else &0)`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `Z:A->real`; `(ak:num->real) k`; `&1`]
     EXPECTATION_IF_GT) THEN ASM_REWRITE_TAC[REAL_POS] THEN SIMP_TAC[];
   ALL_TAC] THEN
  (* Indicator expectation = probability *)
  SUBGOAL_THEN `!Z:A->real k. random_variable p Z ==>
    expectation p (\x:A. if Z x > (ak:num->real) k then &1 else &0) =
    prob p {x:A | x IN prob_carrier p /\ Z x > ak k}` ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `Z:A->real`; `(ak:num->real) k`; `&1`]
     EXPECTATION_IF_GT) THEN ASM_REWRITE_TAC[REAL_POS] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LID];
   ALL_TAC] THEN
  (* Tail probability equality *)
  SUBGOAL_THEN `!a. prob p {x:A | x IN prob_carrier p /\ X x > a} =
                    prob p {x | x IN prob_carrier p /\ Y x > a}`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC EQUIDIST_TAIL_PROB_GT THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step function definition *)
  ABBREV_TAC `step = \z:real. (g:real->real)(--c) +
    sum(0..N-2) (\k. (g((ak:num->real)(k+1)) - g(ak k)) *
      (if z > ak(k+1) then &1 else &0))` THEN
  (* Step function integrability *)
  SUBGOAL_THEN `!Z:A->real. random_variable p Z ==>
    integrable p (\x:A. (step:real->real)(Z x))` ASSUME_TAC THENL
  [X_GEN_TAC `Z:A->real` THEN DISCH_TAC THEN
   EXPAND_TAC "step" THEN REWRITE_TAC[] THEN
   MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
   [REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC] THEN
   SUBGOAL_THEN
     `(\x:A. sum(0..N-2) (\k. (g((ak:num->real)(k+1)) - g(ak k)) *
       (if (Z:A->real) x > ak(k+1) then &1 else &0))) =
      (\x. sum(0..N-2)
        (\k. (\k x. (g(ak(k+1)) - g(ak k)) *
          (if Z x > ak(k+1) then &1 else &0)) k x))` SUBST1_TAC THENL
   [REWRITE_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC INTEGRABLE_SUM THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
   REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  (* Step function expectation equality: E[step(X)] = E[step(Y)] *)
  SUBGOAL_THEN
    `expectation p (\x:A. (step:real->real)((X:A->real) x)) =
     expectation p (\x. step((Y:A->real) x))` ASSUME_TAC THENL
  [EXPAND_TAC "step" THEN REWRITE_TAC[] THEN
   (* E[g(-c) + sum(...)] = g(-c) + E[sum(...)] for both X and Y *)
   SUBGOAL_THEN `!Z:A->real. random_variable p Z ==>
     expectation p (\x. (g:real->real)(--c) +
       sum(0..N-2) (\k. (g((ak:num->real)(k+1)) - g(ak k)) *
         (if Z x > ak(k+1) then &1 else &0))) =
     g(--c) + sum(0..N-2) (\k. (g(ak(k+1)) - g(ak k)) *
       prob p {x:A | x IN prob_carrier p /\ Z x > ak(k+1)})`
     (fun th -> SIMP_TAC[MATCH_MP th (ASSUME `random_variable (p:A prob_space) (X:A->real)`);
                          MATCH_MP th (ASSUME `random_variable (p:A prob_space) (Y:A->real)`)]) THENL
   [X_GEN_TAC `Z:A->real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `\x:A. (g:real->real)(--c)`;
      `\x:A. sum(0..N-2) (\k. (g((ak:num->real)(k+1)) - g(ak k)) *
         (if (Z:A->real) x > ak(k+1) then &1 else &0))`] EXPECTATION_ADD) THEN
    REWRITE_TAC[INTEGRABLE_CONST; EXPECTATION_CONST] THEN ANTS_TAC THENL
    [SUBGOAL_THEN
       `(\x:A. sum(0..N-2) (\k. (g((ak:num->real)(k+1)) - g(ak k)) *
         (if (Z:A->real) x > ak(k+1) then &1 else &0))) =
        (\x. sum(0..N-2)
          (\k. (\k x. (g(ak(k+1)) - g(ak k)) *
            (if Z x > ak(k+1) then &1 else &0)) k x))` SUBST1_TAC THENL
     [REWRITE_TAC[]; ALL_TAC] THEN
     MATCH_MP_TAC INTEGRABLE_SUM THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
     REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_SIMP_TAC[];
     ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_EQ_ADD_LCANCEL] THEN
    (* E[sum(...)] = sum(E[...]) *)
    SUBGOAL_THEN
      `(\x:A. sum(0..N-2) (\k. (g((ak:num->real)(k+1)) - g(ak k)) *
        (if (Z:A->real) x > ak(k+1) then &1 else &0))) =
       (\x. sum(0..N-2) (\k. (\k x. (g(ak(k+1)) - g(ak k)) *
         (if Z x > ak(k+1) then &1 else &0)) k x))` SUBST1_TAC THENL
    [REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`p:A prob_space`;
      `\k:num (x:A). (g((ak:num->real)(k+1)) - g(ak k)) *
        (if (Z:A->real) x > ak(k+1) then &1 else &0)`;
      `N - 2`] EXPECTATION_SUM) THEN REWRITE_TAC[] THEN ANTS_TAC THENL
    [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
     MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p:A prob_space`;
      `(g:real->real)((ak:num->real)(k+1)) - g(ak k)`;
      `\x:A. if (Z:A->real) x > (ak:num->real)(k+1) then &1 else &0`]
      EXPECTATION_CMUL) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o BETA_RULE) THEN AP_TERM_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
   (* Now both sides have form g(-c) + sum(d_k * P(Z > a_k)) *)
   REWRITE_TAC[REAL_EQ_ADD_LCANCEL] THEN
   MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
   REWRITE_TAC[REAL_EQ_MUL_LCANCEL] THEN DISJ2_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Pointwise bound: |g(z) - step(z)| <= 2*L*c/N for |z| <= c *)
  SUBGOAL_THEN `!z. abs z <= c ==>
    abs((g:real->real) z - (step:real->real) z) <= &2 * L * c / &N`
    ASSUME_TAC THENL
  [X_GEN_TAC `z:real` THEN DISCH_TAC THEN
   EXPAND_TAC "step" THEN REWRITE_TAC[] THEN
   (* Use PARTITION_EXISTENCE to find interval containing z *)
   SUBGOAL_THEN `&0 < &2 * c / &N` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
    [REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_LT_DIV THEN
     ASM_SIMP_TAC[REAL_OF_NUM_LT; LE_1]];
    ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= (z + c) / (&2 * c / &N) /\
                  (z + c) / (&2 * c / &N) <= &N` ASSUME_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
     ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
     SUBGOAL_THEN `&N * (&2 * c / &N) = &2 * c` SUBST1_TAC THENL
     [SUBGOAL_THEN `~(&N = &0)` MP_TAC THENL
      [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      CONV_TAC REAL_FIELD; ALL_TAC] THEN
     ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
   MP_TAC(SPECL [`N:num`; `(z + c) / (&2 * c / &N)`] PARTITION_EXISTENCE) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
   (* z is in [ak j, ak(j+1)] *)
   SUBGOAL_THEN `(ak:num->real) j <= z /\ z <= ak(j + 1)` ASSUME_TAC THENL
   [EXPAND_TAC "ak" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `&(2 * j) * c / &N = &j * (&2 * c / &N) /\
                  &(2 * (j + 1)) * c / &N = &(j + 1) * (&2 * c / &N)`
      (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
     CONJ_TAC THEN CONV_TAC REAL_FIELD;
     ALL_TAC] THEN
    UNDISCH_TAC `&j <= (z + c) / (&2 * c / &N)` THEN
    UNDISCH_TAC `(z + c) / (&2 * c / &N) <= &(j + 1)` THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
   (* Case split: z > ak j (strict) vs z = ak j (boundary) *)
   ASM_CASES_TAC `z > (ak:num->real) j` THENL
   [(* Case 1: z > ak j -- indicators are 1 iff k+1 <= j *)
    SUBGOAL_THEN
      `sum(0..N-2) (\k. ((g:real->real)((ak:num->real)(k+1)) - g(ak k)) *
        (if z > ak(k+1) then &1 else &0)) =
       sum(0..N-2) (\k. if k + 1 <= j
         then g(ak(k+1)) - g(ak k) else &0)` SUBST1_TAC THENL
    [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
     BETA_TAC THEN ASM_CASES_TAC `k + 1 <= j` THENL
     [SUBGOAL_THEN `z > (ak:num->real)(k + 1)` ASSUME_TAC THENL
      [SUBGOAL_THEN `ak(k + 1) <= ak j` MP_TAC THENL
       [EXPAND_TAC "ak" THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
        [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
        [REWRITE_TAC[REAL_OF_NUM_LE; GSYM REAL_OF_NUM_MUL] THEN
         ASM_ARITH_TAC;
         MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC];
       ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      SUBGOAL_THEN `~(z > (ak:num->real)(k + 1))` ASSUME_TAC THENL
      [REWRITE_TAC[real_gt; REAL_NOT_LT] THEN
       SUBGOAL_THEN `ak(j + 1) <= ak(k + 1)` MP_TAC THENL
       [EXPAND_TAC "ak" THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
        [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
        [REWRITE_TAC[REAL_OF_NUM_LE; GSYM REAL_OF_NUM_MUL] THEN
         ASM_ARITH_TAC;
         MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC];
       ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]];
     ALL_TAC] THEN
    (* Handle j = 0 separately: all conditional terms are 0 *)
    ASM_CASES_TAC `j = 0` THENL
    [ASM_REWRITE_TAC[ARITH_RULE `k + 1 <= 0 <=> F`] THEN
     REWRITE_TAC[SUM_0; REAL_ADD_RID] THEN
     SUBGOAL_THEN `(ak:num->real) 0 = --c` ASSUME_TAC THENL
     [EXPAND_TAC "ak" THEN
      REWRITE_TAC[MULT_CLAUSES; REAL_MUL_LZERO; real_div; REAL_MUL_LZERO] THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN `&2 * L * c / &N = L * (&2 * c / &N)` SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `L * abs(z - --(c:real))` THEN
     ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
     SUBGOAL_THEN `(ak:num->real)(0 + 1) = --c + &2 * c / &N`
       ASSUME_TAC THENL
     [EXPAND_TAC "ak" THEN REWRITE_TAC[ARITH] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
     UNDISCH_TAC `(ak:num->real) j <= z /\ z <= ak(j + 1)` THEN
     ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
    (* j >= 1: Telescoping via SUM_RESTRICT_SET *)
    REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
    SUBGOAL_THEN `{k | k IN 0..N-2 /\ k + 1 <= j} = 0..j-1`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
     X_GEN_TAC `k:num` THEN ASM_ARITH_TAC;
     ALL_TAC] THEN
    REWRITE_TAC[SUM_DIFFS_ALT; LE_0; ADD_CLAUSES] THEN
    SUBGOAL_THEN `j - 1 + 1 = j` SUBST1_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `(ak:num->real) 0 = --c` ASSUME_TAC THENL
    [EXPAND_TAC "ak" THEN
     REWRITE_TAC[MULT_CLAUSES; REAL_MUL_LZERO; real_div; REAL_MUL_LZERO] THEN
     REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `!x y z:real. x - (y + (z - y)) = x - z`] THEN
    SUBGOAL_THEN `(ak:num->real)(j + 1) = ak j + &2 * c / &N`
      ASSUME_TAC THENL
    [EXPAND_TAC "ak" THEN
     REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD; real_div] THEN
     CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN `&2 * L * c / &N = L * (&2 * c / &N)` SUBST1_TAC THENL
    [REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `L * abs(z - (ak:num->real) j)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `abs(z - (ak:num->real) j) <= &2 * c / &N` MP_TAC THENL
    [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    (* Case 2: ~(z > ak j), so z = ak j *)
    SUBGOAL_THEN `z = (ak:num->real) j` SUBST_ALL_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `j = 0` THENL
    [(* j = 0: ak 0 = --c, all indicators are false *)
     SUBGOAL_THEN `(ak:num->real) 0 = --c` ASSUME_TAC THENL
     [EXPAND_TAC "ak" THEN
      REWRITE_TAC[MULT_CLAUSES; REAL_MUL_LZERO; real_div; REAL_MUL_LZERO] THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN
       `!k. k IN 0..N-2 ==>
        ((g:real->real)((ak:num->real)(k+1)) - g(ak k)) *
        (if --c > ak(k+1) then &1 else &0) = &0` MP_TAC THENL
     [REPEAT STRIP_TAC THEN BETA_TAC THEN
      SUBGOAL_THEN `~(--c > (ak:num->real)(k + 1))` ASSUME_TAC THENL
      [REWRITE_TAC[real_gt; REAL_NOT_LT] THEN
       EXPAND_TAC "ak" THEN REWRITE_TAC[] THEN
       MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> --c <= --c + x`) THEN
       MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
       ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      DISCH_TAC THEN
      ASM_SIMP_TAC[SUM_EQ_0] THEN
      REWRITE_TAC[REAL_ADD_RID; REAL_SUB_REFL; REAL_ABS_0] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
      [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
     ALL_TAC] THEN
    (* j >= 1: indicators are 1 iff k+2 <= j (i.e., ak j > ak(k+1)) *)
    SUBGOAL_THEN `1 <= j` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
      `sum(0..N-2) (\k. ((g:real->real)((ak:num->real)(k+1)) - g(ak k)) *
        (if (ak:num->real) j > ak(k+1) then &1 else &0)) =
       sum(0..N-2) (\k. if k + 2 <= j
         then g(ak(k+1)) - g(ak k) else &0)` SUBST1_TAC THENL
    [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
     BETA_TAC THEN ASM_CASES_TAC `k + 2 <= j` THENL
     [SUBGOAL_THEN `(ak:num->real) j > ak(k + 1)` ASSUME_TAC THENL
      [REWRITE_TAC[real_gt] THEN EXPAND_TAC "ak" THEN REWRITE_TAC[] THEN
       REWRITE_TAC[REAL_ARITH `!c a b:real. --c + a < --c + b <=> a < b`] THEN
       MATCH_MP_TAC REAL_LT_RMUL THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LT; GSYM REAL_OF_NUM_MUL] THEN ASM_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_DIV THEN
        ASM_SIMP_TAC[REAL_OF_NUM_LT; LE_1]];
       ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      SUBGOAL_THEN `~((ak:num->real) j > ak(k + 1))` ASSUME_TAC THENL
      [REWRITE_TAC[real_gt; REAL_NOT_LT] THEN
       EXPAND_TAC "ak" THEN REWRITE_TAC[] THEN
       MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
       MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LE; GSYM REAL_OF_NUM_MUL] THEN ASM_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
       ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]];
     ALL_TAC] THEN
    (* k+2 <= j iff k+1 <= j-1 *)
    SUBGOAL_THEN `!k:num. k + 2 <= j <=> k + 1 <= j - 1`
      (fun th -> REWRITE_TAC[th]) THENL
    [GEN_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    (* Telescoping via SUM_RESTRICT_SET *)
    (* Handle j - 1 = 0, i.e., j = 1 separately *)
    ASM_CASES_TAC `j - 1 = 0` THENL
    [(* j = 1: use Lipschitz bound on g(ak 1) - g(ak 0) *)
     ASM_REWRITE_TAC[ARITH_RULE `k + 1 <= 0 <=> F`] THEN
     REWRITE_TAC[SUM_0] THEN
     SUBGOAL_THEN `(ak:num->real) 0 = --c` ASSUME_TAC THENL
     [EXPAND_TAC "ak" THEN
      REWRITE_TAC[MULT_CLAUSES; REAL_MUL_LZERO; real_div; REAL_MUL_LZERO] THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `j = 1` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC[REAL_ADD_RID] THEN
     SUBGOAL_THEN `&2 * L * c / &N = L * (&2 * c / &N)` SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `L * abs((ak:num->real) 1 - ak 0)` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
     SUBGOAL_THEN `(ak:num->real) 1 = --c + &2 * c / &N` ASSUME_TAC THENL
     [EXPAND_TAC "ak" THEN REWRITE_TAC[ARITH] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN `&0 <= &2 * c / &N` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
      [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC];
     ALL_TAC] THEN
    (* j >= 2: telescope via SUM_RESTRICT_SET *)
    REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
    SUBGOAL_THEN `{k | k IN 0..N-2 /\ k + 1 <= j - 1} = 0..j-1-1`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
     X_GEN_TAC `k:num` THEN ASM_ARITH_TAC;
     ALL_TAC] THEN
    REWRITE_TAC[SUM_DIFFS_ALT; LE_0; ADD_CLAUSES] THEN
    SUBGOAL_THEN `j - 1 - 1 + 1 = j - 1` SUBST1_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `(ak:num->real) 0 = --c` ASSUME_TAC THENL
    [EXPAND_TAC "ak" THEN
     REWRITE_TAC[MULT_CLAUSES; REAL_MUL_LZERO; real_div; REAL_MUL_LZERO] THEN
     REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `!x y z:real. x - (y + (z - y)) = x - z`] THEN
    (* |g(ak j) - g(ak(j-1))| <= L * |ak j - ak(j-1)| <= 2Lc/N *)
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `L * abs((ak:num->real) j - ak(j - 1))` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&2 * L * c / &N = L * (&2 * c / &N)` SUBST1_TAC THENL
    [REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    EXPAND_TAC "ak" THEN REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `!c a b:real. (--c + a) - (--c + b) = a - b`] THEN
    SUBGOAL_THEN `2 * (j - 1) <= 2 * j` ASSUME_TAC THENL
    [ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&(2 * j) * c / &N - &(2 * (j - 1)) * c / &N =
                   &(2 * j - 2 * (j - 1)) * c / &N` SUBST1_TAC THENL
    [ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `2 * j - 2 * (j - 1) = 2` SUBST1_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &2 * c / &N` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
     ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x <= x`]];
   ALL_TAC] THEN
  (* Combine: |E[g(X)] - E[g(Y)]| <= 4Lc/N via EXPECTATION_MONO *)
  SUBGOAL_THEN `!Z:A->real. random_variable p Z /\
    integrable p (\x. (g:real->real)(Z x)) /\
    (!x. x IN prob_carrier p ==> abs(Z x) <= c) ==>
    abs(expectation p (\x. g(Z x)) -
        expectation p (\x. (step:real->real)(Z x))) <= &2 * L * c / &N`
    ASSUME_TAC THENL
  [X_GEN_TAC `Z:A->real` THEN STRIP_TAC THEN
   REWRITE_TAC[REAL_ABS_BOUNDS] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_ARITH `--a <= b - c <=> c <= b + a`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `expectation p (\x:A. (g:real->real)(Z x) + &2 * L * c / &N)` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC EXPECTATION_MONO THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[INTEGRABLE_CONST];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      MP_TAC(SPEC `(Z:A->real) x` (ASSUME `!z. abs z <= c ==>
        abs((g:real->real) z - (step:real->real) z) <= &2 * L * c / &N`)) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REAL_ARITH_TAC];
     MP_TAC(ISPECL [`p:A prob_space`; `\x:A. (g:real->real)((Z:A->real) x)`;
       `\x:A. &2 * L * c / &N`] EXPECTATION_ADD) THEN
     ASM_REWRITE_TAC[INTEGRABLE_CONST; EXPECTATION_CONST] THEN
     REAL_ARITH_TAC];
    REWRITE_TAC[REAL_ARITH `b - c <= a <=> b <= c + a`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `expectation p (\x:A. (step:real->real)((Z:A->real) x) + &2 * L * c / &N)` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC EXPECTATION_MONO THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_ADD THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[]; REWRITE_TAC[INTEGRABLE_CONST]];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      MP_TAC(SPEC `(Z:A->real) x` (ASSUME `!z. abs z <= c ==>
        abs((g:real->real) z - (step:real->real) z) <= &2 * L * c / &N`)) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REAL_ARITH_TAC];
     MP_TAC(ISPECL [`p:A prob_space`; `\x:A. (step:real->real)((Z:A->real) x)`;
       `\x:A. &2 * L * c / &N`] EXPECTATION_ADD) THEN
     ASM_SIMP_TAC[INTEGRABLE_CONST; EXPECTATION_CONST] THEN
     REAL_ARITH_TAC]];
   ALL_TAC] THEN
  (* Final: two-term bound using step equality *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(expectation p (\x:A. (g:real->real)((X:A->real) x)) -
    expectation p (\x. (step:real->real)(X x))) +
    abs(expectation p (\x. (g:real->real)((Y:A->real) x)) -
        expectation p (\x. (step:real->real)(Y x)))` THEN
  CONJ_TAC THENL
  [SUBGOAL_THEN
     `expectation p (\x:A. (g:real->real)((X:A->real) x)) -
      expectation p (\x. g((Y:A->real) x)) =
      (expectation p (\x. g(X x)) - expectation p (\x. (step:real->real)(X x))) -
      (expectation p (\x. g(Y x)) - expectation p (\x. step(Y x)))` SUBST1_TAC THENL
   [MP_TAC(ASSUME `expectation p (\x:A. (step:real->real)((X:A->real) x)) =
      expectation p (\x. step((Y:A->real) x))`) THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC];
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * L * c / &N + &2 * L * c / &N` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[REAL_ARITH `&2 * L * c / N + &2 * L * c / N =
     &4 * L * c / N`] THEN REAL_ARITH_TAC]);;

(* Same CDF implies same characteristic function *)
let CHAR_FN_EQ_OF_SAME_DIST = prove
 (`!p:A prob_space (X:A->real) (Y:A->real) t.
    random_variable p X /\ random_variable p Y /\
    (!x. distribution_fn p X x = distribution_fn p Y x)
    ==> char_fn_re p X t = char_fn_re p Y t /\
        char_fn_im p X t = char_fn_im p Y t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[char_fn_re; char_fn_im] THEN BETA_TAC THEN
  (* Bounded case: for each M, clamped expectations agree *)
  SUBGOAL_THEN
    `!M. expectation (p:A prob_space)
      (\a:A. cos(t * min (max ((X:A->real) a) (-- &(SUC M))) (&(SUC M)))) =
      expectation p
      (\a. cos(t * min (max ((Y:A->real) a) (-- &(SUC M))) (&(SUC M)))) /\
      expectation p
      (\a:A. sin(t * min (max ((X:A->real) a) (-- &(SUC M))) (&(SUC M)))) =
      expectation p
      (\a. sin(t * min (max ((Y:A->real) a) (-- &(SUC M))) (&(SUC M))))`
    (LABEL_TAC "bounded") THENL
  [GEN_TAC THEN CONJ_TAC THENL
   [(* cos case: apply EQUIDIST_BOUNDED_LIPSCHITZ to clamped RVs *)
    MP_TAC(ISPECL [
      `p:A prob_space`;
      `\a:A. min (max ((X:A->real) a) (-- &(SUC M))) (&(SUC M))`;
      `\a:A. min (max ((Y:A->real) a) (-- &(SUC M))) (&(SUC M))`;
      `\x:real. cos(t * x)`;
      `abs(t) + &1`;
      `&(SUC M)`] EQUIDIST_BOUNDED_LIPSCHITZ) THEN
    BETA_TAC THEN ANTS_TAC THENL
    [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RANDOM_VARIABLE_CLAMP THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RANDOM_VARIABLE_CLAMP THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC CLAMP_BOUND THEN
      REWRITE_TAC[REAL_OF_NUM_LT; LT_0];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC CLAMP_BOUND THEN
      REWRITE_TAC[REAL_OF_NUM_LT; LT_0];
      MATCH_MP_TAC CLAMP_DISTRIBUTION_EQ THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LT; LT_0];
      REWRITE_TAC[REAL_OF_NUM_LT; LT_0];
      MP_TAC(SPEC `t:real` REAL_ABS_POS) THEN REAL_ARITH_TAC;
      REPEAT GEN_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `abs(t * a - t * b)` THEN CONJ_TAC THENL
      [MATCH_ACCEPT_TAC COS_LIPSCHITZ;
       REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
       MATCH_MP_TAC REAL_LE_MUL2 THEN
       REWRITE_TAC[REAL_ABS_POS; REAL_LE_REFL] THEN REAL_ARITH_TAC];
      MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `&1` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC RANDOM_VARIABLE_COS THEN
       MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN
       MATCH_MP_TAC RANDOM_VARIABLE_CLAMP THEN ASM_REWRITE_TAC[];
       REPEAT STRIP_TAC THEN REWRITE_TAC[COS_BOUND]];
      MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `&1` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC RANDOM_VARIABLE_COS THEN
       MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN
       MATCH_MP_TAC RANDOM_VARIABLE_CLAMP THEN ASM_REWRITE_TAC[];
       REPEAT STRIP_TAC THEN REWRITE_TAC[COS_BOUND]]];
     SIMP_TAC[]];
    (* sin case: same structure *)
    MP_TAC(ISPECL [
      `p:A prob_space`;
      `\a:A. min (max ((X:A->real) a) (-- &(SUC M))) (&(SUC M))`;
      `\a:A. min (max ((Y:A->real) a) (-- &(SUC M))) (&(SUC M))`;
      `\x:real. sin(t * x)`;
      `abs(t) + &1`;
      `&(SUC M)`] EQUIDIST_BOUNDED_LIPSCHITZ) THEN
    BETA_TAC THEN ANTS_TAC THENL
    [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RANDOM_VARIABLE_CLAMP THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RANDOM_VARIABLE_CLAMP THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC CLAMP_BOUND THEN
      REWRITE_TAC[REAL_OF_NUM_LT; LT_0];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC CLAMP_BOUND THEN
      REWRITE_TAC[REAL_OF_NUM_LT; LT_0];
      MATCH_MP_TAC CLAMP_DISTRIBUTION_EQ THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LT; LT_0];
      REWRITE_TAC[REAL_OF_NUM_LT; LT_0];
      MP_TAC(SPEC `t:real` REAL_ABS_POS) THEN REAL_ARITH_TAC;
      REPEAT GEN_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `abs(t * a - t * b)` THEN CONJ_TAC THENL
      [MATCH_ACCEPT_TAC SIN_LIPSCHITZ;
       REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
       MATCH_MP_TAC REAL_LE_MUL2 THEN
       REWRITE_TAC[REAL_ABS_POS; REAL_LE_REFL] THEN REAL_ARITH_TAC];
      MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `&1` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC RANDOM_VARIABLE_SIN THEN
       MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN
       MATCH_MP_TAC RANDOM_VARIABLE_CLAMP THEN ASM_REWRITE_TAC[];
       REPEAT STRIP_TAC THEN REWRITE_TAC[SIN_BOUND]];
      MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `&1` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC RANDOM_VARIABLE_SIN THEN
       MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN
       MATCH_MP_TAC RANDOM_VARIABLE_CLAMP THEN ASM_REWRITE_TAC[];
       REPEAT STRIP_TAC THEN REWRITE_TAC[SIN_BOUND]]];
     SIMP_TAC[]]];
   ALL_TAC] THEN
  (* DCT: clamp(Z,M) --> Z implies E[trig(t*clamp(Z,M))] --> E[trig(t*Z)] *)
  SUBGOAL_THEN
    `!Z:A->real. random_variable p Z ==>
      ((\n. expectation (p:A prob_space)
        (\a. cos(t * min (max (Z a) (-- &(SUC n))) (&(SUC n)))))
       ---> expectation p (\a. cos(t * Z a))) sequentially /\
      ((\n. expectation (p:A prob_space)
        (\a. sin(t * min (max (Z a) (-- &(SUC n))) (&(SUC n)))))
       ---> expectation p (\a. sin(t * Z a))) sequentially`
    (LABEL_TAC "dct") THENL
  [X_GEN_TAC `Z:A->real` THEN DISCH_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`p:A prob_space`;
      `\n:num (a:A). cos(t * min (max ((Z:A->real) a) (-- &(SUC n))) (&(SUC n)))`;
      `\a:A. cos(t * (Z:A->real) a)`;
      `\a:A. &1`] DOMINATED_CONVERGENCE) THEN
    BETA_TAC THEN ANTS_TAC THENL
    [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `&1` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC RANDOM_VARIABLE_COS THEN
       MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN
       MATCH_MP_TAC RANDOM_VARIABLE_CLAMP THEN ASM_REWRITE_TAC[];
       REPEAT STRIP_TAC THEN REWRITE_TAC[COS_BOUND]];
      REWRITE_TAC[INTEGRABLE_CONST];
      REPEAT STRIP_TAC THEN REWRITE_TAC[COS_BOUND];
      X_GEN_TAC `a:A` THEN DISCH_TAC THEN
      MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
      EXISTS_TAC `\n:num. cos(t * (Z:A->real) a)` THEN CONJ_TAC THENL
      [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
       MP_TAC(SPEC `abs((Z:A->real) a)` REAL_ARCH_SIMPLE) THEN
       STRIP_TAC THEN EXISTS_TAC `n:num` THEN
       X_GEN_TAC `m:num` THEN DISCH_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
       SUBGOAL_THEN `&n <= &(SUC m)` MP_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
       REWRITE_TAC[real_min; real_max] THEN
       REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
       ASM_REAL_ARITH_TAC;
       REWRITE_TAC[REALLIM_CONST]]];
     SIMP_TAC[]];
    (* sin part: same proof structure *)
    MP_TAC(ISPECL
     [`p:A prob_space`;
      `\n:num (a:A). sin(t * min (max ((Z:A->real) a) (-- &(SUC n))) (&(SUC n)))`;
      `\a:A. sin(t * (Z:A->real) a)`;
      `\a:A. &1`] DOMINATED_CONVERGENCE) THEN
    BETA_TAC THEN ANTS_TAC THENL
    [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `&1` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC RANDOM_VARIABLE_SIN THEN
       MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN
       MATCH_MP_TAC RANDOM_VARIABLE_CLAMP THEN ASM_REWRITE_TAC[];
       REPEAT STRIP_TAC THEN REWRITE_TAC[SIN_BOUND]];
      REWRITE_TAC[INTEGRABLE_CONST];
      REPEAT STRIP_TAC THEN REWRITE_TAC[SIN_BOUND];
      X_GEN_TAC `a:A` THEN DISCH_TAC THEN
      MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
      EXISTS_TAC `\n:num. sin(t * (Z:A->real) a)` THEN CONJ_TAC THENL
      [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
       MP_TAC(SPEC `abs((Z:A->real) a)` REAL_ARCH_SIMPLE) THEN
       STRIP_TAC THEN EXISTS_TAC `n:num` THEN
       X_GEN_TAC `m:num` THEN DISCH_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
       SUBGOAL_THEN `&n <= &(SUC m)` MP_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
       REWRITE_TAC[real_min; real_max] THEN
       REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
       ASM_REAL_ARITH_TAC;
       REWRITE_TAC[REALLIM_CONST]]];
     SIMP_TAC[]]];
   ALL_TAC] THEN
  (* Combine: REALLIM_UNIQUE + REALLIM_TRANSFORM_EVENTUALLY *)
  CONJ_TAC THENL
  [MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
   EXISTS_TAC `\n:num. expectation (p:A prob_space)
     (\a:A. cos(t * min (max ((X:A->real) a) (-- &(SUC n))) (&(SUC n))))` THEN
   REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [USE_THEN "dct" (fun th -> MP_TAC(CONJUNCT1(MATCH_MP th
      (ASSUME `random_variable (p:A prob_space) (X:A->real)`)))) THEN
    REWRITE_TAC[];
    MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC `\n:num. expectation (p:A prob_space)
      (\a:A. cos(t * min (max ((Y:A->real) a) (-- &(SUC n))) (&(SUC n))))` THEN
    CONJ_TAC THENL
    [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
     REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
     USE_THEN "bounded" (fun th -> REWRITE_TAC[CONJUNCT1(SPEC `n:num` th)]);
     USE_THEN "dct" (fun th -> MP_TAC(CONJUNCT1(MATCH_MP th
       (ASSUME `random_variable (p:A prob_space) (Y:A->real)`)))) THEN
     REWRITE_TAC[]]];
   (* sin part *)
   MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
   EXISTS_TAC `\n:num. expectation (p:A prob_space)
     (\a:A. sin(t * min (max ((X:A->real) a) (-- &(SUC n))) (&(SUC n))))` THEN
   REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [USE_THEN "dct" (fun th -> MP_TAC(CONJUNCT2(MATCH_MP th
      (ASSUME `random_variable (p:A prob_space) (X:A->real)`)))) THEN
    REWRITE_TAC[];
    MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC `\n:num. expectation (p:A prob_space)
      (\a:A. sin(t * min (max ((Y:A->real) a) (-- &(SUC n))) (&(SUC n))))` THEN
    CONJ_TAC THENL
    [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
     REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
     USE_THEN "bounded" (fun th -> REWRITE_TAC[CONJUNCT2(SPEC `n:num` th)]);
     USE_THEN "dct" (fun th -> MP_TAC(CONJUNCT2(MATCH_MP th
       (ASSUME `random_variable (p:A prob_space) (Y:A->real)`)))) THEN
     REWRITE_TAC[]]]]);;

(* CLT with same-distribution hypothesis instead of char_fn identity *)
let INTEGRABLE_CLT_IID = prove
 (`!p:A prob_space (X:num->A->real).
    (!n. integrable p (X n)) /\
    (!n. integrable p (\x. X n x pow 2)) /\
    (!i. expectation p (X i) = &0) /\
    &0 < variance p (X 0) /\
    (!i. variance p (X i) = variance p (X 0)) /\
    (!i j:num. ~(i = j) ==> indep_rv p (X i) (X j)) /\
    (!i a. distribution_fn p (X i) a = distribution_fn p (X 0) a) /\
    (!n k. k < n ==> indep_rv p (\x. sum(0..k) (\i. X i x)) (X (SUC k)))
    ==> !x:real. ((\n. cdf p
                (\a. sum(0..n) (\i. X i a) /
                     (sqrt(variance p (X 0)) * sqrt(&(SUC n)))) x)
             ---> std_normal_cdf x) sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ths = CONJUNCTS th in
    MAP_EVERY ASSUME_TAC (subtract ths [el 6 ths]) THEN
    LABEL_TAC "dist_eq" (el 6 ths)) THEN
  SUBGOAL_THEN `!i t. char_fn_re (p:A prob_space) ((X:num->A->real) i) t =
    char_fn_re p (X 0) t /\ char_fn_im p (X i) t = char_fn_im p (X 0) t`
    ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN MATCH_MP_TAC CHAR_FN_EQ_OF_SAME_DIST THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_MESON_TAC[];
    CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_MESON_TAC[];
     GEN_TAC THEN USE_THEN "dist_eq" (fun th ->
       MATCH_ACCEPT_TAC(SPECL [`i:num`; `a:real`] th))]];
   ALL_TAC] THEN
  REMOVE_THEN "dist_eq" (fun _ -> ALL_TAC) THEN
  MATCH_MP_TAC INTEGRABLE_CLT THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC);;


(* ======================================================================== *)
(* General Levy Continuity Theorem                                          *)
(* ======================================================================== *)

(* GENERAL_TRIG_POLY_WEAK_CONVERGENCE:
   Generalizes TRIG_POLY_WEAK_CONVERGENCE to arbitrary char fn limits
   phi_re, phi_im instead of exp(-t^2/2) and 0. *)
let GENERAL_TRIG_POLY_WEAK_CONVERGENCE = prove
 (`!p:A prob_space (X:num->A->real) (phi_re:real->real) (phi_im:real->real)
     m (a:num->real) (b:num->real) (freq:num->real).
     (!n. random_variable p (X n)) /\
     (!t. ((\n. char_fn_re p (X n) t) ---> phi_re t) sequentially) /\
     (!t. ((\n. char_fn_im p (X n) t) ---> phi_im t) sequentially)
     ==> ((\n. expectation p
                (\x. sum(0..m) (\k. a k * cos(freq k * X n x) +
                                     b k * sin(freq k * X n x)))) --->
          sum(0..m) (\k. a k * phi_re(freq k) + b k * phi_im(freq k)))
         sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Step 1: Decompose expectation of trig poly into char fn terms *)
  SUBGOAL_THEN
    `!n:num. expectation (p:A prob_space)
       (\x:A. sum(0..m) (\k. (a:num->real) k * cos((freq:num->real) k * (X:num->A->real) n x) +
                               (b:num->real) k * sin(freq k * X n x))) =
     sum(0..m) (\k. a k * char_fn_re p (X n) (freq k) +
                     b k * char_fn_im p (X n) (freq k))`
    ASSUME_TAC THENL
  [GEN_TAC THEN
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
   REWRITE_TAC[char_fn_re; char_fn_im];
   ALL_TAC] THEN
  (* Step 2: Apply limit decomposition *)
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\n:num. sum(0..m) (\k. (a:num->real) k * char_fn_re (p:A prob_space) ((X:num->A->real) n) ((freq:num->real) k) +
                                       (b:num->real) k * char_fn_im p (X n) (freq k))` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
   EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 3: Sum of convergent sequences converges *)
  MATCH_MP_TAC REALLIM_SUM THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_NUMSEG] THEN DISCH_TAC THEN
  BETA_TAC THEN
  MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
  [MATCH_MP_TAC REALLIM_LMUL THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC REALLIM_LMUL THEN ASM_REWRITE_TAC[]]);;

(* Helper: if |a - b| < e for all e > 0, then a = b *)
let REAL_EQ_OF_ABS_LT_ALL = prove
 (`(!e. &0 < e ==> abs(a - b) < e) ==> a = b`,
  DISCH_TAC THEN
  SUBGOAL_THEN `abs(a - b:real) = &0` MP_TAC THENL
  [REWRITE_TAC[GSYM REAL_LE_ANTISYM; REAL_ABS_POS] THEN
   REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `abs(a - b:real)`) THEN
   ASM_REWRITE_TAC[REAL_LT_REFL];
   SIMP_TAC[REAL_ABS_ZERO; REAL_SUB_0]]);;

(* GENERAL_WEAK_CONVERGENCE_CONVERGENT:
   Under char fn convergence + bounded second moments,
   E[g(X_n)] converges for any bounded continuous g.
   Key new result enabling the general Levy theorem. *)
let GENERAL_WEAK_CONVERGENCE_CONVERGENT = prove
 (`!p:A prob_space (X:num->A->real) (phi_re:real->real) (phi_im:real->real)
     (g:real->real) BB.
     (!n. random_variable p (X n)) /\
     (!n. integrable p (X n)) /\
     (!n. integrable p (\x. X n x pow 2)) /\
     (?C. &0 < C /\ !n. expectation p (\x. X n x pow 2) <= C) /\
     (!t. ((\n. char_fn_re p (X n) t) ---> phi_re t) sequentially) /\
     (!t. ((\n. char_fn_im p (X n) t) ---> phi_im t) sequentially) /\
     (!y. g real_continuous atreal y) /\
     &0 < BB /\ (!y. abs(g y) <= BB) /\
     (!n. integrable p (\a. g(X n a)))
     ==> ?l. ((\n. expectation p (\a:A. g(X n a))) ---> l) sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `CC:real` STRIP_ASSUME_TAC) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  (* Strategy: REALLIM_SUBSEQ_SAME_LIMIT.
     First get ONE convergent subsequence via BW to determine the limit,
     then show every sub-subsequential limit equals it. *)
  (* BW gives a convergent subsequence *)
  MP_TAC(ISPECL
    [`\n:num. expectation (p:A prob_space)
       (\a:A. (g:real->real) ((X:num->A->real) n a))`;
     `BB:real`] BOUNDED_REAL_SEQ_HAS_CONVERGENT_SUBSEQ) THEN
  BETA_TAC THEN ANTS_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `expectation (p:A prob_space)
     (\a:A. abs((g:real->real) ((X:num->A->real) n a)))` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC EXPECTATION_ABS_BOUND THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `expectation (p:A prob_space) (\a:A. BB)` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC EXPECTATION_MONO THEN
     ASM_REWRITE_TAC[INTEGRABLE_CONST] THEN
     MP_TAC(ISPECL [`p:A prob_space`;
       `\a:A. (g:real->real)((X:num->A->real) n a)`] INTEGRABLE_ABS) THEN
     REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[EXPECTATION_CONST] THEN
     UNDISCH_TAC `&0 < BB` THEN REAL_ARITH_TAC]];
   ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L0:real`
    (X_CHOOSE_THEN `r0:num->num` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `L0:real` THEN
  (* Now show full sequence converges to L0 via REALLIM_SUBSEQ_SAME_LIMIT *)
  MATCH_MP_TAC(ISPECL
    [`\n:num. expectation (p:A prob_space)
       (\a:A. (g:real->real) ((X:num->A->real) n a))`;
     `L0:real`; `BB:real`] REALLIM_SUBSEQ_SAME_LIMIT) THEN
  BETA_TAC THEN CONJ_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `expectation (p:A prob_space)
     (\a:A. abs((g:real->real) ((X:num->A->real) n a)))` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC EXPECTATION_ABS_BOUND THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `expectation (p:A prob_space) (\a:A. BB)` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC EXPECTATION_MONO THEN
     ASM_REWRITE_TAC[INTEGRABLE_CONST] THEN
     MP_TAC(ISPECL [`p:A prob_space`;
       `\a:A. (g:real->real)((X:num->A->real) n a)`] INTEGRABLE_ABS) THEN
     REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[EXPECTATION_CONST] THEN
     UNDISCH_TAC `&0 < BB` THEN REAL_ARITH_TAC]];
   ALL_TAC] THEN
  (* For any subseq r, find sub-sub s with E[g(X_{r(s(k))})] -> L0 *)
  X_GEN_TAC `r:num->num` THEN DISCH_TAC THEN
  (* BW on the subsequence gives convergent sub-sub *)
  MP_TAC(ISPECL
    [`\k:num. expectation (p:A prob_space)
       (\a:A. (g:real->real) ((X:num->A->real) ((r:num->num) k) a))`;
     `BB:real`] BOUNDED_REAL_SEQ_HAS_CONVERGENT_SUBSEQ) THEN
  BETA_TAC THEN ANTS_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `expectation (p:A prob_space)
     (\a:A. abs((g:real->real) ((X:num->A->real) ((r:num->num) n) a)))` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC EXPECTATION_ABS_BOUND THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `expectation (p:A prob_space) (\a:A. BB)` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC EXPECTATION_MONO THEN
     ASM_REWRITE_TAC[INTEGRABLE_CONST] THEN
     MP_TAC(ISPECL [`p:A prob_space`;
       `\a:A. (g:real->real)((X:num->A->real) ((r:num->num) n) a)`]
       INTEGRABLE_ABS) THEN
     REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[EXPECTATION_CONST] THEN
     UNDISCH_TAC `&0 < BB` THEN REAL_ARITH_TAC]];
   ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L':real`
    (X_CHOOSE_THEN `s:num->num` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `s:num->num` THEN ASM_REWRITE_TAC[] THEN
  (* Must show L' = L0, then we're done *)
  SUBGOAL_THEN `L':real = L0`
    (fun th -> SUBST1_TAC(SYM th) THEN ASM_REWRITE_TAC[]) THEN
  (* Key uniqueness argument: both L0 and L' are within eps of the same
     trig poly limit, for all eps > 0 *)
  MATCH_MP_TAC REAL_EQ_OF_ABS_LT_ALL THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  (* Choose M large enough *)
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
  (* Get trig poly approximation *)
  MP_TAC(SPECL [`g:real->real`; `BB:real`; `M:real`; `e / &6`]
    BOUNDED_CONTINUOUS_TRIG_APPROX) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH];
   ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `nn:num`
    (X_CHOOSE_THEN `aa:num->real`
      (X_CHOOSE_THEN `bb:num->real`
        (X_CHOOSE_THEN `ff:num->real` STRIP_ASSUME_TAC)))) THEN
  (* E[T(X_n)] converges to a limit determined by phi *)
  ABBREV_TAC `Tphi = sum(0..nn)
    (\k. (aa:num->real) k * (phi_re:real->real)((ff:num->real) k) +
         (bb:num->real) k * (phi_im:real->real)(ff k))` THEN
  SUBGOAL_THEN
    `((\n. expectation (p:A prob_space)
       (\x:A. sum(0..nn)
         (\k. (aa:num->real) k * cos((ff:num->real) k * (X:num->A->real) n x) +
              (bb:num->real) k * sin(ff k * X n x)))) --->
      Tphi) sequentially`
    ASSUME_TAC THENL
  [EXPAND_TAC "Tphi" THEN
   MATCH_MP_TAC GENERAL_TRIG_POLY_WEAK_CONVERGENCE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* STEP_C_BOUND gives |E[g(X_n)] - E[T(X_n)]| < e/3 for all n *)
  SUBGOAL_THEN
    `!n:num. abs(expectation (p:A prob_space)
       (\a:A. (g:real->real)((X:num->A->real) n a)) -
      expectation p
       (\a:A. sum(0..nn)
         (\k. (aa:num->real) k * cos((ff:num->real) k * X n a) +
              (bb:num->real) k * sin(ff k * X n a)))) <
      e / &3`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   SUBGOAL_THEN `!n:num. integrable (p:A prob_space)
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
   MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `e / &6 + &2 * BB * CC / M pow 2` THEN
   CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`p:A prob_space`; `X:num->A->real`; `g:real->real`;
      `\y:real. sum(0..nn)
        (\k. (aa:num->real) k * cos((ff:num->real) k * y) +
             (bb:num->real) k * sin(ff k * y))`;
      `BB:real`; `CC:real`; `e:real`; `M:real`] STEP_C_BOUND) THEN
    BETA_TAC THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[];
    MATCH_MP_TAC(REAL_ARITH `x < e / &6 ==> e / &6 + x < e / &3`) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `&2 * BB * (CC + &1) / M pow 2` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [UNDISCH_TAC `&0 < BB` THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_POW_LT] THEN
      REAL_ARITH_TAC]]];
   ALL_TAC] THEN
  (* Along r0: |L0 - Tphi| <= e/3 *)
  SUBGOAL_THEN `abs(L0 - Tphi) <= e / &3` ASSUME_TAC THENL
  [MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LE) THEN
   EXISTS_TAC `\k:num. abs(expectation (p:A prob_space)
       (\a:A. (g:real->real)((X:num->A->real) ((r0:num->num) k) a)) -
      expectation p
       (\a:A. sum(0..nn)
         (\j. (aa:num->real) j * cos((ff:num->real) j * X (r0 k) a) +
              (bb:num->real) j * sin(ff j * X (r0 k) a))))` THEN
   EXISTS_TAC `\k:num. e / &3` THEN BETA_TAC THEN
   REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_ABS THEN
    MATCH_MP_TAC REALLIM_SUB THEN CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     MP_TAC(ISPECL
       [`\n:num. expectation (p:A prob_space)
          (\x:A. sum(0..nn)
            (\j. (aa:num->real) j * cos((ff:num->real) j * (X:num->A->real) n x) +
                 (bb:num->real) j * sin(ff j * X n x)))`;
        `Tphi:real`; `r0:num->num`] REALLIM_SUBSEQUENCE) THEN
     BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    CONJ_TAC THENL
    [REWRITE_TAC[REALLIM_CONST];
     REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
     EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN
     MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]]];
   ALL_TAC] THEN
  (* Along r o s: |L' - Tphi| <= e/3 *)
  SUBGOAL_THEN `abs(L' - Tphi) <= e / &3` ASSUME_TAC THENL
  [MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LE) THEN
   EXISTS_TAC `\k:num. abs(expectation (p:A prob_space)
       (\a:A. (g:real->real)((X:num->A->real) ((r:num->num) ((s:num->num) k)) a)) -
      expectation p
       (\a:A. sum(0..nn)
         (\j. (aa:num->real) j * cos((ff:num->real) j * X (r (s k)) a) +
              (bb:num->real) j * sin(ff j * X (r (s k)) a))))` THEN
   EXISTS_TAC `\k:num. e / &3` THEN BETA_TAC THEN
   REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_ABS THEN
    MATCH_MP_TAC REALLIM_SUB THEN CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     MP_TAC(ISPECL
       [`\n:num. expectation (p:A prob_space)
          (\x:A. sum(0..nn)
            (\j. (aa:num->real) j * cos((ff:num->real) j * (X:num->A->real) n x) +
                 (bb:num->real) j * sin(ff j * X n x)))`;
        `Tphi:real`; `\k:num. (r:num->num) ((s:num->num) k)`] REALLIM_SUBSEQUENCE) THEN
     BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
     REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN
     FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN
     ASM_REWRITE_TAC[]];
    CONJ_TAC THENL
    [REWRITE_TAC[REALLIM_CONST];
     REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
     EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN
     MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]]];
   ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Bounded second moments imply tightness and Helly proper limit *)
let PROHOROV_FORWARD = prove
 (`!p:A prob_space (X:num->A->real) C.
     (!n. integrable p (X n)) /\
     (!n. integrable p (\x. X n x pow 2)) /\
     &0 < C /\
     (!n. expectation p (\x. (X n x) pow 2) <= C)
     ==> ?r H. (!m n. m < n ==> r m < r n) /\
         (!x. &0 <= H x /\ H x <= &1) /\
         (!x y. x <= y ==> H x <= H y) /\
         (!x. H real_continuous (atreal x)
              ==> ((\k. distribution_fn p (X (r k)) x) ---> H x)
                  sequentially) /\
         (!e. &0 < e ==> ?M. &0 < M /\ H(--M) < e /\ &1 - e < H M)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC TIGHT_HELLY_LIMIT_PROPER THEN
  REWRITE_TAC[tight_sequence] THEN CONJ_TAC THENL
  [(* dist_fn_seq *)
   REWRITE_TAC[dist_fn_seq] THEN BETA_TAC THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC DIST_FN_MONO THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
    ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN CONJ_TAC THENL
    [MATCH_MP_TAC DIST_FN_NONNEG THEN
     MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC DIST_FN_LE_1 THEN
     MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[]]];
   (* tightness bounds *)
   X_GEN_TAC `e:real` THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`; `C:real`]
     TIGHTNESS_FROM_SECOND_MOMENTS) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `M:real` THEN ASM_REWRITE_TAC[] THEN
   X_GEN_TAC `n:num` THEN
   MATCH_MP_TAC CDF_BOUNDS_FROM_TIGHTNESS THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ABS_GE_IN_EVENTS THEN
    MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
    REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]]]);;

(* LEVY_CONTINUITY_GENERAL:
   General Levy Continuity Theorem. Under pointwise char fn convergence
   and uniformly bounded second moments, CDFs converge at all continuity
   points to a proper CDF-like limit H.

   This generalizes LEVY_CONTINUITY_CLT which is specific to N(0,1). *)
let LEVY_CONTINUITY_GENERAL = prove
 (`!p:A prob_space (X:num->A->real) (phi_re:real->real) (phi_im:real->real).
     (!n. random_variable p (X n)) /\
     (!n. integrable p (X n)) /\
     (!n. integrable p (\x. X n x pow 2)) /\
     (?C. &0 < C /\ !n. expectation p (\x. X n x pow 2) <= C) /\
     (!t. ((\n. char_fn_re p (X n) t) ---> phi_re t) sequentially) /\
     (!t. ((\n. char_fn_im p (X n) t) ---> phi_im t) sequentially)
     ==> ?H. (!x. &0 <= H x /\ H x <= &1) /\
         (!x y. x <= y ==> H x <= H y) /\
         (!e. &0 < e ==> ?M. &0 < M /\ H(--M) < e /\ &1 - e < H M) /\
         (!x. H real_continuous atreal x
              ==> ((\n. cdf p (X n) x) ---> H x) sequentially)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `CC:real` STRIP_ASSUME_TAC) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  (* Step 1: PROHOROV_FORWARD gives Helly subsequence r0 with limit H *)
  MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`; `CC:real`]
    PROHOROV_FORWARD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:num->num`
    (X_CHOOSE_THEN `H:real->real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `H:real->real` THEN
  ASM_REWRITE_TAC[] THEN
  (* Step 2: Full-sequence convergence at continuity points *)
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  REWRITE_TAC[cdf; GSYM distribution_fn] THEN
  REWRITE_TAC[ETA_AX] THEN
  (* Use REALLIM_SUBSEQ_SAME_LIMIT with target H(x) *)
  MATCH_MP_TAC(ISPECL
    [`\n:num. distribution_fn (p:A prob_space) ((X:num->A->real) n) x`;
     `(H:real->real) x`; `&1`] REALLIM_SUBSEQ_SAME_LIMIT) THEN
  BETA_TAC THEN CONJ_TAC THENL
  [(* Boundedness: |distribution_fn p (X n) x| <= 1 *)
   GEN_TAC THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a <= &1 ==> abs a <= &1`) THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC DIST_FN_NONNEG THEN
    MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC DIST_FN_LE_1 THEN
    MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* For any subseq r, find sub-sub s with dist_fn(X_{r(s(k))}, x) -> H(x) *)
  X_GEN_TAC `r:num->num` THEN DISCH_TAC THEN
  (* BW gives sub-sub with dist_fn convergent to some l *)
  MP_TAC(ISPECL
    [`\k:num. distribution_fn (p:A prob_space) ((X:num->A->real) ((r:num->num) k)) x`;
     `&1`] BOUNDED_REAL_SEQ_HAS_CONVERGENT_SUBSEQ) THEN
  BETA_TAC THEN ANTS_TAC THENL
  [GEN_TAC THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a <= &1 ==> abs a <= &1`) THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC DIST_FN_NONNEG THEN
    MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC DIST_FN_LE_1 THEN
    MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real`
    (X_CHOOSE_THEN `s:num->num` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `s:num->num` THEN ASM_REWRITE_TAC[] THEN
  (* Step 3: Show l = H(x) via CONTINUOUS_LIMIT_SANDWICH *)
  SUBGOAL_THEN `(H:real->real) x = l:real` (fun th -> ASM_REWRITE_TAC[th]) THEN
  ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
  MATCH_MP_TAC CONTINUOUS_LIMIT_SANDWICH THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `h:real` THEN DISCH_TAC THEN
  (* Find continuity points y0 in (x-h, x) and y1 in (x, x+h) *)
  MP_TAC(ISPECL [`H:real->real`; `x - h:real`; `x:real`]
    MONOTONE_CONTINUITY_DENSE) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`H:real->real`; `x:real`; `x + h:real`]
    MONOTONE_CONTINUITY_DENSE) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:real` STRIP_ASSUME_TAC) THEN
  CONJ_TAC THENL
  [(* ---- H(x - h) <= l ---- *)
   (* H(x-h) <= H(y0) by monotonicity, then H(y0) <= l via ramp *)
   MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(H:real->real) y0` THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   (* Ramp from y0 to x *)
   ABBREV_TAC
     `g_low = \y:real. max (&0) (min (&1) (&1 - (y - y0) / (x - y0)))` THEN
   SUBGOAL_THEN `&0 < x - y0` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   (* g_low is bounded continuous, so E[g_low(X_n)] converges *)
   SUBGOAL_THEN `!y:real. abs((g_low:real->real) y) <= &1` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "g_low" THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `!y:real. (g_low:real->real) real_continuous atreal y`
     ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "g_low" THEN
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
         UNDISCH_TAC `&0 < x - y0` THEN REAL_ARITH_TAC]]]]]; ALL_TAC] THEN
   SUBGOAL_THEN `!n:num. integrable (p:A prob_space)
     (\a:A. (g_low:real->real) ((X:num->A->real) n a))` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
    EXISTS_TAC `&1` THEN CONJ_TAC THENL
    [EXPAND_TAC "g_low" THEN
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
     X_GEN_TAC `a:A` THEN DISCH_TAC THEN BETA_TAC THEN
     EXPAND_TAC "g_low" THEN REAL_ARITH_TAC]; ALL_TAC] THEN
   (* E[g_low(X_n)] converges by GENERAL_WEAK_CONVERGENCE_CONVERGENT *)
   MP_TAC(ISPECL
     [`p:A prob_space`; `X:num->A->real`;
      `phi_re:real->real`; `phi_im:real->real`;
      `g_low:real->real`; `&1`]
     GENERAL_WEAK_CONVERGENCE_CONVERGENT) THEN
   BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_01] THEN
    EXISTS_TAC `CC:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_TAC `Llow:real`) THEN
   EXISTS_TAC `Llow:real` THEN CONJ_TAC THENL
   [(* H(y0) <= Llow via Helly convergence at continuity point y0 *)
    MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LE) THEN
    EXISTS_TAC `\k:num. distribution_fn (p:A prob_space)
      ((X:num->A->real) ((r0:num->num) k)) y0` THEN
    EXISTS_TAC `\k:num. expectation (p:A prob_space)
      (\a:A. (g_low:real->real) ((X:num->A->real) ((r0:num->num) k) a))` THEN
    BETA_TAC THEN REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    CONJ_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o SPEC `y0:real` o
      check (fun th -> free_in `r0:num->num` (concl th))) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     DISCH_TAC THEN ASM_REWRITE_TAC[];
     CONJ_TAC THENL
     [MP_TAC(ISPECL
        [`\n:num. expectation (p:A prob_space)
           (\a:A. (g_low:real->real) ((X:num->A->real) n a))`;
         `Llow:real`; `r0:num->num`] REALLIM_SUBSEQUENCE) THEN
      BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[distribution_fn; GSYM cdf] THEN
      REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC CDF_LE_EXPECTATION THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
      [X_GEN_TAC `y:real` THEN DISCH_TAC THEN
       EXPAND_TAC "g_low" THEN
       SUBGOAL_THEN `&1 <= &1 - (y - y0) / (x - y0)` MP_TAC THENL
       [REWRITE_TAC[REAL_ARITH `&1 <= &1 - z <=> z <= &0`] THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
       X_GEN_TAC `y:real` THEN DISCH_TAC THEN
       EXPAND_TAC "g_low" THEN REAL_ARITH_TAC]]];
    (* Llow <= l *)
    MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LE) THEN
    EXISTS_TAC `\k:num. expectation (p:A prob_space)
      (\a:A. (g_low:real->real) ((X:num->A->real)
        ((r:num->num) ((s:num->num) k)) a))` THEN
    EXISTS_TAC `\k:num. distribution_fn (p:A prob_space)
      ((X:num->A->real) ((r:num->num) ((s:num->num) k))) x` THEN
    BETA_TAC THEN REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    CONJ_TAC THENL
    [MP_TAC(ISPECL
       [`\n:num. expectation (p:A prob_space)
          (\a:A. (g_low:real->real) ((X:num->A->real) n a))`;
        `Llow:real`; `\k:num. (r:num->num) ((s:num->num) k)`]
       REALLIM_SUBSEQUENCE) THEN
     BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
     REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN
     FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN ASM_REWRITE_TAC[];
     CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[distribution_fn; GSYM cdf] THEN
      REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC EXPECTATION_LE_CDF THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
      [X_GEN_TAC `y:real` THEN DISCH_TAC THEN
       EXPAND_TAC "g_low" THEN REAL_ARITH_TAC;
       X_GEN_TAC `y:real` THEN DISCH_TAC THEN
       EXPAND_TAC "g_low" THEN
       SUBGOAL_THEN `&1 - (y - y0) / (x - y0) <= &0` MP_TAC THENL
       [SUBGOAL_THEN `&1 <= (y - y0) / (x - y0)` MP_TAC THENL
        [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
         REAL_ARITH_TAC];
        REAL_ARITH_TAC]]]]];
   (* ---- l <= H(x + h) ---- *)
   (* l <= H(y1) via ramp, then H(y1) <= H(x+h) by monotonicity *)
   MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(H:real->real) y1` THEN
   CONJ_TAC THENL
   [ALL_TAC;
    ASM_MESON_TAC[REAL_LT_IMP_LE]] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   ABBREV_TAC
     `g_up = \y:real. max (&0) (min (&1) (&1 - (y - x) / (y1 - x)))` THEN
   SUBGOAL_THEN `&0 < y1 - x` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `!y:real. abs((g_up:real->real) y) <= &1` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "g_up" THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `!y:real. (g_up:real->real) real_continuous atreal y`
     ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "g_up" THEN
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
         UNDISCH_TAC `&0 < y1 - x` THEN REAL_ARITH_TAC]]]]]; ALL_TAC] THEN
   SUBGOAL_THEN `!n:num. integrable (p:A prob_space)
     (\a:A. (g_up:real->real) ((X:num->A->real) n a))` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
    EXISTS_TAC `&1` THEN CONJ_TAC THENL
    [EXPAND_TAC "g_up" THEN
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
     X_GEN_TAC `a:A` THEN DISCH_TAC THEN BETA_TAC THEN
     EXPAND_TAC "g_up" THEN REAL_ARITH_TAC]; ALL_TAC] THEN
   (* E[g_up(X_n)] converges *)
   MP_TAC(ISPECL
     [`p:A prob_space`; `X:num->A->real`;
      `phi_re:real->real`; `phi_im:real->real`;
      `g_up:real->real`; `&1`]
     GENERAL_WEAK_CONVERGENCE_CONVERGENT) THEN
   BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_01] THEN
    EXISTS_TAC `CC:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_TAC `Lup:real`) THEN
   (* l <= Lup *)
   EXISTS_TAC `Lup:real` THEN
   CONJ_TAC THENL
   [(* l <= Lup: along r o s *)
    MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LE) THEN
    EXISTS_TAC `\k:num. distribution_fn (p:A prob_space)
      ((X:num->A->real) ((r:num->num) ((s:num->num) k))) x` THEN
    EXISTS_TAC `\k:num. expectation (p:A prob_space)
      (\a:A. (g_up:real->real) ((X:num->A->real)
        ((r:num->num) ((s:num->num) k)) a))` THEN
    BETA_TAC THEN REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     CONJ_TAC THENL
     [MP_TAC(ISPECL
        [`\n:num. expectation (p:A prob_space)
           (\a:A. (g_up:real->real) ((X:num->A->real) n a))`;
         `Lup:real`; `\k:num. (r:num->num) ((s:num->num) k)`]
        REALLIM_SUBSEQUENCE) THEN
      BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN
      FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[distribution_fn; GSYM cdf] THEN
      REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC CDF_LE_EXPECTATION THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
      [X_GEN_TAC `y:real` THEN DISCH_TAC THEN
       EXPAND_TAC "g_up" THEN
       SUBGOAL_THEN `&1 <= &1 - (y - x) / (y1 - x)` MP_TAC THENL
       [REWRITE_TAC[REAL_ARITH `&1 <= &1 - z <=> z <= &0`] THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
       X_GEN_TAC `y:real` THEN DISCH_TAC THEN
       EXPAND_TAC "g_up" THEN REAL_ARITH_TAC]]];
    (* Lup <= H(y1): along Helly subseq r0 *)
    MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LE) THEN
    EXISTS_TAC `\k:num. expectation (p:A prob_space)
      (\a:A. (g_up:real->real) ((X:num->A->real) ((r0:num->num) k) a))` THEN
    EXISTS_TAC `\k:num. distribution_fn (p:A prob_space)
      ((X:num->A->real) ((r0:num->num) k)) y1` THEN
    BETA_TAC THEN REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    CONJ_TAC THENL
    [MP_TAC(ISPECL
       [`\n:num. expectation (p:A prob_space)
          (\a:A. (g_up:real->real) ((X:num->A->real) n a))`;
        `Lup:real`; `r0:num->num`] REALLIM_SUBSEQUENCE) THEN
     BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
     CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `y1:real` o
       check (fun th -> free_in `r0:num->num` (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[distribution_fn; GSYM cdf] THEN
      REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC EXPECTATION_LE_CDF THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
      [X_GEN_TAC `y:real` THEN DISCH_TAC THEN
       EXPAND_TAC "g_up" THEN REAL_ARITH_TAC;
       X_GEN_TAC `y:real` THEN DISCH_TAC THEN
       EXPAND_TAC "g_up" THEN
       SUBGOAL_THEN `&1 - (y - x) / (y1 - x) <= &0` MP_TAC THENL
       [SUBGOAL_THEN `&1 <= (y - x) / (y1 - x)` MP_TAC THENL
        [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
         REAL_ARITH_TAC];
        REAL_ARITH_TAC]]]]]]);;

(* LEVY_CONTINUITY_GENERAL_CID:
   Same as LEVY_CONTINUITY_GENERAL but conclusion uses
   converges_in_distribution definition. *)
let LEVY_CONTINUITY_GENERAL_CID = prove
 (`!p:A prob_space (X:num->A->real) (phi_re:real->real) (phi_im:real->real).
     (!n. random_variable p (X n)) /\
     (!n. integrable p (X n)) /\
     (!n. integrable p (\x. X n x pow 2)) /\
     (?C. &0 < C /\ !n. expectation p (\x. X n x pow 2) <= C) /\
     (!t. ((\n. char_fn_re p (X n) t) ---> phi_re t) sequentially) /\
     (!t. ((\n. char_fn_im p (X n) t) ---> phi_im t) sequentially)
     ==> ?H. (!x. &0 <= H x /\ H x <= &1) /\
         (!x y. x <= y ==> H x <= H y) /\
         (!e. &0 < e ==> ?M. &0 < M /\ H(--M) < e /\ &1 - e < H M) /\
         converges_in_distribution p X H`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`;
    `phi_re:real->real`; `phi_im:real->real`]
    LEVY_CONTINUITY_GENERAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `H:real->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `H:real->real` THEN ASM_REWRITE_TAC[converges_in_distribution]);;

(* ================================================================== *)
(* CDF RIGHT-CONTINUITY AND CHARACTERISTIC FUNCTION UNIQUENESS        *)
(* ================================================================== *)

(* CDF monotonicity (via distribution_fn) *)
let CDF_MONO = prove
 (`!p:A prob_space (X:A->real) a b.
     random_variable p X /\ a <= b
     ==> cdf p X a <= cdf p X b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cdf] THEN
  MATCH_MP_TAC PROB_MONO THEN CONJ_TAC THENL
  [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [random_variable]) THEN
   DISCH_THEN(MP_TAC o SPEC `a:real`) THEN REWRITE_TAC[];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [random_variable]) THEN
   DISCH_THEN(MP_TAC o SPEC `b:real`) THEN REWRITE_TAC[];
   REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
   GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   ASM_REAL_ARITH_TAC]);;

(* CDF right-continuity *)
let CDF_RIGHT_CONTINUOUS = prove
 (`!p:A prob_space (X:A->real) x e.
     random_variable p X /\ &0 < e
     ==> ?d. &0 < d /\ !y. x <= y /\ y < x + d
             ==> abs(cdf p X y - cdf p X x) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Establish convergence: cdf(x + 1/(n+1)) -> cdf(x) *)
  SUBGOAL_THEN
    `((\n. cdf p (X:A->real) (x + inv(&(SUC n)))) ---> cdf p X x) sequentially`
    MP_TAC THENL
  [REWRITE_TAC[cdf] THEN
   SUBGOAL_THEN
     `INTERS {{a:A | a IN prob_carrier p /\ (X:A->real) a <= x + inv(&(SUC n))} |
      n IN (:num)} = {a | a IN prob_carrier p /\ X a <= x}`
     (LABEL_TAC "intrs") THENL
   [REWRITE_TAC[INTERS_GSPEC; IN_UNIV; EXTENSION; IN_ELIM_THM] THEN
    BETA_TAC THEN X_GEN_TAC `a:A` THEN EQ_TAC THENL
    [DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN SIMP_TAC[];
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      SUBGOAL_THEN `?m. ~(m = 0) /\ &0 < inv(&m) /\ inv(&m) < (X:A->real) a - x`
        STRIP_ASSUME_TAC THENL
      [REWRITE_TAC[GSYM REAL_ARCH_INV] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN STRIP_TAC THEN
      SUBGOAL_THEN `inv(&(SUC m)) <= inv(&m)` MP_TAC THENL
      [MATCH_MP_TAC REAL_LE_INV2 THEN
       REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
       UNDISCH_TAC `~(m = 0)` THEN ARITH_TAC;
       ASM_REAL_ARITH_TAC]];
     STRIP_TAC THEN GEN_TAC THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `x:real` THEN
     ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC(REAL_ARITH `&0 < d ==> x <= x + d`) THEN
     MATCH_MP_TAC REAL_LT_INV THEN
     REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC];
    ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `\n. {a:A | a IN prob_carrier p /\ (X:A->real) a <= x + inv(&(SUC n))}`]
     PROB_CONTINUITY_FROM_ABOVE) THEN BETA_TAC THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [GEN_TAC THEN
     FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [random_variable]) THEN
     DISCH_THEN(MP_TAC o SPEC `x + inv(&(SUC n))`) THEN REWRITE_TAC[];
     GEN_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
     X_GEN_TAC `a:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `x + inv(&(SUC(SUC n)))` THEN
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LADD_IMP THEN
     MATCH_MP_TAC REAL_LE_INV2 THEN
     REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ARITH_TAC];
    USE_THEN "intrs" SUBST1_TAC THEN REWRITE_TAC[]];
   ALL_TAC] THEN
  (* Extract d from convergence *)
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` ASSUME_TAC) THEN
  EXISTS_TAC `inv(&(SUC N))` THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LT_INV THEN
   REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC;
   ALL_TAC] THEN
  X_GEN_TAC `y:real` THEN STRIP_TAC THEN
  (* cdf(x) <= cdf(y) <= cdf(x + 1/(N+1)), and |cdf(x+1/(N+1)) - cdf(x)| < e *)
  SUBGOAL_THEN `cdf p (X:A->real) x <= cdf p X y` ASSUME_TAC THENL
  [MATCH_MP_TAC CDF_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `cdf p (X:A->real) y <= cdf p X (x + inv(&(SUC N)))` ASSUME_TAC THENL
  [MATCH_MP_TAC CDF_MONO THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
  REWRITE_TAC[LE_REFL] THEN ASM_REAL_ARITH_TAC);;

(* Right-continuous monotone functions that agree on a dense set agree everywhere *)
let RIGHT_CONTINUOUS_MONOTONE_AGREE = prove
 (`!f g. (!x y:real. x <= y ==> f x <= f y) /\
         (!x y:real. x <= y ==> g x <= g y) /\
         (!x e. &0 < e ==> ?d. &0 < d /\
           !y. x <= y /\ y < x + d ==> abs(f y - f x) < e) /\
         (!x e. &0 < e ==> ?d. &0 < d /\
           !y. x <= y /\ y < x + d ==> abs(g y - g x) < e) /\
         (!a b. a < b ==> ?c. a < c /\ c < b /\ f c = g c)
         ==> !x. f x = g x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
  [(* Case f(x) > g(x): use g right-continuity + f monotonicity *)
   REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   ABBREV_TAC `eps = (f:real->real) x - g x` THEN
   SUBGOAL_THEN `&0 < eps` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `!x e. &0 < e ==> ?d. &0 < d /\
     (!y. x <= y /\ y < x + d ==> abs((g:real->real) y - g x) < e)` THEN
   DISCH_THEN(MP_TAC o SPECL [`x:real`; `eps:real`]) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
   UNDISCH_TAC `!a b. a < b ==> ?c. a < c /\ c < b /\
     (f:real->real) c = g c` THEN
   DISCH_THEN(MP_TAC o SPECL [`x:real`; `x + d:real`]) THEN
   ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `(f:real->real) x <= f c` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `abs((g:real->real) c - g x) < eps` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC;
   (* Case g(x) > f(x): use f right-continuity + g monotonicity *)
   REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   ABBREV_TAC `eps = (g:real->real) x - f x` THEN
   SUBGOAL_THEN `&0 < eps` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `!x e. &0 < e ==> ?d. &0 < d /\
     (!y. x <= y /\ y < x + d ==> abs((f:real->real) y - f x) < e)` THEN
   DISCH_THEN(MP_TAC o SPECL [`x:real`; `eps:real`]) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
   UNDISCH_TAC `!a b. a < b ==> ?c. a < c /\ c < b /\
     (f:real->real) c = g c` THEN
   DISCH_THEN(MP_TAC o SPECL [`x:real`; `x + d:real`]) THEN
   ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `(g:real->real) x <= g c` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `abs((f:real->real) c - f x) < eps` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC]);;

(* Helper: sequences that are within eps of each other for all eps > 0 are equal *)
let REAL_EQ_FROM_APPROX = prove
 (`!a b:real. (!e. &0 < e ==> abs(a - b) < e) ==> a = b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
  CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `a - b:real`) THEN
   ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
   FIRST_X_ASSUM(MP_TAC o SPEC `b - a:real`) THEN
   ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]);;

(* Characteristic function uniqueness *)
let CHAR_FN_UNIQUENESS = prove
 (`!p:A prob_space (X:A->real) (Y:A->real).
     random_variable p X /\ random_variable p Y /\
     integrable p X /\ integrable p Y /\
     integrable p (\x. X x pow 2) /\ integrable p (\x. Y x pow 2) /\
     (!t. char_fn_re p X t = char_fn_re p Y t) /\
     (!t. char_fn_im p X t = char_fn_im p Y t)
     ==> !x. cdf p X x = cdf p Y x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Define interleaving sequence Z_n = X if EVEN n, Y if ODD n *)
  ABBREV_TAC `Z = \n:num. if EVEN n then (X:A->real) else Y` THEN
  (* All Z_n are random variables *)
  SUBGOAL_THEN `!n. random_variable p ((Z:num->A->real) n)` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "Z" THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* All Z_n are integrable *)
  SUBGOAL_THEN `!n. integrable p ((Z:num->A->real) n)` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "Z" THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* All Z_n have integrable squares *)
  SUBGOAL_THEN `!n. integrable p (\x:A. (Z:num->A->real) n x pow 2)` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "Z" THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Bounded second moments *)
  SUBGOAL_THEN
    `?C. &0 < C /\ !n. expectation p (\x:A. (Z:num->A->real) n x pow 2) <= C`
    ASSUME_TAC THENL
  [EXISTS_TAC `abs(expectation p (\x:A. (X:A->real) x pow 2)) +
               abs(expectation p (\x:A. (Y:A->real) x pow 2)) + &1` THEN
   CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
   GEN_TAC THEN EXPAND_TAC "Z" THEN COND_CASES_TAC THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Char fn of Z_n converges (trivially, since all equal) *)
  SUBGOAL_THEN
    `!t. ((\n. char_fn_re p ((Z:num->A->real) n) t) --->
          char_fn_re p X t) sequentially`
    ASSUME_TAC THENL
  [GEN_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
   EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
   EXPAND_TAC "Z" THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
   ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!t. ((\n. char_fn_im p ((Z:num->A->real) n) t) --->
          char_fn_im p X t) sequentially`
    ASSUME_TAC THENL
  [GEN_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
   EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
   EXPAND_TAC "Z" THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
   ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Apply Levy continuity theorem *)
  MP_TAC(ISPECL [`p:A prob_space`; `Z:num->A->real`;
    `\t. char_fn_re p (X:A->real) t`;
    `\t. char_fn_im p (X:A->real) t`]
    LEVY_CONTINUITY_GENERAL) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `H:real->real` STRIP_ASSUME_TAC) THEN
  (* At continuity points of H: cdf(Z_n, x) -> H(x) *)
  (* Since Z_{2n} = X, cdf(X, x) = H(x) at continuity points *)
  (* Since Z_{2n+1} = Y, cdf(Y, x) = H(x) at continuity points *)
  SUBGOAL_THEN
    `!x. H real_continuous atreal x
         ==> cdf p (X:A->real) x = H x /\ cdf p Y x = H x`
    ASSUME_TAC THENL
  [X_GEN_TAC `c:real` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `c:real`) THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN DISCH_TAC THEN
   CONJ_TAC THENL
   [(* cdf(X, c) = H(c): use even subsequence Z_{2N} = X *)
    MATCH_MP_TAC REAL_EQ_FROM_APPROX THEN
    X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `eps:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` MP_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `2 * N`) THEN
    ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "Z" THEN BETA_TAC THEN REWRITE_TAC[EVEN_DOUBLE] THEN
    SIMP_TAC[];
    (* cdf(Y, c) = H(c): use odd subsequence Z_{2N+1} = Y *)
    MATCH_MP_TAC REAL_EQ_FROM_APPROX THEN
    X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `eps:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` MP_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `2 * N + 1`) THEN
    ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "Z" THEN BETA_TAC THEN
    REWRITE_TAC[EVEN_ADD; EVEN_DOUBLE; EVEN; ARITH] THEN
    SIMP_TAC[]];
   ALL_TAC] THEN
  (* CDFs agree at continuity points of H *)
  SUBGOAL_THEN
    `!x. H real_continuous atreal x
         ==> cdf p (X:A->real) x = cdf p Y x`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  (* Apply RIGHT_CONTINUOUS_MONOTONE_AGREE *)
  MATCH_MP_TAC RIGHT_CONTINUOUS_MONOTONE_AGREE THEN
  REPEAT CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC CDF_MONO THEN ASM_REWRITE_TAC[];
   REPEAT STRIP_TAC THEN MATCH_MP_TAC CDF_MONO THEN ASM_REWRITE_TAC[];
   REPEAT STRIP_TAC THEN MATCH_MP_TAC CDF_RIGHT_CONTINUOUS THEN
   ASM_REWRITE_TAC[];
   REPEAT STRIP_TAC THEN MATCH_MP_TAC CDF_RIGHT_CONTINUOUS THEN
   ASM_REWRITE_TAC[];
   (* Dense agreement via continuity points of H *)
   REPEAT STRIP_TAC THEN
   MP_TAC(SPECL [`H:real->real`; `a:real`; `b:real`]
     MONOTONE_CONTINUITY_DENSE) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ================================================================== *)
(* LEVY INVERSION FORMULA                                             *)
(* The characteristic function determines the distribution via an     *)
(* explicit integral formula: for continuity points a < b of F,       *)
(*   F(b) - F(a) = lim_{T->inf} (1/(2pi)) int_{-T}^T                *)
(*     [(sin(tb)-sin(ta))*phi_re(t) - (cos(tb)-cos(ta))*phi_im(t)]/t *)
(* ================================================================== *)

(* Trig identity: the inversion integrand simplifies via sin subtraction *)
let INVERSION_TRIG_IDENTITY = prove
 (`!t a b x:real.
    (sin(t * b) - sin(t * a)) * cos(t * x) -
    (cos(t * b) - cos(t * a)) * sin(t * x) =
    sin(t * (b - x)) - sin(t * (a - x))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB] THEN
  REWRITE_TAC[SIN_SUB] THEN REAL_ARITH_TAC);;

(* Kernel boundedness: |(sin(t(b-x)) - sin(t(a-x))) / t| <= |b - a| *)
let INVERSION_KERNEL_BOUNDED = prove
 (`!t a b x:real. abs((sin(t * (b - x)) - sin(t * (a - x))) * inv t)
                  <= abs(b - a)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `t = &0` THENL
  [ASM_REWRITE_TAC[REAL_MUL_LZERO; SIN_0; REAL_SUB_REFL; REAL_MUL_LZERO;
                    REAL_ABS_NUM] THEN
   REWRITE_TAC[REAL_ABS_POS];
   ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(t * (b - x) - t * (a - x)) * inv(abs t)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [REWRITE_TAC[SIN_LIPSCHITZ];
    MATCH_MP_TAC REAL_LE_INV THEN REWRITE_TAC[REAL_ABS_POS]];
   ALL_TAC] THEN
  SUBGOAL_THEN `abs(t * (b - x) - t * (a - x)) = abs t * abs(b - a:real)`
    SUBST1_TAC THENL
  [REWRITE_TAC[GSYM REAL_ABS_MUL] THEN AP_TERM_TAC THEN CONV_TAC REAL_RING;
   ALL_TAC] THEN
  SUBGOAL_THEN `(abs t * abs(b - a)) * inv(abs t) =
                abs(b - a:real) * (abs t * inv(abs t))` SUBST1_TAC THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs t * inv(abs t) = &1` SUBST1_TAC THENL
  [MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REWRITE_TAC[REAL_ABS_ZERO];
   REWRITE_TAC[REAL_MUL_RID; REAL_LE_REFL]]);;

(* Integrability of sin(c*t)/t on [0,M] for c > 0 *)
let SINC_SCALED_INTEGRABLE = prove
 (`!c M. &0 < c /\ &0 <= M ==>
   (\t. sin(c * t) * inv t) real_integrable_on real_interval[&0,M]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\t:real. abs c` THEN REPEAT CONJ_TAC THENL
  [(* Measurability: sin(c*t)*inv(t) measurable on [0,M] *)
   MATCH_MP_TAC REAL_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
   EXISTS_TAC `(:real)` THEN
   REWRITE_TAC[SUBSET_UNIV; REAL_LEBESGUE_MEASURABLE_INTERVAL] THEN
   MATCH_MP_TAC REAL_MEASURABLE_ON_MUL THEN CONJ_TAC THENL
   [(* sin(c*t) measurable on (:real) *)
    SUBGOAL_THEN `(\t. sin(c * t)) = sin o (\t:real. c * t)` SUBST1_TAC THENL
    [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_MEASURABLE_ON_COMPOSE_CONTINUOUS THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_SIN] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET THEN
    REWRITE_TAC[REAL_CLOSED_UNIV] THEN
    SIMP_TAC[REAL_CONTINUOUS_ON_LMUL; REAL_CONTINUOUS_ON_ID];
    (* inv(t) measurable on (:real) *)
    SUBGOAL_THEN `inv:real->real = (\x. inv x)` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_MEASURABLE_ON_INV THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET THEN
     REWRITE_TAC[REAL_CLOSED_UNIV; REAL_CONTINUOUS_ON_ID];
     REWRITE_TAC[SET_RULE `{x | x = &0} = {&0}`; REAL_NEGLIGIBLE_SING]]];
   (* Bounding function integrable *)
   REWRITE_TAC[REAL_INTEGRABLE_CONST];
   (* Bound: |sin(c*t)*inv(t)| <= |c| *)
   X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
   STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
   ASM_CASES_TAC `t = &0` THENL
   [ASM_REWRITE_TAC[REAL_INV_0; REAL_ABS_NUM; REAL_MUL_RZERO; REAL_ABS_POS];
    ALL_TAC] THEN
   SUBGOAL_THEN `abs(sin(c * t)) <= abs(c * t)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`c * t:real`; `&0`] SIN_LIPSCHITZ) THEN
    REWRITE_TAC[SIN_0; REAL_SUB_RZERO];
    ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(c * t) * abs(inv t)` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV; GSYM REAL_MUL_ASSOC] THEN
    SUBGOAL_THEN `abs t * inv(abs t) = &1` SUBST1_TAC THENL
    [MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REWRITE_TAC[REAL_ABS_ZERO];
     REWRITE_TAC[REAL_MUL_RID; REAL_LE_REFL]]]]);;

(* Scaled Dirichlet integral: int_0^T sin(c*t)/t dt -> pi/2 for c > 0 *)
let DIRICHLET_INTEGRAL_SCALED = prove
 (`!c. &0 < c ==>
   ((\T. real_integral (real_interval[&0,T]) (\t. sin(c * t) * inv t))
    ---> pi / &2) at_posinfinity`,
  X_GEN_TAC `c:real` THEN DISCH_TAC THEN
  REWRITE_TAC[REALLIM_AT_POSINFINITY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(REWRITE_RULE[REALLIM_AT_POSINFINITY] DIRICHLET_INTEGRAL) THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` (ASSUME_TAC o REWRITE_RULE[])) THEN
  EXISTS_TAC `(abs B + &1) * inv c` THEN
  X_GEN_TAC `M:real` THEN REWRITE_TAC[real_ge] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < M` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(abs B + &1) * inv c` THEN
   ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN
   CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_INV THEN
   ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c * M` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Key: int_0^T sin(ct)/t dt = int_0^{cT} sin(u)/u du by substitution *)
  SUBGOAL_THEN
    `real_integral (real_interval[&0,M]) (\t. sin(c * t) * inv t) =
     real_integral (real_interval[&0,c * M]) (\t. sin t * inv t)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
   MP_TAC(ISPECL [`\t:real. sin t * inv t`;
                   `\t:real. c * t`;
                   `\(t:real). c:real`;
                   `&0:real`; `M:real`;
                   `&0:real`; `c * M:real`;
                   `{&0:real}`]
     HAS_REAL_INTEGRAL_SUBSTITUTION_STRONG) THEN
   REWRITE_TAC[COUNTABLE_SING] THEN
   ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
    [MP_TAC(SPECL [`&1`; `c * M:real`] SINC_SCALED_INTEGRABLE) THEN
     REWRITE_TAC[REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
     ASM_REAL_ARITH_TAC;
     SIMP_TAC[REAL_CONTINUOUS_ON_LMUL; REAL_CONTINUOUS_ON_ID];
     REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
     X_GEN_TAC `y:real` THEN STRIP_TAC THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
     X_GEN_TAC `x:real` THEN
     REWRITE_TAC[IN_DIFF; IN_REAL_INTERVAL; IN_SING] THEN
     STRIP_TAC THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_WITHIN THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_ID];
      MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN
      REWRITE_TAC[REAL_CONTINUOUS_WITHIN_SIN] THEN
      SUBGOAL_THEN `inv:real->real = (\x:real. inv x)` SUBST1_TAC THENL
      [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_INV THEN
      REWRITE_TAC[REAL_CONTINUOUS_WITHIN_ID; NETLIMIT_WITHINREAL] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
     ASM_REAL_ARITH_TAC;
     ASM_REAL_ARITH_TAC;
     REWRITE_TAC[REAL_MUL_RZERO] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
   SIMP_TAC[REAL_MUL_RZERO] THEN
   DISCH_TAC THEN
   MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
   EXISTS_TAC `\x:real. sin(c * x) * inv(c * x) * c` THEN
   CONJ_TAC THENL
   [X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    STRIP_TAC THEN ASM_CASES_TAC `x = &0` THENL
    [ASM_REWRITE_TAC[REAL_MUL_RZERO; SIN_0; REAL_MUL_LZERO];
     ALL_TAC] THEN
    MATCH_MP_TAC(REAL_FIELD
      `~(c = &0) /\ ~(x = &0) ==>
       sin(c * x) * inv(c * x) * c = sin(c * x) * inv x`) THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_MUL_ASSOC] THEN FIRST_X_ASSUM ACCEPT_TAC];
   ALL_TAC] THEN
  (* Apply DIRICHLET_INTEGRAL bound: c*M >= B *)
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[real_ge] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs B + &1` THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `c * ((abs B + &1) * inv c)` THEN
  CONJ_TAC THENL
  [SUBGOAL_THEN `c * ((abs B + &1) * inv c) = abs B + &1` SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_FIELD `~(c = &0) ==> c * ((abs B + &1) * inv c) = abs B + &1`) THEN
    ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC];
   MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]);;

(* Scaled Dirichlet integral for negative c *)
let DIRICHLET_INTEGRAL_SCALED_NEG = prove
 (`!c. c < &0 ==>
   ((\T. real_integral (real_interval[&0,T]) (\t. sin(c * t) * inv t))
    ---> --(pi / &2)) at_posinfinity`,
  X_GEN_TAC `c:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < --c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `--c:real` DIRICHLET_INTEGRAL_SCALED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* Show sin(c*t)/t = --(sin(--c*t)/t) pointwise, hence integrals related *)
  SUBGOAL_THEN
    `!M:real. real_integral (real_interval[&0,M]) (\t. sin(c * t) * inv t) =
              --(real_integral (real_interval[&0,M]) (\t. sin(--c * t) * inv t))`
    (fun th -> REWRITE_TAC[th]) THENL
  [X_GEN_TAC `M:real` THEN
   SUBGOAL_THEN
     `real_integral (real_interval[&0,M]) (\t. sin(c * t) * inv t) =
      real_integral (real_interval[&0,M]) (\t. --(sin(--c * t) * inv t))`
     SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN
    X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    STRIP_TAC THEN REWRITE_TAC[REAL_MUL_LNEG; SIN_NEG; REAL_NEG_NEG];
    MATCH_MP_TAC REAL_INTEGRAL_NEG THEN
    ASM_CASES_TAC `&0 <= M:real` THENL
    [MATCH_MP_TAC SINC_SCALED_INTEGRABLE THEN ASM_REAL_ARITH_TAC;
     SUBGOAL_THEN `real_interval[&0,M:real] = {}` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_INTERVAL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_INTEGRABLE_ON_EMPTY]]]];
   MATCH_MP_TAC REALLIM_NEG THEN ASM_REWRITE_TAC[]]);;

(* Uniform bound on scaled sinc integral *)
let SINC_INTEGRAL_UNIFORM_BOUND = prove
 (`!c TT. &0 < c /\ &0 < TT ==>
   abs(real_integral (real_interval[&0,TT]) (\t. sin(c * t) * inv t)) <=
   pi / &2 + &4`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `real_integral (real_interval[&0,TT]) (\t. sin(c * t) * inv t) =
     real_integral (real_interval[&0,c * TT]) (\t. sin t * inv t)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
   MP_TAC(ISPECL [`\t:real. sin t * inv t`;
                   `\t:real. c * t`;
                   `\(t:real). c:real`;
                   `&0:real`; `TT:real`;
                   `&0:real`; `c * TT:real`;
                   `{&0:real}`]
     HAS_REAL_INTEGRAL_SUBSTITUTION_STRONG) THEN
   REWRITE_TAC[COUNTABLE_SING] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
    [MP_TAC(SPECL [`&1`; `c * TT:real`] SINC_SCALED_INTEGRABLE) THEN
     REWRITE_TAC[REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
     CONJ_TAC THENL [REAL_ARITH_TAC;
     MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 <= x`) THEN
     MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
     SIMP_TAC[REAL_CONTINUOUS_ON_LMUL; REAL_CONTINUOUS_ON_ID];
     REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
     X_GEN_TAC `y:real` THEN STRIP_TAC THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
     X_GEN_TAC `x:real` THEN
     REWRITE_TAC[IN_DIFF; IN_REAL_INTERVAL; IN_SING] THEN
     STRIP_TAC THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_WITHIN THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_ID];
      MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN
      REWRITE_TAC[REAL_CONTINUOUS_WITHIN_SIN] THEN
      SUBGOAL_THEN `inv:real->real = (\x:real. inv x)` SUBST1_TAC THENL
      [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_INV THEN
      REWRITE_TAC[REAL_CONTINUOUS_WITHIN_ID; NETLIMIT_WITHINREAL] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
     ASM_REAL_ARITH_TAC;
     MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 <= x`) THEN
     MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[REAL_MUL_RZERO] THEN
     MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 <= x`) THEN
     MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   SIMP_TAC[REAL_MUL_RZERO] THEN
   DISCH_TAC THEN
   MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
   EXISTS_TAC `\x:real. sin(c * x) * inv(c * x) * c` THEN
   CONJ_TAC THENL
   [X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    STRIP_TAC THEN ASM_CASES_TAC `x = &0` THENL
    [ASM_REWRITE_TAC[REAL_MUL_RZERO; SIN_0; REAL_MUL_LZERO];
     ALL_TAC] THEN
    MATCH_MP_TAC(REAL_FIELD
      `~(c = &0) /\ ~(x = &0) ==>
       sin(c * x) * inv(c * x) * c = sin(c * x) * inv x`) THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_MUL_ASSOC] THEN FIRST_X_ASSUM ACCEPT_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c * TT` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `&1 <= c * TT` THENL
  [MP_TAC(SPEC `c * TT:real` SINC_INTEGRAL_BOUND) THEN ASM_REWRITE_TAC[] THEN
   DISCH_TAC THEN
   SUBGOAL_THEN `&4 * inv(c * TT) <= &4` ASSUME_TAC THENL
   [SUBGOAL_THEN `inv(c * TT) <= &1` MP_TAC THENL
    [SUBGOAL_THEN `inv(c * TT) <= inv(&1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_INV_1]];
     REAL_ARITH_TAC];
    ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `abs(real_integral (real_interval [&0,c * TT])
     (\t. sin t * inv t) - pi / &2) + abs(pi / &2)` THEN
   CONJ_TAC THENL
   [REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 + abs(pi / &2)` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
     MP_TAC PI_POS THEN REAL_ARITH_TAC]];
   MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c * TT:real` THEN CONJ_TAC THENL
   [ALL_TAC; MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `real_integral (real_interval[&0, c * TT]) (\t:real. &1)` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_ABS_BOUND_INTEGRAL THEN REPEAT CONJ_TAC THENL
    [MP_TAC(SPECL [`&1`; `c * TT:real`] SINC_SCALED_INTEGRABLE) THEN
     REWRITE_TAC[REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
     ASM_REAL_ARITH_TAC;
     REWRITE_TAC[REAL_INTEGRABLE_CONST];
     X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
     BETA_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
     ASM_CASES_TAC `t = &0` THENL
     [ASM_REWRITE_TAC[REAL_INV_0; REAL_ABS_NUM; REAL_MUL_RZERO; REAL_POS];
      ALL_TAC] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs t * abs(inv t)` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      MP_TAC(SPECL [`t:real`; `&0`] SIN_LIPSCHITZ) THEN
      REWRITE_TAC[SIN_0; REAL_SUB_RZERO] THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ABS_INV; GSYM REAL_ABS_MUL] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_ABS_NUM; REAL_LE_REFL]]];
    SUBGOAL_THEN `real_integral (real_interval[&0, c * TT]) (\t:real. &1) =
      &1 * (c * TT - &0)` SUBST1_TAC THENL
    [MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
     MATCH_MP_TAC HAS_REAL_INTEGRAL_CONST THEN ASM_REAL_ARITH_TAC;
     REAL_ARITH_TAC]]]);;

(* Inversion kernel bounded by |b - a| (conditional version) *)
let INVERSION_KERNEL_BOUNDED_NZ = prove
 (`!a b x t. ~(t = &0) ==>
   abs((sin(t * (b - x)) - sin(t * (a - x))) * inv t) <= abs(b - a)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV] THEN
  SUBGOAL_THEN `abs(sin(t * (b - x)) - sin(t * (a - x))) <= abs(t) * abs(b - a)`
    ASSUME_TAC THENL
  [MP_TAC(SPECL [`t * (b - x):real`; `t * (a - x):real`] SIN_LIPSCHITZ) THEN
   REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL;
               REAL_ARITH `(b - x) - (a - x) = b - a:real`];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 < abs t` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[GSYM REAL_ABS_NZ]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(abs t * abs(b - a)) * inv(abs t)` THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_RMUL THEN
   ASM_REWRITE_TAC[REAL_LE_INV_EQ; REAL_ABS_POS];
   SUBGOAL_THEN `(abs t * abs(b - a)) * inv(abs t) = abs(b - a)`
     SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_FIELD
     `~(t = &0) ==> (abs t * abs(b - a)) * inv(abs t) = abs(b - a)`) THEN
    ASM_REWRITE_TAC[REAL_ABS_ZERO];
    REAL_ARITH_TAC]]);;

(* Integrability of sin(c*t)/t for c < 0 *)
let SINC_SCALED_NEG_INTEGRABLE = prove
 (`!c M. c < &0 /\ &0 <= M ==>
   (\t. sin(c * t) * inv t) real_integrable_on real_interval[&0,M]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `(\t. sin(c * t) * inv t) = (\t:real. --(sin((--c) * t) * inv t))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `t:real` THEN
   SUBGOAL_THEN `sin(c * t):real = sin(--((--c) * t))` SUBST1_TAC THENL
   [AP_TERM_TAC THEN REAL_ARITH_TAC;
    REWRITE_TAC[SIN_NEG] THEN REAL_ARITH_TAC];
   MATCH_MP_TAC REAL_INTEGRABLE_NEG THEN
   MATCH_MP_TAC SINC_SCALED_INTEGRABLE THEN ASM_REAL_ARITH_TAC]);;

(* Integrability of sin(c*t)/t for nonzero c *)
let SINC_SCALED_INTEGRABLE_NZ = prove
 (`!c M. ~(c = &0) /\ &0 <= M ==>
   (\t. sin(c * t) * inv t) real_integrable_on real_interval[&0,M]`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `&0 < c` THENL
  [MATCH_MP_TAC SINC_SCALED_INTEGRABLE THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC SINC_SCALED_NEG_INTEGRABLE THEN ASM_REAL_ARITH_TAC]);;

(* Inversion kernel converges to 1 inside (a,b) *)
let INVERSION_KERNEL_CONVERGES_INSIDE = prove
 (`!a b v. a < v /\ v < b ==>
  ((\TT. inv(pi) * real_integral (real_interval[&0,TT])
    (\t. (sin(t * (b - v)) - sin(t * (a - v))) * inv t))
   ---> &1) at_posinfinity`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b - v /\ ~(b - v = &0)` STRIP_ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a - v < &0 /\ ~(a - v = &0)` STRIP_ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(pi = &0)` ASSUME_TAC THENL
  [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV)
    [MATCH_MP (REAL_FIELD
      `~(pi = &0) ==> &1 = inv(pi) * (pi / &2 - --(pi / &2))`)
      (ASSUME `~(pi = &0)`)] THEN
  MATCH_MP_TAC REALLIM_LMUL THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\TT. real_integral (real_interval[&0,TT])
    (\t. sin((b - v) * t) * inv t) -
    real_integral (real_interval[&0,TT])
    (\t. sin((a - v) * t) * inv t)` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[EVENTUALLY_AT_POSINFINITY] THEN
   EXISTS_TAC `&1` THEN X_GEN_TAC `TT:real` THEN
   REWRITE_TAC[real_ge] THEN DISCH_TAC THEN BETA_TAC THEN
   SUBGOAL_THEN `&0 < TT` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   CONV_TAC SYM_CONV THEN
   SUBGOAL_THEN
     `(\t. (sin(t * (b - v)) - sin(t * (a - v))) * inv t) =
      (\t:real. sin((b - v) * t) * inv t - sin((a - v) * t) * inv t)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; REAL_SUB_RDISTRIB] THEN GEN_TAC THEN
    BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_INTEGRAL_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC SINC_SCALED_INTEGRABLE_NZ THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < TT ==> &0 <= TT`]];
   MATCH_MP_TAC REALLIM_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC(SPEC `b - v:real` DIRICHLET_INTEGRAL_SCALED) THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(SPEC `a - v:real` DIRICHLET_INTEGRAL_SCALED_NEG) THEN
    ASM_REAL_ARITH_TAC]]);;

(* Inversion kernel converges to 0 outside [a,b] *)
let INVERSION_KERNEL_CONVERGES_OUTSIDE = prove
 (`!a b v. a < b /\ (v < a \/ b < v) ==>
  ((\TT. inv(pi) * real_integral (real_interval[&0,TT])
    (\t. (sin(t * (b - v)) - sin(t * (a - v))) * inv t))
   ---> &0) at_posinfinity`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~(b - v = &0) /\ ~(a - v = &0)` STRIP_ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_NULL_LMUL THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\TT. real_integral (real_interval[&0,TT])
    (\t. sin((b - v) * t) * inv t) -
    real_integral (real_interval[&0,TT])
    (\t. sin((a - v) * t) * inv t)` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[EVENTUALLY_AT_POSINFINITY] THEN
   EXISTS_TAC `&1` THEN X_GEN_TAC `TT:real` THEN
   REWRITE_TAC[real_ge] THEN DISCH_TAC THEN BETA_TAC THEN
   SUBGOAL_THEN `&0 < TT` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   CONV_TAC SYM_CONV THEN
   SUBGOAL_THEN
     `(\t. (sin(t * (b - v)) - sin(t * (a - v))) * inv t) =
      (\t:real. sin((b - v) * t) * inv t - sin((a - v) * t) * inv t)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; REAL_SUB_RDISTRIB] THEN GEN_TAC THEN
    BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_INTEGRAL_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC SINC_SCALED_INTEGRABLE_NZ THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < TT ==> &0 <= TT`]];
   FIRST_X_ASSUM DISJ_CASES_TAC THENL
   [GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV)
     [REAL_ARITH `&0 = pi / &2 - pi / &2`] THEN
    MATCH_MP_TAC REALLIM_SUB THEN CONJ_TAC THENL
    [MATCH_MP_TAC(SPEC `b - v:real` DIRICHLET_INTEGRAL_SCALED) THEN
     ASM_REAL_ARITH_TAC;
     MATCH_MP_TAC(SPEC `a - v:real` DIRICHLET_INTEGRAL_SCALED) THEN
     ASM_REAL_ARITH_TAC];
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV)
     [REAL_ARITH `&0 = --(pi / &2) - --(pi / &2)`] THEN
    MATCH_MP_TAC REALLIM_SUB THEN CONJ_TAC THENL
    [MATCH_MP_TAC(SPEC `b - v:real` DIRICHLET_INTEGRAL_SCALED_NEG) THEN
     ASM_REAL_ARITH_TAC;
     MATCH_MP_TAC(SPEC `a - v:real` DIRICHLET_INTEGRAL_SCALED_NEG) THEN
     ASM_REAL_ARITH_TAC]]]);;

(* ================================================================== *)
(* LEVY INVERSION FORMULA: Phase 4-5                                  *)
(* ================================================================== *)

(* Extend SINC_INTEGRAL_UNIFORM_BOUND to all real c (not just c > 0) *)
let SINC_INTEGRAL_BOUND_ALL = prove
 (`!c TT. &0 < TT ==>
   abs(real_integral (real_interval[&0,TT]) (\t. sin(c * t) * inv t)) <=
   pi / &2 + &4`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&0 < c` THENL
  [ASM_SIMP_TAC[SINC_INTEGRAL_UNIFORM_BOUND]; ALL_TAC] THEN
  ASM_CASES_TAC `c = &0` THENL
  [ASM_REWRITE_TAC[REAL_MUL_LZERO; SIN_0; REAL_MUL_LZERO;
    REAL_INTEGRAL_0; REAL_ABS_NUM] THEN
   MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < --c` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(\t. sin(c * t) * inv t) = (\t:real. --(sin(--c * t) * inv t))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `t:real` THEN
   SUBGOAL_THEN `c * t:real = --(--c * t)` (fun th -> REWRITE_TAC[th]) THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[SIN_NEG] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(\t:real. sin(--c * t) * inv t) real_integrable_on
    real_interval[&0,TT]` ASSUME_TAC THENL
  [MATCH_MP_TAC SINC_SCALED_INTEGRABLE_NZ THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_NEG; REAL_ABS_NEG] THEN
  ASM_SIMP_TAC[SINC_INTEGRAL_UNIFORM_BOUND]);;

(* Uniform bound on the inversion kernel g_T(v) *)
let INVERSION_KERNEL_UNIFORM_BOUND = prove
 (`!a b TT v. &0 < TT ==>
   abs(inv(pi) * real_integral (real_interval[&0,TT])
     (\t. (sin(t * (b - v)) - sin(t * (a - v))) * inv t)) <=
   &1 + &8 * inv(pi)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV] THEN
  SUBGOAL_THEN `abs pi = pi` SUBST1_TAC THENL
  [REWRITE_TAC[REAL_ABS_REFL] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(pi) * (pi / &2 + &4 + (pi / &2 + &4))` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN
     `(\t. (sin(t * (b - v)) - sin(t * (a - v))) * inv t) =
      (\t:real. sin((b-v) * t) * inv t - sin((a-v) * t) * inv t)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    SUBGOAL_THEN `x * (b - v:real) = (b - v) * x`
      (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `x * (a - v:real) = (a - v) * x`
      (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `(\t:real. sin((b-v) * t) * inv t) real_integrable_on
       real_interval[&0,TT] /\
      (\t:real. sin((a-v) * t) * inv t) real_integrable_on
       real_interval[&0,TT]` ASSUME_TAC THENL
   [CONJ_TAC THENL
    [ASM_CASES_TAC `b - v = &0` THENL
     [ASM_REWRITE_TAC[REAL_MUL_LZERO; SIN_0; REAL_MUL_LZERO;
       REAL_INTEGRABLE_0];
      MATCH_MP_TAC SINC_SCALED_INTEGRABLE_NZ THEN ASM_REAL_ARITH_TAC];
     ASM_CASES_TAC `a - v = &0` THENL
     [ASM_REWRITE_TAC[REAL_MUL_LZERO; SIN_0; REAL_MUL_LZERO;
       REAL_INTEGRABLE_0];
      MATCH_MP_TAC SINC_SCALED_INTEGRABLE_NZ THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `real_integral (real_interval[&0,TT])
       (\t. sin((b-v) * t) * inv t - sin((a-v) * t) * inv t) =
      real_integral (real_interval[&0,TT]) (\t. sin((b-v) * t) * inv t) -
      real_integral (real_interval[&0,TT]) (\t. sin((a-v) * t) * inv t)`
     SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `(pi / &2 + &4) + (pi / &2 + &4)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(real_integral (real_interval[&0,TT])
      (\t. sin((b-v) * t) * inv t)) +
      abs(real_integral (real_interval[&0,TT])
      (\t. sin((a-v) * t) * inv t))` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
    MATCH_MP_TAC SINC_INTEGRAL_BOUND_ALL THEN ASM_REWRITE_TAC[];
    REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `inv(pi) * (pi / &2 + &4 + (pi / &2 + &4)) =
    inv(pi) * (pi + &8)` SUBST1_TAC THENL
  [AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_MUL_ASSOC] THEN
  SUBGOAL_THEN `inv pi * pi = &1` SUBST1_TAC THENL
  [MATCH_MP_TAC REAL_MUL_LINV THEN
   MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* Integral of an even function over [-T,T] equals twice the integral over [0,T] *)
let REAL_INTEGRAL_EVEN_SYMMETRIC = prove
 (`!f TT. &0 <= TT /\
    (!t. f(--t) = f t) /\
    f real_integrable_on real_interval[--TT, TT]
    ==> real_integral (real_interval[--TT, TT]) f =
        &2 * real_integral (real_interval[&0, TT]) f`,
  REPEAT STRIP_TAC THEN
  (* Split integral [-T,T] into [-T,0] + [0,T] *)
  SUBGOAL_THEN
    `real_integral (real_interval[--TT, TT]) (f:real->real) =
     real_integral (real_interval[--TT, &0]) f +
     real_integral (real_interval[&0, TT]) f`
    SUBST1_TAC THENL
  [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INTEGRAL_COMBINE THEN
   ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* Show integral [-T,0] f = integral [0,T] f using reflection *)
  SUBGOAL_THEN
    `real_integral (real_interval[--TT, &0]) (f:real->real) =
     real_integral (real_interval[&0, TT]) f`
    SUBST1_TAC THENL
  [(* Rewrite f to (\x. f(-x)) using evenness *)
   SUBGOAL_THEN
     `real_integral (real_interval[--TT, &0]) (f:real->real) =
      real_integral (real_interval[--TT, &0]) (\x. f(--x))`
     SUBST1_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   (* Apply reflection: int[--T, --0] (\x. f(-x)) = int[0, T] f *)
   MP_TAC(ISPECL [`f:real->real`; `&0`; `TT:real`] REAL_INTEGRAL_REFLECT) THEN
   REWRITE_TAC[REAL_NEG_0] THEN MESON_TAC[];
   (* x + x = 2*x *)
   REAL_ARITH_TAC]);;

(* The inversion integrand sin(t(b-x))*inv(t) is even in t *)
let INVERSION_SINC_EVEN = prove
 (`!a b x t. (sin(--t * (b - x)) - sin(--t * (a - x))) * inv(--t) =
             (sin(t * (b - x)) - sin(t * (a - x))) * inv t`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `--t * (b - x) = --(t * (b - x:real))` SUBST1_TAC THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--t * (a - x) = --(t * (a - x:real))` SUBST1_TAC THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SIN_NEG; REAL_INV_NEG] THEN REAL_ARITH_TAC);;

(* Sequential extraction from at_posinfinity: if f -> l at posinfinity
   and s is a sequence with s(n) >= n, then f(s(n)) -> l sequentially *)
let REALLIM_AT_POSINFINITY_IMP_SEQUENTIALLY = prove
 (`!f l (s:num->real). (f ---> l) at_posinfinity /\ (!n. s n >= &n)
    ==> ((\n. f(s n)) ---> l) sequentially`,
  REWRITE_TAC[REALLIM_AT_POSINFINITY; REALLIM_SEQUENTIALLY; real_ge] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` ASSUME_TAC) THEN
  MP_TAC(SPEC `B:real` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` ASSUME_TAC) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&n:real` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N:real` THEN
   ASM_REWRITE_TAC[REAL_OF_NUM_LE];
   ASM_REWRITE_TAC[]]);;

(* Converse: if every divergent subsequence converges to l,
   then the at_posinfinity limit is l. Proof by contradiction. *)
let REALLIM_AT_POSINFINITY_FROM_SUBSEQUENCES = prove
 (`!f l. (!s:num->real. (!n. s n >= &n)
          ==> ((\n. f(s n)) ---> l) sequentially)
    ==> (f ---> l) at_posinfinity`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[REALLIM_AT_POSINFINITY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  (* By contradiction: assume forall B, exists T >= B with |f(T)-l| >= e *)
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM; NOT_FORALL_THM;
    NOT_IMP; REAL_NOT_LT]) THEN
  REWRITE_TAC[real_ge] THEN
  (* Construct bad sequence via Skolem *)
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `&n:real`) THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `s:num->real`) THEN
  (* Apply hypothesis to get f(s n) -> l sequentially *)
  FIRST_X_ASSUM(MP_TAC o SPEC `s:num->real`) THEN
  ANTS_TAC THENL
  [GEN_TAC THEN REWRITE_TAC[real_ge] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN MESON_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` MP_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `N:num`) THEN REWRITE_TAC[LE_REFL] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN REAL_ARITH_TAC);;

(* Inversion kernel at boundary v=a: converges to 1/2 *)
let INVERSION_KERNEL_CONVERGES_AT_A = prove
 (`!a b. a < b ==>
  ((\TT. inv(pi) * real_integral (real_interval[&0,TT])
    (\t. (sin(t * (b - a)) - sin(t * (a - a))) * inv t))
   ---> inv(&2)) at_posinfinity`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a - a = &0` SUBST1_TAC THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RZERO; SIN_0; REAL_SUB_RZERO] THEN
  SUBGOAL_THEN `&0 < b - a` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(pi = &0)` ASSUME_TAC THENL
  [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV)
    [MATCH_MP (REAL_FIELD `~(pi = &0) ==> inv(&2) = inv(pi) * (pi / &2)`)
      (ASSUME `~(pi = &0)`)] THEN
  MATCH_MP_TAC REALLIM_LMUL THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\TT. real_integral (real_interval[&0,TT])
    (\t. sin((b - a) * t) * inv t)` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[EVENTUALLY_AT_POSINFINITY] THEN
   EXISTS_TAC `&1` THEN X_GEN_TAC `TT:real` THEN
   REWRITE_TAC[real_ge] THEN DISCH_TAC THEN BETA_TAC THEN
   AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
   MATCH_MP_TAC(SPEC `b - a:real` DIRICHLET_INTEGRAL_SCALED) THEN
   ASM_REAL_ARITH_TAC]);;

(* Inversion kernel at boundary v=b: converges to 1/2 *)
let INVERSION_KERNEL_CONVERGES_AT_B = prove
 (`!a b. a < b ==>
  ((\TT. inv(pi) * real_integral (real_interval[&0,TT])
    (\t. (sin(t * (b - b)) - sin(t * (a - b))) * inv t))
   ---> inv(&2)) at_posinfinity`,
  REPEAT STRIP_TAC THEN
  (* Reduce to AT_A case: both integrands equal sin(t*(b-a))*inv(t) *)
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\TT. inv(pi) * real_integral (real_interval[&0,TT])
    (\t. (sin(t * (b - a)) - sin(t * (a - a))) * inv t)` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[EVENTUALLY_AT_POSINFINITY] THEN
   EXISTS_TAC `&1` THEN X_GEN_TAC `TT:real` THEN
   REWRITE_TAC[real_ge] THEN DISCH_TAC THEN BETA_TAC THEN
   AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
   X_GEN_TAC `t:real` THEN
   SUBGOAL_THEN `t * (b - b:real) = &0` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `t * (a - a:real) = &0` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `t * (a - b:real) = --(t * (b - a))` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[SIN_0; SIN_NEG] THEN REAL_ARITH_TAC;
   MATCH_MP_TAC INVERSION_KERNEL_CONVERGES_AT_A THEN ASM_REWRITE_TAC[]]);;

(* CDF continuity at a point implies zero probability mass there.
   If distribution_fn p X is continuous at a, then P(X = a) = 0.
   Proof: {X = a} = INTERS_n {a - 1/(n+1) < X <= a} (decreasing events),
   P of each = F(a) - F(a - 1/(n+1)) -> 0 by continuity, so P(X=a) = 0. *)
let DISTRIBUTION_FN_CONTINUOUS_PROB_ZERO = prove
 (`!p:A prob_space X a.
    random_variable p X /\
    (distribution_fn p X) real_continuous (atreal a)
    ==> prob p {x | x IN prob_carrier p /\ X x = a} = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ X x = a} =
     {x | x IN prob_carrier p /\ X x <= a} DIFF
     {x | x IN prob_carrier p /\ X x < a}` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN
   GEN_TAC THEN ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ X x < a} SUBSET
     {x | x IN prob_carrier p /\ X x <= a}` ASSUME_TAC THENL
  [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ X x < a} IN prob_events p`
    ASSUME_TAC THENL
  [MATCH_MP_TAC RV_PREIMAGE_LT THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ X x <= a} IN prob_events p`
    ASSUME_TAC THENL
  [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [random_variable]) THEN
   DISCH_THEN(MP_TAC o SPEC `a:real`) THEN REWRITE_TAC[];
   ALL_TAC] THEN
  ASM_SIMP_TAC[PROB_DIFF_SUBSET] THEN
  REWRITE_TAC[GSYM distribution_fn] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> y - x = &0`) THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC `\n. distribution_fn (p:A prob_space) X (a - &1 / &(SUC n))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
  [REWRITE_TAC[distribution_fn] THEN
   MATCH_MP_TAC PROB_STRICT_INEQ_LIMIT THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC REALLIM_CONTINUOUS_FUNCTION THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   X_GEN_TAC `e:real` THEN DISCH_TAC THEN
   MP_TAC(SPEC `inv(e:real)` REAL_ARCH_SIMPLE) THEN
   DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
   X_GEN_TAC `n:num` THEN DISCH_TAC THEN
   REWRITE_TAC[REAL_ARITH `(a - x) - a:real = --x`; REAL_ABS_NEG;
               real_div; REAL_MUL_LID; REAL_ABS_INV; REAL_ABS_NUM] THEN
   SUBGOAL_THEN `inv(e:real) < &(SUC n)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&n:real` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N:real` THEN
     ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
     REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC];
    ALL_TAC] THEN
   SUBGOAL_THEN `&0 < inv(e:real)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   MP_TAC(SPECL [`inv(e:real)`; `&(SUC n)`] REAL_LT_INV2) THEN
   ASM_REWRITE_TAC[REAL_INV_INV]]);;

(* Random variable property of the inversion kernel g_T(X).
   g_T(v) = inv(pi) * int_0^T (sin(t(b-v)) - sin(t(a-v)))/t dt
   is continuous in v (parametric integral of jointly continuous integrand
   over compact [0,T]), so g_T o X is a random variable when X is. *)
let INVERSION_KERNEL_RV = prove
 (`!p:A prob_space X a b TT.
    random_variable p X /\ &0 <= TT /\ a < b ==>
    random_variable p (\x. inv(pi) * real_integral (real_interval[&0,TT])
      (\t. (sin(t * (b - X x)) - sin(t * (a - X x))) * inv t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `TT = &0` THENL
  [ASM_REWRITE_TAC[REAL_INTEGRAL_REFL; REAL_MUL_RZERO] THEN
   REWRITE_TAC[RANDOM_VARIABLE_CONST]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < TT` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(BETA_RULE(ISPECL [`p:A prob_space`; `X:A->real`;
    `\v:real. inv(pi) * real_integral (real_interval[&0,TT])
      (\t. (sin(t * (b - v)) - sin(t * (a - v))) * inv t)`]
    RANDOM_VARIABLE_COMP_CONTINUOUS)) THEN
  ASM_REWRITE_TAC[] THEN
  (* Need: (\v. inv(pi) * int_0^T ...) real_continuous_on (:real) *)
  MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
  SIMP_TAC[REAL_CONTINUOUS_ON_EQ_REAL_CONTINUOUS_AT; REAL_OPEN_UNIV;
    IN_UNIV] THEN
  X_GEN_TAC `v:real` THEN
  REWRITE_TAC[REAL_CONTINUOUS_ATREAL; REALLIM_ATREAL] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `e / (&2 * TT)` THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `w:real` THEN STRIP_TAC THEN
  (* |int_0^T f(t,v) dt - int_0^T f(t,w) dt| <= int_0^T |f(t,v)-f(t,w)| dt
     <= int_0^T 2*|v-w| dt = 2*T*|v-w| < 2*T*(e/(2T)) = e *)
  (* Step 1: Establish integrability of both integrands *)
  SUBGOAL_THEN
    `!u:real. (\t. (sin(t * (b - u)) - sin(t * (a - u))) * inv t)
       real_integrable_on real_interval[&0,TT]`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   SUBGOAL_THEN `(\t:real. (sin(t * (b - u)) - sin(t * (a - u))) * inv t) =
     (\t. sin((b - u) * t) * inv t - sin((a - u) * t) * inv t)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `t:real` THEN
    SUBGOAL_THEN `t * (b - u:real) = (b - u) * t` (fun th -> REWRITE_TAC[th]) THENL
    [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `t * (a - u:real) = (a - u) * t` (fun th -> REWRITE_TAC[th]) THENL
    [REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN CONJ_TAC THENL
   [ASM_CASES_TAC `b - u = &0` THENL
    [ASM_REWRITE_TAC[REAL_MUL_LZERO; SIN_0; REAL_MUL_LZERO;
      REAL_INTEGRABLE_0];
     MATCH_MP_TAC SINC_SCALED_INTEGRABLE_NZ THEN
     ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ASM_CASES_TAC `a - u = &0` THENL
    [ASM_REWRITE_TAC[REAL_MUL_LZERO; SIN_0; REAL_MUL_LZERO;
      REAL_INTEGRABLE_0];
     MATCH_MP_TAC SINC_SCALED_INTEGRABLE_NZ THEN
     ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]];
   ALL_TAC] THEN
  (* Step 2: Bound abs of integral difference *)
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `(&2 * abs(v - w)) * TT` THEN CONJ_TAC THENL
  [SUBGOAL_THEN
    `real_integral (real_interval[&0,TT])
       (\t. (sin(t * (b - w)) - sin(t * (a - w))) * inv t) -
     real_integral (real_interval[&0,TT])
       (\t. (sin(t * (b - v)) - sin(t * (a - v))) * inv t) =
     real_integral (real_interval[&0,TT])
       (\t. ((sin(t * (b - w)) - sin(t * (a - w))) * inv t) -
            ((sin(t * (b - v)) - sin(t * (a - v))) * inv t))`
     SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INTEGRAL_SUB THEN
    CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC; ALL_TAC] THEN
   (* Apply HAS_REAL_INTEGRAL_BOUND: abs(i) <= B * (b - a) *)
   MP_TAC(ISPECL
     [`\t:real. ((sin(t * (b - w)) - sin(t * (a - w))) * inv t) -
               ((sin(t * (b - v)) - sin(t * (a - v))) * inv t)`;
      `&0`; `TT:real`;
      `real_integral (real_interval[&0,TT])
        (\t:real. ((sin(t * (b - w)) - sin(t * (a - w))) * inv t) -
             ((sin(t * (b - v)) - sin(t * (a - v))) * inv t))`;
      `&2 * abs(v - w:real)`] HAS_REAL_INTEGRAL_BOUND) THEN
   REWRITE_TAC[REAL_SUB_RZERO] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; REWRITE_TAC[REAL_ABS_POS]];
     ASM_REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
     MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN
     CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
    (* Bound: |f_w(t) - f_v(t)| <= 2*|v-w| for all t in [0,TT] *)
    X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    DISCH_TAC THEN
    ASM_CASES_TAC `t = &0` THENL
    [ASM_REWRITE_TAC[REAL_MUL_LZERO; SIN_0; REAL_SUB_REFL;
      REAL_MUL_LZERO; REAL_SUB_REFL; REAL_ABS_NUM] THEN
     MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; REWRITE_TAC[REAL_ABS_POS]]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    (* Factor out inv t from the difference *)
    REWRITE_TAC[REAL_ARITH `!a b c d e:real.
      (a - b) * c - (d - e) * c = ((a - d) - (b - e)) * c`] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs(inv t) = inv t` SUBST1_TAC THENL
    [REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC REAL_LE_INV THEN
     ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    (* Use triangle: |x - y| <= |x| + |y| *)
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(abs(sin(t * (b - w)) - sin(t * (b - v))) +
                 abs(sin(t * (a - w)) - sin(t * (a - v)))) * inv t` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
    (* Use SIN_LIPSCHITZ: |sin a - sin b| <= |a - b| *)
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(abs(t * (b - w) - t * (b - v)) +
                 abs(t * (a - w) - t * (a - v))) * inv t` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD2 THEN REWRITE_TAC[SIN_LIPSCHITZ];
      MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
    (* Simplify: t*(b-w) - t*(b-v) = t*(v-w), same for a *)
    SUBGOAL_THEN `t * (b - w) - t * (b - v) = t * (v - w:real)`
      SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN `t * (a - w) - t * (a - v) = t * (v - w:real)`
      SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs t = t` SUBST1_TAC THENL
    [REWRITE_TAC[REAL_ABS_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(t * abs(v - w) + t * abs(v - w)) * inv t =
                  &2 * abs(v - w:real)`
      (fun th -> REWRITE_TAC[th; REAL_LE_REFL]) THEN
    UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD];
   SIMP_TAC[]];
  (* Step 3: (&2*|v-w|)*TT < e *)
  REWRITE_TAC[REAL_ABS_SUB] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `(&2 * (e / (&2 * TT))) * TT` THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LT_RMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
    [REAL_ARITH_TAC;
     UNDISCH_TAC `abs(w - v:real) < e / (&2 * TT)` THEN REAL_ARITH_TAC];
    UNDISCH_TAC `&0 < TT` THEN REAL_ARITH_TAC];
   MATCH_MP_TAC REAL_EQ_IMP_LE THEN
   UNDISCH_TAC `&0 < TT` THEN CONV_TAC REAL_FIELD]]);;

(* Helper: integrability of the inversion kernel on [0,TT] for any a,b,v,TT *)
let SINC_SCALED_DIFF_INTEGRABLE = prove
 (`!a b v TT. &0 <= TT ==>
   (\t. (sin(t * (b - v)) - sin(t * (a - v))) * inv t)
     real_integrable_on real_interval[&0,TT]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\t:real. (sin(t * (b - v)) - sin(t * (a - v))) * inv t) =
    (\t. sin((b - v) * t) * inv t - sin((a - v) * t) * inv t)`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `t:real` THEN
   SUBGOAL_THEN `t * (b - v:real) = (b - v) * t` (fun th -> REWRITE_TAC[th]) THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `t * (a - v:real) = (a - v) * t` (fun th -> REWRITE_TAC[th]) THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN CONJ_TAC THENL
  [ASM_CASES_TAC `b - v = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO; SIN_0; REAL_MUL_LZERO;
     REAL_INTEGRABLE_0];
    MATCH_MP_TAC SINC_SCALED_INTEGRABLE_NZ THEN
    ASM_REWRITE_TAC[]];
   ASM_CASES_TAC `a - v = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO; SIN_0; REAL_MUL_LZERO;
     REAL_INTEGRABLE_0];
    MATCH_MP_TAC SINC_SCALED_INTEGRABLE_NZ THEN
    ASM_REWRITE_TAC[]]]);;

(* Helper: integral over [0,(n+1)*h] = sum of integrals over subintervals *)
let INTEGRAL_SPLIT_NUMSEG = prove
 (`!f h n. &0 < h /\ f real_integrable_on real_interval[&0, &(SUC n) * h]
   ==> real_integral (real_interval[&0, &(SUC n) * h]) f =
       sum(0..n) (\k. real_integral (real_interval[&k * h, &(SUC k) * h]) f)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [STRIP_TAC THEN REWRITE_TAC[SUM_SING_NUMSEG] THEN
   REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; ARITH_RULE `SUC 0 = 1`];
   STRIP_TAC THEN
   SUBGOAL_THEN `&(SUC(SUC n)) * h = &(SUC n) * h + h` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB; REAL_MUL_LID];
    ALL_TAC] THEN
   SUBGOAL_THEN `real_integral (real_interval [&0,&(SUC n) * h + h]) f =
     real_integral (real_interval [&0, &(SUC n) * h]) f +
     real_integral (real_interval [&(SUC n) * h, &(SUC n) * h + h]) f`
     SUBST1_TAC THENL
   [MATCH_MP_TAC(GSYM REAL_INTEGRAL_COMBINE) THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
     ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `real_interval[&0, &(SUC(SUC n)) * h]` THEN
    ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL; GSYM REAL_OF_NUM_SUC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
   SUBGOAL_THEN `real_integral (real_interval [&0,&(SUC n) * h]) f =
     sum (0..n) (\k. real_integral (real_interval [&k * h,&(SUC k) * h]) f)`
     SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `real_interval[&0, &(SUC(SUC n)) * h]` THEN
    ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL; GSYM REAL_OF_NUM_SUC] THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `&(SUC n) * h + h = &(SUC(SUC n)) * h`
      (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB; REAL_MUL_LID]]]);;

(* Riemann sum convergence for bounded functions continuous on (0,TT].
   Uses uniform continuity on [eta,TT] plus epsilon-delta. *)
let RIEMANN_SUM_CONVERGES = prove
 (`!f TT M.
     f real_integrable_on real_interval[&0,TT] /\
     &0 < TT /\ &0 < M /\
     (!t. t IN real_interval[&0,TT] ==> abs(f t) <= M) /\
     (!t. t IN real_interval[&0,TT] /\ &0 < t ==>
       f real_continuous (atreal t within real_interval[&0,TT]))
     ==> ((\n. sum(0..n) (\k. TT / &(SUC n) *
            f(&k * TT / &(SUC n)))) --->
          real_integral (real_interval[&0,TT]) f) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `eta = min (TT / &2) (e / (&8 * M))` THEN
  (* Establish properties of eta *)
  SUBGOAL_THEN `&0 < eta /\ eta <= TT / &2 /\ eta <= e / (&8 * M)`
    STRIP_ASSUME_TAC THENL
  [EXPAND_TAC "eta" THEN
   ASM_SIMP_TAC[REAL_LT_MIN; REAL_LE_MIN; REAL_LT_DIV; REAL_LT_MUL;
     REAL_ARITH `&0 < &2`; REAL_ARITH `&0 < &8`;
     REAL_ARITH `min a b <= a /\ min a b <= b`] THEN
   ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_ARITH `&0 < &8`];
   ALL_TAC] THEN
  (* f is continuous on [eta, TT] *)
  SUBGOAL_THEN `f real_continuous_on real_interval[eta,TT]` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
   X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
   DISCH_TAC THEN
   MATCH_MP_TAC REAL_CONTINUOUS_WITHINREAL_SUBSET THEN
   EXISTS_TAC `real_interval[&0,TT]` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* f is uniformly continuous on [eta, TT] *)
  SUBGOAL_THEN `f real_uniformly_continuous_on real_interval[eta,TT]`
    ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_COMPACT_UNIFORMLY_CONTINUOUS THEN
   ASM_REWRITE_TAC[REAL_COMPACT_INTERVAL];
   ALL_TAC] THEN
  (* Get delta from uniform continuity *)
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [real_uniformly_continuous_on]) THEN
  DISCH_THEN(MP_TAC o SPEC `e / (&2 * TT)`) THEN
  ANTS_TAC THENL
  [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_ARITH `&0 < &2`];
   ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  (* Choose N *)
  MP_TAC(SPEC `TT / min eta d` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ABBREV_TAC `h = TT / &(SUC n)` THEN
  (* Key properties of h *)
  SUBGOAL_THEN `&0 < h /\ h < eta /\ h < d` STRIP_ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 < &(SUC n)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; LT_0]; ALL_TAC] THEN
   SUBGOAL_THEN `&0 < min eta d` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
   SUBGOAL_THEN `TT / &(SUC n) < min eta d` ASSUME_TAC THENL
   [SUBGOAL_THEN `TT / min eta d < &(SUC n)` MP_TAC THENL
    [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&N` THEN
     ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
     ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN DISCH_TAC THEN
     ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC];
   ASM_MESON_TAC[REAL_LT_MIN; REAL_LT_DIV]];
   ALL_TAC] THEN
  SUBGOAL_THEN `&(SUC n) * h = TT` ASSUME_TAC THENL
  [EXPAND_TAC "h" THEN
   ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ; NOT_SUC]; ALL_TAC] THEN
  (* Use INTEGRAL_SPLIT_NUMSEG *)
  SUBGOAL_THEN
    `real_integral (real_interval [&0,TT]) f =
     sum(0..n) (\k. real_integral (real_interval[&k * h, &(SUC k) * h]) f)`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`f:real->real`; `h:real`; `n:num`] INTEGRAL_SPLIT_NUMSEG) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Rewrite the difference as a sum *)
  SUBGOAL_THEN
    `sum(0..n) (\k. h * f(&k * h)) -
     real_integral (real_interval [&0,TT]) f =
     sum(0..n) (\k. h * f(&k * h) -
       real_integral (real_interval[&k * h, &(SUC k) * h]) f)`
    SUBST1_TAC THENL
  [ASM_REWRITE_TAC[GSYM SUM_SUB_NUMSEG]; ALL_TAC] THEN
  (* Find cutoff index p *)
  SUBGOAL_THEN `?p. p <= n /\ &p * h < eta /\ eta <= &(SUC p) * h`
    STRIP_ASSUME_TAC THENL
  [MP_TAC(ISPEC `\k. k <= n /\ eta <= &k * h` num_WOP) THEN
   DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
   ANTS_TAC THENL
   [EXISTS_TAC `n:num` THEN REWRITE_TAC[] THEN
    CONJ_TAC THENL
    [ARITH_TAC;
     UNDISCH_TAC `&(SUC n) * h = TT` THEN
     REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
     UNDISCH_TAC `h < eta` THEN UNDISCH_TAC `eta <= TT / &2` THEN
     REAL_ARITH_TAC];
    ALL_TAC] THEN
   REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `0 < q` ASSUME_TAC THENL
   [ASM_CASES_TAC `q = 0` THEN ASM_REWRITE_TAC[] THENL
    [UNDISCH_TAC `eta <= &q * h` THEN
     ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC;
     ASM_ARITH_TAC];
    ALL_TAC] THEN
   EXISTS_TAC `q - 1` THEN
   SUBGOAL_THEN `SUC(q - 1) = q` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `q - 1`) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[DE_MORGAN_THM; NOT_LE; REAL_NOT_LE] THEN
   DISCH_THEN DISJ_CASES_TAC THENL
   [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* Split the sum at index p *)
  SUBGOAL_THEN
    `sum(0..n) (\k. h * f(&k * h) -
       real_integral (real_interval[&k * h, &(SUC k) * h]) f) =
     sum(0..p) (\k. h * f(&k * h) -
       real_integral (real_interval[&k * h, &(SUC k) * h]) f) +
     sum(p + 1..n) (\k. h * f(&k * h) -
       real_integral (real_interval[&k * h, &(SUC k) * h]) f)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC(GSYM SUM_COMBINE_R) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  (* Bound: |A + B| <= |A| + |B| < 4*M*eta + e/2 <= e *)
  MATCH_MP_TAC(REAL_ARITH
    `abs a < &4 * M * eta /\ abs b <= e / &2 /\ &4 * M * eta + e / &2 <= e
     ==> abs(a + b) < e`) THEN
  REPEAT CONJ_TAC THENL
  [(* Bound for near-zero part: |sum(0..p)(...)| < 4*M*eta *)
   MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `sum(0..p) (\k. abs(h * (f:real->real)(&k * h) -
     real_integral (real_interval[&k * h, &(SUC k) * h]) f))` THEN
   CONJ_TAC THENL [MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG; REAL_LE_REFL]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `sum(0..p) (\k. &2 * M * h)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    (* Each |h*f(kh) - integral[kh,(k+1)h] f| <= 2*M*h *)
    MATCH_MP_TAC(REAL_ARITH
      `abs a <= M * h /\ abs b <= M * h ==> abs(a - b) <= &2 * M * h`) THEN
    CONJ_TAC THENL
    [(* |h * f(kh)| <= M * h *)
     REWRITE_TAC[REAL_ABS_MUL] THEN
     ASM_SIMP_TAC[REAL_ARITH `&0 < h ==> abs h = h`] THEN
     GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
     ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
     SUBGOAL_THEN `&k * h IN real_interval[&0,TT]` MP_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL] THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
       ASM_REAL_ARITH_TAC;
       MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(SUC n) * h` THEN
       CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[REAL_LE_REFL]] THEN
       MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
       REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
      ASM_MESON_TAC[]];
     (* |integral[kh,(k+1)h] f| <= M * h *)
     MP_TAC(ISPECL [`f:real->real`; `&k * h`; `&(SUC k) * h`;
       `real_integral (real_interval[&k * h, &(SUC k) * h]) f`;
       `M:real`] HAS_REAL_INTEGRAL_BOUND) THEN
     ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
        ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
       MATCH_MP_TAC REAL_INTEGRABLE_ON_SUBINTERVAL THEN
       EXISTS_TAC `real_interval[&0,TT]` THEN ASM_REWRITE_TAC[] THEN
       REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
       DISJ2_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        ASM_REAL_ARITH_TAC;
        CONJ_TAC THENL
        [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
         [REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
          ASM_REAL_ARITH_TAC];
         MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(SUC n) * h` THEN
         CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[REAL_LE_REFL]] THEN
         MATCH_MP_TAC REAL_LE_RMUL THEN
         ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
         REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC]];
       X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
       DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
       REWRITE_TAC[IN_REAL_INTERVAL] THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&k * h` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(SUC k) * h` THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(SUC n) * h` THEN
        CONJ_TAC THENL
        [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
         REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
         ASM_REWRITE_TAC[REAL_LE_REFL]]]];
      REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
      REAL_ARITH_TAC]];
    (* (p+1) * 2*M*h < 4*M*eta *)
    REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0] THEN
    SUBGOAL_THEN `&(p + 1) * h < &2 * eta` ASSUME_TAC THENL
    [REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
     ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&(p + 1) * (&2 * M * h) = &2 * M * (&(p + 1) * h)`
      SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&4 * M * eta = &2 * M * (&2 * eta)`
      SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
    [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
   (* Bound for far part: |sum(p+1..n)(...)| <= e/2 *)
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `sum(p + 1..n) (\k. abs(h * (f:real->real)(&k * h) -
     real_integral (real_interval[&k * h, &(SUC k) * h]) f))` THEN
   CONJ_TAC THENL [MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG; REAL_LE_REFL]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `sum(p + 1..n) (\k. (e / (&2 * TT)) * h)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    (* For k >= p+1: kh >= eta, use uniform continuity *)
    SUBGOAL_THEN `eta <= &k * h` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(SUC p) * h` THEN
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
     ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
     REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
     ALL_TAC] THEN
    (* |h*f(kh) - integral[kh,(k+1)h]f| = |integral (\t. f(kh) - f(t))| *)
    SUBGOAL_THEN `h * (f:real->real)(&k * h) -
      real_integral (real_interval[&k * h, &(SUC k) * h]) f =
      real_integral (real_interval[&k * h, &(SUC k) * h])
        (\t. f(&k * h) - f t)` SUBST1_TAC THENL
    [SUBGOAL_THEN `f real_integrable_on real_interval[&k * h, &(SUC k) * h]`
       ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_ON_SUBINTERVAL THEN
      EXISTS_TAC `real_interval[&0,TT]` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN DISJ2_TAC THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
       ASM_REAL_ARITH_TAC;
       CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
        [REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
         ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(SUC n) * h` THEN
        CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[REAL_LE_REFL]] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC]];
      ALL_TAC] THEN
     ASM_SIMP_TAC[REAL_INTEGRAL_SUB; REAL_INTEGRABLE_CONST] THEN
     SUBGOAL_THEN `&k * h <= &(SUC k) * h` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
      [REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
       ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
     ASM_SIMP_TAC[REAL_INTEGRAL_CONST] THEN
     REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
     CONV_TAC REAL_RING;
     ALL_TAC] THEN
    (* Bound using HAS_REAL_INTEGRAL_BOUND *)
    MP_TAC(ISPECL
      [`\t. (f:real->real)(&k * h) - f t`;
       `&k * h`; `&(SUC k) * h`;
       `real_integral (real_interval[&k * h, &(SUC k) * h])
         (\t. (f:real->real)(&k * h) - f t)`;
       `e / (&2 * TT)`]
      HAS_REAL_INTEGRAL_BOUND) THEN
    ANTS_TAC THENL
    [CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_DIV;
       REAL_LT_MUL; REAL_ARITH `&0 < &2`]; ALL_TAC] THEN
     CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
      MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN
      REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
      MATCH_MP_TAC REAL_INTEGRABLE_ON_SUBINTERVAL THEN
      EXISTS_TAC `real_interval[&0,TT]` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN DISJ2_TAC THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
       ASM_REAL_ARITH_TAC;
       CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
        [REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
         ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(SUC n) * h` THEN
        CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[REAL_LE_REFL]] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC]];
      ALL_TAC] THEN
     (* Bound |f(kh) - f(t)| < e/(2*TT) using uniform continuity *)
     X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
     DISCH_TAC THEN REWRITE_TAC[REAL_ABS_SUB] THEN
     MATCH_MP_TAC REAL_LT_IMP_LE THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     REWRITE_TAC[IN_REAL_INTERVAL] THEN
     REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(SUC n) * h` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[REAL_LE_REFL]] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(SUC k) * h` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(SUC n) * h` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
       REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
       ASM_REWRITE_TAC[REAL_LE_REFL]];
      REWRITE_TAC[REAL_ABS_SUB] THEN
      MATCH_MP_TAC(REAL_ARITH `a <= t /\ t <= a + h /\ h < d
        ==> abs(t - a) < d`) THEN
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB;
        REAL_MUL_LID] THEN
      UNDISCH_TAC `&k * h <= t /\ t <= &(SUC k) * h` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
      REAL_ARITH_TAC];
     MATCH_MP_TAC(REAL_ARITH `a = b ==> x <= a ==> x <= b`) THEN
     REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
     REAL_ARITH_TAC];
    (* Sum of (e/(2*TT))*h over (SUC p)..n <= e/2 *)
    REWRITE_TAC[SUM_CONST_NUMSEG] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(SUC n) * (e / (&2 * TT)) * h` THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
      MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_ARITH `&0 < &2`]];
     SUBGOAL_THEN `&(SUC n) * (e / (&2 * TT)) * h = e / &2`
       (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `&(SUC n) * h = TT` THEN
      UNDISCH_TAC `&0 < TT` THEN
      CONV_TAC REAL_FIELD;
      REAL_ARITH_TAC]]];
   (* 4*M*eta + e/2 <= e, from eta <= e/(8*M) *)
   MATCH_MP_TAC(REAL_ARITH
     `x <= e / &2 ==> x + e / &2 <= e`) THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 * M * (e / (&8 * M))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
     ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `&4 * M * (e / (&8 * M)) = e / &2` (fun th -> REWRITE_TAC[th]) THENL
    [UNDISCH_TAC `&0 < M` THEN CONV_TAC REAL_FIELD; REAL_ARITH_TAC]]]);;


(* Fubini exchange for bounded kernels: int_[0,TT] E[h(t,X)] = E[int_[0,TT] h(t,X)]
   Uses: REALLIM_UNIQUE with Riemann sums as common sequence.
   Branch 1: Riemann sums -> LHS via RIEMANN_SUM_CONVERGES
   Branch 2: Riemann sums -> RHS via BOUNDED_CONVERGENCE_EXPECTATION_GEN
   Extra hypotheses: integrability and continuity of t -> E[h(t,X)] *)
let INTEGRAL_EXPECTATION_EXCHANGE = prove
 (`!p:A prob_space X (h:real->real->real) TT M.
    random_variable p X /\ &0 < TT /\ &0 < M /\
    (!t v. abs(h t v) <= M) /\
    (!v. (\t. h t v) real_integrable_on real_interval[&0,TT]) /\
    (!t. integrable p (\x. h t (X x))) /\
    (!v t. &0 < t /\ t <= TT ==>
      (\s. h s v) real_continuous (atreal t within real_interval[&0,TT])) /\
    (\t. expectation p (\x. h t (X x)))
      real_integrable_on real_interval[&0,TT] /\
    (!t. t IN real_interval[&0,TT] /\ &0 < t ==>
      (\s. expectation p (\x. h s (X x)))
        real_continuous (atreal t within real_interval[&0,TT]))
    ==> real_integral (real_interval [&0,TT])
          (\t. expectation p (\x. h t (X x))) =
        expectation p (\x. real_integral (real_interval [&0,TT])
          (\t. h t (X x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  EXISTS_TAC `\n:num. sum(0..n) (\k. TT / &(SUC n) *
    expectation (p:A prob_space) (\x:A. (h:real->real->real)
      (&k * TT / &(SUC n)) (X x)))` THEN
  CONJ_TAC THENL
  [(* Branch 1: Riemann sums -> integral of E[h(t,X)] *)
   MP_TAC(ISPECL [`\t:real. expectation (p:A prob_space)
     (\x:A. (h:real->real->real) t (X x))`; `TT:real`; `M:real`]
     RIEMANN_SUM_CONVERGES) THEN
   ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[];
     (* Bound: |E[h(t,X)]| <= M *)
     BETA_TAC THEN GEN_TAC THEN DISCH_TAC THEN
     MATCH_MP_TAC EXPECTATION_BOUND THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]];
     (* Continuity of E[h(t,X)] at t > 0 *)
     BETA_TAC THEN GEN_TAC THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN
     ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    REWRITE_TAC[]];
   (* Branch 2: Riemann sums -> E[integral h(t,X)] *)
   (* Step 1: Rewrite sum of delta*E[h_k] as E[sum of delta*h_k] *)
   SUBGOAL_THEN `!n:num. sum(0..n) (\k. TT / &(SUC n) *
     expectation (p:A prob_space) (\x:A. (h:real->real->real)
       (&k * TT / &(SUC n)) (X x))) =
     expectation p (\x. sum(0..n) (\k. TT / &(SUC n) *
       h (&k * TT / &(SUC n)) (X x)))` ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `sum(0..n) (\k. TT / &(SUC n) *
      expectation (p:A prob_space) (\x:A. (h:real->real->real)
        (&k * TT / &(SUC n)) (X x))) =
      sum(0..n) (\k. expectation p (\x. TT / &(SUC n) *
        h (&k * TT / &(SUC n)) (X x)))` SUBST1_TAC THENL
    [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
     BETA_TAC THEN CONV_TAC SYM_CONV THEN
     MATCH_MP_TAC EXPECTATION_CMUL THEN ASM_REWRITE_TAC[];
     CONV_TAC SYM_CONV THEN
     MP_TAC(ISPECL [`p:A prob_space`;
       `\k (x:A). TT / &(SUC n) *
         (h:real->real->real) (&k * TT / &(SUC n)) ((X:A->real) x)`;
       `n:num`] EXPECTATION_SUM) THEN
     ANTS_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[]]];
    ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   (* Step 2: Apply bounded convergence *)
   SUBGOAL_THEN
     `integrable (p:A prob_space)
        (\x:A. real_integral (real_interval[&0,TT])
          (\t. (h:real->real->real) t (X x))) /\
      ((\n. expectation p (\x. sum(0..n) (\k. TT / &(SUC n) *
        h (&k * TT / &(SUC n)) (X x)))) --->
       expectation p (\x. real_integral (real_interval[&0,TT])
        (\t. h t (X x)))) sequentially`
     (fun th -> ACCEPT_TAC(CONJUNCT2 th)) THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `\n (x:A). sum(0..n) (\k. TT / &(SUC n) *
        (h:real->real->real) (&k * TT / &(SUC n)) ((X:A->real) x))`;
     `\x:A. real_integral (real_interval[&0,TT])
        (\t. (h:real->real->real) t ((X:A->real) x))`;
     `(M:real) * (TT:real)`] BOUNDED_CONVERGENCE_EXPECTATION_GEN) THEN
   ANTS_TAC THENL
   [BETA_TAC THEN REPEAT CONJ_TAC THENL
    [(* random_variable p (\x. sum ...) for each n *)
     GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
     MATCH_MP_TAC INTEGRABLE_SUM THEN GEN_TAC THEN DISCH_TAC THEN
     BETA_TAC THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
     (* Bound: |sum(0..n)(\k. delta*h(k*delta, X x))| <= M*TT *)
     REPEAT STRIP_TAC THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `sum(0..n) (\k:num. TT / &(SUC n) * M)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_ABS_LE THEN
      REWRITE_TAC[FINITE_NUMSEG] THEN BETA_TAC THEN
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 <= TT / &(SUC n)` ASSUME_TAC THENL
      [MATCH_MP_TAC REAL_LE_DIV THEN
       CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; REWRITE_TAC[REAL_POS]];
       ALL_TAC] THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0; GSYM ADD1] THEN
      SUBGOAL_THEN `~(&(SUC n) = &0)` ASSUME_TAC THENL
      [REWRITE_TAC[REAL_OF_NUM_EQ; NOT_SUC]; ALL_TAC] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_DIV_LMUL] THEN REAL_ARITH_TAC];
     (* Pointwise convergence: Riemann sums -> integral for each x *)
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN
     MP_TAC(ISPECL [`\t:real. (h:real->real->real) t ((X:A->real) x)`;
       `TT:real`; `M:real`] RIEMANN_SUM_CONVERGES) THEN
     ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
      [ASM_SIMP_TAC[];
       ASM_REWRITE_TAC[];
       ASM_REWRITE_TAC[];
       BETA_TAC THEN GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
       GEN_TAC THEN STRIP_TAC THEN
       FIRST_X_ASSUM(MP_TAC o SPECL [`(X:A->real) x`; `t:real`]) THEN
       ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_REAL_INTERVAL]) THEN
        REAL_ARITH_TAC;
        SIMP_TAC[]]];
      REWRITE_TAC[]]];
    SIMP_TAC[]]]);;

(* Sequential characterization implies real continuity (bridge lemma). *)
let REAL_CONTINUOUS_ATREAL_SEQUENTIALLY = prove
 (`!f x. (!s. (s ---> x) sequentially ==> ((\n. f(s n)) ---> f x) sequentially)
         ==> f real_continuous (atreal x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS_ATREAL; CONTINUOUS_AT_SEQUENTIALLY] THEN
  X_GEN_TAC `s:num->real^1` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(drop:real^1->real) o (s:num->real^1)`) THEN
  ANTS_TAC THENL
  [UNDISCH_TAC `(s:num->real^1 --> lift x) sequentially` THEN
   REWRITE_TAC[REAL_TENDSTO; LIFT_DROP];
   REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_DROP]]);;

(* Continuity of characteristic function (real and imaginary parts).
   Proof uses bounded convergence: for t_n -> t,
   cos(t_n * X) -> cos(t * X) pointwise with |cos(t_n * X)| <= 1,
   so E[cos(t_n * X)] -> E[cos(t * X)] by BCT. *)
let CHAR_FN_RE_CONTINUOUS = prove
 (`!p:A prob_space X. random_variable p X ==>
   char_fn_re p X real_continuous_on (:real)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_UNIV;
              WITHINREAL_UNIV] THEN
  X_GEN_TAC `t:real` THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_SEQUENTIALLY THEN
  X_GEN_TAC `s:num->real` THEN DISCH_TAC THEN
  REWRITE_TAC[char_fn_re] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `(\n:num. \x:A. cos(s n * X x)):num->A->real`;
                  `(\x:A. cos(t * X x)):A->real`; `&1`]
    BOUNDED_CONVERGENCE_EXPECTATION_GEN) THEN
  BETA_TAC THEN REWRITE_TAC[] THEN ANTS_TAC THENL
  [CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_COS THEN
    MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[COS_BOUND];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REALLIM_COS THEN
    MATCH_MP_TAC REALLIM_RMUL THEN ASM_REWRITE_TAC[]];
   SIMP_TAC[]]);;

let CHAR_FN_IM_CONTINUOUS = prove
 (`!p:A prob_space X. random_variable p X ==>
   char_fn_im p X real_continuous_on (:real)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_UNIV;
              WITHINREAL_UNIV] THEN
  X_GEN_TAC `t:real` THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_SEQUENTIALLY THEN
  X_GEN_TAC `s:num->real` THEN DISCH_TAC THEN
  REWRITE_TAC[char_fn_im] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `(\n:num. \x:A. sin(s n * X x)):num->A->real`;
                  `(\x:A. sin(t * X x)):A->real`; `&1`]
    BOUNDED_CONVERGENCE_EXPECTATION_GEN) THEN
  BETA_TAC THEN REWRITE_TAC[] THEN ANTS_TAC THENL
  [CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_SIN THEN
    MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[SIN_BOUND];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REALLIM_SIN THEN
    MATCH_MP_TAC REALLIM_RMUL THEN ASM_REWRITE_TAC[]];
   SIMP_TAC[]]);;

(* Fubini exchange: connect inversion integral to expectation of kernel.
   For T > 0, the inversion integral equals E[g_T(X)] where
   g_T(v) = inv(pi) * int_0^T (sin(t(b-v)) - sin(t(a-v)))/t dt.
   The proof uses:
   - Algebraic rewriting of char_fn_re/im as expectations
   - The trig identity INVERSION_TRIG_IDENTITY
   - Evenness of the integrand (REAL_INTEGRAL_EVEN_SYMMETRIC)
   - Exchange of bounded integral with expectation (Fubini) *)
let INVERSION_FUBINI = prove
 (`!p:A prob_space X a b TT.
    random_variable p X /\ &0 < TT /\ a < b ==>
    inv(&2 * pi) *
    real_integral (real_interval [--TT, TT])
      (\t. ((sin(t * b) - sin(t * a)) * char_fn_re p X t -
            (cos(t * b) - cos(t * a)) * char_fn_im p X t) * inv t) =
    expectation p (\x. inv(pi) * real_integral (real_interval[&0,TT])
      (\t. (sin(t * (b - X x)) - sin(t * (a - X x))) * inv t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `h = \t v:real. (sin(t * (b - v)) - sin(t * (a - v))) * inv t` THEN
  (* Integrability facts needed throughout *)
  SUBGOAL_THEN `!t:real. integrable (p:A prob_space) (\x. cos(t * X x))`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_COS_CMUL THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!t:real. integrable (p:A prob_space) (\x. sin(t * X x))`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_SIN_CMUL THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 2: Show for each t the integrand = E[h(t,X)] *)
  SUBGOAL_THEN `!t:real.
    ((sin(t * b) - sin(t * a)) * char_fn_re (p:A prob_space) X t -
     (cos(t * b) - cos(t * a)) * char_fn_im p X t) * inv t =
    expectation p (\x:A. (h:real->real->real) t (X x))` ASSUME_TAC THENL
  [X_GEN_TAC `t:real` THEN EXPAND_TAC "h" THEN BETA_TAC THEN
   REWRITE_TAC[char_fn_re; char_fn_im] THEN
   SUBGOAL_THEN
     `((sin(t * b) - sin(t * a)) * expectation (p:A prob_space) (\x. cos(t * X x)) -
       (cos(t * b) - cos(t * a)) * expectation p (\x. sin(t * X x))) * inv t =
      expectation p (\x. ((sin(t * b) - sin(t * a)) * cos(t * X x) -
        (cos(t * b) - cos(t * a)) * sin(t * X x)) * inv t)` SUBST1_TAC THENL
   [SUBGOAL_THEN `integrable (p:A prob_space)
      (\x. (sin(t * b) - sin(t * a)) * cos(t * X x))` ASSUME_TAC THENL
    [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `integrable (p:A prob_space)
      (\x. (cos(t * b) - cos(t * a)) * sin(t * X x))` ASSUME_TAC THENL
    [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[EXPECTATION_SUB] THEN
    SUBGOAL_THEN `integrable (p:A prob_space) (\x.
      (sin(t * b) - sin(t * a)) * cos(t * X x) -
      (cos(t * b) - cos(t * a)) * sin(t * X x))` ASSUME_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(\x:A. ((sin(t * b) - sin(t * a)) * cos(t * (X:A->real) x) -
      (cos(t * b) - cos(t * a)) * sin(t * X x)) * inv t) =
      (\x. inv t * ((sin(t * b) - sin(t * a)) * cos(t * X x) -
      (cos(t * b) - cos(t * a)) * sin(t * X x)))` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[EXPECTATION_CMUL] THEN
    ASM_SIMP_TAC[EXPECTATION_SUB] THEN
    ASM_SIMP_TAC[EXPECTATION_CMUL] THEN REAL_ARITH_TAC;
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC `x:A` THEN BETA_TAC THEN
    MP_TAC(SPECL [`t:real`; `a:real`; `b:real`; `(X:A->real) x`]
      INVERSION_TRIG_IDENTITY) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th])];
   ALL_TAC] THEN
  (* Integrability of h(t, X x) for each t *)
  SUBGOAL_THEN `!t:real. integrable (p:A prob_space)
    (\x:A. (h:real->real->real) t (X x))` ASSUME_TAC THENL
  [X_GEN_TAC `t:real` THEN EXPAND_TAC "h" THEN BETA_TAC THEN
   MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `abs(b - a:real)` THEN
   CONJ_TAC THENL
   [SUBGOAL_THEN `(\x:A. (sin(t * (b - X x)) - sin(t * (a - X x))) * inv t) =
     (\x. (\v:real. (sin(t * (b - v)) - sin(t * (a - v))) * inv t) (X x))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
    MATCH_MP_TAC RANDOM_VARIABLE_COMP_CONTINUOUS THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_SIN] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_CONST; REAL_CONTINUOUS_ON_ID];
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_SIN] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_CONST; REAL_CONTINUOUS_ON_ID]];
     REWRITE_TAC[REAL_CONTINUOUS_ON_CONST]];
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[INVERSION_KERNEL_BOUNDED]];
   ALL_TAC] THEN
  (* Step 3: Rewrite the integral *)
  SUBGOAL_THEN
    `real_integral (real_interval [--TT, TT])
      (\t. ((sin(t * b) - sin(t * a)) * char_fn_re (p:A prob_space) X t -
            (cos(t * b) - cos(t * a)) * char_fn_im p X t) * inv t) =
     real_integral (real_interval [--TT, TT])
      (\t. expectation p (\x:A. (h:real->real->real) t (X x)))`
    SUBST1_TAC THENL
  [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Integrability on [-TT,TT] via measurability + boundedness *)
  SUBGOAL_THEN `(\t. expectation (p:A prob_space)
    (\x:A. (h:real->real->real) t (X x)))
    real_integrable_on real_interval[--TT,TT]` ASSUME_TAC THENL
  [SUBGOAL_THEN `(\t. expectation (p:A prob_space)
      (\x:A. (h:real->real->real) t (X x))) =
    (\t. ((sin(t * b) - sin(t * a)) * char_fn_re p X t -
          (cos(t * b) - cos(t * a)) * char_fn_im p X t) * inv t)`
    SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    CONV_TAC SYM_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
   EXISTS_TAC `\t:real. abs(b - a:real)` THEN REPEAT CONJ_TAC THENL
   [(* Measurability of integrand on [-TT,TT] *)
    MATCH_MP_TAC REAL_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real)` THEN
    REWRITE_TAC[SUBSET_UNIV; REAL_LEBESGUE_MEASURABLE_INTERVAL] THEN
    MATCH_MP_TAC REAL_MEASURABLE_ON_MUL THEN CONJ_TAC THENL
    [(* Numerator: continuous on (:real), hence measurable *)
     MATCH_MP_TAC REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET THEN
     REWRITE_TAC[REAL_CLOSED_UNIV] THEN
     MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
      [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN CONJ_TAC THEN
       GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
       MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THEN
       TRY(MATCH_MP_TAC REAL_CONTINUOUS_ON_RMUL THEN
         REWRITE_TAC[REAL_CONTINUOUS_ON_ID]) THEN
       REWRITE_TAC[REAL_CONTINUOUS_ON_SIN];
       REWRITE_TAC[ETA_AX] THEN
       MATCH_MP_TAC CHAR_FN_RE_CONTINUOUS THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
      [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN CONJ_TAC THEN
       GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
       MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THEN
       TRY(MATCH_MP_TAC REAL_CONTINUOUS_ON_RMUL THEN
         REWRITE_TAC[REAL_CONTINUOUS_ON_ID]) THEN
       REWRITE_TAC[REAL_CONTINUOUS_ON_COS];
       REWRITE_TAC[ETA_AX] THEN
       MATCH_MP_TAC CHAR_FN_IM_CONTINUOUS THEN ASM_REWRITE_TAC[]]];
     (* inv measurable on (:real) *)
     SUBGOAL_THEN `inv:real->real = (\x. inv x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
     MATCH_MP_TAC REAL_MEASURABLE_ON_INV THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET THEN
      REWRITE_TAC[REAL_CLOSED_UNIV; REAL_CONTINUOUS_ON_ID];
      REWRITE_TAC[SET_RULE `{x | x = &0} = {&0}`; REAL_NEGLIGIBLE_SING]]];
    (* Bounding function integrable *)
    REWRITE_TAC[REAL_INTEGRABLE_CONST];
    (* Pointwise bound: |integrand(t)| <= |b-a| *)
    X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `((sin(t * b) - sin(t * a)) * char_fn_re (p:A prob_space) X t -
      (cos(t * b) - cos(t * a)) * char_fn_im p X t) * inv t =
      expectation p (\x:A. (h:real->real->real) t (X x))` SUBST1_TAC THENL
    [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `--a <= x /\ x <= a ==> abs x <= a`) THEN
    CONJ_TAC THENL
    [SUBGOAL_THEN `--abs(b - a:real) =
       expectation (p:A prob_space) (\x:A. --abs(b - a))` SUBST1_TAC THENL
     [REWRITE_TAC[EXPECTATION_CONST]; ALL_TAC] THEN
     MATCH_MP_TAC EXPECTATION_MONO THEN ASM_REWRITE_TAC[INTEGRABLE_CONST] THEN
     GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "h" THEN BETA_TAC THEN
     MP_TAC(SPECL [`t:real`; `a:real`; `b:real`; `(X:A->real) x`]
       INVERSION_KERNEL_BOUNDED) THEN REAL_ARITH_TAC;
     SUBGOAL_THEN `abs(b - a:real) =
       expectation (p:A prob_space) (\x:A. abs(b - a))` SUBST1_TAC THENL
     [REWRITE_TAC[EXPECTATION_CONST]; ALL_TAC] THEN
     MATCH_MP_TAC EXPECTATION_MONO THEN ASM_REWRITE_TAC[INTEGRABLE_CONST] THEN
     GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "h" THEN BETA_TAC THEN
     MP_TAC(SPECL [`t:real`; `a:real`; `b:real`; `(X:A->real) x`]
       INVERSION_KERNEL_BOUNDED) THEN REAL_ARITH_TAC]];
   ALL_TAC] THEN
  (* Derive integrability on [0,TT] from [-TT,TT] via subinterval *)
  SUBGOAL_THEN `(\t. expectation (p:A prob_space)
    (\x:A. (h:real->real->real) t (X x)))
    real_integrable_on real_interval[&0,TT]` ASSUME_TAC THENL
  [SUBGOAL_THEN `(\t. expectation (p:A prob_space)
      (\x:A. (h:real->real->real) t (X x))) =
    (\t. ((sin(t * b) - sin(t * a)) * char_fn_re p X t -
          (cos(t * b) - cos(t * a)) * char_fn_im p X t) * inv t)`
    SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    CONV_TAC SYM_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   MATCH_MP_TAC REAL_INTEGRABLE_ON_SUBINTERVAL THEN
   EXISTS_TAC `real_interval[--TT,TT]` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(\t. expectation (p:A prob_space)
      (\x:A. (h:real->real->real) t (X x))) =
      (\t. ((sin(t * b) - sin(t * a)) * char_fn_re p X t -
          (cos(t * b) - cos(t * a)) * char_fn_im p X t) * inv t)`
      (fun th -> REWRITE_TAC[GSYM th]) THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
     CONV_TAC SYM_CONV THEN ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[]];
    REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* Establish continuity of E[h(t,X)] at t > 0 *)
  SUBGOAL_THEN `!t:real. t IN real_interval[&0,TT] /\ &0 < t ==>
    (\s. expectation (p:A prob_space)
      (\x:A. (h:real->real->real) s (X x)))
    real_continuous (atreal t within real_interval[&0,TT])` ASSUME_TAC THENL
  [X_GEN_TAC `t0:real` THEN STRIP_TAC THEN
   SUBGOAL_THEN `(\s. expectation (p:A prob_space)
     (\x:A. (h:real->real->real) s (X x))) =
     (\s. ((sin(s * b) - sin(s * a)) * char_fn_re p X s -
           (cos(s * b) - cos(s * a)) * char_fn_im p X s) * inv s)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    CONV_TAC SYM_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN CONJ_TAC THENL
      [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
       MATCH_MP_TAC REAL_CONTINUOUS_WITHINREAL_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN
        REWRITE_TAC[REAL_CONTINUOUS_CONST; REAL_CONTINUOUS_WITHIN_ID];
        REWRITE_TAC[REAL_CONTINUOUS_WITHIN_SIN]];
       GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
       MATCH_MP_TAC REAL_CONTINUOUS_WITHINREAL_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN
        REWRITE_TAC[REAL_CONTINUOUS_CONST; REAL_CONTINUOUS_WITHIN_ID];
        REWRITE_TAC[REAL_CONTINUOUS_WITHIN_SIN]]];
      REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      SUBGOAL_THEN `char_fn_re (p:A prob_space) X real_continuous_on (:real)`
        MP_TAC THENL
      [MATCH_MP_TAC CHAR_FN_RE_CONTINUOUS THEN ASM_REWRITE_TAC[];
       SIMP_TAC[REAL_CONTINUOUS_ON_EQ_REAL_CONTINUOUS_AT;
                REAL_OPEN_UNIV; IN_UNIV]]];
     MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN CONJ_TAC THENL
      [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
       MATCH_MP_TAC REAL_CONTINUOUS_WITHINREAL_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN
        REWRITE_TAC[REAL_CONTINUOUS_CONST; REAL_CONTINUOUS_WITHIN_ID];
        REWRITE_TAC[REAL_CONTINUOUS_WITHIN_COS]];
       GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
       MATCH_MP_TAC REAL_CONTINUOUS_WITHINREAL_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN
        REWRITE_TAC[REAL_CONTINUOUS_CONST; REAL_CONTINUOUS_WITHIN_ID];
        REWRITE_TAC[REAL_CONTINUOUS_WITHIN_COS]]];
      REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      SUBGOAL_THEN `char_fn_im (p:A prob_space) X real_continuous_on (:real)`
        MP_TAC THENL
      [MATCH_MP_TAC CHAR_FN_IM_CONTINUOUS THEN ASM_REWRITE_TAC[];
       SIMP_TAC[REAL_CONTINUOUS_ON_EQ_REAL_CONTINUOUS_AT;
                REAL_OPEN_UNIV; IN_UNIV]]]];
    SUBGOAL_THEN `inv = (\s:real. inv s)` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_INV_WITHINREAL THEN
    REWRITE_TAC[REAL_CONTINUOUS_WITHIN_ID] THEN ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* Step 4: Use evenness to convert [-TT,TT] to 2*[0,TT] *)
  SUBGOAL_THEN
    `real_integral (real_interval [--TT, TT])
      (\t. expectation (p:A prob_space) (\x:A. (h:real->real->real) t (X x))) =
     &2 * real_integral (real_interval [&0, TT])
      (\t. expectation p (\x. h t (X x)))` SUBST1_TAC THENL
  [MATCH_MP_TAC REAL_INTEGRAL_EVEN_SYMMETRIC THEN
   CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN EXPAND_TAC "h" THEN BETA_TAC THEN
    SUBGOAL_THEN `!v:real. (sin(--t * (b - v)) - sin(--t * (a - v))) * inv(--t) =
      (sin(t * (b - v)) - sin(t * (a - v))) * inv t` ASSUME_TAC THENL
    [GEN_TAC THEN MATCH_ACCEPT_TAC INVERSION_SINC_EVEN; ALL_TAC] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* Step 5: Simplify inv(2*pi) * 2 = inv(pi) *)
  SUBGOAL_THEN `inv(&2 * pi) * (&2 * real_integral (real_interval [&0,TT])
    (\t. expectation (p:A prob_space) (\x:A. (h:real->real->real) t (X x)))) =
    inv(pi) * real_integral (real_interval [&0,TT])
    (\t. expectation p (\x. h t (X x)))` SUBST1_TAC THENL
  [SUBGOAL_THEN `~(pi = &0)` ASSUME_TAC THENL
   [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_INV_MUL] THEN CONV_TAC REAL_FIELD;
   ALL_TAC] THEN
  (* Step 6: Pull inv(pi) out of expectation on RHS *)
  SUBGOAL_THEN
    `expectation (p:A prob_space)
      (\x. inv pi * real_integral (real_interval [&0,TT])
        (\t. (sin(t * (b - X x)) - sin(t * (a - X x))) * inv t)) =
     inv(pi) * expectation p
      (\x. real_integral (real_interval [&0,TT])
        (\t. (sin(t * (b - X x)) - sin(t * (a - X x))) * inv t))`
    SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_CMUL THEN
   MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
   EXISTS_TAC `abs(b - a) * TT` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(\x:A. real_integral (real_interval[&0,TT])
      (\t. (sin(t * (b - (X:A->real) x)) - sin(t * (a - X x))) * inv t)) =
      (\x. (\v. real_integral (real_interval[&0,TT])
        (\t. (sin(t * (b - v)) - sin(t * (a - v))) * inv t)) (X x))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
    MATCH_MP_TAC RANDOM_VARIABLE_COMP_CONTINUOUS THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[REAL_CONTINUOUS_ON_EQ_REAL_CONTINUOUS_AT;
             REAL_OPEN_UNIV; IN_UNIV] THEN
    X_GEN_TAC `v:real` THEN
    REWRITE_TAC[REAL_CONTINUOUS_ATREAL; REALLIM_ATREAL] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    EXISTS_TAC `e / (&2 * TT)` THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `w:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `(&2 * abs(v - w)) * TT` THEN CONJ_TAC THENL
    [MATCH_MP_TAC(REAL_ARITH `abs(x - y) <= a ==> abs(y - x) <= a`) THEN
     SUBGOAL_THEN
       `real_integral (real_interval[&0,TT])
          (\t. (sin(t * (b - v)) - sin(t * (a - v))) * inv t) -
        real_integral (real_interval[&0,TT])
          (\t. (sin(t * (b - w)) - sin(t * (a - w))) * inv t) =
        real_integral (real_interval[&0,TT])
          (\t. ((sin(t * (b - v)) - sin(t * (a - v))) * inv t) -
               ((sin(t * (b - w)) - sin(t * (a - w))) * inv t))`
       SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INTEGRAL_SUB THEN
      CONJ_TAC THEN MATCH_MP_TAC SINC_SCALED_DIFF_INTEGRABLE THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     MP_TAC(ISPECL
       [`\t:real. ((sin(t * (b - v)) - sin(t * (a - v))) * inv t) -
                 ((sin(t * (b - w)) - sin(t * (a - w))) * inv t)`;
        `&0`; `TT:real`;
        `real_integral (real_interval[&0,TT])
          (\t:real. ((sin(t * (b - v)) - sin(t * (a - v))) * inv t) -
               ((sin(t * (b - w)) - sin(t * (a - w))) * inv t))`;
        `&2 * abs(v - w:real)`] HAS_REAL_INTEGRAL_BOUND) THEN
     REWRITE_TAC[REAL_SUB_RZERO] THEN
     DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
      [REAL_ARITH_TAC; REWRITE_TAC[REAL_ABS_POS]];
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
      MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN
      CONJ_TAC THEN MATCH_MP_TAC SINC_SCALED_DIFF_INTEGRABLE THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      DISCH_TAC THEN
      REWRITE_TAC[REAL_ARITH `!a b c d e:real.
        (a - b) * c - (d - e) * c = ((a - d) - (b - e)) * c`] THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV] THEN
      ASM_CASES_TAC `t = &0` THENL
      [ASM_REWRITE_TAC[REAL_ABS_NUM; REAL_INV_0; REAL_MUL_RZERO] THEN
       REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(abs(t * (b - v) - t * (b - w)) +
                   abs(t * (a - v) - t * (a - w))) * inv(abs t)` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_RMUL THEN
       REWRITE_TAC[REAL_LE_INV_EQ; REAL_ABS_POS] THEN
       MATCH_MP_TAC(REAL_ARITH
         `abs(a) <= x /\ abs(b) <= y ==>
          abs(a - b) <= x + y`) THEN
       REWRITE_TAC[SIN_LIPSCHITZ];
       SUBGOAL_THEN `t * (b - v) - t * (b - w) = t * (w - v:real)`
         SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
       SUBGOAL_THEN `t * (a - v) - t * (a - w) = t * (w - v:real)`
         SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
       REWRITE_TAC[REAL_ABS_MUL] THEN
       SUBGOAL_THEN `(abs t * abs(w - v) + abs t * abs(w - v)) * inv(abs t) =
         &2 * abs(v - w:real)` SUBST1_TAC THENL
       [UNDISCH_TAC `~(t = &0)` THEN
        REWRITE_TAC[REAL_ARITH `abs(w - v:real) = abs(v - w)`] THEN
        CONV_TAC REAL_FIELD;
        REWRITE_TAC[REAL_LE_REFL]]]];
     MATCH_MP_TAC REAL_LTE_TRANS THEN
     EXISTS_TAC `(&2 * (e / (&2 * TT))) * TT` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
      REWRITE_TAC[REAL_ABS_SUB] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      UNDISCH_TAC `&0 < TT` THEN CONV_TAC REAL_FIELD]];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL
      [`\t:real. (sin(t * (b - (X:A->real) x)) - sin(t * (a - X x))) * inv t`;
       `&0`; `TT:real`;
       `real_integral (real_interval[&0,TT])
         (\t. (sin(t * (b - (X:A->real) x)) - sin(t * (a - X x))) * inv t)`;
       `abs(b - a:real)`] HAS_REAL_INTEGRAL_BOUND) THEN
    REWRITE_TAC[REAL_ABS_POS; REAL_SUB_RZERO] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
     MATCH_MP_TAC SINC_SCALED_DIFF_INTEGRABLE THEN ASM_REAL_ARITH_TAC;
     X_GEN_TAC `t:real` THEN DISCH_TAC THEN
     REWRITE_TAC[INVERSION_KERNEL_BOUNDED]]];
   ALL_TAC] THEN
  (* Step 7: The Fubini exchange: integral E[h(t,X)] = E[integral h(t,X)] *)
  AP_TERM_TAC THEN
  SUBGOAL_THEN
    `real_integral (real_interval [&0,TT])
      (\t. expectation (p:A prob_space) (\x:A. (h:real->real->real) t (X x))) =
     expectation p (\x. real_integral (real_interval [&0,TT])
      (\t. h t (X x)))` SUBST1_TAC THENL
  [MATCH_MP_TAC INTEGRAL_EXPECTATION_EXCHANGE THEN
   EXISTS_TAC `abs(b - a:real)` THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `a < b` THEN REAL_ARITH_TAC;
    (* !t v. abs(h t v) <= |b-a| *)
    REPEAT GEN_TAC THEN EXPAND_TAC "h" THEN BETA_TAC THEN
    REWRITE_TAC[INVERSION_KERNEL_BOUNDED];
    (* !v. (\t. h t v) integrable on [0,TT] *)
    GEN_TAC THEN EXPAND_TAC "h" THEN BETA_TAC THEN
    MATCH_MP_TAC SINC_SCALED_DIFF_INTEGRABLE THEN ASM_REAL_ARITH_TAC;
    (* !v t. 0 < t /\ t <= TT ==> h continuous in t at (t,v) *)
    REPEAT STRIP_TAC THEN EXPAND_TAC "h" THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_WITHINREAL_COMPOSE THEN CONJ_TAC THENL
      [MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN
       REWRITE_TAC[REAL_CONTINUOUS_CONST; REAL_CONTINUOUS_WITHIN_ID];
       REWRITE_TAC[REAL_CONTINUOUS_WITHIN_SIN]];
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_WITHINREAL_COMPOSE THEN CONJ_TAC THENL
      [MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN
       REWRITE_TAC[REAL_CONTINUOUS_CONST; REAL_CONTINUOUS_WITHIN_ID];
       REWRITE_TAC[REAL_CONTINUOUS_WITHIN_SIN]]];
    SUBGOAL_THEN `inv = (\s:real. inv s)` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_INV_WITHINREAL THEN
    REWRITE_TAC[REAL_CONTINUOUS_WITHIN_ID] THEN ASM_REAL_ARITH_TAC]];
   ALL_TAC] THEN
  (* Final: show both expectations have the same integrand *)
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `x:A` THEN EXPAND_TAC "h" THEN REWRITE_TAC[]);;


(* Levy inversion formula: recovers F(b) - F(a) from the characteristic
   function via an integral. Requires continuity of F at a and b.
   Proof: Use REALLIM_AT_POSINFINITY_FROM_SUBSEQUENCES to reduce to
   sequential case, then INVERSION_FUBINI + bounded convergence. *)
let LEVY_INVERSION = prove
 (`!p:A prob_space (X:A->real) a b.
    random_variable p X /\
    a < b /\
    (distribution_fn p X) real_continuous (atreal a) /\
    (distribution_fn p X) real_continuous (atreal b)
    ==> ((\TT. inv(&2 * pi) *
              real_integral (real_interval [--TT, TT])
                (\t. ((sin(t * b) - sin(t * a)) * char_fn_re p X t -
                      (cos(t * b) - cos(t * a)) * char_fn_im p X t) * inv t))
         ---> (distribution_fn p X b - distribution_fn p X a)) at_posinfinity`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REALLIM_AT_POSINFINITY_FROM_SUBSEQUENCES THEN
  X_GEN_TAC `s:num->real` THEN DISCH_TAC THEN BETA_TAC THEN
  ABBREV_TAC `g = \TT:real. \v:real. inv(pi) *
    real_integral (real_interval[&0,TT])
      (\t. (sin(t * (b - v)) - sin(t * (a - v))) * inv t)` THEN
  SUBGOAL_THEN `!TT. &0 < TT ==>
    inv(&2 * pi) * real_integral (real_interval [--TT, TT])
      (\t. ((sin(t * b) - sin(t * a)) * char_fn_re (p:A prob_space) X t -
            (cos(t * b) - cos(t * a)) * char_fn_im p X t) * inv t) =
    expectation p (\x. (g:real->real->real) TT (X x))` ASSUME_TAC THENL
  [X_GEN_TAC `TT:real` THEN DISCH_TAC THEN
   EXPAND_TAC "g" THEN BETA_TAC THEN
   MATCH_MP_TAC INVERSION_FUBINI THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\n:num. expectation (p:A prob_space)
    (\x. (g:real->real->real) (s n) (X x))` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
   X_GEN_TAC `n:num` THEN DISCH_TAC THEN
   CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&n:real` THEN
   CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[real_ge]];
   ALL_TAC] THEN
  SUBGOAL_THEN `distribution_fn (p:A prob_space) X b - distribution_fn p X a =
    expectation p (\x:A. if a < X x /\ X x < b then &1
      else if X x < a \/ b < X x then &0 else inv(&2))` SUBST1_TAC THENL
  [(* Prove F(b) - F(a) = E[f(X)]. Strategy: show both sides equal P(a < X < b) *)
   SUBGOAL_THEN `prob (p:A prob_space) {x | x IN prob_carrier p /\
     (X:A->real) x = a} = &0` ASSUME_TAC THENL
   [MATCH_MP_TAC DISTRIBUTION_FN_CONTINUOUS_PROB_ZERO THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `prob (p:A prob_space) {x | x IN prob_carrier p /\
     (X:A->real) x = b} = &0` ASSUME_TAC THENL
   [MATCH_MP_TAC DISTRIBUTION_FN_CONTINUOUS_PROB_ZERO THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ (X:A->real) x = a}
     IN prob_events p` ASSUME_TAC THENL
   [SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ (X:A->real) x = a} =
     {x | x IN prob_carrier p /\ X x <= a} DIFF
     {x | x IN prob_carrier p /\ X x < a}` SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN GEN_TAC THEN
     ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
     REAL_ARITH_TAC;
     MATCH_MP_TAC PROB_DIFF_IN_EVENTS THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [random_variable]) THEN
      DISCH_THEN(MP_TAC o SPEC `a:real`) THEN REWRITE_TAC[];
      MATCH_MP_TAC RV_PREIMAGE_LT THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ (X:A->real) x = b}
     IN prob_events p` ASSUME_TAC THENL
   [SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ (X:A->real) x = b} =
     {x | x IN prob_carrier p /\ X x <= b} DIFF
     {x | x IN prob_carrier p /\ X x < b}` SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN GEN_TAC THEN
     ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
     REAL_ARITH_TAC;
     MATCH_MP_TAC PROB_DIFF_IN_EVENTS THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [random_variable]) THEN
      DISCH_THEN(MP_TAC o SPEC `b:real`) THEN REWRITE_TAC[];
      MATCH_MP_TAC RV_PREIMAGE_LT THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ a < (X:A->real) x /\ X x < b}
     IN prob_events p` ASSUME_TAC THENL
   [SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ a < (X:A->real) x /\ X x < b} =
     {x | x IN prob_carrier p /\ X x < b} DIFF
     {x | x IN prob_carrier p /\ X x <= a}` SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN GEN_TAC THEN
     ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
     REAL_ARITH_TAC;
     MATCH_MP_TAC PROB_DIFF_IN_EVENTS THEN CONJ_TAC THENL
     [MATCH_MP_TAC RV_PREIMAGE_LT THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [random_variable]) THEN
      DISCH_THEN(MP_TAC o SPEC `a:real`) THEN REWRITE_TAC[]]];
    ALL_TAC] THEN
   ABBREV_TAC `C_bdry = {x:A | x IN prob_carrier p /\ (X:A->real) x = a}
     UNION {x | x IN prob_carrier p /\ X x = b}` THEN
   SUBGOAL_THEN `C_bdry:A->bool IN prob_events p` ASSUME_TAC THENL
   [EXPAND_TAC "C_bdry" THEN MATCH_MP_TAC PROB_UNION_IN_EVENTS THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `prob (p:A prob_space) C_bdry = &0` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
       `prob (p:A prob_space) {x | x IN prob_carrier p /\ (X:A->real) x = a} +
        prob p {x | x IN prob_carrier p /\ X x = b}` THEN
     CONJ_TAC THENL
     [EXPAND_TAC "C_bdry" THEN MATCH_MP_TAC PROB_SUBADDITIVE THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[REAL_ADD_LID; REAL_LE_REFL]]];
    ALL_TAC] THEN
   SUBGOAL_THEN `distribution_fn (p:A prob_space) X b - distribution_fn p X a =
     prob p {x | x IN prob_carrier p /\ a < (X:A->real) x /\ X x < b}`
     SUBST1_TAC THENL
   [(* LHS: F(b) - F(a) = P(a < X < b) *)
    REWRITE_TAC[distribution_fn] THEN
    SUBGOAL_THEN `prob (p:A prob_space)
      {x | x IN prob_carrier p /\ (X:A->real) x <= b} -
      prob p {x | x IN prob_carrier p /\ X x <= a} =
      prob p ({x | x IN prob_carrier p /\ X x <= b} DIFF
              {x | x IN prob_carrier p /\ X x <= a})` SUBST1_TAC THENL
    [CONV_TAC SYM_CONV THEN MATCH_MP_TAC PROB_DIFF_SUBSET THEN
     CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [random_variable]) THEN
      DISCH_THEN(MP_TAC o SPEC `a:real`) THEN REWRITE_TAC[]; ALL_TAC] THEN
     CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [random_variable]) THEN
      DISCH_THEN(MP_TAC o SPEC `b:real`) THEN REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(X:A->real) x <= a` THEN
      UNDISCH_TAC `(a:real) < b` THEN REAL_ARITH_TAC]; ALL_TAC] THEN
    SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ (X:A->real) x <= b} DIFF
      {x | x IN prob_carrier p /\ X x <= a} =
      {x | x IN prob_carrier p /\ a < X x /\ X x < b} UNION
      {x | x IN prob_carrier p /\ X x = b}` SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNION; IN_ELIM_THM] THEN GEN_TAC THEN
     ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `(a:real) < b` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`p:A prob_space`;
      `{x:A | x IN prob_carrier p /\ a < (X:A->real) x /\ X x < b}`;
      `{x:A | x IN prob_carrier p /\ (X:A->real) x = b}`] PROB_ADDITIVE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
    [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
     GEN_TAC THEN ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN
     ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
     DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_ADD_RID]];
    (* RHS: E[f(X)] = P(a < X < b).
       Prove inside a single SUBGOAL_THEN to avoid SUBST1_TAC alpha issues *)
    ABBREV_TAC `A_open = {x:A | x IN prob_carrier p /\ a < (X:A->real) x /\
      X x < b}` THEN
    CONV_TAC SYM_CONV THEN
    (* Goal is now: E[f] = prob p A_open *)
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `expectation (p:A prob_space) (indicator_fn A_open) +
      inv(&2) * expectation p (indicator_fn C_bdry)` THEN
    CONJ_TAC THENL
    [SUBGOAL_THEN `integrable (p:A prob_space) (indicator_fn A_open)`
       ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_INDICATOR THEN
      EXPAND_TAC "A_open" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     SUBGOAL_THEN `integrable (p:A prob_space)
       (indicator_fn (C_bdry:A->bool))` ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     SUBGOAL_THEN `integrable (p:A prob_space)
       (\x:A. inv(&2) * indicator_fn (C_bdry:A->bool) x)` ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
     SUBGOAL_THEN `inv(&2) * expectation (p:A prob_space)
       (indicator_fn (C_bdry:A->bool)) =
       expectation p (\x:A. inv(&2) * indicator_fn C_bdry x)`
       ASSUME_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXPECTATION_CMUL THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
     (* Branch 1: E[f] = E[ind A_open] + inv(2) * E[ind C_bdry] *)
     ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN `integrable (p:A prob_space)
       (\x:A. indicator_fn A_open x + inv(&2) * indicator_fn C_bdry x)`
       ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
     MATCH_MP_TAC EQ_TRANS THEN
     EXISTS_TAC `expectation (p:A prob_space)
       (\x:A. indicator_fn A_open x +
              inv(&2) * indicator_fn (C_bdry:A->bool) x)` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC EXPECTATION_EXT THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
      EXPAND_TAC "A_open" THEN EXPAND_TAC "C_bdry" THEN
      REWRITE_TAC[IN_ELIM_THM; IN_UNION] THEN
      ASM_CASES_TAC `a < (X:A->real) x /\ X x < b` THENL
      [ASM_REWRITE_TAC[] THEN
       SUBGOAL_THEN `~((X:A->real) x = a) /\ ~(X x = b)` ASSUME_TAC THENL
       [POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
       ASM_CASES_TAC `(X:A->real) x < a \/ b < X x` THENL
       [ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `~(a < (X:A->real) x /\ X x < b) /\
          ~((X:A->real) x = a) /\ ~(X x = b)` ASSUME_TAC THENL
        [POP_ASSUM MP_TAC THEN UNDISCH_TAC `(a:real) < b` THEN REAL_ARITH_TAC;
         ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `(X:A->real) x = a \/ X x = b` ASSUME_TAC THENL
        [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
         ASM_REWRITE_TAC[] THEN
         SUBGOAL_THEN `~(a < (X:A->real) x /\ X x < b)` ASSUME_TAC THENL
         [POP_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
          ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]]]];
      MP_TAC(ISPECL [`p:A prob_space`; `indicator_fn (A_open:A->bool)`;
        `\x:A. inv(&2) * indicator_fn (C_bdry:A->bool) x`]
        EXPECTATION_ADD) THEN
      ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN(fun th -> REWRITE_TAC[th])];
     (* Branch 2: E[ind A_open] + inv(2) * E[ind C_bdry] = prob A_open *)
     SUBGOAL_THEN `expectation (p:A prob_space) (indicator_fn C_bdry) = &0`
       SUBST1_TAC THENL
     [SUBGOAL_THEN `expectation (p:A prob_space) (indicator_fn C_bdry) =
        prob p C_bdry` SUBST1_TAC THENL
      [MATCH_MP_TAC EXPECTATION_INDICATOR THEN ASM_REWRITE_TAC[];
       ASM_REWRITE_TAC[]]; ALL_TAC] THEN
     REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN
     MATCH_MP_TAC EXPECTATION_INDICATOR THEN
     EXPAND_TAC "A_open" THEN ASM_REWRITE_TAC[]]];
   ALL_TAC] THEN
  MP_TAC(ISPECL
    [`p:A prob_space`;
     `\n:num. \x:A. (g:real->real->real) ((s:num->real) n) ((X:A->real) x)`;
     `\x:A. if a < (X:A->real) x /\ X x < b then &1
       else if X x < a \/ b < X x then &0 else inv(&2)`;
     `&1 + &8 * inv(pi)`]
    BOUNDED_CONVERGENCE_EXPECTATION_GEN) THEN
  BETA_TAC THEN ANTS_TAC THENL
  [REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN EXPAND_TAC "g" THEN BETA_TAC THEN
    MATCH_MP_TAC INVERSION_KERNEL_RV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&n:real` THEN
    CONJ_TAC THENL [REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[real_ge];
    X_GEN_TAC `n:num` THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    EXPAND_TAC "g" THEN BETA_TAC THEN
    SUBGOAL_THEN `(s:num->real) n = &0 \/ &0 < s n` DISJ_CASES_TAC THENL
    [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> x = &0 \/ &0 < x`) THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&n:real` THEN
     CONJ_TAC THENL [REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[real_ge];
     ASM_REWRITE_TAC[REAL_INTEGRAL_REFL; REAL_MUL_RZERO; REAL_ABS_0] THEN
     MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
      [REAL_ARITH_TAC;
       MATCH_MP_TAC REAL_LE_INV THEN MP_TAC PI_POS THEN REAL_ARITH_TAC]];
     MATCH_MP_TAC INVERSION_KERNEL_UNIFORM_BOUND THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    EXPAND_TAC "g" THEN BETA_TAC THEN
    ASM_CASES_TAC `a < (X:A->real) x /\ X x < b` THENL
    [ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC(BETA_RULE(ISPECL
       [`\TT:real. inv(pi) * real_integral (real_interval[&0,TT])
          (\t. (sin(t * ((b:real) - (X:A->real) x)) -
                sin(t * ((a:real) - X x))) * inv t)`;
        `&1`; `s:num->real`]
       REALLIM_AT_POSINFINITY_IMP_SEQUENTIALLY)) THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC INVERSION_KERNEL_CONVERGES_INSIDE THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
     ALL_TAC] THEN
    ASM_CASES_TAC `(X:A->real) x < a \/ b < X x` THENL
    [SUBGOAL_THEN `~(a < (X:A->real) x /\ X x < b)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
     MATCH_MP_TAC(BETA_RULE(ISPECL
       [`\TT:real. inv(pi) * real_integral (real_interval[&0,TT])
          (\t. (sin(t * ((b:real) - (X:A->real) x)) -
                sin(t * ((a:real) - X x))) * inv t)`;
        `&0`; `s:num->real`]
       REALLIM_AT_POSINFINITY_IMP_SEQUENTIALLY)) THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC INVERSION_KERNEL_CONVERGES_OUTSIDE THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
     ALL_TAC] THEN
    SUBGOAL_THEN `(X:A->real) x = a \/ X x = b` ASSUME_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(a < (X:A->real) x /\ X x < b)` ASSUME_TAC THENL
    [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    SUBGOAL_THEN `~((X:A->real) x < a \/ b < X x)` ASSUME_TAC THENL
    [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC(BETA_RULE(ISPECL
       [`\TT:real. inv(pi) * real_integral (real_interval[&0,TT])
          (\t. (sin(t * ((b:real) - a)) -
                sin(t * (a - a))) * inv t)`;
        `inv(&2)`; `s:num->real`]
       REALLIM_AT_POSINFINITY_IMP_SEQUENTIALLY)) THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC INVERSION_KERNEL_CONVERGES_AT_A THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
     ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC(BETA_RULE(ISPECL
       [`\TT:real. inv(pi) * real_integral (real_interval[&0,TT])
          (\t. (sin(t * ((b:real) - b)) -
                sin(t * (a - b))) * inv t)`;
        `inv(&2)`; `s:num->real`]
       REALLIM_AT_POSINFINITY_IMP_SEQUENTIALLY)) THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC INVERSION_KERNEL_CONVERGES_AT_B THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]]]];
   ALL_TAC] THEN
  MESON_TAC[]);;

(* ================================================================== *)
(* LINDEBERG-FELLER CLT                                               *)
(* ================================================================== *)

(* L1: Telescoping product inequality *)
let PRODUCT_DIFF_SUM_BOUND = prove
 (`!n (a:num->real) (b:num->real).
    (!i. i <= n ==> abs(a i) <= &1) /\
    (!i. i <= n ==> abs(b i) <= &1)
    ==> abs(product(0..n) a - product(0..n) b)
        <= sum(0..n) (\i. abs(a i - b i))`,
  INDUCT_TAC THENL
  [REWRITE_TAC[PRODUCT_CLAUSES_NUMSEG; SUM_CLAUSES_NUMSEG; LE_0; LE; ARITH] THEN
   BETA_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SIMP_TAC[PRODUCT_CLAUSES_NUMSEG; SUM_CLAUSES_NUMSEG;
           ARITH_RULE `0 <= SUC n`] THEN BETA_TAC THEN
  ABBREV_TAC `Pa = product(0..n) (a:num->real)` THEN
  ABBREV_TAC `Pb = product(0..n) (b:num->real)` THEN
  SUBGOAL_THEN `Pa * (a:num->real)(SUC n) - Pb * b(SUC n) =
    a(SUC n) * (Pa - Pb) + (a(SUC n) - b(SUC n)) * Pb`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs((a:num->real)(SUC n)) <= &1` ASSUME_TAC THENL
  [FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(Pa - Pb) <=
    sum(0..n) (\i. abs((a:num->real) i - b i))` ASSUME_TAC THENL
  [EXPAND_TAC "Pa" THEN EXPAND_TAC "Pb" THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_MESON_TAC[ARITH_RULE `i <= n ==> i <= SUC n`];
   ALL_TAC] THEN
  SUBGOAL_THEN `abs Pb <= &1` ASSUME_TAC THENL
  [EXPAND_TAC "Pb" THEN
   MP_TAC(ISPECL [`b:num->real`; `0..n`] PRODUCT_ABS) THEN
   REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `product(0..n) (\i:num. &1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ABS_POS] THEN
    UNDISCH_TAC `!i. i <= SUC n ==> abs ((b:num->real) i) <= &1` THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_ARITH_TAC;
    REWRITE_TAC[PRODUCT_CONST_NUMSEG; REAL_POW_ONE; REAL_LE_REFL]];
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs((a:num->real)(SUC n)) * abs(Pa - Pb) +
    abs(a(SUC n) - b(SUC n)) * abs Pb` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[GSYM REAL_ABS_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&1 * sum(0..n) (\i. abs((a:num->real) i - b i)) +
    abs(a(SUC n) - b(SUC n)) * &1` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS; REAL_LE_REFL] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN GEN_TAC THEN STRIP_TAC THEN
    BETA_TAC THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]];
   REAL_ARITH_TAC]);;

(* L2: Upper bound: product(1-c_i) <= exp(-sum c_i) *)
let PRODUCT_1_MINUS_LE_EXP = prove
 (`!n (c:num->real). (!i. i <= n ==> &0 <= c i /\ c i <= &1)
    ==> product(0..n) (\i. &1 - c i) <= exp(--(sum(0..n) c))`,
  INDUCT_TAC THENL
  [GEN_TAC THEN STRIP_TAC THEN
   REWRITE_TAC[PRODUCT_CLAUSES_NUMSEG; SUM_CLAUSES_NUMSEG; LE_0; LE; ARITH] THEN
   BETA_TAC THEN
   MP_TAC(SPEC `--((c:num->real) 0)` REAL_EXP_LE_X) THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  GEN_TAC THEN STRIP_TAC THEN
  SIMP_TAC[PRODUCT_CLAUSES_NUMSEG; SUM_CLAUSES_NUMSEG;
           ARITH_RULE `0 <= SUC n`] THEN BETA_TAC THEN
  REWRITE_TAC[REAL_NEG_ADD; REAL_EXP_ADD] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC PRODUCT_POS_LE_NUMSEG THEN
   GEN_TAC THEN STRIP_TAC THEN BETA_TAC THEN
   FIRST_ASSUM(MP_TAC o SPEC `x:num`) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; REAL_ARITH_TAC];
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_MESON_TAC[ARITH_RULE `i <= n ==> i <= SUC n`];
   FIRST_ASSUM(MP_TAC o SPEC `SUC n`) THEN
   REWRITE_TAC[LE_REFL] THEN REAL_ARITH_TAC;
   MP_TAC(SPEC `--((c:num->real)(SUC n))` REAL_EXP_LE_X) THEN
   REAL_ARITH_TAC]);;

(* Helper: exp(-c/(1-delta)) <= 1-c when 0 <= c <= delta < 1 *)
(* From LOG_LOWER_BOUND: log(1-c) >= 1-1/(1-c) = -c/(1-c) >= -c/(1-delta) *)
let EXP_NEG_DIV_LE_1_MINUS = prove
 (`!c delta. &0 <= c /\ c <= delta /\ delta < &1
    ==> exp(--(c / (&1 - delta))) <= &1 - c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 - c` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - delta` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(log(&1 - c))` THEN CONJ_TAC THENL
  [REWRITE_TAC[REAL_EXP_MONO_LE] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `&1 - inv(&1 - c)` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `&1 - inv(&1 - c) = --(c / (&1 - c))`
      SUBST1_TAC THENL
    [SUBGOAL_THEN `~(&1 - c = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]; ALL_TAC] THEN
    REWRITE_TAC[REAL_LE_NEG2; real_div] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC LOG_LOWER_BOUND THEN ASM_REWRITE_TAC[]];
   ASM_SIMP_TAC[EXP_LOG; REAL_LE_REFL]]);;

(* L3: Lower bound: exp(-sum c_i/(1-delta)) <= product(1-c_i) *)
let EXP_LE_PRODUCT_1_MINUS = prove
 (`!n (c:num->real) delta.
    (!i. i <= n ==> &0 <= c i /\ c i <= delta) /\ delta < &1
    ==> exp(--(sum(0..n) c / (&1 - delta)))
        <= product(0..n) (\i. &1 - c i)`,
  INDUCT_TAC THENL
  [REPEAT GEN_TAC THEN STRIP_TAC THEN
   REWRITE_TAC[PRODUCT_CLAUSES_NUMSEG; SUM_CLAUSES_NUMSEG; LE_0; LE; ARITH] THEN
   BETA_TAC THEN MATCH_MP_TAC EXP_NEG_DIV_LE_1_MINUS THEN
   FIRST_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[LE_0] THEN
   ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SIMP_TAC[PRODUCT_CLAUSES_NUMSEG; SUM_CLAUSES_NUMSEG;
           ARITH_RULE `0 <= SUC n`] THEN BETA_TAC THEN
  SUBGOAL_THEN `&0 < &1 - delta` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `(sum(0..n) (c:num->real) + c(SUC n)) / (&1 - delta) =
     sum(0..n) c / (&1 - delta) + c(SUC n) / (&1 - delta)`
    SUBST1_TAC THENL
  [SUBGOAL_THEN `~(&1 - delta = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
   ALL_TAC] THEN
  REWRITE_TAC[REAL_NEG_ADD; REAL_EXP_ADD] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC[REAL_EXP_POS_LE];
   FIRST_X_ASSUM(MP_TAC o SPECL [`c:num->real`; `delta:real`]) THEN
   ANTS_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `i <= n ==> i <= SUC n`]; SIMP_TAC[]];
   REWRITE_TAC[REAL_EXP_POS_LE];
   MATCH_MP_TAC EXP_NEG_DIV_LE_1_MINUS THEN
   FIRST_ASSUM(MP_TAC o SPEC `SUC n`) THEN
   REWRITE_TAC[LE_REFL] THEN ASM_REAL_ARITH_TAC]);;

(* L4: Non-IID generalization of CHAR_FN_SUM_IID_RE_BOUND.
   Telescoping product inequality for characteristic function real parts.
   |Re(char_fn(S_n)) - prod(Re(char_fn(X_i)))| <= sum(|Im(char_fn(X_i))|) *)
let CHAR_FN_SUM_RE_PRODUCT_BOUND = prove
 (`!p:A prob_space (X:num->A->real) n t.
      (!i. random_variable p (X i)) /\
      (!k. k < n ==> indep_rv p (\x. sum(0..k) (\i. X i x)) (X (SUC k)))
      ==> abs(char_fn_re p (\x. sum(0..n) (\i. X i x)) t -
              product(0..n) (\i. char_fn_re p (X i) t))
          <= sum(0..n) (\i. abs(char_fn_im p (X i) t))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [(* Base case *)
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `(\x:A. sum(0..0) (\i. (X:num->A->real) i x)) = X 0`
     (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; SUM_SING_NUMSEG] THEN GEN_TAC THEN BETA_TAC THEN
    REFL_TAC; ALL_TAC] THEN
   REWRITE_TAC[PRODUCT_CLAUSES_NUMSEG; SUM_CLAUSES_NUMSEG;
               LE_0; LE; ARITH] THEN
   BETA_TAC THEN
   REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM; REAL_ADD_RID; REAL_ABS_POS];
   ALL_TAC] THEN
  (* Step case *)
  GEN_TAC THEN STRIP_TAC THEN
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
    CHAR_FN_ADD_INDEP_RE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  BETA_TAC THEN DISCH_TAC THEN
  SIMP_TAC[PRODUCT_CLAUSES_NUMSEG; SUM_CLAUSES_NUMSEG;
           ARITH_RULE `0 <= SUC n`] THEN BETA_TAC THEN
  ONCE_ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Rn = char_fn_re (p:A prob_space)
    (\x:A. sum(0..n) (\i. (X:num->A->real) i x)) t` THEN
  ABBREV_TAC `Sn = char_fn_im (p:A prob_space)
    (\x:A. sum(0..n) (\i. (X:num->A->real) i x)) t` THEN
  ABBREV_TAC `rn1 = char_fn_re (p:A prob_space)
    ((X:num->A->real) (SUC n)) t` THEN
  ABBREV_TAC `sn1 = char_fn_im (p:A prob_space)
    ((X:num->A->real) (SUC n)) t` THEN
  ABBREV_TAC `Pn = product(0..n)
    (\i. char_fn_re (p:A prob_space) ((X:num->A->real) i) t)` THEN
  SUBGOAL_THEN `abs rn1 <= &1` ASSUME_TAC THENL
  [EXPAND_TAC "rn1" THEN MATCH_MP_TAC CHAR_FN_RE_BOUND THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs Sn <= &1` ASSUME_TAC THENL
  [EXPAND_TAC "Sn" THEN MATCH_MP_TAC CHAR_FN_IM_BOUND THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(Rn - Pn) <=
    sum(0..n) (\i. abs(char_fn_im (p:A prob_space)
      ((X:num->A->real) i) t))`
    ASSUME_TAC THENL
  [EXPAND_TAC "Rn" THEN EXPAND_TAC "Pn" THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN
   ANTS_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `k < n ==> k < SUC n`]; SIMP_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `Rn * rn1 - Sn * sn1 - Pn * rn1 =
                (Rn - Pn) * rn1 + (-- &1) * (Sn * sn1)`
    SUBST1_TAC THENL
  [REWRITE_TAC[REAL_SUB_RDISTRIB] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs((Rn - Pn) * rn1) + abs(-- &1 * Sn * sn1)` THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NEG; REAL_ABS_NUM;
              REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(0..n) (\i. abs(char_fn_im (p:A prob_space)
    ((X:num->A->real) i) t)) * &1 + &1 * abs sn1` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN GEN_TAC THEN STRIP_TAC THEN
    BETA_TAC THEN REWRITE_TAC[REAL_ABS_POS];
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS; REAL_LE_REFL]];
   REAL_ARITH_TAC]);;

(* Pointwise bound: cos Taylor remainder split by truncation threshold d.
   Case |x|<=d: cos(sx)-1+(sx)^2/2 <= s^4*d^2*x^2/6 (from COS_TAYLOR_BOUND_4)
   Case |x|>d:  cos(sx)-1+(sx)^2/2 <= s^2*x^2/2 (from COS_TAYLOR_UPPER) *)
let TAYLOR_COS_SPLIT_BOUND = prove
 (`!x s d. &0 <= d
   ==> cos(s * x) - &1 + (s * x) pow 2 / &2
       <= s pow 4 * d pow 2 * x pow 2 / &6 +
          s pow 2 * x pow 2 / &2 * (if abs(x) > d then &1 else &0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= s pow 4` ASSUME_TAC THENL
  [REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW; REAL_LE_POW_2];
   ALL_TAC] THEN
  DISJ_CASES_TAC (REAL_ARITH `abs x <= d \/ abs x > d`) THENL
  [SUBGOAL_THEN `~(abs x > d)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `(s * x) pow 4 / &6` THEN
   REWRITE_TAC[COS_TAYLOR_BOUND_4; REAL_POW_MUL] THEN
   REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[REAL_MUL_ASSOC] THEN
   MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `4 = 2 + 2`; REAL_POW_ADD] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_INV THEN REAL_ARITH_TAC];
   ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_MUL_RID] THEN
   MP_TAC(SPEC `s * x:real` COS_TAYLOR_UPPER) THEN
   REWRITE_TAC[REAL_POW_MUL] THEN
   SUBGOAL_THEN `&0 <= s pow 4 * d pow 2 * x pow 2 / &6` MP_TAC THENL
   [REWRITE_TAC[real_div] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2] THEN
    TRY(MATCH_MP_TAC REAL_LE_INV THEN REAL_ARITH_TAC);
    REAL_ARITH_TAC]]);;

(* Pointwise bound: |sin(sx)-sx| split by truncation threshold d.
   Case |x|<=d: |sin(sx)-sx| <= |s|^3*d*x^2/2 (from SIN_APPROX_BOUND)
   Case |x|>d:  |sin(sx)-sx| <= s^2*x^2 (from SIN_MINUS_X_SQ_BOUND) *)
let SIN_MINUS_X_SPLIT_BOUND = prove
 (`!x s d. &0 <= d
   ==> abs(sin(s * x) - s * x)
       <= abs(s) pow 3 * d * x pow 2 / &2 +
          s pow 2 * x pow 2 * (if abs(x) > d then &1 else &0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  DISJ_CASES_TAC (REAL_ARITH `abs x <= d \/ abs x > d`) THENL
  [SUBGOAL_THEN `~(abs x > d)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `abs(s * x) pow 3 / &2` THEN
   REWRITE_TAC[SIN_APPROX_BOUND] THEN
   REWRITE_TAC[REAL_ABS_MUL; REAL_POW_MUL] THEN
   REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_MUL_ASSOC] THEN
   MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    SUBGOAL_THEN `abs x pow 3 = abs x * x pow 2`
      SUBST1_TAC THENL
    [REWRITE_TAC[ARITH_RULE `3 = 1 + 2`; REAL_POW_ADD; REAL_POW_1;
                 REAL_POW2_ABS]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_INV THEN REAL_ARITH_TAC];
   ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_MUL_RID] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `(s * x:real) pow 2` THEN CONJ_TAC THENL
   [REWRITE_TAC[SIN_MINUS_X_SQ_BOUND];
    REWRITE_TAC[REAL_POW_MUL] THEN
    SUBGOAL_THEN `&0 <= abs s pow 3 * d * x pow 2 / &2` MP_TAC THENL
    [REWRITE_TAC[real_div] THEN
     REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
     ASM_REWRITE_TAC[REAL_LE_POW_2] THEN
     TRY(MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC) THEN
     TRY(MATCH_MP_TAC REAL_LE_INV THEN REAL_ARITH_TAC);
     REAL_ARITH_TAC]]]);;

(* Indicator function is a random variable when the threshold test
   involves a random variable *)
let RANDOM_VARIABLE_INDICATOR_GT = prove
 (`!p:A prob_space X d.
    random_variable p X /\ &0 <= d
    ==> random_variable p (\x. if abs(X x) > d then &1 else &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[random_variable] THEN
  X_GEN_TAC `c:real` THEN BETA_TAC THEN
  ASM_CASES_TAC `c < &0` THENL
  [SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ (if abs (X x) > d then &1 else &0) <= c} = {}`
    SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SIGMA_ALGEBRA_EMPTY THEN
    REWRITE_TAC[PROB_SPACE_SIGMA_ALGEBRA]];
   ALL_TAC] THEN
  ASM_CASES_TAC `&1 <= c` THENL
  [SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ (if abs (X x) > d then &1 else &0) <= c} = prob_carrier p`
    SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    GEN_TAC THEN EQ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPEC `prob_events(p:A prob_space)` SIGMA_ALGEBRA_CARRIER) THEN
    REWRITE_TAC[PROB_SPACE_SIGMA_ALGEBRA] THEN
    REWRITE_TAC[GSYM prob_carrier]];
   ALL_TAC] THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ (if abs (X x) > d then &1 else &0) <= c} =
    {x | x IN prob_carrier p /\ X x <= d} INTER
    {x | x IN prob_carrier p /\ --X x <= d}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN
   X_GEN_TAC `x:A` THEN
   ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
   COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
   MATCH_MP_TAC(ISPEC `prob_events(p:A prob_space)` SIGMA_ALGEBRA_INTER) THEN
   REWRITE_TAC[PROB_SPACE_SIGMA_ALGEBRA] THEN
   CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [random_variable]) THEN
    DISCH_THEN(MP_TAC o SPEC `d:real`) THEN REWRITE_TAC[];
    MP_TAC(MATCH_MP RANDOM_VARIABLE_NEG (ASSUME `random_variable p (X:A->real)`)) THEN
    REWRITE_TAC[random_variable] THEN
    DISCH_THEN(MP_TAC o SPEC `d:real`) THEN BETA_TAC THEN REWRITE_TAC[]]]);;

(* Indicator of {abs(X) <= d} is a random variable *)
let RANDOM_VARIABLE_INDICATOR_LE = prove
 (`!p:A prob_space X d.
    random_variable p X /\ &0 <= d
    ==> random_variable p (\x. if abs(X x) <= d then &1 else &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[random_variable] THEN
  X_GEN_TAC `c:real` THEN BETA_TAC THEN
  ASM_CASES_TAC `c < &0` THENL
  [SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
     (if abs ((X:A->real) x) <= d then &1 else &0) <= c} = {}`
    SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SIGMA_ALGEBRA_EMPTY THEN
    REWRITE_TAC[PROB_SPACE_SIGMA_ALGEBRA]];
   ALL_TAC] THEN
  ASM_CASES_TAC `&1 <= c` THENL
  [SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
     (if abs ((X:A->real) x) <= d then &1 else &0) <= c} = prob_carrier p`
    SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    GEN_TAC THEN EQ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPEC `prob_events(p:A prob_space)` SIGMA_ALGEBRA_CARRIER) THEN
    REWRITE_TAC[PROB_SPACE_SIGMA_ALGEBRA] THEN
    REWRITE_TAC[GSYM prob_carrier]];
   ALL_TAC] THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
     (if abs ((X:A->real) x) <= d then &1 else &0) <= c} =
    prob_carrier p DIFF
    ({x | x IN prob_carrier p /\ X x <= d} INTER
     {x | x IN prob_carrier p /\ --X x <= d})`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_INTER] THEN
   X_GEN_TAC `x:A` THEN
   ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
   COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
   MATCH_MP_TAC PROB_COMPL_IN_EVENTS THEN
   MATCH_MP_TAC(ISPEC `prob_events(p:A prob_space)` SIGMA_ALGEBRA_INTER) THEN
   REWRITE_TAC[PROB_SPACE_SIGMA_ALGEBRA] THEN
   CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [random_variable]) THEN
    DISCH_THEN(MP_TAC o SPEC `d:real`) THEN REWRITE_TAC[];
    MP_TAC(MATCH_MP RANDOM_VARIABLE_NEG
      (ASSUME `random_variable p (X:A->real)`)) THEN
    REWRITE_TAC[random_variable] THEN
    DISCH_THEN(MP_TAC o SPEC `d:real`) THEN
    BETA_TAC THEN REWRITE_TAC[]]]);;

(* X^2 * indicator(abs X > d) is integrable when X^2 is integrable *)
let INTEGRABLE_INDICATOR_WEIGHTED_POW2 = prove
 (`!p:A prob_space X d.
    random_variable p X /\ integrable p (\x. X x pow 2) /\ &0 <= d
    ==> integrable p (\x. X x pow 2 * (if abs(X x) > d then &1 else &0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC INTEGRABLE_DOMINATED THEN
  EXISTS_TAC `\x:A. (X:A->real) x pow 2` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RANDOM_VARIABLE_INDICATOR_GT THEN ASM_REWRITE_TAC[]];
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   REWRITE_TAC[REAL_ABS_MUL] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(X(x:A) pow 2) * &1` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]]);;

let INTEGRABLE_INDICATOR_WEIGHTED_POW2_LE = prove
 (`!p:A prob_space X d.
    random_variable p X /\ integrable p (\x. X x pow 2) /\ &0 <= d
    ==> integrable p (\x. X x pow 2 * (if abs(X x) <= d then &1 else &0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC INTEGRABLE_DOMINATED THEN
  EXISTS_TAC `\x:A. (X:A->real) x pow 2` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RANDOM_VARIABLE_INDICATOR_LE THEN ASM_REWRITE_TAC[]];
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   REWRITE_TAC[REAL_ABS_MUL] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(X(x:A) pow 2) * &1` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]]);;

(* Per-component bound on real part of char fn Taylor remainder.
   char_fn_re p X s - (1 - s^2*E[X^2]/2) <= s^4*d^2*E[X^2]/6 + s^2/2*E[X^2*I(abs X>d)]
   Uses COS_TAYLOR_BOUND_4 for |X|<=d part, COS_TAYLOR_UPPER for |X|>d part. *)
let CHAR_FN_RE_COMPONENT_BOUND = prove
 (`!p:A prob_space X s d.
    integrable p X /\ integrable p (\x. X x pow 2) /\
    expectation p X = &0 /\ &0 <= d
    ==> char_fn_re p X s - (&1 - s pow 2 * expectation p (\x. X x pow 2) / &2)
        <= s pow 4 * d pow 2 * expectation p (\x. X x pow 2) / &6 +
           s pow 2 / &2 * expectation p (\x. X x pow 2 *
              (if abs(X x) > d then &1 else &0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `random_variable p (X:A->real)` ASSUME_TAC THENL
  [ASM_MESON_TAC[INTEGRABLE_IMP_RANDOM_VARIABLE]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (\x:A. X x pow 2 * (if abs(X x) > d then &1 else &0))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_INDICATOR_WEIGHTED_POW2 THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `char_fn_re p X s - (&1 - s pow 2 * expectation p (\x:A. X x pow 2) / &2) =
     expectation p (\x. cos(s * X x) - &1 + s pow 2 * X x pow 2 / &2)`
    SUBST1_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `s:real`]
    TAYLOR_REMAINDER_EXPECTATION) THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `expectation p (\x:A. s pow 4 * d pow 2 / &6 * X x pow 2 +
    s pow 2 / &2 * (X x pow 2 * (if abs(X x) > d then &1 else &0)))` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC EXPECTATION_MONO THEN
   ASM_SIMP_TAC[INTEGRABLE_TAYLOR_REMAINDER] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_CMUL THEN
     MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(X:A->real) x`; `s:real`; `d:real`] TAYLOR_COS_SPLIT_BOUND) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_POW_MUL] THEN
    REAL_ARITH_TAC];
   SUBGOAL_THEN `integrable p (\x:A. s pow 4 * d pow 2 / &6 * X x pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CMUL THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `integrable p (\x:A. s pow 2 / &2 * (X x pow 2 * (if abs(X x) > d then &1 else &0)))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_SIMP_TAC[EXPECTATION_ADD] THEN
   ASM_SIMP_TAC[EXPECTATION_CMUL; INTEGRABLE_CMUL] THEN
   REAL_ARITH_TAC]);;

(* Per-component bound on imaginary part of char fn.
   |char_fn_im p X s| <= |s|^3*d*E[X^2]/2 + s^2*E[X^2*I(abs X>d)]
   Uses E[X]=0, SIN_APPROX_BOUND for |X|<=d, SIN_MINUS_X_SQ_BOUND for |X|>d. *)
let CHAR_FN_IM_COMPONENT_BOUND = prove
 (`!p:A prob_space X s d.
    integrable p X /\ integrable p (\x. X x pow 2) /\
    expectation p X = &0 /\ &0 <= d
    ==> abs(char_fn_im p X s)
        <= abs(s) pow 3 * d * expectation p (\x. X x pow 2) / &2 +
           s pow 2 * expectation p (\x. X x pow 2 *
              (if abs(X x) > d then &1 else &0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `random_variable p (X:A->real)` ASSUME_TAC THENL
  [ASM_MESON_TAC[INTEGRABLE_IMP_RANDOM_VARIABLE]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (\x:A. X x pow 2 * (if abs(X x) > d then &1 else &0))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_INDICATOR_WEIGHTED_POW2 THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (\x:A. sin(s * X x))` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_SIN_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (\x:A. s * X x)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `char_fn_im p X s = expectation p (\x:A. sin(s * X x) - s * X x)`
    SUBST1_TAC THENL
  [REWRITE_TAC[char_fn_im] THEN
   ASM_SIMP_TAC[EXPECTATION_SUB; EXPECTATION_CMUL] THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `expectation p (\x:A. abs(sin(s * X x) - s * X x))` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC EXPECTATION_ABS_BOUND THEN
   MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `expectation p (\x:A. abs s pow 3 * d / &2 * X x pow 2 +
    s pow 2 * (X x pow 2 * (if abs(X x) > d then &1 else &0)))` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC EXPECTATION_MONO THEN
   ASM_SIMP_TAC[INTEGRABLE_ABS; INTEGRABLE_SUB] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_CMUL THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
     ASM_REWRITE_TAC[];
     MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(X:A->real) x`; `s:real`; `d:real`] SIN_MINUS_X_SPLIT_BOUND) THEN
    ASM_REWRITE_TAC[REAL_ABS_MUL; REAL_POW_MUL] THEN REAL_ARITH_TAC];
   SUBGOAL_THEN `integrable p (\x:A. abs s pow 3 * d / &2 * X x pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CMUL THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `integrable p (\x:A. s pow 2 * (X x pow 2 * (if abs(X x) > d then &1 else &0)))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_SIMP_TAC[EXPECTATION_ADD] THEN
   ASM_SIMP_TAC[EXPECTATION_CMUL; INTEGRABLE_CMUL] THEN
   REAL_ARITH_TAC]);;

(* L4_IM: Imaginary part analog of CHAR_FN_SUM_RE_PRODUCT_BOUND.
   |char_fn_im(sum X_i)| <= sum |char_fn_im(X_i)| *)
let CHAR_FN_SUM_IM_BOUND = prove
 (`!p:A prob_space (X:num->A->real) n t.
      (!i. random_variable p (X i)) /\
      (!k. k < n ==> indep_rv p (\x. sum(0..k) (\i. X i x)) (X (SUC k)))
      ==> abs(char_fn_im p (\x. sum(0..n) (\i. X i x)) t)
          <= sum(0..n) (\i. abs(char_fn_im p (X i) t))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [(* Base case *)
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `(\x:A. sum(0..0) (\i. (X:num->A->real) i x)) = X 0`
     (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; SUM_SING_NUMSEG] THEN GEN_TAC THEN BETA_TAC THEN
    REFL_TAC; ALL_TAC] THEN
   REWRITE_TAC[SUM_SING_NUMSEG] THEN BETA_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  GEN_TAC THEN STRIP_TAC THEN
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
    CHAR_FN_ADD_INDEP_IM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  BETA_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `0 <= SUC n`] THEN BETA_TAC THEN
  SUBGOAL_THEN `abs(char_fn_re (p:A prob_space)
    (\x:A. sum(0..n) (\i. (X:num->A->real) i x)) t) <= &1` ASSUME_TAC THENL
  [MATCH_MP_TAC CHAR_FN_RE_BOUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(char_fn_re (p:A prob_space)
    ((X:num->A->real) (SUC n)) t) <= &1` ASSUME_TAC THENL
  [MATCH_MP_TAC CHAR_FN_RE_BOUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(char_fn_im (p:A prob_space)
    (\x:A. sum(0..n) (\i. (X:num->A->real) i x)) t) <=
    sum(0..n) (\i. abs(char_fn_im p (X i) t))`
    ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN
   ANTS_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `k < n ==> k < SUC n`]; SIMP_TAC[]];
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(char_fn_re (p:A prob_space)
    (\x:A. sum(0..n) (\i. (X:num->A->real) i x)) t) *
    abs(char_fn_im p (X (SUC n)) t) +
    abs(char_fn_im p (\x. sum(0..n) (\i. X i x)) t) *
    abs(char_fn_re p (X (SUC n)) t)` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[GSYM REAL_ABS_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&1 * abs(char_fn_im (p:A prob_space)
    ((X:num->A->real) (SUC n)) t) +
    sum(0..n) (\i. abs(char_fn_im p (X i) t)) * &1` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS; REAL_LE_REFL];
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN GEN_TAC THEN STRIP_TAC THEN
    BETA_TAC THEN REWRITE_TAC[REAL_ABS_POS]];
   REAL_ARITH_TAC]);;

(* ===================================================================== *)
(* Lindeberg-Feller Central Limit Theorem                                *)
(* ===================================================================== *)

(* LOCAL_ASM_REAL_ARITH_TAC: filters foralls, existentials,
   ABBREV_TAC equations (where one side is a plain variable),
   and assumptions containing lambda abstractions (which
   REAL_ARITH cannot handle, e.g. sum/expectation terms) *)
let LOCAL_ASM_REAL_ARITH_TAC =
  let is_abbrev_eq c =
    try let l,r = dest_eq c in is_var r || is_var l
    with Failure _ -> false in
  let rec has_abs tm =
    if is_abs tm then true
    else if is_comb tm then
      let f,x = dest_comb tm in has_abs f || has_abs x
    else false in
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
    let c = concl th in
    not(is_forall c) && not(is_exists c) &&
    not(is_abbrev_eq c) && not(has_abs c)))) THEN
  REAL_ARITH_TAC;;

(* Main theorem: Lindeberg-Feller CLT
   For independent (not necessarily identically distributed) random
   variables with zero mean and finite second moments, if the Lindeberg
   condition holds then the standardized partial sums converge in
   distribution to the standard normal. *)
let REAL_EQ_SUB_RADD = prove
 (`!a b c:real. a = b - c ==> b = c + a`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let REAL_POW2_ABS_LE = prove
 (`!x y:real. abs x <= y ==> x pow 2 <= y pow 2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW2_ABS] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN
  ASM_REWRITE_TAC[REAL_ABS_POS]);;

let LINDEBERG_FELLER_CLT = prove
 (`!p:A prob_space (X:num->A->real).
    (!n. integrable p (X n)) /\
    (!n. integrable p (\x. X n x pow 2)) /\
    (!i. expectation p (X i) = &0) /\
    (!i j:num. ~(i = j) ==> indep_rv p (X i) (X j)) /\
    (!n k. k < n ==>
       indep_rv p (\x. sum(0..k) (\i. X i x)) (X (SUC k))) /\
    (!n. &0 < sum(0..n) (\i. expectation p (\x. X i x pow 2))) /\
    (!eps. &0 < eps ==>
      ((\n. sum(0..n) (\i. expectation p (\x. X i x pow 2 *
              (if abs(X i x) >
                  eps * sqrt(sum(0..n) (\j. expectation p (\y. X j y pow 2)))
               then &1 else &0))) /
            sum(0..n) (\i. expectation p (\x. X i x pow 2)))
       ---> &0) sequentially)
    ==>
    !x. ((\n. cdf p (\a. sum(0..n) (\i. X i a) /
              sqrt(sum(0..n) (\j. expectation p (\y. X j y pow 2)))) x)
         ---> std_normal_cdf x) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Abbreviate sn2 n = sum(0..n) E[X_i^2] *)
  ABBREV_TAC `sn2 = \n:num. sum(0..n)
    (\i. expectation p (\x. (X:num->A->real) i x pow 2))` THEN
  (* Abbreviate Y_n = standardized partial sum *)
  ABBREV_TAC `Y = \n:num. \a:A. sum(0..n) (\i. (X:num->A->real) i a) /
    sqrt((sn2:num->real) n)` THEN
  (* random_variable for each X_i *)
  SUBGOAL_THEN `!i:num. random_variable p ((X:num->A->real) i)` ASSUME_TAC
    THENL
  [ASM_MESON_TAC[INTEGRABLE_IMP_RANDOM_VARIABLE]; ALL_TAC] THEN
  (* sn2 n > 0 *)
  SUBGOAL_THEN `!n:num. &0 < (sn2:num->real) n` ASSUME_TAC THENL
  [EXPAND_TAC "sn2" THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  (* sqrt(sn2 n) > 0 *)
  SUBGOAL_THEN `!n:num. &0 < sqrt((sn2:num->real) n)` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[ETA_AX];
   ALL_TAC] THEN
  (* sqrt(sn2 n) != 0 *)
  SUBGOAL_THEN `!n:num. ~(sqrt((sn2:num->real) n) = &0)` ASSUME_TAC THENL
  [ASM_MESON_TAC[REAL_LT_IMP_NZ]; ALL_TAC] THEN
  (* Rewrite conclusion in terms of Y *)
  SUBGOAL_THEN `!n x:real. cdf p ((Y:num->A->real) n) x =
    cdf p (\a. sum(0..n) (\i. (X:num->A->real) i a) /
      sqrt((sn2:num->real) n)) x` ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   EXPAND_TAC "Y" THEN REFL_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `!n x:real. cdf p (\a. sum(0..n)
    (\i. (X:num->A->real) i a) /
    sqrt(sum(0..n) (\j. expectation p (\y. X j y pow 2)))) x =
    cdf p ((Y:num->A->real) n) x` ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN ASM_REWRITE_TAC[ETA_AX] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "sn2" THEN REFL_TAC;
   ALL_TAC] THEN
  ASM_REWRITE_TAC[ETA_AX] THEN
  (* Apply LEVY_CONTINUITY_CLT to Y *)
  MATCH_MP_TAC LEVY_CONTINUITY_CLT THEN
  (* Fold sn2 abbreviation back into goal -- MATCH_MP_TAC expanded it *)
  SUBGOAL_THEN `!n. sum(0..n)
    (\j. expectation p (\y:A. (X:num->A->real) j y pow 2)) =
    (sn2:num->real) n` (fun th -> REWRITE_TAC[th]) THENL
  [GEN_TAC THEN EXPAND_TAC "sn2" THEN REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
  [(* random_variable p (expanded form) *)
   X_GEN_TAC `n:num` THEN
   SUBGOAL_THEN `(\a:A. sum(0..n) (\i. (X:num->A->real) i a) /
     sqrt((sn2:num->real) n)) =
     (\a. inv(sqrt(sn2 n)) * sum(0..n) (\i. X i a))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; real_div] THEN GEN_TAC THEN REAL_ARITH_TAC;
    MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN
    MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN
    GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[ETA_AX]];
   (* Bounded second moments: ?C. ... *)
   EXISTS_TAC `&2` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
   X_GEN_TAC `n:num` THEN BETA_TAC THEN
   (* Goal: expectation p (\x. (sum/sqrt(sn2)) pow 2) <= &2 *)
   MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1` THEN
   CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
   (* Suffices to show E[(sum/sqrt(sn2))^2] = 1 *)
   REWRITE_TAC[REAL_POW_DIV] THEN
   SUBGOAL_THEN
     `(\x:A. sum(0..n) (\i. (X:num->A->real) i x) pow 2 /
        sqrt((sn2:num->real) n) pow 2) =
      (\x. inv(sqrt(sn2 n) pow 2) * sum(0..n) (\i. X i x) pow 2)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; real_div] THEN GEN_TAC THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
     `expectation p (\x:A. inv(sqrt((sn2:num->real) n) pow 2) *
        sum(0..n) (\i. (X:num->A->real) i x) pow 2) =
      inv(sqrt(sn2 n) pow 2) *
        expectation p (\x. sum(0..n) (\i. X i x) pow 2)`
     SUBST1_TAC THENL
   [MATCH_MP_TAC EXPECTATION_CMUL THEN
    MATCH_MP_TAC INTEGRABLE_SUM_SQUARE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `sqrt((sn2:num->real) n) pow 2 = sn2 n` SUBST1_TAC THENL
   [MATCH_MP_TAC SQRT_POW_2 THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
   (* E[sum^2] = sn2 n *)
   SUBGOAL_THEN `expectation p
     (\x:A. sum(0..n) (\i. (X:num->A->real) i x) pow 2) =
     (sn2:num->real) n` SUBST1_TAC THENL
   [SUBGOAL_THEN `expectation p
       (\x:A. sum(0..n) (\i. (X:num->A->real) i x) pow 2) =
       variance p (\x. sum(0..n) (\i. X i x))` SUBST1_TAC THENL
    [MATCH_MP_TAC VARIANCE_MEAN_ZERO THEN ASM_REWRITE_TAC[ETA_AX] THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_SUM THEN ASM_SIMP_TAC[];
      CONJ_TAC THENL
      [MATCH_MP_TAC INTEGRABLE_SUM_SQUARE THEN ASM_SIMP_TAC[];
       ASM_SIMP_TAC[EXPECTATION_SUM] THEN ASM_REWRITE_TAC[SUM_0]]];
     ALL_TAC] THEN
    SUBGOAL_THEN `variance p
       (\x:A. sum(0..n) (\i. (X:num->A->real) i x)) =
       sum(0..n) (\i. variance p (X i))` SUBST1_TAC THENL
    [MATCH_MP_TAC VARIANCE_SUM_UNCORRELATED THEN ASM_SIMP_TAC[] THEN
     REPEAT STRIP_TAC THEN MATCH_MP_TAC COVARIANCE_INDEP THEN
     ASM_SIMP_TAC[] THEN
     MATCH_MP_TAC INTEGRABLE_MUL_SQUARE THEN
     REWRITE_TAC[ETA_AX] THEN ASM_MESON_TAC[INTEGRABLE_IMP_RANDOM_VARIABLE];
     ALL_TAC] THEN
    SUBGOAL_THEN `!i:num. variance p ((X:num->A->real) i) =
       expectation p (\x:A. X i x pow 2)` (fun th -> REWRITE_TAC[th]) THENL
    [GEN_TAC THEN CONV_TAC SYM_CONV THEN
     MATCH_MP_TAC VARIANCE_MEAN_ZERO THEN ASM_SIMP_TAC[];
     ALL_TAC] THEN
    EXPAND_TAC "sn2" THEN REFL_TAC;
    ALL_TAC] THEN
   (* inv(sn2 n) * sn2 n = 1 *)
   SUBGOAL_THEN `~((sn2:num->real) n = &0)` MP_TAC THENL
   [ASM_MESON_TAC[REAL_LT_IMP_NZ]; ALL_TAC] THEN
   CONV_TAC REAL_FIELD;
   (* integrable p (expanded form) *)
   X_GEN_TAC `n:num` THEN
   REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
   MATCH_MP_TAC INTEGRABLE_CMUL THEN
   MATCH_MP_TAC INTEGRABLE_SUM THEN ASM_SIMP_TAC[];
   (* integrable p (\x. (expanded form) pow 2) *)
   X_GEN_TAC `n:num` THEN BETA_TAC THEN
   REWRITE_TAC[REAL_POW_DIV; real_div] THEN
   ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
   MATCH_MP_TAC INTEGRABLE_CMUL THEN
   MATCH_MP_TAC INTEGRABLE_SUM_SQUARE THEN ASM_SIMP_TAC[];
   (* ============================================================ *)
   (* char_fn_re convergence:                                      *)
   (*   char_fn_re p (Y n) t ---> exp(-t^2/2)                     *)
   (* Decomposition: [A]+[B]+[C] where                            *)
   (*   [A] = |char_fn_re(Y_n) - prod r_i| by L4                 *)
   (*   [B] = |prod r_i - prod(1-c_i)| by L1                     *)
   (*   [C] = |prod(1-c_i) - exp(-t^2/2)| by L2+L3              *)
   (* ============================================================ *)
   X_GEN_TAC `t:real` THEN
   ((* Scaling: char_fn_re p (\a. sum/sqrt(sn2)) t =
               char_fn_re p (\a. sum) (t/sqrt(sn2)) *)
   SUBGOAL_THEN `!n. char_fn_re p
     (\a:A. sum(0..n) (\i. (X:num->A->real) i a) /
       sqrt((sn2:num->real) n)) t =
     char_fn_re p (\a. sum(0..n) (\i. X i a))
       (t / sqrt(sn2 n))`
     (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[char_fn_re] THEN
    BETA_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    GEN_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
    (SUBGOAL_THEN `!a b:real. a / b = inv(b) * a`
      (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN REAL_ARITH_TAC; ALL_TAC]) THEN
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   X_GEN_TAC `eta:real` THEN DISCH_TAC THEN
   ((* Handle t = 0 case *)
   ASM_CASES_TAC `t = &0` THENL
   [EXISTS_TAC `0` THEN GEN_TAC THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; char_fn_re; COS_0;
      EXPECTATION_CONST; REAL_POW_2; REAL_MUL_LZERO;
      REAL_NEG_0; REAL_EXP_0; REAL_SUB_REFL; REAL_ABS_NUM] THEN
    LOCAL_ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
   (* For eta >= 2, bound is trivial: |char_fn_re - exp| <= 1+1 = 2 < eta *)
   (ASM_CASES_TAC `&2 <= eta` THENL
   [EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
      `abs a <= &1 /\ &0 <= b /\ b < &1 /\ &2 <= e
        ==> abs(a - b) < e`) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC CHAR_FN_RE_BOUND THEN
     MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN ASM_MESON_TAC[];
     REWRITE_TAC[REAL_EXP_POS_LE];
     REWRITE_TAC[GSYM REAL_EXP_0; REAL_EXP_MONO_LT] THEN
     SUBGOAL_THEN `&0 < (t:real) pow 2` MP_TAC THENL
     [REWRITE_TAC[REAL_ARITH `&0 < x <=> &0 <= x /\ ~(x = &0)`] THEN
      REWRITE_TAC[REAL_LE_POW_2; REAL_POW_EQ_0; ARITH_EQ] THEN
      ASM_REWRITE_TAC[];
      REAL_ARITH_TAC]]; ALL_TAC]) THEN
   (* Now eta < 2 *)
   (* t != 0 *)
   (* Abbreviate Lindeberg tail as Ln *)
   ABBREV_TAC `Ln = \(eps:real) (n:num).
     sum(0..n) (\i. expectation p (\x:A. (X:num->A->real) i x pow 2 *
       (if abs(X i x) > eps * sqrt((sn2:num->real) n)
        then &1 else &0))) / sn2 n` THEN
   (* Choose eps for the constant terms *)
   ABBREV_TAC `eps = min (&1)
     (eta / (&5 * (abs(t:real) pow 3 + t pow 4 + &1)))` THEN
   (SUBGOAL_THEN `&0 < eps` ASSUME_TAC THENL
   [EXPAND_TAC "eps" THEN REWRITE_TAC[REAL_LT_MIN] THEN
    (CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC]) THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
    [REAL_ARITH_TAC;
     MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 < a + b + &1`) THEN
     CONJ_TAC THENL
     [SIMP_TAC[REAL_POW_LE; REAL_ABS_POS];
      REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW;
        REAL_LE_POW_2]]]; ALL_TAC]) THEN
   (SUBGOAL_THEN `eps <= &1` ASSUME_TAC THENL
   [EXPAND_TAC "eps" THEN REAL_ARITH_TAC; ALL_TAC]) THEN
   ((* Bound: |t|^3 * eps / 2 < eta/4 *)
   SUBGOAL_THEN `abs(t:real) pow 3 * eps / &2 < eta / &5`
     ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `abs(t:real) pow 3 *
      (eta / (&5 * (abs t pow 3 + t pow 4 + &1))) / &2` THEN
    (CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [SIMP_TAC[REAL_POW_LE; REAL_ABS_POS];
      SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ARITH `&0 < &2`] THEN
      EXPAND_TAC "eps" THEN REAL_ARITH_TAC]; ALL_TAC]) THEN
    (* abs(t)^3 * eta/(4*D) / 2 < eta / 4 where D = abs(t)^3+t^4+1 *)
    (SUBGOAL_THEN `&0 < abs(t:real) pow 3 + t pow 4 + &1` ASSUME_TAC THENL
    [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 < a + b + &1`) THEN
     CONJ_TAC THENL
     [SIMP_TAC[REAL_POW_LE; REAL_ABS_POS];
      REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW;
        REAL_LE_POW_2]]; ALL_TAC]) THEN
    (SUBGOAL_THEN `abs(t:real) pow 3 / (abs t pow 3 + t pow 4 + &1) < &1`
      ASSUME_TAC THENL
    [ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REWRITE_TAC[REAL_MUL_LID] THEN
     MATCH_MP_TAC(REAL_ARITH `&0 <= b ==> a < a + b + &1`) THEN
     REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW;
       REAL_LE_POW_2]; ALL_TAC]) THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `eta / &10` THEN
    (CONJ_TAC THENL [ALL_TAC; LOCAL_ASM_REAL_ARITH_TAC]) THEN
    SUBGOAL_THEN
      `abs(t:real) pow 3 * eta /
         (&5 * (abs t pow 3 + t pow 4 + &1)) / &2 =
       (eta / &10) *
         (abs t pow 3 / (abs t pow 3 + t pow 4 + &1))`
      SUBST1_TAC THENL
    [UNDISCH_TAC `&0 < abs(t:real) pow 3 + t pow 4 + &1` THEN
     CONV_TAC REAL_FIELD; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LT_DIV THEN LOCAL_ASM_REAL_ARITH_TAC;
     ASM_REWRITE_TAC[ETA_AX]];
    ALL_TAC]) THEN
   ((* Bound: t^4 * eps^2 / 6 < eta/4 *)
   SUBGOAL_THEN `t pow 4 * eps pow 2 / &6 < eta / &5`
     ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `t pow 4 * eps / &6` THEN CONJ_TAC THENL
    [(* eps^2 <= eps since eps <= 1 *)
     REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW; REAL_LE_POW_2];
      ALL_TAC] THEN
     MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_INV THEN REAL_ARITH_TAC]; ALL_TAC] THEN
    (* t^4 * eps / 6 < eta / 4 *)
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `t pow 4 *
      (eta / (&5 * (abs(t:real) pow 3 + t pow 4 + &1))) / &6` THEN
    CONJ_TAC THENL
    [(* eps <= eta/(4*D) *)
     REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW; REAL_LE_POW_2];
      ALL_TAC] THEN
     MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [EXPAND_TAC "eps" THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV THEN REAL_ARITH_TAC]; ALL_TAC] THEN
    (* eta * t^4/(24*D) < eta/4 *)
    (SUBGOAL_THEN `&0 < abs(t:real) pow 3 + t pow 4 + &1` ASSUME_TAC THENL
    [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 < a + b + &1`) THEN
     CONJ_TAC THENL
     [SIMP_TAC[REAL_POW_LE; REAL_ABS_POS];
      REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW;
        REAL_LE_POW_2]]; ALL_TAC]) THEN
    SUBGOAL_THEN
      `t pow 4 * eta / (&5 * (abs(t:real) pow 3 + t pow 4 + &1)) / &6 =
       (eta / &30) * (t pow 4 / (abs t pow 3 + t pow 4 + &1))`
      SUBST1_TAC THENL
    [UNDISCH_TAC `&0 < abs(t:real) pow 3 + t pow 4 + &1` THEN
     CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `eta / &30` THEN
    CONJ_TAC THENL [ALL_TAC; LOCAL_ASM_REAL_ARITH_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LT_DIV THEN LOCAL_ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REWRITE_TAC[REAL_MUL_LID] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> b < a + b + &1`) THEN
    SIMP_TAC[REAL_POW_LE; REAL_ABS_POS];
    ALL_TAC]) THEN
   ((* By Lindeberg at eps, Ln(eps) -> 0 *)
   SUBGOAL_THEN `((Ln:real->num->real) eps ---> &0) sequentially`
     ASSUME_TAC THENL
   [EXPAND_TAC "Ln" THEN BETA_TAC THEN
    UNDISCH_TAC `!eps. &0 < eps ==>
      ((\n. sum (0..n) (\i. expectation (p:A prob_space)
        (\x. (X:num->A->real) i x pow 2 *
          (if abs (X i x) > eps * sqrt (sum (0..n)
            (\j. expectation p (\y. X j y pow 2))) then &1 else &0))) /
        sum (0..n) (\i. expectation p (\x. X i x pow 2)))
      ---> &0) sequentially` THEN
    DISCH_THEN(MP_TAC o SPEC `eps:real`) THEN ASM_REWRITE_TAC[ETA_AX] THEN
    EXPAND_TAC "sn2" THEN SIMP_TAC[]; ALL_TAC]) THEN
   (* Get N from Lindeberg *)
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
   DISCH_THEN(MP_TAC o SPEC
     `eta / (&5 * (t pow 2 + t pow 4 + &1))`) THEN
   (ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
    [REAL_ARITH_TAC;
     MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 < a + b + &1`) THEN
     CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_POW_2];
      REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW;
        REAL_LE_POW_2]]]; ALL_TAC]) THEN
   REWRITE_TAC[REAL_SUB_RZERO] THEN
   DISCH_THEN(X_CHOOSE_THEN `N1:num` ASSUME_TAC) THEN
   ((* Get N2 from max variance vanishing: eventually max c_i <= 1/2 *)
   (* Use a fresh Lindeberg invocation with eps2 = sqrt(inv(4t^2+4)) *)
   (* Then sigma_i^2/sn2 < 2*inv(4t^2+4) = inv(2t^2+2) *)
   (* So ci = t^2*sigma_i^2/(2*sn2) < t^2/(2*(2t^2+2)) = t^2/(4t^2+4) <= 1/4 *)
   SUBGOAL_THEN `?N2. !n. N2 <= n ==>
     !i. i <= n ==> t pow 2 *
       expectation p (\x:A. (X:num->A->real) i x pow 2) /
         (&2 * (sn2:num->real) n) <= &1 / &2`
     (X_CHOOSE_THEN `N2:num` ASSUME_TAC) THENL
   [ABBREV_TAC `eps2 = sqrt(inv(&4 * t pow 2 + &4))` THEN
    (SUBGOAL_THEN `&0 < &4 * t pow 2 + &4` ASSUME_TAC THENL
    [MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> &0 < &4 * a + &4`) THEN
     REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC]) THEN
    (SUBGOAL_THEN `&0 < eps2` ASSUME_TAC THENL
    [EXPAND_TAC "eps2" THEN MATCH_MP_TAC SQRT_POS_LT THEN
     MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC]) THEN
    (SUBGOAL_THEN `eps2 pow 2 = inv(&4 * t pow 2 + &4)` ASSUME_TAC THENL
    [EXPAND_TAC "eps2" THEN MATCH_MP_TAC SQRT_POW_2 THEN
     MATCH_MP_TAC REAL_LE_INV THEN LOCAL_ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    (* Get Lindeberg at eps2: keep universal condition as well *)
    UNDISCH_TAC `!eps. &0 < eps ==>
      ((\n. sum (0..n) (\i. expectation (p:A prob_space)
        (\x. (X:num->A->real) i x pow 2 *
          (if abs (X i x) > eps * sqrt (sum (0..n)
            (\j. expectation p (\y. X j y pow 2))) then &1 else &0))) /
        sum (0..n) (\i. expectation p (\x. X i x pow 2)))
      ---> &0) sequentially` THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN
      MP_TAC(SPEC `eps2:real` th)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
    REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
    DISCH_THEN(MP_TAC o SPEC `inv(&4 * t pow 2 + &4)`) THEN
    (ANTS_TAC THENL
    [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `M:num` ASSUME_TAC) THEN
    EXISTS_TAC `M:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    (* Get Ln(eps2,n) bound in sn2 terms *)
    SUBGOAL_THEN `abs(sum(0..n) (\i'. expectation (p:A prob_space)
      (\x:A. (X:num->A->real) i' x pow 2 *
        (if abs(X i' x) > eps2 * sqrt((sn2:num->real) n)
         then &1 else &0))) / sn2 n) < inv(&4 * t pow 2 + &4)`
      ASSUME_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
     ASM_REWRITE_TAC[ETA_AX] THEN EXPAND_TAC "sn2" THEN SIMP_TAC[];
     ALL_TAC] THEN
    ((* sigma_i^2/sn2 < 2*inv(4t^2+4) via decomposition *)
    SUBGOAL_THEN `expectation p (\x:A. (X:num->A->real) i x pow 2) /
      (sn2:num->real) n < &2 * inv(&4 * t pow 2 + &4)` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_LET_TRANS THEN
     EXISTS_TAC `eps2 pow 2 + abs(sum(0..n) (\i'. expectation (p:A prob_space)
       (\x:A. (X:num->A->real) i' x pow 2 *
         (if abs(X i' x) > eps2 * sqrt((sn2:num->real) n)
          then &1 else &0))) / sn2 n)` THEN
     CONJ_TAC THENL
     [ALL_TAC; ASM_REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC(REAL_ARITH `x < y ==> y + x < &2 * y`) THEN
      FIRST_X_ASSUM MATCH_ACCEPT_TAC] THEN
     ((* sigma_i^2/sn2 <= eps2^2 + |sum/sn2| -- decomposition *)
     SUBGOAL_THEN `expectation p (\x:A. (X:num->A->real) i x pow 2) =
       expectation p (\x. X i x pow 2 *
         (if abs(X i x) <= eps2 * sqrt((sn2:num->real) n) then &1 else &0)) +
       expectation p (\x. X i x pow 2 *
         (if abs(X i x) > eps2 * sqrt(sn2 n) then &1 else &0))`
       SUBST1_TAC THENL
     [(SUBGOAL_THEN `(\x:A. (X:num->A->real) i x pow 2) =
        (\x. X i x pow 2 *
          (if abs(X i x) <= eps2 * sqrt((sn2:num->real) n) then &1 else &0) +
          X i x pow 2 *
          (if abs(X i x) > eps2 * sqrt(sn2 n) then &1 else &0))`
        SUBST1_TAC THENL
      [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN BETA_TAC THEN
       REAL_ARITH_TAC; ALL_TAC]) THEN
      MATCH_MP_TAC EXPECTATION_ADD THEN CONJ_TAC THENL
      [MATCH_MP_TAC INTEGRABLE_DOMINATED THEN
       EXISTS_TAC `\x:A. (X:num->A->real) i x pow 2` THEN
       ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
       [MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN CONJ_TAC THENL
        [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN ASM_REWRITE_TAC[ETA_AX];
         MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) i`;
           `eps2 * sqrt((sn2:num->real) n)`]
           RANDOM_VARIABLE_INDICATOR_LE) THEN
         ANTS_TAC THENL
         [ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC REAL_LE_MUL THEN
          ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC SQRT_POS_LE THEN
          LOCAL_ASM_REAL_ARITH_TAC;
          BETA_TAC THEN SIMP_TAC[]]];
        X_GEN_TAC `x:A` THEN DISCH_TAC THEN
        REWRITE_TAC[REAL_ABS_MUL] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `abs((X:num->A->real) i (x:A) pow 2) * &1` THEN
        CONJ_TAC THENL
        [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
         COND_CASES_TAC THEN REAL_ARITH_TAC;
         REAL_ARITH_TAC]];
       MATCH_MP_TAC INTEGRABLE_INDICATOR_WEIGHTED_POW2 THEN
       ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC REAL_LE_MUL THEN
       ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC SQRT_POS_LE THEN
       LOCAL_ASM_REAL_ARITH_TAC]; ALL_TAC]) THEN
     (* E[Xi^2*1_small] <= eps2^2 * sn2 *)
     SUBGOAL_THEN `expectation p (\x:A. (X:num->A->real) i x pow 2 *
       (if abs(X i x) <= eps2 * sqrt((sn2:num->real) n) then &1 else &0)) <=
       eps2 pow 2 * sn2 n` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `expectation p
        (\x:A. (eps2 * sqrt((sn2:num->real) n)) pow 2)` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC EXPECTATION_MONO THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_DOMINATED THEN
        EXISTS_TAC `\x:A. (X:num->A->real) i x pow 2` THEN
        ASM_REWRITE_TAC[ETA_AX] THEN (CONJ_TAC THENL
        [MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN ASM_REWRITE_TAC[ETA_AX];
          MATCH_MP_TAC RANDOM_VARIABLE_INDICATOR_LE THEN
          ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC REAL_LE_MUL THEN
          ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC SQRT_POS_LE THEN
          LOCAL_ASM_REAL_ARITH_TAC]; ALL_TAC]) THEN
        X_GEN_TAC `x:A` THEN DISCH_TAC THEN
        REWRITE_TAC[REAL_ABS_MUL] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `abs((X:num->A->real) i (x:A) pow 2) * &1` THEN
        CONJ_TAC THENL
        [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
         COND_CASES_TAC THEN REAL_ARITH_TAC;
         REAL_ARITH_TAC];
        ( CONJ_TAC THENL
       [REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC]) THEN
       X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
       (COND_CASES_TAC THENL
       [REWRITE_TAC[REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_POW2_ABS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
       REWRITE_TAC[REAL_MUL_RZERO; REAL_LE_POW_2]];
       REWRITE_TAC[EXPECTATION_CONST; REAL_POW_MUL] THEN
       SUBGOAL_THEN `sqrt((sn2:num->real) n) pow 2 = sn2 n`
         SUBST1_TAC THENL
       [MATCH_MP_TAC SQRT_POW_2 THEN ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
       REAL_ARITH_TAC]; ALL_TAC] THEN
     ((* E[Xi^2*1_big]/sn2 <= |sum/sn2| *)
     SUBGOAL_THEN
       `expectation p (\x:A. (X:num->A->real) i x pow 2 *
         (if abs (X i x) > eps2 * sqrt ((sn2:num->real) n)
          then &1 else &0)) / sn2 n <=
        abs(sum(0..n) (\i'. expectation p
          (\x:A. (X:num->A->real) i' x pow 2 *
            (if abs(X i' x) > eps2 * sqrt((sn2:num->real) n)
             then &1 else &0))) / sn2 n)` ASSUME_TAC THENL
     [REWRITE_TAC[real_div; REAL_ABS_MUL] THEN
      SUBGOAL_THEN `abs(inv((sn2:num->real) n)) = inv(sn2 n)`
        SUBST1_TAC THENL
      [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN
       MATCH_MP_TAC REAL_LE_INV THEN
       ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN (CONJ_TAC THENL
      [ALL_TAC; MATCH_MP_TAC REAL_LE_INV THEN
       ASM_MESON_TAC[REAL_LT_IMP_LE]]) THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> x <= abs y`) THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC EXPECTATION_POS THEN CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_INDICATOR_WEIGHTED_POW2 THEN
        ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC SQRT_POS_LE THEN
        LOCAL_ASM_REAL_ARITH_TAC;
        GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
        COND_CASES_TAC THEN REAL_ARITH_TAC];
       MATCH_MP_TAC REAL_LE_TRANS THEN
       EXISTS_TAC `sum(0..n) (\i'. expectation p
         (\x:A. (X:num->A->real) i' x pow 2 *
           (if abs(X i' x) > eps2 * sqrt((sn2:num->real) n)
            then &1 else &0)))` THEN
       CONJ_TAC THENL
       [MP_TAC(ISPECL [`\i'. expectation (p:A prob_space)
          (\x:A. (X:num->A->real) i' x pow 2 *
            (if abs(X i' x) > eps2 * sqrt((sn2:num->real) n)
             then &1 else &0))`; `0..n`; `i:num`]
          SUM_DELETE) THEN
        REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
        (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN BETA_TAC THEN
        DISCH_THEN(SUBST1_TAC o
          MATCH_MP REAL_EQ_SUB_RADD) THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= s ==> x <= x + s`) THEN
        MATCH_MP_TAC SUM_POS_LE THEN
        REWRITE_TAC[FINITE_DELETE; FINITE_NUMSEG] THEN
        GEN_TAC THEN STRIP_TAC THEN BETA_TAC THEN
        MATCH_MP_TAC EXPECTATION_POS THEN CONJ_TAC THENL
        [MATCH_MP_TAC INTEGRABLE_INDICATOR_WEIGHTED_POW2 THEN
         ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC REAL_LE_MUL THEN
         ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC SQRT_POS_LE THEN
         LOCAL_ASM_REAL_ARITH_TAC;
         GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
         MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
         COND_CASES_TAC THEN REAL_ARITH_TAC];
        REAL_ARITH_TAC]]; ALL_TAC]) THEN
     GEN_REWRITE_TAC LAND_CONV [real_div] THEN
     REWRITE_TAC[REAL_ADD_RDISTRIB; GSYM real_div] THEN
     MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[]]; ALL_TAC]) THEN
    (* ci = t^2 * sigma_i^2/(2*sn2) < t^2 * inv(2t^2+2) *)
    (*    = t^2/(4t^2+4) <= 1/4 <= 1/2 *)
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `t pow 2 / (&4 * t pow 2 + &4)` THEN
    (CONJ_TAC THENL
    [(* t^2 * E[Xi^2]/(2*sn2) <= t^2/(4t^2+4) *)
     SUBGOAL_THEN `~((sn2:num->real) n = &0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[REAL_LT_IMP_NZ]; ALL_TAC] THEN
     SUBGOAL_THEN `t pow 2 * expectation p
       (\x:A. (X:num->A->real) i x pow 2) / (&2 * (sn2:num->real) n) =
       t pow 2 * (expectation p (\x. X i x pow 2) / sn2 n) / &2`
       SUBST1_TAC THENL
     [UNDISCH_TAC `~((sn2:num->real) n = &0)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
     REWRITE_TAC[real_div; REAL_INV_MUL; GSYM REAL_MUL_ASSOC] THEN
     MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `&2 * inv (&4 * t pow 2 + &4) * inv(&2)` THEN
     CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_MESON_TAC[real_div];
       MATCH_MP_TAC REAL_LE_INV THEN REAL_ARITH_TAC];
      MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= y`) THEN
      CONV_TAC REAL_RING];
     (* t^2/(4t^2+4) <= 1/2 *)
     ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
     MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC]);
    ALL_TAC]) THEN
   (* Take N = max(N1, N2) *)
   EXISTS_TAC `MAX N1 N2` THEN
   X_GEN_TAC `n:num` THEN DISCH_TAC THEN
   (SUBGOAL_THEN `N1 <= n /\ N2 <= (n:num)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC]) THEN
   ((* Key bound: abs(Ln eps n) < delta *)
   SUBGOAL_THEN `abs((Ln:real->num->real) eps n) <
     eta / (&5 * (t pow 2 + t pow 4 + &1))`
     ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
     if free_in `Ln:real->num->real` (concl th)
     then MP_TAC(SPEC `n:num` th)
     else FAIL_TAC "") THEN
    ASM_REWRITE_TAC[ETA_AX]; ALL_TAC]) THEN
   (SUBGOAL_THEN `&0 < eta / (&5 * (t pow 2 + t pow 4 + &1))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
    [REAL_ARITH_TAC;
     MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 < a + b + &1`) THEN
     CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_POW_2];
      REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW;
        REAL_LE_POW_2]]]; ALL_TAC]) THEN
   (* Abbreviate s = t/sqrt(sn2 n) and d = eps * sqrt(sn2 n) *)
   ABBREV_TAC `s = t / sqrt((sn2:num->real) n)` THEN
   ABBREV_TAC `d = eps * sqrt((sn2:num->real) n)` THEN
   (SUBGOAL_THEN `&0 <= (d:real)` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC SQRT_POS_LE THEN
    LOCAL_ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
   (* Abbreviate c_i = t^2 * sigma_i^2 / (2 * sn2) *)
   ABBREV_TAC `ci = \i:num. t pow 2 *
     expectation p (\x:A. (X:num->A->real) i x pow 2) /
       (&2 * (sn2:num->real) n)` THEN
   ((* sum c_i = t^2/2 *)
   SUBGOAL_THEN `sum(0..n) (ci:num->real) = t pow 2 / &2`
     ASSUME_TAC THENL
   [EXPAND_TAC "ci" THEN BETA_TAC THEN
    REWRITE_TAC[real_div] THEN
    (SUBGOAL_THEN `!i. t pow 2 * expectation p
      (\x:A. (X:num->A->real) i x pow 2) * inv(&2 * (sn2:num->real) n) =
      (t pow 2 * inv(&2 * sn2 n)) * expectation p (\x. X i x pow 2)`
      (fun th -> REWRITE_TAC[th]) THENL
    [GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[SUM_LMUL] THEN
    (SUBGOAL_THEN `sum(0..n) (\i. expectation p
      (\x:A. (X:num->A->real) i x pow 2)) = (sn2:num->real) n`
      SUBST1_TAC THENL
    [EXPAND_TAC "sn2" THEN REFL_TAC; ALL_TAC]) THEN
    (SUBGOAL_THEN `~(&2 * (sn2:num->real) n = &0)` ASSUME_TAC THENL
    [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(&2 * x = &0)`) THEN
     ASM_REWRITE_TAC[ETA_AX]; ALL_TAC]) THEN
    (SUBGOAL_THEN `~((sn2:num->real) n = &0)` ASSUME_TAC THENL
    [ASM_MESON_TAC[REAL_LT_IMP_NZ]; ALL_TAC]) THEN
    UNDISCH_TAC `~(&2 * (sn2:num->real) n = &0)` THEN
    CONV_TAC REAL_FIELD; ALL_TAC]) THEN
   ((* 0 <= c_i *)
   SUBGOAL_THEN `!i:num. &0 <= (ci:num->real) i` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "ci" THEN BETA_TAC THEN
    REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
    [REWRITE_TAC[REAL_LE_POW_2];
     MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC EXPECTATION_POS THEN ASM_REWRITE_TAC[ETA_AX] THEN
      SIMP_TAC[REAL_LE_POW_2];
      MATCH_MP_TAC REAL_LE_INV THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 <= &2 * x`) THEN
      ASM_REWRITE_TAC[ETA_AX]]]; ALL_TAC]) THEN
   ((* c_i <= 1/2 for i <= n (from N2 bound) *)
   SUBGOAL_THEN `!i:num. i <= n ==> (ci:num->real) i <= &1 / &2`
     ASSUME_TAC THENL
   [EXPAND_TAC "ci" THEN BETA_TAC THEN ASM_MESON_TAC[]; ALL_TAC]) THEN
   ((* c_i <= 1 for i <= n *)
   SUBGOAL_THEN `!i:num. i <= n ==> (ci:num->real) i <= &1`
     ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 / &2` THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC; ALL_TAC]) THEN
   ((* [A]: |char_fn_re(Y_n, t) - prod r_i| <= sum |s_i| *)
   SUBGOAL_THEN
     `abs(char_fn_re p (\a:A. sum(0..n) (\i. (X:num->A->real) i a))
       (t / sqrt((sn2:num->real) n)) -
       product(0..n) (\i. char_fn_re p (X i) (t / sqrt(sn2 n))))
      <= sum(0..n) (\i. abs(char_fn_im p (X i) (t / sqrt(sn2 n))))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC CHAR_FN_SUM_RE_PRODUCT_BOUND THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC]) THEN
   ((* [B]: |prod r_i - prod(1-c_i)| <= sum |r_i - (1-c_i)| *)
   SUBGOAL_THEN
     `abs(product(0..n) (\i. char_fn_re p ((X:num->A->real) i)
       (t / sqrt((sn2:num->real) n))) -
       product(0..n) (\i. &1 - (ci:num->real) i))
      <= sum(0..n) (\i. abs(char_fn_re p (X i) (t / sqrt(sn2 n)) -
                             (&1 - ci i)))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC PRODUCT_DIFF_SUM_BOUND THEN CONJ_TAC THENL
    [GEN_TAC THEN DISCH_TAC THEN
     MATCH_MP_TAC CHAR_FN_RE_BOUND THEN ASM_REWRITE_TAC[ETA_AX];
     GEN_TAC THEN DISCH_TAC THEN
     REWRITE_TAC[REAL_ABS_BOUNDS] THEN
     ASM_SIMP_TAC[REAL_ARITH `&0 <= c /\ c <= &1 ==>
       -- &1 <= &1 - c /\ &1 - c <= &1`]]; ALL_TAC]) THEN
   ((* [C]: |prod(1-c_i) - exp(-t^2/2)| by squeeze *)
   SUBGOAL_THEN
     `abs(product(0..n) (\i. &1 - (ci:num->real) i) -
       exp(--(t pow 2 / &2))) < eta / &5`
     ASSUME_TAC THENL
   [(SUBGOAL_THEN
      `product(0..n) (\i. &1 - (ci:num->real) i) <=
       exp(--(sum(0..n) ci))`
      ASSUME_TAC THENL
    [MATCH_MP_TAC PRODUCT_1_MINUS_LE_EXP THEN
     GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[]; ALL_TAC]) THEN
    SUBGOAL_THEN
      `exp(--(sum(0..n) (ci:num->real) / (&1 - &1 / &2))) <=
       product(0..n) (\i. &1 - ci i)`
      ASSUME_TAC THENL
    [MATCH_MP_TAC EXP_LE_PRODUCT_1_MINUS THEN CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[]; REAL_ARITH_TAC];
     ALL_TAC] THEN
    ASM_REWRITE_TAC[ETA_AX] THEN
    (SUBGOAL_THEN `sum(0..n) (ci:num->real) / (&1 - &1 / &2) =
      t pow 2` SUBST1_TAC THENL
    [ASM_REWRITE_TAC[ETA_AX] THEN
     CONV_TAC REAL_FIELD; ALL_TAC]) THEN
    ((* prod(1-c_i) is between exp(-t^2) and exp(-t^2/2) *)
    (* so |prod - exp(-t^2/2)| = exp(-t^2/2) - prod <= exp(-t^2/2) - exp(-t^2) *)
    SUBGOAL_THEN
      `exp(--(t pow 2)) <=
       product(0..n) (\i. &1 - (ci:num->real) i) /\
       product(0..n) (\i. &1 - ci i) <= exp(--(t pow 2 / &2))`
      STRIP_ASSUME_TAC THENL
    [CONJ_TAC THENL
     [UNDISCH_TAC `exp (--(sum (0..n) (ci:num->real) / (&1 - &1 / &2))) <=
       product (0..n) (\i. &1 - ci i)` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= p ==> b <= p`) THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC REAL_FIELD;
      UNDISCH_TAC `product (0..n) (\i. &1 - (ci:num->real) i) <=
       exp (--sum (0..n) ci)` THEN
      ASM_REWRITE_TAC[]]; ALL_TAC]) THEN
    (* Two cases based on eta *)
    (ASM_CASES_TAC `&2 <= eta` THENL
    [(* Case eta >= 2: gap <= u(1-u) <= 1/4 < eta/5 *)
     MATCH_MP_TAC REAL_LET_TRANS THEN
     EXISTS_TAC `exp(--(t pow 2 / &2)) - exp(--(t pow 2))` THEN
     (CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
       `el <= p /\ p <= eh ==> abs(p - eh) <= eh - el`) THEN
      ASM_REWRITE_TAC[ETA_AX]; ALL_TAC]) THEN
     SUBGOAL_THEN `exp(--(t pow 2)) = exp(--(t pow 2 / &2)) pow 2`
       SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_N] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
     ABBREV_TAC `u = exp(--(t pow 2 / &2))` THEN
     MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&1 / &4` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
       `u * (&1 - u) <= &1 / &4 ==> u - u pow 2 <= &1 / &4`) THEN
      MATCH_MP_TAC(REAL_ARITH
        `&0 <= (u - &1 / &2) pow 2 ==> u * (&1 - u) <= &1 / &4`) THEN
      REWRITE_TAC[REAL_LE_POW_2];
      LOCAL_ASM_REAL_ARITH_TAC]; ALL_TAC]) THEN
    ((* Case eta < 2: tighter squeeze via Lindeberg *)
    (* Convert abs(p - eh) to eh - p since p <= eh *)
    MATCH_MP_TAC(REAL_ARITH
      `p <= eh /\ eh - p < e ==> abs(p - eh) < e`) THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
    (* Step 1: Bound each ci tightly *)
    SUBGOAL_THEN `!i:num. i <= n ==> (ci:num->real) i <=
      t pow 2 * (eps pow 2 + abs((Ln:real->num->real) eps n)) / &2`
      ASSUME_TAC THENL
    [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
     EXPAND_TAC "ci" THEN BETA_TAC THEN
     REWRITE_TAC[real_div] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `t pow 2 *
       ((eps pow 2 + abs((Ln:real->num->real) eps n)) *
        (sn2:num->real) n) * inv(&2 * sn2 n)` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN (CONJ_TAC THENL
      [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC]) THEN
      W(fun (_,w) ->
        let l = rand(rator w) in
        let r = rand w in
        let x = rand(rator l) in
        let z = rand l in
        let y = rand(rator r) in
        MP_TAC(SPECL [x; y; z] REAL_LE_RMUL)) THEN
      ANTS_TAC THENL
      [CONJ_TAC THENL
       [ALL_TAC;
        ASM_MESON_TAC[REAL_LE_INV; REAL_LT_IMP_LE;
          REAL_ARITH `&0 < x ==> &0 <= &2 * x`]];
       DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
      ((* E[Xi^2] <= (eps^2 + |Ln|) * sn2 *)
      SUBGOAL_THEN `expectation p (\x:A. (X:num->A->real) i x pow 2) =
        expectation p (\x. X i x pow 2 *
          (if abs(X i x) <= eps * sqrt((sn2:num->real) n)
           then &1 else &0)) +
        expectation p (\x. X i x pow 2 *
          (if abs(X i x) > eps * sqrt(sn2 n)
           then &1 else &0))` SUBST1_TAC THENL
      [(SUBGOAL_THEN `(\x:A. (X:num->A->real) i x pow 2) =
        (\x. X i x pow 2 *
          (if abs(X i x) <= eps * sqrt((sn2:num->real) n)
           then &1 else &0) +
         X i x pow 2 *
          (if abs(X i x) > eps * sqrt(sn2 n)
           then &1 else &0))` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN BETA_TAC THEN
        REWRITE_TAC[real_gt] THEN REAL_ARITH_TAC; ALL_TAC]) THEN
       MATCH_MP_TAC EXPECTATION_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_INDICATOR_WEIGHTED_POW2_LE THEN
        ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC SQRT_POS_LE THEN
        LOCAL_ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC INTEGRABLE_INDICATOR_WEIGHTED_POW2 THEN
        ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC SQRT_POS_LE THEN
        LOCAL_ASM_REAL_ARITH_TAC]; ALL_TAC]) THEN
      REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
      [(* E[Xi^2 * I_small] <= eps^2 * sn2 *)
       MATCH_MP_TAC REAL_LE_TRANS THEN
       EXISTS_TAC `expectation p
         (\x:A. (eps * sqrt((sn2:num->real) n)) pow 2)` THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC EXPECTATION_MONO THEN CONJ_TAC THENL
        [MATCH_MP_TAC INTEGRABLE_INDICATOR_WEIGHTED_POW2_LE THEN
         ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC REAL_LE_MUL THEN
         ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC SQRT_POS_LE THEN
         LOCAL_ASM_REAL_ARITH_TAC;(
         CONJ_TAC THENL [REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC]) THEN
         X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
         COND_CASES_TAC THENL
         [REWRITE_TAC[REAL_MUL_RID] THEN
          MATCH_MP_TAC REAL_POW2_ABS_LE THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[REAL_MUL_RZERO; REAL_LE_POW_2]]];
        REWRITE_TAC[EXPECTATION_CONST; REAL_POW_MUL] THEN
        SUBGOAL_THEN `sqrt((sn2:num->real) n) pow 2 = sn2 n`
          SUBST1_TAC THENL
        [MATCH_MP_TAC SQRT_POW_2 THEN ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
        REAL_ARITH_TAC];
       (* E[Xi^2 * I_big] <= |Ln|*sn2 n *)
       MATCH_MP_TAC REAL_LE_TRANS THEN
       EXISTS_TAC `sum(0..n) (\j. expectation (p:A prob_space)
         (\x:A. (X:num->A->real) j x pow 2 *
           (if abs(X j x) > eps * sqrt((sn2:num->real) n)
            then &1 else &0)))` THEN
       CONJ_TAC THENL
       [(* E_big_i <= sum(0..n) E_j_big *)
        MP_TAC(ISPECL [`\j. expectation (p:A prob_space)
          (\x:A. (X:num->A->real) j x pow 2 *
            (if abs(X j x) > eps * sqrt((sn2:num->real) n)
             then &1 else &0))`; `0..n`; `i:num`] SUM_DELETE) THEN
        REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
        (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN BETA_TAC THEN
        DISCH_THEN(SUBST1_TAC o
          MATCH_MP REAL_EQ_SUB_RADD) THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= s ==> x <= x + s`) THEN
        MATCH_MP_TAC SUM_POS_LE THEN
        REWRITE_TAC[FINITE_DELETE; FINITE_NUMSEG] THEN
        GEN_TAC THEN STRIP_TAC THEN BETA_TAC THEN
        MATCH_MP_TAC EXPECTATION_POS THEN CONJ_TAC THENL
        [MATCH_MP_TAC INTEGRABLE_INDICATOR_WEIGHTED_POW2 THEN
         ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC REAL_LE_MUL THEN
         ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC SQRT_POS_LE THEN
         LOCAL_ASM_REAL_ARITH_TAC;
         GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
         MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
         COND_CASES_TAC THEN REAL_ARITH_TAC];
        (* sum(0..n) E_j_big <= |Ln|*sn2 n *)
        EXPAND_TAC "Ln" THEN BETA_TAC THEN
        (SUBGOAL_THEN `~((sn2:num->real) n = &0)` ASSUME_TAC THENL
        [ASM_MESON_TAC[REAL_LT_IMP_NZ]; ALL_TAC]) THEN
        (SUBGOAL_THEN `&0 <= sum(0..n) (\j. expectation p
          (\x:A. (X:num->A->real) j x pow 2 *
            (if abs(X j x) > eps * sqrt((sn2:num->real) n)
             then &1 else &0)))` ASSUME_TAC THENL
        [MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
         GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
         MATCH_MP_TAC EXPECTATION_POS THEN CONJ_TAC THENL
         [MATCH_MP_TAC INTEGRABLE_INDICATOR_WEIGHTED_POW2 THEN
          ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC REAL_LE_MUL THEN
          ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC SQRT_POS_LE THEN
          LOCAL_ASM_REAL_ARITH_TAC;
          GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
          MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
          COND_CASES_TAC THEN REAL_ARITH_TAC]; ALL_TAC]) THEN
        (SUBGOAL_THEN `&0 <= sum(0..n) (\j. expectation p
          (\x:A. (X:num->A->real) j x pow 2 *
            (if abs(X j x) > eps * sqrt((sn2:num->real) n)
             then &1 else &0))) / sn2 n` MP_TAC THENL
        [MATCH_MP_TAC REAL_LE_DIV THEN
         ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC]) THEN
        DISCH_THEN(SUBST1_TAC o MATCH_MP(REAL_ARITH
          `&0 <= x ==> abs x = x`)) THEN
        MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= y`) THEN
        UNDISCH_TAC `~((sn2:num->real) n = &0)` THEN
        CONV_TAC REAL_FIELD]];
      (* C2: (eps^2+|Ln|)*sn2*inv(2*sn2) = (eps^2+|Ln|)*inv(2) *)
      MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= y`) THEN
      (SUBGOAL_THEN `~(&2 * (sn2:num->real) n = &0)` ASSUME_TAC THENL
      [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(&2 * x = &0)`) THEN
       ASM_REWRITE_TAC[ETA_AX]; ALL_TAC]) THEN
      (SUBGOAL_THEN `~((sn2:num->real) n = &0)` ASSUME_TAC THENL
      [ASM_MESON_TAC[REAL_LT_IMP_NZ]; ALL_TAC]) THEN
      UNDISCH_TAC `~(&2 * (sn2:num->real) n = &0)` THEN
      UNDISCH_TAC `~((sn2:num->real) n = &0)` THEN
      CONV_TAC REAL_FIELD]; ALL_TAC]) THEN
    (* Step 2: Let delta' = t^2*(eps^2+|Ln|)/2 *)
    ABBREV_TAC `delta' = t pow 2 *
      (eps pow 2 + abs((Ln:real->num->real) eps n)) / &2` THEN
    SUBGOAL_THEN `&0 <= delta'` ASSUME_TAC THENL
    [EXPAND_TAC "delta'" THEN MATCH_MP_TAC REAL_LE_MUL THEN
     CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_POW_2];
      MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_ADD THEN
       REWRITE_TAC[REAL_LE_POW_2; REAL_ABS_POS];
       REAL_ARITH_TAC]]; ALL_TAC] THEN
    ((* Step 3: Show delta' < 1/2 *)
    SUBGOAL_THEN `delta' < &1 / &2` ASSUME_TAC THENL
    [EXPAND_TAC "delta'" THEN
     MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `eta / &5` THEN
     CONJ_TAC THENL [ALL_TAC; LOCAL_ASM_REAL_ARITH_TAC] THEN
     (* Bound eps^2 by eps *)
     MATCH_MP_TAC REAL_LET_TRANS THEN
     EXISTS_TAC `t pow 2 * (eps + abs((Ln:real->num->real) eps n)) / &2` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
      [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
      SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ARITH `&0 < &2`] THEN
      MATCH_MP_TAC(REAL_ARITH `a <= b ==> a + c <= b + c`) THEN
      REWRITE_TAC[REAL_POW_2] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
     (* Split into t^2*eps/2 + t^2*|Ln|/2 *)
     SUBGOAL_THEN `t pow 2 * (eps +
       abs((Ln:real->num->real) eps n)) / &2 =
       t pow 2 * eps / &2 +
       t pow 2 * abs((Ln:real->num->real) eps n) / &2` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `eta / &5 = eta / &10 + eta / &10` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
     MATCH_MP_TAC REAL_LTE_ADD2 THEN CONJ_TAC THENL
     [(* t^2 * eps / 2 < eta/10 *)
      (SUBGOAL_THEN
        `eps <= eta / (&5 * (abs(t:real) pow 3 + t pow 4 + &1))`
        ASSUME_TAC THENL
      [EXPAND_TAC "eps" THEN REAL_ARITH_TAC; ALL_TAC]) THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `t pow 2 *
        (eta / (&5 * (abs(t:real) pow 3 + t pow 4 + &1))) / &2` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
       SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ARITH `&0 < &2`] THEN
       ASM_REWRITE_TAC[]; ALL_TAC] THEN
      (SUBGOAL_THEN `&0 < abs(t:real) pow 3 + t pow 4 + &1`
        ASSUME_TAC THENL
      [MATCH_MP_TAC(REAL_ARITH
        `&0 <= a /\ &0 <= b ==> &0 < a + b + &1`) THEN
       CONJ_TAC THENL
       [SIMP_TAC[REAL_POW_LE; REAL_ABS_POS];
        REWRITE_TAC[ARITH_RULE `4 = 2 * 2`;
          GSYM REAL_POW_POW; REAL_LE_POW_2]]; ALL_TAC]) THEN
      SUBGOAL_THEN
        `t pow 2 * eta /
          (&5 * (abs(t:real) pow 3 + t pow 4 + &1)) / &2 =
         (eta / &10) *
          (t pow 2 / (abs t pow 3 + t pow 4 + &1))`
        SUBST1_TAC THENL
      [UNDISCH_TAC `&0 < abs(t:real) pow 3 + t pow 4 + &1` THEN
       CONV_TAC REAL_FIELD; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LT_DIV THEN LOCAL_ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REWRITE_TAC[REAL_MUL_LID] THEN
      SUBGOAL_THEN `t pow 2 = abs(t:real) pow 2` SUBST1_TAC THENL
      [REWRITE_TAC[REAL_POW2_ABS]; ALL_TAC] THEN
      ASM_CASES_TAC `&1 <= abs(t:real)` THENL
      [MATCH_MP_TAC(REAL_ARITH
        `a <= b /\ &0 <= c ==> a < b + c + &1`) THEN
       CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `3 = SUC 2`; real_pow] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
        [ASM_REWRITE_TAC[]; REWRITE_TAC[REAL_LE_POW_2]];
        REWRITE_TAC[ARITH_RULE `4 = 2 * 2`;
          GSYM REAL_POW_POW; REAL_LE_POW_2]];
       MATCH_MP_TAC(REAL_ARITH
        `a < &1 /\ &0 <= b /\ &0 <= c ==> a < b + c + &1`) THEN
       REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_1_LT THEN
        REWRITE_TAC[REAL_ABS_POS; ARITH_RULE `~(2 = 0)`] THEN
        LOCAL_ASM_REAL_ARITH_TAC;
        SIMP_TAC[REAL_POW_LE; REAL_ABS_POS];
        REWRITE_TAC[ARITH_RULE `4 = 2 * 2`;
          GSYM REAL_POW_POW; REAL_LE_POW_2]]];
      (* t^2 * |Ln| / 2 <= eta/10 *)
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `t pow 2 *
        (eta / (&5 * (t pow 2 + t pow 4 + &1))) / &2` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
       SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ARITH `&0 < &2`] THEN
       MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
      (SUBGOAL_THEN `&0 < t pow 2 + t pow 4 + &1` ASSUME_TAC THENL
      [MATCH_MP_TAC(REAL_ARITH
        `&0 <= a /\ &0 <= b ==> &0 < a + b + &1`) THEN
       CONJ_TAC THENL
       [REWRITE_TAC[REAL_LE_POW_2];
        REWRITE_TAC[ARITH_RULE `4 = 2 * 2`;
          GSYM REAL_POW_POW; REAL_LE_POW_2]]; ALL_TAC]) THEN
      SUBGOAL_THEN
        `t pow 2 * eta /
          (&5 * (t pow 2 + t pow 4 + &1)) / &2 =
         (eta / &10) *
          (t pow 2 / (t pow 2 + t pow 4 + &1))`
        SUBST1_TAC THENL
      [UNDISCH_TAC `&0 < t pow 2 + t pow 4 + &1` THEN
       CONV_TAC REAL_FIELD; ALL_TAC] THEN
      SUBGOAL_THEN
        `t pow 2 / (t pow 2 + t pow 4 + &1) <= &1`
        ASSUME_TAC THENL
      [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REWRITE_TAC[REAL_MUL_LID] THEN
       MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> b <= b + a + &1`) THEN
       REWRITE_TAC[ARITH_RULE `4 = 2 * 2`;
         GSYM REAL_POW_POW; REAL_LE_POW_2]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `eta / &10 * &1` THEN CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [LOCAL_ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
       REAL_ARITH_TAC]]; ALL_TAC]) THEN
    ((* Step 4: Apply EXP_LE_PRODUCT_1_MINUS with delta' *)
    SUBGOAL_THEN `exp(--(sum(0..n) (ci:num->real) / (&1 - delta'))) <=
      product(0..n) (\i. &1 - ci i)` ASSUME_TAC THENL
    [MATCH_MP_TAC EXP_LE_PRODUCT_1_MINUS THEN CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `delta':real` THEN
      ASM_SIMP_TAC[];
      LOCAL_ASM_REAL_ARITH_TAC]; ALL_TAC]) THEN
    ((* Simplify: sum/(1-delta') = t^2/(2*(1-delta')) *)
    SUBGOAL_THEN `sum(0..n) (ci:num->real) / (&1 - delta') =
      t pow 2 / (&2 * (&1 - delta'))` SUBST_ALL_TAC THENL
    [ASM_REWRITE_TAC[ETA_AX] THEN
     SUBGOAL_THEN `~(&1 - delta' = &0)` MP_TAC THENL
     [LOCAL_ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]; ALL_TAC]) THEN
    (* Transit: use product >= exp(-t^2/(2(1-d'))) *)
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `exp(--(t pow 2 / &2)) -
      exp(--(t pow 2 / (&2 * (&1 - delta'))))` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC(REAL_ARITH `a <= p ==> e - p <= e - a`) THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
    (* Step 5: Bound exp(-t^2/2)-exp(-t^2/(2(1-d'))) via EXP_DIFF_LE *)
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `(t:real) pow 2 * (delta':real)` THEN
    (CONJ_TAC THENL
    [(* exp(-t^2/2) - exp(-t^2/(2(1-d'))) <= t^2*d' *)
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `t pow 2 / (&2 * (&1 - delta')) - t pow 2 / &2` THEN
     (CONJ_TAC THENL
     [(* exp(-a) - exp(-b) <= b - a *)
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `exp(--(t pow 2 / &2)) *
        (t pow 2 / (&2 * (&1 - delta')) - t pow 2 / &2)` THEN
      (CONJ_TAC THENL
      [(SUBGOAL_THEN `exp(--(t pow 2 / (&2 * (&1 - delta')))) =
         exp(--((t pow 2 / &2) +
           (t pow 2 / (&2 * (&1 - delta')) - t pow 2 / &2)))`
         SUBST1_TAC THENL
        [AP_TERM_TAC THEN SUBGOAL_THEN `~(&1 - delta' = &0)` MP_TAC THENL
         [LOCAL_ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]; ALL_TAC]) THEN
        MP_TAC(SPECL [`t pow 2 / &2`;
          `t pow 2 / (&2 * (&1 - delta')) - t pow 2 / &2`]
          EXP_DIFF_LE) THEN
        REWRITE_TAC[]; ALL_TAC]) THEN
      (* exp(-t^2/2) * y <= 1 * y *)
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&1 * (t pow 2 / (&2 * (&1 - delta')) -
        t pow 2 / &2)` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM REAL_EXP_0; REAL_EXP_MONO_LE] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> --(x / &2) <= &0`) THEN
        REWRITE_TAC[REAL_LE_POW_2];
        (SUBGOAL_THEN `t pow 2 / &2 <=
         t pow 2 / (&2 * (&1 - delta'))` MP_TAC THENL
        [REWRITE_TAC[real_div] THEN
         MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
         MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
         [LOCAL_ASM_REAL_ARITH_TAC; LOCAL_ASM_REAL_ARITH_TAC]; ALL_TAC]) THEN
        REAL_ARITH_TAC]; REAL_ARITH_TAC]; ALL_TAC]) THEN
    ((* t^2/(2(1-d))-t^2/2 = t^2*d/(2(1-d)) <= t^2*d *)
    SUBGOAL_THEN `~(&1 - delta' = &0)` ASSUME_TAC THENL
    [LOCAL_ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    SUBGOAL_THEN `t pow 2 / (&2 * (&1 - delta')) - t pow 2 / &2 =
      t pow 2 * delta' / (&2 * (&1 - delta'))` SUBST1_TAC THENL
    [UNDISCH_TAC `~(&1 - delta' = &0)` THEN CONV_TAC REAL_FIELD;
     ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN (CONJ_TAC THENL
    [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC]) THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [EXPAND_TAC "delta'" THEN MATCH_MP_TAC REAL_LE_MUL THEN
     REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_LE_DIV THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN
      REWRITE_TAC[REAL_LE_POW_2; REAL_ABS_POS];
      REAL_ARITH_TAC];
     MATCH_MP_TAC REAL_INV_LE_1 THEN LOCAL_ASM_REAL_ARITH_TAC]; ALL_TAC]) THEN
    (* Step 6: t^2*delta' = t^4*(eps^2+|Ln|)/2 < eta/4 *)
    EXPAND_TAC "delta'" THEN
    (SUBGOAL_THEN `t pow 2 * (t pow 2 *
      (eps pow 2 + abs((Ln:real->num->real) eps n)) / &2) =
      t pow 4 * eps pow 2 / &2 +
      t pow 4 * abs(Ln eps n) / &2`
      SUBST1_TAC THENL
    [REWRITE_TAC[ARITH_RULE `4 = 2 + 2`; REAL_POW_ADD] THEN
     REAL_ARITH_TAC; ALL_TAC]) THEN
    SUBGOAL_THEN `eta / &5 = &2 * (eta / &10)` SUBST1_TAC THENL
    [CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a < e /\ b < e ==> a + b < &2 * e`) THEN
    (CONJ_TAC THENL
    [(* t^4*eps^2/2 < eta/8 *)
     MATCH_MP_TAC REAL_LET_TRANS THEN
     EXISTS_TAC `t pow 4 * eps / &2` THEN (CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN (CONJ_TAC THENL
      [REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW;
        REAL_LE_POW_2]; ALL_TAC]) THEN
      REWRITE_TAC[real_div] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN (CONJ_TAC THENL
      [ALL_TAC; MATCH_MP_TAC REAL_LE_INV THEN REAL_ARITH_TAC]) THEN
      REWRITE_TAC[ARITH_RULE `2 = 1 + 1`; REAL_POW_ADD; REAL_POW_1] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN LOCAL_ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
     MATCH_MP_TAC REAL_LET_TRANS THEN
     EXISTS_TAC `t pow 4 *
       eta / (&5 * (abs(t:real) pow 3 + t pow 4 + &1)) / &2` THEN
     (CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN (CONJ_TAC THENL
      [REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW;
        REAL_LE_POW_2]; ALL_TAC]) THEN
      SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ARITH `&0 < &2`] THEN
      EXPAND_TAC "eps" THEN REWRITE_TAC[REAL_MIN_LE] THEN DISJ2_TAC THEN
      REAL_ARITH_TAC; ALL_TAC]) THEN
     (SUBGOAL_THEN `&0 < abs(t:real) pow 3 + t pow 4 + &1` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
       `&0 <= a /\ &0 <= b ==> &0 < a + b + &1`) THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
       REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW;
         REAL_LE_POW_2]]; ALL_TAC]) THEN
     (SUBGOAL_THEN `~(abs(t:real) pow 3 + t pow 4 + &1 = &0)` ASSUME_TAC THENL
     [LOCAL_ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
     (SUBGOAL_THEN `t pow 4 *
       eta / (&5 * (abs(t:real) pow 3 + t pow 4 + &1)) / &2 =
       (eta / &10) * (t pow 4 / (abs t pow 3 + t pow 4 + &1))`
       SUBST1_TAC THENL
     [UNDISCH_TAC `~(abs(t:real) pow 3 + t pow 4 + &1 = &0)` THEN
      CONV_TAC REAL_FIELD; ALL_TAC]) THEN
     GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
     MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
     [LOCAL_ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REWRITE_TAC[REAL_MUL_LID] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= b ==> a < b + a + &1`) THEN
      MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC];
     (* t^4*|Ln|/2 < eta/8 *)
     MATCH_MP_TAC REAL_LET_TRANS THEN
     EXISTS_TAC `t pow 4 *
       eta / (&5 * (t pow 2 + t pow 4 + &1)) / &2` THEN
     (CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN (CONJ_TAC THENL
      [REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW;
        REAL_LE_POW_2]; ALL_TAC]) THEN
      SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ARITH `&0 < &2`] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC]) THEN
     (SUBGOAL_THEN `&0 < t pow 2 + t pow 4 + &1` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
       `&0 <= a /\ &0 <= b ==> &0 < a + b + &1`) THEN
      CONJ_TAC THEN REWRITE_TAC[ARITH_RULE `4 = 2 * 2`;
        GSYM REAL_POW_POW; REAL_LE_POW_2]; ALL_TAC]) THEN
     (SUBGOAL_THEN `~(t pow 2 + t pow 4 + &1 = &0)` ASSUME_TAC THENL
     [LOCAL_ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
     (SUBGOAL_THEN `t pow 4 *
       eta / (&5 * (t pow 2 + t pow 4 + &1)) / &2 =
       (eta / &10) * (t pow 4 / (t pow 2 + t pow 4 + &1))`
       SUBST1_TAC THENL
     [UNDISCH_TAC `~(t pow 2 + t pow 4 + &1 = &0)` THEN
      CONV_TAC REAL_FIELD; ALL_TAC]) THEN
     GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
     MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
     [LOCAL_ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REWRITE_TAC[REAL_MUL_LID] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= b ==> a < b + a + &1`) THEN
      REWRITE_TAC[REAL_LE_POW_2]]]);
    ALL_TAC]) THEN
   (* Bound sum |s_i| *)
   SUBGOAL_THEN
     `sum(0..n) (\i. abs(char_fn_im p ((X:num->A->real) i)
       (t / sqrt((sn2:num->real) n)))) < eta / &5 + eta / &5`
     ASSUME_TAC THENL
   [(* Gap 2: sum |char_fn_im(Xi, s)| < eta/4 + eta/4 *)
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `sum(0..n) (\i.
      abs(t / sqrt((sn2:num->real) n)) pow 3 *
        (eps * sqrt(sn2 n)) *
        expectation p (\x:A. (X:num->A->real) i x pow 2) / &2 +
      (t / sqrt(sn2 n)) pow 2 *
        expectation p (\x. X i x pow 2 *
          (if abs(X i x) > eps * sqrt(sn2 n) then &1 else &0)))` THEN
    (CONJ_TAC THENL
    [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
     BETA_TAC THEN
     MATCH_MP_TAC CHAR_FN_IM_COMPONENT_BOUND THEN
     ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC SQRT_POS_LE THEN LOCAL_ASM_REAL_ARITH_TAC]; ALL_TAC]) THEN
    REWRITE_TAC[SUM_ADD_NUMSEG] THEN
    (SUBGOAL_THEN `sum(0..n) (\i.
      abs(t / sqrt((sn2:num->real) n)) pow 3 *
        (eps * sqrt(sn2 n)) *
        expectation p (\x:A. (X:num->A->real) i x pow 2) / &2) =
      abs t pow 3 * eps / &2`
      SUBST1_TAC THENL
    [(SUBGOAL_THEN `!i. abs(t / sqrt((sn2:num->real) n)) pow 3 *
      (eps * sqrt(sn2 n)) *
      expectation p (\x:A. (X:num->A->real) i x pow 2) / &2 =
      (abs(t / sqrt(sn2 n)) pow 3 * (eps * sqrt(sn2 n)) / &2) *
      expectation p (\x. X i x pow 2)` (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC]) THEN
     REWRITE_TAC[SUM_LMUL] THEN
     (SUBGOAL_THEN `sum(0..n) (\i. expectation p
       (\x:A. (X:num->A->real) i x pow 2)) = (sn2:num->real) n`
       SUBST1_TAC THENL
     [EXPAND_TAC "sn2" THEN REFL_TAC; ALL_TAC]) THEN
     MP_TAC(SPECL [`t:real`; `sqrt((sn2:num->real) n)`; `eps:real`]
       (prove(`!t c e. &0 < c ==>
         abs(t / c) pow 3 * e * c * c pow 2 / &2 =
         abs(t) pow 3 * e / &2`,
        REPEAT STRIP_TAC THEN
        REWRITE_TAC[REAL_ABS_DIV; REAL_POW_DIV] THEN
        (SUBGOAL_THEN `abs c = c` SUBST1_TAC THENL
        [LOCAL_ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
        (SUBGOAL_THEN `~(c = &0)` ASSUME_TAC THENL
        [LOCAL_ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
        SUBGOAL_THEN `~(c pow 3 = &0)` MP_TAC THENL
        [REWRITE_TAC[REAL_POW_EQ_0] THEN ASM_ARITH_TAC;
         CONV_TAC REAL_FIELD]))) THEN
     ASM_REWRITE_TAC[ETA_AX] THEN DISCH_TAC THEN
     (SUBGOAL_THEN `sqrt((sn2:num->real) n) pow 2 = sn2 n`
       SUBST1_TAC THENL
     [MATCH_MP_TAC SQRT_POW_2 THEN ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC]) THEN
     ASM_REWRITE_TAC[ETA_AX] THEN
     EXPAND_TAC "s" THEN EXPAND_TAC "d" THEN
     REWRITE_TAC[REAL_ABS_DIV; REAL_POW_DIV] THEN
     (SUBGOAL_THEN `abs(sqrt((sn2:num->real) n)) = sqrt(sn2 n)`
       SUBST1_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN
      MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      ASM_REWRITE_TAC[ETA_AX]; ALL_TAC]) THEN
     (SUBGOAL_THEN `sqrt((sn2:num->real) n) pow 2 = sn2 n` MP_TAC THENL
     [MATCH_MP_TAC SQRT_POW_2 THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      ASM_REWRITE_TAC[ETA_AX]; ALL_TAC]) THEN
     (SUBGOAL_THEN `~(sqrt((sn2:num->real) n) = &0)` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC]) THEN
     CONV_TAC REAL_FIELD; ALL_TAC]) THEN
    (SUBGOAL_THEN `sum(0..n) (\i.
      (t / sqrt((sn2:num->real) n)) pow 2 *
        expectation p (\x:A. (X:num->A->real) i x pow 2 *
          (if abs(X i x) > eps * sqrt(sn2 n) then &1 else &0))) =
      t pow 2 * (sum(0..n) (\i. expectation p (\x. X i x pow 2 *
        (if abs(X i x) > eps * sqrt(sn2 n)
         then &1 else &0))) / sn2 n)`
      SUBST1_TAC THENL
    [(SUBGOAL_THEN `!i. (t / sqrt((sn2:num->real) n)) pow 2 *
      expectation p (\x:A. (X:num->A->real) i x pow 2 *
        (if abs(X i x) > eps * sqrt(sn2 n) then &1 else &0)) =
      (t pow 2 / (sn2 n)) *
      expectation p (\x. X i x pow 2 *
        (if abs(X i x) > eps * sqrt(sn2 n) then &1 else &0))`
      (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[REAL_POW_DIV] THEN
      (SUBGOAL_THEN `sqrt((sn2:num->real) n) pow 2 = sn2 n`
        SUBST1_TAC THENL
      [MATCH_MP_TAC SQRT_POW_2 THEN ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC]) THEN
      REFL_TAC; ALL_TAC]) THEN
     REWRITE_TAC[SUM_LMUL] THEN
     (SUBGOAL_THEN `~((sn2:num->real) n = &0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[REAL_LT_IMP_NZ]; ALL_TAC]) THEN
     UNDISCH_TAC `~((sn2:num->real) n = &0)` THEN
     CONV_TAC REAL_FIELD; ALL_TAC]) THEN
    (SUBGOAL_THEN `sum(0..n) (\i. expectation p
      (\x:A. (X:num->A->real) i x pow 2 *
        (if abs(X i x) > eps * sqrt((sn2:num->real) n)
         then &1 else &0))) / sn2 n = (Ln:real->num->real) eps n`
      SUBST1_TAC THENL
    [EXPAND_TAC "Ln" THEN BETA_TAC THEN REFL_TAC; ALL_TAC]) THEN
    MATCH_MP_TAC(REAL_ARITH
      `a < e /\ &0 <= b /\ b < e ==> a + b < e + e`) THEN
    ASM_REWRITE_TAC[ETA_AX] THEN (CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
     EXPAND_TAC "Ln" THEN BETA_TAC THEN
     MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC EXPECTATION_POS THEN CONJ_TAC THENL
      [MATCH_MP_TAC INTEGRABLE_INDICATOR_WEIGHTED_POW2 THEN
       ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC REAL_LE_MUL THEN
       ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC SQRT_POS_LE THEN
       LOCAL_ASM_REAL_ARITH_TAC;
       GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
       MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
       COND_CASES_TAC THEN REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[ETA_AX]];
     ALL_TAC]) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `t pow 2 * abs((Ln:real->num->real) eps n)` THEN
    (CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
     REAL_ARITH_TAC; ALL_TAC]) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `t pow 2 * eta / (&5 * (t pow 2 + t pow 4 + &1))` THEN
    (CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
     MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC]) THEN
    (SUBGOAL_THEN `&0 < t pow 2 + t pow 4 + &1` ASSUME_TAC THENL
    [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 < a + b + &1`) THEN
     CONJ_TAC THEN
     REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW;
       REAL_LE_POW_2]; ALL_TAC]) THEN
    (SUBGOAL_THEN `~(t pow 2 + t pow 4 + &1 = &0)` ASSUME_TAC THENL
    [LOCAL_ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    (SUBGOAL_THEN `t pow 2 * eta / (&5 * (t pow 2 + t pow 4 + &1)) =
      (eta / &5) * (t pow 2 / (t pow 2 + t pow 4 + &1))` SUBST1_TAC THENL
    [UNDISCH_TAC `~(t pow 2 + t pow 4 + &1 = &0)` THEN
     CONV_TAC REAL_FIELD; ALL_TAC]) THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
    [LOCAL_ASM_REAL_ARITH_TAC;
     ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REWRITE_TAC[REAL_MUL_LID] THEN
     MATCH_MP_TAC(REAL_ARITH `&0 <= b ==> a < a + b + &1`) THEN
     REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW;
       REAL_LE_POW_2]];
    ALL_TAC] THEN
   (* Bound sum |r_i - (1-c_i)| *)
   SUBGOAL_THEN
     `sum(0..n) (\i. abs(char_fn_re p ((X:num->A->real) i)
       (t / sqrt((sn2:num->real) n)) - (&1 - (ci:num->real) i))) <
      eta / &5 + eta / &5`
     ASSUME_TAC THENL
   [((* Gap 3 proof: sum |char_fn_re(X_i, s) - (1 - ci i)| < eta/4 + eta/4 *)
   (* Step 1: Remove abs by showing char_fn_re >= 1 - ci *)
   SUBGOAL_THEN `!i:num. i <= n ==>
     abs(char_fn_re p ((X:num->A->real) i) (t / sqrt((sn2:num->real) n)) -
       (&1 - (ci:num->real) i)) =
     char_fn_re p (X i) (t / sqrt(sn2 n)) - (&1 - ci i)` ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x - y ==> abs(x - y) = x - y`) THEN
    ((* char_fn_re >= 1 - s^2*E[X^2]/2 = 1 - ci *)
    SUBGOAL_THEN `&1 - (ci:num->real) i =
      &1 - (t / sqrt((sn2:num->real) n)) pow 2 *
        expectation p (\x:A. (X:num->A->real) i x pow 2) / &2` SUBST1_TAC THENL
    [EXPAND_TAC "ci" THEN BETA_TAC THEN
     REWRITE_TAC[REAL_POW_DIV] THEN
     (SUBGOAL_THEN `sqrt((sn2:num->real) n) pow 2 = sn2 n` SUBST1_TAC THENL
     [MATCH_MP_TAC SQRT_POW_2 THEN ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC]) THEN
     SUBGOAL_THEN `~(&2 * (sn2:num->real) n = &0)` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(&2 * x = &0)`) THEN
      ASM_REWRITE_TAC[ETA_AX]; CONV_TAC REAL_FIELD]; ALL_TAC]) THEN
    REWRITE_TAC[char_fn_re] THEN
    SUBGOAL_THEN `&1 - (t / sqrt((sn2:num->real) n)) pow 2 *
      expectation p (\x:A. (X:num->A->real) i x pow 2) / &2 =
      expectation p (\x. &1 - (t / sqrt(sn2 n)) pow 2 * X i x pow 2 / &2)`
      SUBST1_TAC THENL
    [(SUBGOAL_THEN `expectation p (\x:A. &1 - (t / sqrt((sn2:num->real) n)) pow 2 *
      (X:num->A->real) i x pow 2 / &2) =
      expectation p (\x. &1) - (t / sqrt(sn2 n)) pow 2 / &2 *
      expectation p (\x. X i x pow 2)` SUBST1_TAC THENL
     [SUBGOAL_THEN `(\x:A. &1 - (t / sqrt((sn2:num->real) n)) pow 2 *
       (X:num->A->real) i x pow 2 / &2) =
       (\x. (\x. &1) x + (-- ((t / sqrt(sn2 n)) pow 2 / &2)) * (\x. X i x pow 2) x)`
       SUBST1_TAC THENL
      [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN BETA_TAC THEN REAL_ARITH_TAC;
       ASM_SIMP_TAC[EXPECTATION_ADD; INTEGRABLE_CONST; INTEGRABLE_CMUL;
         EXPECTATION_CMUL]]; ALL_TAC]) THEN
     REWRITE_TAC[EXPECTATION_CONST; PROB_SPACE] THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
    (* Now show E[cos(s*Xi)] - E[1 - s^2*Xi^2/2] >= 0 *)
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&0` THEN
    (CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC]) THEN
    (SUBGOAL_THEN `expectation p (\x:A. cos((t / sqrt((sn2:num->real) n)) *
      (X:num->A->real) i x)) -
      expectation p (\x. &1 - (t / sqrt(sn2 n)) pow 2 * X i x pow 2 / &2) =
      expectation p (\x. cos((t / sqrt(sn2 n)) * X i x) -
        (&1 - (t / sqrt(sn2 n)) pow 2 * X i x pow 2 / &2))`
      SUBST1_TAC THENL
    [
     MATCH_MP_TAC(GSYM EXPECTATION_SUB) THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_COS_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
      [REWRITE_TAC[INTEGRABLE_CONST];
       MATCH_MP_TAC INTEGRABLE_CMUL THEN REWRITE_TAC[real_div] THEN
       ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
       MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[ETA_AX]]]; ALL_TAC]) THEN
    MATCH_MP_TAC EXPECTATION_POS THEN CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_COS_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
      [REWRITE_TAC[INTEGRABLE_CONST];
       MATCH_MP_TAC INTEGRABLE_CMUL THEN REWRITE_TAC[real_div] THEN
       ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
       MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[ETA_AX]]];
     GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
     MP_TAC(SPEC `(t / sqrt((sn2:num->real) n)) * (X:num->A->real) i x`
       COS_LOWER_BOUND) THEN
     REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC]; ALL_TAC]) THEN
   ((* Step 2: Replace abs with value and bound via CHAR_FN_RE_COMPONENT_BOUND *)
   SUBGOAL_THEN `sum(0..n) (\i. abs(char_fn_re p ((X:num->A->real) i)
     (t / sqrt((sn2:num->real) n)) - (&1 - (ci:num->real) i))) =
     sum(0..n) (\i. char_fn_re p (X i) (t / sqrt(sn2 n)) - (&1 - ci i))`
     SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    BETA_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC]) THEN
   (* Upper bound via CHAR_FN_RE_COMPONENT_BOUND *)
   MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `sum(0..n) (\i.
     (t / sqrt((sn2:num->real) n)) pow 4 *
       (eps * sqrt(sn2 n)) pow 2 *
       expectation p (\x:A. (X:num->A->real) i x pow 2) / &6 +
     (t / sqrt(sn2 n)) pow 2 / &2 *
       expectation p (\x. X i x pow 2 *
         (if abs(X i x) > eps * sqrt(sn2 n) then &1 else &0)))` THEN
   (CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    ((* Show ci = s^2*E[Xi^2]/2 *)
    SUBGOAL_THEN `char_fn_re p ((X:num->A->real) i)
      (t / sqrt((sn2:num->real) n)) - (&1 - (ci:num->real) i) =
      char_fn_re p (X i) (t / sqrt(sn2 n)) -
        (&1 - (t / sqrt(sn2 n)) pow 2 *
          expectation p (\x:A. X i x pow 2) / &2)` SUBST1_TAC THENL
    [AP_TERM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "ci" THEN BETA_TAC THEN
     REWRITE_TAC[REAL_POW_DIV] THEN
     (SUBGOAL_THEN `sqrt((sn2:num->real) n) pow 2 = sn2 n` SUBST1_TAC THENL
     [MATCH_MP_TAC SQRT_POW_2 THEN ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC]) THEN
     SUBGOAL_THEN `~(&2 * (sn2:num->real) n = &0)` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(&2 * x = &0)`) THEN
      ASM_REWRITE_TAC[ETA_AX]; CONV_TAC REAL_FIELD]; ALL_TAC]) THEN
    MATCH_MP_TAC CHAR_FN_RE_COMPONENT_BOUND THEN
    ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[ETA_AX];
     MATCH_MP_TAC SQRT_POS_LE THEN LOCAL_ASM_REAL_ARITH_TAC]; ALL_TAC]) THEN
   (* Step 3: Split and simplify sums *)
   REWRITE_TAC[SUM_ADD_NUMSEG] THEN
   ((* First sum: s^4*d^2*E[Xi^2]/6 summed = t^4*eps^2/6 *)
   SUBGOAL_THEN `sum(0..n) (\i.
     (t / sqrt((sn2:num->real) n)) pow 4 *
       (eps * sqrt(sn2 n)) pow 2 *
       expectation p (\x:A. (X:num->A->real) i x pow 2) / &6) =
     t pow 4 * eps pow 2 / &6`
     SUBST1_TAC THENL
   [(SUBGOAL_THEN `!i. (t / sqrt((sn2:num->real) n)) pow 4 *
     (eps * sqrt(sn2 n)) pow 2 *
     expectation p (\x:A. (X:num->A->real) i x pow 2) / &6 =
     (t pow 4 * eps pow 2 / (&6 * sn2 n)) *
     expectation p (\x. X i x pow 2)` (fun th -> REWRITE_TAC[th]) THENL
    [GEN_TAC THEN REWRITE_TAC[REAL_POW_DIV; REAL_POW_MUL] THEN
     (SUBGOAL_THEN `sqrt((sn2:num->real) n) pow 4 = sn2 n pow 2`
       SUBST1_TAC THENL
     [(SUBGOAL_THEN `sqrt((sn2:num->real) n) pow 4 =
       (sqrt(sn2 n) pow 2) pow 2` SUBST1_TAC THENL
      [REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW]; ALL_TAC]) THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC]) THEN
     (SUBGOAL_THEN `sqrt((sn2:num->real) n) pow 2 = sn2 n` SUBST1_TAC THENL
     [MATCH_MP_TAC SQRT_POW_2 THEN ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC]) THEN
     SUBGOAL_THEN `~((sn2:num->real) n = &0)` MP_TAC THENL
     [ASM_MESON_TAC[REAL_LT_IMP_NZ]; CONV_TAC REAL_FIELD]; ALL_TAC]) THEN
    REWRITE_TAC[SUM_LMUL] THEN
    (SUBGOAL_THEN `sum(0..n) (\i. expectation p
      (\x:A. (X:num->A->real) i x pow 2)) = (sn2:num->real) n`
      SUBST1_TAC THENL
    [EXPAND_TAC "sn2" THEN REFL_TAC; ALL_TAC]) THEN
    SUBGOAL_THEN `~((sn2:num->real) n = &0)` MP_TAC THENL
    [ASM_MESON_TAC[REAL_LT_IMP_NZ]; CONV_TAC REAL_FIELD]; ALL_TAC]) THEN
   ((* Second sum: s^2/2 * E[Xi^2*I] summed = t^2/2 * Ln *)
   SUBGOAL_THEN `sum(0..n) (\i.
     (t / sqrt((sn2:num->real) n)) pow 2 / &2 *
       expectation p (\x:A. (X:num->A->real) i x pow 2 *
         (if abs(X i x) > eps * sqrt(sn2 n) then &1 else &0))) =
     t pow 2 / &2 * (sum(0..n) (\i. expectation p (\x. X i x pow 2 *
       (if abs(X i x) > eps * sqrt(sn2 n)
        then &1 else &0))) / sn2 n)`
     SUBST1_TAC THENL
   [(SUBGOAL_THEN `!i. (t / sqrt((sn2:num->real) n)) pow 2 / &2 *
     expectation p (\x:A. (X:num->A->real) i x pow 2 *
       (if abs(X i x) > eps * sqrt(sn2 n) then &1 else &0)) =
     (t pow 2 / (&2 * sn2 n)) *
     expectation p (\x. X i x pow 2 *
       (if abs(X i x) > eps * sqrt(sn2 n) then &1 else &0))`
     (fun th -> REWRITE_TAC[th]) THENL
    [GEN_TAC THEN REWRITE_TAC[REAL_POW_DIV] THEN
     (SUBGOAL_THEN `sqrt((sn2:num->real) n) pow 2 = sn2 n`
       SUBST1_TAC THENL
     [MATCH_MP_TAC SQRT_POW_2 THEN ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC]) THEN
     SUBGOAL_THEN `~((sn2:num->real) n = &0)` MP_TAC THENL
     [ASM_MESON_TAC[REAL_LT_IMP_NZ]; CONV_TAC REAL_FIELD]; ALL_TAC]) THEN
    REWRITE_TAC[SUM_LMUL] THEN
    SUBGOAL_THEN `~((sn2:num->real) n = &0)` MP_TAC THENL
    [ASM_MESON_TAC[REAL_LT_IMP_NZ]; CONV_TAC REAL_FIELD]; ALL_TAC]) THEN
   ((* Step 4: Connect with Ln and bound *)
   SUBGOAL_THEN `sum(0..n) (\i. expectation p (\x:A. (X:num->A->real) i x pow 2 *
     (if abs(X i x) > eps * sqrt((sn2:num->real) n)
      then &1 else &0))) / sn2 n = (Ln:real->num->real) eps n`
     SUBST1_TAC THENL
   [EXPAND_TAC "Ln" THEN BETA_TAC THEN REFL_TAC; ALL_TAC]) THEN
   (* Now goal: t^4*eps^2/6 + t^2/2*Ln < eta/4 + eta/4 *)
   MATCH_MP_TAC(REAL_ARITH
     `a < e /\ &0 <= b /\ b < e ==> a + b < e + e`) THEN
   ASM_REWRITE_TAC[ETA_AX] THEN (CONJ_TAC THENL
   [(* 0 <= t^2/2 * Ln *)
    MATCH_MP_TAC REAL_LE_MUL THEN (CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
     REAL_ARITH_TAC; ALL_TAC]) THEN
    EXPAND_TAC "Ln" THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
    [MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
     GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
     MATCH_MP_TAC EXPECTATION_POS THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_INDICATOR_WEIGHTED_POW2 THEN
      ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC SQRT_POS_LE THEN
      ASM_MESON_TAC[REAL_LT_IMP_LE];
      GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      COND_CASES_TAC THEN REAL_ARITH_TAC];
     ASM_MESON_TAC[REAL_LT_IMP_LE]]; ALL_TAC]) THEN
   (* t^2/2 * Ln < eta/4 *)
   MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `t pow 2 * abs((Ln:real->num->real) eps n)` THEN
   (CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `t pow 2 / &2 * abs((Ln:real->num->real) eps n)` THEN
    (CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      REAL_ARITH_TAC;
      REAL_ARITH_TAC]; ALL_TAC]) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> a / &2 <= a`) THEN
    REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC]) THEN
   MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `t pow 2 * eta / (&5 * (t pow 2 + t pow 4 + &1))` THEN
   (CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC]) THEN
   (* t^2 * eta / (4*(t^2+t^4+1)) < eta/4 *)
   SUBGOAL_THEN `&0 < t pow 2 + t pow 4 + &1` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 < a + b + &1`) THEN
    CONJ_TAC THEN
    REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW; REAL_LE_POW_2];
    ALL_TAC] THEN
   (SUBGOAL_THEN `~(t pow 2 + t pow 4 + &1 = &0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LT_IMP_NZ]; ALL_TAC]) THEN
   SUBGOAL_THEN `t pow 2 * eta / (&5 * (t pow 2 + t pow 4 + &1)) =
     (eta / &5) * (t pow 2 / (t pow 2 + t pow 4 + &1))` SUBST1_TAC THENL
   [UNDISCH_TAC `~(t pow 2 + t pow 4 + &1 = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
   GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
   MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
   [UNDISCH_TAC `&0 < eta` THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REWRITE_TAC[REAL_MUL_LID] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= b ==> a < a + b + &1`) THEN
    REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW; REAL_LE_POW_2]];
   ALL_TAC] THEN
   (* Assembly: total error < eta *)
   (* Expand s back to t / sqrt(sn2 n), then chain the 5 bounds *)
   EXPAND_TAC "s" THEN
   FIRST_X_ASSUM MP_TAC THEN (* sum re diffs < 2*eta/5 *)
   FIRST_X_ASSUM MP_TAC THEN (* sum im parts < 2*eta/5 *)
   FIRST_X_ASSUM MP_TAC THEN (* |prod_ci - exp| < eta/5 *)
   FIRST_X_ASSUM MP_TAC THEN (* |prod_re - prod_ci| <= sum_re_diffs *)
   FIRST_X_ASSUM MP_TAC THEN (* |re - prod_re| <= sum_im *)
   REAL_ARITH_TAC;
   (* ============================================================ *)
   (* char_fn_im convergence:                                      *)
   (*   char_fn_im p (Y n) t ---> &0                              *)
   (* Uses CHAR_FN_SUM_IM_BOUND + component bounds + Lindeberg    *)
   (* ============================================================ *)
   X_GEN_TAC `t:real` THEN
   ((* Scaling: char_fn_im p (\a. sum/sqrt(sn2)) t =
               char_fn_im p (\a. sum) (t/sqrt(sn2)) *)
   SUBGOAL_THEN `!n. char_fn_im p
     (\a:A. sum(0..n) (\i. (X:num->A->real) i a) /
       sqrt((sn2:num->real) n)) t =
     char_fn_im p (\a. sum(0..n) (\i. X i a))
       (t / sqrt(sn2 n))`
     (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[char_fn_im] THEN
    BETA_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    GEN_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
    (SUBGOAL_THEN `!a b:real. a / b = inv(b) * a`
      (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN REAL_ARITH_TAC; ALL_TAC]) THEN
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   X_GEN_TAC `eta:real` THEN DISCH_TAC THEN
   ((* Handle t = 0 case *)
   ASM_CASES_TAC `t = &0` THENL
   [EXISTS_TAC `0` THEN GEN_TAC THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; char_fn_im; SIN_0;
      EXPECTATION_CONST; REAL_SUB_RZERO; REAL_ABS_NUM] THEN
    LOCAL_ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
   (* t != 0: use CHAR_FN_SUM_IM_BOUND + component bounds *)
   (* Choose eps *)
   ABBREV_TAC `eps' = min (&1)
     (eta / (&2 * (abs(t:real) pow 3 + &1)))` THEN
   (SUBGOAL_THEN `&0 < eps'` ASSUME_TAC THENL
   [EXPAND_TAC "eps'" THEN REWRITE_TAC[REAL_LT_MIN] THEN
    (CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC]) THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
    [REAL_ARITH_TAC;
     MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> &0 < a + &1`) THEN
     MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC]; ALL_TAC]) THEN
   (SUBGOAL_THEN `eps' <= &1` ASSUME_TAC THENL
   [EXPAND_TAC "eps'" THEN REAL_ARITH_TAC; ALL_TAC]) THEN
   ((* |t|^3 * eps' / 2 < eta/2 *)
   SUBGOAL_THEN `abs(t:real) pow 3 * eps' / &2 < eta / &2`
     ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `abs(t:real) pow 3 *
      (eta / (&2 * (abs t pow 3 + &1))) / &2` THEN
    (CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
      EXPAND_TAC "eps'" THEN REAL_ARITH_TAC]; ALL_TAC]) THEN
    (SUBGOAL_THEN `&0 < abs(t:real) pow 3 + &1` ASSUME_TAC THENL
    [MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> &0 < a + &1`) THEN
     MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC]) THEN
    (SUBGOAL_THEN `~(abs(t:real) pow 3 + &1 = &0)` ASSUME_TAC THENL
    [LOCAL_ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    (SUBGOAL_THEN `abs(t:real) pow 3 *
      (eta / (&2 * (abs t pow 3 + &1))) / &2 =
      eta * abs t pow 3 / (&4 * (abs t pow 3 + &1))`
      SUBST1_TAC THENL
    [UNDISCH_TAC `~(abs(t:real) pow 3 + &1 = &0)` THEN
     CONV_TAC REAL_FIELD; ALL_TAC]) THEN
    (* Goal: eta * abs t^3 / (4*(abs t^3+1)) < eta / 2 *)
    REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
    [LOCAL_ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    (* Goal: abs t^3 * inv(4*(abs t^3+1)) < inv(2) *)
    SUBGOAL_THEN `inv(&2:real) =
      (&2 * (abs(t:real) pow 3 + &1)) * inv(&4 * (abs t pow 3 + &1))`
      SUBST1_TAC THENL
    [UNDISCH_TAC `~(abs(t:real) pow 3 + &1 = &0)` THEN
     CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_RMUL THEN CONJ_TAC THENL
    [MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> a < &2 * (a + &1)`) THEN
     MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
     CONJ_TAC THENL [REAL_ARITH_TAC; LOCAL_ASM_REAL_ARITH_TAC]];
    ALL_TAC]) THEN
   ((* By Lindeberg at eps', get N *)
   SUBGOAL_THEN `?N:num. !n. N <= n ==>
     abs(sum(0..n) (\i. expectation p (\x:A. (X:num->A->real) i x pow 2 *
       (if abs(X i x) > eps' * sqrt((sn2:num->real) n)
        then &1 else &0))) / sn2 n) < eta / (&2 * t pow 2 + &2)`
     (X_CHOOSE_THEN `N:num` ASSUME_TAC) THENL
   [UNDISCH_TAC `!eps. &0 < eps ==>
     ((\n. sum (0..n) (\i. expectation (p:A prob_space)
       (\x. (X:num->A->real) i x pow 2 *
         (if abs (X i x) > eps * sqrt (sum (0..n)
           (\j. expectation p (\y. X j y pow 2))) then &1 else &0))) /
       sum (0..n) (\i. expectation p (\x. X i x pow 2)))
     ---> &0) sequentially` THEN
    DISCH_THEN(MP_TAC o SPEC `eps':real`) THEN ASM_REWRITE_TAC[ETA_AX] THEN
    REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
    DISCH_THEN(MP_TAC o SPEC `eta / (&2 * t pow 2 + &2)`) THEN
    (ANTS_TAC THENL
    [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[ETA_AX] THEN
     MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> &0 < &2 * a + &2`) THEN
     REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `M:num` ASSUME_TAC) THEN
    EXISTS_TAC `M:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[ETA_AX] THEN
    EXPAND_TAC "sn2" THEN SIMP_TAC[]; ALL_TAC]) THEN
   (* N works *)
   EXISTS_TAC `N:num` THEN
   X_GEN_TAC `n:num` THEN DISCH_TAC THEN
   REWRITE_TAC[REAL_SUB_RZERO] THEN
   (* |char_fn_im(Y_n, t)| <= sum |s_i| by CHAR_FN_SUM_IM_BOUND *)
   MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `sum(0..n) (\i. abs(char_fn_im p ((X:num->A->real) i)
     (t / sqrt((sn2:num->real) n))))` THEN
   (CONJ_TAC THENL
   [MATCH_MP_TAC CHAR_FN_SUM_IM_BOUND THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC]) THEN
   (* Bound each |s_i| using CHAR_FN_IM_COMPONENT_BOUND *)
   MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `sum(0..n) (\i.
     abs(t / sqrt((sn2:num->real) n)) pow 3 *
       (eps' * sqrt(sn2 n)) *
       expectation p (\x:A. (X:num->A->real) i x pow 2) / &2 +
     (t / sqrt(sn2 n)) pow 2 *
       expectation p (\x. X i x pow 2 *
         (if abs(X i x) > eps' * sqrt(sn2 n) then &1 else &0)))` THEN
   (CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MATCH_MP_TAC CHAR_FN_IM_COMPONENT_BOUND THEN
    ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
    [ASM_MESON_TAC[REAL_LT_IMP_LE];
     MATCH_MP_TAC SQRT_POS_LE THEN ASM_MESON_TAC[REAL_LT_IMP_LE]];
    ALL_TAC]) THEN
   ((* Split sum and factor constants *)
   SUBGOAL_THEN `!f g:num->real.
     sum(0..n) (\i. f i + g i) = sum(0..n) f + sum(0..n) g`
     (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[SUM_ADD_NUMSEG]; ALL_TAC]) THEN
   ((* Factor out constants from each sum *)
   SUBGOAL_THEN `sum(0..n) (\i.
     abs(t / sqrt((sn2:num->real) n)) pow 3 *
       (eps' * sqrt(sn2 n)) *
       expectation p (\x:A. (X:num->A->real) i x pow 2) / &2) =
     abs t pow 3 * eps' / &2`
     SUBST1_TAC THENL
   [(SUBGOAL_THEN `!i. abs(t / sqrt((sn2:num->real) n)) pow 3 *
     (eps' * sqrt(sn2 n)) *
     expectation p (\x:A. (X:num->A->real) i x pow 2) / &2 =
     (abs(t / sqrt(sn2 n)) pow 3 * (eps' * sqrt(sn2 n)) / &2) *
     expectation p (\x. X i x pow 2)` (fun th -> REWRITE_TAC[th]) THENL
    [GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[SUM_LMUL] THEN
    (SUBGOAL_THEN `sum(0..n) (\i. expectation p
      (\x:A. (X:num->A->real) i x pow 2)) = (sn2:num->real) n`
      SUBST1_TAC THENL
    [EXPAND_TAC "sn2" THEN REFL_TAC; ALL_TAC]) THEN
    SUBGOAL_THEN `(abs(t / sqrt((sn2:num->real) n)) pow 3 *
      (eps' * sqrt(sn2 n)) / &2) * sn2 n = abs t pow 3 * eps' / &2`
      (fun th -> REWRITE_TAC[th]) THENL
    [(SUBGOAL_THEN `(abs(t / sqrt((sn2:num->real) n)) pow 3 *
       (eps' * sqrt(sn2 n)) / &2) * sn2 n =
       abs(t / sqrt(sn2 n)) pow 3 * eps' * sqrt(sn2 n) * sn2 n / &2`
       SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC]) THEN
     MP_TAC(SPECL [`t:real`; `sqrt((sn2:num->real) n)`; `eps':real`]
       (prove(`!t c e. &0 < c ==>
         abs(t / c) pow 3 * e * c * c pow 2 / &2 =
         abs(t) pow 3 * e / &2`,
        REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_DIV; REAL_POW_DIV] THEN
        (SUBGOAL_THEN `abs c = c` SUBST1_TAC THENL
        [LOCAL_ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
        (SUBGOAL_THEN `~(c = &0)` ASSUME_TAC THENL
        [LOCAL_ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
        SUBGOAL_THEN `~(c pow 3 = &0)` MP_TAC THENL
        [REWRITE_TAC[REAL_POW_EQ_0] THEN ASM_ARITH_TAC;
         CONV_TAC REAL_FIELD]))) THEN
     ASM_REWRITE_TAC[ETA_AX] THEN DISCH_TAC THEN
     (SUBGOAL_THEN `sqrt((sn2:num->real) n) pow 2 = sn2 n`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [MATCH_MP_TAC SQRT_POW_2 THEN ASM_MESON_TAC[REAL_LT_IMP_LE];
      ALL_TAC]) THEN
     ASM_REWRITE_TAC[ETA_AX]]; ALL_TAC]) THEN
   (SUBGOAL_THEN `sum(0..n) (\i.
     (t / sqrt((sn2:num->real) n)) pow 2 *
       expectation p (\x:A. (X:num->A->real) i x pow 2 *
         (if abs(X i x) > eps' * sqrt(sn2 n) then &1 else &0))) =
     t pow 2 * (sum(0..n) (\i. expectation p (\x. X i x pow 2 *
       (if abs(X i x) > eps' * sqrt(sn2 n)
        then &1 else &0))) / sn2 n)`
     SUBST1_TAC THENL
   [(SUBGOAL_THEN `!i. (t / sqrt((sn2:num->real) n)) pow 2 *
     expectation p (\x:A. (X:num->A->real) i x pow 2 *
       (if abs(X i x) > eps' * sqrt(sn2 n) then &1 else &0)) =
     (t pow 2 / (sn2 n)) *
     expectation p (\x. X i x pow 2 *
       (if abs(X i x) > eps' * sqrt(sn2 n) then &1 else &0))`
     (fun th -> REWRITE_TAC[th]) THENL
    [GEN_TAC THEN REWRITE_TAC[REAL_POW_DIV] THEN
     (SUBGOAL_THEN `sqrt((sn2:num->real) n) pow 2 = sn2 n`
       SUBST1_TAC THENL
     [MATCH_MP_TAC SQRT_POW_2 THEN ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC]) THEN
     REFL_TAC; ALL_TAC]) THEN
    REWRITE_TAC[SUM_LMUL] THEN
    (SUBGOAL_THEN `~((sn2:num->real) n = &0)` ASSUME_TAC THENL
    [ASM_MESON_TAC[REAL_LT_IMP_NZ]; ALL_TAC]) THEN
    UNDISCH_TAC `~((sn2:num->real) n = &0)` THEN
    CONV_TAC REAL_FIELD; ALL_TAC]) THEN
   (* Now bound: |t|^3 * eps'/2 + t^2 * Ln(eps') < eta *)
   MATCH_MP_TAC(REAL_ARITH
     `a < e / &2 /\ b < e / &2 ==> a + b < e`) THEN
   ASM_REWRITE_TAC[ETA_AX] THEN
   MATCH_MP_TAC(REAL_ARITH
     `&0 <= a /\ a * b < e ==> a * b < e`) THEN
    (CONJ_TAC THENL [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC]) THEN
    (SUBGOAL_THEN `abs(sum(0..n) (\i. expectation p
      (\x:A. (X:num->A->real) i x pow 2 *
        (if abs(X i x) > eps' * sqrt((sn2:num->real) n)
         then &1 else &0))) / sn2 n) <
      eta / (&2 * t pow 2 + &2)` ASSUME_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC]) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `t pow 2 * abs(sum(0..n) (\i. expectation p
      (\x:A. (X:num->A->real) i x pow 2 *
        (if abs(X i x) > eps' * sqrt((sn2:num->real) n)
         then &1 else &0))) / sn2 n)` THEN
    (CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
     REAL_ARITH_TAC; ALL_TAC]) THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN
    EXISTS_TAC `t pow 2 * eta / (&2 * t pow 2 + &2)` THEN
    (CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
     (SUBGOAL_THEN `&0 < t pow 2` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LT_POW_2] THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC]) THEN
     ASM_REWRITE_TAC[ETA_AX]; ALL_TAC]) THEN
    (SUBGOAL_THEN `&0 < &2 * t pow 2 + &2` ASSUME_TAC THENL
    [MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> &0 < &2 * a + &2`) THEN
     REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC]) THEN
    (SUBGOAL_THEN `~(&2 * t pow 2 + &2 = &0)` ASSUME_TAC THENL
    [LOCAL_ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    (SUBGOAL_THEN `t pow 2 * eta / (&2 * t pow 2 + &2) < eta / &2`
      MP_TAC THENL
    [(SUBGOAL_THEN `t pow 2 * eta / (&2 * t pow 2 + &2) =
      eta * t pow 2 / (&2 * t pow 2 + &2)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC]) THEN
     REWRITE_TAC[real_div] THEN
     MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
     [LOCAL_ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `inv(&2:real) =
       (t pow 2 + &1) * inv(&2 * t pow 2 + &2)`
       SUBST1_TAC THENL
     [UNDISCH_TAC `~(&2 * t pow 2 + &2 = &0)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
     MATCH_MP_TAC REAL_LT_RMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> a < a + &1`) THEN
      REWRITE_TAC[REAL_LE_POW_2];
      MATCH_MP_TAC REAL_LT_INV THEN LOCAL_ASM_REAL_ARITH_TAC];
     ALL_TAC]) THEN
    SIMP_TAC[]]);;

(* Cr inequality: (x+y)^4 <= 8*(x^4 + y^4) *)
let FOURTH_POWER_SUM_BOUND = prove
 (`!x y. (x + y) pow 4 <= &8 * (x pow 4 + y pow 4)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
    `&0 <= (x - y) pow 2 * (&7 * x pow 2 + &10 * x * y + &7 * y pow 2)
     ==> (x + y) pow 4 <= &8 * (x pow 4 + y pow 4)`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
  [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &7 * (&7 * x pow 2 + &10 * x * y + &7 * y pow 2)`
    MP_TAC THENL
  [SUBGOAL_THEN `&7 * (&7 * x pow 2 + &10 * x * y + &7 * y pow 2) =
    (&7 * x + &5 * y) pow 2 + &24 * y pow 2` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= a + b`) THEN
   CONJ_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2];
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    REAL_ARITH_TAC];
   MP_TAC(REAL_ARITH `&0 < &7`) THEN
   MESON_TAC[REAL_LE_MUL_EQ]]);;

(* Bounded sum pow integrability *)
let INTEGRABLE_BOUNDED_SUM_POW = prove
 (`!p:A prob_space (Y:num->A->real) c n k.
    (!i. integrable p (Y i)) /\
    (!i w. w IN prob_carrier p ==> abs(Y i w) <= c)
    ==> integrable p (\w. sum(0..n) (\i. Y i w) pow k)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
  EXISTS_TAC `((&n + &1) * c) pow k` THEN CONJ_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
   MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN
   REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
   REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
   X_GEN_TAC `w:A` THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
   MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `sum(0..n) (\i. abs((Y:num->A->real) i w))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC[SUM_ABS_NUMSEG];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..n) (\i:num. c:real)` THEN CONJ_TAC THENL
    [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
     REWRITE_TAC[] THEN ASM_SIMP_TAC[];
     REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0] THEN
     REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_SUC] THEN
     REAL_ARITH_TAC]]]);;

(* Nonneg bounded partial sums => summable *)
let NONNEG_BOUNDED_PARTIAL_SUMS_SUMMABLE = prove
 (`!f M. (!n. &0 <= f n) /\ (!n. sum(0..n) f <= M)
   ==> real_summable (from 0) f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[real_summable; real_sums; REALLIM_SEQUENTIALLY] THEN
  SUBGOAL_THEN `!k:num. from 0 INTER (0..k) = (0..k)`
    (fun th -> REWRITE_TAC[th]) THENL
  [GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_NUMSEG;
     from; IN_ELIM_THM] THEN ARITH_TAC;
   ALL_TAC] THEN
  MP_TAC(ISPECL [`\k:num. sum(0..k) (f:num->real)`; `M:real`]
    CONVERGENT_BOUNDED_INCREASING) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`f:num->real`; `0`; `m:num`; `n:num`] SUM_COMBINE_R) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= b ==> a <= a + b`) THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= s /\ s <= M ==> abs s <= M`) THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[]]];
   MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
   MESON_TAC[]]);;

(* ================================================================== *)
(* SECOND_MOMENT_BOUNDED_FROM_AS_CONVERGENCE                          *)
(* If partial sums converge a.s. and have a 4th moment bound, then    *)
(* the second moments are uniformly bounded.                          *)
(* ================================================================== *)

(* Key idea: a.s. convergence => partial sums bounded a.s.            *)
(* Define A_m = {x | exists n, |S_n(x)| >= m}. Then A_m decreasing,  *)
(* INTERS A_m subset {divergent}, so P(A_m) -> 0.                    *)
(* Choose m with P(A_m) < 1/(4K). Then by Cauchy-Schwarz:            *)
(* E[S_n^2*1(|S_n|>=m)] <= sqrt(E[S_n^4]*P(A_m)) < E[S_n^2]/2      *)
(* So E[S_n^2] <= m^2 + E[S_n^2]/2, giving E[S_n^2] <= 2*m^2.      *)

let PROB_LIM_HELPER = prove
 (`!p:A prob_space Am.
    (!m. Am m IN prob_events p) /\
    (!m. Am (SUC m) SUBSET Am m) /\
    prob p (INTERS {Am m | m IN (:num)}) = &0
    ==> ((\m. prob p (Am m)) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC PROB_CONTINUITY_FROM_ABOVE THEN
  ASM_REWRITE_TAC[]);;

let SECOND_MOMENT_BOUNDED_FROM_AS_CONVERGENCE = prove
 (`!p:A prob_space (Y:num->A->real) B K.
    &0 < B /\ &1 <= K /\
    (!n. integrable p (Y n)) /\
    (!n x. x IN prob_carrier p ==> abs(Y n x) <= B) /\
    (!n. expectation p (\x. sum(0..n) (\i. Y i x) pow 4) <=
         K * expectation p (\x. sum(0..n) (\i. Y i x) pow 2) pow 2) /\
    almost_surely p {x | ?L. ((\n. sum(0..n) (\i. Y i x)) ---> L) sequentially}
    ==> ?M. !n. expectation p (\x. sum(0..n) (\i. Y i x) pow 2) <= M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Phase 0: Setup - establish random_variable, bounds, integrability *)
  SUBGOAL_THEN `!i. random_variable p ((Y:num->A->real) i)` ASSUME_TAC THENL
  [ASM_MESON_TAC[INTEGRABLE_IMP_RANDOM_VARIABLE]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. random_variable p (\x:A. sum(0..n) (\i. (Y:num->A->real) i x))` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n x. x IN prob_carrier p
    ==> abs(sum(0..n) (\i. (Y:num->A->real) i x)) <= &(n + 1) * B` ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `sum(0..n) (\i. abs((Y:num->A->real) i x))` THEN CONJ_TAC THENL
   [REWRITE_TAC[SUM_ABS_NUMSEG]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `sum(0..n) (\i:num. B)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_MESON_TAC[];
    REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0] THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n. integrable p (\x:A. sum(0..n) (\i. (Y:num->A->real) i x) pow 2)` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
   EXISTS_TAC `(&(n + 1) * B) pow 2` THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
   MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n. integrable p (\x:A. sum(0..n) (\i. (Y:num->A->real) i x) pow 4)` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
   EXISTS_TAC `(&(n + 1) * B) pow 4` THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
   MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* Phase 1: Events - show abs(S_n(x)) >= m is an event *)
  SUBGOAL_THEN `!n m. {x | x IN prob_carrier p /\
    abs(sum(0..n) (\i. (Y:num->A->real) i x)) >= &m} IN prob_events p`
    ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN
   SUBGOAL_THEN `{x | x IN prob_carrier p /\
     abs(sum(0..n) (\i. (Y:num->A->real) i x)) >= &m} =
     {x | x IN prob_carrier p /\ sum(0..n) (\i. Y i x) >= &m} UNION
     {x | x IN prob_carrier p /\ --sum(0..n) (\i. Y i x) >= &m}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN
    GEN_TAC THEN ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   MATCH_MP_TAC PROB_UNION_IN_EVENTS THEN CONJ_TAC THENL
   [MATCH_MP_TAC RV_LEVEL_GE_IN_EVENTS THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
      --sum(0..n) (\i. (Y:num->A->real) i x) >= &m} =
      {x | x IN prob_carrier p /\
       (\x. --sum(0..n) (\i. Y i x)) x >= &m}` SUBST1_TAC THENL
    [REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC RV_LEVEL_GE_IN_EVENTS THEN
    MATCH_MP_TAC RANDOM_VARIABLE_NEG THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* Define Am = UNIONS of level sets *)
  ABBREV_TAC `Am = \m. UNIONS {(\n.
    {x | x IN prob_carrier p /\
     abs(sum(0..n) (\i. (Y:num->A->real) i x)) >= &m}) n | n IN (:num)}` THEN
  SUBGOAL_THEN `!m. (Am:num->A->bool) m IN prob_events (p:A prob_space)` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "Am" THEN
   MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!m (x:A). x IN (Am:num->A->bool) m
    ==> x IN prob_carrier p /\ ?n. abs(sum(0..n) (\i. (Y:num->A->real) i x)) >= &m`
    ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN EXPAND_TAC "Am" THEN
   REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
   DISCH_THEN(X_CHOOSE_THEN `t:A->bool` MP_TAC) THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   FIRST_X_ASSUM(X_CHOOSE_THEN `nn:num` SUBST1_TAC) THEN
   REWRITE_TAC[IN_ELIM_THM] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* Phase 2: Am decreasing *)
  SUBGOAL_THEN `!m. (Am:num->A->bool) (SUC m) SUBSET Am m` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "Am" THEN REWRITE_TAC[SUBSET; IN_UNIONS] THEN
   REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC) THEN
   EXISTS_TAC `{x:A | x IN prob_carrier p /\
     abs(sum(0..n) (\i. (Y:num->A->real) i x)) >= &m}` THEN
   CONJ_TAC THENL [EXISTS_TAC `n:num` THEN REWRITE_TAC[]; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_ELIM_THM]) THEN
   REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC(REAL_ARITH `x >= &(SUC m) /\ &m <= &(SUC m) ==> x >= &m`) THEN
   ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
   ALL_TAC] THEN
  (* Phase 3: INTERS Am subset divergent *)
  SUBGOAL_THEN `INTERS {(Am:num->A->bool) m | m IN (:num)} SUBSET
    {x:A | x IN prob_carrier p /\
     ~(x IN {x | ?L. ((\n. sum(0..n) (\i. (Y:num->A->real) i x)) ---> L)
                       sequentially})}` ASSUME_TAC THENL
  [REWRITE_TAC[SUBSET; IN_INTERS; IN_ELIM_THM; IN_UNIV] THEN
   X_GEN_TAC `y:A` THEN DISCH_TAC THEN
   SUBGOAL_THEN `!m. (y:A) IN (Am:num->A->bool) m` ASSUME_TAC THENL
   [GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `(Am:num->A->bool) m`) THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `m:num` THEN REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `(y:A) IN prob_carrier p` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `!m. ?n. abs(sum(0..n) (\i. (Y:num->A->real) i y)) >= &m`
     ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_TAC `L:real`) THEN
   MP_TAC(ISPECL [`(\n. sum(0..n) (\i. (Y:num->A->real) i y))`; `L:real`]
     REAL_CONVERGENT_IMP_BOUNDED) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[REAL_BOUNDED_POS_LT; IN_IMAGE; IN_UNIV] THEN
   DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN
   MP_TAC(ISPEC `b:real` REAL_ARCH_SIMPLE) THEN
   DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
   DISCH_THEN(X_CHOOSE_TAC `j:num`) THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `sum(0..j) (\i. (Y:num->A->real) i y)`) THEN
   ANTS_TAC THENL [EXISTS_TAC `j:num` THEN REWRITE_TAC[]; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Phase 3b: P(INTERS Am) = 0 *)
  SUBGOAL_THEN `prob p (INTERS {(Am:num->A->bool) m | m IN (:num)}) = &0`
    ASSUME_TAC THENL
  [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC PROB_POSITIVE THEN
    MATCH_MP_TAC PROB_INDEXED_INTER_IN_EVENTS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   UNDISCH_TAC `almost_surely p
     {x:A | ?L. ((\n. sum(0..n) (\i. (Y:num->A->real) i x)) ---> L) sequentially}` THEN
   REWRITE_TAC[almost_surely] THEN
   DISCH_THEN(X_CHOOSE_THEN `N:A->bool` STRIP_ASSUME_TAC) THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `prob p (N:A->bool)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC PROB_MONO THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC PROB_INDEXED_INTER_IN_EVENTS THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    CONJ_TAC THENL
    [ASM_MESON_TAC[null_event]; ALL_TAC] THEN
    ASM_MESON_TAC[SUBSET_TRANS];
    ASM_MESON_TAC[null_event; REAL_LE_REFL]];
   ALL_TAC] THEN
  (* Phase 4: P(Am) -> 0 *)
  SUBGOAL_THEN `&0 < inv(&4 * K)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
   CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(ASSUME `&1 <= K`) THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `Am:num->A->bool`] PROB_LIM_HELPER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[REALLIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `inv(&4 * K)`) THEN ASM_REWRITE_TAC[] THEN
  (* Phase 5: Choose m0 *)
  DISCH_THEN(X_CHOOSE_TAC `m0:num`) THEN
  SUBGOAL_THEN `prob p ((Am:num->A->bool) m0) < inv(&4 * K)` ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `m0:num`) THEN
   REWRITE_TAC[LE_REFL] THEN
   SUBGOAL_THEN `&0 <= prob p ((Am:num->A->bool) m0)` MP_TAC THENL
   [MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Provide witness M = 2 * m0^2 *)
  EXISTS_TAC `&2 * &m0 pow 2` THEN X_GEN_TAC `n:num` THEN
  (* Phase 6: For arbitrary n, bound E[S_n^2] *)
  ABBREV_TAC `an = {x:A | x IN prob_carrier p /\
    abs(sum(0..n) (\i. (Y:num->A->real) i x)) >= &m0}` THEN
  SUBGOAL_THEN `an IN prob_events (p:A prob_space)` ASSUME_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `prob_carrier p DIFF an IN prob_events (p:A prob_space)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC PROB_DIFF_IN_EVENTS THEN
   REWRITE_TAC[PROB_CARRIER_IN_EVENTS] THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `(an:A->bool) SUBSET (Am:num->A->bool) m0` ASSUME_TAC THENL
  [EXPAND_TAC "an" THEN EXPAND_TAC "Am" THEN
   REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
   X_GEN_TAC `x:A` THEN STRIP_TAC THEN
   EXISTS_TAC `{x:A | x IN prob_carrier p /\
     abs(sum(0..n) (\i. (Y:num->A->real) i x)) >= &m0}` THEN
   CONJ_TAC THENL
   [EXISTS_TAC `n:num` THEN REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `prob p (an:A->bool) < inv(&4 * K)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `prob p ((Am:num->A->bool) m0)` THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC PROB_MONO THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* abs bound on complement *)
  SUBGOAL_THEN `!x:A. x IN prob_carrier p /\ x IN prob_carrier p DIFF an
    ==> abs(sum(0..n) (\i. (Y:num->A->real) i x)) < &m0` ASSUME_TAC THENL
  [GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
   UNDISCH_TAC `~((x:A) IN an)` THEN
   EXPAND_TAC "an" THEN REWRITE_TAC[IN_ELIM_THM] THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Integrability of S_n^2 * indicators *)
  SUBGOAL_THEN `integrable p (\x:A. sum(0..n) (\i. (Y:num->A->real) i x) pow 2 *
    indicator_fn (prob_carrier p DIFF an) x)` ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`;
    `(\x:A. sum(0..n) (\i. (Y:num->A->real) i x) pow 2)`;
    `prob_carrier p DIFF (an:A->bool)`] INTEGRABLE_MUL_INDICATOR_FN) THEN
   REWRITE_TAC[BETA_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (\x:A. sum(0..n) (\i. (Y:num->A->real) i x) pow 2 *
    indicator_fn an x)` ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`;
    `(\x:A. sum(0..n) (\i. (Y:num->A->real) i x) pow 2)`;
    `an:A->bool`] INTEGRABLE_MUL_INDICATOR_FN) THEN
   REWRITE_TAC[BETA_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Pointwise bound on complement: S_n^2 * 1_compl <= m0^2 *)
  SUBGOAL_THEN `!x:A. x IN prob_carrier p
    ==> sum(0..n) (\i. (Y:num->A->real) i x) pow 2 *
        indicator_fn (prob_carrier p DIFF an) x <= &m0 pow 2` ASSUME_TAC THENL
  [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   REWRITE_TAC[indicator_fn; IN_DIFF] THEN COND_CASES_TAC THENL
   [ALL_TAC; REWRITE_TAC[REAL_MUL_RZERO; REAL_LE_POW_2]] THEN
   REWRITE_TAC[REAL_MUL_RID] THEN
   SUBGOAL_THEN `sum(0..n) (\i. (Y:num->A->real) i x) pow 2 =
     abs(sum(0..n) (\i. Y i x)) pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
   MATCH_MP_TAC REAL_LT_IMP_LE THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF];
   ALL_TAC] THEN
  (* Complement expectation bound: E[S_n^2 * 1_compl] <= m0^2 *)
  SUBGOAL_THEN `expectation p (\x:A. sum(0..n) (\i. (Y:num->A->real) i x) pow 2 *
    indicator_fn (prob_carrier p DIFF an) x) <= &m0 pow 2` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `expectation p (\x:A. &m0 pow 2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC EXPECTATION_MONO THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[EXPECTATION_CONST; REAL_LE_REFL]];
   ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (indicator_fn (an:A->bool))` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Phase 6d: Cauchy-Schwarz *)
  SUBGOAL_THEN
    `expectation p (\x:A. sum (0..n) (\i. (Y:num->A->real) i x) pow 2 *
       indicator_fn an x) pow 2
     <= expectation p (\x. (sum (0..n) (\i. Y i x) pow 2) pow 2) *
        expectation p (\x. indicator_fn an x pow 2)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC EXPECTATION_CAUCHY_SCHWARZ THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL [ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
   CONJ_TAC THENL
   [SUBGOAL_THEN `(\x:A. sum (0..n) (\i. (Y:num->A->real) i x) pow 2 pow 2) =
      (\x. sum (0..n) (\i. Y i x) pow 4)` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
     REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW];
     ASM_REWRITE_TAC[]]; ALL_TAC] THEN
   SUBGOAL_THEN `(\x:A. indicator_fn an x pow 2) = indicator_fn an`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; indicator_fn] THEN GEN_TAC THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[ETA_AX]];
   ALL_TAC] THEN
  (* Simplify pow 2 pow 2 = pow 4 *)
  SUBGOAL_THEN
    `expectation p (\x:A. sum (0..n) (\i. (Y:num->A->real) i x) pow 2 pow 2) =
     expectation p (\x. sum (0..n) (\i. Y i x) pow 4)` ASSUME_TAC THENL
  [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
   REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW];
   ALL_TAC] THEN
  (* E[indicator^2] = P(an) *)
  SUBGOAL_THEN
    `expectation p (\x:A. indicator_fn an x pow 2) = prob p an` ASSUME_TAC THENL
  [SUBGOAL_THEN `(\x:A. indicator_fn an x pow 2) = indicator_fn an`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; indicator_fn] THEN GEN_TAC THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    MATCH_MP_TAC EXPECTATION_INDICATOR THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* Combine: E[S^2*1_an]^2 <= E[S^4]*P(an) *)
  SUBGOAL_THEN
    `expectation p (\x:A. sum (0..n) (\i. (Y:num->A->real) i x) pow 2 *
       indicator_fn an x) pow 2
     <= expectation p (\x. sum (0..n) (\i. Y i x) pow 4) * prob p an`
    ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `expectation p (\x:A. sum (0..n) (\i. (Y:num->A->real) i x) pow 2 pow 2) *
     expectation p (\x:A. indicator_fn an x pow 2)` THEN
   ASM_REWRITE_TAC[REAL_LE_REFL; REAL_LE_RMUL; REAL_LE_LMUL];
   ALL_TAC] THEN
  (* Non-negativity facts *)
  SUBGOAL_THEN `&0 <= expectation p (\x:A. sum(0..n) (\i. (Y:num->A->real) i x) pow 4)` ASSUME_TAC THENL
  [MATCH_MP_TAC EXPECTATION_POS THEN ASM_REWRITE_TAC[] THEN
   GEN_TAC THEN DISCH_TAC THEN
   SUBGOAL_THEN `sum (0..n) (\i. (Y:num->A->real) i x) pow 4 =
     (sum (0..n) (\i. Y i x) pow 2) pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_POW; ARITH]; REWRITE_TAC[REAL_LE_POW_2]];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= expectation p (\x:A. sum(0..n) (\i. (Y:num->A->real) i x) pow 2)` ASSUME_TAC THENL
  [MATCH_MP_TAC EXPECTATION_POS THEN ASM_REWRITE_TAC[] THEN
   GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_LE_POW_2];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= expectation p (\x:A. sum(0..n) (\i. (Y:num->A->real) i x) pow 2 *
    indicator_fn an x)` ASSUME_TAC THENL
  [MATCH_MP_TAC EXPECTATION_POS THEN ASM_REWRITE_TAC[] THEN
   GEN_TAC THEN DISCH_TAC THEN
   MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
   REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= prob p (an:A->bool)` ASSUME_TAC THENL
  [MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Chain: E[S^4]*P(an) <= K*E[S^2]^2*P(an) *)
  SUBGOAL_THEN
    `expectation p (\x:A. sum (0..n) (\i. (Y:num->A->real) i x) pow 4) * prob p an
     <= (K * expectation p (\x. sum (0..n) (\i. Y i x) pow 2) pow 2) * prob p an`
    ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Chain: K*E[S^2]^2*P(an) <= K*E[S^2]^2*inv(4K) *)
  SUBGOAL_THEN
    `(K * expectation p (\x:A. sum (0..n) (\i. (Y:num->A->real) i x) pow 2) pow 2) * prob p an
     <= (K * expectation p (\x. sum (0..n) (\i. Y i x) pow 2) pow 2) * inv(&4 * K)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
    [MP_TAC(ASSUME `&1 <= K`) THEN REAL_ARITH_TAC;
     REWRITE_TAC[REAL_LE_POW_2]];
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* Simplify K*E[S^2]^2*inv(4K) = E[S^2]^2*inv(4) *)
  SUBGOAL_THEN
    `(K * expectation p (\x:A. sum (0..n) (\i. (Y:num->A->real) i x) pow 2) pow 2) *
     inv(&4 * K) =
     expectation p (\x. sum (0..n) (\i. Y i x) pow 2) pow 2 * inv(&4)`
    ASSUME_TAC THENL
  [SUBGOAL_THEN `~(K = &0)` ASSUME_TAC THENL
   [MP_TAC(ASSUME `&1 <= K`) THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `K * inv(K) = &1` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_MUL_RINV]; ALL_TAC] THEN
   REWRITE_TAC[REAL_INV_MUL] THEN
   ABBREV_TAC `e2' = expectation p (\x:A. sum (0..n) (\i. (Y:num->A->real) i x) pow 2)` THEN
   SUBGOAL_THEN `(K * e2' pow 2) * inv (&4) * inv K =
     (K * inv K) * (e2' pow 2 * inv(&4))` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ASM_REWRITE_TAC[REAL_MUL_LID]];
   ALL_TAC] THEN
  (* Combine to get E[S^2*1_an]^2 <= E[S^2]^2/4 *)
  SUBGOAL_THEN
    `expectation p (\x:A. sum (0..n) (\i. (Y:num->A->real) i x) pow 2 *
       indicator_fn an x) pow 2
     <= expectation p (\x. sum (0..n) (\i. Y i x) pow 2) pow 2 * inv(&4)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `expectation p (\x:A. sum (0..n) (\i. (Y:num->A->real) i x) pow 4) *
     prob p an` THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `(K * expectation p (\x:A. sum (0..n) (\i. (Y:num->A->real) i x) pow 2) pow 2) *
     prob p an` THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `(K * expectation p (\x:A. sum (0..n) (\i. (Y:num->A->real) i x) pow 2) pow 2) *
     inv (&4 * K)` THEN
   ASM_REWRITE_TAC[REAL_LE_REFL];
   ALL_TAC] THEN
  (* Deduce E[S^2*1_an] <= E[S^2]/2 *)
  SUBGOAL_THEN
    `expectation p (\x:A. sum (0..n) (\i. (Y:num->A->real) i x) pow 2 *
       indicator_fn an x)
     <= expectation p (\x. sum (0..n) (\i. Y i x) pow 2) * inv (&2)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
   REWRITE_TAC[ARITH_RULE `~(2 = 0)`] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `expectation p (\x:A. sum (0..n) (\i. (Y:num->A->real) i x) pow 2) pow 2 *
     inv(&4)` THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[REAL_POW_MUL] THEN
   SUBGOAL_THEN `inv(&2) pow 2 = inv(&4)` SUBST1_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV; REWRITE_TAC[REAL_LE_REFL]];
   ALL_TAC] THEN
  (* Phase 7: EXPECTATION_SPLIT and conclude *)
  MP_TAC(ISPECL [`p:A prob_space`;
    `(\x:A. sum (0..n) (\i. (Y:num->A->real) i x) pow 2)`;
    `an:A->bool`] EXPECTATION_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `e2 = expectation p (\x:A. sum (0..n) (\i. (Y:num->A->real) i x) pow 2)` THEN
  ABBREV_TAC `a = expectation p (\x:A. sum (0..n) (\i. (Y:num->A->real) i x) pow 2 *
    indicator_fn an x)` THEN
  ABBREV_TAC `c = expectation p (\x:A. sum (0..n) (\i. (Y:num->A->real) i x) pow 2 *
    indicator_fn (prob_carrier p DIFF an) x)` THEN
  SUBGOAL_THEN `&2 * a <= e2` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `&2 * (e2 * inv(&2))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `&2 * (e2 * inv(&2)) = e2`
      (fun th -> REWRITE_TAC[th; REAL_LE_REFL]) THEN
    SUBGOAL_THEN `&2 * inv(&2) = &1` ASSUME_TAC THENL
    [CONV_TAC REAL_RAT_REDUCE_CONV;
     MP_TAC(ASSUME `&2 * inv (&2) = &1`) THEN REAL_ARITH_TAC]];
   ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
    `e2 = a + c /\ a <= c /\ c <= M ==> e2 <= &2 * M`) THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
  [SUBGOAL_THEN `&2 * a <= a + c` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e2:real` THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    REAL_ARITH_TAC];
   ASM_REWRITE_TAC[]]);;
(* ================================================================== *)
(* THREE_SERIES_NECESSITY: Necessity of the Kolmogorov Three-Series   *)
(* ================================================================== *)

(* Helper tactics for curried abbreviations in THREE_SERIES_NECESSITY.
   EXPAND_CURRY_TAC s: finds assumption !n x. ... = f n x where f's name is s,
     then rewrites f n x -> ... (backward rewrite, unfolding the abbreviation).
   FOLD_CURRY_TAC s: same but rewrites ... -> f n x (forward rewrite). *)
let EXPAND_CURRY_TAC s =
  FIRST_ASSUM(fun th ->
    try let _,eq = strip_forall(concl th) in
        let _,r = dest_eq eq in
        let v,_ = strip_comb r in
        if fst(dest_var v) = s
        then PURE_REWRITE_TAC[GSYM th]
        else failwith ""
    with _ -> failwith "");;

let FOLD_CURRY_TAC s =
  FIRST_ASSUM(fun th ->
    try let _,eq = strip_forall(concl th) in
        let _,r = dest_eq eq in
        let v,_ = strip_comb r in
        if fst(dest_var v) = s
        then PURE_REWRITE_TAC[th]
        else failwith ""
    with _ -> failwith "");;

let THREE_SERIES_NECESSITY = prove
 (`!p:A prob_space (X:num->A->real) c C.
    &0 < c /\ &1 <= C /\
    (!n. integrable p (X n)) /\
    (!n. integrable p (\x. X n x pow 2)) /\
    indep_events_seq p (\n. {x | x IN prob_carrier p /\ abs(X n x) > c}) /\
    (!i j. ~(i = j) ==> covariance p
      (\x. min(max(X i x) (--c)) c - expectation p (\y. min(max(X i y) (--c)) c))
      (\x. min(max(X j x) (--c)) c - expectation p (\y. min(max(X j y) (--c)) c))
      = &0) /\
    (!n x. x IN prob_carrier p ==> abs(min(max(X n x) (--c)) c -
      expectation p (\y. min(max(X n y) (--c)) c)) <= &2 * c) /\
    (!n. expectation p (\x. sum(0..n) (\i. min(max(X i x) (--c)) c -
      expectation p (\y. min(max(X i y) (--c)) c)) pow 4) <=
      C * expectation p (\x. sum(0..n) (\i. min(max(X i x) (--c)) c -
          expectation p (\y. min(max(X i y) (--c)) c)) pow 2) pow 2) /\
    (!a b k t. a <= k /\ k < b /\ &0 < t ==>
      expectation p (\x. sum(a..k)
        (\i. min(max(X i x) (--c)) c -
             expectation p (\y. min(max(X i y) (--c)) c)) *
        sum(SUC k..b)
        (\i. min(max(X i x) (--c)) c -
             expectation p (\y. min(max(X i y) (--c)) c)) *
        indicator_fn {z | z IN prob_carrier p /\
          (!j. a <= j /\ j < k ==>
            abs(sum(a..j) (\i. min(max(X i z) (--c)) c -
              expectation p (\y. min(max(X i y) (--c)) c))) < t) /\
          abs(sum(a..k) (\i. min(max(X i z) (--c)) c -
            expectation p (\y. min(max(X i y) (--c)) c))) >= t} x) = &0) /\
    almost_surely p {x | ?L. ((\n. sum(0..n) (\i. X i x)) ---> L) sequentially}
    ==> real_summable (from 0)
          (\n. prob p {x | x IN prob_carrier p /\ abs(X n x) > c}) /\
        real_summable (from 0)
          (\n. expectation p (\x. min(max(X n x) (--c)) c)) /\
        real_summable (from 0)
          (\n. variance p (\x. min(max(X n x) (--c)) c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Phase 0: Setup - abbreviations and basic facts *)
  ABBREV_TAC `(Y:num->A->real) n (x:A) = min(max((X:num->A->real) n x) (--c)) c` THEN
  ABBREV_TAC
    `(Z:num->A->real) n (x:A) = (Y:num->A->real) n x - expectation p (\y. Y n y)` THEN
  SUBGOAL_THEN `!n (x:A). (Z:num->A->real) n x =
    min(max((X:num->A->real) n x) (--c)) c -
    expectation p (\y. min(max(X n y) (--c)) c)` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. random_variable p ((X:num->A->real) n)` ASSUME_TAC THENL
  [ASM_MESON_TAC[INTEGRABLE_IMP_RANDOM_VARIABLE]; ALL_TAC] THEN
  (* Phase 1: C1 -- tail probability summability *)
  SUBGOAL_THEN `real_summable (from 0)
    (\n. prob p {x | x IN prob_carrier p /\ abs((X:num->A->real) n x) > c})`
    ASSUME_TAC THENL
  [MATCH_MP_TAC THREE_SERIES_CONDITION1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Phase 2: a.s. convergence of sum Y *)
  SUBGOAL_THEN `almost_surely p {x | ?L. ((\n. sum(0..n) (\i.
    min(max((X:num->A->real) i x) (--c)) c)) ---> L) sequentially}`
    ASSUME_TAC THENL
  [MATCH_MP_TAC THREE_SERIES_REDUCTION THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Phase 3: Integrability and structural facts *)
  SUBGOAL_THEN `!n. integrable p (\x:A. (Y:num->A->real) n x)` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_CURRY_TAC "Y" THEN
   MATCH_MP_TAC INTEGRABLE_CLAMP THEN REWRITE_TAC[ETA_AX] THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n (x:A). abs((Y:num->A->real) n x) <= c`
    ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN EXPAND_CURRY_TAC "Y" THEN
   REWRITE_TAC[real_max; real_min] THEN
   REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `!n. integrable p (\x:A. (Y:num->A->real) n x pow 2)`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
   EXISTS_TAC `(c:real) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
    MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
   MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!i j. ~(i = j) ==>
    covariance p (\x:A. (Y:num->A->real) i x) (\x. Y j x) = &0` ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `\x:A. (Y:num->A->real) i x`;
     `\x:A. (Y:num->A->real) j x`;
     `expectation p (\y:A. (Y:num->A->real) i y)`;
     `expectation p (\y:A. (Y:num->A->real) j y)`]
     COVARIANCE_SHIFT) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(SUBST1_TAC o GSYM) THEN
   BETA_TAC THEN FOLD_CURRY_TAC "Z" THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n (x:A). abs(sum(0..n) (\i. (Y:num->A->real) i x)) <=
    &(n + 1) * c` ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `sum(0..n) (\i. abs((Y:num->A->real) i x))` THEN
   CONJ_TAC THENL [REWRITE_TAC[SUM_ABS_NUMSEG]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `sum(0..n) (\i:num. c)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_MESON_TAC[];
    REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0] THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n. random_variable p
    (\x:A. sum(0..n) (\i. (Y:num->A->real) i x))` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN
   GEN_TAC THEN DISCH_TAC THEN
   SUBGOAL_THEN `(Y:num->A->real) i = (\x. Y i x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
   MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n. integrable p
    (\x:A. sum(0..n) (\i. (Y:num->A->real) i x) pow 2)` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
   EXISTS_TAC `(&(n + 1) * c) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
   MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n. integrable p
    (\x:A. sum(0..n) (\i. (Y:num->A->real) i x) pow 4)` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
   EXISTS_TAC `(&(n + 1) * c) pow 4` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
   MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* Phase 4: Fourth moment bound for non-centered Y *)
  SUBGOAL_THEN `!n. expectation p
    (\x:A. sum(0..n) (\i. (Y:num->A->real) i x) pow 4) <=
    &8 * C * expectation p (\x. sum(0..n) (\i. Y i x) pow 2) pow 2`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   ABBREV_TAC `(T_n:A->real) (x:A) = sum(0..n) (\i. (Z:num->A->real) i x)` THEN
   ABBREV_TAC
     `M_n = sum(0..n) (\i. expectation p (\y:A. (Y:num->A->real) i y))` THEN
   SUBGOAL_THEN `!x:A. sum(0..n) (\i. (Y:num->A->real) i x) =
     (T_n:A->real) x + M_n` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_CURRY_TAC "T_n" THEN EXPAND_TAC "M_n" THEN
    EXPAND_CURRY_TAC "Z" THEN
    REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `expectation p (\x:A. (T_n:A->real) x pow 4) <=
     C * expectation p (\x. T_n x pow 2) pow 2` ASSUME_TAC THENL
   [EXPAND_CURRY_TAC "T_n" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `!(a:real) b. (a + b) pow 4 <= &8 * (a pow 4 + b pow 4)`
     ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 * (a pow 2 + b pow 2)) pow 2` THEN CONJ_TAC THENL
    [SUBGOAL_THEN `(a + b:real) pow 4 = ((a + b) pow 2) pow 2`
       SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
     MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
     MP_TAC(SPEC `a - b:real` REAL_LE_POW_2) THEN REWRITE_TAC[REAL_POW_2] THEN
     REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPEC `(a:real) pow 2 - b pow 2` REAL_LE_POW_2) THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `!n. integrable p (\x:A. (Z:num->A->real) n x)` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_CURRY_TAC "Z" THEN
    MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[INTEGRABLE_CONST];
    ALL_TAC] THEN
   SUBGOAL_THEN `!i. expectation p (\x:A. (Z:num->A->real) i x) = &0`
     ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_CURRY_TAC "Z" THEN
    W(MP_TAC o PART_MATCH (lhand o rand) EXPECTATION_SUB o lhand o snd) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[EXPECTATION_CONST] THEN
    MATCH_MP_TAC(REAL_ARITH `a = b ==> a - b = &0`) THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM];
    ALL_TAC] THEN
   SUBGOAL_THEN `integrable p (\x:A. (T_n:A->real) x)` ASSUME_TAC THENL
   [EXPAND_CURRY_TAC "T_n" THEN
    MATCH_MP_TAC INTEGRABLE_SUM THEN
    REWRITE_TAC[IN_NUMSEG; LE_0] THEN GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(Z:num->A->real) i = (\x. Z i x)` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `expectation p (\x:A. (T_n:A->real) x) = &0` ASSUME_TAC THENL
   [EXPAND_CURRY_TAC "T_n" THEN
    W(MP_TAC o PART_MATCH (lhand o rand) EXPECTATION_SUM o lhand o snd) THEN
    ANTS_TAC THENL
    [REWRITE_TAC[IN_NUMSEG; LE_0] THEN GEN_TAC THEN DISCH_TAC THEN
     SUBGOAL_THEN `(Z:num->A->real) i = (\x. Z i x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN BETA_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(Z:num->A->real) i = (\x. Z i x)` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `integrable p (\x:A. (T_n:A->real) x pow 2)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
    EXISTS_TAC `(&(n + 1) * &2 * c) pow 2` THEN
    CONJ_TAC THENL
    [EXPAND_CURRY_TAC "T_n" THEN
     MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
     MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN
     GEN_TAC THEN DISCH_TAC THEN
     SUBGOAL_THEN `(Z:num->A->real) i = (\x. Z i x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
     MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..n) (\i. abs((Z:num->A->real) i x))` THEN
    CONJ_TAC THENL
    [EXPAND_CURRY_TAC "T_n" THEN REWRITE_TAC[SUM_ABS_NUMSEG];
     ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..n) (\i:num. &2 * c)` THEN CONJ_TAC THENL
    [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
     ASM_MESON_TAC[];
     REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
   SUBGOAL_THEN `integrable p (\x:A. &2 * (T_n:A->real) x * M_n)`
     ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x:A. &2 * (T_n:A->real) x * M_n) =
     (\x. (&2 * M_n) * T_n x)` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
    MATCH_MP_TAC INTEGRABLE_CMUL THEN
    SUBGOAL_THEN `(T_n:A->real) = (\x:A. T_n x)` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `integrable p (\x:A. (T_n:A->real) x pow 4)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
    EXISTS_TAC `(&(n + 1) * &2 * c) pow 4` THEN
    CONJ_TAC THENL
    [EXPAND_CURRY_TAC "T_n" THEN
     MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
     MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN
     GEN_TAC THEN DISCH_TAC THEN
     SUBGOAL_THEN `(Z:num->A->real) i = (\x. Z i x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
     MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..n) (\i. abs((Z:num->A->real) i x))` THEN
    CONJ_TAC THENL
    [EXPAND_CURRY_TAC "T_n" THEN REWRITE_TAC[SUM_ABS_NUMSEG];
     ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..n) (\i:num. &2 * c)` THEN CONJ_TAC THENL
    [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
     ASM_MESON_TAC[];
     REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= expectation p (\x:A. (T_n:A->real) x pow 2)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC EXPECTATION_POS THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
   SUBGOAL_THEN `expectation p (\x:A. &2 * (T_n:A->real) x * M_n) = &0`
     ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x:A. &2 * (T_n:A->real) x * M_n) =
     (\x. (&2 * M_n) * T_n x)` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) EXPECTATION_CMUL o lhand o snd) THEN
    ANTS_TAC THENL
    [SUBGOAL_THEN `(T_n:A->real) = (\x:A. T_n x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `expectation p (T_n:A->real) =
      expectation p (\x:A. T_n x)` SUBST1_TAC THENL
    [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `(\x:A. sum(0..n) (\i. (Y:num->A->real) i x) pow 4) =
     (\x. ((T_n:A->real) x + M_n) pow 4)` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `expectation p
     (\x:A. sum(0..n) (\i. (Y:num->A->real) i x) pow 2) =
     expectation p (\x. (T_n:A->real) x pow 2) + M_n pow 2`
     SUBST1_TAC THENL
   [SUBGOAL_THEN `(\x:A. sum(0..n) (\i. (Y:num->A->real) i x) pow 2) =
     (\x. (T_n:A->real) x pow 2 + &2 * T_n x * M_n + M_n pow 2)`
     SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) EXPECTATION_ADD o lhand o snd) THEN
    ANTS_TAC THENL
    [CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[INTEGRABLE_CONST]];
     ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) EXPECTATION_ADD o
      rand o lhand o snd) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[EXPECTATION_CONST] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `&8 * C *
     (expectation p (\x:A. (T_n:A->real) x pow 2) pow 2 + M_n pow 4)` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&8 *
      (expectation p (\x:A. (T_n:A->real) x pow 4) + M_n pow 4)` THEN
    CONJ_TAC THENL
    [SUBGOAL_THEN `expectation p
       (\x:A. &8 * ((T_n:A->real) x pow 4 + M_n pow 4)) =
       &8 * (expectation p (\x. T_n x pow 4) + M_n pow 4)`
       ASSUME_TAC THENL
     [W(MP_TAC o PART_MATCH (lhand o rand) EXPECTATION_CMUL o
        lhand o snd) THEN
      ANTS_TAC THENL
      [MATCH_MP_TAC INTEGRABLE_ADD THEN
       ASM_REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
      W(MP_TAC o PART_MATCH (lhand o rand) EXPECTATION_ADD o
        lhand o snd) THEN
      ANTS_TAC THENL
      [ASM_REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[EXPECTATION_CONST];
      ALL_TAC] THEN
     FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
     MATCH_MP_TAC EXPECTATION_MONO THEN
     REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `(\x:A. ((T_n:A->real) x + M_n) pow 4) =
       (\x. sum(0..n) (\i. (Y:num->A->real) i x) pow 4)` SUBST1_TAC THENL
      [REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC INTEGRABLE_CMUL THEN
      MATCH_MP_TAC INTEGRABLE_ADD THEN
      ASM_REWRITE_TAC[INTEGRABLE_CONST];
      GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]];
     MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
     REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
     MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
      [ASM_REWRITE_TAC[];
       SUBGOAL_THEN `(M_n:real) pow 4 = (M_n pow 2) pow 2`
         (fun th -> REWRITE_TAC[th; REAL_LE_POW_2]) THEN
       REWRITE_TAC[REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV]]];
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(M_n:real) pow 4 = (M_n pow 2) pow 2`
      SUBST1_TAC THENL
    [REWRITE_TAC[REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &2 * expectation p
      (\x:A. (T_n:A->real) x pow 2) * (M_n:real) pow 2` MP_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]];
     ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* Phase 5: C3 via SUMMABLE_VARIANCE_FROM_CONVERGENCE *)
  SUBGOAL_THEN `real_summable (from 0) (\n. variance p (\x:A. (Y:num->A->real) n x))`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `Y:num->A->real`; `&8 * C`]
    SUMMABLE_VARIANCE_FROM_CONVERGENCE) THEN
   ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC;
     GEN_TAC THEN
     ONCE_REWRITE_TAC[GSYM(ISPEC `(Y:num->A->real) n` ETA_AX)] THEN
     ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[];
     REPEAT STRIP_TAC THEN
     ONCE_REWRITE_TAC[GSYM(ISPEC `(Y:num->A->real) i` ETA_AX)] THEN
     ONCE_REWRITE_TAC[GSYM(ISPEC `(Y:num->A->real) j` ETA_AX)] THEN
     ASM_SIMP_TAC[];
     ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[];
     REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[];
     EXPAND_CURRY_TAC "Y" THEN ASM_REWRITE_TAC[]];
    SIMP_TAC[ETA_AX]];
   ALL_TAC] THEN
  (* Phase 6+7: Combine C1, C2, C3 *)
  SUBGOAL_THEN `!n (x:A). min(max((X:num->A->real) n x) (--c)) c =
    (Y:num->A->real) n x` (fun th -> REWRITE_TAC[th]) THENL
  [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  EXPAND_CURRY_TAC "Y" THEN
  SUBGOAL_THEN `real_summable (from 0) (\n. variance p
    (\x:A. min(max((X:num->A->real) n x)(--c)) c))` ASSUME_TAC THENL
  [UNDISCH_TAC `real_summable (from 0)
     (\n. variance p (\x:A. (Y:num->A->real) n x))` THEN
   EXPAND_CURRY_TAC "Y" THEN SIMP_TAC[];
   ALL_TAC] THEN
  MATCH_MP_TAC THREE_SERIES_CONDITION2 THEN
  REPEAT CONJ_TAC THENL
  [FIRST_ASSUM ACCEPT_TAC;
   FIRST_ASSUM ACCEPT_TAC;
   FIRST_ASSUM ACCEPT_TAC;
   PURE_REWRITE_TAC[GSYM(ASSUME `!n (x:A). (Z:num->A->real) n x =
     min (max ((X:num->A->real) n x) (--c)) c -
     expectation p (\y. min (max (X n y) (--c)) c)`)] THEN
   FIRST_ASSUM ACCEPT_TAC;
   PURE_REWRITE_TAC[GSYM(ASSUME `!n (x:A). (Z:num->A->real) n x =
     min (max ((X:num->A->real) n x) (--c)) c -
     expectation p (\y. min (max (X n y) (--c)) c)`)] THEN
   FIRST_ASSUM ACCEPT_TAC;
   PURE_REWRITE_TAC[GSYM(ASSUME `!n (x:A). (Z:num->A->real) n x =
     min (max ((X:num->A->real) n x) (--c)) c -
     expectation p (\y. min (max (X n y) (--c)) c)`)] THEN
   FIRST_ASSUM ACCEPT_TAC;
   FIRST_ASSUM ACCEPT_TAC;
   FIRST_ASSUM ACCEPT_TAC]);;


(* ================================================================== *)
(* Mutual independence infrastructure                                 *)
(* ================================================================== *)

(* Mutual independence of a sequence of random variables: finite-dimensional
   distributions factorize into marginals for all finite subsets. *)
let mutually_indep_rv_seq = new_definition
 `mutually_indep_rv_seq (p:A prob_space) (X:num->A->real) <=>
  (!n. random_variable p (X n)) /\
  (!S a. FINITE S /\ ~(S = {}) ==>
    prob p (INTERS (IMAGE (\n. {x | x IN prob_carrier p /\ X n x <= a n}) S)) =
    product S (\n. prob p {x | x IN prob_carrier p /\ X n x <= a n}))`;;

(* Helper: product over a two-element set *)
let PRODUCT_2 = prove
 (`!i j (f:num->real). ~(i = j) ==> product {i, j} f = f i * f j`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[PRODUCT_CLAUSES; FINITE_EMPTY; FINITE_INSERT] THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY; IN_SING; REAL_MUL_RID]);;

(* Mutual independence implies pairwise independence *)
let MUTUALLY_INDEP_RV_SEQ_PAIRWISE = prove
 (`!p:A prob_space (X:num->A->real).
   mutually_indep_rv_seq p X
   ==> !i j. ~(i = j) ==> indep_rv p (X i) (X j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mutually_indep_rv_seq; indep_rv] THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `a:real` THEN X_GEN_TAC `b:real` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`{i:num, j:num}`; `(\n:num. if n = i then a else b):num->real`]) THEN
  SIMP_TAC[FINITE_INSERT; FINITE_EMPTY; NOT_INSERT_EMPTY] THEN
  BETA_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `INTERS (IMAGE (\n. {x:A | x IN prob_carrier p /\
       X n x <= (if n = i then a else b)}) {i,j}) =
     {x | x IN prob_carrier p /\ (X:num->A->real) i x <= a /\ X j x <= b}`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
  [REWRITE_TAC[IMAGE_CLAUSES] THEN
   SUBGOAL_THEN `~(j:num = i)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN REWRITE_TAC[INTERS_2] THEN SET_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `product {i,j} (\n:num. prob (p:A prob_space)
       {w:A | w IN prob_carrier p /\
              (X:num->A->real) n w <= (if n = i then a else b)}) =
     prob p {w | w IN prob_carrier p /\ X i w <= a} *
     prob p {w | w IN prob_carrier p /\ X j w <= b}`
    (fun th -> ASM_REWRITE_TAC[th]) THEN
  ASM_SIMP_TAC[PRODUCT_2]);;

let MUTUALLY_INDEP_CDF_POINT_MASS_MIXED = prove
 (`!p:A prob_space (Z:num->A->real) (a:num->real) (v:num->real)
     (R:num->bool) (U:num->bool).
    mutually_indep_rv_seq p Z /\
    (!i. i IN U ==> simple_rv p (Z i)) /\
    FINITE R /\ FINITE U /\ DISJOINT R U /\ ~(R UNION U = EMPTY)
    ==> prob p
          (INTERS (IMAGE (\t. {x | x IN prob_carrier p /\ Z t x <= a t}) R)
           INTER
           INTERS (IMAGE (\u. {x | x IN prob_carrier p /\ Z u x = v u}) U))
      = product R (\t. prob p {x | x IN prob_carrier p /\ Z t x <= a t}) *
        product U (\u. prob p {x | x IN prob_carrier p /\ Z u x = v u})`,
  GEN_TAC THEN GEN_TAC THEN
  SUBGOAL_THEN
    `!U:num->bool. FINITE U ==>
      !a:num->real v:num->real (R:num->bool).
        mutually_indep_rv_seq (p:A prob_space) (Z:num->A->real) /\
        (!i. i IN U ==> simple_rv p (Z i)) /\
        FINITE R /\ DISJOINT R U /\ ~(R UNION U = {})
        ==> prob p
              (INTERS (IMAGE (\t. {x:A | x IN prob_carrier p /\ Z t x <= a t}) R)
               INTER
               INTERS (IMAGE (\u. {x:A | x IN prob_carrier p /\ Z u x = v u}) U))
          = product R (\t. prob p {x:A | x IN prob_carrier p /\ Z t x <= a t}) *
            product U (\u. prob p {x:A | x IN prob_carrier p /\ Z u x = v u})`
    ASSUME_TAC THENL
  [MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [(* === BASE CASE === *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[IMAGE_CLAUSES; INTERS_0; INTER_UNIV;
                PRODUCT_CLAUSES; REAL_MUL_RID] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mutually_indep_rv_seq]) THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`R:num->bool`; `a:num->real`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `~((R:num->bool) UNION {} = {})` THEN
    REWRITE_TAC[UNION_EMPTY];
    ALL_TAC] THEN
   (* === INDUCTIVE STEP === *)
   X_GEN_TAC `u:num` THEN X_GEN_TAC `U':num->bool` THEN STRIP_TAC THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `~(u:num IN R)` ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT (R:num->bool) (u INSERT U')` THEN SET_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `DISJOINT (R:num->bool) (U':num->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT (R:num->bool) (u INSERT U')` THEN SET_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `DISJOINT (u INSERT R:num->bool) (U':num->bool)` ASSUME_TAC
   THENL
   [UNDISCH_TAC `~(u:num IN U')` THEN
    UNDISCH_TAC `DISJOINT (R:num->bool) (U':num->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `!n:num. random_variable (p:A prob_space) ((Z:num->A->real) n)`
     ASSUME_TAC THENL
   [UNDISCH_TAC `mutually_indep_rv_seq (p:A prob_space) (Z:num->A->real)` THEN
    REWRITE_TAC[mutually_indep_rv_seq] THEN MESON_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `simple_rv (p:A prob_space) ((Z:num->A->real) u)`
     ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `u:num` o
      check(fun th -> try fst(dest_forall(concl th)) = `i:num`
                      with _ -> false)) THEN
    REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
   SUBGOAL_THEN `!i:num. i IN U' ==> simple_rv (p:A prob_space) ((Z:num->A->real) i)`
     ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o
      check(fun th -> try fst(dest_forall(concl th)) = `i:num`
                      with _ -> false)) THEN
    ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
   MP_TAC(SPECL [`p:A prob_space`; `(Z:num->A->real) u`; `(v:num->real) u`]
     SIMPLE_RV_GAP_BELOW) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `w:real` (LABEL_TAC "gap")) THEN
   REWRITE_TAC[IMAGE_CLAUSES; INTERS_INSERT] THEN
   ASM_SIMP_TAC[PRODUCT_CLAUSES] THEN
   (* pm_diff -- keep it for later use *)
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ (Z:num->A->real) u x = (v:num->real) u} =
      {x | x IN prob_carrier p /\ Z u x <= v u} DIFF
      {x | x IN prob_carrier p /\ Z u x <= w}`
     (LABEL_TAC "pm_diff") THENL
   [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
    ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:A) IN prob_carrier p` THEN
    DISCH_THEN(fun xth -> USE_THEN "gap" (fun gap ->
      ASSUME_TAC(MP (SPEC `x:A` gap) xth))) THEN
    ASM_CASES_TAC `(Z:num->A->real) u (x:A) <= w` THEN
    ASM_CASES_TAC `(Z:num->A->real) u (x:A) <= (v:num->real) u` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   (* Events membership *)
   SUBGOAL_THEN
     `!t:num a':real.
        {x:A | x IN prob_carrier p /\ (Z:num->A->real) t x <= a'} IN
        prob_events p`
     ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:num` o
      check(fun th -> try fst(dest_forall(concl th)) = `n:num`
                      with _ -> false)) THEN
    REWRITE_TAC[random_variable] THEN MESON_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN
     `!t:num v':real.
        {x:A | x IN prob_carrier p /\ (Z:num->A->real) t x = v'} IN
        prob_events p`
     ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `(Z:num->A->real) t`; `v':real`]
      RANDOM_VARIABLE_LEVEL_SET) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   (* Rewrite {Z u = v u} as DIFF in the LHS -- USE not REMOVE *)
   USE_THEN "pm_diff" (fun th ->
     GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o LAND_CONV) [th]) THEN
   (* Distribute INTER over DIFF *)
   SUBGOAL_THEN
     `INTERS (IMAGE (\t. {x:A | x IN prob_carrier p /\
        (Z:num->A->real) t x <= (a:num->real) t}) R) INTER
      (({x | x IN prob_carrier p /\ Z u x <= (v:num->real) u} DIFF
        {x | x IN prob_carrier p /\ Z u x <= w}) INTER
       INTERS (IMAGE (\u'. {x | x IN prob_carrier p /\ Z u' x = v u'}) U'))
      = (INTERS (IMAGE (\t. {x | x IN prob_carrier p /\ Z t x <= a t}) R) INTER
         {x | x IN prob_carrier p /\ Z u x <= v u} INTER
         INTERS (IMAGE (\u'. {x | x IN prob_carrier p /\ Z u' x = v u'}) U'))
        DIFF
        (INTERS (IMAGE (\t. {x | x IN prob_carrier p /\ Z t x <= a t}) R) INTER
         {x | x IN prob_carrier p /\ Z u x <= w} INTER
         INTERS (IMAGE (\u'. {x | x IN prob_carrier p /\ Z u' x = v u'}) U'))`
     SUBST1_TAC THENL
   [MATCH_ACCEPT_TAC(SET_RULE
      `!A B C D:A->bool.
         A INTER ((B DIFF C) INTER D) =
         (A INTER B INTER D) DIFF (A INTER C INTER D)`);
    ALL_TAC] THEN
   (* ABBREV_TAC with labels *)
   ABBREV_TAC `termA =
     INTERS (IMAGE (\t. {x:A | x IN prob_carrier p /\
       (Z:num->A->real) t x <= (a:num->real) t}) R) INTER
     {x | x IN prob_carrier p /\ Z u x <= (v:num->real) u} INTER
     INTERS (IMAGE (\u'. {x | x IN prob_carrier p /\ Z u' x = v u'}) U')` THEN
   POP_ASSUM(LABEL_TAC "termA_def") THEN
   ABBREV_TAC `termB =
     INTERS (IMAGE (\t. {x:A | x IN prob_carrier p /\
       (Z:num->A->real) t x <= (a:num->real) t}) R) INTER
     {x | x IN prob_carrier p /\ Z u x <= w} INTER
     INTERS (IMAGE (\u'. {x | x IN prob_carrier p /\ Z u' x = (v:num->real) u'}) U')` THEN
   POP_ASSUM(LABEL_TAC "termB_def") THEN
   (* === termB SUBSET termA === *)
   SUBGOAL_THEN `termB SUBSET (termA:A->bool)` ASSUME_TAC THENL
   [REMOVE_THEN "termA_def" (fun ta -> REMOVE_THEN "termB_def" (fun tb ->
      SUBST1_TAC(SYM ta) THEN SUBST1_TAC(SYM tb))) THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:A) IN prob_carrier p` THEN
    DISCH_THEN(fun xth -> USE_THEN "gap" (fun gap ->
      ASSUME_TAC(MP (SPEC `x:A` gap) xth))) THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   (* === Measurability === *)
   SUBGOAL_THEN `(termA:A->bool) IN prob_events p /\
                  (termB:A->bool) IN prob_events p` STRIP_ASSUME_TAC THENL
   [REMOVE_THEN "termA_def" (fun ta -> REMOVE_THEN "termB_def" (fun tb ->
      SUBST1_TAC(SYM ta) THEN SUBST1_TAC(SYM tb))) THEN
    ASM_CASES_TAC `(R:num->bool) = {}` THENL
    [ASM_REWRITE_TAC[IMAGE_CLAUSES; INTERS_0; INTER_UNIV] THEN
     ASM_CASES_TAC `(U':num->bool) = {}` THENL
     [ASM_REWRITE_TAC[IMAGE_CLAUSES; INTERS_0; INTER_UNIV]; ALL_TAC] THEN
     SUBGOAL_THEN
       `INTERS (IMAGE (\u'. {x:A | x IN prob_carrier p /\
          (Z:num->A->real) u' x = (v:num->real) u'}) U') IN prob_events p`
       ASSUME_TAC THENL
     [MATCH_MP_TAC PROB_COUNTABLE_INTERS_IN_EVENTS THEN
      ASM_SIMP_TAC[FINITE_IMP_COUNTABLE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `i':num` THEN DISCH_TAC THEN BETA_TAC THEN
      FIRST_ASSUM MATCH_ACCEPT_TAC; ALL_TAC] THEN
     CONJ_TAC THEN MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `INTERS (IMAGE (\t. {x:A | x IN prob_carrier p /\
         (Z:num->A->real) t x <= (a:num->real) t}) R) IN prob_events p`
      ASSUME_TAC THENL
    [MATCH_MP_TAC PROB_COUNTABLE_INTERS_IN_EVENTS THEN
     ASM_SIMP_TAC[FINITE_IMP_COUNTABLE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
     REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
     X_GEN_TAC `t':num` THEN DISCH_TAC THEN BETA_TAC THEN
     FIRST_ASSUM MATCH_ACCEPT_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `(U':num->bool) = {}` THENL
    [ASM_REWRITE_TAC[IMAGE_CLAUSES; INTERS_0; INTER_UNIV] THEN
     CONJ_TAC THEN MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `INTERS (IMAGE (\u'. {x:A | x IN prob_carrier p /\
         (Z:num->A->real) u' x = (v:num->real) u'}) U') IN prob_events p`
      ASSUME_TAC THENL
    [MATCH_MP_TAC PROB_COUNTABLE_INTERS_IN_EVENTS THEN
     ASM_SIMP_TAC[FINITE_IMP_COUNTABLE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
     REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
     X_GEN_TAC `i':num` THEN DISCH_TAC THEN BETA_TAC THEN
     FIRST_ASSUM MATCH_ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN ASM_REWRITE_TAC[]];
     MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
   (* === PROB_DIFF_SUBSET === *)
   SUBGOAL_THEN
     `prob (p:A prob_space) (termA DIFF termB:A->bool) =
      prob p termA - prob p termB`
     SUBST1_TAC THENL
   [MATCH_MP_TAC PROB_DIFF_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   (* === termA evaluation === *)
   SUBGOAL_THEN
     `prob (p:A prob_space) (termA:A->bool) =
      prob p {x:A | x IN prob_carrier p /\ (Z:num->A->real) u x <=
        (v:num->real) u} *
      product R (\t. prob p {x | x IN prob_carrier p /\ Z t x <=
        (a:num->real) t}) *
      product U' (\u'. prob p {x | x IN prob_carrier p /\ Z u' x = v u'})`
     SUBST1_TAC THENL
   [REMOVE_THEN "termA_def" (fun ta -> REMOVE_THEN "termB_def" (fun _ ->
      SUBST1_TAC(SYM ta))) THEN
    SUBGOAL_THEN
      `INTERS (IMAGE (\t. {x:A | x IN prob_carrier p /\
         (Z:num->A->real) t x <= (a:num->real) t}) R) INTER
       {x | x IN prob_carrier p /\ Z u x <= (v:num->real) u} INTER
       INTERS (IMAGE (\u'. {x | x IN prob_carrier p /\ Z u' x = v u'}) U')
       = INTERS (IMAGE (\t. {x | x IN prob_carrier p /\ Z t x <=
           ((\t:num. if t = u then v u else a t) t)}) (u INSERT R)) INTER
         INTERS (IMAGE (\u'. {x | x IN prob_carrier p /\ Z u' x = v u'}) U')`
      SUBST1_TAC THENL
    [REWRITE_TAC[IMAGE_CLAUSES; INTERS_INSERT] THEN
     GEN_REWRITE_TAC LAND_CONV [GSYM INTER_ASSOC] THEN
     AP_THM_TAC THEN AP_TERM_TAC THEN
     GEN_REWRITE_TAC LAND_CONV [INTER_COMM] THEN
     BINOP_TAC THENL
     [REFL_TAC;
      AP_TERM_TAC THEN
      MATCH_MP_TAC IMAGE_EQ THEN X_GEN_TAC `t:num` THEN DISCH_TAC THEN
      BETA_TAC THEN
      SUBGOAL_THEN `~(t:num = u)` (fun th -> REWRITE_TAC[th]) THEN
      (UNDISCH_TAC `(t:num) IN R` THEN
       UNDISCH_TAC `~(u:num IN R)` THEN MESON_TAC[])]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`(\t:num. if t = u then (v:num->real) u else (a:num->real) t)`;
       `v:num->real`; `u INSERT (R:num->bool)`]) THEN
    ASM_REWRITE_TAC[FINITE_INSERT; EMPTY_UNION; NOT_INSERT_EMPTY] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[PRODUCT_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    BINOP_TAC THENL
    [REFL_TAC;
     BINOP_TAC THENL
     [MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `t:num` THEN DISCH_TAC THEN
      BETA_TAC THEN
      SUBGOAL_THEN `~(t:num = u)` (fun th -> REWRITE_TAC[th]) THEN
      (UNDISCH_TAC `(t:num) IN R` THEN
       UNDISCH_TAC `~(u:num IN R)` THEN MESON_TAC[]);
      REFL_TAC]]; ALL_TAC] THEN
   (* === termB evaluation === *)
   SUBGOAL_THEN
     `prob (p:A prob_space) (termB:A->bool) =
      prob p {x:A | x IN prob_carrier p /\ (Z:num->A->real) u x <= w} *
      product R (\t. prob p {x | x IN prob_carrier p /\ Z t x <=
        (a:num->real) t}) *
      product U' (\u'. prob p {x | x IN prob_carrier p /\ Z u' x =
        (v:num->real) u'})`
     SUBST1_TAC THENL
   [REMOVE_THEN "termB_def" (fun tb -> SUBST1_TAC(SYM tb)) THEN
    SUBGOAL_THEN
      `INTERS (IMAGE (\t. {x:A | x IN prob_carrier p /\
         (Z:num->A->real) t x <= (a:num->real) t}) R) INTER
       {x | x IN prob_carrier p /\ Z u x <= w} INTER
       INTERS (IMAGE (\u'. {x | x IN prob_carrier p /\ Z u' x =
         (v:num->real) u'}) U')
       = INTERS (IMAGE (\t. {x | x IN prob_carrier p /\ Z t x <=
           ((\t:num. if t = u then w else a t) t)}) (u INSERT R)) INTER
         INTERS (IMAGE (\u'. {x | x IN prob_carrier p /\ Z u' x = v u'}) U')`
      SUBST1_TAC THENL
    [REWRITE_TAC[IMAGE_CLAUSES; INTERS_INSERT] THEN
     GEN_REWRITE_TAC LAND_CONV [GSYM INTER_ASSOC] THEN
     AP_THM_TAC THEN AP_TERM_TAC THEN
     GEN_REWRITE_TAC LAND_CONV [INTER_COMM] THEN
     BINOP_TAC THENL
     [REFL_TAC;
      AP_TERM_TAC THEN
      MATCH_MP_TAC IMAGE_EQ THEN X_GEN_TAC `t:num` THEN DISCH_TAC THEN
      BETA_TAC THEN
      SUBGOAL_THEN `~(t:num = u)` (fun th -> REWRITE_TAC[th]) THEN
      (UNDISCH_TAC `(t:num) IN R` THEN
       UNDISCH_TAC `~(u:num IN R)` THEN MESON_TAC[])]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`(\t:num. if t = u then w else (a:num->real) t)`;
       `v:num->real`; `u INSERT (R:num->bool)`]) THEN
    ASM_REWRITE_TAC[FINITE_INSERT; EMPTY_UNION; NOT_INSERT_EMPTY] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[PRODUCT_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    BINOP_TAC THENL
    [REFL_TAC;
     BINOP_TAC THENL
     [MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `t:num` THEN DISCH_TAC THEN
      BETA_TAC THEN
      SUBGOAL_THEN `~(t:num = u)` (fun th -> REWRITE_TAC[th]) THEN
      (UNDISCH_TAC `(t:num) IN R` THEN
       UNDISCH_TAC `~(u:num IN R)` THEN MESON_TAC[]);
      REFL_TAC]]; ALL_TAC] THEN
   (* === Point-mass probability: prob p {=v u} = pv - pw === *)
   SUBGOAL_THEN
     `prob (p:A prob_space)
       {x:A | x IN prob_carrier p /\ (Z:num->A->real) u x = (v:num->real) u} =
      prob p {x | x IN prob_carrier p /\ Z u x <= v u} -
      prob p {x | x IN prob_carrier p /\ Z u x <= w}`
     SUBST1_TAC THENL
   [USE_THEN "pm_diff" (fun th ->
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    MATCH_MP_TAC PROB_DIFF_SUBSET THEN
    CONJ_TAC THENL [FIRST_ASSUM MATCH_ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [FIRST_ASSUM MATCH_ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:A) IN prob_carrier p` THEN
    DISCH_THEN(fun xth -> USE_THEN "gap" (fun gap ->
      ASSUME_TAC(MP (SPEC `x:A` gap) xth))) THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   (* === Final algebra === *)
   CONV_TAC(RAND_CONV(RAND_CONV(RAND_CONV(RAND_CONV
     (ALPHA_CONV `u':num`))))) THEN
   ABBREV_TAC `pv:real = prob (p:A prob_space)
     {x:A | x IN prob_carrier p /\ (Z:num->A->real) u x <= (v:num->real) u}` THEN
   ABBREV_TAC `pw:real = prob (p:A prob_space)
     {x:A | x IN prob_carrier p /\ (Z:num->A->real) u x <= w}` THEN
   ABBREV_TAC `pr:real = product R
     (\t:num. prob (p:A prob_space)
       {x:A | x IN prob_carrier p /\ (Z:num->A->real) t x <= (a:num->real) t})` THEN
   ABBREV_TAC `pu:real = product (U':num->bool)
     (\u'. prob (p:A prob_space)
       {x:A | x IN prob_carrier p /\ (Z:num->A->real) u' x = (v:num->real) u'})` THEN
   CONV_TAC REAL_RING;
   ALL_TAC] THEN
  (* === Outer wrapper === *)
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `U:num->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL
    [`a:num->real`; `v:num->real`; `R:num->bool`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* Corollary: pure multivariate point-mass factorization *)
let MUTUALLY_INDEP_POINT_MASS = prove
 (`!p:A prob_space (Z:num->A->real) (v:num->real) (S:num->bool).
    mutually_indep_rv_seq p Z /\
    (!i. i IN S ==> simple_rv p (Z i)) /\
    FINITE S /\ ~(S = {})
    ==> prob p
          (INTERS (IMAGE (\i. {x | x IN prob_carrier p /\ Z i x = v i}) S))
      = product S (\i. prob p {x | x IN prob_carrier p /\ Z i x = v i})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `Z:num->A->real`;
                  `(\n:num. &0):num->real`; `v:num->real`;
                  `EMPTY:num->bool`; `S:num->bool`]
    MUTUALLY_INDEP_CDF_POINT_MASS_MIXED) THEN
  ASM_REWRITE_TAC[FINITE_EMPTY; DISJOINT_EMPTY; UNION_EMPTY;
    IMAGE_CLAUSES; INTERS_0; INTER_UNIV; PRODUCT_CLAUSES; REAL_MUL_LID]);;


(* Helper: CDF events are in prob_events *)
let RV_CDF_EVENTS = prove
 (`random_variable (p:A prob_space) (f:A->real)
   ==> {x | x IN prob_carrier p /\ f x <= a} IN prob_events p`,
  REWRITE_TAC[random_variable] THEN MESON_TAC[]);;

(* Lemma A: Shifting preserves mutual independence *)
let MUTUALLY_INDEP_RV_SEQ_SHIFT = prove
 (`!p:A prob_space (Z:num->A->real) c.
    mutually_indep_rv_seq p Z
    ==> mutually_indep_rv_seq p (\i x. Z i x + c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mutually_indep_rv_seq] THEN STRIP_TAC THEN
  CONJ_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_SHIFT THEN
   ASM_REWRITE_TAC[ETA_AX];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `IMAGE (\n. {x:A | x IN prob_carrier p /\
       (Z:num->A->real) n x + c <= (a:num->real) n}) S =
     IMAGE (\n. {x | x IN prob_carrier p /\ Z n x <= a n - c}) S`
    SUBST1_TAC THENL
  [MATCH_MP_TAC IMAGE_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
   REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
   ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!n:num. prob p {x:A | x IN prob_carrier p /\
       (Z:num->A->real) n x + c <= (a:num->real) n} =
     prob p {x | x IN prob_carrier p /\ Z n x <= a n - c}`
    (fun th -> REWRITE_TAC[th]) THENL
  [GEN_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
   ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`S:num->bool`; `\n:num. (a:num->real) n - c`]) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC);;

(* Helper: Finite product of convergent sequences converges *)
let REALLIM_PRODUCT_FINITE = prove
 (`!S:B->bool (f:B->num->real) (g:B->real).
    FINITE S /\
    (!i. i IN S ==> ((\n. f i n) ---> g i) sequentially)
    ==> ((\n. product S (\i. f i n)) ---> product S g) sequentially`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
  [REPEAT GEN_TAC THEN DISCH_TAC THEN
   REWRITE_TAC[PRODUCT_CLAUSES; REALLIM_CONST];
   ALL_TAC] THEN
  X_GEN_TAC `s:B` THEN X_GEN_TAC `S':B->bool` THEN STRIP_TAC THEN
  X_GEN_TAC `f:B->num->real` THEN X_GEN_TAC `g:B->real` THEN
  DISCH_TAC THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES] THEN
  MATCH_MP_TAC REALLIM_MUL THEN CONJ_TAC THENL
  [UNDISCH_TAC `!i:B. i IN s INSERT S'
     ==> ((\n. (f:B->num->real) i n) ---> (g:B->real) i) sequentially` THEN
   DISCH_THEN(MP_TAC o SPEC `s:B`) THEN REWRITE_TAC[IN_INSERT];
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   X_GEN_TAC `i:B` THEN DISCH_TAC THEN
   UNDISCH_TAC `!i:B. i IN s INSERT S'
     ==> ((\n. (f:B->num->real) i n) ---> (g:B->real) i) sequentially` THEN
   DISCH_THEN(MP_TAC o SPEC `i:B`) THEN
   ASM_REWRITE_TAC[IN_INSERT]]);;

(* Lemma B: Strict inequality factorization for mutual independence *)
let MUTUALLY_INDEP_RV_SEQ_STRICT_INEQ = prove
 (`!p:A prob_space (Z:num->A->real) (a:num->real) (S:num->bool).
    mutually_indep_rv_seq p Z /\ FINITE S /\ ~(S = {})
    ==> prob p (INTERS (IMAGE (\i. {x | x IN prob_carrier p /\
          Z i x < a i}) S)) =
        product S (\i. prob p {x | x IN prob_carrier p /\ Z i x < a i})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mutually_indep_rv_seq] THEN
  STRIP_TAC THEN
  (* Measurability of joint approximants *)
  SUBGOAL_THEN
    `!n:num. INTERS (IMAGE (\i:num. {x:A | x IN prob_carrier p /\
       (Z:num->A->real) i x <= (a:num->real) i - &1 / &(SUC n)}) S)
       IN prob_events p`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC PROB_COUNTABLE_INTERS_IN_EVENTS THEN
   ASM_SIMP_TAC[FINITE_IMP_COUNTABLE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
   REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
   X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
   MATCH_MP_TAC RV_CDF_EVENTS THEN
   REWRITE_TAC[ETA_AX] THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* Monotonicity *)
  SUBGOAL_THEN
    `!n:num. INTERS (IMAGE (\i. {x:A | x IN prob_carrier p /\
       (Z:num->A->real) i x <= (a:num->real) i - &1 / &(SUC n)}) S) SUBSET
     INTERS (IMAGE (\i. {x | x IN prob_carrier p /\
       Z i x <= a i - &1 / &(SUC (SUC n))}) S)`
    ASSUME_TAC THENL
  [GEN_TAC THEN REWRITE_TAC[SUBSET; IN_INTERS; FORALL_IN_IMAGE] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `(a:num->real) i - &1 / &(SUC n)` THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[REAL_LE_SUB_LADD; REAL_ARITH `a - x + y <= a <=> y <= x`] THEN
   REWRITE_TAC[real_div; REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
   REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ARITH_TAC;
   ALL_TAC] THEN
  (* UNIONS identity *)
  SUBGOAL_THEN
    `UNIONS {INTERS (IMAGE (\i. {x:A | x IN prob_carrier p /\
       (Z:num->A->real) i x <= (a:num->real) i - &1 / &(SUC n)}) S) |
       n IN (:num)} =
     INTERS (IMAGE (\i. {x | x IN prob_carrier p /\ Z i x < a i}) S)`
    ASSUME_TAC THENL
  [REWRITE_TAC[SIMPLE_IMAGE; UNIONS_IMAGE; IN_UNIV] THEN
   REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTERS; FORALL_IN_IMAGE] THEN
   X_GEN_TAC `x:A` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `n:num` ASSUME_TAC) THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < &1 / &(SUC n)` MP_TAC THENL
    [SIMP_TAC[REAL_LT_DIV; REAL_LT_01; REAL_OF_NUM_LT; LT_0];
     ASM_REAL_ARITH_TAC];
    DISCH_TAC THEN
    SUBGOAL_THEN `(x:A) IN prob_carrier p` ASSUME_TAC THENL
    [UNDISCH_TAC `~((S:num->bool) = {})` THEN
     REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
     DISCH_THEN(X_CHOOSE_TAC `j:num`) THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN
     ASM_REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN `!i:num. i IN S ==>
      &0 < (a:num->real) i - (Z:num->A->real) i x` ASSUME_TAC THENL
    [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
     REAL_ARITH_TAC;
     ALL_TAC] THEN
    SUBGOAL_THEN
      `&0 < inf(IMAGE (\i:num. (a:num->real) i - (Z:num->A->real) i x) S)`
      ASSUME_TAC THENL
    [ASM_SIMP_TAC[REAL_LT_INF_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
     REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    MP_TAC(ISPEC
      `inf(IMAGE (\i:num. (a:num->real) i - (Z:num->A->real) i x) S)`
      REAL_ARCH_INV) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `m:num` THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&1 / &(SUC m) <= inv(&m:real)` ASSUME_TAC THENL
    [REWRITE_TAC[real_div; REAL_MUL_LID] THEN
     MATCH_MP_TAC REAL_LE_INV2 THEN
     REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
     ALL_TAC] THEN
    SUBGOAL_THEN
      `inf(IMAGE (\i:num. (a:num->real) i - (Z:num->A->real) i x) S)
       <= (a:num->real) i - (Z:num->A->real) i x`
      ASSUME_TAC THENL
    [MP_TAC(ISPEC
       `IMAGE (\i:num. (a:num->real) i - (Z:num->A->real) i x) S`
       INF_FINITE) THEN
     ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
     DISCH_THEN(MP_TAC o CONJUNCT2) THEN
     DISCH_THEN MATCH_MP_TAC THEN
     REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
     ASM_REAL_ARITH_TAC]];
   ALL_TAC] THEN
  (* Apply PROB_CONTINUITY_FROM_BELOW *)
  MP_TAC(ISPECL [`p:A prob_space`;
    `\n:num. INTERS (IMAGE (\i:num. {x:A | x IN prob_carrier p /\
       (Z:num->A->real) i x <= (a:num->real) i - &1 / &(SUC n)}) S)`]
    PROB_CONTINUITY_FROM_BELOW) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* REALLIM_UNIQUE *)
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC `\n:num. product S (\i:num. prob (p:A prob_space)
    {x:A | x IN prob_carrier p /\ (Z:num->A->real) i x <=
      (a:num->real) i - &1 / &(SUC n)})` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
  [(* product seq --> prob p (joint < a_i) *)
   SUBGOAL_THEN
     `(\n:num. product S (\i:num. prob (p:A prob_space)
        {x:A | x IN prob_carrier p /\
          (Z:num->A->real) i x <= (a:num->real) i - &1 / &(SUC n)})) =
      (\n. prob p (INTERS (IMAGE (\i. {x | x IN prob_carrier p /\
          Z i x <= a i - &1 / &(SUC n)}) S)))`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
    CONV_TAC SYM_CONV THEN
    UNDISCH_TAC `!S' (a':num->real). FINITE S' /\ ~(S' = {}) ==>
      prob (p:A prob_space) (INTERS (IMAGE (\i. {x:A | x IN prob_carrier p /\
        (Z:num->A->real) i x <= a' i}) S')) =
      product S' (\i. prob p {x | x IN prob_carrier p /\ Z i x <= a' i})` THEN
    DISCH_THEN(MP_TAC o SPECL [`S:num->bool`;
      `\i:num. (a:num->real) i - &1 / &(SUC n)`]) THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
    ASM_REWRITE_TAC[]];
   (* product seq --> product S (marginal < a_i) *)
   MATCH_MP_TAC REALLIM_PRODUCT_FINITE THEN ASM_REWRITE_TAC[] THEN
   X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `(Z:num->A->real) i`; `(a:num->real) i`]
     PROB_STRICT_INEQ_LIMIT) THEN
   ASM_REWRITE_TAC[ETA_AX]]);;

(* Lemma C: nsfa preserves mutual independence *)
let MUTUALLY_INDEP_RV_SEQ_NSFA = prove
 (`!p:A prob_space (Z:num->A->real) n.
    mutually_indep_rv_seq p Z /\
    (!i x. x IN prob_carrier p ==> &0 <= Z i x)
    ==> mutually_indep_rv_seq p (\i. nonneg_simple_fn_approx p (Z i) n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!m:num. random_variable (p:A prob_space) ((Z:num->A->real) m)`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[mutually_indep_rv_seq]; ALL_TAC] THEN
  REWRITE_TAC[mutually_indep_rv_seq] THEN CONJ_TAC THENL
  [GEN_TAC THEN BETA_TAC THEN
   MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_RV THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`S:num->bool`; `a:num->real`] THEN
  STRIP_TAC THEN BETA_TAC THEN
  ASM_CASES_TAC `?j:num. j IN S /\ (a:num->real) j < &0` THENL
  [(* Some a_j < 0: nsfa >= 0 so sets are empty *)
   FIRST_X_ASSUM(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\
        nonneg_simple_fn_approx p ((Z:num->A->real) j) n x <=
        (a:num->real) j} = {}`
     ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`p:A prob_space`; `(Z:num->A->real) j`; `n:num`; `z:A`]
      NONNEG_SIMPLE_FN_APPROX_NONNEG) THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN
     `INTERS (IMAGE (\n':num. {x:A | x IN prob_carrier p /\
        nonneg_simple_fn_approx p ((Z:num->A->real) n') n x <=
        (a:num->real) n'}) S) = {}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTERS; NOT_IN_EMPTY; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `z:A` THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN
    MP_TAC(SPECL [`p:A prob_space`; `(Z:num->A->real) j`; `n:num`; `z:A`]
      NONNEG_SIMPLE_FN_APPROX_NONNEG) THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   REWRITE_TAC[PROB_EMPTY] THEN
   SUBGOAL_THEN `S = (j:num) INSERT (S DELETE j)` SUBST1_TAC THENL
   [UNDISCH_TAC `(j:num) IN S` THEN SET_TAC[]; ALL_TAC] THEN
   ASM_SIMP_TAC[PRODUCT_CLAUSES; FINITE_DELETE; IN_DELETE] THEN
   ASM_REWRITE_TAC[PROB_EMPTY; REAL_MUL_LZERO];
   ALL_TAC] THEN
  (* All a_i >= 0 *)
  SUBGOAL_THEN `!i:num. i IN S ==> &0 <= (a:num->real) i` ASSUME_TAC THENL
  [UNDISCH_TAC `~(?j:num. j IN S /\ (a:num->real) j < &0)` THEN
   REWRITE_TAC[NOT_EXISTS_THM; DE_MORGAN_THM] THEN
   MESON_TAC[REAL_NOT_LT];
   ALL_TAC] THEN
  (* Apply NSFA_CDF_EQUIV to each index *)
  SUBGOAL_THEN
    `!i:num. i IN S ==>
      (?c:real. !x:A. x IN prob_carrier p ==>
        (nonneg_simple_fn_approx p ((Z:num->A->real) i) n x <=
         (a:num->real) i <=> Z i x < c)) \/
      (!x. x IN prob_carrier p ==>
        nonneg_simple_fn_approx p (Z i) n x <= a i)`
    ASSUME_TAC THENL
  [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   MP_TAC(SPECL [`p:A prob_space`; `(Z:num->A->real) i`; `n:num`;
     `(a:num->real) i`] NSFA_CDF_EQUIV) THEN
   ASM_SIMP_TAC[ETA_AX];
   ALL_TAC] THEN
  (* Define partition: T' = strict indices *)
  ABBREV_TAC `T' = {i:num | i IN S /\
    ~(!x:A. x IN prob_carrier p ==>
      nonneg_simple_fn_approx p ((Z:num->A->real) i) n x <=
      (a:num->real) i)}` THEN
  SUBGOAL_THEN `(T':num->bool) SUBSET S` ASSUME_TAC THENL
  [EXPAND_TAC "T'" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (T':num->bool)` ASSUME_TAC THENL
  [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  (* For i in T': strict ineq characterization *)
  SUBGOAL_THEN
    `!i:num. i IN T' ==>
      ?c:real. !x:A. x IN prob_carrier p ==>
        (nonneg_simple_fn_approx p ((Z:num->A->real) i) n x <=
         (a:num->real) i <=> Z i x < c)`
    ASSUME_TAC THENL
  [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   SUBGOAL_THEN `(i:num) IN S` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o
     check(fun th -> try fst(dest_forall(concl th)) = `i:num` &&
       is_disj(snd(dest_imp(snd(dest_forall(concl th))))) with _ -> false)) THEN
   ASM_REWRITE_TAC[] THEN
   STRIP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   UNDISCH_TAC `(i:num) IN T'` THEN
   EXPAND_TAC "T'" THEN REWRITE_TAC[IN_ELIM_THM] THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* For i in S \ T': event = carrier *)
  SUBGOAL_THEN
    `!i:num. i IN S /\ ~(i IN T') ==>
      {x:A | x IN prob_carrier p /\
        nonneg_simple_fn_approx p ((Z:num->A->real) i) n x <=
        (a:num->real) i} = prob_carrier p`
    ASSUME_TAC THENL
  [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
   SUBGOAL_THEN `!x:A. x IN prob_carrier p ==>
     nonneg_simple_fn_approx p ((Z:num->A->real) i) n x <=
     (a:num->real) i` ASSUME_TAC THENL
   [UNDISCH_TAC `~((i:num) IN T')` THEN EXPAND_TAC "T'" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
   REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
   EQ_TAC THENL [MESON_TAC[]; ASM_MESON_TAC[]];
   ALL_TAC] THEN
  (* Extract threshold function cc *)
  ABBREV_TAC `cc = \i:num. @c:real. !x:A. x IN prob_carrier p ==>
    (nonneg_simple_fn_approx p ((Z:num->A->real) i) n x <=
     (a:num->real) i <=> Z i x < c)` THEN
  SUBGOAL_THEN
    `!i:num. i IN T' ==>
      !x:A. x IN prob_carrier p ==>
        (nonneg_simple_fn_approx p ((Z:num->A->real) i) n x <=
         (a:num->real) i <=> Z i x < (cc:num->real) i)`
    ASSUME_TAC THENL
  [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   UNDISCH_TAC `!i:num. i IN T' ==>
     (?c:real. !x:A. x IN prob_carrier p ==>
       (nonneg_simple_fn_approx p ((Z:num->A->real) i) n x <=
        (a:num->real) i <=> Z i x < c))` THEN
   DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_TAC `c':real`) THEN
   EXPAND_TAC "cc" THEN BETA_TAC THEN
   CONV_TAC SELECT_CONV THEN EXISTS_TAC `c':real` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Set equality for T' events *)
  SUBGOAL_THEN
    `!i:num. i IN T' ==>
      {x:A | x IN prob_carrier p /\
        nonneg_simple_fn_approx p ((Z:num->A->real) i) n x <=
        (a:num->real) i} =
      {x | x IN prob_carrier p /\ Z i x < (cc:num->real) i}`
    ASSUME_TAC THENL
  [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
   ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* Case split: T' = {} vs T' <> {} *)
  ASM_CASES_TAC `(T':num->bool) = {}` THENL
  [(* T' = {}: all events = carrier *)
   SUBGOAL_THEN `!i:num. i IN S ==>
     {x:A | x IN prob_carrier p /\
       nonneg_simple_fn_approx p ((Z:num->A->real) i) n x <=
       (a:num->real) i} = prob_carrier p`
     ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `!i:num. i IN S /\ ~(i IN T') ==>
      {x:A | x IN prob_carrier p /\
        nonneg_simple_fn_approx p ((Z:num->A->real) i) n x <=
        (a:num->real) i} = prob_carrier p` THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `prob (p:A prob_space)
       (INTERS (IMAGE (\n':num. {x:A | x IN prob_carrier p /\
          nonneg_simple_fn_approx p ((Z:num->A->real) n') n x <=
          (a:num->real) n'}) S)) = &1`
     SUBST1_TAC THENL
   [SUBGOAL_THEN
      `INTERS (IMAGE (\n':num. {x:A | x IN prob_carrier p /\
         nonneg_simple_fn_approx p ((Z:num->A->real) n') n x <=
         (a:num->real) n'}) S) = prob_carrier (p:A prob_space)`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_INTERS; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
     X_GEN_TAC `z:A` THEN EQ_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `~((S:num->bool) = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      MESON_TAC[];
      DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `!i:num. i IN S ==>
        {x:A | x IN prob_carrier p /\
          nonneg_simple_fn_approx p ((Z:num->A->real) i) n x <=
          (a:num->real) i} = prob_carrier p` THEN
      DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(z:A) IN {x | x IN prob_carrier p /\
        nonneg_simple_fn_approx p ((Z:num->A->real) i) n x <=
        (a:num->real) i}` MP_TAC THENL
      [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]];
     REWRITE_TAC[PROB_SPACE]];
    ALL_TAC] THEN
   CONV_TAC SYM_CONV THEN
   SUBGOAL_THEN
     `product S (\n':num. prob (p:A prob_space)
        {x:A | x IN prob_carrier p /\
          nonneg_simple_fn_approx p ((Z:num->A->real) n') n x <=
          (a:num->real) n'}) =
      product S (\n':num. &1)` SUBST1_TAC THENL
   [MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    BETA_TAC THEN ASM_SIMP_TAC[] THEN REWRITE_TAC[PROB_SPACE];
    REWRITE_TAC[GSYM(BETA_CONV `(\n':num. &1) n'`)] THEN
    ASM_SIMP_TAC[PRODUCT_CONST; REAL_POW_ONE]];
   ALL_TAC] THEN
  (* T' <> {}: use strict inequality factorization *)
  (* Rewrite INTERS over S as INTERS over T' *)
  SUBGOAL_THEN
    `INTERS (IMAGE (\n':num. {x:A | x IN prob_carrier p /\
       nonneg_simple_fn_approx p ((Z:num->A->real) n') n x <=
       (a:num->real) n'}) S) =
     INTERS (IMAGE (\i:num. {x:A | x IN prob_carrier p /\
       (Z:num->A->real) i x < (cc:num->real) i}) T')`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_INTERS; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
   X_GEN_TAC `z:A` THEN EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(i:num) IN S` ASSUME_TAC THENL
    [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `!i:num. i IN T' ==>
      (!x:A. x IN prob_carrier p ==>
        (nonneg_simple_fn_approx p ((Z:num->A->real) i) n x <=
         (a:num->real) i <=> Z i x < (cc:num->real) i))` THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_CASES_TAC `(i:num) IN T'` THENL
    [UNDISCH_TAC `!i:num. i IN T' ==>
       {x:A | x IN prob_carrier p /\
         nonneg_simple_fn_approx p ((Z:num->A->real) i) n x <=
         (a:num->real) i} =
       {x | x IN prob_carrier p /\ Z i x < (cc:num->real) i}` THEN
     DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
     DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `!i:num. i IN T' ==>
       (!x:A. x IN prob_carrier p ==>
         (nonneg_simple_fn_approx p ((Z:num->A->real) i) n x <=
          (a:num->real) i <=> Z i x < (cc:num->real) i))` THEN
     DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
     ASM_MESON_TAC[];
     SUBGOAL_THEN `(z:A) IN prob_carrier p` ASSUME_TAC THENL
     [UNDISCH_TAC `~((T':num->bool) = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      MESON_TAC[];
      ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `!i:num. i IN S /\ ~(i IN T') ==>
       {x:A | x IN prob_carrier p /\
         nonneg_simple_fn_approx p ((Z:num->A->real) i) n x <=
         (a:num->real) i} = prob_carrier p` THEN
     DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
     DISCH_TAC THEN
     SUBGOAL_THEN `(z:A) IN {x | x IN prob_carrier p /\
       nonneg_simple_fn_approx p ((Z:num->A->real) i) n x <=
       (a:num->real) i}` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]]];
   ALL_TAC] THEN
  (* Apply Lemma B *)
  SUBGOAL_THEN
    `prob (p:A prob_space)
      (INTERS (IMAGE (\i:num. {x:A | x IN prob_carrier p /\
        (Z:num->A->real) i x < (cc:num->real) i}) T')) =
     product T' (\i. prob p {x | x IN prob_carrier p /\ Z i x < cc i})`
    SUBST1_TAC THENL
  [MATCH_MP_TAC MUTUALLY_INDEP_RV_SEQ_STRICT_INEQ THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Decompose product S = product T' * product (S\T') *)
  SUBGOAL_THEN `(S:num->bool) = T' UNION (S DIFF T')`
    (fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
  [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `product (T' UNION S DIFF T')
      (\n':num. prob (p:A prob_space)
        {x:A | x IN prob_carrier p /\
          nonneg_simple_fn_approx p ((Z:num->A->real) n') n x <=
          (a:num->real) n'}) =
     product T'
      (\n'. prob p {x | x IN prob_carrier p /\
        nonneg_simple_fn_approx p (Z n') n x <= a n'}) *
     product (S DIFF T')
      (\n'. prob p {x | x IN prob_carrier p /\
        nonneg_simple_fn_approx p (Z n') n x <= a n'})`
    SUBST1_TAC THENL
  [REWRITE_TAC[product] THEN
   MATCH_MP_TAC(REWRITE_RULE[MONOIDAL_REAL_MUL]
     (ISPEC `( * ):real->real->real` ITERATE_UNION)) THEN
   ASM_SIMP_TAC[FINITE_DIFF] THEN ASM SET_TAC[];
   ALL_TAC] THEN
  (* product (S\T') = 1 *)
  SUBGOAL_THEN
    `product (S DIFF T')
      (\n':num. prob (p:A prob_space)
        {x:A | x IN prob_carrier p /\
          nonneg_simple_fn_approx p ((Z:num->A->real) n') n x <=
          (a:num->real) n'}) = &1`
    SUBST1_TAC THENL
  [SUBGOAL_THEN
     `product (S DIFF T')
       (\n':num. prob (p:A prob_space)
         {x:A | x IN prob_carrier p /\
           nonneg_simple_fn_approx p ((Z:num->A->real) n') n x <=
           (a:num->real) n'}) =
      product (S DIFF T') (\n':num. &1)` SUBST1_TAC THENL
   [MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN BETA_TAC THEN
    UNDISCH_TAC `!i:num. i IN S /\ ~(i IN T') ==>
      {x:A | x IN prob_carrier p /\
        nonneg_simple_fn_approx p ((Z:num->A->real) i) n x <=
        (a:num->real) i} = prob_carrier p` THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[PROB_SPACE];
    ASM_SIMP_TAC[FINITE_DIFF; PRODUCT_CONST; REAL_POW_ONE]];
   ALL_TAC] THEN
  (* Match products over T' *)
  REWRITE_TAC[REAL_MUL_RID] THEN
  MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  BETA_TAC THEN
  UNDISCH_TAC `!i:num. i IN T' ==>
    {x:A | x IN prob_carrier p /\
      nonneg_simple_fn_approx p ((Z:num->A->real) i) n x <=
      (a:num->real) i} =
    {x | x IN prob_carrier p /\ Z i x < (cc:num->real) i}` THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;


(* Helper: product of indicator functions = indicator of INTERS *)
let PRODUCT_INDICATOR_FN_INTERS = prove
 (`!R (A:num->(A->bool)) (x:A). FINITE R /\ ~(R = {})
   ==> product R (\i. indicator_fn (A i) x) =
       indicator_fn (INTERS (IMAGE A R)) x`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_INSERT_EMPTY] THEN
  X_GEN_TAC `s:num` THEN X_GEN_TAC `R:num->bool` THEN STRIP_TAC THEN
  X_GEN_TAC `A:num->(A->bool)` THEN X_GEN_TAC `z:A` THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES; IMAGE_CLAUSES; INTERS_INSERT] THEN
  ASM_CASES_TAC `R:num->bool = {}` THENL
  [ASM_REWRITE_TAC[PRODUCT_CLAUSES; IMAGE_CLAUSES; INTERS_0;
    REAL_MUL_RID; INTER_UNIV];
   ASM_SIMP_TAC[] THEN REWRITE_TAC[INDICATOR_FN_INTER]]);;

(* Helper: simple_rv for finite products *)
let SIMPLE_RV_PRODUCT_FINITE = prove
 (`!p:A prob_space (f:num->A->real) (S:num->bool).
     FINITE S /\ (!i. i IN S ==> simple_rv p (f i))
     ==> simple_rv p (\x. product S (\i. f i x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  SPEC_TAC(`S:num->bool`, `S:num->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
  [REWRITE_TAC[PRODUCT_CLAUSES; SIMPLE_RV_CONST; NOT_IN_EMPTY];
   ALL_TAC] THEN
  X_GEN_TAC `s:num` THEN X_GEN_TAC `S':num->bool` THEN STRIP_TAC THEN
  REWRITE_TAC[IN_INSERT] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES] THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `(f:num->A->real) s`;
    `\x:A. product S' (\i:num. (f:num->A->real) i x)`]
    SIMPLE_RV_MUL) THEN
  REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `s:num`) THEN REWRITE_TAC[];
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   FIRST_X_ASSUM(fun th -> MESON_TAC[th])]);;

(* Strengthened IH: E[prod_R indicators * prod_S functions] factors *)
let MUTUALLY_INDEP_INDICATOR_PRODUCT_EXPECTATION = prove
 (`!p:A prob_space (Z:num->A->real).
     mutually_indep_rv_seq p Z
     ==> !S:num->bool. FINITE S
     ==> !R:num->bool (v:num->real) (f:num->real->real).
       FINITE R /\ DISJOINT R S /\
       (!i. i IN (R UNION S) ==> simple_rv p (Z i)) /\
       ~(R UNION S = {})
       ==> simple_expectation p
             (\x. product R
               (\i. indicator_fn
                 {z | z IN prob_carrier p /\ Z i z = v i} x) *
               product S (\i. f i (Z i x)))
         = product R
             (\i. prob p {x | x IN prob_carrier p /\ Z i x = v i}) *
           product S
             (\i. simple_expectation p (\x. f i (Z i x)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
  [(* BASE CASE: S = {} *)
   REWRITE_TAC[PRODUCT_CLAUSES; REAL_MUL_RID; UNION_EMPTY; DISJOINT_EMPTY] THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   REWRITE_TAC[REAL_MUL_RID] THEN
   SUBGOAL_THEN
     `simple_expectation (p:A prob_space)
        (\x:A. product R
          (\i:num. indicator_fn
            {z | z IN prob_carrier p /\ (Z:num->A->real) i z = (v:num->real) i}
            x)) =
      simple_expectation p
        (indicator_fn
          (INTERS (IMAGE (\i. {z | z IN prob_carrier p /\ Z i z = v i}) R)))`
     SUBST1_TAC THENL
   [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC PRODUCT_INDICATOR_FN_INTERS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `INTERS (IMAGE (\i:num. {z:A | z IN prob_carrier p /\
        (Z:num->A->real) i z = (v:num->real) i}) R) IN prob_events p`
     ASSUME_TAC THENL
   [MATCH_MP_TAC PROB_COUNTABLE_INTERS_IN_EVENTS THEN
    CONJ_TAC THENL
    [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `j:num` THEN
     DISCH_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_LEVEL_SET THEN
     REWRITE_TAC[ETA_AX] THEN
     UNDISCH_TAC `!i:num. i IN R ==>
       simple_rv (p:A prob_space) ((Z:num->A->real) i)` THEN
     DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[simple_rv] THEN MESON_TAC[];
     ASM_SIMP_TAC[FINITE_IMAGE; FINITE_IMP_COUNTABLE; IMAGE_EQ_EMPTY]];
    ALL_TAC] THEN
   ASM_SIMP_TAC[SIMPLE_EXPECTATION_INDICATOR] THEN
   MATCH_MP_TAC MUTUALLY_INDEP_POINT_MASS THEN ASM_REWRITE_TAC[];
   (* STEP CASE: s INSERT S' *)
   ALL_TAC] THEN
  X_GEN_TAC `s:num` THEN X_GEN_TAC `S':num->bool` THEN STRIP_TAC THEN
  X_GEN_TAC `R:num->bool` THEN X_GEN_TAC `v:num->real` THEN
  X_GEN_TAC `f:num->real->real` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES] THEN
  (* Establish key facts *)
  SUBGOAL_THEN `~((s:num) IN R)` ASSUME_TAC THENL
  [UNDISCH_TAC `DISJOINT R (s INSERT S':num->bool)` THEN SET_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT R (S':num->bool)` ASSUME_TAC THENL
  [UNDISCH_TAC `DISJOINT R (s INSERT S':num->bool)` THEN SET_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) ((Z:num->A->real) s)` ASSUME_TAC THENL
  [UNDISCH_TAC `!i:num. i IN R UNION s INSERT S' ==>
     simple_rv p ((Z:num->A->real) i)` THEN
   DISCH_THEN(MP_TAC o SPEC `s:num`) THEN
   REWRITE_TAC[IN_UNION; IN_INSERT];
   ALL_TAC] THEN
  ABBREV_TAC `Rs = IMAGE ((Z:num->A->real) s) (prob_carrier (p:A prob_space))` THEN
  SUBGOAL_THEN `FINITE (Rs:real->bool)` ASSUME_TAC THENL
  [EXPAND_TAC "Rs" THEN REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
   UNDISCH_TAC `simple_rv (p:A prob_space) ((Z:num->A->real) s)` THEN
   REWRITE_TAC[simple_rv] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!u:real. simple_rv (p:A prob_space)
       (\x:A. product R (\i:num. indicator_fn
         {z | z IN prob_carrier p /\ (Z:num->A->real) i z =
           (v:num->real) i} x) *
        (indicator_fn {z | z IN prob_carrier p /\ Z s z = u} x *
         product S' (\i. (f:num->real->real) i (Z i x))))`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   MP_TAC(ISPECL
     [`p:A prob_space`;
      `\x:A. product R (\i:num. indicator_fn
        {z:A | z IN prob_carrier (p:A prob_space) /\
          (Z:num->A->real) i z = (v:num->real) i} x)`;
      `\x:A. indicator_fn
        {z:A | z IN prob_carrier (p:A prob_space) /\
          (Z:num->A->real) s z = u} x *
        product S' (\i:num. (f:num->real->real) i ((Z:num->A->real) i x))`]
     SIMPLE_RV_MUL) THEN
   BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_PRODUCT_FINITE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
    MATCH_MP_TAC RANDOM_VARIABLE_LEVEL_SET THEN REWRITE_TAC[ETA_AX] THEN
    UNDISCH_TAC `!i:num. i IN R UNION s INSERT S' ==>
      simple_rv (p:A prob_space) ((Z:num->A->real) i)` THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
    REWRITE_TAC[IN_UNION; IN_INSERT; simple_rv] THEN
    UNDISCH_TAC `(i:num) IN R` THEN MESON_TAC[];
    MP_TAC(ISPECL
      [`p:A prob_space`;
       `indicator_fn
         {z:A | z IN prob_carrier (p:A prob_space) /\
           (Z:num->A->real) s z = u}`;
       `\x:A. product S' (\i:num. (f:num->real->real) i
         ((Z:num->A->real) i x))`]
      SIMPLE_RV_MUL) THEN
    REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
    [MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
     MATCH_MP_TAC RANDOM_VARIABLE_LEVEL_SET THEN REWRITE_TAC[ETA_AX] THEN
     UNDISCH_TAC `simple_rv (p:A prob_space) ((Z:num->A->real) s)` THEN
     REWRITE_TAC[simple_rv] THEN MESON_TAC[];
     MATCH_MP_TAC SIMPLE_RV_PRODUCT_FINITE THEN ASM_REWRITE_TAC[] THEN
     X_GEN_TAC `i:num` THEN DISCH_TAC THEN
     MATCH_MP_TAC SIMPLE_RV_REAL_COMPOSE THEN
     UNDISCH_TAC `(i:num) IN S'` THEN
     UNDISCH_TAC `!i:num. i IN R UNION s INSERT S' ==>
       simple_rv (p:A prob_space) ((Z:num->A->real) i)` THEN
     POP_ASSUM_LIST(K ALL_TAC) THEN
     DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
     REWRITE_TAC[IN_UNION; IN_INSERT; ETA_AX] THEN MESON_TAC[]]];
   ALL_TAC] THEN
  (* Step 1: Expand f s (Z s x) and rewrite *)
  SUBGOAL_THEN
    `!x:A. x IN prob_carrier (p:A prob_space)
      ==> product R
            (\i:num. indicator_fn
              {z | z IN prob_carrier p /\ (Z:num->A->real) i z =
                (v:num->real) i} x) *
          ((f:num->real->real) s (Z s x) *
           product S' (\i. f i (Z i x))) =
        sum Rs (\u. f s u *
          (product R (\i. indicator_fn
            {z | z IN prob_carrier p /\ Z i z = v i} x) *
           (indicator_fn {z | z IN prob_carrier p /\ Z s z = u} x *
            product S' (\i. f i (Z i x)))))`
    ASSUME_TAC THENL
  [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   SUBGOAL_THEN
     `(f:num->real->real) s ((Z:num->A->real) s x) =
      sum Rs (\u. f s u *
        indicator_fn {z:A | z IN prob_carrier p /\ Z s z = u} x)`
     SUBST1_TAC THENL
   [EXPAND_TAC "Rs" THEN
    MATCH_MP_TAC SIMPLE_RV_COMPOSE_SUM_INDICATOR THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
   MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN
   BETA_TAC THEN
   ABBREV_TAC `a' = product R
     (\i:num. indicator_fn
       {z:A | z IN prob_carrier p /\ (Z:num->A->real) i z =
         (v:num->real) i} x)` THEN
   ABBREV_TAC `b' = indicator_fn
     {z:A | z IN prob_carrier p /\ (Z:num->A->real) s z = u} x` THEN
   ABBREV_TAC `c' = product S'
     (\i:num. (f:num->real->real) i ((Z:num->A->real) i x))` THEN
   CONV_TAC REAL_RING;
   ALL_TAC] THEN
  (* Step 2: Replace via SIMPLE_EXPECTATION_EXT *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
       (\x:A. product R
         (\i:num. indicator_fn
           {z | z IN prob_carrier p /\ (Z:num->A->real) i z =
             (v:num->real) i} x) *
         ((f:num->real->real) s (Z s x) *
          product S' (\i. f i (Z i x)))) =
     simple_expectation p
       (\x. sum Rs (\u. f s u *
         (product R (\i. indicator_fn
           {z | z IN prob_carrier p /\ Z i z = v i} x) *
          (indicator_fn {z | z IN prob_carrier p /\ Z s z = u} x *
           product S' (\i. f i (Z i x))))))`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 3: Push E through sum *)
  MP_TAC(ISPECL
    [`p:A prob_space`;
     `\(u:real) (x:A). (f:num->real->real) s u *
       (product R (\i:num. indicator_fn
         {z:A | z IN prob_carrier (p:A prob_space) /\
           (Z:num->A->real) i z = (v:num->real) i} x) *
        (indicator_fn {z | z IN prob_carrier p /\ Z s z = u} x *
         product S' (\i:num. f i (Z i x))))`;
     `Rs:real->bool`]
    SIMPLE_EXPECTATION_SUM_FINITE) THEN
  BETA_TAC THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN
   MP_TAC(ISPECL
     [`p:A prob_space`;
      `\x:A. product R (\i:num. indicator_fn
        {z:A | z IN prob_carrier (p:A prob_space) /\
          (Z:num->A->real) i z = (v:num->real) i} x) *
        (indicator_fn {z | z IN prob_carrier p /\ Z s z = u} x *
         product S' (\i:num. (f:num->real->real) i (Z i x)))`;
      `(f:num->real->real) s u`]
     SIMPLE_RV_CMUL) THEN
   BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  (* Step 4: For each term, extract CMUL *)
  SUBGOAL_THEN
    `!u:real. u IN Rs ==>
       simple_expectation (p:A prob_space) (\x:A.
         (f:num->real->real) s u *
         (product R (\i:num. indicator_fn
           {z | z IN prob_carrier p /\ (Z:num->A->real) i z =
             (v:num->real) i} x) *
          (indicator_fn {z | z IN prob_carrier p /\ Z s z = u} x *
           product S' (\i. f i (Z i x))))) =
       f s u *
       simple_expectation p (\x.
         product R (\i. indicator_fn
           {z | z IN prob_carrier p /\ Z i z = v i} x) *
         (indicator_fn {z | z IN prob_carrier p /\ Z s z = u} x *
          product S' (\i. f i (Z i x))))`
    ASSUME_TAC THENL
  [X_GEN_TAC `u:real` THEN DISCH_TAC THEN
   MP_TAC(ISPECL
     [`p:A prob_space`;
      `\x:A. product R (\i:num. indicator_fn
        {z:A | z IN prob_carrier (p:A prob_space) /\
          (Z:num->A->real) i z = (v:num->real) i} x) *
        (indicator_fn {z | z IN prob_carrier p /\ Z s z = u} x *
         product S' (\i:num. (f:num->real->real) i (Z i x)))`;
      `(f:num->real->real) s u`]
     SIMPLE_EXPECTATION_CMUL) THEN
   BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `sum Rs (\u:real. simple_expectation (p:A prob_space) (\x:A.
       (f:num->real->real) s u *
       (product R (\i:num. indicator_fn
         {z | z IN prob_carrier p /\ (Z:num->A->real) i z =
           (v:num->real) i} x) *
        (indicator_fn {z | z IN prob_carrier p /\ Z s z = u} x *
         product S' (\i. f i (Z i x)))))) =
     sum Rs (\u. f s u *
       simple_expectation p (\x.
         product R (\i. indicator_fn
           {z | z IN prob_carrier p /\ Z i z = v i} x) *
         (indicator_fn {z | z IN prob_carrier p /\ Z s z = u} x *
          product S' (\i. f i (Z i x)))))`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN
   BETA_TAC THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  (* Step 5: Merge indicator into R product and apply IH *)
  SUBGOAL_THEN
    `!u:real (x:A).
       product R (\i:num. indicator_fn
         {z:A | z IN prob_carrier (p:A prob_space) /\
           (Z:num->A->real) i z = (v:num->real) i} x) *
       (indicator_fn {z | z IN prob_carrier p /\ Z s z = u} x *
        product S' (\i:num. (f:num->real->real) i (Z i x))) =
       product (s INSERT R) (\i. indicator_fn
         {z | z IN prob_carrier p /\ Z i z =
           ((\i:num. if i = s then u else v i):num->real) i} x) *
       product S' (\i. f i (Z i x))`
    ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN
   ASM_SIMP_TAC[PRODUCT_CLAUSES] THEN
   SUBGOAL_THEN
     `(\i:num. if i = s then (u:real) else (v:num->real) i) s = u`
     SUBST1_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN
     `product R (\i:num. indicator_fn
       {z:A | z IN prob_carrier (p:A prob_space) /\
         (Z:num->A->real) i z =
         (if i = s then u else (v:num->real) i)} x) =
      product R (\i. indicator_fn
       {z | z IN prob_carrier p /\ Z i z = v i} x)`
     SUBST1_TAC THENL
   [MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    BETA_TAC THEN
    SUBGOAL_THEN `~((i:num) = s)` (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `(i:num) IN R` THEN
    UNDISCH_TAC `~((s:num) IN R)` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN MESON_TAC[];
    ABBREV_TAC `a' = product R (\i:num. indicator_fn
      {z:A | z IN prob_carrier (p:A prob_space) /\
        (Z:num->A->real) i z = (v:num->real) i} x)` THEN
    ABBREV_TAC `b' = indicator_fn
      {z:A | z IN prob_carrier (p:A prob_space) /\
        (Z:num->A->real) s z = u} x` THEN
    ABBREV_TAC `c' = product S' (\i:num. (f:num->real->real) i
      ((Z:num->A->real) i x))` THEN
    CONV_TAC REAL_RING];
   ALL_TAC] THEN
  (* Step 6: Apply IH *)
  SUBGOAL_THEN
    `!u:real.
     simple_expectation (p:A prob_space)
       (\x:A. product (s INSERT R) (\i:num. indicator_fn
         {z | z IN prob_carrier p /\ (Z:num->A->real) i z =
           ((\i. if i = s then u else (v:num->real) i):num->real) i} x) *
         product S' (\i. (f:num->real->real) i (Z i x))) =
     product (s INSERT R) (\i. prob p
       {x | x IN prob_carrier p /\ Z i x =
         ((\i. if i = s then u else v i):num->real) i}) *
     product S' (\i. simple_expectation p (\x. f i (Z i x)))`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPECL
     [`s INSERT R:num->bool`;
      `(\i:num. if i = s then u else (v:num->real) i):num->real`;
      `f:num->real->real`]) THEN
   ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_INSERT] THEN
    CONJ_TAC THENL
    [UNDISCH_TAC `~((s:num) IN S')` THEN
     UNDISCH_TAC `DISJOINT R (s INSERT S':num->bool)` THEN
     POP_ASSUM_LIST(K ALL_TAC) THEN SET_TAC[];
     ALL_TAC] THEN
    CONJ_TAC THENL
    [X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_UNION; IN_INSERT] THEN
     STRIP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `simple_rv (p:A prob_space) ((Z:num->A->real) s)` THEN
      MESON_TAC[];
      UNDISCH_TAC `!i:num. i IN R UNION s INSERT S' ==>
        simple_rv (p:A prob_space) ((Z:num->A->real) i)` THEN
      DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
      REWRITE_TAC[IN_UNION; IN_INSERT] THEN
      UNDISCH_TAC `(i:num) IN R` THEN MESON_TAC[];
      UNDISCH_TAC `!i:num. i IN R UNION s INSERT S' ==>
        simple_rv (p:A prob_space) ((Z:num->A->real) i)` THEN
      DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
      REWRITE_TAC[IN_UNION; IN_INSERT] THEN
      UNDISCH_TAC `(i:num) IN S'` THEN MESON_TAC[]];
     REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_UNION; IN_INSERT] THEN
     MESON_TAC[]];
    DISCH_THEN ACCEPT_TAC];
   ALL_TAC] THEN
  (* Step 7: Rewrite each sum term *)
  SUBGOAL_THEN
    `sum Rs (\u:real.
       (f:num->real->real) s u *
       simple_expectation (p:A prob_space) (\x:A.
         product R (\i:num. indicator_fn
           {z | z IN prob_carrier p /\ (Z:num->A->real) i z =
             (v:num->real) i} x) *
         (indicator_fn {z | z IN prob_carrier p /\ Z s z = u} x *
          product S' (\i. f i (Z i x))))) =
     sum Rs (\u.
       f s u *
       (product (s INSERT R) (\i. prob p
         {x | x IN prob_carrier p /\ Z i x =
           ((\i. if i = s then u else v i):num->real) i}) *
        product S' (\i. simple_expectation p (\x. f i (Z i x)))))`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN
   CONV_TAC(BINOP_CONV BETA_CONV) THEN AP_TERM_TAC THEN
   SUBGOAL_THEN
     `simple_expectation (p:A prob_space) (\x:A.
       product R (\i:num. indicator_fn
         {z | z IN prob_carrier p /\ (Z:num->A->real) i z =
           (v:num->real) i} x) *
       (indicator_fn {z | z IN prob_carrier p /\ Z s z = u} x *
        product S' (\i. (f:num->real->real) i (Z i x)))) =
      simple_expectation p (\x.
       product (s INSERT R) (\i. indicator_fn
         {z | z IN prob_carrier p /\ Z i z =
           ((\i. if i = s then u else v i):num->real) i} x) *
       product S' (\i. f i (Z i x)))`
     SUBST1_TAC THENL
   [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    CONV_TAC(BINOP_CONV BETA_CONV) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`u:real`; `x:A`]) THEN
    DISCH_THEN ACCEPT_TAC;
    ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `u:real`) THEN
   DISCH_THEN ACCEPT_TAC;
   ALL_TAC] THEN
  (* Step 8: Decompose product (s INSERT R) probs *)
  SUBGOAL_THEN
    `!u:real.
      product (s INSERT R) (\i:num. prob (p:A prob_space)
        {x:A | x IN prob_carrier p /\ (Z:num->A->real) i x =
          ((\i. if i = s then u else (v:num->real) i):num->real) i}) =
      prob p {x | x IN prob_carrier p /\ Z s x = u} *
      product R (\i. prob p {x | x IN prob_carrier p /\ Z i x = v i})`
    ASSUME_TAC THENL
  [GEN_TAC THEN ASM_SIMP_TAC[PRODUCT_CLAUSES] THEN
   SUBGOAL_THEN
     `(\i:num. if i = s then (u:real) else (v:num->real) i) s = u`
     SUBST1_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   BETA_TAC THEN
   SUBGOAL_THEN `~((i:num) = s)` (fun th -> REWRITE_TAC[th]) THEN
   UNDISCH_TAC `(i:num) IN R` THEN
   UNDISCH_TAC `~((s:num) IN R)` THEN
   POP_ASSUM_LIST(K ALL_TAC) THEN MESON_TAC[];
   ALL_TAC] THEN
  (* Step 9: Factor out constants *)
  SUBGOAL_THEN
    `sum Rs (\u:real.
       (f:num->real->real) s u *
       (product (s INSERT R) (\i:num. prob (p:A prob_space)
         {x:A | x IN prob_carrier p /\ (Z:num->A->real) i x =
           ((\i. if i = s then u else (v:num->real) i):num->real) i}) *
        product S' (\i. simple_expectation p (\x. f i (Z i x))))) =
     product R (\i. prob p {x | x IN prob_carrier p /\ Z i x = v i}) *
     product S' (\i. simple_expectation p (\x. f i (Z i x))) *
     sum Rs (\u. f s u * prob p {x | x IN prob_carrier p /\ Z s x = u})`
    SUBST1_TAC THENL
  [REWRITE_TAC[GSYM SUM_LMUL] THEN
   MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN
   BETA_TAC THEN
   FIRST_X_ASSUM(fun th ->
     if is_forall(concl th) then
       ASSUME_TAC(CONV_RULE(DEPTH_CONV BETA_CONV) th)
     else failwith "not forall") THEN
   ASM_REWRITE_TAC[] THEN
   ABBREV_TAC `d = (f:num->real->real) s u` THEN
   ABBREV_TAC `e = prob (p:A prob_space) {x:A | x IN prob_carrier p /\
     (Z:num->A->real) s x = u}` THEN
   ABBREV_TAC `g = product R (\i:num. prob (p:A prob_space)
     {x:A | x IN prob_carrier p /\ (Z:num->A->real) i x =
       (v:num->real) i})` THEN
   ABBREV_TAC `h = product S' (\i:num. simple_expectation (p:A prob_space)
     (\x:A. (f:num->real->real) i ((Z:num->A->real) i x)))` THEN
   CONV_TAC REAL_RING;
   ALL_TAC] THEN
  (* Step 10: Recognize sum as E[f s (Z s)] *)
  SUBGOAL_THEN
    `sum Rs (\u:real. (f:num->real->real) s u *
       prob (p:A prob_space)
         {x:A | x IN prob_carrier p /\ (Z:num->A->real) s x = u}) =
     simple_expectation p (\x. f s (Z s x))`
    SUBST1_TAC THENL
  [CONV_TAC SYM_CONV THEN EXPAND_TAC "Rs" THEN
   MATCH_MP_TAC SIMPLE_EXPECTATION_COMPOSE_SUM THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 11: Final rearrangement *)
  ABBREV_TAC `P = product R (\i:num. prob (p:A prob_space)
    {x:A | x IN prob_carrier p /\ (Z:num->A->real) i x =
      (v:num->real) i})` THEN
  ABBREV_TAC `E = simple_expectation (p:A prob_space)
    (\x:A. (f:num->real->real) s ((Z:num->A->real) s x))` THEN
  ABBREV_TAC `Q = product S' (\i:num. simple_expectation (p:A prob_space)
    (\x:A. (f:num->real->real) i ((Z:num->A->real) i x)))` THEN
  CONV_TAC REAL_RING);;

(* Main Lemma D: simple_expectation of product factors *)
let MUTUALLY_INDEP_SIMPLE_EXPECTATION_PRODUCT = prove
 (`!p:A prob_space (Z:num->A->real) (f:num->real->real) (S:num->bool).
     mutually_indep_rv_seq p Z /\
     (!i. i IN S ==> simple_rv p (Z i)) /\
     FINITE S /\ ~(S = {})
     ==> simple_expectation p (\x. product S (\i. f i (Z i x))) =
         product S (\i. simple_expectation p (\x. f i (Z i x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
    [`p:A prob_space`; `Z:num->A->real`]
    MUTUALLY_INDEP_INDICATOR_PRODUCT_EXPECTATION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `S:num->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL
    [`EMPTY:num->bool`; `(\n:num. &0):num->real`;
     `f:num->real->real`]) THEN
  REWRITE_TAC[FINITE_EMPTY; DISJOINT_EMPTY; UNION_EMPTY;
    PRODUCT_CLAUSES; REAL_MUL_LID] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN ACCEPT_TAC);;

(* Helper: random_variable for finite products *)
let RANDOM_VARIABLE_PRODUCT_FINITE = prove
 (`!p:A prob_space (f:num->A->real) (S:num->bool).
     FINITE S /\ (!i. i IN S ==> random_variable p (f i))
     ==> random_variable p (\x. product S (\i. f i x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  SPEC_TAC(`S:num->bool`, `S:num->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
  [REWRITE_TAC[PRODUCT_CLAUSES; RANDOM_VARIABLE_CONST; NOT_IN_EMPTY];
   ALL_TAC] THEN
  X_GEN_TAC `s:num` THEN X_GEN_TAC `S':num->bool` THEN STRIP_TAC THEN
  REWRITE_TAC[IN_INSERT] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES] THEN
  MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN REWRITE_TAC[ETA_AX] THEN
  CONJ_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `s:num`) THEN REWRITE_TAC[];
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

(* Expectation of product of powers factors for mutually independent bounded RVs.
   Proof: approximate with simple functions, factor via Lemma D, take limits
   using bounded convergence theorem. *)
let MUTUALLY_INDEP_EXPECTATION_PRODUCT_POW = prove
 (`!p:A prob_space (Z:num->A->real) B (a:num->num) (S:num->bool).
    mutually_indep_rv_seq p Z /\
    (!i x. x IN prob_carrier p ==> abs(Z i x) <= B) /\
    FINITE S /\ ~(S = {})
    ==> expectation p (\x. product S (\i. Z i x pow (a i))) =
        product S (\i. expectation p (\x. Z i x pow (a i)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Step 0: B >= 0 and carrier nonempty *)
  SUBGOAL_THEN `?z:A. z IN prob_carrier p` STRIP_ASSUME_TAC THENL
  [MP_TAC(ISPEC `p:A prob_space` PROB_CARRIER_NONEMPTY) THEN SET_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `abs((Z:num->A->real) (ARB:num) z)` THEN
   REWRITE_TAC[REAL_ABS_POS] THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  (* Step 1: random_variable for each Z_i *)
  SUBGOAL_THEN `!i:num. random_variable (p:A prob_space) ((Z:num->A->real) i)`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[mutually_indep_rv_seq]; ALL_TAC] THEN
  (* Step 2: U_i = Z_i + B nonneg, mutually indep *)
  SUBGOAL_THEN `!i:num x:A. x IN prob_carrier p
    ==> &0 <= (Z:num->A->real) i x + B` ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `abs((Z:num->A->real) i x) <= B` MP_TAC THENL
   [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `mutually_indep_rv_seq (p:A prob_space)
    (\i (x:A). (Z:num->A->real) i x + B)` ASSUME_TAC THENL
  [MATCH_MP_TAC MUTUALLY_INDEP_RV_SEQ_SHIFT THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 3: For each n, nsfa(U_i, n) are mutually indep *)
  SUBGOAL_THEN `!n:num. mutually_indep_rv_seq (p:A prob_space)
    (\i:num. nonneg_simple_fn_approx p (\x:A. (Z:num->A->real) i x + B) n)`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC MUTUALLY_INDEP_RV_SEQ_NSFA THEN
   ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
   ASM_SIMP_TAC[];
   ALL_TAC] THEN
  (* Step 4: Wn(n,i) = nsfa(U_i, n) - B are mutually indep *)
  SUBGOAL_THEN `!n:num. mutually_indep_rv_seq (p:A prob_space)
    (\i:num (x:A).
      nonneg_simple_fn_approx p (\y:A. (Z:num->A->real) i y + B) n x - B)`
    ASSUME_TAC THENL
  [GEN_TAC THEN REWRITE_TAC[real_sub] THEN
   MATCH_MP_TAC MUTUALLY_INDEP_RV_SEQ_SHIFT THEN
   REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 5: simple_rv for Wn(n,i) *)
  SUBGOAL_THEN `!n:num i:num. simple_rv (p:A prob_space)
    (\x:A. nonneg_simple_fn_approx p (\y:A. (Z:num->A->real) i y + B) n x - B)`
    ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `nonneg_simple_fn_approx (p:A prob_space)
        (\y:A. (Z:num->A->real) i y + B) n`;
     `\t:real. t - B`] SIMPLE_RV_REAL_COMPOSE) THEN
   BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
   MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_SIMPLE_RV THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_SHIFT THEN ASM_REWRITE_TAC[ETA_AX];
    REPEAT STRIP_TAC THEN BETA_TAC THEN ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  (* Step 6: |Wn(n,i)| <= B *)
  SUBGOAL_THEN `!n:num i:num (w:A). w IN prob_carrier p
    ==> abs(nonneg_simple_fn_approx (p:A prob_space)
              (\y:A. (Z:num->A->real) i y + B) n w - B) <= B`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `nonneg_simple_fn_approx (p:A prob_space)
     (\y:A. (Z:num->A->real) i y + B) n w <=
     (Z:num->A->real) i w + B` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`;
      `\y:A. (Z:num->A->real) i y + B`; `n:num`; `w:A`]
      NONNEG_SIMPLE_FN_APPROX_LE) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN BETA_TAC THEN ASM_SIMP_TAC[];
     BETA_TAC THEN DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= nonneg_simple_fn_approx (p:A prob_space)
     (\y:A. (Z:num->A->real) i y + B) n w` ASSUME_TAC THENL
   [REWRITE_TAC[NONNEG_SIMPLE_FN_APPROX_NONNEG]; ALL_TAC] THEN
   SUBGOAL_THEN `abs((Z:num->A->real) i w) <= B` MP_TAC THENL
   [ASM_SIMP_TAC[]; ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* Step 7: Wn(n,i) -> Z_i pointwise *)
  SUBGOAL_THEN `!i:num (w:A). w IN prob_carrier p
    ==> ((\n. nonneg_simple_fn_approx (p:A prob_space)
                (\y:A. (Z:num->A->real) i y + B) n w - B) --->
         (Z:num->A->real) i w) sequentially` ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `(Z:num->A->real) i w =
     ((Z:num->A->real) i w + B) - B` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REALLIM_SUB THEN REWRITE_TAC[REALLIM_CONST] THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `\y:A. (Z:num->A->real) i y + B`; `w:A`]
     NONNEG_SIMPLE_FN_APPROX_CONVERGES) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN BETA_TAC THEN ASM_SIMP_TAC[];
    BETA_TAC THEN DISCH_THEN ACCEPT_TAC];
   ALL_TAC] THEN
  (* Step 8: Per-step factorization via Lemma D + EXPECTATION_SIMPLE_AGREE *)
  SUBGOAL_THEN `!n:num. expectation (p:A prob_space)
    (\x:A. product S (\i:num.
      (nonneg_simple_fn_approx p (\y:A. (Z:num->A->real) i y + B) n x - B)
      pow (a i))) =
    product S (\i. expectation p (\x.
      (nonneg_simple_fn_approx p (\y. Z i y + B) n x - B) pow (a i)))`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   SUBGOAL_THEN `!i:num. simple_rv (p:A prob_space)
     (\x:A. (nonneg_simple_fn_approx p (\y:A. (Z:num->A->real) i y + B) n x - B)
       pow ((a:num->num) i))` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`;
      `\x:A. nonneg_simple_fn_approx (p:A prob_space)
        (\y:A. (Z:num->A->real) i y + B) n x - B`;
      `\t:real. t pow ((a:num->num) i)`] SIMPLE_RV_REAL_COMPOSE) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
   SUBGOAL_THEN `simple_rv (p:A prob_space)
     (\x:A. product S (\i:num.
       (nonneg_simple_fn_approx p (\y:A. (Z:num->A->real) i y + B) n x - B)
       pow ((a:num->num) i)))` ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_PRODUCT_FINITE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   ASM_SIMP_TAC[EXPECTATION_SIMPLE_AGREE] THEN
   MP_TAC(ISPECL
     [`p:A prob_space`;
      `\i:num (x:A).
        nonneg_simple_fn_approx (p:A prob_space)
          (\y:A. (Z:num->A->real) i y + B) n x - B`;
      `\i:num (t:real). t pow ((a:num->num) i)`;
      `S:num->bool`]
     MUTUALLY_INDEP_SIMPLE_EXPECTATION_PRODUCT) THEN
   BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
   ALL_TAC] THEN
  (* Step 9: Main argument via REALLIM_UNIQUE with BCT *)
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC `\n:num. expectation (p:A prob_space) (\x:A.
    product S (\i:num.
      (nonneg_simple_fn_approx p (\y:A. (Z:num->A->real) i y + B) n x - B)
      pow ((a:num->num) i)))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
  [(* LHS: BCT => E[prod Wn^a] -> E[prod Z^a] *)
   MATCH_MP_TAC BOUNDED_CONVERGENCE_EXPECTATION THEN
   EXISTS_TAC `product (S:num->bool) (\i:num. B pow ((a:num->num) i))` THEN
   REPEAT CONJ_TAC THENL
   [(* rv: product Wn^a for each n *)
    GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_PRODUCT_FINITE THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
    UNDISCH_TAC `!n:num i:num. simple_rv (p:A prob_space)
      (\x:A. nonneg_simple_fn_approx p (\y:A. (Z:num->A->real) i y + B) n x - B)` THEN
    DISCH_THEN(MP_TAC o SPECL [`n:num`; `i:num`]) THEN
    REWRITE_TAC[simple_rv] THEN MESON_TAC[];
    (* rv: product Z^a *)
    MATCH_MP_TAC RANDOM_VARIABLE_PRODUCT_FINITE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC RANDOM_VARIABLE_POW THEN ASM_REWRITE_TAC[ETA_AX];
    (* bound: |prod Wn^a| <= prod B^a *)
    REPEAT STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[GSYM PRODUCT_ABS] THEN
    MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ABS_POW] THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_ABS_POS];
     MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
     ASM_SIMP_TAC[]];
    (* bound: |prod Z^a| <= prod B^a *)
    REPEAT STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[GSYM PRODUCT_ABS] THEN
    MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ABS_POW] THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_ABS_POS];
     MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
     ASM_SIMP_TAC[]];
    (* conv: prod Wn^a -> prod Z^a pointwise *)
    REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REALLIM_PRODUCT_FINITE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC REALLIM_POW THEN ASM_SIMP_TAC[]];
   (* RHS: prod E[Wn^a] -> prod E[Z^a] *)
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REALLIM_PRODUCT_FINITE THEN ASM_REWRITE_TAC[] THEN
   X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   MATCH_MP_TAC BOUNDED_CONVERGENCE_EXPECTATION THEN
   EXISTS_TAC `(B:real) pow ((a:num->num) i)` THEN REPEAT CONJ_TAC THENL
   [(* rv: Wn^a for each n *)
    GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
    UNDISCH_TAC `!n:num i:num. simple_rv (p:A prob_space)
      (\x:A. nonneg_simple_fn_approx p (\y:A. (Z:num->A->real) i y + B) n x - B)` THEN
    DISCH_THEN(MP_TAC o SPECL [`n:num`; `i:num`]) THEN
    REWRITE_TAC[simple_rv] THEN MESON_TAC[];
    (* rv: Z^a *)
    MATCH_MP_TAC RANDOM_VARIABLE_POW THEN ASM_REWRITE_TAC[ETA_AX];
    (* bound: |Wn^a| <= B^a *)
    REPEAT STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    ASM_SIMP_TAC[];
    (* bound: |Z^a| <= B^a *)
    REPEAT STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    ASM_SIMP_TAC[];
    (* conv: Wn^a -> Z^a pointwise *)
    REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REALLIM_POW THEN ASM_SIMP_TAC[]]]);;

(* Helper: extract rv from indep_rv *)
let INDEP_RV_RV_LEFT = prove
 (`!p:A prob_space X Y. indep_rv p X Y ==> random_variable p X`,
  REWRITE_TAC[indep_rv] THEN MESON_TAC[]);;

let INDEP_RV_RV_RIGHT = prove
 (`!p:A prob_space X Y. indep_rv p X Y ==> random_variable p Y`,
  REWRITE_TAC[indep_rv] THEN MESON_TAC[]);;

(* Bridge: mutually_indep_rv_seq (infinite, CDF-based) implies
   mutually_indep_rv (finite, point-mass-based) for simple RVs. *)
let MUTUALLY_INDEP_RV_SEQ_IMP_FINITE = prove
 (`!p:A prob_space (X:num->A->real) n.
    mutually_indep_rv_seq p X /\ (!k. k <= n ==> simple_rv p (X k))
    ==> mutually_indep_rv p X n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mutually_indep_rv] THEN
  CONJ_TAC THENL
  [ASM_MESON_TAC[mutually_indep_rv_seq]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MUTUALLY_INDEP_POINT_MASS THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[SUBSET; IN_NUMSEG; LE_0]);;

(* Block independence for partial sums: E[S_n^m * Z_{n+1}^k] factors.
   Proof: approximate Z_i via nsfa, use MUTUALLY_INDEP_RV_SUM_INDEP_RV for
   independence, EXPECTATION_PRODUCT_POW_BOUNDED_INDEP for factorization,
   then take limits via BCT (BOUNDED_CONVERGENCE_EXPECTATION). *)
let BLOCK_INDEP_SUM_POW = prove
 (`!p:A prob_space (Z:num->A->real) B m k n.
    mutually_indep_rv_seq p Z /\
    (!i x. x IN prob_carrier p ==> abs(Z i x) <= B) /\
    (!i. integrable p (Z i)) /\
    (!i. expectation p (Z i) = &0)
    ==> expectation p (\x. sum(0..n) (\i. Z i x) pow m * Z (n + 1) x pow k) =
        expectation p (\x. sum(0..n) (\i. Z i x) pow m) *
        expectation p (\x. Z (n + 1) x pow k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Step 0: basic setup *)
  SUBGOAL_THEN `!i:num. random_variable (p:A prob_space) ((Z:num->A->real) i)`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[mutually_indep_rv_seq]; ALL_TAC] THEN
  SUBGOAL_THEN `?z:A. z IN prob_carrier p` STRIP_ASSUME_TAC THENL
  [MP_TAC(ISPEC `p:A prob_space` PROB_CARRIER_NONEMPTY) THEN SET_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `abs((Z:num->A->real) 0 z)` THEN
   REWRITE_TAC[REAL_ABS_POS] THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  (* Step 1: Shifted infrastructure *)
  SUBGOAL_THEN `mutually_indep_rv_seq (p:A prob_space)
    (\i (x:A). (Z:num->A->real) i x + B)` ASSUME_TAC THENL
  [MATCH_MP_TAC MUTUALLY_INDEP_RV_SEQ_SHIFT THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!N:num. mutually_indep_rv_seq (p:A prob_space)
    (\i:num. nonneg_simple_fn_approx p (\x:A. (Z:num->A->real) i x + B) N)`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC MUTUALLY_INDEP_RV_SEQ_NSFA THEN
   ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
   SUBGOAL_THEN `abs((Z:num->A->real) i x) <= B` MP_TAC THENL
   [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `!N:num. mutually_indep_rv_seq (p:A prob_space)
    (\i:num (x:A).
      nonneg_simple_fn_approx p (\y:A. (Z:num->A->real) i y + B) N x - B)`
    ASSUME_TAC THENL
  [GEN_TAC THEN REWRITE_TAC[real_sub] THEN
   MATCH_MP_TAC MUTUALLY_INDEP_RV_SEQ_SHIFT THEN
   REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!N:num i:num. simple_rv (p:A prob_space)
    (\x:A. nonneg_simple_fn_approx p (\y:A. (Z:num->A->real) i y + B) N x - B)`
    ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `nonneg_simple_fn_approx (p:A prob_space)
        (\y:A. (Z:num->A->real) i y + B) N`;
     `\t:real. t - B`] SIMPLE_RV_REAL_COMPOSE) THEN
   BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
   MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_SIMPLE_RV THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_SHIFT THEN ASM_REWRITE_TAC[ETA_AX];
    REPEAT STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `abs((Z:num->A->real) i x) <= B` MP_TAC THENL
    [ASM_SIMP_TAC[]; REAL_ARITH_TAC]];
   ALL_TAC] THEN
  (* Step 2: |W_i^N| <= B *)
  SUBGOAL_THEN `!N:num i:num (w:A). w IN prob_carrier p
    ==> abs(nonneg_simple_fn_approx (p:A prob_space)
              (\y:A. (Z:num->A->real) i y + B) N w - B) <= B`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `nonneg_simple_fn_approx (p:A prob_space)
     (\y:A. (Z:num->A->real) i y + B) N w <= Z i w + B` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`;
      `\y:A. (Z:num->A->real) i y + B`; `N:num`; `w:A`]
      NONNEG_SIMPLE_FN_APPROX_LE) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN BETA_TAC THEN
     SUBGOAL_THEN `abs((Z:num->A->real) i w) <= B` MP_TAC THENL
     [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
     BETA_TAC THEN DISCH_THEN ACCEPT_TAC]; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= nonneg_simple_fn_approx (p:A prob_space)
     (\y:A. (Z:num->A->real) i y + B) N w` ASSUME_TAC THENL
   [REWRITE_TAC[NONNEG_SIMPLE_FN_APPROX_NONNEG]; ALL_TAC] THEN
   SUBGOAL_THEN `abs((Z:num->A->real) i w) <= B` MP_TAC THENL
   [ASM_SIMP_TAC[]; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  (* Step 3: W_i^N -> Z_i pointwise *)
  SUBGOAL_THEN `!i:num (w:A). w IN prob_carrier p
    ==> ((\N. nonneg_simple_fn_approx (p:A prob_space)
                (\y:A. (Z:num->A->real) i y + B) N w - B) --->
         Z i w) sequentially` ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `(Z:num->A->real) i w = (Z i w + B) - B`
     SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REALLIM_SUB THEN REWRITE_TAC[REALLIM_CONST] THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `\y:A. (Z:num->A->real) i y + B`; `w:A`]
     NONNEG_SIMPLE_FN_APPROX_CONVERGES) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN BETA_TAC THEN
    SUBGOAL_THEN `abs((Z:num->A->real) i w) <= B` MP_TAC THENL
    [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
    BETA_TAC THEN DISCH_THEN ACCEPT_TAC]; ALL_TAC] THEN
  (* Step 4: finite mutual independence and indep_rv *)
  SUBGOAL_THEN `!N:num. indep_rv (p:A prob_space)
    (\x:A. sum(0..n) (\i.
      nonneg_simple_fn_approx p (\y:A. (Z:num->A->real) i y + B) N x - B))
    (\x. nonneg_simple_fn_approx p (\y. Z (n + 1) y + B) N x - B)`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   MP_TAC(ISPECL
     [`p:A prob_space`;
      `\i:num (x:A). nonneg_simple_fn_approx (p:A prob_space)
        (\y:A. (Z:num->A->real) i y + B) N x - B`;
      `n + 1`; `n:num`] MUTUALLY_INDEP_RV_SUM_INDEP_RV) THEN
   REWRITE_TAC[ARITH_RULE `n < n + 1`] THEN
   REWRITE_TAC[ARITH_RULE `SUC n = n + 1`] THEN
   DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC MUTUALLY_INDEP_RV_SEQ_IMP_FINITE THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* Step 5: Factorization for nsfa *)
  SUBGOAL_THEN `!N:num.
    expectation (p:A prob_space)
      (\x:A. sum(0..n) (\i.
        nonneg_simple_fn_approx p (\y:A. (Z:num->A->real) i y + B) N x - B)
        pow m *
        (nonneg_simple_fn_approx p (\y. Z (n+1) y + B) N x - B) pow k) =
    expectation p (\x. sum(0..n) (\i.
        nonneg_simple_fn_approx p (\y. Z i y + B) N x - B) pow m) *
    expectation p (\x.
        (nonneg_simple_fn_approx p (\y. Z (n+1) y + B) N x - B) pow k)`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   MP_TAC(ISPECL
     [`p:A prob_space`;
      `\x:A. sum(0..n) (\i.
        nonneg_simple_fn_approx (p:A prob_space)
          (\y:A. (Z:num->A->real) i y + B) N x - B)`;
      `\x:A. nonneg_simple_fn_approx (p:A prob_space)
          (\y:A. (Z:num->A->real) (n+1) y + B) N x - B`;
      `m:num`; `k:num`;
      `(&n + &1) * B`; `B:real`]
     EXPECTATION_PRODUCT_POW_BOUNDED_INDEP) THEN
   BETA_TAC THEN ANTS_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC INDEP_RV_RV_LEFT THEN
     EXISTS_TAC `\x:A. nonneg_simple_fn_approx (p:A prob_space)
       (\y. (Z:num->A->real) (n+1) y + B) N x - B` THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC INDEP_RV_RV_RIGHT THEN
     EXISTS_TAC `\x:A. sum(0..n) (\i.
       nonneg_simple_fn_approx (p:A prob_space)
         (\y. (Z:num->A->real) i y + B) N x - B)` THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
    [REPEAT STRIP_TAC THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `sum(0..n) (\i:num. B:real)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`N:num`; `x':num`; `x:A`]) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0] THEN
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; REAL_LE_REFL]];
     ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]];
    DISCH_THEN ACCEPT_TAC];
   ALL_TAC] THEN
  (* Step 6: (&n + &1) * B >= 0 *)
  SUBGOAL_THEN `&0 <= (&n + &1) * B` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Step 7: REALLIM_UNIQUE *)
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC `\N:num. expectation (p:A prob_space)
    (\x:A. sum(0..n) (\i.
      nonneg_simple_fn_approx p (\y:A. (Z:num->A->real) i y + B) N x - B)
      pow m *
      (nonneg_simple_fn_approx p (\y. Z (n+1) y + B) N x - B) pow k)` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
  [(* LHS: BCT => E[prod_N] -> E[S^m * Z^k] *)
   MATCH_MP_TAC BOUNDED_CONVERGENCE_EXPECTATION THEN
   EXISTS_TAC `((&n + &1) * B) pow m * B pow k` THEN REPEAT CONJ_TAC THENL
   [(* rv for each N *)
    GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN
    REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
     MATCH_MP_TAC INDEP_RV_RV_LEFT THEN
     EXISTS_TAC `\x:A. nonneg_simple_fn_approx (p:A prob_space)
       (\y. (Z:num->A->real) (n+1) y + B) N x - B` THEN
     ASM_REWRITE_TAC[];
     MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
     MATCH_MP_TAC INDEP_RV_RV_RIGHT THEN
     EXISTS_TAC `\x:A. sum(0..n) (\i.
       nonneg_simple_fn_approx (p:A prob_space)
         (\y. (Z:num->A->real) i y + B) N x - B)` THEN
     ASM_REWRITE_TAC[]];
    (* rv for limit *)
    MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN REWRITE_TAC[ETA_AX] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
     MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN ASM_REWRITE_TAC[LE_REFL] THEN
     GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[ETA_AX];
     MATCH_MP_TAC RANDOM_VARIABLE_POW THEN ASM_REWRITE_TAC[ETA_AX]];
    (* bound for each N *)
    REPEAT STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_ABS_POS];
     MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(0..n) (\i:num. B:real)` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`N:num`; `x':num`; `x:A`]) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0] THEN
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; REAL_LE_REFL]];
     MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_ABS_POS];
     MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
     ASM_MESON_TAC[]];
    (* bound for limit *)
    REPEAT STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_ABS_POS];
     MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(0..n) (\i:num. B:real)` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      ASM_MESON_TAC[];
      REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0] THEN
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; REAL_LE_REFL]];
     MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_ABS_POS];
     MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
     ASM_MESON_TAC[]];
    (* pointwise convergence *)
    REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REALLIM_MUL THEN CONJ_TAC THENL
    [MATCH_MP_TAC REALLIM_POW THEN
     MP_TAC(ISPECL [`sequentially`;
       `\i:num (N:num). nonneg_simple_fn_approx (p:A prob_space)
         (\y:A. (Z:num->A->real) i y + B) N x - B`;
       `\i:num. (Z:num->A->real) i x`;
       `(0..n)`] REALLIM_SUM) THEN
     REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
     REPEAT STRIP_TAC THEN ASM_MESON_TAC[];
     MATCH_MP_TAC REALLIM_POW THEN ASM_MESON_TAC[]]];
   (* RHS: rewrite using factorization, then REALLIM_MUL + BCT *)
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REALLIM_MUL THEN CONJ_TAC THENL
   [(* E[(sum W)^m] -> E[S^m] *)
    MATCH_MP_TAC BOUNDED_CONVERGENCE_EXPECTATION THEN
    EXISTS_TAC `((&n + &1) * B) pow m` THEN REPEAT CONJ_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
     MATCH_MP_TAC INDEP_RV_RV_LEFT THEN
     EXISTS_TAC `\x:A. nonneg_simple_fn_approx (p:A prob_space)
       (\y. (Z:num->A->real) (n+1) y + B) N x - B` THEN
     ASM_REWRITE_TAC[];
     MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
     MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN ASM_REWRITE_TAC[LE_REFL] THEN
     GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[ETA_AX];
     REPEAT STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
     MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(0..n) (\i:num. B:real)` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`N:num`; `x':num`; `x:A`]) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0] THEN
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; REAL_LE_REFL]];
     REPEAT STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
     MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(0..n) (\i:num. B:real)` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      ASM_MESON_TAC[];
      REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0] THEN
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; REAL_LE_REFL]];
     REPEAT STRIP_TAC THEN BETA_TAC THEN
     MATCH_MP_TAC REALLIM_POW THEN
     MP_TAC(ISPECL [`sequentially`;
       `\i:num (N:num). nonneg_simple_fn_approx (p:A prob_space)
         (\y:A. (Z:num->A->real) i y + B) N x - B`;
       `\i:num. (Z:num->A->real) i x`;
       `(0..n)`] REALLIM_SUM) THEN
     REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
     REPEAT STRIP_TAC THEN ASM_MESON_TAC[]];
    (* E[W_{n+1}^k] -> E[Z_{n+1}^k] *)
    MATCH_MP_TAC BOUNDED_CONVERGENCE_EXPECTATION THEN
    EXISTS_TAC `(B:real) pow k` THEN REPEAT CONJ_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
     MATCH_MP_TAC INDEP_RV_RV_RIGHT THEN
     EXISTS_TAC `\x:A. sum(0..n) (\i.
       nonneg_simple_fn_approx (p:A prob_space)
         (\y. (Z:num->A->real) i y + B) N x - B)` THEN
     ASM_REWRITE_TAC[];
     MATCH_MP_TAC RANDOM_VARIABLE_POW THEN ASM_REWRITE_TAC[ETA_AX];
     REPEAT STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
     MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
     ASM_MESON_TAC[];
     REPEAT STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
     MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
     ASM_MESON_TAC[];
     REPEAT STRIP_TAC THEN BETA_TAC THEN
     MATCH_MP_TAC REALLIM_POW THEN ASM_MESON_TAC[]]]])

(* Helper: expectation of sum of centered RVs is zero. *)
let EXPECTATION_SUM_CENTERED = prove
 (`!p:A prob_space (Z:num->A->real) n.
    (!i. integrable p (Z i)) /\ (!i. expectation p (Z i) = &0)
    ==> expectation p (\x. sum(0..n) (\i. Z i x)) = &0`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN STRIP_TAC THENL
  [REWRITE_TAC[SUM_SING_NUMSEG] THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `\x:A. sum(0..n)(\i. (Z:num->A->real) i x)`;
    `(Z:num->A->real) (SUC n)`] EXPECTATION_ADD) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_SUM THEN
     ASM_REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG];
     ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  REWRITE_TAC[BETA_THM; ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `expectation p (\x:A. sum(0..n)(\i. (Z:num->A->real) i x)) = &0`
    SUBST1_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Fourth moment bound for independent centered bounded RVs:
   E[S_n^4] <= B^2 * E[S_n^2] + 3 * (E[S_n^2])^2.
   Proof by induction on n. Base case uses pointwise Z^4 <= B^2*Z^2.
   Inductive step expands (S+Z)^4, factors cross-moments via
   BLOCK_INDEP_SUM_POW, kills odd terms by centering, and uses
   the second moment recurrence E[(S+Z)^2] = E[S^2] + E[Z^2]. *)
let FOURTH_MOMENT_BOUND_INDEP_CENTERED = prove
 (`!p:A prob_space (Z:num->A->real) B.
    mutually_indep_rv_seq p Z /\
    &0 < B /\
    (!i. integrable p (Z i)) /\
    (!i. expectation p (Z i) = &0) /\
    (!i x. x IN prob_carrier p ==> abs(Z i x) <= B) /\
    (!i. integrable p (\x. Z i x pow 2))
    ==> !n. expectation p (\x. sum(0..n) (\i. Z i x) pow 4) <=
      B pow 2 * expectation p (\x. sum(0..n) (\i. Z i x) pow 2) +
      &3 * expectation p (\x. sum(0..n) (\i. Z i x) pow 2) pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
  [(* Base case: n = 0 *)
   REWRITE_TAC[SUM_SING_NUMSEG] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `B pow 2 * expectation p (\x:A. (Z:num->A->real) 0 x pow 2)` THEN
   CONJ_TAC THENL
   [SUBGOAL_THEN `B pow 2 * expectation p (\x:A. (Z:num->A->real) 0 x pow 2) =
                   expectation p (\x. B pow 2 * Z 0 x pow 2)` SUBST1_TAC THENL
    [MATCH_MP_TAC(GSYM EXPECTATION_CMUL) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC EXPECTATION_MONO THEN REPEAT CONJ_TAC THENL
    [SUBGOAL_THEN `random_variable p ((Z:num->A->real) 0)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mutually_indep_rv_seq]) THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN
      REWRITE_TAC[]; ALL_TAC] THEN
     MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `(B:real) pow 4` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN ASM_REWRITE_TAC[ETA_AX];
      REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
      ASM_SIMP_TAC[]];
     MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[BETA_THM] THEN REPEAT STRIP_TAC THEN
     REWRITE_TAC[ARITH_RULE `4 = 2 + 2`; REAL_POW_ADD] THEN
     MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
     SUBGOAL_THEN `(Z:num->A->real) 0 x pow 2 = abs(Z 0 x) pow 2` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW2_ABS]; ALL_TAC] THEN
     MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
     ASM_SIMP_TAC[]];
    MATCH_MP_TAC(REAL_ARITH `&0 <= c ==> a <= a + c`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
    [REAL_ARITH_TAC; REWRITE_TAC[REAL_LE_POW_2]]];
   (* Inductive step: n -> SUC n *)
   REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
   SUBGOAL_THEN `!i. random_variable p ((Z:num->A->real) i)` ASSUME_TAC THENL
   [ASM_MESON_TAC[mutually_indep_rv_seq]; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `!x:A. x IN prob_carrier p
       ==> abs(sum(0..n)(\i. (Z:num->A->real) i x)) <= &(n + 1) * B`
     ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..n)(\i. abs((Z:num->A->real) i x))` THEN
    REWRITE_TAC[SUM_ABS_NUMSEG] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(0..n)(\i:num. B:real)` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_SIMP_TAC[];
     REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0] THEN REAL_ARITH_TAC]; ALL_TAC] THEN
   SUBGOAL_THEN `random_variable p (\x:A. sum(0..n)(\i. (Z:num->A->real) i x))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN
    ASM_REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG]; ALL_TAC] THEN
   SUBGOAL_THEN `integrable p (\x:A. sum(0..n)(\i. (Z:num->A->real) i x) pow 2)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
    EXISTS_TAC `(&(n + 1) * B) pow 2` THEN CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN ASM_REWRITE_TAC[];
     REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
     MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
     ASM_SIMP_TAC[]]; ALL_TAC] THEN
   SUBGOAL_THEN `integrable p (\x:A. sum(0..n)(\i. (Z:num->A->real) i x) pow 4)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
    EXISTS_TAC `(&(n + 1) * B) pow 4` THEN CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN ASM_REWRITE_TAC[];
     REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
     MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
     ASM_SIMP_TAC[]]; ALL_TAC] THEN
   SUBGOAL_THEN `!x:A. x IN prob_carrier p
       ==> abs(sum(0..n)(\i. (Z:num->A->real) i x) + Z (SUC n) x) <=
           &(n + 2) * B` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(sum(0..n)(\i. (Z:num->A->real) i x)) +
                abs(Z (SUC n) x)` THEN
    REWRITE_TAC[REAL_ABS_TRIANGLE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(n + 1) * B + B:real` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_SIMP_TAC[];
     REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC]; ALL_TAC] THEN
   SUBGOAL_THEN
     `random_variable p (\x:A. sum(0..n)(\i. (Z:num->A->real) i x) +
                                Z (SUC n) x)` ASSUME_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
   SUBGOAL_THEN
     `integrable p (\x:A. (sum(0..n)(\i. (Z:num->A->real) i x) +
                            Z (SUC n) x) pow 2) /\
      integrable p (\x. (sum(0..n)(\i. Z i x) + Z (SUC n) x) pow 4)`
     STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_BOUNDED THENL
    [EXISTS_TAC `(&(n + 2) * B) pow 2`;
     EXISTS_TAC `(&(n + 2) * B) pow 4`] THEN
    (CONJ_TAC THENL
     [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
      ASM_SIMP_TAC[]]); ALL_TAC] THEN
   (* Establish cross-term integrabilities *)
   SUBGOAL_THEN
     `integrable p (\x:A. sum(0..n)(\i. (Z:num->A->real) i x) pow 3 *
                           Z (SUC n) x)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
    EXISTS_TAC `(&(n + 1) * B) pow 3 * (B:real)` THEN CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[ETA_AX]];
     REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW] THEN
     MP_TAC(ISPECL [`abs(sum(0..n)(\i. (Z:num->A->real) i x)) pow 3`;
                      `(&(n+1) * B) pow 3`;
                      `abs((Z:num->A->real) (SUC n) x)`;
                      `B:real`] REAL_LE_MUL2) THEN
     ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_ABS_POS];
        MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
        ASM_SIMP_TAC[];
        REWRITE_TAC[REAL_ABS_POS];
        ASM_SIMP_TAC[]];
      SIMP_TAC[]]]; ALL_TAC] THEN
   SUBGOAL_THEN
     `integrable p (\x:A. sum(0..n)(\i. (Z:num->A->real) i x) pow 2 *
                           Z (SUC n) x pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
    EXISTS_TAC `(&(n + 1) * B) pow 2 * (B:real) pow 2` THEN CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN CONJ_TAC THEN
     MATCH_MP_TAC RANDOM_VARIABLE_POW THEN ASM_REWRITE_TAC[ETA_AX];
     REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW] THEN
     MP_TAC(ISPECL [`abs(sum(0..n)(\i. (Z:num->A->real) i x)) pow 2`;
                      `(&(n+1) * B) pow 2`;
                      `abs((Z:num->A->real) (SUC n) x) pow 2`;
                      `(B:real) pow 2`] REAL_LE_MUL2) THEN
     ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_ABS_POS];
        MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
        ASM_SIMP_TAC[];
        MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_ABS_POS];
        MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
        ASM_SIMP_TAC[]];
      SIMP_TAC[]]]; ALL_TAC] THEN
   SUBGOAL_THEN
     `integrable p (\x:A. sum(0..n)(\i. (Z:num->A->real) i x) *
                           Z (SUC n) x pow 3)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
    EXISTS_TAC `(&(n + 1) * B) * (B:real) pow 3` THEN CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC RANDOM_VARIABLE_POW THEN ASM_REWRITE_TAC[ETA_AX]];
     REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW] THEN
     MP_TAC(ISPECL [`abs(sum(0..n)(\i. (Z:num->A->real) i x))`;
                      `(&(n+1) * B):real`;
                      `abs((Z:num->A->real) (SUC n) x) pow 3`;
                      `(B:real) pow 3`] REAL_LE_MUL2) THEN
     ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REWRITE_TAC[REAL_ABS_POS];
        ASM_SIMP_TAC[];
        MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_ABS_POS];
        MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
        ASM_SIMP_TAC[]];
      SIMP_TAC[]]]; ALL_TAC] THEN
   SUBGOAL_THEN `integrable p (\x:A. (Z:num->A->real) (SUC n) x pow 4)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `(B:real) pow 4` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN ASM_REWRITE_TAC[ETA_AX];
     REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
     MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
     ASM_SIMP_TAC[]]; ALL_TAC] THEN
   SUBGOAL_THEN
     `integrable p (\x:A. sum(0..n)(\i. (Z:num->A->real) i x) *
                           Z (SUC n) x)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
    EXISTS_TAC `(&(n + 1) * B) * (B:real)` THEN CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN ASM_REWRITE_TAC[ETA_AX];
     REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
     MP_TAC(ISPECL [`abs(sum(0..n)(\i. (Z:num->A->real) i x))`;
                      `(&(n+1) * B):real`;
                      `abs((Z:num->A->real) (SUC n) x)`;
                      `B:real`] REAL_LE_MUL2) THEN
     ANTS_TAC THENL
     [REWRITE_TAC[REAL_ABS_POS] THEN ASM_SIMP_TAC[];
      SIMP_TAC[]]]; ALL_TAC] THEN
   SUBGOAL_THEN
     `integrable p (\x:A. &4 * sum(0..n)(\i. (Z:num->A->real) i x) pow 3 *
                           Z (SUC n) x) /\
      integrable p (\x. &6 * sum(0..n)(\i. Z i x) pow 2 *
                         Z (SUC n) x pow 2) /\
      integrable p (\x. &4 * sum(0..n)(\i. Z i x) * Z (SUC n) x pow 3)`
     STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* Fourth moment expansion *)
   SUBGOAL_THEN
     `expectation p (\x:A. (sum(0..n)(\i. (Z:num->A->real) i x) +
                             Z (SUC n) x) pow 4) =
      expectation p (\x. sum(0..n)(\i. Z i x) pow 4) +
      &6 * expectation p (\x. sum(0..n)(\i. Z i x) pow 2) *
           expectation p (\x. Z (SUC n) x pow 2) +
      expectation p (\x. Z (SUC n) x pow 4)` SUBST1_TAC THENL
   [(* Expand (S+Z)^4 pointwise *)
    SUBGOAL_THEN `!x:A. (sum(0..n)(\i. (Z:num->A->real) i x) +
                          Z (SUC n) x) pow 4 =
        sum(0..n)(\i. Z i x) pow 4 +
        &4 * sum(0..n)(\i. Z i x) pow 3 * Z (SUC n) x +
        &6 * sum(0..n)(\i. Z i x) pow 2 * Z (SUC n) x pow 2 +
        &4 * sum(0..n)(\i. Z i x) * Z (SUC n) x pow 3 +
        Z (SUC n) x pow 4`
      (fun th -> REWRITE_TAC[th]) THENL
    [GEN_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    (* Split E[S^4] from the rest *)
    SUBGOAL_THEN
      `(\x:A. sum(0..n)(\i. (Z:num->A->real) i x) pow 4 +
              &4 * sum(0..n)(\i. Z i x) pow 3 * Z (SUC n) x +
              &6 * sum(0..n)(\i. Z i x) pow 2 * Z (SUC n) x pow 2 +
              &4 * sum(0..n)(\i. Z i x) * Z (SUC n) x pow 3 +
              Z (SUC n) x pow 4) =
       (\x. (\x. sum(0..n)(\i. Z i x) pow 4) x +
            (\x. &4 * sum(0..n)(\i. Z i x) pow 3 * Z (SUC n) x +
                 (&6 * sum(0..n)(\i. Z i x) pow 2 * Z (SUC n) x pow 2 +
                 (&4 * sum(0..n)(\i. Z i x) * Z (SUC n) x pow 3 +
                  Z (SUC n) x pow 4))) x)`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REWRITE_TAC[] THEN
     REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`p:A prob_space`;
      `(\x:A. sum(0..n)(\i. (Z:num->A->real) i x) pow 4)`;
      `(\x:A. &4 * sum(0..n)(\i. (Z:num->A->real) i x) pow 3 *
              Z (SUC n) x +
              &6 * sum(0..n)(\i. Z i x) pow 2 * Z (SUC n) x pow 2 +
              &4 * sum(0..n)(\i. Z i x) * Z (SUC n) x pow 3 +
              Z (SUC n) x pow 4)`] EXPECTATION_ADD) THEN
    REWRITE_TAC[BETA_THM] THEN ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[];
     DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN
    (* Claim the 4-term split *)
    SUBGOAL_THEN
      `expectation p (\x:A.
          &4 * sum(0..n)(\i. (Z:num->A->real) i x) pow 3 * Z (SUC n) x +
          &6 * sum(0..n)(\i. Z i x) pow 2 * Z (SUC n) x pow 2 +
          &4 * sum(0..n)(\i. Z i x) * Z (SUC n) x pow 3 +
          Z (SUC n) x pow 4) =
       &4 * expectation p (\x. sum(0..n)(\i. Z i x) pow 3 * Z (SUC n) x) +
       &6 * expectation p (\x. sum(0..n)(\i. Z i x) pow 2 *
                                Z (SUC n) x pow 2) +
       &4 * expectation p (\x. sum(0..n)(\i. Z i x) * Z (SUC n) x pow 3) +
       expectation p (\x. Z (SUC n) x pow 4)` SUBST1_TAC THENL
    [(* Split via chain of EXPECTATION_ADD + EXPECTATION_CMUL *)
     SUBGOAL_THEN
       `(\x:A. &4 * sum(0..n)(\i. (Z:num->A->real) i x) pow 3 *
               Z (SUC n) x +
               &6 * sum(0..n)(\i. Z i x) pow 2 * Z (SUC n) x pow 2 +
               &4 * sum(0..n)(\i. Z i x) * Z (SUC n) x pow 3 +
               Z (SUC n) x pow 4) =
        (\x. (\x. &4 * sum(0..n)(\i. Z i x) pow 3 * Z (SUC n) x) x +
         (\x. (\x. &6 * sum(0..n)(\i. Z i x) pow 2 *
                    Z (SUC n) x pow 2) x +
         (\x. (\x. &4 * sum(0..n)(\i. Z i x) * Z (SUC n) x pow 3) x +
         (\x. Z (SUC n) x pow 4) x) x) x)`
       SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; BETA_THM]; ALL_TAC] THEN
     MP_TAC(ISPECL [`p:A prob_space`;
       `\x:A. &4 * sum(0..n)(\i. (Z:num->A->real) i x) pow 3 *
              Z (SUC n) x`;
       `\x:A. (\x. &6 * sum(0..n)(\i. (Z:num->A->real) i x) pow 2 *
                    Z (SUC n) x pow 2) x +
              (\x. (\x. &4 * sum(0..n)(\i. Z i x) * Z (SUC n) x pow 3) x +
              (\x. Z (SUC n) x pow 4) x) x`] EXPECTATION_ADD) THEN
     REWRITE_TAC[BETA_THM] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC INTEGRABLE_ADD THEN REWRITE_TAC[BETA_THM] THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC INTEGRABLE_ADD THEN REWRITE_TAC[BETA_THM] THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
     SUBGOAL_THEN
       `expectation p (\x:A. &4 * sum(0..n)(\i. (Z:num->A->real) i x) pow 3 *
                              Z (SUC n) x) =
        &4 * expectation p (\x. sum(0..n)(\i. Z i x) pow 3 * Z (SUC n) x)`
       SUBST1_TAC THENL
     [MATCH_MP_TAC EXPECTATION_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     AP_TERM_TAC THEN
     MP_TAC(ISPECL [`p:A prob_space`;
       `\x:A. &6 * sum(0..n)(\i. (Z:num->A->real) i x) pow 2 *
              Z (SUC n) x pow 2`;
       `\x:A. (\x. &4 * sum(0..n)(\i. (Z:num->A->real) i x) *
                    Z (SUC n) x pow 3) x +
              (\x. Z (SUC n) x pow 4) x`] EXPECTATION_ADD) THEN
     REWRITE_TAC[BETA_THM] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC INTEGRABLE_ADD THEN REWRITE_TAC[BETA_THM] THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
     SUBGOAL_THEN
       `expectation p (\x:A. &6 * sum(0..n)(\i. (Z:num->A->real) i x) pow 2 *
                              Z (SUC n) x pow 2) =
        &6 * expectation p (\x. sum(0..n)(\i. Z i x) pow 2 *
                                 Z (SUC n) x pow 2)`
       SUBST1_TAC THENL
     [MATCH_MP_TAC EXPECTATION_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     AP_TERM_TAC THEN
     MP_TAC(ISPECL [`p:A prob_space`;
       `\x:A. &4 * sum(0..n)(\i. (Z:num->A->real) i x) *
              Z (SUC n) x pow 3`;
       `\x:A. (Z:num->A->real) (SUC n) x pow 4`] EXPECTATION_ADD) THEN
     REWRITE_TAC[BETA_THM; ETA_AX] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
     SUBGOAL_THEN
       `expectation p (\x:A. &4 * sum(0..n)(\i. (Z:num->A->real) i x) *
                              Z (SUC n) x pow 3) =
        &4 * expectation p (\x. sum(0..n)(\i. Z i x) * Z (SUC n) x pow 3)`
       SUBST1_TAC THENL
     [MATCH_MP_TAC EXPECTATION_CMUL THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC]; ALL_TAC] THEN
    (* Now use BLOCK_INDEP_SUM_POW and centering *)
    SUBGOAL_THEN `SUC n = n + 1` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    (* Factor E[S^3*Z] = E[S^3]*E[Z] via BLOCK_INDEP_SUM_POW *)
    SUBGOAL_THEN
      `expectation p (\x:A. sum(0..n)(\i. (Z:num->A->real) i x) pow 3 *
                             Z (SUC n) x) =
       expectation p (\x. sum(0..n)(\i. Z i x) pow 3) *
       expectation p (\x. Z (SUC n) x pow 1)` SUBST1_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     MP_TAC(ISPECL [`p:A prob_space`; `Z:num->A->real`; `B:real`;
                     `3`; `1`; `n:num`] BLOCK_INDEP_SUM_POW) THEN
     ASM_REWRITE_TAC[REAL_POW_1; ETA_AX]; ALL_TAC] THEN
    SUBGOAL_THEN `expectation p (\x:A. (Z:num->A->real) (SUC n) x pow 1) = &0`
      SUBST1_TAC THENL
    [REWRITE_TAC[REAL_POW_1; ETA_AX] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID] THEN
    (* Factor E[S^2*Z^2] = E[S^2]*E[Z^2] *)
    SUBGOAL_THEN
      `expectation p (\x:A. sum(0..n)(\i. (Z:num->A->real) i x) pow 2 *
                             Z (SUC n) x pow 2) =
       expectation p (\x. sum(0..n)(\i. Z i x) pow 2) *
       expectation p (\x. Z (SUC n) x pow 2)` SUBST1_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     MP_TAC(ISPECL [`p:A prob_space`; `Z:num->A->real`; `B:real`;
                     `2`; `2`; `n:num`] BLOCK_INDEP_SUM_POW) THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
    (* Factor E[S*Z^3] = E[S]*E[Z^3], then E[S] = 0 *)
    SUBGOAL_THEN
      `expectation p (\x:A. sum(0..n)(\i. (Z:num->A->real) i x) *
                             Z (SUC n) x pow 3) =
       expectation p (\x. sum(0..n)(\i. Z i x)) *
       expectation p (\x. Z (SUC n) x pow 3)` SUBST1_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     MP_TAC(ISPECL [`p:A prob_space`; `Z:num->A->real`; `B:real`;
                     `1`; `3`; `n:num`] BLOCK_INDEP_SUM_POW) THEN
     ASM_REWRITE_TAC[REAL_POW_1; ETA_AX]; ALL_TAC] THEN
    SUBGOAL_THEN
      `expectation p (\x:A. sum(0..n)(\i. (Z:num->A->real) i x)) = &0`
      SUBST1_TAC THENL
    [MATCH_MP_TAC EXPECTATION_SUM_CENTERED THEN ASM_REWRITE_TAC[];
     REAL_ARITH_TAC]; ALL_TAC] THEN
   (* Second moment recurrence: E[(S+Z)^2] = E[S^2] + E[Z^2] *)
   SUBGOAL_THEN
     `expectation p (\x:A. (sum(0..n)(\i. (Z:num->A->real) i x) +
                             Z (SUC n) x) pow 2) =
      expectation p (\x. sum(0..n)(\i. Z i x) pow 2) +
      expectation p (\x. Z (SUC n) x pow 2)` SUBST1_TAC THENL
   [SUBGOAL_THEN `!x:A. (sum(0..n)(\i. (Z:num->A->real) i x) +
                          Z (SUC n) x) pow 2 =
       sum(0..n)(\i. Z i x) pow 2 +
       &2 * sum(0..n)(\i. Z i x) * Z (SUC n) x +
       Z (SUC n) x pow 2`
     (fun th -> REWRITE_TAC[th]) THENL
    [GEN_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN
      `(\x:A. sum(0..n)(\i. (Z:num->A->real) i x) pow 2 +
              &2 * sum(0..n)(\i. Z i x) * Z (SUC n) x +
              Z (SUC n) x pow 2) =
       (\x. (\x. sum(0..n)(\i. Z i x) pow 2) x +
            (\x. &2 * sum(0..n)(\i. Z i x) * Z (SUC n) x +
                 Z (SUC n) x pow 2) x)`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM; BETA_THM]; ALL_TAC] THEN
    MP_TAC(ISPECL [`p:A prob_space`;
      `\x:A. sum(0..n)(\i. (Z:num->A->real) i x) pow 2`;
      `\x:A. &2 * sum(0..n)(\i. (Z:num->A->real) i x) * Z (SUC n) x +
             Z (SUC n) x pow 2`] EXPECTATION_ADD) THEN
    REWRITE_TAC[BETA_THM] THEN ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_ADD THEN
     ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
     DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN
      `(\x:A. &2 * sum(0..n)(\i. (Z:num->A->real) i x) * Z (SUC n) x +
              Z (SUC n) x pow 2) =
       (\x. (\x. &2 * sum(0..n)(\i. Z i x) * Z (SUC n) x) x +
            (\x. Z (SUC n) x pow 2) x)`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM; BETA_THM]; ALL_TAC] THEN
    MP_TAC(ISPECL [`p:A prob_space`;
      `\x:A. &2 * sum(0..n)(\i. (Z:num->A->real) i x) * Z (SUC n) x`;
      `\x:A. (Z:num->A->real) (SUC n) x pow 2`] EXPECTATION_ADD) THEN
    REWRITE_TAC[BETA_THM; ETA_AX] THEN ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
     ASM_REWRITE_TAC[];
     DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN
      `expectation p (\x:A. &2 * sum(0..n)(\i. (Z:num->A->real) i x) *
                              Z (SUC n) x) = &0` SUBST1_TAC THENL
    [MP_TAC(ISPECL [`p:A prob_space`; `&2`;
      `\x:A. sum(0..n)(\i. (Z:num->A->real) i x) * Z (SUC n) x`]
      EXPECTATION_CMUL) THEN
     REWRITE_TAC[BETA_THM] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
     SUBGOAL_THEN
       `expectation p (\x:A. sum(0..n)(\i. (Z:num->A->real) i x) *
                              Z (SUC n) x) = &0` SUBST1_TAC THENL
     [SUBGOAL_THEN `SUC n = n + 1` ASSUME_TAC THENL
      [ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`p:A prob_space`; `Z:num->A->real`; `B:real`;
                       `1`; `1`; `n:num`] BLOCK_INDEP_SUM_POW) THEN
      ASM_REWRITE_TAC[REAL_POW_1; ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN
        `expectation p (\x:A. sum(0..n)(\i. (Z:num->A->real) i x)) = &0`
        SUBST1_TAC THENL
      [MATCH_MP_TAC EXPECTATION_SUM_CENTERED THEN ASM_REWRITE_TAC[];
       REAL_ARITH_TAC];
      REAL_ARITH_TAC];
     REAL_ARITH_TAC]; ALL_TAC] THEN
   (* Final algebra *)
   SUBGOAL_THEN
     `expectation p (\x:A. (Z:num->A->real) (SUC n) x pow 4) <=
      B pow 2 * expectation p (\x. Z (SUC n) x pow 2)` ASSUME_TAC THENL
   [SUBGOAL_THEN
      `B pow 2 * expectation p (\x:A. (Z:num->A->real) (SUC n) x pow 2) =
       expectation p (\x. B pow 2 * Z (SUC n) x pow 2)` SUBST1_TAC THENL
    [MATCH_MP_TAC(GSYM EXPECTATION_CMUL) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC EXPECTATION_MONO THEN REPEAT CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[BETA_THM] THEN REPEAT STRIP_TAC THEN
     REWRITE_TAC[ARITH_RULE `4 = 2 + 2`; REAL_POW_ADD] THEN
     MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
     SUBGOAL_THEN `(Z:num->A->real) (SUC n) x pow 2 = abs(Z (SUC n) x) pow 2`
       SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW2_ABS]; ALL_TAC] THEN
     MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
     ASM_SIMP_TAC[]]; ALL_TAC] THEN
   SUBGOAL_THEN
     `&0 <= expectation p (\x:A. sum(0..n)(\i. (Z:num->A->real) i x) pow 2)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC EXPECTATION_POS THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
   SUBGOAL_THEN
     `&0 <= expectation p (\x:A. (Z:num->A->real) (SUC n) x pow 2)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC EXPECTATION_POS THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC
     `(B pow 2 * expectation p (\x:A. sum(0..n)(\i. (Z:num->A->real) i x) pow 2) +
       &3 * expectation p (\x. sum(0..n)(\i. Z i x) pow 2) pow 2) +
      &6 * expectation p (\x. sum(0..n)(\i. Z i x) pow 2) *
           expectation p (\x. Z (SUC n) x pow 2) +
      B pow 2 * expectation p (\x:A. (Z:num->A->real) (SUC n) x pow 2)` THEN
   CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
     `(expectation p (\x:A. sum(0..n)(\i. (Z:num->A->real) i x) pow 2) +
       expectation p (\x. Z (SUC n) x pow 2)) pow 2 =
      expectation p (\x. sum(0..n)(\i. Z i x) pow 2) pow 2 +
      &2 * expectation p (\x. sum(0..n)(\i. Z i x) pow 2) *
           expectation p (\x. Z (SUC n) x pow 2) +
      expectation p (\x. Z (SUC n) x pow 2) pow 2` SUBST1_TAC THENL
   [CONV_TAC REAL_RING; ALL_TAC] THEN
   GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [REAL_ADD_LDISTRIB] THEN
   MATCH_MP_TAC(REAL_ARITH
     `&0 <= v2 ==> (a + &3 * c) + (&6 * b + d) <=
                    (a + d) + &3 * (c + &2 * b + v2)`) THEN
   REWRITE_TAC[REAL_LE_POW_2]]);;

(* Mutual independence is preserved by clamping *)
let MUTUALLY_INDEP_RV_SEQ_CLAMP = prove
 (`!p:A prob_space (X:num->A->real) c.
    &0 < c /\ mutually_indep_rv_seq p X
    ==> mutually_indep_rv_seq p (\i x. min(max(X i x) (--c)) c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mutually_indep_rv_seq] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  STRIP_TAC THEN CONJ_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_CLAMP THEN
   ASM_REWRITE_TAC[ETA_AX];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `?n:num. n IN S /\ (a:num->real) n < --c` THENL
  [FIRST_X_ASSUM(X_CHOOSE_THEN `n0:num` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\
       min (max ((X:num->A->real) n0 x) (--c)) c <= (a:num->real) n0} = {}`
     ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:A` THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN
     `INTERS (IMAGE (\n. {x:A | x IN prob_carrier p /\
       min (max ((X:num->A->real) n x) (--c)) c <= (a:num->real) n}) S) = {}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTERS; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:A` THEN REWRITE_TAC[NOT_FORALL_THM] THEN
    EXISTS_TAC `({}:A->bool)` THEN
    REWRITE_TAC[NOT_IN_EMPTY; IN_IMAGE; NOT_IMP] THEN
    EXISTS_TAC `n0:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   REWRITE_TAC[PROB_EMPTY] THEN CONV_TAC SYM_CONV THEN
   ASM_SIMP_TAC[PRODUCT_EQ_0] THEN
   EXISTS_TAC `n0:num` THEN ASM_REWRITE_TAC[] THEN
   ASM_REWRITE_TAC[PROB_EMPTY];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n:num. n IN S ==> ~((a:num->real) n < --c)`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `!n:num. n IN S ==> (a:num->real) n >= c` THENL
  [SUBGOAL_THEN
     `!n. n IN S ==>
       {x:A | x IN prob_carrier p /\
         min (max ((X:num->A->real) n x) (--c)) c <=
         (a:num->real) n} = prob_carrier p`
     ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
    EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN
     `IMAGE (\n. {x:A | x IN prob_carrier p /\
       min (max ((X:num->A->real) n x) (--c)) c <=
       (a:num->real) n}) S =
      IMAGE (\n:num. prob_carrier p:A->bool) S`
     SUBST1_TAC THENL
   [MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN
     `!n. n IN S ==>
       prob p {x:A | x IN prob_carrier p /\
         min (max ((X:num->A->real) n x) (--c)) c <=
         (a:num->real) n} = &1`
     (fun th -> SIMP_TAC[th]) THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[PROB_SPACE]; ALL_TAC] THEN
   SUBGOAL_THEN
     `IMAGE (\n:num. prob_carrier p:A->bool) S = {prob_carrier p}`
     SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[INTERS_1; PROB_SPACE] THEN
   ASM_SIMP_TAC[PRODUCT_CONST; REAL_POW_ONE];
   ALL_TAC] THEN
  ABBREV_TAC `S' = {n:num | n IN S /\ ~((a:num->real) n >= c)}` THEN
  SUBGOAL_THEN
    `(S':num->bool) SUBSET S /\ FINITE S' /\ ~(S' = {})`
    STRIP_ASSUME_TAC THENL
  [EXPAND_TAC "S'" THEN REPEAT CONJ_TAC THENL
   [SET_TAC[];
    MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM;
                     NOT_FORALL_THM] THEN
    ASM_MESON_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!n. n IN S' ==> ~((a:num->real) n < --c) /\ ~(a n >= c)`
    ASSUME_TAC THENL
  [X_GEN_TAC `n:num` THEN EXPAND_TAC "S'" THEN
   REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!n. n IN S' ==>
      {x:A | x IN prob_carrier p /\
        min (max ((X:num->A->real) n x) (--c)) c <=
        (a:num->real) n} =
      {x | x IN prob_carrier p /\ X n x <= a n}`
    ASSUME_TAC THENL
  [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
   STRIP_TAC THEN
   REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
   EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!n. n IN S DIFF S' ==>
      {x:A | x IN prob_carrier p /\
        min (max ((X:num->A->real) n x) (--c)) c <=
        (a:num->real) n} = prob_carrier p`
    ASSUME_TAC THENL
  [X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
   SUBGOAL_THEN `(a:num->real) n >= c` ASSUME_TAC THENL
   [ASM_CASES_TAC `(a:num->real) n >= c` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((n:num) IN S')` THEN
    EXPAND_TAC "S'" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
   REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
   EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
   DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `S = (S':num->bool) UNION (S DIFF S')`
    (fun th ->
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th] THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
  [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_UNION; INTERS_UNION] THEN
  SUBGOAL_THEN
    `IMAGE (\n. {x:A | x IN prob_carrier p /\
      min (max ((X:num->A->real) n x) (--c)) c <=
      (a:num->real) n}) S' =
     IMAGE (\n. {x | x IN prob_carrier p /\ X n x <= a n}) S'`
    SUBST1_TAC THENL
  [MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `IMAGE (\n. {x:A | x IN prob_carrier p /\
      min (max ((X:num->A->real) n x) (--c)) c <=
      (a:num->real) n}) (S DIFF S') =
     IMAGE (\n:num. prob_carrier p:A->bool) (S DIFF S')`
    SUBST1_TAC THENL
  [MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `S DIFF (S':num->bool) = {}` THENL
  [SUBGOAL_THEN `S = (S':num->bool)` SUBST_ALL_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
   ASM_REWRITE_TAC[IMAGE_CLAUSES; INTERS_0; INTER_UNIV; UNION_EMPTY] THEN
   SUBGOAL_THEN
     `product S' (\n. prob p {x:A | x IN prob_carrier p /\
       min (max ((X:num->A->real) n x) (--c)) c <=
       (a:num->real) n}) =
      product S' (\n. prob p {x | x IN prob_carrier p /\ X n x <= a n})`
     SUBST1_TAC THENL
   [MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    BETA_TAC THEN AP_TERM_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`S':num->bool`; `a:num->real`]) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `IMAGE (\n:num. prob_carrier p:A->bool) (S DIFF S') = {prob_carrier p}`
    SUBST1_TAC THENL
  [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[INTERS_1] THEN
  SUBGOAL_THEN
    `INTERS (IMAGE (\n. {x:A | x IN prob_carrier p /\
      (X:num->A->real) n x <= (a:num->real) n}) S') SUBSET
     prob_carrier p`
    (fun th ->
      REWRITE_TAC[MATCH_MP
        (prove(`!s:A->bool t. s SUBSET t ==> s INTER t = s`,
               SET_TAC[])) th]) THENL
  [REWRITE_TAC[SUBSET; IN_INTERS; IN_IMAGE] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   UNDISCH_TAC `~((S':num->bool) = {})` THEN
   REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
   DISCH_THEN(X_CHOOSE_TAC `n0:num`) THEN
   FIRST_X_ASSUM(MP_TAC o SPEC
     `{x:A | x IN prob_carrier p /\
       (X:num->A->real) n0 x <= (a:num->real) n0}`) THEN
   ANTS_TAC THENL
   [EXISTS_TAC `n0:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SIMP_TAC[IN_ELIM_THM];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `FINITE (S DIFF (S':num->bool)) /\ DISJOINT S' (S DIFF S')`
    STRIP_ASSUME_TAC THENL
  [CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_DIFF THEN ASM_REWRITE_TAC[];
    SET_TAC[]];
   ALL_TAC] THEN
  ASM_SIMP_TAC[PRODUCT_UNION] THEN
  REWRITE_TAC[PROB_SPACE] THEN
  SUBGOAL_THEN `product (S DIFF (S':num->bool)) (\x:num. &1) = &1`
    SUBST1_TAC THENL
  [ASM_SIMP_TAC[PRODUCT_CONST; REAL_POW_ONE]; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RID] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`S':num->bool`; `a:num->real`]) THEN
  ASM_REWRITE_TAC[]);;

(* Mutual independence with index-dependent shift *)
let MUTUALLY_INDEP_RV_SEQ_SHIFT_VARYING = prove
 (`!p:A prob_space (Z:num->A->real) (d:num->real).
    mutually_indep_rv_seq p Z
    ==> mutually_indep_rv_seq p (\i x. Z i x - d i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mutually_indep_rv_seq] THEN STRIP_TAC THEN
  CONJ_TAC THENL
  [GEN_TAC THEN REWRITE_TAC[real_sub] THEN
   MATCH_MP_TAC RANDOM_VARIABLE_SHIFT THEN
   ASM_REWRITE_TAC[ETA_AX];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `IMAGE (\n. {x:A | x IN prob_carrier p /\
       (Z:num->A->real) n x - (d:num->real) n <=
       (a:num->real) n}) S =
     IMAGE (\n. {x | x IN prob_carrier p /\
       Z n x <= a n + d n}) S`
    SUBST1_TAC THENL
  [MATCH_MP_TAC IMAGE_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
   REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
   ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!n:num. prob p {x:A | x IN prob_carrier p /\
       (Z:num->A->real) n x - (d:num->real) n <=
       (a:num->real) n} =
     prob p {x | x IN prob_carrier p /\ Z n x <= a n + d n}`
    (fun th -> REWRITE_TAC[th]) THENL
  [GEN_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
   ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`S:num->bool`;
     `\n:num. (a:num->real) n + (d:num->real) n`]) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC);;

(* ================================================================== *)
(* THREE_SERIES_NECESSITY_INDEP: Three-series necessity for indep RVs *)
(* Independent proof using FOURTH_MOMENT_BOUND_INDEP_CENTERED and    *)
(* SUMMABLE_VARIANCE_FROM_CONVERGENCE_V2, rather than the crossing   *)
(* condition approach of THREE_SERIES_NECESSITY.                      *)
(* ================================================================== *)
let EXPECTATION_SUMMABLE_CHEBYSHEV = prove
 (`!(p:A prob_space) (Y:num->A->real) (Z:num->A->real) c.
    &0 < c /\
    (!n. integrable p (\x. Y n x)) /\
    (!n x. abs(Y n x) <= c) /\
    (!n x. Y n x - expectation p (\y. Y n y) = Z n x) /\
    mutually_indep_rv_seq p Z /\
    (!n. integrable p (\x. Z n x)) /\
    (!n. expectation p (\x. Z n x) = &0) /\
    (!n x. x IN prob_carrier p ==> abs(Z n x) <= &2 * c) /\
    (!n. integrable p (\x. Z n x pow 2)) /\
    (!n. &0 <= variance p (\x. Y n x)) /\
    real_summable (from 0) (\n. variance p (\x. Y n x)) /\
    almost_surely p
      {x | ?L. ((\n. sum(0..n) (\i. Y i x)) ---> L) sequentially}
    ==> real_summable (from 0) (\n. expectation p (\x. Y n x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
   (* Proof by contradiction *)
   MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
   (* Negate REAL_SUMMABLE_CAUCHY: exists eps, forall N, exists m,n >= N
      with |sum(from 0 INTER m..n)(E[Y])| >= eps *)
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
     [REAL_SUMMABLE_CAUCHY]) THEN
   DISCH_THEN(fun th -> MP_TAC(REWRITE_RULE
     [NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM;
      REAL_NOT_LT; FROM_0_INTER_NUMSEG] th)) THEN
   DISCH_THEN(X_CHOOSE_THEN `eps:real` MP_TAC) THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NC")) THEN
   (* From summable Var(Y), get tail bound K0 *)
   SUBGOAL_THEN `!n. &0 <= variance p (\x:A. (Y:num->A->real) n x)`
     ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   MP_TAC(ISPEC `\n. variance (p:A prob_space) (\x:A. (Y:num->A->real) n x)`
     REAL_SUMMABLE_TAIL_BOUND) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(MP_TAC o SPEC `(eps / &2) pow 2 / &2`) THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
     REAL_ARITH_TAC]; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_TAC `K0:num`) THEN
   (* Var(Z_n) = Var(Y_n) *)
   SUBGOAL_THEN `!n. variance p (\x:A. (Z:num->A->real) n x) =
     variance p (\x. (Y:num->A->real) n x)` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_CURRY_TAC "Z" THEN
    SUBGOAL_THEN `(\x:A. (Y:num->A->real) n x -
      expectation p (\y. Y n y)) =
      (\x. Y n x + (--expectation p (\y. Y n y)))` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC VARIANCE_SHIFT THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM ETA_AX] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* Covariance of Z_i, Z_j = 0 for i != j *)
   SUBGOAL_THEN `!i j. ~(i = j) ==>
     covariance p (\x:A. (Z:num->A->real) i x)
       (\x. Z j x) = &0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC COVARIANCE_BOUNDED_INDEP THEN
    MAP_EVERY EXISTS_TAC [`&2 * c`; `&2 * c`] THEN
    REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
     GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[];
     GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[];
     SUBGOAL_THEN `(\x:A. (Z:num->A->real) i x) = Z i` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
     SUBGOAL_THEN `(\x:A. (Z:num->A->real) j x) = Z j` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
     UNDISCH_TAC `mutually_indep_rv_seq p (Z:num->A->real)` THEN
     DISCH_THEN(MP_TAC o MATCH_MP MUTUALLY_INDEP_RV_SEQ_PAIRWISE) THEN
     DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   (* Define C_K = non-Cauchy set at rate eps/2 from index K *)
   ABBREV_TAC `C_K = \K:num. UNIONS {UNIONS
     {{(x:A) | x IN prob_carrier p /\
       abs(sum(K + a..K + a + b) (\i. (Y:num->A->real) i x)) >=
         eps / &2} | b IN (:num)} | a IN (:num)}` THEN
   (* Each inner set is an event *)
   SUBGOAL_THEN `!K a b.
     {x:A | x IN prob_carrier p /\
       abs(sum(K + a..K + a + b) (\i. (Y:num->A->real) i x)) >=
         eps / &2} IN prob_events p` (LABEL_TAC "Sev") THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC RV_PREIMAGE_GE THEN
    MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN
    SUBGOAL_THEN `(\x:A. sum(K + a..K + a + b)
      (\i. (Y:num->A->real) i x)) =
      (\x. sum(0..b) (\i. Y (K + a + i) x))` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM; ADD_ASSOC; SUM_REINDEX_SHIFT]; ALL_TAC] THEN
    MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* C_K is an event for each K *)
   SUBGOAL_THEN `!K. (C_K:num->A->bool) K IN prob_events p`
     (LABEL_TAC "Cev") THENL
   [GEN_TAC THEN EXPAND_TAC "C_K" THEN
    MATCH_MP_TAC PROB_COUNTABLE_UNION_IN_EVENTS THEN CONJ_TAC THENL
    [REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
     GEN_TAC THEN DISCH_TAC THEN
     MATCH_MP_TAC PROB_COUNTABLE_UNION_IN_EVENTS THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
      GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC COUNTABLE_IMAGE THEN
      REWRITE_TAC[NUM_COUNTABLE]];
     REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC COUNTABLE_IMAGE THEN
     REWRITE_TAC[NUM_COUNTABLE]];
    ALL_TAC] THEN
   (* C_K is decreasing: C_{SUC K} SUBSET C_K *)
   SUBGOAL_THEN `!K. (C_K:num->A->bool) (SUC K) SUBSET C_K K`
     (LABEL_TAC "Cdec") THENL
   [GEN_TAC THEN EXPAND_TAC "C_K" THEN
    REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_UNIV; IN_ELIM_THM] THEN
    X_GEN_TAC `x:A` THEN
    DISCH_THEN(X_CHOOSE_THEN `a:num` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `b:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `a + 1` THEN EXISTS_TAC `b:num` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `K + (a + 1) = SUC K + a` SUBST1_TAC THENL
    [ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `K + (a + 1) + b = SUC K + a + b` SUBST1_TAC THENL
    [ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   (* INTERS {C_K} SUBSET {x | sum Y not Cauchy at rate eps/2} *)
   (* Actually: INTERS {C_K} has prob 0 because sum Y converges a.s. *)
   SUBGOAL_THEN `prob p (INTERS {(C_K:num->A->bool) K | K IN (:num)}) = &0`
     (LABEL_TAC "CK0") THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC PROB_POSITIVE THEN
     MATCH_MP_TAC PROB_INDEXED_INTER_IN_EVENTS THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    (* Extract null event B from almost_surely *)
    UNDISCH_TAC `almost_surely p {x:A | ?L. ((\n. sum(0..n)
      (\i. (Y:num->A->real) i x)) ---> L) sequentially}` THEN
    REWRITE_TAC[almost_surely; null_event] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:A->bool` STRIP_ASSUME_TAC) THEN
    (* prob(INTERS C_K) <= prob(B) = 0 *)
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `prob p (B:A->bool)` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC PROB_MONO THEN ASM_REWRITE_TAC[] THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC PROB_INDEXED_INTER_IN_EVENTS THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
     (* Show INTERS C_K SUBSET B *)
     MATCH_MP_TAC SUBSET_TRANS THEN
     EXISTS_TAC `{x:A | x IN prob_carrier p /\
       ~(x IN {x | ?L. ((\n. sum(0..n) (\i. (Y:num->A->real) i x)) ---> L)
         sequentially})}` THEN
     CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; INTERS_GSPEC; IN_UNIV; IN_ELIM_THM] THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:A) IN prob_carrier p` ASSUME_TAC THENL
      [SUBGOAL_THEN `(x:A) IN (C_K:num->A->bool) 0` MP_TAC THENL
       [ASM_REWRITE_TAC[];
        EXPAND_TAC "C_K" THEN
        REWRITE_TAC[UNIONS_GSPEC; IN_UNIV; IN_ELIM_THM] THEN
        MESON_TAC[]];
       ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      (* x is in every C_K, so partial sums not Cauchy, hence diverge *)
      REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `L:real` THEN
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o
        REWRITE_RULE[REALLIM_SEQUENTIALLY]) THEN
      DISCH_THEN(MP_TAC o SPEC `eps / &4`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN
      (* Use SUC N0 so range starts >= 1, avoiding edge case *)
      SUBGOAL_THEN `(x:A) IN (C_K:num->A->bool) (SUC N0)` MP_TAC THENL
      [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "C_K" THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_UNIV; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `aa:num`
        (X_CHOOSE_THEN `bb:num` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `abs(sum(0..SUC N0+aa+bb)
        (\i. (Y:num->A->real) i x) - L) < eps / &4` ASSUME_TAC THENL
      [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `abs(sum(0..(SUC N0+aa)-1)
        (\i. (Y:num->A->real) i x) - L) < eps / &4` ASSUME_TAC THENL
      [FIRST_X_ASSUM(MP_TAC o SPEC `(SUC N0 + aa) - 1`) THEN
       ANTS_TAC THENL [ARITH_TAC; SIMP_TAC[]]; ALL_TAC] THEN
      SUBGOAL_THEN `sum(SUC N0+aa..SUC N0+aa+bb)
        (\i. (Y:num->A->real) i x) =
        sum(0..SUC N0+aa+bb) (\i. Y i x) -
        sum(0..(SUC N0+aa)-1) (\i. Y i x)` ASSUME_TAC THENL
      [MATCH_MP_TAC(REAL_ARITH
        `!a b c:real. a + b = c ==> b = c - a`) THEN
       MATCH_MP_TAC SUM_COMBINE_L THEN ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `abs(sum(SUC N0 + aa..SUC N0 + aa + bb)
        (\i. (Y:num->A->real) i x)) >= eps / &2` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]];
     ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
   (* By PROB_CONTINUITY_FROM_ABOVE: prob(C_K) -> 0 *)
   MP_TAC(ISPECL [`p:A prob_space`; `C_K:num->A->bool`]
     PROB_CONTINUITY_FROM_ABOVE) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   (* Get K1 with prob(C_{K1}) < 1/2 *)
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
   DISCH_THEN(MP_TAC o SPEC `&1 / &2`) THEN
   ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_TAC `K1:num`) THEN
   SUBGOAL_THEN `prob p ((C_K:num->A->bool) K1) < &1 / &2`
     ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `K1:num`) THEN
    ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH
      `&0 <= p ==> abs(p - &0) < &1 / &2 ==> p < &1 / &2`) THEN
    MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* Take K = max(K0, K1), get m,n from non-Cauchy *)
   REMOVE_THEN "NC" (MP_TAC o SPEC `K0 + K1:num`) THEN
   REWRITE_TAC[NOT_FORALL_THM; REAL_NOT_LT] THEN
   DISCH_THEN(X_CHOOSE_THEN `m1:num` (X_CHOOSE_THEN `n1:num`
     STRIP_ASSUME_TAC)) THEN
   (* Key facts: m1 >= K0, m1 >= K1 *)
   SUBGOAL_THEN `K0:num <= m1` ASSUME_TAC THENL
   [UNDISCH_TAC `m1:num >= K0 + K1` THEN
    MESON_TAC[LE_TRANS; LE_ADD; GE]; ALL_TAC] THEN
   SUBGOAL_THEN `K1:num <= m1` ASSUME_TAC THENL
   [UNDISCH_TAC `m1:num >= K0 + K1` THEN
    MESON_TAC[LE_TRANS; LE_ADDR; GE]; ALL_TAC] THEN
   (* Derive m1 <= n1 from non-triviality of sum *)
   SUBGOAL_THEN `m1:num <= n1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `sum(m1..n1) (\n. expectation p (\x:A.
      (Y:num->A->real) n x)) = &0` MP_TAC THENL
    [MATCH_MP_TAC SUM_TRIV_NUMSEG THEN ASM_REWRITE_TAC[GSYM NOT_LE];
     UNDISCH_TAC `eps <= abs(sum(m1..n1)
       (\n. expectation p (\x:A. (Y:num->A->real) n x)))` THEN
     ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
   (* For x in carrier \ C_K1: |sum(m1..n1)(Y(x))| < eps/2 *)
   (* So |sum(m1..n1)(Z(x))| >= eps/2 *)
   (* Hence carrier \ C_{K1} SUBSET {abs(sum(m1..n1)(Z)) >= eps/2} *)
   SUBGOAL_THEN `(prob_carrier p DIFF (C_K:num->A->bool) K1) SUBSET
     {x:A | x IN prob_carrier p /\
       abs(sum(m1..n1) (\i. (Z:num->A->real) i x)) >= eps / &2}`
     ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_DIFF; IN_ELIM_THM] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    (* x not in C_{K1}, so for all a,b: |sum(K1+a..K1+a+b)(Y(x))| < eps/2 *)
    SUBGOAL_THEN `!a b. abs(sum(K1 + a..K1 + a + b)
      (\i. (Y:num->A->real) i x)) < eps / &2` ASSUME_TAC THENL
    [REPEAT GEN_TAC THEN
     UNDISCH_TAC `~((x:A) IN (C_K:num->A->bool) K1)` THEN
     EXPAND_TAC "C_K" THEN
     REWRITE_TAC[UNIONS_GSPEC; IN_UNIV; IN_ELIM_THM] THEN
     REWRITE_TAC[NOT_EXISTS_THM] THEN
     DISCH_THEN(MP_TAC o SPECL [`a:num`; `b:num`]) THEN
     REWRITE_TAC[DE_MORGAN_THM; real_ge; REAL_NOT_LE] THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    (* With a = m1 - K1, b = n1 - m1:
       |sum(m1..n1)(Y(x))| < eps/2 *)
    SUBGOAL_THEN `abs(sum(m1..n1) (\i. (Y:num->A->real) i x)) < eps / &2`
      ASSUME_TAC THENL
    [SUBGOAL_THEN `K1 + (m1 - K1) = m1:num` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `K1 + (m1 - K1) + (n1 - m1) = n1:num` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
     FIRST_X_ASSUM(MP_TAC o SPECL [`m1 - K1:num`; `n1 - m1:num`]) THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    (* sum(m1..n1)(Z(x)) = sum(m1..n1)(Y(x)) - sum(m1..n1)(E[Y]) *)
    SUBGOAL_THEN `sum(m1..n1) (\i. (Z:num->A->real) i x) =
      sum(m1..n1) (\i. (Y:num->A->real) i x) -
      sum(m1..n1) (\i. expectation p (\y:A. Y i y))`
      ASSUME_TAC THENL
    [REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN
     MATCH_MP_TAC SUM_EQ_NUMSEG THEN
     REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH
      `eps <= abs(e) /\ abs(y) < eps / &2
       ==> abs(y - e) >= eps / &2`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* Apply Chebyshev to sum(m1..n1)(Z) *)
   (* First: reindex sum(m1..n1)(Z) = sum(0..n1-m1)(\j. Z(m1+j)) *)
   ABBREV_TAC `nn = n1 - m1:num` THEN
   SUBGOAL_THEN `m1 + nn = n1:num` ASSUME_TAC THENL
   [EXPAND_TAC "nn" THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
   (* The Chebyshev event is also an event *)
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
     abs(sum(m1..n1) (\i. (Z:num->A->real) i x)) >= eps / &2}
     IN prob_events p` ASSUME_TAC THENL
   [MATCH_MP_TAC RV_PREIMAGE_GE THEN
    MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN
    SUBGOAL_THEN `n1 = m1 + nn:num` (fun th -> REWRITE_TAC[th; SUM_REINDEX_SHIFT]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* prob(carrier \ C_{K1}) <= prob({abs(sum Z) >= eps/2}) *)
   SUBGOAL_THEN `prob p (prob_carrier p DIFF (C_K:num->A->bool) K1) <=
     prob p {x:A | x IN prob_carrier p /\
       abs(sum(m1..n1) (\i. (Z:num->A->real) i x)) >= eps / &2}`
     ASSUME_TAC THENL
   [MATCH_MP_TAC PROB_MONO THEN
    ASM_SIMP_TAC[PROB_COMPL_IN_EVENTS] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      SUBSET_TRANS)) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
   (* prob(carrier \ C_{K1}) > 1/2 *)
   SUBGOAL_THEN `&1 / &2 < prob p (prob_carrier p DIFF
     (C_K:num->A->bool) K1)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `(C_K:num->A->bool) K1`]
     PROB_COMPL) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   (* Apply Chebyshev: prob({abs(sum Z) >= eps/2}) <= Var(sum Z) / (eps/2)^2 *)
   (* Need: Var(sum(m1..n1)(Z)) = sum(m1..n1)(Var(Z)) = sum(m1..n1)(Var(Y)) *)
   SUBGOAL_THEN `variance p (\x:A. sum(m1..n1)
     (\i. (Z:num->A->real) i x)) =
     sum(m1..n1) (\i. variance p (\x. Z i x))` ASSUME_TAC THENL
   [SUBGOAL_THEN `n1 = m1 + nn:num` (fun th -> REWRITE_TAC[th; SUM_REINDEX_SHIFT]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`p:A prob_space`;
      `\i (x:A). (Z:num->A->real) (m1 + i) x`; `nn:num`]
      VARIANCE_SUM_UNCORRELATED) THEN BETA_TAC THEN
    ANTS_TAC THENL
    [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun t ->
        try fst(dest_forall(concl t)) = `i:num` with _ -> false)) THEN
      UNDISCH_TAC `~(i:num = j)` THEN ARITH_TAC];
     SIMP_TAC[]];
    ALL_TAC] THEN
   SUBGOAL_THEN `sum(m1..n1) (\i. variance p (\x:A.
     (Z:num->A->real) i x)) =
     sum(m1..n1) (\i. variance p (\x. (Y:num->A->real) i x))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* The variance bound: sum(m1..n1)(Var(Y)) < (eps/2)^2 / 2 *)
   SUBGOAL_THEN `sum(m1..n1) (\i. variance p (\x:A.
     (Y:num->A->real) i x)) < (eps / &2) pow 2 / &2`
     ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `sum(K0..n1) (\i. variance p (\x:A.
      (Y:num->A->real) i x))` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
     REWRITE_TAC[FINITE_NUMSEG] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_NUMSEG] THEN
      UNDISCH_TAC `K0:num <= m1` THEN ARITH_TAC;
      REWRITE_TAC[IN_DIFF; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[]];
     SUBGOAL_THEN `n1 = K0 + (n1 - K0):num` SUBST1_TAC THENL
     [UNDISCH_TAC `K0:num <= m1` THEN UNDISCH_TAC `m1:num <= n1` THEN
      ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   (* E[sum Z] = 0 *)
   SUBGOAL_THEN `expectation p
     (\x:A. sum(m1..n1) (\i. (Z:num->A->real) i x)) = &0`
     (LABEL_TAC "EsumZ") THENL
   [SUBGOAL_THEN `n1 = m1 + nn:num`
      (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUM_REINDEX_SHIFT] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) EXPECTATION_SUM o
      lhand o snd) THEN
    ANTS_TAC THENL
    [REWRITE_TAC[IN_NUMSEG; LE_0] THEN GEN_TAC THEN DISCH_TAC THEN
     ASM_REWRITE_TAC[];
     DISCH_THEN SUBST1_TAC THEN
     MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN BETA_TAC THEN
     REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   (* integrable sum Z *)
   SUBGOAL_THEN `integrable p (\x:A. sum(m1..n1)
     (\i. (Z:num->A->real) i x))` (LABEL_TAC "IntSumZ") THENL
   [SUBGOAL_THEN `n1 = m1 + nn:num`
      (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUM_REINDEX_SHIFT] THEN
    MATCH_MP_TAC INTEGRABLE_SUM THEN
    REWRITE_TAC[IN_NUMSEG; LE_0] THEN GEN_TAC THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* Var(sum Z) / (eps/2)^2 < 1/2 *)
   SUBGOAL_THEN `variance p (\x:A. sum(m1..n1)
     (\i. (Z:num->A->real) i x)) / (eps / &2) pow 2 < &1 / &2`
     (LABEL_TAC "VarBound") THENL
   [SUBGOAL_THEN `&0 < (eps / &2) pow 2` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
    (* Goal: Var(sum Z) < 1/2 * (eps/2)^2 *)
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `(eps / &2) pow 2 / &2` THEN
    CONJ_TAC THENL
    [(* Var(sum Z) < (eps/2)^2/2 *)
     MATCH_MP_TAC REAL_LET_TRANS THEN
     EXISTS_TAC `sum(m1..n1) (\i. variance p (\x:A.
       (Y:num->A->real) i x))` THEN
     CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]];
     (* (eps/2)^2/2 <= 1/2 * (eps/2)^2 *)
     REAL_ARITH_TAC];
    ALL_TAC] THEN
   (* Set equality: sum Z = sum Z - E[sum Z] since E[sum Z] = 0 *)
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
     abs(sum(m1..n1) (\i. (Z:num->A->real) i x)) >= eps / &2} =
     {x | x IN prob_carrier p /\
       abs((\x. sum(m1..n1) (\i. Z i x)) x -
         expectation p (\x. sum(m1..n1) (\i. Z i x))) >=
           eps / &2}` (LABEL_TAC "SetEq") THENL
   [AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `x:A` THEN
    USE_THEN "EsumZ" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[REAL_SUB_RZERO];
    ALL_TAC] THEN
   (* integrable (sum Z - E[sum Z])^2 = integrable (sum Z)^2 *)
   SUBGOAL_THEN `integrable p (\x:A. ((\x. sum(m1..n1)
     (\i. (Z:num->A->real) i x)) x -
     expectation p (\x. sum(m1..n1) (\i. Z i x))) pow 2)`
     (LABEL_TAC "IntPow") THENL
   [USE_THEN "EsumZ" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[REAL_SUB_RZERO] THEN
    MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
    EXISTS_TAC `(&(nn + 1) * &2 * c) pow 2` THEN CONJ_TAC THENL
    [SUBGOAL_THEN `n1 = m1 + nn:num`
       (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     REWRITE_TAC[SUM_REINDEX_SHIFT] THEN
     MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
     MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN REPEAT STRIP_TAC THEN
     MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
     ASM_REWRITE_TAC[];
     GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
     MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `sum(m1..n1) (\i. abs((Z:num->A->real) i x))` THEN
     CONJ_TAC THENL
     [REWRITE_TAC[SUM_ABS_NUMSEG]; ALL_TAC] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `sum(m1..n1) (\i:num. &2 * c)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[];
      SUBGOAL_THEN `n1 = m1 + nn:num`
        (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[SUM_REINDEX_SHIFT; SUM_CONST_NUMSEG; SUB_0] THEN
      REAL_ARITH_TAC]];
    ALL_TAC] THEN
   (* Chebyshev: prob({abs(f) >= t}) <= Var(f) / t^2 *)
   SUBGOAL_THEN `prob p {x:A | x IN prob_carrier p /\
     abs(sum(m1..n1) (\i. (Z:num->A->real) i x)) >= eps / &2} < &1 / &2`
     ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `variance p (\x:A. sum(m1..n1)
      (\i. (Z:num->A->real) i x)) / (eps / &2) pow 2` THEN
    CONJ_TAC THENL
    [(* Chebyshev bound *)
     USE_THEN "SetEq" SUBST1_TAC THEN
     MATCH_MP_TAC CHEBYSHEV_INEQUALITY THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     REPEAT CONJ_TAC THENL
     [USE_THEN "IntSumZ" ACCEPT_TAC;
      USE_THEN "IntPow" (ACCEPT_TAC o BETA_RULE);
      MP_TAC(ASSUME `&0 < eps`) THEN REAL_ARITH_TAC];
     USE_THEN "VarBound" ACCEPT_TAC];
    ALL_TAC] THEN
   ASM_MESON_TAC[REAL_LTE_TRANS; REAL_LT_TRANS; REAL_LT_REFL]);;


let THREE_SERIES_NECESSITY_INDEP = prove
 (`!p:A prob_space (X:num->A->real) c.
    &0 < c /\
    (!n. integrable p (X n)) /\
    (!n. integrable p (\x. X n x pow 2)) /\
    mutually_indep_rv_seq p X /\
    indep_events_seq p (\n. {x | x IN prob_carrier p /\ abs(X n x) > c}) /\
    almost_surely p {x | ?L. ((\n. sum(0..n) (\i. X i x)) ---> L) sequentially}
    ==> real_summable (from 0)
          (\n. prob p {x | x IN prob_carrier p /\ abs(X n x) > c}) /\
        real_summable (from 0)
          (\n. expectation p (\x. min(max(X n x) (--c)) c)) /\
        real_summable (from 0)
          (\n. variance p (\x. min(max(X n x) (--c)) c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Phase 0: Setup -- abbreviations and basic facts *)
  ABBREV_TAC
    `(Y:num->A->real) n (x:A) = min(max((X:num->A->real) n x) (--c)) c` THEN
  ABBREV_TAC
    `(Z:num->A->real) n (x:A) =
       (Y:num->A->real) n x - expectation p (\y. Y n y)` THEN
  SUBGOAL_THEN `!n. random_variable p ((X:num->A->real) n)` ASSUME_TAC THENL
  [ASM_MESON_TAC[INTEGRABLE_IMP_RANDOM_VARIABLE]; ALL_TAC] THEN
  (* Phase 1: C1 -- tail probability summability (done early for stack safety) *)
  SUBGOAL_THEN `real_summable (from 0)
    (\n. prob p {x | x IN prob_carrier p /\ abs((X:num->A->real) n x) > c})`
    ASSUME_TAC THENL
  [MATCH_MP_TAC THREE_SERIES_CONDITION1 THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* a.s. convergence of sum Y (done early for stack safety) *)
  SUBGOAL_THEN `almost_surely p {x | ?L. ((\n. sum(0..n)
    (\i. (Y:num->A->real) i x)) ---> L) sequentially}` ASSUME_TAC THENL
  [PURE_REWRITE_TAC[GSYM(ASSUME `!n (x:A).
     min(max((X:num->A->real) n x) (--c)) c =
     (Y:num->A->real) n x`)] THEN
   MATCH_MP_TAC THREE_SERIES_REDUCTION THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n. integrable p (\x:A. (Y:num->A->real) n x)`
    ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_CURRY_TAC "Y" THEN
   MATCH_MP_TAC INTEGRABLE_CLAMP THEN REWRITE_TAC[ETA_AX] THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n (x:A). abs((Y:num->A->real) n x) <= c`
    ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN EXPAND_CURRY_TAC "Y" THEN
   REWRITE_TAC[real_max; real_min] THEN
   REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!n. integrable p (\x:A. (Y:num->A->real) n x pow 2)`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
   EXISTS_TAC `(c:real) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
    MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
   MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
   ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. abs(expectation p (\y:A. (Y:num->A->real) n y)) <= c`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `expectation p (\y:A. abs((Y:num->A->real) n y))` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC EXPECTATION_ABS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `expectation p (\y:A. c)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC EXPECTATION_MONO THEN CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_ABS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC] THEN
    GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[EXPECTATION_CONST; REAL_ABS_REFL] THEN
    ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `mutually_indep_rv_seq p (Y:num->A->real)` ASSUME_TAC THENL
  [SUBGOAL_THEN `(Y:num->A->real) =
    (\i x. min(max((X:num->A->real) i x) (--c)) c)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MUTUALLY_INDEP_RV_SEQ_CLAMP THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `mutually_indep_rv_seq p (Z:num->A->real)` ASSUME_TAC THENL
  [SUBGOAL_THEN `(Z:num->A->real) =
    (\i x. (Y:num->A->real) i x - expectation p (\y. Y i y))`
    SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MUTUALLY_INDEP_RV_SEQ_SHIFT_VARYING THEN
    ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. integrable p (\x:A. (Z:num->A->real) n x)`
    ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_CURRY_TAC "Z" THEN
   MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[INTEGRABLE_CONST];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n. expectation p (\x:A. (Z:num->A->real) n x) = &0`
    ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_CURRY_TAC "Z" THEN
   W(MP_TAC o PART_MATCH (lhand o rand) EXPECTATION_SUB o lhand o snd) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[EXPECTATION_CONST] THEN
   MATCH_MP_TAC(REAL_ARITH `a = b ==> a - b = &0`) THEN
   AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
    `!n (x:A). x IN prob_carrier p ==> abs((Z:num->A->real) n x) <= &2 * c`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN EXPAND_CURRY_TAC "Z" THEN
   MATCH_MP_TAC(REAL_ARITH
     `abs a <= c /\ abs b <= c ==> abs(a - b) <= &2 * c`) THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. integrable p (\x:A. (Z:num->A->real) n x pow 2)`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
   EXISTS_TAC `(&2 * c) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
    MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    ASM_SIMP_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `!i j. ~(i = j) ==>
    covariance p (\x:A. (Y:num->A->real) i x) (\x. Y j x) = &0`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC COVARIANCE_BOUNDED_INDEP THEN
   MAP_EVERY EXISTS_TAC [`c:real`; `c:real`] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN ASM_MESON_TAC[];
    GEN_TAC THEN DISCH_TAC THEN ASM_MESON_TAC[];
    SUBGOAL_THEN `(\x:A. (Y:num->A->real) i x) = Y i` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
    SUBGOAL_THEN `(\x:A. (Y:num->A->real) j x) = Y j` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
    UNDISCH_TAC `mutually_indep_rv_seq p (Y:num->A->real)` THEN
    DISCH_THEN(MP_TAC o MATCH_MP MUTUALLY_INDEP_RV_SEQ_PAIRWISE) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. &0 <= variance p (\x:A. (Y:num->A->real) n x)`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC VARIANCE_NONNEG THEN
   SUBGOAL_THEN `(\x:A. ((Y:num->A->real) n x -
     expectation p (\y. Y n y)) pow 2) = (\x. Z n x pow 2)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. variance p (\x:A. sum(0..n)
    (\i. (Y:num->A->real) i x)) =
    sum(0..n) (\i. variance p (\x. Y i x))` ASSUME_TAC THENL
  [GEN_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `\i (x:A). (Y:num->A->real) i x`; `n:num`]
     VARIANCE_SUM_UNCORRELATED) THEN BETA_TAC THEN
   ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
    [GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
     GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
     ASM_MESON_TAC[]];
    SIMP_TAC[]]; ALL_TAC] THEN
  (* Phase 2: C3 -- variance summability *)
  SUBGOAL_THEN `real_summable (from 0)
    (\n. variance p (\x:A. (Y:num->A->real) n x))` ASSUME_TAC THENL
  [ASM_CASES_TAC `!N. sum(0..N) (\i. variance p (\x:A.
     (Y:num->A->real) i x)) < (&2 * c) pow 2` THENL
   [(* Case A: partial sums bounded, use REAL_SUMMABLE_BOUND_PARTIAL *)
    MATCH_MP_TAC REAL_SUMMABLE_BOUND_PARTIAL THEN
    EXISTS_TAC `(&2 * c) pow 2` THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
    (* Case B: partial sums reach (2c)^2, use V2 *)
    POP_ASSUM MP_TAC THEN REWRITE_TAC[NOT_FORALL_THM; REAL_NOT_LT] THEN
    DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN
    MP_TAC(ISPECL [`p:A prob_space`; `Y:num->A->real`; `&32`]
      SUMMABLE_VARIANCE_FROM_CONVERGENCE_V2) THEN
    ANTS_TAC THENL
    [CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
     CONJ_TAC THENL
     [GEN_TAC THEN
      ONCE_REWRITE_TAC[GSYM(ISPEC `(Y:num->A->real) n` ETA_AX)] THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
     CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      ONCE_REWRITE_TAC[GSYM(ISPEC `(Y:num->A->real) i` ETA_AX)] THEN
      ONCE_REWRITE_TAC[GSYM(ISPEC `(Y:num->A->real) j` ETA_AX)] THEN
      ASM_SIMP_TAC[]; ALL_TAC] THEN
     (* integrable (sum Y)^2 and (sum Y)^4 *)
     SUBGOAL_THEN `!n (x:A). abs(sum(0..n) (\i. (Y:num->A->real) i x)) <=
       &(n + 1) * c` ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum(0..n) (\i. abs((Y:num->A->real) i x))` THEN
      CONJ_TAC THENL [REWRITE_TAC[SUM_ABS_NUMSEG]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum(0..n) (\i:num. c)` THEN CONJ_TAC THENL
      [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
       ASM_REWRITE_TAC[];
       REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
     SUBGOAL_THEN `!n. random_variable p
       (\x:A. sum(0..n) (\i. (Y:num->A->real) i x))` ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN
      GEN_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `(Y:num->A->real) i = (\x:A. Y i x)` SUBST1_TAC THENL
      [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
      MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
     CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
      EXISTS_TAC `(&(n + 1) * c) pow 2` THEN CONJ_TAC THENL
      [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN ASM_REWRITE_TAC[];
       GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
       MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
       ASM_REWRITE_TAC[]]; ALL_TAC] THEN
     CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
      EXISTS_TAC `(&(n + 1) * c) pow 4` THEN CONJ_TAC THENL
      [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN ASM_REWRITE_TAC[];
       GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
       MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
       ASM_REWRITE_TAC[]]; ALL_TAC] THEN
     CONJ_TAC THENL
     [ALL_TAC; ASM_REWRITE_TAC[]] THEN
     (* Fourth moment bound: exists N0 s.t. for n >= N0,
        E[(sum Y)^4] <= 32 * E[(sum Y)^2]^2 *)
     EXISTS_TAC `N0:num` THEN GEN_TAC THEN DISCH_TAC THEN
     ABBREV_TAC
       `(T_n:A->real) (x:A) = sum(0..n) (\i. (Z:num->A->real) i x)` THEN
     ABBREV_TAC
       `M_n = sum(0..n) (\i. expectation p (\y:A. (Y:num->A->real) i y))` THEN
     SUBGOAL_THEN `!x:A. sum(0..n) (\i. (Y:num->A->real) i x) =
       (T_n:A->real) x + M_n` ASSUME_TAC THENL
     [GEN_TAC THEN EXPAND_CURRY_TAC "T_n" THEN EXPAND_TAC "M_n" THEN
      EXPAND_CURRY_TAC "Z" THEN
      REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
     SUBGOAL_THEN `!n (x:A). abs((Z:num->A->real) n x) <= &2 * c`
       ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN EXPAND_CURRY_TAC "Z" THEN
      MATCH_MP_TAC(REAL_ARITH
        `abs a <= c /\ abs b <= c ==> abs(a - b) <= &2 * c`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
     SUBGOAL_THEN `integrable p (\x:A. (T_n:A->real) x)` ASSUME_TAC THENL
     [EXPAND_CURRY_TAC "T_n" THEN
      MATCH_MP_TAC INTEGRABLE_SUM THEN
      REWRITE_TAC[IN_NUMSEG; LE_0] THEN GEN_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `(Z:num->A->real) i = (\x. Z i x)` SUBST1_TAC THENL
      [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
     SUBGOAL_THEN `expectation p (\x:A. (T_n:A->real) x) = &0`
       ASSUME_TAC THENL
     [EXPAND_CURRY_TAC "T_n" THEN
      W(MP_TAC o PART_MATCH (lhand o rand) EXPECTATION_SUM o lhand o snd) THEN
      ANTS_TAC THENL
      [REWRITE_TAC[IN_NUMSEG; LE_0] THEN GEN_TAC THEN DISCH_TAC THEN
       SUBGOAL_THEN `(Z:num->A->real) i = (\x. Z i x)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
       ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN BETA_TAC THEN
      GEN_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `(Z:num->A->real) i = (\x. Z i x)` SUBST1_TAC THENL
      [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
     SUBGOAL_THEN `integrable p (\x:A. (T_n:A->real) x pow 2)`
       ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
      EXISTS_TAC `(&(n + 1) * &2 * c) pow 2` THEN
      CONJ_TAC THENL
      [EXPAND_CURRY_TAC "T_n" THEN
       MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
       MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN
       GEN_TAC THEN DISCH_TAC THEN
       SUBGOAL_THEN `(Z:num->A->real) i = (\x. Z i x)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
       MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
       ASM_REWRITE_TAC[]; ALL_TAC] THEN
      GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum(0..n) (\i. abs((Z:num->A->real) i x))` THEN
      CONJ_TAC THENL
      [EXPAND_CURRY_TAC "T_n" THEN REWRITE_TAC[SUM_ABS_NUMSEG];
       ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum(0..n) (\i:num. &2 * c)` THEN CONJ_TAC THENL
      [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
       ASM_REWRITE_TAC[];
       REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
     SUBGOAL_THEN `integrable p (\x:A. &2 * (T_n:A->real) x * M_n)`
       ASSUME_TAC THENL
     [SUBGOAL_THEN `(\x:A. &2 * (T_n:A->real) x * M_n) =
       (\x. (&2 * M_n) * T_n x)` SUBST1_TAC THENL
      [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
       ALL_TAC] THEN
      MATCH_MP_TAC INTEGRABLE_CMUL THEN
      SUBGOAL_THEN `(T_n:A->real) = (\x:A. T_n x)` SUBST1_TAC THENL
      [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
     SUBGOAL_THEN `integrable p (\x:A. (T_n:A->real) x pow 4)`
       ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
      EXISTS_TAC `(&(n + 1) * &2 * c) pow 4` THEN
      CONJ_TAC THENL
      [EXPAND_CURRY_TAC "T_n" THEN
       MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
       MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN
       GEN_TAC THEN DISCH_TAC THEN
       SUBGOAL_THEN `(Z:num->A->real) i = (\x. Z i x)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
       MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
       ASM_REWRITE_TAC[]; ALL_TAC] THEN
      GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum(0..n) (\i. abs((Z:num->A->real) i x))` THEN
      CONJ_TAC THENL
      [EXPAND_CURRY_TAC "T_n" THEN REWRITE_TAC[SUM_ABS_NUMSEG];
       ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum(0..n) (\i:num. &2 * c)` THEN CONJ_TAC THENL
      [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
       ASM_REWRITE_TAC[];
       REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
     SUBGOAL_THEN `&0 <= expectation p (\x:A. (T_n:A->real) x pow 2)`
       ASSUME_TAC THENL
     [MATCH_MP_TAC EXPECTATION_POS THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      ALL_TAC] THEN
     (* Fourth moment bound for T_n from FOURTH_MOMENT_BOUND_INDEP_CENTERED *)
     SUBGOAL_THEN `expectation p (\x:A. (T_n:A->real) x pow 4) <=
       (&2 * c) pow 2 * expectation p (\x. T_n x pow 2) +
       &3 * expectation p (\x. T_n x pow 2) pow 2` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`p:A prob_space`; `Z:num->A->real`; `&2 * c`]
       FOURTH_MOMENT_BOUND_INDEP_CENTERED) THEN
      ANTS_TAC THENL
      [REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC;
        GEN_TAC THEN
        ONCE_REWRITE_TAC[GSYM(ISPEC `(Z:num->A->real) i` ETA_AX)] THEN
        ASM_REWRITE_TAC[];
        GEN_TAC THEN
        ONCE_REWRITE_TAC[GSYM(ISPEC `(Z:num->A->real) i` ETA_AX)] THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
      SUBGOAL_THEN `(\x:A. sum(0..n) (\i. (Z:num->A->real) i x) pow 4) =
        (\x. (T_n:A->real) x pow 4)` SUBST1_TAC THENL
      [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
      SUBGOAL_THEN `(\x:A. sum(0..n) (\i. (Z:num->A->real) i x) pow 2) =
        (\x. (T_n:A->real) x pow 2)` SUBST1_TAC THENL
      [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
      SIMP_TAC[];
      ALL_TAC] THEN
     (* Key: (2c)^2 <= E[T_n^2] because sum Var(Y) >= (2c)^2 for n >= N0 *)
     SUBGOAL_THEN `(&2 * c) pow 2 <= expectation p
       (\x:A. (T_n:A->real) x pow 2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum(0..n) (\i. variance p (\x:A. (Y:num->A->real) i x))` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_TRANS THEN
       EXISTS_TAC
         `sum(0..N0) (\i. variance p (\x:A. (Y:num->A->real) i x))` THEN
       ASM_REWRITE_TAC[] THEN
       SUBGOAL_THEN `sum(0..N0) (\i. variance p (\x:A.
           (Y:num->A->real) i x)) +
         sum(N0+1..n) (\i. variance p (\x. Y i x)) =
         sum(0..n) (\i. variance p (\x. Y i x))` (fun th ->
           GEN_REWRITE_TAC RAND_CONV [GSYM th]) THENL
       [MATCH_MP_TAC SUM_COMBINE_R THEN ASM_ARITH_TAC; ALL_TAC] THEN
       MATCH_MP_TAC(REAL_ARITH `&0 <= b ==> a <= a + b`) THEN
       MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
      SUBGOAL_THEN `sum(0..n) (\i. variance p (\x:A.
         (Y:num->A->real) i x)) =
        expectation p (\x. (T_n:A->real) x pow 2)` SUBST1_TAC THENL
      [ONCE_REWRITE_TAC[GSYM(ASSUME `!n. variance p (\x:A. sum(0..n)
          (\i. (Y:num->A->real) i x)) =
          sum(0..n) (\i. variance p (\x. Y i x))`)] THEN
       (* variance(sum Y) = E[(sum Y - E[sum Y])^2] *)
       REWRITE_TAC[variance] THEN
       (* E[sum Y] = M_n *)
       SUBGOAL_THEN `expectation p (\y:A. sum(0..n)
         (\i. (Y:num->A->real) i y)) = M_n` SUBST1_TAC THENL
       [W(MP_TAC o PART_MATCH (lhand o rand) EXPECTATION_SUM o
          lhand o snd) THEN
        ANTS_TAC THENL
        [REWRITE_TAC[IN_NUMSEG; LE_0] THEN GEN_TAC THEN DISCH_TAC THEN
         SUBGOAL_THEN `(Y:num->A->real) i = (\x. Y i x)` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN ASM_REWRITE_TAC[];
         ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN
        SUBGOAL_THEN `!i. expectation p ((Y:num->A->real) i) =
          expectation p (\y:A. Y i y)`
          (fun th -> REWRITE_TAC[th]) THENL
        [GEN_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
       (* sum Y x - M_n = T_n x *)
       AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
       AP_THM_TAC THEN AP_TERM_TAC THEN ASM_REWRITE_TAC[] THEN
       REAL_ARITH_TAC;
       REAL_ARITH_TAC];
      ALL_TAC] THEN
     (* So E[T_n^4] <= (2c)^2 * E[T_n^2] + 3 * E[T_n^2]^2
        <= E[T_n^2] * E[T_n^2] + 3 * E[T_n^2]^2 = 4 * E[T_n^2]^2 *)
     SUBGOAL_THEN `expectation p (\x:A. (T_n:A->real) x pow 4) <=
       &4 * expectation p (\x. T_n x pow 2) pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&2 * c) pow 2 * expectation p
        (\x:A. (T_n:A->real) x pow 2) +
        &3 * expectation p (\x. T_n x pow 2) pow 2` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `expectation p (\x:A. (T_n:A->real) x pow 2) *
        expectation p (\x. T_n x pow 2) +
        &3 * expectation p (\x. T_n x pow 2) pow 2` THEN
      CONJ_TAC THENL
      [ONCE_REWRITE_TAC[REAL_LE_RADD] THEN
       MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
       REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
     (* E[2*T_n*M_n] = 0 *)
     SUBGOAL_THEN `expectation p (\x:A. &2 * (T_n:A->real) x * M_n) = &0`
       ASSUME_TAC THENL
     [SUBGOAL_THEN `(\x:A. &2 * (T_n:A->real) x * M_n) =
       (\x. (&2 * M_n) * T_n x)` SUBST1_TAC THENL
      [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
       ALL_TAC] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) EXPECTATION_CMUL o
        lhand o snd) THEN
      ANTS_TAC THENL
      [SUBGOAL_THEN `(T_n:A->real) = (\x:A. T_n x)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `expectation p (T_n:A->real) =
        expectation p (\x:A. T_n x)` SUBST1_TAC THENL
      [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
     (* E[(sum Y)^2] = E[T_n^2] + M_n^2 *)
     SUBGOAL_THEN `expectation p
       (\x:A. sum(0..n) (\i. (Y:num->A->real) i x) pow 2) =
       expectation p (\x. (T_n:A->real) x pow 2) + M_n pow 2`
       SUBST1_TAC THENL
     [SUBGOAL_THEN `(\x:A. sum(0..n) (\i. (Y:num->A->real) i x) pow 2) =
       (\x. (T_n:A->real) x pow 2 + &2 * T_n x * M_n + M_n pow 2)`
       SUBST1_TAC THENL
      [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN ASM_REWRITE_TAC[] THEN
       REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) EXPECTATION_ADD o
        lhand o snd) THEN
      ANTS_TAC THENL
      [CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        MATCH_MP_TAC INTEGRABLE_ADD THEN
        ASM_REWRITE_TAC[INTEGRABLE_CONST]];
       ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      W(MP_TAC o PART_MATCH (lhand o rand) EXPECTATION_ADD o
        rand o lhand o snd) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[EXPECTATION_CONST] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
     (* (a+b)^4 <= 8*(a^4+b^4) *)
     SUBGOAL_THEN `!(a:real) b. (a + b) pow 4 <= &8 * (a pow 4 + b pow 4)`
       ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&2 * (a pow 2 + b pow 2)) pow 2` THEN CONJ_TAC THENL
      [SUBGOAL_THEN `(a + b:real) pow 4 = ((a + b) pow 2) pow 2`
         SUBST1_TAC THENL
       [REWRITE_TAC[REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC] THEN
       MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
       MP_TAC(SPEC `a - b:real` REAL_LE_POW_2) THEN
       REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPEC `(a:real) pow 2 - b pow 2` REAL_LE_POW_2) THEN
      REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
     (* Main chain: E[(sum Y)^4] = E[(T_n + M_n)^4]
        <= 8*(E[T_n^4] + M_n^4) <= 8*(4*E[T_n^2]^2 + M_n^4)
        = 32*E[T_n^2]^2 + 8*M_n^4
        <= 32*(E[T_n^2] + M_n^2)^2 = 32*E[(sum Y)^2]^2 *)
     ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `&8 *
       (expectation p (\x:A. (T_n:A->real) x pow 4) + M_n pow 4)` THEN
     CONJ_TAC THENL
     [SUBGOAL_THEN `expectation p
        (\x:A. &8 * ((T_n:A->real) x pow 4 + M_n pow 4)) =
        &8 * (expectation p (\x. T_n x pow 4) + M_n pow 4)`
        ASSUME_TAC THENL
      [W(MP_TAC o PART_MATCH (lhand o rand) EXPECTATION_CMUL o
         lhand o snd) THEN
       ANTS_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_ADD THEN
        ASM_REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC] THEN
       DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
       W(MP_TAC o PART_MATCH (lhand o rand) EXPECTATION_ADD o
         lhand o snd) THEN
       ANTS_TAC THENL
       [ASM_REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC] THEN
       DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[EXPECTATION_CONST];
       ALL_TAC] THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
      MATCH_MP_TAC EXPECTATION_MONO THEN
      REPEAT CONJ_TAC THENL
      [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
       EXISTS_TAC `(&(n + 1) * c) pow 4` THEN CONJ_TAC THENL
       [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
        SUBGOAL_THEN `(\x:A. (T_n:A->real) x + M_n) =
          (\x. sum(0..n) (\i. (Y:num->A->real) i x))` SUBST1_TAC THENL
        [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
         CONV_TAC SYM_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        ASM_REWRITE_TAC[];
        X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
        REWRITE_TAC[REAL_ABS_POW] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
        [REWRITE_TAC[REAL_ABS_POS];
         SUBGOAL_THEN `(T_n:A->real) (x:A) + M_n =
           sum(0..n) (\i. (Y:num->A->real) i x)` SUBST1_TAC THENL
         [CONV_TAC SYM_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
         ASM_REWRITE_TAC[]]];
       MATCH_MP_TAC INTEGRABLE_CMUL THEN
       MATCH_MP_TAC INTEGRABLE_ADD THEN
       ASM_REWRITE_TAC[INTEGRABLE_CONST];
       GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `&8 *
       (&4 * expectation p (\x:A. (T_n:A->real) x pow 2) pow 2 +
        M_n pow 4)` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
      [REAL_ARITH_TAC; ALL_TAC] THEN
      ONCE_REWRITE_TAC[REAL_LE_RADD] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
     SUBGOAL_THEN `(M_n:real) pow 4 = (M_n pow 2) pow 2`
       SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
     SUBGOAL_THEN `&0 <= &2 * expectation p
       (\x:A. (T_n:A->real) x pow 2) * (M_n:real) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
      [REAL_ARITH_TAC;
       MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]];
      ALL_TAC] THEN
     SUBGOAL_THEN `&0 <= (M_n:real) pow 2 * M_n pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2];
      ALL_TAC] THEN
     REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
    SIMP_TAC[ETA_AX]]; ALL_TAC] THEN
  (* Phase 3: C2 -- expectation summability *)
  SUBGOAL_THEN `real_summable (from 0)
    (\n. expectation p (\x:A. (Y:num->A->real) n x))` ASSUME_TAC THENL
  [MATCH_MP_TAC(ISPECL [`p:A prob_space`; `Y:num->A->real`;
     `Z:num->A->real`; `c:real`] EXPECTATION_SUMMABLE_CHEBYSHEV) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Phase 4: Combine C1, C2, C3 *)
  SUBGOAL_THEN `!n (x:A). min(max((X:num->A->real) n x) (--c)) c =
    (Y:num->A->real) n x` (fun th -> REWRITE_TAC[th]) THENL
  [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;
