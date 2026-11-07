(* ========================================================================= *)
(* Two logarithms, the Laurent bound: the numeric layer.                     *)
(*                                                                           *)
(* Purpose: the parameter theorem behind M. Laurent, Linear forms in two     *)
(* logarithms and interpolation determinants II, Acta Arith. 133 (2008),     *)
(* Theorem 2 at mu = 1, for any degree D: under the hypotheses of Theorem 2  *)
(* (with h >= 10) there are parameters K, L, R1, S1, R2, S2 satisfying the   *)
(* grid conditions of Theorem 1 and the main inequality laurent_main, with   *)
(* the size bounds needed for the step from Lambda prime to Lambda and for   *)
(* the collision cases. Also a lower bound for the sum of log j! for j < K   *)
(* (D. Lombardo, Interpolation determinants and the Lebesgue-Nagell          *)
(* equation, arXiv 2609.23899 (2026), Lemma 3.7).                            *)
(*                                                                           *)
(* Route: with m = (V/U) sqrt(L a1 a2) the parameter k of LAURENT_PARAM_MAIN *)
(* gives K > m^2 + 2 m + w with w = (V/U)(a1 + a2) >= 0, hence               *)
(* m (1 + sqrt(K-1)) < K, and the binomial size X = (R-1) b2 + (S-1) b1      *)
(* satisfies X < K lam bb 3 (L - H) / L (lam = log rho, bb = b1/a2 + b2/a1). *)
(* With the Lombardo sum bound and the height hypothesis the main inequality *)
(* laurent_main reduces to Pnew <= 0, Pnew = (2/N) log N! +                  *)
(* (K-1)(kap + 3/2 - c) + (K-1)/K (log K + 1/2),                             *)
(* kap = log(3 (L - H) / (2 L)) <= -0.23, independently of D. Pnew <= 0 is a *)
(* linear chain (LOG_FACT_BOUNDS and tangent lines of log) in the two        *)
(* regimes c = 5/2 (a1 a2 >= lam^2) and c = 3/2 (a_i >= rho + 1).            *)
(*                                                                           *)
(* Main results: LAURENT_PARAMETERS (regime a_i >= 1, a1 a2 >= (log rho)^2,  *)
(* height threshold 5/2), LAURENT_PARAMETERS_LARGE (regime a_i >= rho + 1,   *)
(* threshold 3/2), LOMBARDO_LOGFACT_SUM; helper names LAURENT_PB_*.          *)
(*                                                                           *)
(* Uses: Baker/laurent_param_main.ml (LAURENT_PARAM_MAIN),                   *)
(* Baker/laurent_defs.ml (laurent_main), Baker/laurent_glemma.ml             *)
(* (GLEMMA_SUM_ID), Baker/twolog.ml (LOG_LE_SUB_1), Baker/twolog_param.ml    *)
(* (LOG_LE_EXP, EXP_NUM_GE_POW), Baker/lemmas.ml (LOG_2_LE_1,                *)
(* LOG_SUC_SUB_LE_INV), LOG_FACT_BOUNDS of Examples/mangoldt.ml.             *)
(* ========================================================================= *)

needs "Baker/twolog.ml";;
needs "Baker/laurent_glemma.ml";;
needs "Baker/laurent_param_main.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* 1. Numerical constants.                                                   *)
(* ------------------------------------------------------------------------- *)

let LAURENT_PB_LOG_LE_TANGENT = prove
 (`!x y c. &0 < x /\ &0 < c /\ c <= exp y ==> log x <= y - &1 + x / c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `y:real`] LOG_LE_EXP) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a <= b ==> l <= (y:real) - &1 + a ==> l <= y - &1 + b`) THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV2]);;

let LAURENT_PB_LOG_LE_E2 = prove
 (`!x. &0 < x ==> log x <= &1 + x * &1000 / &7389`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `&2`; `&7389 / &1000`] LAURENT_PB_LOG_LE_TANGENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `2` EXP_NUM_GE_POW) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let LAURENT_PB_LOG_LE_E4 = prove
 (`!x. &0 < x ==> log x <= &3 + x * &1000 / &54597`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `&4`; `&54597 / &1000`]
    LAURENT_PB_LOG_LE_TANGENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `4` EXP_NUM_GE_POW) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let LAURENT_PB_LOG_8 = prove
 (`log(&8) <= &21 / &10`,
  MP_TAC(SPEC `&8` LAURENT_PB_LOG_LE_E2) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let LAURENT_PB_LOG_15_19 = prove
 (`!y. &0 < y /\ y <= &15 / &19 ==> log y <= --(&23 / &100)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `exp(&23 / &100) <= &19 / &15` ASSUME_TAC THENL
   [SUBGOAL_THEN `exp(&23 / &100) = exp(&23 / &1000) pow 10` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_N] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1000 / &977) pow 10` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      SUBGOAL_THEN `&1000 / &977 = inv(&1 + --(&23 / &1000))` SUBST1_TAC
      THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC[GSYM REAL_EXP_NEG; REAL_EXP_LE_X] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  MP_TAC(SPECL [`y:real`; `--(&23 / &100)`] LOG_LE_EXP) THEN
  ASM_REWRITE_TAC[REAL_EXP_NEG; real_div; REAL_INV_INV] THEN
  MATCH_MP_TAC(REAL_ARITH
   `y * e <= &1
    ==> l <= --(&23 * inv(&100)) - &1 + y * e
    ==> l <= --(&23 * inv(&100))`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&15 / &19 * &19 / &15` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_EXP_POS_LE; GSYM real_div];
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

let LAURENT_PB_RHO_LOG = prove
 (`!rho. &4 <= rho ==> &7 / &2 * log rho <= rho + &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&448 / &100 <= exp(&3 / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
    REWRITE_TAC[ARITH_EQ; REAL_EXP_POS_LE; GSYM REAL_EXP_N] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MP_TAC(SPEC `3` EXP_NUM_GE_POW) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`rho:real`; `&3 / &2`; `&448 / &100`]
    LAURENT_PB_LOG_LE_TANGENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&4 <= rho` THEN REAL_ARITH_TAC;
    UNDISCH_TAC `&4 <= rho` THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 2. Lombardo, Lemma 3.7: sum of log j! for j < K (telescoping proof).      *)
(* ------------------------------------------------------------------------- *)

let LAURENT_PB_LOG_FACT_GE = prove
 (`!j. &j * log(&j) - &j <= log(&(FACT j))`,
  INDUCT_TAC THENL
   [REWRITE_TAC[FACT; LOG_1; REAL_MUL_LZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[FACT; GSYM REAL_OF_NUM_MUL] THEN
  SIMP_TAC[LOG_MUL; REAL_OF_NUM_LT; FACT_LT; LT_0] THEN
  SUBGOAL_THEN `&j * (log(&(SUC j)) - log(&j)) <= &1` MP_TAC THENL
   [ASM_CASES_TAC `j = 0` THENL
     [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_POS]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &j` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `&j` LOG_SUC_SUB_LE_INV) THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_SUC] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&j * inv(&j)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_LE_REFL]];
    ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  REAL_ARITH_TAC);;

let LAURENT_PB_SUM_NLOGN_GE = prove
 (`!n. 1 <= n
       ==> &n pow 2 / &2 * log(&n) - &n pow 2 / &4 + &1 / &4
           <= sum(1..n) (\j. &j * log(&j))`,
  INDUCT_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[GSYM ONE; SUM_SING_NUMSEG; LOG_1] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&n pow 2 * (log(&n + &1) - log(&n)) <= &n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&n pow 2 * inv(&n)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[LOG_SUC_SUB_LE_INV; REAL_POW_LE; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < &n` THEN
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&n + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN ASM_REAL_ARITH_TAC);;

let LAURENT_PB_LOG_PRED = prove
 (`!K. 2 <= K ==> log(&K) <= log(&K - &1) + inv(&K - &1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `&K - &1` LOG_SUC_SUB_LE_INV) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `2 <= K` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[REAL_SUB_ADD] THEN REAL_ARITH_TAC]);;

let LOMBARDO_LOGFACT_SUM = prove
 (`!K. 3 <= K
       ==> &K * (&K - &1) / &2 * (log(&K) - &3 / &2) -
           (&K - &1) / &2 * (log(&K) + &1 / &2)
           <= sum(1..K - 1) (\j. log(&(FACT j)))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..K - 1) (\j. &j * log(&j) - &j)` THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SUM_LE_NUMSEG THEN REWRITE_TAC[LAURENT_PB_LOG_FACT_GE]] THEN
  REWRITE_TAC[SUM_SUB_NUMSEG] THEN
  REWRITE_TAC[REWRITE_RULE[ETA_AX] GLEMMA_SUM_ID] THEN
  MP_TAC(SPEC `K - 1` LAURENT_PB_SUM_NLOGN_GE) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE `3 <= K ==> 1 <= K`] THEN
  SUBGOAL_THEN `&2 <= &K - &1` ASSUME_TAC THENL
   [UNDISCH_TAC `3 <= K` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&K - &1) pow 2 * log(&K) - (&K - &1) <= (&K - &1) pow 2 * log(&K - &1)`
  MP_TAC THENL
   [MP_TAC(SPEC `K:num` LAURENT_PB_LOG_PRED) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN
     `(&K - &1) pow 2 * log(&K) <=
      (&K - &1) pow 2 * (log(&K - &1) + inv(&K - &1))`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      ALL_TAC] THEN
    SUBGOAL_THEN `(&K - &1) pow 2 * inv(&K - &1) = &K - &1` MP_TAC THENL
     [UNDISCH_TAC `&2 <= &K - &1` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 3. The lower-order residual Pnew is negative (two regimes).               *)
(* ------------------------------------------------------------------------- *)

let LAURENT_PB_LOGFACT_DIV = prove
 (`!N e. 1 <= N /\ &4 <= e * &N
         ==> &2 / &N * log(&(FACT N)) <= (&2 + e) * log(&N) - &2 + e / &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &N` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &N` ASSUME_TAC THENL
   [UNDISCH_TAC `&1 <= &N` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `N:num` LOG_FACT_BOUNDS) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `abs(f - (n * l - n + &1)) <= &2 * l ==> f <= n * l - n + &1 + &2 * l`)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&4 / &N <= e` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `&4 / &N * log(&N) <= e * log(&N)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[LOG_POS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 / &N * (&N * log(&N) - &N + &1 + &2 * log(&N))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN UNDISCH_TAC `&0 < &N` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 / &N * (&N * log(&N) - &N + &1 + &2 * log(&N)) =
    &2 * log(&N) - &2 + (&4 / &N) / &2 + &4 / &N * log(&N)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < &N` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  UNDISCH_TAC `&4 / &N * log(&N) <= e * log(&N)` THEN
  UNDISCH_TAC `&4 / &N <= e` THEN REAL_ARITH_TAC);;

let LAURENT_PB_PRED_DIV_LE = prove
 (`!K y. 1 <= K /\ &0 <= y ==> (&K - &1) / &K * y <= y`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < &K` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC);;

let LAURENT_PB_PNEW_A = prove
 (`!K L kap.
     12 <= L /\
     (&19 / &30) pow 2 * &L + &2 * (&19 / &30) * sqrt(&L) + &2 * (&19 / &30)
     < &K /\
     kap <= --(&23 / &100)
     ==> &2 / &(K * L) * log(&(FACT(K * L))) +
         (&K - &1) * (kap + &3 / &2 - &5 / &2) +
         (&K - &1) / &K * (log(&K) + &1 / &2) <= &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&12 <= &L` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&3464 / &1000 <= sqrt(&L)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN UNDISCH_TAC `&12 <= &L` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&361 / &900 * &L + &565 / &100 < &K` ASSUME_TAC THENL
   [UNDISCH_TAC `&3464 / &1000 <= sqrt(&L)` THEN
    UNDISCH_TAC
     `(&19 / &30) pow 2 * &L + &2 * (&19 / &30) * sqrt(&L) + &2 * (&19 / &30)
      < &K` THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `11 <= K` ASSUME_TAC THENL
   [SUBGOAL_THEN `&10 < &K` MP_TAC THENL
     [UNDISCH_TAC `&361 / &900 * &L + &565 / &100 < &K` THEN
      UNDISCH_TAC `&12 <= &L` THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`K * L`; `&1 / &33`] LAURENT_PB_LOGFACT_DIV) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `1 * 1 <= K * L ==> 1 <= K * L`) THEN
      MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `132 <= K * L` MP_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `11 * 12 <= K * L ==> 132 <= K * L`) THEN
      MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&(K * L)) = log(&K) + log(&L)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN MATCH_MP_TAC LOG_MUL THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `log(&K) <= &1 + &K * &1000 / &7389 /\ log(&L) <= &1 + &L * &1000 / &7389`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LAURENT_PB_LOG_LE_E2 THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&K - &1) / &K * (log(&K) + &1 / &2) <= log(&K) + &1 / &2`
  MP_TAC THENL
   [MATCH_MP_TAC LAURENT_PB_PRED_DIV_LE THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= x + &1 / &2`) THEN
    MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&K - &1) * (kap + &3 / &2 - &5 / &2) <=
    (&K - &1) * (--(&23 / &100) + &3 / &2 - &5 / &2)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_SUB_LE; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      UNDISCH_TAC `kap <= --(&23 / &100)` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&11 <= &K` MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  UNDISCH_TAC `&361 / &900 * &L + &565 / &100 < &K` THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REAL_ARITH_TAC);;

let LAURENT_PB_PNEW_B = prove
 (`!K L kap.
     12 <= L /\
     (&133 / &60) pow 2 * &L + &2 * (&133 / &60) * sqrt(&L) +
     &2 * (&133 / &60) < &K /\
     kap <= --(&23 / &100)
     ==> &2 / &(K * L) * log(&(FACT(K * L))) +
         (&K - &1) * (kap + &3 / &2 - &3 / &2) +
         (&K - &1) / &K * (log(&K) + &1 / &2) <= &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&12 <= &L` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&3464 / &1000 <= sqrt(&L)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN UNDISCH_TAC `&12 <= &L` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&4913 / &1000 * &L + &1979 / &100 < &K` ASSUME_TAC THENL
   [UNDISCH_TAC `&3464 / &1000 <= sqrt(&L)` THEN
    UNDISCH_TAC
     `(&133 / &60) pow 2 * &L + &2 * (&133 / &60) * sqrt(&L) +
      &2 * (&133 / &60) < &K` THEN
    UNDISCH_TAC `&12 <= &L` THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `79 <= K` ASSUME_TAC THENL
   [SUBGOAL_THEN `&78 < &K` MP_TAC THENL
     [UNDISCH_TAC `&4913 / &1000 * &L + &1979 / &100 < &K` THEN
      UNDISCH_TAC `&12 <= &L` THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`K * L`; `&1 / &237`] LAURENT_PB_LOGFACT_DIV) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `1 * 1 <= K * L ==> 1 <= K * L`) THEN
      MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `948 <= K * L` MP_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `79 * 12 <= K * L ==> 948 <= K * L`) THEN
      MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&(K * L)) = log(&K) + log(&L)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN MATCH_MP_TAC LOG_MUL THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `log(&K) <= &3 + &K * &1000 / &54597 /\
    log(&L) <= &1 + &L * &1000 / &7389`
  MP_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LAURENT_PB_LOG_LE_E4; MATCH_MP_TAC LAURENT_PB_LOG_LE_E2] THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&K - &1) / &K * (log(&K) + &1 / &2) <= log(&K) + &1 / &2`
  MP_TAC THENL
   [MATCH_MP_TAC LAURENT_PB_PRED_DIV_LE THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= x + &1 / &2`) THEN
    MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&K - &1) * (kap + &3 / &2 - &3 / &2) <=
    (&K - &1) * (--(&23 / &100) + &3 / &2 - &3 / &2)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_SUB_LE; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      UNDISCH_TAC `kap <= --(&23 / &100)` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&79 <= &K` MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  UNDISCH_TAC `&4913 / &1000 * &L + &1979 / &100 < &K` THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 4. The b-estimate: X (V/U) < K bb from K > m^2 + 2 m.                     *)
(* ------------------------------------------------------------------------- *)

let LAURENT_PB_MT = prove
 (`!m t. &0 <= m /\ &0 <= t /\ m pow 2 + &2 * m < t pow 2 + &1
         ==> m * (&1 + t) < t pow 2 + &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(t pow 2 + &1) pow 2 <= (m * (&1 + t)) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= x + &1`) THEN
    REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t pow 2 + &1) * (&1 + t) <= (m * (&1 + t)) * (&1 + t)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 <= t` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(m pow 2 + &2 * m) * (&1 + t) pow 2 < (t pow 2 + &1) * (&1 + t) pow 2`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT THEN UNDISCH_TAC `&0 <= t` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REAL_ARITH_TAC);;

let LAURENT_PB_SQRT_RATIO = prove
 (`!x a b. &0 < a ==> a * sqrt(x * b / a) = sqrt(x * a * b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x * a * b = a pow 2 * (x * b / a)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_MUL; POW_2_SQRT; REAL_LT_IMP_LE]);;

let LAURENT_PB_BEST = prove
 (`!K L R S b1 b2 a1 a2 q.
     2 <= K /\ 1 <= R /\ 1 <= S /\ &0 < a1 /\ &0 < a2 /\ &0 <= &L /\
     &0 <= q /\
     &R - &1 <= (&1 + sqrt(&K - &1)) * sqrt(&L * a2 / a1) /\
     &S - &1 <= (&1 + sqrt(&K - &1)) * sqrt(&L * a1 / a2) /\
     (q * sqrt(&L * a1 * a2)) pow 2 + &2 * (q * sqrt(&L * a1 * a2)) < &K
     ==> q * &((R - 1) * b2 + (S - 1) * b1) <= &K * (&b1 / a2 + &b2 / a1)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `t = sqrt(&K - &1)` THEN
  ABBREV_TAC `m = q * sqrt(&L * a1 * a2)` THEN
  SUBGOAL_THEN `&0 <= t /\ t pow 2 = &K - &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN CONJ_TAC THEN
    TRY(MATCH_MP_TAC SQRT_POS_LE) THEN TRY(MATCH_MP_TAC SQRT_POW_2) THEN
    REWRITE_TAC[REAL_SUB_LE; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(&L * a1 * a2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= m` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `m * (&1 + t) <= &K` ASSUME_TAC THENL
   [MP_TAC(SPECL [`m:real`; `t:real`] LAURENT_PB_MT) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `m pow 2 + &2 * m < &K` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&((R - 1) * b2 + (S - 1) * b1) = (&R - &1) * &b2 + (&S - &1) * &b1`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL;
                 GSYM REAL_OF_NUM_SUB];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&R - &1) * &b2 <= ((&1 + t) * sqrt(&L * a1 * a2)) * (&b2 / a1) /\
    (&S - &1) * &b1 <= ((&1 + t) * sqrt(&L * a1 * a2)) * (&b1 / a2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN
       `((&1 + t) * sqrt(&L * a1 * a2)) * (&b2 / a1) =
        ((&1 + t) * sqrt(&L * a2 / a1)) * &b2`
      SUBST1_TAC THENL
       [MP_TAC(SPECL [`&L`; `a1:real`; `a2:real`] LAURENT_PB_SQRT_RATIO) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        UNDISCH_TAC `&0 < a1` THEN CONV_TAC REAL_FIELD;
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_POS]];
      SUBGOAL_THEN
       `((&1 + t) * sqrt(&L * a1 * a2)) * (&b1 / a2) =
        ((&1 + t) * sqrt(&L * a1 / a2)) * &b1`
      SUBST1_TAC THENL
       [MP_TAC(SPECL [`&L`; `a2:real`; `a1:real`] LAURENT_PB_SQRT_RATIO) THEN
        ASM_REWRITE_TAC[REAL_ARITH `&L * a2 * a1 = &L * a1 * (a2:real)`] THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        UNDISCH_TAC `&0 < a2` THEN CONV_TAC REAL_FIELD;
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_POS]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &b1 / a2 + &b2 / a1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `q * ((&1 + t) * sqrt(&L * a1 * a2)) * (&b1 / a2 + &b2 / a1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `(&R - &1) * &b2 <= ((&1 + t) * sqrt(&L * a1 * a2)) * (&b2 / a1)` THEN
    UNDISCH_TAC
     `(&S - &1) * &b1 <= ((&1 + t) * sqrt(&L * a1 * a2)) * (&b1 / a2)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `q * ((&1 + t) * sqrt(&L * a1 * a2)) * (&b1 / a2 + &b2 / a1) =
    (m * (&1 + t)) * (&b1 / a2 + &b2 / a1)`
  SUBST1_TAC THENL
   [EXPAND_TAC "m" THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 5. Assembly of laurent_main from the b-estimate, Lombardo and Pnew.       *)
(* ------------------------------------------------------------------------- *)

let LAURENT_PB_MAIN_INEQ = prove
 (`!D rho h a1 a2 b1 b2 c K L R S H E.
     1 <= D /\ &1 < rho /\ &10 <= h /\ 1 <= b1 /\ 1 <= b2 /\
     &0 < a1 /\ &0 < a2 /\ 3 <= K /\ 1 <= L /\ 2 <= R /\ 2 <= S /\
     H < &L /\ &0 <= E /\
     &D * (log(&b1 / a2 + &b2 / a1) + log(log rho) + c) <= h /\
     &((R - 1) * b2 + (S - 1) * b1) / &2 <=
       &K * (log rho * (&b1 / a2 + &b2 / a1)) * (&3 * (&L - H) / (&2 * &L)) /\
     (&1 / &4 - &(K * L) / (&12 * &R * &S)) * &L * (&R * a1 + &S * a2) <=
       log rho * &K * &L - &K * (h + log rho) - E /\
     &2 / &(K * L) * log(&(FACT(K * L))) +
     (&K - &1) * (log(&3 * (&L - H) / (&2 * &L)) + &3 / &2 - c) +
     (&K - &1) / &K * (log(&K) + &1 / &2) <= &0
     ==> laurent_main D rho b1 b2 a1 a2 K L R S`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[laurent_main] THEN
  SUBGOAL_THEN `&0 < log rho` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &b1 / a2 + &b2 / a1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &3 * (&L - H) / (&2 * &L)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
     [UNDISCH_TAC `H < &L` THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `&0 < &2 * x <=> &0 < x`; REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &K` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &((R - 1) * b2 + (S - 1) * b1) / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC(ARITH_RULE `1 * 1 <= x ==> 0 < x + y`) THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  (* the b-estimate in logarithmic form *)
  SUBGOAL_THEN
   `log(&((R - 1) * b2 + (S - 1) * b1) / &2) <=
    log(&K) + (log(log rho) + log(&b1 / a2 + &b2 / a1)) +
    log(&3 * (&L - H) / (&2 * &L))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `log(&K * (log rho * (&b1 / a2 + &b2 / a1)) *
          (&3 * (&L - H) / (&2 * &L)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_MUL; REAL_LT_MUL; REAL_LE_REFL];
    ALL_TAC] THEN
  (* Lombardo, multiplied by 2 / K *)
  SUBGOAL_THEN `&0 <= &2 / &K` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 / &K * (&K * (&K - &1) / &2 * (log(&K) - &3 / &2) -
               (&K - &1) / &2 * (log(&K) + &1 / &2)) <=
    &2 / &K * sum(1..K - 1) (\k. log(&(FACT k)))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LOMBARDO_LOGFACT_SUM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 / &K * (&K * (&K - &1) / &2 * (log(&K) - &3 / &2) -
               (&K - &1) / &2 * (log(&K) + &1 / &2)) =
    (&K - &1) * (log(&K) - &3 / &2) - (&K - &1) / &K * (log(&K) + &1 / &2)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < &K` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  DISCH_TAC THEN
  (* the per-D quantity *)
  SUBGOAL_THEN
   `&2 / &(K * L) * log(&(FACT(K * L))) +
    ((&K - &1) * log(&((R - 1) * b2 + (S - 1) * b1) / &2) -
     &2 / &K * sum(1..K - 1) (\k. log(&(FACT k))))
    <= (&K - &1) * (log(&b1 / a2 + &b2 / a1) + log(log rho) + c)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(&K - &1) * log(&((R - 1) * b2 + (S - 1) * b1) / &2) <=
      (&K - &1) * (log(&K) + (log(log rho) + log(&b1 / a2 + &b2 / a1)) +
                   log(&3 * (&L - H) / (&2 * &L)))`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_SUB_LE; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC
     `&2 / &(K * L) * log(&(FACT(K * L))) +
      (&K - &1) * (log(&3 * (&L - H) / (&2 * &L)) + &3 / &2 - c) +
      (&K - &1) / &K * (log(&K) + &1 / &2) <= &0` THEN
    UNDISCH_TAC
     `(&K - &1) * (log(&K) - &3 / &2) -
      (&K - &1) / &K * (log(&K) + &1 / &2) <=
      &2 / &K * sum(1..K - 1) (\k. log(&(FACT k)))` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 * &D / &(K * L) * log(&(FACT(K * L))) +
    &D * ((&K - &1) * log(&((R - 1) * b2 + (S - 1) * b1) / &2) -
          &2 / &K * sum(1..K - 1) (\k. log(&(FACT k))))
    <= (&K - &1) * h`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `&D * ((&K - &1) * (log(&b1 / a2 + &b2 / a1) + log(log rho) + c))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
       `d * (&2 / n * f + y) <= z ==> &2 * d / n * f + d * y <= z`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(d:real) * k * x = k * d * x`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_SUB_LE; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC LOG_2_LE_1 THEN
  UNDISCH_TAC `&10 <= h` THEN UNDISCH_TAC `&0 <= E` THEN
  UNDISCH_TAC
   `(&1 / &4 - &(K * L) / (&12 * &R * &S)) * &L * (&R * a1 + &S * a2) <=
    log rho * &K * &L - &K * (h + log rho) - E` THEN
  UNDISCH_TAC
   `&2 * &D / &(K * L) * log(&(FACT(K * L))) +
    &D * ((&K - &1) * log(&((R - 1) * b2 + (S - 1) * b1) / &2) -
          &2 / &K * sum(1..K - 1) (\k. log(&(FACT k))))
    <= (&K - &1) * h` THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 6. Facts from LAURENT_PARAM_MAIN: the L interval, the K lower bound.      *)
(* ------------------------------------------------------------------------- *)

let LAURENT_PB_INTERVAL = prove
 (`!H L. &575 / &100 < H /\
         H + sqrt(H pow 2 + &1 / &4) - &1 / &2 < &L /\
         &L <= H + sqrt(H pow 2 + &1 / &4) + &1 / &2
         ==> 12 <= L /\ H < &L /\ &9 * &L <= &19 * H`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `H <= sqrt(H pow 2 + &1 / &4)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(H pow 2 + &1 / &4) <= &10 / &9 * H - &1 / &2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL
     [UNDISCH_TAC `&575 / &100 < H` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH
     `(&10 / &9 * H - &1 / &2) pow 2 =
      (H pow 2 + &1 / &4) + H * (&19 / &81 * H - &10 / &9)`] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x <= x + y`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    UNDISCH_TAC `&575 / &100 < H` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `&11 < &L` MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`&575 / &100 < H`; `H <= sqrt(H pow 2 + &1 / &4)`;
        `H + sqrt(H pow 2 + &1 / &4) - &1 / &2 < &L`] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC];
    MAP_EVERY UNDISCH_TAC
     [`&575 / &100 < H`; `H <= sqrt(H pow 2 + &1 / &4)`;
      `H + sqrt(H pow 2 + &1 / &4) - &1 / &2 < &L`] THEN
    REAL_ARITH_TAC;
    MAP_EVERY UNDISCH_TAC
     [`sqrt(H pow 2 + &1 / &4) <= &10 / &9 * H - &1 / &2`;
      `&L <= H + sqrt(H pow 2 + &1 / &4) + &1 / &2`] THEN
    REAL_ARITH_TAC]);;

let LAURENT_PB_H_GE = prove
 (`!rho h. &4 <= rho /\ rho <= &8 /\ &10 <= h
           ==> &575 / &100 < h / log rho + &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < log rho /\ log rho <= &21 / &10` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN UNDISCH_TAC `&4 <= rho` THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&8)` THEN
      REWRITE_TAC[LAURENT_PB_LOG_8] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&4 <= rho` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&100 / &21 <= x ==> &575 / &100 < x + &1`) THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  MAP_EVERY UNDISCH_TAC [`&10 <= h`; `log rho <= &21 / &10`] THEN
  REAL_ARITH_TAC);;

let LAURENT_PB_SQRT_DIV = prove
 (`!x p. &0 < p ==> sqrt(x / p) = sqrt(x * p) / p`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x * p = p pow 2 * (x / p)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < p` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_MUL; POW_2_SQRT; REAL_LT_IMP_LE] THEN
  UNDISCH_TAC `&0 < p` THEN CONV_TAC REAL_FIELD);;

let LAURENT_PB_KBOUND = prove
 (`!K L a1 a2 k U.
     &0 < a1 /\ &0 < a2 /\ &0 <= &L /\ &0 < U /\
     (&L / &3 / U) pow 2 +
     ((inv a1 + inv a2) / &3 + &2 / &3 * sqrt(&L / (a1 * a2))) / U <= k /\
     k * &L * a1 * a2 < &K
     ==> (&L / &3 / U * sqrt(&L * a1 * a2)) pow 2 +
         &2 * (&L / &3 / U * sqrt(&L * a1 * a2)) +
         &L / &3 / U * (a1 + a2) < &K`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < a1 * a2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &L * a1 * a2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `t = sqrt(&L * a1 * a2)` THEN
  SUBGOAL_THEN `t pow 2 = &L * a1 * a2` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN MATCH_MP_TAC SQRT_POW_2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&L / (a1 * a2)) = t / (a1 * a2)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "t" THEN ASM_SIMP_TAC[LAURENT_PB_SQRT_DIV] THEN
    REWRITE_TAC[REAL_MUL_ASSOC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `k * &L * a1 * a2` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `((&L / &3 / U) pow 2 +
     ((inv a1 + inv a2) / &3 + &2 / &3 * t / (a1 * a2)) / U) *
    (&L * a1 * a2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    REWRITE_TAC[REAL_POW_MUL] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < a1`; `&0 < a2`; `&0 < U`] THEN
    CONV_TAC REAL_FIELD;
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]]);;

let LAURENT_PB_AM_GM = prove
 (`!x y. &0 <= x /\ &0 <= y ==> &2 * sqrt(x * y) <= x + y`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `s <= (x + y) / &2 ==> &2 * s <= x + y`) THEN
  MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 <= x`; `&0 <= y`] THEN REAL_ARITH_TAC;
    MP_TAC(SPEC `x - y:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC]);;

let LAURENT_PB_KL = prove
 (`!K L H a1 a2 k lam be.
     &0 < lam /\ &0 < a1 /\ &0 < a2 /\ 12 <= L /\ H < &L /\
     &9 * &L <= &19 * H /\
     &19 / &30 <= be /\ &30 * be * lam <= &19 * sqrt(a1 * a2) /\
     (&L / &3 / (lam * (&L - H))) pow 2 +
     ((inv a1 + inv a2) / &3 + &2 / &3 * sqrt(&L / (a1 * a2))) /
     (lam * (&L - H)) <= k /\
     k * &L * a1 * a2 < &K
     ==> 3 <= K /\
         be pow 2 * &L + &2 * be * sqrt(&L) + &2 * be < &K /\
         (&L / &3 / (lam * (&L - H)) * sqrt(&L * a1 * a2)) pow 2 +
         &2 * (&L / &3 / (lam * (&L - H)) * sqrt(&L * a1 * a2)) < &K`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&12 <= &L` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < lam * (&L - H)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `H < &L` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `q = &L / &3 / (lam * (&L - H))` THEN
  SUBGOAL_THEN `&0 < q` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&12 <= &L` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`K:num`; `L:num`; `a1:real`; `a2:real`; `k:real`;
                `lam * (&L - H)`] LAURENT_PB_KBOUND) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [UNDISCH_TAC `&12 <= &L` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= q * (a1 + a2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN
    MAP_EVERY UNDISCH_TAC [`&0 < q`; `&0 < a1`; `&0 < a2`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(a1 * a2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  (* be <= q sqrt(a1 a2), from 9 L <= 19 H *)
  SUBGOAL_THEN `be <= q * sqrt(a1 * a2)` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `q * sqrt(a1 * a2) = (&L * sqrt(a1 * a2)) / (&3 * lam * (&L - H))`
    SUBST1_TAC THENL
     [EXPAND_TAC "q" THEN UNDISCH_TAC `&0 < lam * (&L - H)` THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &3 * lam * (&L - H)` ASSUME_TAC THENL
     [UNDISCH_TAC `&0 < lam * (&L - H)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    SUBGOAL_THEN `&0 <= be * lam` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN
      MAP_EVERY UNDISCH_TAC [`&19 / &30 <= be`; `&0 < lam`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(be * lam) * (&3 * (&L - H)) <= (be * lam) * (&30 / &19 * &L)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&9 * &L <= &19 * H` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(&30 / &19 * be * lam) * &L <= sqrt(a1 * a2) * &L` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [UNDISCH_TAC `&30 * be * lam <= &19 * sqrt(a1 * a2)` THEN
        REAL_ARITH_TAC;
        UNDISCH_TAC `&12 <= &L` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * be <= q * (a1 + a2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `q * &2 * sqrt(a1 * a2)` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `be <= q * sqrt(a1 * a2)` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; LAURENT_PB_AM_GM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(&L)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN UNDISCH_TAC `&12 <= &L` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `be * sqrt(&L) <= q * sqrt(&L * a1 * a2)` ASSUME_TAC THENL
   [SUBGOAL_THEN `q * sqrt(&L * a1 * a2) = (q * sqrt(a1 * a2)) * sqrt(&L)`
    SUBST1_TAC THENL
     [REWRITE_TAC[SQRT_MUL] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `be pow 2 * &L <= (q * sqrt(&L * a1 * a2)) pow 2`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `be pow 2 * &L = (be * sqrt(&L)) pow 2` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_MUL] THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_POW_2 THEN
      UNDISCH_TAC `&12 <= &L` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&19 / &30 <= be` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `be pow 2 * &L + &2 * be * sqrt(&L) + &2 * be < &K`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`be * sqrt(&L) <= q * sqrt(&L * a1 * a2)`;
      `be pow 2 * &L <= (q * sqrt(&L * a1 * a2)) pow 2`;
      `&2 * be <= q * (a1 + a2)`;
      `(q * sqrt(&L * a1 * a2)) pow 2 + &2 * (q * sqrt(&L * a1 * a2)) +
       q * (a1 + a2) < &K`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(&19 / &30) pow 2 * &12 <= be pow 2 * &L` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_POW_LE2) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= be * sqrt(&L)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&19 / &30 <= be` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&3 < &K` MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(&19 / &30) pow 2 * &12 <= be pow 2 * &L`; `&0 <= be * sqrt(&L)`;
        `&19 / &30 <= be`;
        `be pow 2 * &L + &2 * be * sqrt(&L) + &2 * be < &K`] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC];
    ASM_REWRITE_TAC[];
    UNDISCH_TAC
     `(q * sqrt(&L * a1 * a2)) pow 2 + &2 * (q * sqrt(&L * a1 * a2)) +
      q * (a1 + a2) < &K` THEN
    UNDISCH_TAC `&0 <= q * (a1 + a2)` THEN REAL_ARITH_TAC]);;

let LAURENT_PB_BEST_SCALE = prove
 (`!x y b lam L H.
     &0 < lam /\ H < L /\ &0 < L /\ L / &3 / (lam * (L - H)) * x <= y * b
     ==> x / &2 <= y * (lam * b) * (&3 * (L - H) / (&2 * L))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (L:real) - H` ASSUME_TAC THENL
   [UNDISCH_TAC `(H:real) < L` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `x / &2 = (L / &3 / (lam * (L - H)) * x) *
             (lam * &3 * (L - H) / (&2 * L))`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`&0 < (lam:real)`; `&0 < (L:real) - H`; `&0 < (L:real)`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `y * (lam * b) * (&3 * (L - H) / (&2 * L)) =
    (y * b) * (lam * &3 * (L - H) / (&2 * L))`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [UNDISCH_TAC `&0 < (lam:real)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN
  MAP_EVERY UNDISCH_TAC [`&0 < (L:real) - H`; `&0 < (L:real)`] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 7. The generic export (regime given by c, be and a Pnew lemma).           *)
(* ------------------------------------------------------------------------- *)

let LAURENT_PB_GENERIC = prove
 (`!D rho h a1 a2 b1 b2 c be.
     1 <= D /\ &4 <= rho /\ rho <= &8 /\ &10 <= h /\
     &1 <= a1 /\ &1 <= a2 /\ log rho pow 2 <= a1 * a2 /\
     1 <= b1 /\ 1 <= b2 /\
     &D * (log(&b1 / a2 + &b2 / a1) + log(log rho) + c) <= h /\
     &19 / &30 <= be /\ &30 * be * log rho <= &19 * sqrt(a1 * a2) /\
     (!K L kap.
        12 <= L /\ be pow 2 * &L + &2 * be * sqrt(&L) + &2 * be < &K /\
        kap <= --(&23 / &100)
        ==> &2 / &(K * L) * log(&(FACT(K * L))) +
            (&K - &1) * (kap + &3 / &2 - c) +
            (&K - &1) / &K * (log(&K) + &1 / &2) <= &0)
     ==> ?K L R1 S1 R2 S2.
           2 <= K /\ 2 <= L /\ 1 <= R1 /\ 1 <= S1 /\ 1 <= R2 /\ 1 <= S2 /\
           2 <= (R1 + R2) - 1 /\ 2 <= (S1 + S2) - 1 /\
           L <= R1 * S1 /\ (K - 1) * L < R2 * S2 /\
           laurent_main D rho b1 b2 a1 a2 K L ((R1 + R2) - 1) ((S1 + S2) - 1) /\
           &(K * L) * log rho <=
             laurent_C rho h a1 a2 * (h + log rho) pow 2 * a1 * a2 +
             sqrt(laurent_omega (h / log rho + &1) *
                  laurent_theta (h / log rho + &1)) * (h + log rho) /\
           &(L * ((R1 + R2) - 1)) <=
             &186 / &100 * laurent_Cp rho h a1 a2 * (h + log rho) pow 2 *
             a1 * a2 /\
           &(L * ((S1 + S2) - 1)) <=
             &186 / &100 * laurent_Cp rho h a1 a2 * (h + log rho) pow 2 *
             a1 * a2 /\
           &((R1 + R2) - 1) * a1 + &((S1 + S2) - 1) * a2 <=
             laurent_C rho h a1 a2 * (h + log rho) pow 2 * a1 * a2 / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`rho:real`; `h:real`; `a1:real`; `a2:real`]
    LAURENT_PARAM_MAIN) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`K:num`; `L:num`; `R1:num`; `S1:num`; `R2:num`; `S2:num`; `k:real`] THEN
  DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`K:num`; `L:num`; `R1:num`; `S1:num`; `R2:num`; `S2:num`] THEN
  POP_ASSUM MP_TAC THEN
  ABBREV_TAC `H = h / log rho + &1` THEN
  ABBREV_TAC `R = (R1 + R2) - 1` THEN
  ABBREV_TAC `S = (S1 + S2) - 1` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `laurent_main D rho b1 b2 a1 a2 K L R S` ASSUME_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN `2 <= L` ASSUME_TAC THENL
     [UNDISCH_TAC `11 <= L` THEN ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC] THEN
  SUBGOAL_THEN `&0 < a1 /\ &0 < a2 /\ &0 < log rho` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `&1 <= a1` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `&1 <= a2` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_POS_LT THEN UNDISCH_TAC `&4 <= rho` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&575 / &100 < H` ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN MATCH_MP_TAC LAURENT_PB_H_GE THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`H:real`; `L:num`] LAURENT_PB_INTERVAL) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`K:num`; `L:num`; `H:real`; `a1:real`; `a2:real`; `k:real`;
                `log rho`; `be:real`] LAURENT_PB_KL) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &L` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN UNDISCH_TAC `12 <= L` THEN ARITH_TAC;
    ALL_TAC] THEN
  (* kap <= -0.23 *)
  SUBGOAL_THEN `log(&3 * (&L - H) / (&2 * &L)) <= --(&23 / &100)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LAURENT_PB_LOG_15_19 THEN
    SUBGOAL_THEN `&0 < &2 * &L` ASSUME_TAC THENL
     [UNDISCH_TAC `&0 < &L` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LE_LDIV_EQ] THEN
    MAP_EVERY UNDISCH_TAC [`H < &L`; `&9 * &L <= &19 * H`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the b-estimate *)
  MP_TAC(SPECL [`K:num`; `L:num`; `R:num`; `S:num`; `b1:num`; `b2:num`;
                `a1:real`; `a2:real`; `&L / &3 / (log rho * (&L - H))`]
    LAURENT_PB_BEST) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [UNDISCH_TAC `2 <= R` THEN ARITH_TAC;
      UNDISCH_TAC `2 <= S` THEN ARITH_TAC;
      UNDISCH_TAC `&0 < &L` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
       [UNDISCH_TAC `&0 < &L` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      MAP_EVERY UNDISCH_TAC [`&0 < log rho`; `H < &L`] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`&((R - 1) * b2 + (S - 1) * b1)`; `&K`;
                `&b1 / a2 + &b2 / a1`; `log rho`; `&L`; `H:real`]
    LAURENT_PB_BEST_SCALE) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  (* Pnew *)
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`K:num`; `L:num`; `log(&3 * (&L - H) / (&2 * &L))`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC LAURENT_PB_MAIN_INEQ THEN
  MAP_EVERY EXISTS_TAC
   [`h:real`; `c:real`; `H:real`;
    `&L * sqrt(&L) * sqrt(a1 * a2) / (&6 * (&1 + sqrt(&K - &1)))`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [UNDISCH_TAC `&4 <= rho` THEN REAL_ARITH_TAC;
    UNDISCH_TAC `12 <= L` THEN ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [UNDISCH_TAC `&0 < &L` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN UNDISCH_TAC `&0 < &L` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN
      MAP_EVERY UNDISCH_TAC [`&0 < a1`; `&0 < a2`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    MATCH_MP_TAC SQRT_POS_LE THEN REWRITE_TAC[REAL_SUB_LE; REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `3 <= K` THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 8. The exports of the numeric layer.                                      *)
(* ------------------------------------------------------------------------- *)

let LAURENT_PARAMETERS = prove
 (`!D rho h a1 a2 b1 b2.
     1 <= D /\ &4 <= rho /\ rho <= &8 /\ &10 <= h /\
     &1 <= a1 /\ &1 <= a2 /\ log rho pow 2 <= a1 * a2 /\
     1 <= b1 /\ 1 <= b2 /\
     &D * (log(&b1 / a2 + &b2 / a1) + log(log rho) + &5 / &2) <= h
     ==> ?K L R1 S1 R2 S2.
           2 <= K /\ 2 <= L /\ 1 <= R1 /\ 1 <= S1 /\ 1 <= R2 /\ 1 <= S2 /\
           2 <= (R1 + R2) - 1 /\ 2 <= (S1 + S2) - 1 /\
           L <= R1 * S1 /\ (K - 1) * L < R2 * S2 /\
           laurent_main D rho b1 b2 a1 a2 K L ((R1 + R2) - 1) ((S1 + S2) - 1) /\
           &(K * L) * log rho <=
             laurent_C rho h a1 a2 * (h + log rho) pow 2 * a1 * a2 +
             sqrt(laurent_omega (h / log rho + &1) *
                  laurent_theta (h / log rho + &1)) * (h + log rho) /\
           &(L * ((R1 + R2) - 1)) <=
             &186 / &100 * laurent_Cp rho h a1 a2 * (h + log rho) pow 2 *
             a1 * a2 /\
           &(L * ((S1 + S2) - 1)) <=
             &186 / &100 * laurent_Cp rho h a1 a2 * (h + log rho) pow 2 *
             a1 * a2 /\
           &((R1 + R2) - 1) * a1 + &((S1 + S2) - 1) * a2 <=
             laurent_C rho h a1 a2 * (h + log rho) pow 2 * a1 * a2 / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC LAURENT_PB_GENERIC THEN
  MAP_EVERY EXISTS_TAC [`&5 / &2`; `&19 / &30`] THEN
  REWRITE_TAC[LAURENT_PB_PNEW_A; REAL_LE_REFL] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  MATCH_MP_TAC(REAL_ARITH `l <= s ==> &30 * &19 / &30 * l <= &19 * s`) THEN
  MATCH_MP_TAC REAL_LE_RSQRT THEN FIRST_ASSUM ACCEPT_TAC);;

let LAURENT_PARAMETERS_LARGE = prove
 (`!D rho h a1 a2 b1 b2.
     1 <= D /\ &4 <= rho /\ rho <= &8 /\ &10 <= h /\
     rho + &1 <= a1 /\ rho + &1 <= a2 /\
     1 <= b1 /\ 1 <= b2 /\
     &D * (log(&b1 / a2 + &b2 / a1) + log(log rho) + &3 / &2) <= h
     ==> ?K L R1 S1 R2 S2.
           2 <= K /\ 2 <= L /\ 1 <= R1 /\ 1 <= S1 /\ 1 <= R2 /\ 1 <= S2 /\
           2 <= (R1 + R2) - 1 /\ 2 <= (S1 + S2) - 1 /\
           L <= R1 * S1 /\ (K - 1) * L < R2 * S2 /\
           laurent_main D rho b1 b2 a1 a2 K L ((R1 + R2) - 1) ((S1 + S2) - 1) /\
           &(K * L) * log rho <=
             laurent_C rho h a1 a2 * (h + log rho) pow 2 * a1 * a2 +
             sqrt(laurent_omega (h / log rho + &1) *
                  laurent_theta (h / log rho + &1)) * (h + log rho) /\
           &(L * ((R1 + R2) - 1)) <=
             &186 / &100 * laurent_Cp rho h a1 a2 * (h + log rho) pow 2 *
             a1 * a2 /\
           &(L * ((S1 + S2) - 1)) <=
             &186 / &100 * laurent_Cp rho h a1 a2 * (h + log rho) pow 2 *
             a1 * a2 /\
           &((R1 + R2) - 1) * a1 + &((S1 + S2) - 1) * a2 <=
             laurent_C rho h a1 a2 * (h + log rho) pow 2 * a1 * a2 / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= log rho /\ log rho <= rho + &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN UNDISCH_TAC `&4 <= rho` THEN REAL_ARITH_TAC;
      MP_TAC(SPEC `rho:real` LOG_LE_SUB_1) THEN
      UNDISCH_TAC `&4 <= rho` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(rho + &1) pow 2 <= a1 * a2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&4 <= rho` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC LAURENT_PB_GENERIC THEN
  MAP_EVERY EXISTS_TAC [`&3 / &2`; `&133 / &60`] THEN
  REWRITE_TAC[LAURENT_PB_PNEW_B] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [MAP_EVERY UNDISCH_TAC [`&4 <= rho`; `rho + &1 <= a1`] THEN
    REAL_ARITH_TAC;
    MAP_EVERY UNDISCH_TAC [`&4 <= rho`; `rho + &1 <= a2`] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY UNDISCH_TAC
     [`log rho <= rho + &1`; `rho + &1 <= a1`; `rho + &1 <= a2`] THEN
    REAL_ARITH_TAC;
    CONV_TAC REAL_RAT_REDUCE_CONV;
    MP_TAC(SPEC `rho:real` LAURENT_PB_RHO_LOG) THEN ANTS_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `rho + &1 <= sqrt(a1 * a2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC]);;
