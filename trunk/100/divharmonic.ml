(* ========================================================================= *)
(* Divergence of harmonic series.                                            *)
(* ========================================================================= *)

prioritize_real();;

let HARMONIC_DIVERGES = prove
 (`~(?s. !e. &0 < e
             ==> ?N. !n. N <= n ==> abs(sum(1..n) (\i. &1 / &i) - s) < e)`,
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `&1 / &4`) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `N + 1`) THEN REWRITE_TAC[LE_ADD] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(N + 1) + (N + 1)`) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[SUM_ADD_SPLIT; ARITH_RULE `1 <= (N + 1) + 1`] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&1 / &2 <= y
    ==> abs((x + y) - s) < &1 / &4 ==> ~(abs(x - s) < &1 / &4)`) THEN
  REWRITE_TAC[GSYM MULT_2] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum((N + 1) + 1 .. 2 * (N + 1)) (\i. &1 / &(2 * (N + 1)))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[SUM_CONST_NUMSEG; ARITH_RULE `(2 * x + 1) - (x + 1) = x`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
    MP_TAC(SPEC `n:num` REAL_POS) THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Formulation in terms of limits.                                           *)
(* ------------------------------------------------------------------------- *)

needs "Library/analysis.ml";;

let HARMONIC_DIVERGES' = prove
 (`~(convergent (\n. sum(1..n) (\i. &1 / &i)))`,
  REWRITE_TAC[convergent; SEQ; GE; HARMONIC_DIVERGES]);;

(* ------------------------------------------------------------------------- *)
(* Lower bound on the partial sums.                                          *)
(* ------------------------------------------------------------------------- *)

let HARMONIC_LEMMA = prove
 (`!m. sum(1..2 EXP m) (\n. &1 / &n) >= &m / &2`,
  REWRITE_TAC[real_ge] THEN INDUCT_TAC THEN
  REWRITE_TAC[EXP; MULT_2; SUM_SING_NUMSEG] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SIMP_TAC[SUM_ADD_SPLIT; ARITH_RULE `1 <= 2 EXP m + 1`] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
   `a <= x ==> b - a <= y ==> b <= x + y`)) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; GSYM (CONJUNCT2 EXP); GSYM MULT_2] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(2 EXP m + 1..2 EXP (SUC m))(\n. &1 / &(2 EXP (SUC m)))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[SUM_CONST_NUMSEG; EXP; ARITH_RULE `(2 * x + 1) - (x + 1) = x`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    MP_TAC(SPECL [`2`; `m:num`] EXP_EQ_0) THEN
    REWRITE_TAC[ARITH] THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
    CONV_TAC REAL_FIELD;
    MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Germ of an alternative proof.                                             *)
(* ------------------------------------------------------------------------- *)

needs "Library/transc.ml";;

let LOG_BOUND = prove
 (`&0 < x /\ x < &1 ==> ln(&1 + x) >= x / &2`,
  REWRITE_TAC[real_ge] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM LN_EXP] THEN
  ASM_SIMP_TAC[LN_MONO_LE; REAL_EXP_POS_LT; REAL_LT_ADD; REAL_LT_01] THEN
  MP_TAC(SPEC `x / &2` REAL_EXP_BOUND_LEMMA) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC);;
