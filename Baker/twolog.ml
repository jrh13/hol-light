(* ========================================================================= *)
(* Two logarithms: the explicit lower bound for linear forms in two          *)
(* logarithms of positive rationals,                                         *)
(*   |b2 log(p2/q2) - b1 log(p1/q1)| >= exp(-40000 h1 h2 B^2)                *)
(*   with B = max(10, log(b1/h2 + b2/h1), log(h1 h2)),                       *)
(* and the corollary |b2 log 2 - b1 log 3| >= exp(-45000 M^2) with           *)
(* M = max(10, log(b1 + b2)), the form needed for the 3x+1 application.      *)
(*                                                                           *)
(* Purpose: the final assembly, following Y. Bugeaud, Linear Forms in        *)
(* Logarithms and Applications (EMS 2018), chapter 11.                       *)
(*                                                                           *)
(* Main results: TWOLOG_RATIONAL_ORDERED, TWOLOG_RATIONAL, TWOLOG_LOG2_LOG3  *)
(* and its existential form TWOLOG_LOG2_LOG3_EXISTS.                         *)
(*                                                                           *)
(* Uses: TWOLOG_ZERO_MINOR (Baker/twolog_zero.ml), TWOLOG_CORE_PARAMETRIC    *)
(* (Baker/twolog_core.ml), TWOLOG_PARAMETERS and EXP_1_APPROX                *)
(* (Baker/twolog_param.ml), REAL_ABS_SUB_NUM_GE_1, REAL_INV_LE_FROM_MUL and  *)
(* REAL_POW_DIV_LE_EXP (Baker/lemmas.ml).                                    *)
(*                                                                           *)
(* Contents.                                                                 *)
(*  1. Elementary bounds for exp and log (e, log 3 <= 9/8, ...).             *)
(*  2. A Liouville inequality: |log(x/y)| >= 1/(x y) for integers x <> y.    *)
(*  3. Cardinality of an injective image of a grid.                          *)
(*  4. The sums of (i - 1) MOD K and (i - 1) DIV K over 1..K L.              *)
(*  5. From the conclusion of the parametric core to an exponential bound.   *)
(*  6. Numerics.                                                             *)
(*  7. Degenerate cases: collisions of the two grid maps.                    *)
(*  8. The main case: both grid maps injective.                              *)
(*  9. The ordered theorem and the final theorem TWOLOG_RATIONAL.            *)
(* 10. The linear form b2 log 2 - b1 log 3: TWOLOG_LOG2_LOG3 and the         *)
(*     existential form TWOLOG_LOG2_LOG3_EXISTS.                             *)
(*                                                                           *)
(* Parsing note: in HOL Light the infix - binds tighter than +, so the term  *)
(* R1 + R2 - 2 of TWOLOG_PARAMETERS is R1 + (R2 - 2). The core is applied    *)
(* with R = (R1 + R2 - 2) + 1 and S = (S1 + S2 - 2) + 1: then R - 1 and      *)
(* S - 1 reduce by ADD_SUB to exactly those terms, also when R2 = 1 or       *)
(* S2 = 1, and rr j < R, ss j < S still follow from TWOLOG_ZERO_MINOR.       *)
(* ========================================================================= *)

needs "Baker/twolog_zero.ml";;
needs "Baker/twolog_core.ml";;
needs "Baker/twolog_param.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* 1. Elementary bounds for exp and log.                                     *)
(* ------------------------------------------------------------------------- *)

let LOG_LE_SUB_1 = prove
 (`!z. &0 < z ==> log z <= z - &1`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `(z:real) - &1` LOG_LE_STRONG) THEN
  REWRITE_TAC[REAL_ARITH `&1 + ((z:real) - &1) = z`] THEN
  ASM_REWRITE_TAC[]);;

let LOG_3_BOUNDS = prove
 (`&1 <= log(&3) /\ log(&3) <= &9 / &8`,
  MP_TAC EXP_1_APPROX THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`exp(&1)`; `&3`] LOG_MONO_LE_IMP) THEN
    REWRITE_TAC[LOG_EXP; REAL_EXP_POS_LT] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(SPECL [`&3`; `exp(&9 / &8)`] LOG_MONO_LE_IMP) THEN
    REWRITE_TAC[LOG_EXP] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `exp(&9 / &8) = exp(&1) * exp(&1 / &8)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `&1 / &8` REAL_EXP_LE_X) THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&27 / &10) * (&1 + &1 / &8)` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC]);;

let NUM_POW_LE_EXP = prove
 (`!p v h. 1 <= p /\ log(&p) <= h ==> &p pow v <= exp(&v * h)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&p pow v = exp(&v * log(&p))` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_EXP_N] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXP_LOG THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REWRITE_TAC[REAL_POS]);;

let LOG_RATIO_ABS_LE = prove
 (`!p q h. 1 <= p /\ 1 <= q /\ log(&p) <= h /\ log(&q) <= h
           ==> abs(log(&p / &q)) <= h`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &p /\ &0 < &q /\ &1 <= &p /\ &1 <= &q`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_DIV] THEN
  MP_TAC(SPEC `&p:real` LOG_POS) THEN MP_TAC(SPEC `&q:real` LOG_POS) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let LOG_NUM_BOUND_POS = prove
 (`!p h. 1 <= p /\ log(&p) <= h ==> &0 <= h`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `&p:real` LOG_POS) THEN
  REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 2. A Liouville inequality for logarithms of rationals.                    *)
(* ------------------------------------------------------------------------- *)

let LOG_DIV_LOWER_REAL = prove
 (`!a b. &1 <= b /\ b + &1 <= a ==> inv(a * b) <= log(a / b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < a /\ &0 < b` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `log(a / b) = --log(b / a)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[LOG_DIV] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `b / a` LOG_LE_SUB_1) THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN
  SUBGOAL_THEN `b / a - &1 <= --inv(a * b)`
   (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
  SUBGOAL_THEN `&0 < a * b` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    ONCE_REWRITE_TAC[GSYM(MATCH_MP REAL_LE_RMUL_EQ th)]) THEN
  SUBGOAL_THEN `(b / a - &1) * (a * b) = b * b - a * b /\
                --inv(a * b) * (a * b) = --(&1)`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN
    MAP_EVERY UNDISCH_TAC [`&0 < a`; `&0 < b`] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(SPECL [`&1`; `b:real`; `&1`; `a - b:real`] REAL_LE_MUL2) THEN
  ASM_REAL_ARITH_TAC);;

let LOG_RATIO_LOWER_INV = prove
 (`!x y. 1 <= x /\ 1 <= y /\ ~(x = y) ==> inv(&x * &y) <= abs(log(&x / &y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &x /\ &0 < &y` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `y + 1 <= x \/ x + 1 <= y` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC;
    MP_TAC(SPECL [`&x:real`; `&y:real`] LOG_DIV_LOWER_REAL) THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    MP_TAC(SPECL [`&y:real`; `&x:real`] LOG_DIV_LOWER_REAL) THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN `log(&x / &y) = --log(&y / &x)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[LOG_DIV] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_SYM] THEN REAL_ARITH_TAC]);;

let LOG_RATIO_LOWER_PRODUCT = prove
 (`!x y a. 1 <= x /\ 1 <= y /\ ~(x = y) /\ &x * &y <= exp a
           ==> exp(--a) <= abs(log(&x / &y))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(&x * &y)` THEN ASM_SIMP_TAC[LOG_RATIO_LOWER_INV] THEN
  REWRITE_TAC[REAL_EXP_NEG] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN
  REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 3. Cardinality of an injective image of a grid.                           *)
(* ------------------------------------------------------------------------- *)

let CARD_IMAGE_INJ_GRID = prove
 (`!(f:num->num->A) R S.
     (!r s r' s'. r < R /\ s < S /\ r' < R /\ s' < S /\ f r s = f r' s'
                  ==> r = r' /\ s = s')
     ==> CARD {f r s | r,s | r < R /\ s < S} = R * S`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{(f:num->num->A) r s | r,s | r < R /\ s < S} =
                IMAGE (\p. f (FST p) (SND p)) ({r | r < R} CROSS {s | s < S})`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_CROSS; IN_ELIM_THM; EXISTS_PAIR_THM;
                FST; SND] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CARD_IMAGE_INJ o lhand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG_LT] THEN
    REWRITE_TAC[IN_CROSS; IN_ELIM_THM; FORALL_PAIR_THM; PAIR_EQ; FST; SND] THEN
    ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC THEN
    SIMP_TAC[CARD_CROSS; FINITE_NUMSEG_LT; CARD_NUMSEG_LT]]);;

(* ------------------------------------------------------------------------- *)
(* 4. The sums of the row exponents (i - 1) MOD K and (i - 1) DIV K.         *)
(* ------------------------------------------------------------------------- *)

let PRED_MULT_ADD_2 = prove
 (`!n. n * (n - 1) + 2 * n = SUC n * n`,
  INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES; SUC_SUB1; SUB_0] THEN
  ARITH_TAC);;

let NSUM_NUMSEG_PRED = prove
 (`!n. 2 * nsum(1..n) (\i. i - 1) = n * (n - 1)`,
  INDUCT_TAC THEN
  REWRITE_TAC[NSUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`; ARITH_EQ] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; SUC_SUB1; PRED_MULT_ADD_2] THEN
  ARITH_TAC);;

let NSUM_NUMSEG_BLOCK = prove
 (`!(f:num->num) K L.
     nsum(1..K * SUC L) f = nsum(1..K * L) f + nsum(1..K) (\i. f(i + K * L))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `K * SUC L = K * L + K` SUBST1_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:num->num`; `1`; `K * L`; `K:num`] NSUM_ADD_SPLIT) THEN
  REWRITE_TAC[ARITH_RULE `1 <= n + 1`] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `K * L + 1 = 1 + K * L /\ K * L + K = K + K * L`
   (fun th -> REWRITE_TAC[th]) THENL
   [ARITH_TAC; REWRITE_TAC[NSUM_OFFSET]]);;

let NSUM_NUMSEG_PRED_MOD = prove
 (`!K L. 2 * nsum(1..K * L) (\i. (i - 1) MOD K) = K * L * (K - 1)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; NSUM_CLAUSES_NUMSEG; ARITH_EQ]; ALL_TAC] THEN
  REWRITE_TAC[NSUM_NUMSEG_BLOCK; LEFT_ADD_DISTRIB] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `nsum(1..K) (\i. ((i + K * L) - 1) MOD K) =
                nsum(1..K) (\i. i - 1)` SUBST1_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= i ==> (i + x) - 1 = (i - 1) + x`;
                 MOD_MULT_ADD] THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[NSUM_NUMSEG_PRED] THEN
  REWRITE_TAC[MULT_CLAUSES; RIGHT_ADD_DISTRIB; MULT_ASSOC] THEN ARITH_TAC);;

let NSUM_NUMSEG_PRED_DIV = prove
 (`!K L. 1 <= K ==> 2 * nsum(1..K * L) (\i. (i - 1) DIV K) = K * L * (L - 1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC(`L:num`,`L:num`) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; NSUM_CLAUSES_NUMSEG; ARITH_EQ]; ALL_TAC] THEN
  REWRITE_TAC[NSUM_NUMSEG_BLOCK; LEFT_ADD_DISTRIB] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `nsum(1..K) (\i. ((i + K * L) - 1) DIV K) =
                nsum(1..K) (\i. L)` SUBST1_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= i ==> (i + x) - 1 = (i - 1) + x`;
                 DIV_MULT_ADD; ARITH_RULE `1 <= K ==> ~(K = 0)`] THEN
    SUBGOAL_THEN `(i - 1) DIV K = 0` SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_LT THEN ASM_ARITH_TAC; ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[NSUM_CONST_NUMSEG; ADD_SUB; SUC_SUB1] THEN
  REWRITE_TAC[GSYM PRED_MULT_ADD_2] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN ARITH_TAC);;

let NSUM_NUMSEG_BOUND_LT = prove
 (`!(rr:num->num) N R.
     (!j. j IN 1..N ==> rr j < R) ==> nsum(1..N) rr <= N * (R - 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`1..N`; `rr:num->num`; `R - 1`] NSUM_BOUND) THEN
  REWRITE_TAC[FINITE_NUMSEG; CARD_NUMSEG_1] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 5. From the conclusion of the parametric core to an exponential bound.    *)
(* ------------------------------------------------------------------------- *)

let REAL_INV_LT_FROM_MUL = prove
 (`!z t. &0 < z /\ &1 < z * t ==> inv z < t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`&1`; `t:real`; `z:real`] REAL_LT_LDIV_EQ) THEN
  ASM_REWRITE_TAC[real_div; REAL_MUL_LID] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REAL_ARITH_TAC);;

let TL_FINAL_CORE_TO_BOUND = prove
 (`!t m b N.
     &0 <= t /\ &1 <= m /\ &1 <= b /\
     inv(&3 pow N) < t * m * exp(m * t / b) / b
     ==> exp(--(&1 + &N * log(&3) + log m)) <= t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b /\ &0 < m` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exp(--(&1 + &N * log(&3) + log m)) =
                inv(exp(&1) * &3 pow N * m)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_EXP_NEG; REAL_EXP_ADD; REAL_EXP_N] THEN
    ASM_SIMP_TAC[EXP_LOG; REAL_ARITH `&0 < &3`];
    ALL_TAC] THEN
  MP_TAC EXP_1_APPROX THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &3 pow N` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= exp(&1) * &3 pow N` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * &1` THEN
    CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < exp(&1) * &3 pow N * m` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `t / b <= t` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `m * t / b <= m * t` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&1 <= m * t / b` THENL
   [MATCH_MP_TAC REAL_INV_LE_FROM_MUL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`&1`; `exp(&1) * &3 pow N`; `&1`; `m * t:real`]
      REAL_LE_MUL2) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(m * t / b) / b <= exp(&1)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(&1)` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `t * m * exp(m * t / b) / b <= t * m * exp(&1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < &3 pow N * (t * m * exp(&1))` ASSUME_TAC THENL
   [SUBGOAL_THEN `&3 pow N * inv(&3 pow N) = &1`
     (fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THENL
     [MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_INV_LT_FROM_MUL THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 6. Numerics.                                                              *)
(* ------------------------------------------------------------------------- *)

let TL_FINAL_X_FACTS = prove
 (`!h1 h2 B. &1 <= h1 /\ &1 <= h2 /\ &10 <= B
             ==> &100 <= h1 * h2 * B pow 2 /\
                 &100 * h1 <= h1 * h2 * B pow 2 /\
                 &100 * h2 <= h1 * h2 * B pow 2 /\
                 &10 * h1 * h2 * B <= h1 * h2 * B pow 2 /\
                 h1 * B <= h1 * h2 * B /\
                 h2 * B <= h1 * h2 * B /\
                 &1 <= h1 * h2 * B pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= h1 * h2 * B * (B - &10) /\ &0 <= h1 * B * (h2 - &1) /\
                &0 <= h2 * B * (h1 - &1) /\ &0 <= h1 * h2 * (B - &10) /\
                &0 <= h1 * (h2 - &1) /\ &0 <= h2 * (h1 - &1)`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC]);;

let TL_FINAL_LOG_BOUND = prove
 (`!M X. 1 <= M /\ &M <= &7000000 * X pow 2 /\ &1 <= X
         ==> &1 + log(&M) <= &625 * X`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `log(&M) <= &624 * X`
   (fun th -> MP_TAC th THEN ASM_REAL_ARITH_TAC) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(exp(&624 * X))` THEN
  CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[LOG_EXP; REAL_LE_REFL]] THEN
  MATCH_MP_TAC LOG_MONO_LE_IMP THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&7000000 * X pow 2` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `((&624 * X) / &3) pow 3` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `&0 <= X pow 2 * (X - &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `X:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_POW_DIV_LE_EXP THEN ASM_REAL_ARITH_TAC]);;

let TL_FINAL_MAIN_NUMERIC = prove
 (`!h1 h2 B K L S1 S2.
     &1 <= h1 /\ &1 <= h2 /\ &10 <= B /\ 1 <= K /\ 1 <= L /\ 2 <= S1 /\
     1 <= S2 /\
     &(K * L) <= &35000 * h1 * h2 * B pow 2 /\
     &(S1 + S2) <= &200 * h1 * B
     ==> &1 + &(K * L) * log(&3) + log(&(L * ((S1 + S2 - 2) + 1))) <=
         &40000 * h1 * h2 * B pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`h1:real`; `h2:real`; `B:real`] TL_FINAL_X_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `X = h1 * h2 * B pow 2` THEN
  MP_TAC LOG_3_BOUNDS THEN STRIP_TAC THEN
  SUBGOAL_THEN `&(K * L) * log(&3) <= (&35000 * X) * (&9 / &8)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_POS] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 + log(&(L * ((S1 + S2 - 2) + 1))) <= &625 * X`
  ASSUME_TAC THENL
   [MATCH_MP_TAC TL_FINAL_LOG_BOUND THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `1 * 1 <= x ==> 1 <= x`) THEN
      MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(K * L) * &(S1 + S2)` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
      MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `1 * L <= K * L ==> L <= K * L`) THEN
        MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC;
        ASM_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&35000 * X) * (&200 * h1 * B)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_POS];
      ALL_TAC] THEN
    SUBGOAL_THEN `(X:real) * (h1 * B) <= X * X` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let TL_FINAL_DEGEN_M_NUMERIC = prove
 (`!h1 h2 B R1 R2.
     &1 <= h1 /\ &1 <= h2 /\ &10 <= B /\ &(R1 + R2) <= &200 * h2 * B
     ==> &2 * h1 + &2 * h2 + &R1 <= &40000 * h1 * h2 * B pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`h1:real`; `h2:real`; `B:real`] TL_FINAL_X_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&R1 <= &(R1 + R2)` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let TL_FINAL_DEGEN_A_NUMERIC = prove
 (`!h1 h2 B R1 S1 R2 S2.
     &1 <= h1 /\ &1 <= h2 /\ &10 <= B /\
     &(R1 + R2) <= &200 * h2 * B /\ &(S1 + S2) <= &200 * h1 * B
     ==> &2 * (&S2 * h2 + &R2 * h1) + &R2 <= &40000 * h1 * h2 * B pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`h1:real`; `h2:real`; `B:real`] TL_FINAL_X_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&R2 <= &200 * h2 * B /\ &S2 <= &200 * h1 * B`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `&(R1 + R2)`; EXISTS_TAC `&(S1 + S2)`] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&S2 * h2 <= (&200 * h1 * B) * h2 /\
                &R2 * h1 <= (&200 * h2 * B) * h1`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let TL_FINAL_B_SYM = prove
 (`!b1 b2 h1 h2.
     max (&10) (max (log(&b2 / h1 + &b1 / h2)) (log(h2 * h1))) =
     max (&10) (max (log(&b1 / h2 + &b2 / h1)) (log(h1 * h2)))`,
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN BINOP_TAC THEN AP_TERM_TAC THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 7. Degenerate cases: collisions of the two grid maps.                     *)
(* ------------------------------------------------------------------------- *)

let EXP_NEG_ADD_MUL_LE = prove
 (`!a x. &0 <= x ==> exp(--(a + x)) * x <= exp(--a)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(--(a + x)) * exp x` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MP_TAC(SPEC `x:real` REAL_EXP_LE_X) THEN REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN REAL_ARITH_TAC]);;

let NUM_LE_EXP = prove
 (`!p h. 1 <= p /\ log(&p) <= h ==> &p <= exp h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `1`; `h:real`] NUM_POW_LE_EXP) THEN
  ASM_REWRITE_TAC[REAL_POW_1; REAL_MUL_LID]);;

let LOG_RATIO_LOWER_HEIGHT = prove
 (`!p q h. 1 <= p /\ 1 <= q /\ log(&p) <= h /\ log(&q) <= h /\
           ~(log(&p / &q) = &0)
           ==> exp(--(&2 * h)) <= abs(log(&p / &q))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LOG_RATIO_LOWER_PRODUCT THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(log(&p / &q) = &0)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&q / &q = &1` (fun th -> REWRITE_TAC[th; LOG_1]) THEN
    MATCH_MP_TAC REAL_DIV_REFL THEN REWRITE_TAC[REAL_OF_NUM_EQ] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[REAL_ARITH `&2 * h = h + h`; REAL_EXP_ADD] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_POS] THEN
    ASM_SIMP_TAC[NUM_LE_EXP]]);;

let LOG_POW_MUL = prove
 (`!x y r s. &0 < x /\ &0 < y
             ==> log(x pow r * y pow s) = &r * log x + &s * log y`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LOG_MUL; REAL_POW_LT; LOG_POW]);;

let TL_FINAL_MCOLL_REAL_LE = prove
 (`!l1 l2 b1 b2 R1 r s r' s'.
     1 <= b1 /\ 1 <= b2 /\ r < R1 /\ r' <= r /\ ~(r = r' /\ s = s') /\
     &r * l1 + &s * l2 = &r' * l1 + &s' * l2 /\
     ~(&b2 * l2 - &b1 * l1 = &0)
     ==> (l2 = &0 /\ ~(l1 = &0) /\ abs l1 <= abs(&b2 * l2 - &b1 * l1)) \/
         (~(l2 = &0) /\ abs l2 <= &R1 * abs(&b2 * l2 - &b1 * l1))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `r':num = r` THENL
   [DISJ1_TAC THEN
    SUBGOAL_THEN `~(s:num = s')` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `l2 = &0` ASSUME_TAC THENL
     [SUBGOAL_THEN `(&s - &s') * l2 = &0` MP_TAC THENL
       [UNDISCH_TAC `&r * l1 + &s * l2 = &r' * l1 + &s' * l2` THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        ASM_REWRITE_TAC[REAL_ENTIRE; REAL_SUB_0; REAL_OF_NUM_EQ]];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(&b2 * l2 - &b1 * l1 = &0)` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_LZERO; REAL_ABS_NEG;
                    REAL_ABS_MUL; REAL_ABS_NUM] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 * a <= b ==> a <= b`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[REAL_ABS_POS; REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISJ2_TAC THEN
  SUBGOAL_THEN `?u. r = r' + u /\ 1 <= u` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `r - r':num` THEN
    MAP_EVERY UNDISCH_TAC [`r':num <= r`; `~(r':num = r)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&u * l1 = (&s' - &s) * l2` ASSUME_TAC THENL
   [UNDISCH_TAC `&r * l1 + &s * l2 = &r' * l1 + &s' * l2` THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(&u * (&b2 * l2 - &b1 * l1) = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_ENTIRE; REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&u * (&b2 * l2 - &b1 * l1) =
                (&(u * b2 + b1 * s) - &(b1 * s')) * l2` ASSUME_TAC THENL
   [SUBGOAL_THEN `&b1 * &u * l1 = &b1 * (&s' - &s) * l2` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(&(u * b2 + b1 * s) - &(b1 * s') = &0) /\ ~(l2 = &0)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM DE_MORGAN_THM; GSYM REAL_ENTIRE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&1 <= abs(&(u * b2 + b1 * s) - &(b1 * s'))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_ABS_SUB_NUM_GE_1 THEN DISCH_TAC THEN
    UNDISCH_TAC `~(&(u * b2 + b1 * s) - &(b1 * s') = &0)` THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&u * abs(&b2 * l2 - &b1 * l1)` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `&u * abs(&b2 * l2 - &b1 * l1) =
                  abs(&(u * b2 + b1 * s) - &(b1 * s')) * abs l2`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM REAL_ABS_NUM] THEN
      REWRITE_TAC[GSYM REAL_ABS_MUL] THEN AP_TERM_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 * a <= b ==> a <= b`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[REAL_ABS_POS; REAL_OF_NUM_LE] THEN
    MAP_EVERY UNDISCH_TAC [`r = r' + u`; `r < R1`] THEN ARITH_TAC]);;

let TL_FINAL_MCOLL_REAL = prove
 (`!l1 l2 b1 b2 R1 r s r' s'.
     1 <= b1 /\ 1 <= b2 /\ r < R1 /\ r' < R1 /\ ~(r = r' /\ s = s') /\
     &r * l1 + &s * l2 = &r' * l1 + &s' * l2 /\
     ~(&b2 * l2 - &b1 * l1 = &0)
     ==> (l2 = &0 /\ ~(l1 = &0) /\ abs l1 <= abs(&b2 * l2 - &b1 * l1)) \/
         (~(l2 = &0) /\ abs l2 <= &R1 * abs(&b2 * l2 - &b1 * l1))`,
  REPEAT STRIP_TAC THEN DISJ_CASES_TAC(ARITH_RULE `r' <= r \/ r <= r':num`)
  THENL
   [MP_TAC(SPECL [`l1:real`; `l2:real`; `b1:num`; `b2:num`; `R1:num`;
                  `r:num`; `s:num`; `r':num`; `s':num`]
     TL_FINAL_MCOLL_REAL_LE);
    MP_TAC(SPECL [`l1:real`; `l2:real`; `b1:num`; `b2:num`; `R1:num`;
                  `r':num`; `s':num`; `r:num`; `s:num`]
     TL_FINAL_MCOLL_REAL_LE)] THEN
  ANTS_TAC THEN ASM_MESON_TAC[]);;

let TL_FINAL_MCOLL = prove
 (`!p1 q1 p2 q2 b1 b2 h1 h2 R1 r s r' s'.
     1 <= p1 /\ 1 <= q1 /\ 1 <= p2 /\ 1 <= q2 /\ 1 <= b1 /\ 1 <= b2 /\
     log(&p1) <= h1 /\ log(&q1) <= h1 /\ log(&p2) <= h2 /\ log(&q2) <= h2 /\
     ~(&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1) = &0) /\
     r < R1 /\ r' < R1 /\ ~(r = r' /\ s = s') /\
     (&p1 / &q1) pow r * (&p2 / &q2) pow s =
     (&p1 / &q1) pow r' * (&p2 / &q2) pow s'
     ==> exp(--(&2 * h1 + &2 * h2 + &R1)) <=
         abs(&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &p1 / &q1 /\ &0 < &p2 / &q2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN
    MAP_EVERY UNDISCH_TAC [`1 <= p1`; `1 <= q1`; `1 <= p2`; `1 <= q2`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= h1 /\ &0 <= h2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[LOG_NUM_BOUND_POS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&r * log(&p1 / &q1) + &s * log(&p2 / &q2) =
    &r' * log(&p1 / &q1) + &s' * log(&p2 / &q2)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`&p1 / &q1`; `&p2 / &q2`; `r:num`; `s:num`]
      LOG_POW_MUL) THEN
    MP_TAC(ISPECL [`&p1 / &q1`; `&p2 / &q2`; `r':num`; `s':num`]
      LOG_POW_MUL) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`log(&p1 / &q1)`; `log(&p2 / &q2)`; `b1:num`; `b2:num`;
                `R1:num`; `r:num`; `s:num`; `r':num`; `s':num`]
    TL_FINAL_MCOLL_REAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(--(&2 * h1))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(log(&p1 / &q1))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LOG_RATIO_LOWER_HEIGHT THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(--(&2 * h2 + &R1))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &R1` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN UNDISCH_TAC `r < R1` THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`exp(--(&2 * h2 + &R1))`;
                `abs(&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1))`; `&R1`]
    REAL_LE_RMUL_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(--(&2 * h2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EXP_NEG_ADD_MUL_LE THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(log(&p2 / &q2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LOG_RATIO_LOWER_HEIGHT THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

let LOG_RATIO_COMBINE = prove
 (`!p1 q1 p2 q2 u v.
     1 <= p1 /\ 1 <= q1 /\ 1 <= p2 /\ 1 <= q2
     ==> &v * log(&p2 / &q2) - &u * log(&p1 / &q1) =
         log(&(p2 EXP v * q1 EXP u) / &(q2 EXP v * p1 EXP u))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &p1 /\ &0 < &q1 /\ &0 < &p2 /\ &0 < &q2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
  ASM_SIMP_TAC[LOG_DIV; LOG_MUL; LOG_POW; REAL_POW_LT; REAL_LT_MUL] THEN
  REAL_ARITH_TAC);;

let TL_FINAL_ACOLL_LT = prove
 (`!p1 q1 p2 q2 b1 b2 h1 h2 R2 S2 r s r' s'.
     1 <= p1 /\ 1 <= q1 /\ 1 <= p2 /\ 1 <= q2 /\ 1 <= b1 /\ 1 <= b2 /\
     log(&p1) <= h1 /\ log(&q1) <= h1 /\ log(&p2) <= h2 /\ log(&q2) <= h2 /\
     ~(&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1) = &0) /\
     r < R2 /\ s < S2 /\ r' < R2 /\ s' < S2 /\ r' < r /\
     r * b2 + s * b1 = r' * b2 + s' * b1
     ==> exp(--(&2 * (&S2 * h2 + &R2 * h1) + &R2)) <=
         abs(&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= h1 /\ &0 <= h2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[LOG_NUM_BOUND_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `r' * b2 < r * b2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LT_MULT_RCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s < s':num` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `s' * b1 <= s * b1` MP_TAC THENL
     [ASM_SIMP_TAC[LE_MULT_RCANCEL]; ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?u v. r = r' + u /\ s' = s + v /\ 1 <= u /\ 1 <= v`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`r - r':num`; `s' - s:num`] THEN
    MAP_EVERY UNDISCH_TAC [`r' < r:num`; `s < s':num`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `u * b2 = v * b1` ASSUME_TAC THENL
   [UNDISCH_TAC `r * b2 + s * b1 = r' * b2 + s' * b1` THEN
    ASM_REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&u * (&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1)) =
    &b1 * (&v * log(&p2 / &q2) - &u * log(&p1 / &q1))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&u * &b2 = &v * &b1` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_EQ]; CONV_TAC REAL_RING];
    ALL_TAC] THEN
  MP_TAC(SPECL [`p1:num`; `q1:num`; `p2:num`; `q2:num`; `u:num`; `v:num`]
    LOG_RATIO_COMBINE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  ABBREV_TAC `X = p2 EXP v * q1 EXP u` THEN
  ABBREV_TAC `Y = q2 EXP v * p1 EXP u` THEN
  SUBGOAL_THEN `1 <= X /\ 1 <= Y` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN
    REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; MULT_EQ_0; EXP_EQ_0] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(X:num = Y)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC
     `&u * (&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1)) =
      &b1 * log(&X / &Y)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&Y / &Y = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_DIV_REFL THEN REWRITE_TAC[REAL_OF_NUM_EQ] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[LOG_1; REAL_MUL_RZERO; REAL_ENTIRE; REAL_OF_NUM_EQ] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&X * &Y <= exp(&2 * (&v * h2 + &u * h1))` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    SUBGOAL_THEN
     `exp(&2 * (&v * h2 + &u * h1)) =
      (exp(&v * h2) * exp(&u * h1)) * (exp(&v * h2) * exp(&u * h1))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_POS] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    SIMP_TAC[REAL_POW_LE; REAL_POS] THEN ASM_SIMP_TAC[NUM_POW_LE_EXP];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(--(&2 * (&v * h2 + &u * h1))) <= abs(log(&X / &Y))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_RATIO_LOWER_PRODUCT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &R2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN UNDISCH_TAC `r < R2` THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`exp(--(&2 * (&S2 * h2 + &R2 * h1) + &R2))`;
                `abs(&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1))`; `&R2`]
    REAL_LE_RMUL_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(--(&2 * (&S2 * h2 + &R2 * h1)))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC EXP_NEG_ADD_MUL_LE THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(--(&2 * (&v * h2 + &u * h1)))` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
    MATCH_MP_TAC(REAL_ARITH
     `a <= c /\ b <= d ==> &2 * (a + b) <= &2 * (c + d)`) THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    MAP_EVERY UNDISCH_TAC
     [`r = r' + u`; `s' = s + v`; `r < R2`; `s' < S2`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(log(&X / &Y))` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&u * abs(&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1))` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `&u * abs(&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1)) =
      &b1 * abs(log(&X / &Y))`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM REAL_ABS_NUM] THEN
      REWRITE_TAC[GSYM REAL_ABS_MUL] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 * a <= b ==> a <= b`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[REAL_ABS_POS; REAL_OF_NUM_LE] THEN
    FIRST_ASSUM ACCEPT_TAC;
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[REAL_ABS_POS; REAL_OF_NUM_LE] THEN
    MAP_EVERY UNDISCH_TAC [`r = r' + u`; `r < R2`] THEN ARITH_TAC]);;

let TL_FINAL_ACOLL = prove
 (`!p1 q1 p2 q2 b1 b2 h1 h2 R2 S2 r s r' s'.
     1 <= p1 /\ 1 <= q1 /\ 1 <= p2 /\ 1 <= q2 /\ 1 <= b1 /\ 1 <= b2 /\
     log(&p1) <= h1 /\ log(&q1) <= h1 /\ log(&p2) <= h2 /\ log(&q2) <= h2 /\
     ~(&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1) = &0) /\
     r < R2 /\ s < S2 /\ r' < R2 /\ s' < S2 /\ ~(r = r' /\ s = s') /\
     r * b2 + s * b1 = r' * b2 + s' * b1
     ==> exp(--(&2 * (&S2 * h2 + &R2 * h1) + &R2)) <=
         abs(&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(r:num = r')` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `r * b2 + s * b1 = r' * b2 + s' * b1` THEN
    ASM_REWRITE_TAC[EQ_ADD_LCANCEL; EQ_MULT_RCANCEL] THEN
    ASM_MESON_TAC[ARITH_RULE `1 <= b1 ==> ~(b1 = 0)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `r' < r \/ r < r':num` DISJ_CASES_TAC THENL
   [ASM_ARITH_TAC;
    MATCH_MP_TAC TL_FINAL_ACOLL_LT THEN
    MAP_EVERY EXISTS_TAC [`r:num`; `s:num`; `r':num`; `s':num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`p1:num`; `q1:num`; `p2:num`; `q2:num`; `b1:num`; `b2:num`;
                `h1:real`; `h2:real`; `R2:num`; `S2:num`;
                `r':num`; `s':num`; `r:num`; `s:num`] TL_FINAL_ACOLL_LT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 8. The main case: both grid maps injective.                               *)
(* ------------------------------------------------------------------------- *)

let NUMSEG_MOD_DIV_LT = prove
 (`!K L i. 1 <= K /\ i IN 1..K * L ==> (i - 1) MOD K < K /\ (i - 1) DIV K < L`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MOD_LT_EQ; RDIV_LT_EQ; ARITH_RULE `1 <= K ==> ~(K = 0)`] THEN
  ASM_ARITH_TAC);;

let TL_FINAL_MAIN_CASE = prove
 (`!p1 q1 p2 q2 b1 b2 h1 h2 K L R1 S1 R2 S2.
     1 <= p1 /\ 1 <= q1 /\ 1 <= p2 /\ 1 <= q2 /\ 1 <= b1 /\ 1 <= b2 /\
     log(&p1) <= h1 /\ log(&q1) <= h1 /\ log(&p2) <= h2 /\ log(&q2) <= h2 /\
     &b1 * abs(log(&p1 / &q1)) <= &b2 * abs(log(&p2 / &q2)) /\
     2 <= K /\ 2 <= L /\ 2 <= R1 /\ 2 <= S1 /\ 1 <= R2 /\ 1 <= S2 /\
     L <= R1 * S1 /\ (K - 1) * L < R2 * S2 /\
     (!r s r' s'. r < R1 /\ s < S1 /\ r' < R1 /\ s' < S1 /\
                  (&p1 / &q1) pow r * (&p2 / &q2) pow s =
                  (&p1 / &q1) pow r' * (&p2 / &q2) pow s'
                  ==> r = r' /\ s = s') /\
     (!r s r' s'. r < R2 /\ s < S2 /\ r' < R2 /\ s' < S2 /\
                  r * b2 + s * b1 = r' * b2 + s' * b1
                  ==> r = r' /\ s = s') /\
     (!l1 l2 x1 x2 Sk Sl Sr Ss.
        abs l1 <= h1 /\ abs l2 <= h2 /\
        &1 <= x1 /\ log x1 <= h1 /\ &1 <= x2 /\ log x2 <= h2 /\
        2 * Sk <= K * L * (K - 1) /\ 2 * Sl <= K * L * (L - 1) /\
        Sr <= K * L * (R1 + R2 - 2) /\ Ss <= K * L * (S1 + S2 - 2)
        ==> &2 pow (K * L) * &(FACT (K * L)) *
            (&3 * &((R1 + R2 - 2) * b2 + (S1 + S2 - 2) * b1)) pow Sk *
            exp(&Sl * &3 * (&(R1 + R2 - 2) * abs l1 +
                             &(S1 + S2 - 2) * abs l2)) *
            x1 pow ((L - 1) * Sr) * x2 pow ((L - 1) * Ss) *
            inv(&3 pow (((K * L) * (K * L - 1)) DIV 2)) < &1)
     ==> exp(--(&1 + &(K * L) * log(&3) +
                log(&(L * ((S1 + S2 - 2) + 1))))) <=
         abs(&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= K /\ 1 <= L /\ 2 <= (R1 + R2 - 2) + 1 /\
                1 <= (S1 + S2 - 2) + 1`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`2 <= K`; `2 <= L`; `2 <= R1`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= L * ((S1 + S2 - 2) + 1)` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `1 * 1 <= x ==> 1 <= x`) THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\r s. (&p1 / &q1) pow r * (&p2 / &q2) pow s`;
                 `R1:num`; `S1:num`] CARD_IMAGE_INJ_GRID) THEN
  BETA_TAC THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`\r s. r * b2 + s * b1`; `R2:num`; `S2:num`]
    CARD_IMAGE_INJ_GRID) THEN
  BETA_TAC THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`p1:num`; `q1:num`; `p2:num`; `q2:num`; `b1:num`; `b2:num`;
                `K:num`; `L:num`; `R1:num`; `S1:num`; `R2:num`; `S2:num`]
    TWOLOG_ZERO_MINOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rr:num->num`
   (X_CHOOSE_THEN `ss:num->num` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!i. i IN 1..K * L ==> (i - 1) MOD K < K /\ (i - 1) DIV K < L`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC NUMSEG_MOD_DIV_LT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `2 * nsum(1..K * L) (\i. (i - 1) MOD K) <= K * L * (K - 1) /\
    2 * nsum(1..K * L) (\i. (i - 1) DIV K) <= K * L * (L - 1)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[NSUM_NUMSEG_PRED_MOD; LE_REFL] THEN
    MP_TAC(SPECL [`K:num`; `L:num`] NSUM_NUMSEG_PRED_DIV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j IN 1..K * L
        ==> (rr:num->num) j < (R1 + R2 - 2) + 1 /\
            (ss:num->num) j < (S1 + S2 - 2) + 1`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(rr:num->num) j < R1 + R2 - 1 /\
                  (ss:num->num) j < S1 + S2 - 1`
    MP_TAC THENL
     [UNDISCH_TAC `j IN 1..K * L` THEN SPEC_TAC(`j:num`,`j:num`) THEN
      FIRST_ASSUM ACCEPT_TAC;
      ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `nsum(1..K * L) rr <= K * L * (R1 + R2 - 2) /\
    nsum(1..K * L) ss <= K * L * (S1 + S2 - 2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`rr:num->num`; `K * L`; `(R1 + R2 - 2) + 1`]
        NSUM_NUMSEG_BOUND_LT);
      MP_TAC(ISPECL [`ss:num->num`; `K * L`; `(S1 + S2 - 2) + 1`]
        NSUM_NUMSEG_BOUND_LT)] THEN
    REWRITE_TAC[ADD_SUB; GSYM MULT_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC
     `!j. j IN 1..K * L
          ==> (rr:num->num) j < (R1 + R2 - 2) + 1 /\
              (ss:num->num) j < (S1 + S2 - 2) + 1` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(log(&p1 / &q1)) <= h1 /\ abs(log(&p2 / &q2)) <= h2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LOG_RATIO_ABS_LE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`log(&p1 / &q1)`; `log(&p2 / &q2)`; `&q1:real`; `&q2:real`;
    `nsum(1..K * L) (\i. (i - 1) MOD K)`;
    `nsum(1..K * L) (\i. (i - 1) DIV K)`;
    `nsum(1..K * L) rr`; `nsum(1..K * L) ss`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; DISCH_TAC] THEN
  MP_TAC(SPECL [`p1:num`; `q1:num`; `p2:num`; `q2:num`; `b1:num`; `b2:num`;
                `K:num`; `L:num`; `(R1 + R2 - 2) + 1`; `(S1 + S2 - 2) + 1`;
                `K * L`;
                `\i. (i - 1) MOD K`; `\i. (i - 1) DIV K`;
                `rr:num->num`; `ss:num->num`; `&3`]
    TWOLOG_CORE_PARAMETRIC) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[ADD_SUB] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN CONV_TAC NUM_REDUCE_CONV;
    DISCH_TAC] THEN
  MATCH_MP_TAC TL_FINAL_CORE_TO_BOUND THEN EXISTS_TAC `&b2:real` THEN
  ASM_REWRITE_TAC[REAL_ABS_POS; REAL_OF_NUM_LE]);;

(* ------------------------------------------------------------------------- *)
(* 9. The ordered theorem and the final theorem.                             *)
(* ------------------------------------------------------------------------- *)

let TWOLOG_RATIONAL_ORDERED = prove
 (`!p1 q1 p2 q2 b1 b2 h1 h2.
      1 <= p1 /\ 1 <= q1 /\ 1 <= p2 /\ 1 <= q2 /\ 1 <= b1 /\ 1 <= b2 /\
      &1 <= h1 /\ log(&p1) <= h1 /\ log(&q1) <= h1 /\
      &1 <= h2 /\ log(&p2) <= h2 /\ log(&q2) <= h2 /\
      ~(&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1) = &0) /\
      &b1 * abs(log(&p1 / &q1)) <= &b2 * abs(log(&p2 / &q2))
      ==> exp(--(&40000 * h1 * h2 *
                 max (&10) (max (log(&b1 / h2 + &b2 / h1)) (log(h1 * h2)))
                 pow 2))
          <= abs(&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`h1:real`; `h2:real`; `b1:num`; `b2:num`]
    TWOLOG_PARAMETERS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `B = max (&10) (max (log(&b1 / h2 + &b2 / h1)) (log(h1 * h2)))` THEN
  SUBGOAL_THEN `&10 <= B` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:num` (X_CHOOSE_THEN `L:num`
   (X_CHOOSE_THEN `R1:num` (X_CHOOSE_THEN `S1:num`
   (X_CHOOSE_THEN `R2:num` (X_CHOOSE_THEN `S2:num` STRIP_ASSUME_TAC)))))) THEN
  SUBGOAL_THEN `1 <= K /\ 1 <= L` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`2 <= K`; `2 <= L`] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC
   `!r s r' s'. r < R1 /\ s < S1 /\ r' < R1 /\ s' < S1 /\
                (&p1 / &q1) pow r * (&p2 / &q2) pow s =
                (&p1 / &q1) pow r' * (&p2 / &q2) pow s'
                ==> r = r' /\ s = s'`
  THENL
   [ALL_TAC;
    POP_ASSUM(MP_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`r:num`; `s:num`; `r':num`; `s':num`] THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(--(&2 * h1 + &2 * h2 + &R1))` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
      MATCH_MP_TAC TL_FINAL_DEGEN_M_NUMERIC THEN EXISTS_TAC `R2:num` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC TL_FINAL_MCOLL THEN
      MAP_EVERY EXISTS_TAC [`r:num`; `s:num`; `r':num`; `s':num`] THEN
      ASM_REWRITE_TAC[]]] THEN
  ASM_CASES_TAC
   `!r s r' s'. r < R2 /\ s < S2 /\ r' < R2 /\ s' < S2 /\
                r * b2 + s * b1 = r' * b2 + s' * b1
                ==> r = r' /\ s = s'`
  THENL
   [ALL_TAC;
    POP_ASSUM(MP_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`r:num`; `s:num`; `r':num`; `s':num`] THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(--(&2 * (&S2 * h2 + &R2 * h1) + &R2))` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
      MATCH_MP_TAC TL_FINAL_DEGEN_A_NUMERIC THEN
      MAP_EVERY EXISTS_TAC [`R1:num`; `S1:num`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC TL_FINAL_ACOLL THEN
      MAP_EVERY EXISTS_TAC [`r:num`; `s:num`; `r':num`; `s':num`] THEN
      ASM_REWRITE_TAC[]]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(--(&1 + &(K * L) * log(&3) +
                      log(&(L * ((S1 + S2 - 2) + 1)))))`
  THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
    MATCH_MP_TAC TL_FINAL_MAIN_NUMERIC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC TL_FINAL_MAIN_CASE THEN
    MAP_EVERY EXISTS_TAC [`h1:real`; `h2:real`; `R1:num`; `R2:num`] THEN
    ASM_REWRITE_TAC[]]);;

let TWOLOG_RATIONAL = prove
 (`!p1 q1 p2 q2 b1 b2 h1 h2.
      1 <= p1 /\ 1 <= q1 /\ 1 <= p2 /\ 1 <= q2 /\ 1 <= b1 /\ 1 <= b2 /\
      &1 <= h1 /\ log(&p1) <= h1 /\ log(&q1) <= h1 /\
      &1 <= h2 /\ log(&p2) <= h2 /\ log(&q2) <= h2 /\
      ~(&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1) = &0)
      ==> exp(--(&40000 * h1 * h2 *
                 max (&10) (max (log(&b1 / h2 + &b2 / h1)) (log(h1 * h2)))
                 pow 2))
          <= abs(&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `&b1 * abs(log(&p1 / &q1)) <= &b2 * abs(log(&p2 / &q2))`
  THENL [MATCH_MP_TAC TWOLOG_RATIONAL_ORDERED THEN ASM_REWRITE_TAC[];
         ALL_TAC] THEN
  MP_TAC(SPECL [`p2:num`; `q2:num`; `p1:num`; `q1:num`; `b2:num`; `b1:num`;
                `h2:real`; `h1:real`] TWOLOG_RATIONAL_ORDERED) THEN
  REWRITE_TAC[TL_FINAL_B_SYM] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(MESON[]
   `a = b /\ x = y ==> exp(--a) <= x ==> exp(--b) <= y`) THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_MUL_AC]; REWRITE_TAC[REAL_ABS_SUB]]);;

(* ------------------------------------------------------------------------- *)
(* 10. The linear form b2 log 2 - b1 log 3.                                  *)
(* ------------------------------------------------------------------------- *)

let TL_FINAL_LOG23_NZ = prove
 (`!b1 b2. 1 <= b2 ==> ~(&b2 * log(&2) - &b1 * log(&3) = &0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `log(&2 pow b2) = log(&3 pow b1)` MP_TAC THENL
   [SIMP_TAC[LOG_POW; REAL_ARITH `&0 < &2`; REAL_ARITH `&0 < &3`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[LOG_INJ; REAL_POW_LT; REAL_ARITH `&0 < &2`;
           REAL_ARITH `&0 < &3`] THEN
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_EQ] THEN
  DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN
  REWRITE_TAC[EVEN_EXP; ARITH] THEN ASM_ARITH_TAC);;

let TL_FINAL_LOG23_B = prove
 (`!b1 b2. 1 <= b1 /\ 1 <= b2
           ==> &40000 * log(&3) *
               max (&10) (max (log(&b1 + &b2 / log(&3))) (log(log(&3))))
               pow 2 <=
               &45000 * max (&10) (log(&b1 + &b2)) pow 2`,
  REPEAT STRIP_TAC THEN MP_TAC LOG_3_BOUNDS THEN STRIP_TAC THEN
  SUBGOAL_THEN `log(&b1 + &b2 / log(&3)) <= log(&b1 + &b2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_MONO_LE_IMP THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&1 <= x /\ &0 <= y ==> &0 < x + y`) THEN
      ASM_SIMP_TAC[REAL_OF_NUM_LE; REAL_LE_DIV; REAL_POS;
                   REAL_ARITH `&1 <= x ==> &0 <= x`];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `(y:real) <= z ==> x + y <= x + z`) THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(log(&3)) <= &10` ASSUME_TAC THENL
   [MP_TAC(SPEC `log(&3)` LOG_LE_SUB_1) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `B = max (&10) (max (log(&b1 + &b2 / log(&3))) (log(log(&3))))` THEN
  ABBREV_TAC `M = max (&10) (log(&b1 + &b2))` THEN
  SUBGOAL_THEN `&10 <= B /\ B <= M` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["B"; "M"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `B pow 2 <= M pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&40000 * (&9 / &8) * M pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_LE_POW_2] THEN
    ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let TWOLOG_LOG2_LOG3 = prove
 (`!b1 b2. 1 <= b1 /\ 1 <= b2
           ==> exp(--(&45000 * max (&10) (log(&b1 + &b2)) pow 2)) <=
               abs(&b2 * log(&2) - &b1 * log(&3))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`3`; `1`; `2`; `1`; `b1:num`; `b2:num`; `log(&3)`; `&1`]
    TWOLOG_RATIONAL) THEN
  REWRITE_TAC[REAL_DIV_1; LOG_1; REAL_MUL_RID; REAL_MUL_LID] THEN
  MP_TAC LOG_3_BOUNDS THEN MP_TAC LOG_2_BOUNDS THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[TL_FINAL_LOG23_NZ; REAL_LE_REFL] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(a:real) <= b ==> b <= x ==> a <= x`) THEN
  REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
  MATCH_MP_TAC TL_FINAL_LOG23_B THEN ASM_REWRITE_TAC[]);;

let TWOLOG_LOG2_LOG3_EXISTS = prove
 (`?C. &0 <= C /\ C <= &10 pow 6 /\
       !b1 b2. 1 <= b1 /\ 1 <= b2
               ==> exp(--(C * max (&10) (log(&b1 + &b2)) pow 2)) <=
                   abs(&b2 * log(&2) - &b1 * log(&3))`,
  EXISTS_TAC `&45000` THEN REWRITE_TAC[TWOLOG_LOG2_LOG3] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]);;
