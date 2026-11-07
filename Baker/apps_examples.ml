(* ========================================================================= *)
(* Examples: the Baker theorems applied to specific numbers and to           *)
(* Diophantine equations.                                                    *)
(*                                                                           *)
(* Purpose: instances of the results of Baker/apps.ml (Baker, Transcendental *)
(* Number Theory, Ch. 1-3) and of the Lindemann-Weierstrass theorem of       *)
(* 100/transcendence.ml.                                                     *)
(*                                                                           *)
(* Main results:                                                             *)
(*   - Gelfond-Schneider: LOG_RATIO_TRANSCENDENTAL (log b / log a for        *)
(*     multiplicatively independent a, b; LOG2_3_TRANSCENDENTAL),            *)
(*     LOG_DIV_PI_TRANSCENDENTAL (log a / pi; LOG2_DIV_PI_TRANSCENDENTAL),   *)
(*     EXP_PI_ALGEBRAIC_TRANSCENDENTAL (exp(pi a) for real algebraic a <> 0; *)
(*     EXP_PI_SQRT_TRANSCENDENTAL, EXP_PI_SQRT_163_TRANSCENDENTAL),          *)
(*     II_CPOW_II (i^i = exp(-pi / 2)) and II_CPOW_II_TRANSCENDENTAL;        *)
(*   - Baker Thm 2.4: POW_SQRT_PRODUCT_TRANSCENDENTAL (2^sqrt 2 * 3^sqrt 3)  *)
(*     and EXP_PI_POW_SQRT2_TRANSCENDENTAL (e^pi * 2^sqrt 2);                *)
(*   - S-unit gaps: STORMER_CONSECUTIVE_SMOOTH (finitely many consecutive    *)
(*     S-smooth numbers), LARGEST_PRIME_FACTOR_CONSECUTIVE (the largest      *)
(*     prime factor of n (n + 1) tends to infinity), PILLAI_FINITE           *)
(*     (a^m - b^n = k, k <> 0, has finitely many solutions, from             *)
(*     SUNIT_POW_GAP of Baker/apps.ml) and its case PILLAI_2_3;              *)
(*   - irrationality measures from the Baker-Feldman bound:                  *)
(*     LOG_IRRATIONALITY_MEASURE (log a for algebraic a > 0, a <> 1),        *)
(*     LOG_RATIO_IRRATIONALITY_MEASURE (log b / log a),                      *)
(*     LOG2_3_IRRATIONALITY_MEASURE;                                         *)
(*   - Baker Thm 2.2: INTEGRAL_INV_1_PLUS_CUBE_TRANSCENDENTAL                *)
(*     (integral_0^1 dx / (1 + x^3) = (log 2 + pi / sqrt 3) / 3) and         *)
(*     INTEGRAL_INV_1_PLUS_FOURTH_TRANSCENDENTAL                             *)
(*     (integral_0^1 dx / (1 + x^4) =                                        *)
(*      (pi + 2 log(1 + sqrt 2)) / (4 sqrt 2));                              *)
(*   - Lindemann: CSIN_TRANSCENDENTAL, CCOS_TRANSCENDENTAL,                  *)
(*     CTAN_TRANSCENDENTAL, SIN_COS_TAN_TRANSCENDENTAL, ATN_TRANSCENDENTAL,  *)
(*     ASN_TRANSCENDENTAL, ACS_TRANSCENDENTAL, EXP_ALGEBRAIC_TRANSCENDENTAL, *)
(*     LOG_TRANSCENDENTAL (values at non-zero algebraic arguments, with the  *)
(*     obvious exceptions).                                                  *)
(*                                                                           *)
(* Uses: Baker/apps.ml (BAKER_LOG_COMBINATION_TRANSCENDENTAL,                *)
(* BAKER_POWER_PRODUCT_TRANSCENDENTAL, GELFOND_SCHNEIDER,                    *)
(* GELFOND_SCHNEIDER_CPOW, SUNIT_GAP, SUNIT_POW_GAP,                         *)
(* IRRATIONALITY_MEASURE_LINEAR_FORM), Baker/theorem.ml (BAKER_FELDMAN),     *)
(* Baker/bridge.ml (closure properties of algebraic_number,                  *)
(* ALGEBRAIC_NUMBER_CX_SQRT), Baker/lemmas.ml (LOG_POLY_BOUND,               *)
(* LOG_NUM_GE_HALF, VSUM_DEGREE_1_ROOT); 100/sqrt.ml (IRRATIONAL_SQRT_2,     *)
(* IRRATIONAL_SQRT_NONSQUARE), 100/transcendence.ml (algebraic_number_neg,   *)
(* zero_sum_algebraic_exp_algebraic,                                         *)
(* transcendental_if_exp_nonzero_algebraic) and Multivariate/vectors.ml      *)
(* (VSUM_2).                                                                 *)
(* ========================================================================= *)

needs "Baker/apps.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Small non-squares (square roots of natural numbers are algebraic:         *)
(* ALGEBRAIC_NUMBER_CX_SQRT of Baker/bridge.ml).                             *)
(* ------------------------------------------------------------------------- *)

let IRRATIONAL_SQRT_3 = prove
 (`~rational(sqrt(&3))`,
  DISCH_THEN(X_CHOOSE_TAC `m:num` o MATCH_MP IRRATIONAL_SQRT_NONSQUARE) THEN
  ASM_CASES_TAC `m <= 1` THENL
   [UNDISCH_TAC `3 = m EXP 2` THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
      (ARITH_RULE `m <= 1 ==> m = 0 \/ m = 1`)) THEN
    CONV_TAC NUM_REDUCE_CONV;
    MP_TAC(SPECL [`2`; `m:num`; `2`; `m:num`] LE_MULT2) THEN
    UNDISCH_TAC `3 = m EXP 2` THEN REWRITE_TAC[EXP_2] THEN ASM_ARITH_TAC]);;

let IRRATIONAL_SQRT_6 = prove
 (`~rational(sqrt(&6))`,
  DISCH_THEN(X_CHOOSE_TAC `m:num` o MATCH_MP IRRATIONAL_SQRT_NONSQUARE) THEN
  ASM_CASES_TAC `m <= 2` THENL
   [UNDISCH_TAC `6 = m EXP 2` THEN
    FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
      (ARITH_RULE `m <= 2 ==> m = 0 \/ m = 1 \/ m = 2`)) THEN
    CONV_TAC NUM_REDUCE_CONV;
    MP_TAC(SPECL [`3`; `m:num`; `3`; `m:num`] LE_MULT2) THEN
    UNDISCH_TAC `6 = m EXP 2` THEN REWRITE_TAC[EXP_2] THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Quotients of logarithms: log b / log a is transcendental when a and b are *)
(* multiplicatively independent; e.g. log 3 / log 2 (Gelfond-Schneider).     *)
(* ------------------------------------------------------------------------- *)

let LOG_RATIO_IRRATIONAL = prove
 (`!a b. 2 <= a /\ 2 <= b /\ (!m n. a EXP m = b EXP n ==> m = 0 /\ n = 0)
         ==> ~rational(log(&b) / log(&a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < log(&a) /\ &0 < log(&b) /\ &0 < &a /\ &0 < &b`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC LOG_POS_LT) THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[rational] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` (X_CHOOSE_THEN `n:real`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `abs n * log(&b) = abs m * log(&a)` MP_TAC THENL
   [SUBGOAL_THEN `n * log(&b) = m * log(&a)` MP_TAC THENL
     [UNDISCH_TAC `log(&b) / log(&a) = m / n` THEN
      UNDISCH_TAC `~(n = &0)` THEN UNDISCH_TAC `&0 < log(&a)` THEN
      CONV_TAC REAL_FIELD;
      DISCH_THEN(MP_TAC o AP_TERM `abs:real->real`) THEN
      SIMP_TAC[REAL_ABS_MUL; REAL_ARITH `&0 < x ==> abs x = x`;
               ASSUME `&0 < log(&a)`; ASSUME `&0 < log(&b)`]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `j:num` o GEN_REWRITE_RULE I [integer] o
    check (fun th -> concl th = `integer m`)) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `k:num` o GEN_REWRITE_RULE I [integer] o
    check (fun th -> concl th = `integer n`)) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[GSYM LOG_POW; LOG_INJ; REAL_POW_LT; ASSUME `&0 < &a`;
           ASSUME `&0 < &b`] THEN
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_EQ] THEN
  DISCH_THEN(MP_TAC o SYM) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ASSUME
    `!m n. a EXP m = b EXP n ==> m = 0 /\ n = 0`)) THEN
  STRIP_TAC THEN UNDISCH_TAC `abs n = &k` THEN
  ASM_REWRITE_TAC[REAL_ABS_ZERO]);;

let LOG_RATIO_TRANSCENDENTAL = prove
 (`!a b. 2 <= a /\ 2 <= b /\ (!m n. a EXP m = b EXP n ==> m = 0 /\ n = 0)
         ==> ~algebraic_number(Cx(log(&b) / log(&a)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LOG_RATIO_IRRATIONAL) THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM STRIP_ASSUME_TAC THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < log(&a) /\ &0 < &a /\ &0 < &b` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC LOG_POS_LT) THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`Cx(log(&a))`; `Cx(log(&b) / log(&a))`] GELFOND_SCHNEIDER) THEN
  REWRITE_TAC[GSYM CX_MUL; GSYM CX_EXP; CX_INJ] THEN
  SUBGOAL_THEN `log(&b) / log(&a) * log(&a) = log(&b)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < log(&a)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SIMP_TAC[EXP_LOG; ALGEBRAIC_NUMBER_CX_NUM; REAL_LT_IMP_NZ;
           ASSUME `&0 < &a`; ASSUME `&0 < &b`; ASSUME `&0 < log(&a)`] THEN
  ASM_MESON_TAC[]);;

let EXP_2_3_INDEPENDENT = prove
 (`!m n. 2 EXP m = 3 EXP n ==> m = 0 /\ n = 0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `m = 0` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `EVEN`) THEN
    REWRITE_TAC[EVEN_EXP; ARITH] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN UNDISCH_TAC `2 EXP 0 = 3 EXP n` THEN
  REWRITE_TAC[EXP] THEN DISCH_THEN(MP_TAC o SYM) THEN
  REWRITE_TAC[EXP_EQ_1] THEN ARITH_TAC);;

let LOG2_3_TRANSCENDENTAL = prove
 (`~algebraic_number(Cx(log(&3) / log(&2)))`,
  MATCH_MP_TAC LOG_RATIO_TRANSCENDENTAL THEN
  REWRITE_TAC[EXP_2_3_INDEPENDENT; ARITH]);;

(* ------------------------------------------------------------------------- *)
(* log a / pi is transcendental for algebraic a > 0, a <> 1                  *)
(* (Gelfond-Schneider with base -1 = cexp(ii pi)); e.g. log 2 / pi.          *)
(* ------------------------------------------------------------------------- *)

let LOG_DIV_PI_TRANSCENDENTAL = prove
 (`!a. &0 < a /\ ~(a = &1) /\ algebraic_number(Cx a)
       ==> ~algebraic_number(Cx(log a / pi))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ii * Cx pi`; `--ii * Cx(log a / pi)`] GELFOND_SCHNEIDER) THEN
  REWRITE_TAC[CEXP_II_PI; COMPLEX_ENTIRE; II_NZ; CX_INJ; PI_NZ] THEN
  SUBGOAL_THEN `(--ii * Cx(log a / pi)) * ii * Cx pi = Cx(log a)`
  SUBST1_TAC THENL
   [REWRITE_TAC[CX_DIV] THEN MP_TAC PI_NZ THEN REWRITE_TAC[GSYM CX_INJ] THEN
    MP_TAC COMPLEX_POW_II_2 THEN CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM CX_EXP; EXP_LOG] THEN
  ASM_SIMP_TAC[algebraic_number_neg; ALGEBRAIC_NUMBER_MUL;
               ALGEBRAIC_NUMBER_CX_NUM; algebraic_number_ii] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real` (MP_TAC o AP_TERM `Im` o CONJUNCT2)) THEN
  REWRITE_TAC[COMPLEX_MUL_LNEG; IM_NEG; IM_MUL_II; RE_CX; IM_CX] THEN
  REWRITE_TAC[REAL_NEG_EQ_0; real_div; REAL_ENTIRE; REAL_INV_EQ_0; PI_NZ] THEN
  REWRITE_TAC[GSYM LOG_1] THEN ASM_SIMP_TAC[LOG_INJ; REAL_LT_01]);;

let LOG2_DIV_PI_TRANSCENDENTAL = prove
 (`~algebraic_number(Cx(log(&2) / pi))`,
  MATCH_MP_TAC LOG_DIV_PI_TRANSCENDENTAL THEN
  REWRITE_TAC[ALGEBRAIC_NUMBER_CX_NUM] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* exp(pi a) is transcendental for real algebraic a <> 0                     *)
(* (Gelfond-Schneider with exp(pi a) = (-1)^(-ii a)): e^(pi sqrt 2),         *)
(* e^(pi sqrt 163), i^i.                                                     *)
(* ------------------------------------------------------------------------- *)

let EXP_PI_ALGEBRAIC_TRANSCENDENTAL = prove
 (`!a. algebraic_number(Cx a) /\ ~(a = &0)
       ==> ~algebraic_number(Cx(exp(pi * a)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ii * Cx pi`; `--ii * Cx a`] GELFOND_SCHNEIDER) THEN
  REWRITE_TAC[CEXP_II_PI; COMPLEX_ENTIRE; II_NZ; CX_INJ; PI_NZ] THEN
  SUBGOAL_THEN `(--ii * Cx a) * ii * Cx pi = Cx(pi * a)` SUBST1_TAC THENL
   [REWRITE_TAC[CX_MUL] THEN MP_TAC COMPLEX_POW_II_2 THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM CX_EXP] THEN
  ASM_SIMP_TAC[algebraic_number_neg; ALGEBRAIC_NUMBER_MUL;
               ALGEBRAIC_NUMBER_CX_NUM; algebraic_number_ii] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real` (MP_TAC o AP_TERM `Im` o CONJUNCT2)) THEN
  REWRITE_TAC[COMPLEX_MUL_LNEG; IM_NEG; IM_MUL_II; RE_CX; IM_CX] THEN
  ASM_REAL_ARITH_TAC);;

let EXP_PI_SQRT_TRANSCENDENTAL = prove
 (`!n. ~(n = 0) ==> ~algebraic_number(Cx(exp(pi * sqrt(&n))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `sqrt(&n)` EXP_PI_ALGEBRAIC_TRANSCENDENTAL) THEN
  ASM_REWRITE_TAC[ALGEBRAIC_NUMBER_CX_SQRT; SQRT_EQ_0; REAL_OF_NUM_EQ]);;

let EXP_PI_SQRT_163_TRANSCENDENTAL = prove
 (`~algebraic_number(Cx(exp(pi * sqrt(&163))))`,
  MATCH_MP_TAC EXP_PI_SQRT_TRANSCENDENTAL THEN ARITH_TAC);;

let II_CPOW_II = prove
 (`ii cpow ii = Cx(exp(--(pi / &2)))`,
  REWRITE_TAC[cpow; II_NZ; CLOG_II; CX_EXP; CX_NEG] THEN AP_TERM_TAC THEN
  MP_TAC COMPLEX_POW_II_2 THEN CONV_TAC COMPLEX_RING);;

let II_CPOW_II_TRANSCENDENTAL = prove
 (`~algebraic_number(ii cpow ii)`,
  MATCH_MP_TAC GELFOND_SCHNEIDER_CPOW THEN
  REWRITE_TAC[algebraic_number_ii; II_NZ] THEN CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `Im`) THEN REWRITE_TAC[IM_II; IM_CX] THEN
    REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `q:real` (MP_TAC o AP_TERM `Im` o CONJUNCT2)) THEN
    REWRITE_TAC[IM_II; IM_CX] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Baker Thm 2.4 instances (beyond Gelfond-Schneider):                       *)
(* 2^sqrt 2 * 3^sqrt 3 and e^pi * 2^sqrt 2 are transcendental.               *)
(* ------------------------------------------------------------------------- *)

let SQRT_2_3_INDEPENDENT = prove
 (`!a b c. rational a /\ rational b /\ rational c /\
           a + b * sqrt(&2) + c * sqrt(&3) = &0
           ==> a = &0 /\ b = &0 /\ c = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `sqrt(&2) pow 2 = &2 /\ sqrt(&3) pow 2 = &3 /\
                sqrt(&2) * sqrt(&3) = sqrt(&6) /\ &0 < sqrt(&2) /\
                &0 < sqrt(&3)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SQRT_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SIMP_TAC[SQRT_POW_2; REAL_POS; SQRT_POS_LT; REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `a = &0 \/ b = &0` MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_ENTIRE] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC IRRATIONAL_SQRT_2 THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(a + b * sqrt(&2)) pow 2 = &3 * c pow 2` ASSUME_TAC THENL
     [SUBGOAL_THEN `a + b * sqrt(&2) = --(c * sqrt(&3))` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[REAL_POW_NEG; ARITH; REAL_POW_MUL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `sqrt(&2) = (&3 * c pow 2 - a pow 2 - &2 * b pow 2) / (&2 * a * b)`
    SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(a + b * sqrt(&2)) pow 2 = &3 * c pow 2`; `sqrt(&2) pow 2 = &2`;
        `~(a * b = &0)`] THEN
      CONV_TAC REAL_FIELD;
      MATCH_MP_TAC RATIONAL_DIV THEN CONJ_TAC THEN
      TRY(MATCH_MP_TAC RATIONAL_SUB THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[RATIONAL_CLOSED]];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `c = &0` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      MP_TAC IRRATIONAL_SQRT_6 THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `sqrt(&6) = --(&2 * b) / c` SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`a + b * sqrt(&2) + c * sqrt(&3) = &0`; `a = &0`;
          `sqrt(&2) pow 2 = &2`; `sqrt(&2) * sqrt(&3) = sqrt(&6)`;
          `~(c = &0)`] THEN
        CONV_TAC REAL_FIELD;
        ASM_SIMP_TAC[RATIONAL_CLOSED]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `a + b * sqrt(&2) + c * sqrt(&3) = &0` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID; REAL_ADD_RID;
                    REAL_ENTIRE] THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `c = &0` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      MP_TAC IRRATIONAL_SQRT_3 THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `sqrt(&3) = --a / c` SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`a + b * sqrt(&2) + c * sqrt(&3) = &0`; `b = &0`; `~(c = &0)`] THEN
        CONV_TAC REAL_FIELD;
        ASM_SIMP_TAC[RATIONAL_CLOSED]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `a + b * sqrt(&2) + c * sqrt(&3) = &0` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID]]);;

let POW_SQRT_PRODUCT_TRANSCENDENTAL = prove
 (`~algebraic_number(Cx(&2 rpow sqrt(&2) * &3 rpow sqrt(&3)))`,
  MP_TAC(SPECL [`2`; `\r. if r = 1 then Cx(log(&2)) else Cx(log(&3))`;
                `\r. if r = 1 then Cx(sqrt(&2)) else Cx(sqrt(&3))`]
         BAKER_POWER_PRODUCT_TRANSCENDENTAL) THEN
  BETA_TAC THEN REWRITE_TAC[VSUM_2] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `r:num` THEN STRIP_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[GSYM CX_EXP; CX_INJ] THEN
      SIMP_TAC[EXP_LOG; REAL_OF_NUM_LT; ARITH; ALGEBRAIC_NUMBER_CX_NUM] THEN
      MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC LOG_POS_LT THEN
      REAL_ARITH_TAC;
      X_GEN_TAC `r:num` THEN STRIP_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[ALGEBRAIC_NUMBER_CX_SQRT];
      X_GEN_TAC `b:num->real` THEN
      REWRITE_TAC[GSYM CX_MUL; GSYM CX_ADD; CX_INJ] THEN STRIP_TAC THEN
      MP_TAC(SPECL [`(b:num->real) 0`; `(b:num->real) 1`; `(b:num->real) 2`]
                   SQRT_2_3_INDEPENDENT) THEN
      ASM_SIMP_TAC[RATIONAL_INTEGER; LE_0; ARITH] THEN STRIP_TAC THEN
      X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `r = 0 \/ r = 1 \/ r = 2` MP_TAC THENL
       [ASM_ARITH_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[]]];
    SUBGOAL_THEN
     `Cx(&2 rpow sqrt(&2) * &3 rpow sqrt(&3)) =
      cexp(Cx(sqrt(&2)) * Cx(log(&2)) + Cx(sqrt(&3)) * Cx(log(&3)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[rpow; REAL_OF_NUM_LT; ARITH; CX_EXP; CX_MUL; CEXP_ADD];
      REWRITE_TAC[]]]);;

let EXP_PI_POW_SQRT2_TRANSCENDENTAL = prove
 (`~algebraic_number(Cx(exp pi * &2 rpow sqrt(&2)))`,
  MP_TAC(SPECL [`2`; `\r. if r = 1 then ii * Cx pi else Cx(log(&2))`;
                `\r. if r = 1 then --ii else Cx(sqrt(&2))`]
         BAKER_POWER_PRODUCT_TRANSCENDENTAL) THEN
  BETA_TAC THEN REWRITE_TAC[VSUM_2] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `r:num` THEN STRIP_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[CEXP_II_PI; COMPLEX_ENTIRE; II_NZ; CX_INJ; PI_NZ;
                  GSYM CX_EXP] THEN
      SIMP_TAC[algebraic_number_neg; ALGEBRAIC_NUMBER_CX_NUM; EXP_LOG;
               REAL_OF_NUM_LT; ARITH] THEN
      MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC LOG_POS_LT THEN
      REAL_ARITH_TAC;
      X_GEN_TAC `r:num` THEN STRIP_TAC THEN COND_CASES_TAC THEN
      SIMP_TAC[algebraic_number_neg; algebraic_number_ii;
               ALGEBRAIC_NUMBER_CX_SQRT];
      X_GEN_TAC `b:num->real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(fun th -> MP_TAC(AP_TERM `Im` th) THEN
                              MP_TAC(AP_TERM `Re` th)) THEN
      REWRITE_TAC[RE_ADD; IM_ADD; RE_CX; IM_CX; COMPLEX_MUL_RNEG; RE_NEG;
                  IM_NEG; RE_MUL_II; IM_MUL_II; GSYM CX_MUL] THEN
      REWRITE_TAC[REAL_NEG_0; REAL_ADD_LID; REAL_ADD_RID; REAL_NEG_EQ_0] THEN
      DISCH_TAC THEN DISCH_TAC THEN
      MP_TAC(SPECL [`(b:num->real) 0`; `(b:num->real) 2`; `&0`]
                   SQRT_2_3_INDEPENDENT) THEN
      ASM_SIMP_TAC[RATIONAL_INTEGER; LE_0; ARITH; RATIONAL_CLOSED] THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `r = 0 \/ r = 1 \/ r = 2` MP_TAC THENL
       [ASM_ARITH_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[]]];
    SUBGOAL_THEN
     `Cx(exp pi * &2 rpow sqrt(&2)) =
      cexp(--ii * ii * Cx pi + Cx(sqrt(&2)) * Cx(log(&2)))`
    SUBST1_TAC THENL
     [SUBGOAL_THEN `--ii * ii * Cx pi = Cx pi` SUBST1_TAC THENL
       [MP_TAC COMPLEX_POW_II_2 THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
      REWRITE_TAC[rpow; REAL_OF_NUM_LT; ARITH; CX_EXP; CX_MUL; CEXP_ADD];
      REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Stormer theorem (effective form via the S-unit gap): only finitely many   *)
(* consecutive S-smooth numbers; the largest prime factor of n (n + 1)       *)
(* tends to infinity.                                                        *)
(* ------------------------------------------------------------------------- *)

let REAL_GAP_INV = prove
 (`!c x l. &0 < c /\ &0 < l /\ c * x / l <= &1 ==> x <= inv c * l`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x = (c * x / l) * (inv c * l)` SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 < c`; `&0 < l`] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]);;

let STORMER_CONSECUTIVE_SMOOTH = prove
 (`!S. FINITE S /\ (!p. p IN S ==> prime p)
       ==> ?N. !n. (!p. prime p /\ p divides n ==> p IN S) /\
                   (!p. prime p /\ p divides (n + 1) ==> p IN S)
                   ==> n <= N`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP SUNIT_GAP) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `C:num`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`inv c`; `C:num`] LOG_POLY_BOUND) THEN
  DISCH_THEN(X_CHOOSE_TAC `M:real`) THEN
  MP_TAC(SPEC `M:real` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N + 2` THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  ASM_CASES_TAC `3 <= n` THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `n + 1`] o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `y:num`)) (concl th))) THEN
  ASM_REWRITE_TAC[ARITH_RULE `n < n + 1`; GSYM REAL_OF_NUM_ADD;
                  REAL_ADD_SUB] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < log(&n) pow C` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC LOG_POS_LT THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&n <= M` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN CONJ_TAC THENL
     [ASM_ARITH_TAC; MATCH_MP_TAC REAL_GAP_INV THEN ASM_REWRITE_TAC[]];
    UNDISCH_TAC `M <= &N` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD] THEN
    REAL_ARITH_TAC]);;

let LARGEST_PRIME_FACTOR_CONSECUTIVE = prove
 (`!P. ?N. !n. N <= n ==> ?p. prime p /\ P < p /\ p divides n * (n + 1)`,
  GEN_TAC THEN
  MP_TAC(SPEC `{p | prime p /\ p <= P}` STORMER_CONSECUTIVE_SMOOTH) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..P` THEN
      REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
      ARITH_TAC;
      SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N + 1` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    REWRITE_TAC[] THEN EXISTS_TAC `p:num` THEN
    ASM_MESON_TAC[DIVIDES_LMUL; DIVIDES_RMUL];
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Pillai equation a^m - b^n = k (k <> 0) for a, b >= 2: finitely many       *)
(* solutions, from the gap |a^m - b^n| >= c a^m / m^C (a^m <> b^n,           *)
(* SUNIT_POW_GAP of Baker/apps.ml); PILLAI_2_3 is the case 2^m - 3^n = k.    *)
(* ------------------------------------------------------------------------- *)

let REAL_GAP_DIV = prove
 (`!c x y z. &0 < c /\ &0 < y /\ c * x / y <= z ==> x <= z / c * y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x = (c * x / y) * (y / c)` SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 < c`; `&0 < y`] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `z / c * y = z * (y / c)` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_AC]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let PILLAI_FINITE = prove
 (`!a b k. 2 <= a /\ 2 <= b /\ ~(k = &0)
           ==> ?N. !m n. &a pow m - &b pow n = k ==> m <= N /\ n <= N`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:num`; `b:num`] SUNIT_POW_GAP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `C:num`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`abs k / c * &2 pow C`; `C:num`] LOG_POLY_BOUND) THEN
  DISCH_THEN(X_CHOOSE_TAC `M:real`) THEN
  MP_TAC(SPEC `abs M + &a + abs k` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(a EXP m = b EXP n)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `&a pow m - &b pow n = k` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_POW; REAL_SUB_REFL] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &2 <= log(&a) /\ &0 < &a /\ &2 <= &a` STRIP_ASSUME_TAC
  THENL
   [ASM_SIMP_TAC[LOG_NUM_GE_HALF; REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&a pow m <= abs M + &a` ASSUME_TAC THENL
   [ASM_CASES_TAC `2 <= m` THENL
     [ALL_TAC;
      SUBGOAL_THEN `m = 0 \/ m = 1` MP_TAC THENL
       [ASM_ARITH_TAC;
        STRIP_TAC THEN ASM_REWRITE_TAC[real_pow; REAL_POW_1] THEN
        REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC]] THEN
    TRANS_TAC REAL_LE_TRANS `M:real` THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &m pow C /\ &m <= &2 * log(&a pow m)`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[LOG_POW] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
        ASM_ARITH_TAC;
        MP_TAC(SPECL [`&m`; `&1`; `&2 * log(&a)`] REAL_LE_LMUL) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `abs k / c * &m pow C` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_GAP_DIV THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `n:num`] o check (fun th ->
        is_forall(concl th) &&
        can (find_term ((=) `abs:real->real`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_ABS_POS] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      REWRITE_TAC[GSYM REAL_POW_MUL] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      ASM_REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&m < &a pow m /\ &n < &b pow n` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LT] THEN CONJ_TAC THENL
     [TRANS_TAC LTE_TRANS `2 EXP m`; TRANS_TAC LTE_TRANS `2 EXP n`] THEN
    REWRITE_TAC[LT_POW2_REFL] THEN MATCH_MP_TAC EXP_MONO_LE_IMP THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
  UNDISCH_TAC `abs M + &a + abs k <= &N` THEN
  UNDISCH_TAC `&a pow m - &b pow n = k` THEN
  MAP_EVERY UNDISCH_TAC [`&m < &a pow m`; `&n < &b pow n`;
                         `&a pow m <= abs M + &a`] THEN
  REAL_ARITH_TAC);;

let PILLAI_2_3 = prove
 (`!k. ~(k = &0)
       ==> ?N. !m n. &2 pow m - &3 pow n = k ==> m <= N /\ n <= N`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PILLAI_FINITE THEN
  ASM_REWRITE_TAC[ARITH]);;

(* ------------------------------------------------------------------------- *)
(* Irrationality measures: |log a - p/q| >= c / q^C for algebraic a > 0,     *)
(* a <> 1, and |log b / log a - p/q| >= c / q^C (e.g. log2 3), from the      *)
(* Baker-Feldman bound.                                                      *)
(* ------------------------------------------------------------------------- *)

let ALGEBRAIC_NUMBER_CX_RATIONAL = prove
 (`!x. rational x ==> algebraic_number(Cx x)`,
  REWRITE_TAC[rational] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[CX_DIV] THEN MATCH_MP_TAC ALGEBRAIC_NUMBER_DIV THEN
  ASM_SIMP_TAC[ALGEBRAIC_NUMBER_CX_INTEGER]);;

let LOG_IRRATIONAL = prove
 (`!a. &0 < a /\ ~(a = &1) /\ algebraic_number(Cx a) ==> ~rational(log a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `Cx(log a)` transcendental_if_exp_nonzero_algebraic) THEN
  ASM_SIMP_TAC[ALGEBRAIC_NUMBER_CX_RATIONAL; GSYM CX_EXP; EXP_LOG; CX_INJ] THEN
  REWRITE_TAC[GSYM LOG_1] THEN ASM_SIMP_TAC[LOG_INJ; REAL_LT_01]);;

let LOG_IRRATIONALITY_MEASURE = prove
 (`!a. &0 < a /\ ~(a = &1) /\ algebraic_number(Cx a)
       ==> ?c C. &0 < c /\
                 !p q. integer p /\ integer q /\ &1 <= q
                       ==> c / q pow C <= abs(log a - p / q)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IRRATIONALITY_MEASURE_LINEAR_FORM THEN
  MAP_EVERY EXISTS_TAC [`&1`; `abs(log a) + &2`] THEN
  ASM_SIMP_TAC[LOG_IRRATIONAL; REAL_LT_01; REAL_MUL_LID;
               REAL_ARITH `x + &1 <= x + &2`] THEN
  MP_TAC(SPECL [`1`; `\r:num. Cx(log a)`; `1`] BAKER_FELDMAN) THEN
  ASM_SIMP_TAC[GSYM CX_EXP; EXP_LOG] THEN
  DISCH_THEN(X_CHOOSE_TAC `C:num`) THEN EXISTS_TAC `C:num` THEN
  MAP_EVERY X_GEN_TAC [`p:real`; `q:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&2 <= (abs(log a) + &2) * q /\ q <= (abs(log a) + &2) * q`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&2 * &1 <= x ==> &2 <= x`) THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&1 * q <= x ==> q <= x`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`(abs(log a) + &2) * q`; `\j. if j = 0 then Cx(--p) else Cx q`;
    `\j:num. 1`;
    `\j i. if j = 0 then (if i = 0 then p else if i = 1 then &1 else &0)
           else (if i = 0 then --q else if i = 1 then &1 else &0)`]) THEN
  BETA_TAC THEN REWRITE_TAC[VSUM_SING_NUMSEG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `Cx(--p) + Cx q * Cx(log a) = Cx(q * log a - p)`
  SUBST1_TAC THENL
   [REWRITE_TAC[CX_SUB; CX_MUL; CX_NEG] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_CX; CX_INJ] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[ARITH_RULE `j <= 1 <=> j = 0 \/ j = 1`] THEN
  GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN REPEAT COND_CASES_TAC THEN
    SIMP_TAC[INTEGER_CLOSED; REAL_ABS_NUM; ASSUME `integer p`] THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC(SPEC `--p` VSUM_DEGREE_1_ROOT) THEN REWRITE_TAC[REAL_NEG_NEG];
    GEN_TAC THEN REPEAT COND_CASES_TAC THEN
    SIMP_TAC[INTEGER_CLOSED; REAL_ABS_NUM; REAL_ABS_NEG;
             ASSUME `integer q`] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[VSUM_DEGREE_1_ROOT]]);;

let LOG_RATIO_IRRATIONALITY_MEASURE = prove
 (`!a b. 2 <= a /\ 2 <= b /\ (!m n. a EXP m = b EXP n ==> m = 0 /\ n = 0)
         ==> ?c C. &0 < c /\
                   !p q. integer p /\ integer q /\ &1 <= q
                         ==> c / q pow C <= abs(log(&b) / log(&a) - p / q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:num`; `b:num`] LOG_RATIO_IRRATIONAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < log(&a) /\ &0 < &a /\ &0 < &b` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC LOG_POS_LT) THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC IRRATIONALITY_MEASURE_LINEAR_FORM THEN
  MAP_EVERY EXISTS_TAC [`log(&a)`; `abs(log(&b) / log(&a)) + &2`] THEN
  ASM_REWRITE_TAC[REAL_ARITH `x + &1 <= x + &2`] THEN
  MP_TAC(SPECL [`2`; `\r. if r = 1 then Cx(log(&a)) else Cx(log(&b))`; `1`]
               BAKER_FELDMAN) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN GEN_TAC THEN STRIP_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[GSYM CX_EXP] THEN
    SIMP_TAC[EXP_LOG; ALGEBRAIC_NUMBER_CX_NUM; ASSUME `&0 < &a`;
             ASSUME `&0 < &b`];
    DISCH_THEN(X_CHOOSE_TAC `C:num`)] THEN
  EXISTS_TAC `C:num` THEN
  MAP_EVERY X_GEN_TAC [`p:real`; `q:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `&2 <= (abs(log(&b) / log(&a)) + &2) * q /\
    q <= (abs(log(&b) / log(&a)) + &2) * q`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&2 * &1 <= x ==> &2 <= x`) THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&1 * q <= x ==> q <= x`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`(abs(log(&b) / log(&a)) + &2) * q`;
    `\j. if j = 0 then Cx(&0) else if j = 1 then Cx(--p) else Cx q`;
    `\j:num. 1`;
    `\j i. if j = 0 then (if i = 0 then &0 else if i = 1 then &1 else &0)
           else if j = 1
           then (if i = 0 then p else if i = 1 then &1 else &0)
           else (if i = 0 then --q else if i = 1 then &1 else &0)`]) THEN
  BETA_TAC THEN REWRITE_TAC[VSUM_2] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `Cx(&0) + Cx(--p) * Cx(log(&a)) + Cx q * Cx(log(&b)) =
    Cx(log(&a) * (q * log(&b) / log(&a) - p))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM CX_MUL; GSYM CX_ADD; CX_INJ] THEN
    UNDISCH_TAC `&0 < log(&a)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_CX; CX_INJ; REAL_ENTIRE; REAL_ABS_MUL;
              MATCH_MP REAL_LT_IMP_NZ (ASSUME `&0 < log(&a)`);
              MATCH_MP (REAL_ARITH `&0 < x ==> abs x = x`)
                       (ASSUME `&0 < log(&a)`)] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[ARITH_RULE `j <= 2 <=> j = 0 \/ j = 1 \/ j = 2`] THEN
  GEN_TAC THEN DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN REPEAT COND_CASES_TAC THEN
    SIMP_TAC[INTEGER_CLOSED; REAL_ABS_NUM; ASSUME `integer p`] THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC(SPEC `&0` VSUM_DEGREE_1_ROOT) THEN REWRITE_TAC[REAL_NEG_0];
    GEN_TAC THEN REPEAT COND_CASES_TAC THEN
    SIMP_TAC[INTEGER_CLOSED; REAL_ABS_NUM; ASSUME `integer p`] THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC(SPEC `--p` VSUM_DEGREE_1_ROOT) THEN REWRITE_TAC[REAL_NEG_NEG];
    GEN_TAC THEN REPEAT COND_CASES_TAC THEN
    SIMP_TAC[INTEGER_CLOSED; REAL_ABS_NUM; REAL_ABS_NEG;
             ASSUME `integer q`] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[VSUM_DEGREE_1_ROOT]]);;

let LOG2_3_IRRATIONALITY_MEASURE = prove
 (`?c C. &0 < c /\
         !p q. integer p /\ integer q /\ &1 <= q
               ==> c / q pow C <= abs(log(&3) / log(&2) - p / q)`,
  MATCH_MP_TAC LOG_RATIO_IRRATIONALITY_MEASURE THEN
  REWRITE_TAC[EXP_2_3_INDEPENDENT; ARITH]);;

(* ------------------------------------------------------------------------- *)
(* The classical illustration of Baker theorem:                              *)
(*   integral_0^1 dx / (1 + x^3) = (log 2 + pi / sqrt 3) / 3                 *)
(* is transcendental (a non-zero linear form in log 2 and log(-1) = ii pi    *)
(* with algebraic coefficients, Baker Thm 2.2).                              *)
(* ------------------------------------------------------------------------- *)

let ATN_INV_SQRT3 = prove
 (`atn(&1 / sqrt(&3)) = pi / &6`,
  SUBGOAL_THEN `&1 / sqrt(&3) = tan(pi / &6)` SUBST1_TAC THENL
   [REWRITE_TAC[tan; SIN_PI6; COS_PI6] THEN
    SUBGOAL_THEN `&0 < sqrt(&3)` MP_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    MATCH_MP_TAC TAN_ATN THEN MP_TAC PI_POS THEN REAL_ARITH_TAC]);;

let INTEGRAL_CUBE_DERIVATIVE_IDENTITY = prove
 (`!x s. &0 < &1 + x /\ &0 < x pow 2 - x + &1 /\ &0 < s /\ s pow 2 = &3
         ==> ((&0 + &1) * inv(&1 + x)) / &3 -
             ((&2 * x pow 1 * &1 - &1 + &0) * inv(x pow 2 - x + &1)) / &6 +
             ((&2 * &1 - &0) / s * inv(&1 + ((&2 * x - &1) / s) pow 2)) / s =
             inv(&1 + x pow 3)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 + ((&2 * x - &1) / s) pow 2 = &4 / &3 * (x pow 2 - x + &1)`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 < s`; `s pow 2 = &3`] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 + x pow 3 = (&1 + x) * (x pow 2 - x + &1)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`&0 < &1 + x`; `&0 < x pow 2 - x + &1`; `&0 < s`; `s pow 2 = &3`] THEN
  CONV_TAC REAL_FIELD);;

let INTEGRAL_INV_1_PLUS_CUBE = prove
 (`((\x. inv(&1 + x pow 3)) has_real_integral ((log(&2) + pi / sqrt(&3)) / &3))
   (real_interval[&0,&1])`,
  MP_TAC(ISPECL
   [`\x. log(&1 + x) / &3 - log(x pow 2 - x + &1) / &6 +
         atn((&2 * x - &1) / sqrt(&3)) / sqrt(&3)`;
    `\x. inv(&1 + x pow 3)`; `&0`; `&1`]
   REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  BETA_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&3) /\ sqrt(&3) pow 2 = &3` STRIP_ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_POS; REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_POS; IN_REAL_INTERVAL] THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    SUBGOAL_THEN `&0 < &1 + x /\ &0 < x pow 2 - x + &1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH
         `&0 <= (x - &1 / &2) pow 2 /\
          x pow 2 - x + &1 = (x - &1 / &2) pow 2 + &3 / &4
          ==> &0 < x pow 2 - x + &1`) THEN
        REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(DISCH_ALL(REAL_DIFF_CONV
     `((\x. log(&1 + x) / &3 - log(x pow 2 - x + &1) / &6 +
            atn((&2 * x - &1) / sqrt(&3)) / sqrt(&3))
       has_real_derivative f') (atreal x)`)) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC INTEGRAL_CUBE_DERIVATIVE_IDENTITY THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[LOG_1; real_div; REAL_MUL_LNEG; ATN_NEG] THEN
  REWRITE_TAC[GSYM real_div; ATN_INV_SQRT3] THEN
  UNDISCH_TAC `&0 < sqrt(&3)` THEN CONV_TAC REAL_FIELD);;

let INTEGRAL_INV_1_PLUS_CUBE_TRANSCENDENTAL = prove
 (`real_integral (real_interval[&0,&1]) (\x. inv(&1 + x pow 3)) =
   (log(&2) + pi / sqrt(&3)) / &3 /\
   ~algebraic_number
     (Cx(real_integral (real_interval[&0,&1]) (\x. inv(&1 + x pow 3))))`,
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
    REWRITE_TAC[INTEGRAL_INV_1_PLUS_CUBE];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&3) /\ &0 < log(&2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT; MATCH_MP_TAC LOG_POS_LT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`2`; `\r. if r = 1 then Cx(log(&2)) else ii * Cx pi`;
                `\r. if r = 1 then Cx(&1 / &3)
                     else --ii * Cx(inv(&3 * sqrt(&3)))`]
         BAKER_LOG_COMBINATION_TRANSCENDENTAL) THEN
  BETA_TAC THEN REWRITE_TAC[VSUM_2] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `Cx(&1 / &3) * Cx(log(&2)) + (--ii * Cx(inv(&3 * sqrt(&3)))) * ii * Cx pi =
    Cx((log(&2) + pi / sqrt(&3)) / &3)`
  SUBST1_TAC THENL
   [REWRITE_TAC[CX_DIV; CX_ADD; CX_MUL; CX_INV] THEN
    UNDISCH_TAC `&0 < sqrt(&3)` THEN
    REWRITE_TAC[REAL_ARITH `&0 < x <=> ~(x = &0) /\ &0 <= x`] THEN
    REWRITE_TAC[GSYM CX_INJ] THEN STRIP_TAC THEN
    MP_TAC COMPLEX_POW_II_2 THEN UNDISCH_TAC `~(Cx(sqrt(&3)) = Cx(&0))` THEN
    CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `r:num` THEN STRIP_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[CEXP_II_PI; GSYM CX_EXP] THEN
    SIMP_TAC[EXP_LOG; REAL_OF_NUM_LT; ARITH; ALGEBRAIC_NUMBER_CX_NUM;
             algebraic_number_neg];
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[CX_DIV; CX_INV; CX_MUL] THEN
    SIMP_TAC[ALGEBRAIC_NUMBER_DIV; ALGEBRAIC_NUMBER_MUL; ALGEBRAIC_NUMBER_INV;
             algebraic_number_neg; algebraic_number_ii;
             ALGEBRAIC_NUMBER_CX_NUM; ALGEBRAIC_NUMBER_CX_SQRT];
    REWRITE_TAC[CX_INJ] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN
    MATCH_MP_TAC REAL_LT_DIV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_LT_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[PI_POS]]);;

(* ------------------------------------------------------------------------- *)
(* integral_0^1 dx / (1 + x^4) = (pi + 2 log(1 + sqrt 2)) / (4 sqrt 2) is    *)
(* transcendental (Baker Thm 2.2 with log(-1) = ii pi and log(1 + sqrt 2)).  *)
(* ------------------------------------------------------------------------- *)

let INTEGRAL_FOURTH_DERIVATIVE_IDENTITY = prove
 (`!x s. &0 < x pow 2 + s * x + &1 /\ &0 < x pow 2 - s * x + &1 /\
         &0 < s /\ s pow 2 = &2
         ==> ((s * &1 + &0) * inv(&1 + (s * x + &1) pow 2) +
              (s * &1 - &0) * inv(&1 + (s * x - &1) pow 2)) / (&2 * s) +
             ((&2 * x pow 1 * &1 + s * &1 + &0) * inv(x pow 2 + s * x + &1) -
              (&2 * x pow 1 * &1 - s * &1 + &0) * inv(x pow 2 - s * x + &1)) /
             (&4 * s) =
             inv(&1 + x pow 4)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 + (s * x + &1) pow 2 = &2 * (x pow 2 + s * x + &1) /\
                &1 + (s * x - &1) pow 2 = &2 * (x pow 2 - s * x + &1) /\
                &1 + x pow 4 = (x pow 2 + s * x + &1) * (x pow 2 - s * x + &1)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT CONJ_TAC THEN UNDISCH_TAC `s pow 2 = &2` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`&0 < x pow 2 + s * x + &1`; `&0 < x pow 2 - s * x + &1`; `&0 < s`;
    `s pow 2 = &2`] THEN
  CONV_TAC REAL_FIELD);;

let INTEGRAL_INV_1_PLUS_FOURTH = prove
 (`((\x. inv(&1 + x pow 4)) has_real_integral
    ((pi + &2 * log(&1 + sqrt(&2))) / (&4 * sqrt(&2))))
   (real_interval[&0,&1])`,
  MP_TAC(ISPECL
   [`\x. (atn(sqrt(&2) * x + &1) + atn(sqrt(&2) * x - &1)) / (&2 * sqrt(&2)) +
         (log(x pow 2 + sqrt(&2) * x + &1) -
          log(x pow 2 - sqrt(&2) * x + &1)) / (&4 * sqrt(&2))`;
    `\x. inv(&1 + x pow 4)`; `&0`; `&1`]
   REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  BETA_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&2) /\ sqrt(&2) pow 2 = &2 /\ sqrt(&2) < &2`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_POS; REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
    SIMP_TAC[SQRT_POW_2; REAL_POS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. &0 < x pow 2 + sqrt(&2) * x + &1 /\
                    &0 < x pow 2 - sqrt(&2) * x + &1`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
       `!s. &0 <= (x + s / &2) pow 2 /\ y = (x + s / &2) pow 2 + &1 / &2
            ==> &0 < y`) THEN
      EXISTS_TAC `sqrt(&2)` THEN REWRITE_TAC[REAL_LE_POW_2];
      MATCH_MP_TAC(REAL_ARITH
       `!s. &0 <= (x - s / &2) pow 2 /\ y = (x - s / &2) pow 2 + &1 / &2
            ==> &0 < y`) THEN
      EXISTS_TAC `sqrt(&2)` THEN REWRITE_TAC[REAL_LE_POW_2]] THEN
    UNDISCH_TAC `sqrt(&2) pow 2 = &2` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_POS; IN_REAL_INTERVAL] THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    MP_TAC(DISCH_ALL(REAL_DIFF_CONV
     `((\x. (atn(sqrt(&2) * x + &1) + atn(sqrt(&2) * x - &1)) /
            (&2 * sqrt(&2)) +
            (log(x pow 2 + sqrt(&2) * x + &1) -
             log(x pow 2 - sqrt(&2) * x + &1)) / (&4 * sqrt(&2)))
       has_real_derivative f') (atreal x)`)) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC INTEGRAL_FOURTH_DERIVATIVE_IDENTITY THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `atn(sqrt(&2) * &1 + &1) + atn(sqrt(&2) * &1 - &1) = pi / &2 /\
    atn(sqrt(&2) * &0 + &1) + atn(sqrt(&2) * &0 - &1) = &0`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO; REAL_ADD_LID;
                REAL_SUB_LZERO; ATN_NEG; REAL_ADD_RINV] THEN
    SUBGOAL_THEN `sqrt(&2) - &1 = inv(sqrt(&2) + &1)` SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`&0 < sqrt(&2)`; `sqrt(&2) pow 2 = &2`] THEN
      CONV_TAC REAL_FIELD;
      ASM_SIMP_TAC[ATN_INV; REAL_ARITH `&0 < s ==> &0 < s + &1`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `log(&1 pow 2 + sqrt(&2) * &1 + &1) - log(&1 pow 2 - sqrt(&2) * &1 + &1) =
    &2 * log(&1 + sqrt(&2)) /\
    log(&0 pow 2 + sqrt(&2) * &0 + &1) - log(&0 pow 2 - sqrt(&2) * &0 + &1) =
    &0`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO; REAL_ADD_LID; REAL_SUB_RZERO;
                REAL_SUB_REFL] THEN
    SUBGOAL_THEN `&1 + sqrt(&2) + &1 = (&1 + sqrt(&2)) pow 2 * (&2 - sqrt(&2))`
    SUBST1_TAC THENL
     [UNDISCH_TAC `sqrt(&2) pow 2 = &2` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN `&1 - sqrt(&2) + &1 = &2 - sqrt(&2)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_MUL; LOG_POW; REAL_POW_LT; REAL_SUB_LT;
                 REAL_ARITH `&0 < s ==> &0 < &1 + s`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `&0 < sqrt(&2)` THEN CONV_TAC REAL_FIELD);;

let INTEGRAL_INV_1_PLUS_FOURTH_TRANSCENDENTAL = prove
 (`real_integral (real_interval[&0,&1]) (\x. inv(&1 + x pow 4)) =
   (pi + &2 * log(&1 + sqrt(&2))) / (&4 * sqrt(&2)) /\
   ~algebraic_number
     (Cx(real_integral (real_interval[&0,&1]) (\x. inv(&1 + x pow 4))))`,
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
    REWRITE_TAC[INTEGRAL_INV_1_PLUS_FOURTH];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2) /\ &0 < log(&1 + sqrt(&2))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC;
      DISCH_TAC THEN MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`2`; `\r. if r = 1 then ii * Cx pi
                         else Cx(log(&1 + sqrt(&2)))`;
                `\r. if r = 1 then --ii * Cx(inv(&4 * sqrt(&2)))
                     else Cx(inv(&2 * sqrt(&2)))`]
         BAKER_LOG_COMBINATION_TRANSCENDENTAL) THEN
  BETA_TAC THEN REWRITE_TAC[VSUM_2] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(--ii * Cx(inv(&4 * sqrt(&2)))) * ii * Cx pi +
    Cx(inv(&2 * sqrt(&2))) * Cx(log(&1 + sqrt(&2))) =
    Cx((pi + &2 * log(&1 + sqrt(&2))) / (&4 * sqrt(&2)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[CX_DIV; CX_ADD; CX_MUL; CX_INV] THEN
    SUBGOAL_THEN `~(Cx(sqrt(&2)) = Cx(&0))` MP_TAC THENL
     [REWRITE_TAC[CX_INJ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC COMPLEX_POW_II_2 THEN CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `r:num` THEN STRIP_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[CEXP_II_PI; GSYM CX_EXP] THEN
    ASM_SIMP_TAC[EXP_LOG; REAL_ARITH `&0 < s ==> &0 < &1 + s`;
                 ALGEBRAIC_NUMBER_CX_NUM; algebraic_number_neg] THEN
    REWRITE_TAC[CX_ADD] THEN MATCH_MP_TAC ALGEBRAIC_NUMBER_ADD THEN
    REWRITE_TAC[ALGEBRAIC_NUMBER_CX_NUM; ALGEBRAIC_NUMBER_CX_SQRT];
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[CX_INV; CX_MUL] THEN
    SIMP_TAC[ALGEBRAIC_NUMBER_MUL; ALGEBRAIC_NUMBER_INV; algebraic_number_neg;
             algebraic_number_ii; ALGEBRAIC_NUMBER_CX_NUM;
             ALGEBRAIC_NUMBER_CX_SQRT];
    REWRITE_TAC[CX_INJ] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN
    MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
     [MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Lindemann (from the Lindemann-Weierstrass theorem of 100/transcendence):  *)
(* sin, cos, tan, atn, asn, acs, log and exp of non-zero algebraic numbers   *)
(* (with the obvious exceptions) are transcendental.                         *)
(* ------------------------------------------------------------------------- *)

let LINDEMANN_THREE_TERMS = prove
 (`!u v w a b c.
     algebraic_number u /\ algebraic_number v /\ algebraic_number w /\
     ~(u = v) /\ ~(u = w) /\ ~(v = w) /\
     algebraic_number a /\ algebraic_number b /\ algebraic_number c /\
     a * cexp u + b * cexp v + c * cexp w = Cx(&0)
     ==> a = Cx(&0) /\ b = Cx(&0) /\ c = Cx(&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(v:complex = u) /\ ~(w:complex = u) /\ ~(w:complex = v)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`{u:complex,v,w}`;
                 `\s:complex. if s = u then a else if s = v then b
                              else c:complex`]
                zero_sum_algebraic_exp_algebraic) THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN];
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN X_GEN_TAC `s:complex` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[];
      SIMP_TAC[COMPLEX_RING_SUM; FINITE_INSERT; FINITE_EMPTY] THEN
      SIMP_TAC[VSUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; COMPLEX_VEC_0;
                      COMPLEX_ADD_RID]];
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `u:complex` th) THEN
      MP_TAC(SPEC `v:complex` th) THEN MP_TAC(SPEC `w:complex` th)) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

let II_MUL_DISTINCT = prove
 (`!z. ~(z = Cx(&0))
       ==> ~(ii * z = --ii * z) /\ ~(ii * z = Cx(&0)) /\
           ~(--ii * z = Cx(&0))`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THEN DISCH_TAC THEN
  MP_TAC II_NZ THEN UNDISCH_TAC `~(z = Cx(&0))` THEN REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_RING);;

let CSIN_TRANSCENDENTAL = prove
 (`!z. algebraic_number z /\ ~(z = Cx(&0)) ==> ~algebraic_number(csin z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ii * z`; `--ii * z`; `Cx(&0)`; `Cx(&1)`; `--Cx(&1)`;
                `--(Cx(&2) * ii * csin z)`] LINDEMANN_THREE_TERMS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[ALGEBRAIC_NUMBER_MUL; algebraic_number_neg;
                 algebraic_number_ii; ALGEBRAIC_NUMBER_CX_NUM;
                 II_MUL_DISTINCT] THEN
    REWRITE_TAC[csin; CEXP_0] THEN MP_TAC II_NZ THEN
    CONV_TAC COMPLEX_FIELD;
    REWRITE_TAC[CX_INJ] THEN REAL_ARITH_TAC]);;

let CCOS_TRANSCENDENTAL = prove
 (`!z. algebraic_number z /\ ~(z = Cx(&0)) ==> ~algebraic_number(ccos z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ii * z`; `--ii * z`; `Cx(&0)`; `Cx(&1)`; `Cx(&1)`;
                `--(Cx(&2) * ccos z)`] LINDEMANN_THREE_TERMS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[ALGEBRAIC_NUMBER_MUL; algebraic_number_neg;
                 algebraic_number_ii; ALGEBRAIC_NUMBER_CX_NUM;
                 II_MUL_DISTINCT] THEN
    REWRITE_TAC[ccos; CEXP_0] THEN CONV_TAC COMPLEX_FIELD;
    REWRITE_TAC[CX_INJ] THEN REAL_ARITH_TAC]);;

let CTAN_TRANSCENDENTAL = prove
 (`!z. algebraic_number z /\ ~(z = Cx(&0)) ==> ~algebraic_number(ctan z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(ccos z = Cx(&0))` ASSUME_TAC THENL
   [DISCH_TAC THEN MP_TAC(SPEC `z:complex` CCOS_TRANSCENDENTAL) THEN
    ASM_REWRITE_TAC[ALGEBRAIC_NUMBER_CX_NUM];
    ALL_TAC] THEN
  MP_TAC(SPECL [`ii * z`; `--ii * z`; `Cx(&0)`; `Cx(&1) - ii * ctan z`;
                `--Cx(&1) - ii * ctan z`; `Cx(&0)`] LINDEMANN_THREE_TERMS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[ALGEBRAIC_NUMBER_MUL; algebraic_number_neg;
                 ALGEBRAIC_NUMBER_SUB; algebraic_number_ii;
                 ALGEBRAIC_NUMBER_CX_NUM; II_MUL_DISTINCT] THEN
    UNDISCH_TAC `~(ccos z = Cx(&0))` THEN
    REWRITE_TAC[ctan; csin; ccos; COMPLEX_MUL_LZERO; COMPLEX_ADD_RID] THEN
    MP_TAC II_NZ THEN CONV_TAC COMPLEX_FIELD;
    DISCH_THEN(MP_TAC o MATCH_MP (COMPLEX_RING
     `a - b = Cx(&0) /\ --a - b = Cx(&0) /\ c = Cx(&0)
      ==> Cx(&2) * a = Cx(&0)`)) THEN
    REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ] THEN REAL_ARITH_TAC]);;

let EXP_ALGEBRAIC_TRANSCENDENTAL = prove
 (`!z. algebraic_number z /\ ~(z = Cx(&0)) ==> ~algebraic_number(cexp z)`,
  MESON_TAC[transcendental_if_exp_nonzero_algebraic]);;

let LOG_TRANSCENDENTAL = prove
 (`!a. &0 < a /\ ~(a = &1) /\ algebraic_number(Cx a)
       ==> ~algebraic_number(Cx(log a))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `Cx(log a)` transcendental_if_exp_nonzero_algebraic) THEN
  ASM_SIMP_TAC[GSYM CX_EXP; EXP_LOG; CX_INJ] THEN
  REWRITE_TAC[GSYM LOG_1] THEN ASM_SIMP_TAC[LOG_INJ; REAL_LT_01]);;

let SIN_COS_TAN_TRANSCENDENTAL = prove
 (`!a. algebraic_number(Cx a) /\ ~(a = &0)
       ==> ~algebraic_number(Cx(sin a)) /\ ~algebraic_number(Cx(cos a)) /\
           ~algebraic_number(Cx(tan a))`,
  REWRITE_TAC[CX_SIN; CX_COS; CX_TAN] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(Cx a = Cx(&0))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CX_INJ]; ALL_TAC] THEN
  ASM_SIMP_TAC[CSIN_TRANSCENDENTAL; CCOS_TRANSCENDENTAL;
               CTAN_TRANSCENDENTAL]);;

let ATN_TRANSCENDENTAL = prove
 (`!a. algebraic_number(Cx a) /\ ~(a = &0) ==> ~algebraic_number(Cx(atn a))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `atn a` SIN_COS_TAN_TRANSCENDENTAL) THEN
  ASM_REWRITE_TAC[ATN_TAN] THEN DISCH_TAC THEN
  UNDISCH_TAC `~(a = &0)` THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `tan`) THEN REWRITE_TAC[ATN_TAN; TAN_0]);;

let ASN_TRANSCENDENTAL = prove
 (`!a. algebraic_number(Cx a) /\ ~(a = &0) /\ --(&1) <= a /\ a <= &1
       ==> ~algebraic_number(Cx(asn a))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `asn a` SIN_COS_TAN_TRANSCENDENTAL) THEN
  ASM_SIMP_TAC[SIN_ASN] THEN DISCH_TAC THEN
  UNDISCH_TAC `~(a = &0)` THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `sin`) THEN ASM_SIMP_TAC[SIN_ASN; SIN_0]);;

let ACS_TRANSCENDENTAL = prove
 (`!a. algebraic_number(Cx a) /\ ~(a = &1) /\ --(&1) <= a /\ a <= &1
       ==> ~algebraic_number(Cx(acs a))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `acs a` SIN_COS_TAN_TRANSCENDENTAL) THEN
  ASM_SIMP_TAC[COS_ACS] THEN DISCH_TAC THEN
  UNDISCH_TAC `~(a = &1)` THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `cos`) THEN ASM_SIMP_TAC[COS_ACS; COS_0]);;
