(* ========================================================================= *)
(* The Poisson kernel identity: the sum over all integers n of               *)
(* 1 / ((n + t)^2 + c^2).                                                    *)
(*                                                                           *)
(* Purpose: for c > 0 the sum over all integers n of 1 / ((n + t)^2 + c^2)   *)
(* is (pi / c) sinh(2 pi c) / (cosh(2 pi c) - cos(2 pi t))                   *)
(* (POISSON_KERNEL_SUM, stated with exp and summed in the pairs n,           *)
(* -(n + 1)). This is the identity behind the limit formula at s = 1 of the  *)
(* class number one problem; Baker (Transcendental Number Theory, Ch. 5,     *)
(* sec. 2 and 3) obtains the corresponding Fourier expansion from the        *)
(* integrals of (u^2 + 1)^-s, here no Fourier analysis is needed.            *)
(*                                                                           *)
(* Method: the product formula for the complex sine (CSIN_PRODUCT) at        *)
(* z = pi (t + i c). The squared norms of its partial products are real      *)
(* products of the positive factors                                          *)
(* ((m - t)^2 + c^2) ((m + t)^2 + c^2) / m^4, so their logarithms give a     *)
(* convergent series of functions of c; its termwise derivative              *)
(* 2 c / ((m - t)^2 + c^2) + 2 c / ((m + t)^2 + c^2) converges uniformly on  *)
(* bounded sets of c by the M-test, so termwise differentiation              *)
(* (HAS_REAL_DERIVATIVE_SERIES) and the uniqueness of derivatives identify   *)
(* its sum with the derivative of log(abs(sin z)^2).                         *)
(*                                                                           *)
(* Main results: POISSON_KERNEL_SUM; the symmetric form                      *)
(* POISSON_KERNEL_SUM_SYM (the sum over m >= 1 of the terms at m - t and     *)
(* m + t); POISSON_REAL_SUMS_INTERLACE; helper names POISSON_*.              *)
(*                                                                           *)
(* Uses: Multivariate/gamma.ml (CSIN_PRODUCT),                               *)
(* Multivariate/realanalysis.ml (HAS_REAL_DERIVATIVE_SERIES,                 *)
(* REAL_SERIES_COMPARISON_UNIFORM, REAL_DERIVATIVE_UNIQUE_ATREAL).           *)
(* ========================================================================= *)

needs "Multivariate/gamma.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Elementary facts.                                                         *)
(* ------------------------------------------------------------------------- *)

let POISSON_EXP_ADD_EXP_NEG_GT = prove
 (`!y. ~(y = &0) ==> &2 < exp y + exp(--y)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_EXP_NEG] THEN
  SUBGOAL_THEN `&0 < exp y /\ ~(exp y = &1)` MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_EXP_POS_LT; REAL_EXP_EQ_1]; ALL_TAC] THEN
  SPEC_TAC(`exp y`,`u:real`) THEN GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (u - &1) pow 2 * inv u` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
    REWRITE_TAC[REAL_POW_2; REAL_LT_SQUARE] THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `~(u = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[REAL_FIELD
     `~(u = &0) ==> (u - &1) pow 2 * inv u = u + inv u - &2`] THEN
    REAL_ARITH_TAC]);;

let POISSON_DENOM_POS = prove
 (`!x y. ~(y = &0) ==> &0 < exp y + exp(--y) - &2 * cos x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `y:real` POISSON_EXP_ADD_EXP_NEG_GT) THEN
  MP_TAC(SPEC `x:real` COS_BOUND) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let POISSON_PRODUCT_POW2 = prove
 (`!f s:A->bool. FINITE s ==> product s f pow 2 = product s (\x. f x pow 2)`,
  SIMP_TAC[REAL_POW_2; PRODUCT_MUL]);;

let POISSON_NORM_ONE_SUB_POW2 = prove
 (`!x y. norm(Cx(&1) - (Cx x + ii * Cx y) pow 2) pow 2 =
         ((&1 - x) pow 2 + y pow 2) * ((&1 + x) pow 2 + y pow 2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[COMPLEX_SQNORM; COMPLEX_POW_2; complex_mul; RE_SUB; IM_SUB;
              RE_ADD; IM_ADD; RE; IM; RE_CX; IM_CX; RE_II; IM_II] THEN
  CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* The squared norms of the partial products of CSIN_PRODUCT at              *)
(* z = pi (t + i c), and the series of their logarithms.                     *)
(* ------------------------------------------------------------------------- *)

let POISSON_CSIN_PRODUCT_NORM = prove
 (`!t c. ((\n. pi pow 2 * (t pow 2 + c pow 2) *
               product(1..n) (\m. ((&m - t) pow 2 + c pow 2) *
                                  ((&m + t) pow 2 + c pow 2) / &m pow 4))
          ---> (exp(&2 * pi * c) + exp(--(&2 * pi * c)) -
                &2 * cos(&2 * pi * t)) / &4) sequentially`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `z = Cx(pi * t) + ii * Cx(pi * c)` THEN
  SUBGOAL_THEN `Re z = pi * t /\ Im z = pi * c` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN
    REWRITE_TAC[RE_ADD; IM_ADD; RE_CX; IM_CX; RE_MUL_II; IM_MUL_II] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_NEG] THEN
  MP_TAC(SPEC `z:complex` NORM_CSIN_POW_2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `!n. pi pow 2 * (t pow 2 + c pow 2) *
        product(1..n) (\m. ((&m - t) pow 2 + c pow 2) *
                           ((&m + t) pow 2 + c pow 2) / &m pow 4) =
        norm(z * cproduct(1..n) (\m. Cx(&1) - (z / Cx(pi * &m)) pow 2)) pow 2`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[COMPLEX_NORM_MUL; REAL_POW_MUL] THEN
    SIMP_TAC[NORM_CPRODUCT; FINITE_NUMSEG; POISSON_PRODUCT_POW2] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_ASSOC] THEN BINOP_TAC THENL
     [ASM_REWRITE_TAC[COMPLEX_SQNORM] THEN CONV_TAC REAL_RING;
      MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN
      STRIP_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(&m = &0)` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `z / Cx(pi * &m) = Cx(t / &m) + ii * Cx(c / &m)`
      SUBST1_TAC THENL
       [EXPAND_TAC "z" THEN REWRITE_TAC[CX_MUL; CX_DIV] THEN
        MP_TAC PI_NZ THEN UNDISCH_TAC `~(&m = &0)` THEN
        REWRITE_TAC[GSYM CX_INJ] THEN CONV_TAC COMPLEX_FIELD;
        REWRITE_TAC[POISSON_NORM_ONE_SUB_POW2] THEN
        UNDISCH_TAC `~(&m = &0)` THEN CONV_TAC REAL_FIELD]];
    REWRITE_TAC[REALLIM_COMPLEX; o_DEF; CX_POW; COMPLEX_NORM_POW_2] THEN
    MATCH_MP_TAC LIM_COMPLEX_MUL THEN REWRITE_TAC[LIM_CNJ; CSIN_PRODUCT]]);;

let POISSON_LOG_SERIES = prove
 (`!t c. &0 < c
         ==> ((\m. log((&m - t) pow 2 + c pow 2) +
                   log((&m + t) pow 2 + c pow 2) - &4 * log(&m)) real_sums
              (log((exp(&2 * pi * c) + exp(--(&2 * pi * c)) -
                    &2 * cos(&2 * pi * t)) / &4) -
               log(pi pow 2 * (t pow 2 + c pow 2)))) (from 1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_sums; FROM_INTER_NUMSEG] THEN
  SUBGOAL_THEN `&0 < c pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < pi pow 2 * (t pow 2 + c pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN SIMP_TAC[REAL_POW_LT; PI_POS] THEN
    MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. &0 < (&m - t) pow 2 + c pow 2 /\ &0 < (&m + t) pow 2 + c pow 2`
  ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(SPEC `&m - t:real` REAL_LE_POW_2) THEN
    MP_TAC(SPEC `&m + t:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. 1 <= m
        ==> &0 < ((&m - t) pow 2 + c pow 2) *
                 ((&m + t) pow 2 + c pow 2) / &m pow 4 /\
            log(((&m - t) pow 2 + c pow 2) *
                ((&m + t) pow 2 + c pow 2) / &m pow 4) =
            log((&m - t) pow 2 + c pow 2) +
            log((&m + t) pow 2 + c pow 2) - &4 * log(&m)`
  ASSUME_TAC THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < &m` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &m pow 4` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV; LOG_MUL; LOG_DIV; LOG_POW];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. sum(1..n) (\m. log((&m - t) pow 2 + c pow 2) +
                       log((&m + t) pow 2 + c pow 2) - &4 * log(&m)) =
        log(pi pow 2 * (t pow 2 + c pow 2) *
            product(1..n) (\m. ((&m - t) pow 2 + c pow 2) *
                               ((&m + t) pow 2 + c pow 2) / &m pow 4)) -
        log(pi pow 2 * (t pow 2 + c pow 2))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    SUBGOAL_THEN
     `&0 < product(1..n) (\m. ((&m - t) pow 2 + c pow 2) *
                              ((&m + t) pow 2 + c pow 2) / &m pow 4)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC PRODUCT_POS_LT_NUMSEG THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL
     [`pi pow 2 * (t pow 2 + c pow 2)`;
      `product(1..n) (\m. ((&m - t) pow 2 + c pow 2) *
                          ((&m + t) pow 2 + c pow 2) / &m pow 4)`]
     LOG_MUL) THEN
    ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_ARITH `(a + b) - a:real = b`] THEN
    ASM_SIMP_TAC[LOG_PRODUCT; FINITE_NUMSEG; IN_NUMSEG];
    MATCH_MP_TAC REALLIM_SUB THEN REWRITE_TAC[REALLIM_CONST] THEN
    MATCH_MP_TAC REALLIM_REAL_CONTINUOUS_FUNCTION THEN
    REWRITE_TAC[POISSON_CSIN_PRODUCT_NORM] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_AT_LOG THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 < x / &4`) THEN
    MATCH_MP_TAC POISSON_DENOM_POS THEN
    MP_TAC PI_POS THEN UNDISCH_TAC `&0 < c` THEN
    REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Termwise derivatives in c and their uniform convergence.                  *)
(* ------------------------------------------------------------------------- *)

let POISSON_LOG_TERM_DERIV = prove
 (`!m t x. ~(x = &0)
           ==> ((\y. log((m - t) pow 2 + y pow 2) +
                     log((m + t) pow 2 + y pow 2) - &4 * log m)
                has_real_derivative
                (&2 * x / ((m - t) pow 2 + x pow 2) +
                 &2 * x / ((m + t) pow 2 + x pow 2))) (atreal x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (m - t) pow 2 + x pow 2 /\ &0 < (m + t) pow 2 + x pow 2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `m - t:real` REAL_LE_POW_2) THEN
    MP_TAC(SPEC `m + t:real` REAL_LE_POW_2) THEN
    MP_TAC(SPEC `x:real` REAL_LT_POW_2) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    REAL_DIFF_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_1; real_div] THEN
    REAL_ARITH_TAC]);;

let POISSON_INV_BOUND = prove
 (`!m t c. &0 < m /\ &2 * abs t <= m
           ==> inv((m + t) pow 2 + c pow 2) <= &4 * inv(m pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&4 * inv(m pow 2) = inv((m / &2) pow 2)` SUBST1_TAC THENL
   [SUBGOAL_THEN `~(m = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b /\ &0 <= c ==> a <= b + c`) THEN
  REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
  ASM_REAL_ARITH_TAC);;

let POISSON_DERIV_TERM_BOUND = prove
 (`!m t x b. &0 < m /\ &2 * abs t <= m /\ &0 < x /\ x <= b
             ==> abs(&2 * x / ((m - t) pow 2 + x pow 2) +
                     &2 * x / ((m + t) pow 2 + x pow 2))
                 <= &16 * b * inv(m pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`m:real`; `t:real`; `x:real`] POISSON_INV_BOUND) THEN
  MP_TAC(SPECL [`m:real`; `--t:real`; `x:real`] POISSON_INV_BOUND) THEN
  ASM_REWRITE_TAC[REAL_ABS_NEG; GSYM real_sub] THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= u /\ &0 <= v /\ u <= b * (&4 * w) /\ v <= b * (&4 * w)
    ==> abs(&2 * u + &2 * v) <= &16 * b * w`) THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC REAL_LE_MUL2) THEN TRY(MATCH_MP_TAC REAL_LE_MUL) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ; REAL_LE_REFL] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= a + b`) THEN
  REWRITE_TAC[REAL_LE_POW_2]);;

let POISSON_DERIV_SERIES_UNIFORM = prove
 (`!t b. ?l. !e. &0 < e
                 ==> ?N. !n x. N <= n /\ &0 < x /\ x <= b
                               ==> abs(sum(1..n)
                                         (\m. &2 * x / ((&m - t) pow 2 +
                                                         x pow 2) +
                                              &2 * x / ((&m + t) pow 2 +
                                                         x pow 2)) -
                                       l x) < e`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL
   [`\x m. &2 * x / ((&m - t) pow 2 + x pow 2) +
           &2 * x / ((&m + t) pow 2 + x pow 2)`;
    `\m. &16 * b * inv(&m pow 2)`; `\x. &0 < x /\ x <= b`; `from 1`]
   REAL_SERIES_COMPARISON_UNIFORM) THEN
  REWRITE_TAC[FROM_INTER_NUMSEG] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM real_summable] THEN
      MATCH_MP_TAC REAL_SUMMABLE_LMUL THEN
      MATCH_MP_TAC REAL_SUMMABLE_LMUL THEN
      MATCH_MP_TAC REAL_SUMMABLE_ZETA_INTEGER THEN ARITH_TAC;
      MP_TAC(SPEC `&2 * abs t` REAL_ARCH_SIMPLE) THEN
      DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N + 1` THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `x:real`] THEN
      REWRITE_TAC[IN_FROM] THEN STRIP_TAC THEN
      MATCH_MP_TAC POISSON_DERIV_TERM_BOUND THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&N + &1 <= &n` MP_TAC THENL
       [ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[]]);;

let POISSON_LOG_CSIN_DERIV = prove
 (`!t c. &0 < c
         ==> ((\x. log((exp(&2 * pi * x) + exp(--(&2 * pi * x)) -
                        &2 * cos(&2 * pi * t)) / &4) -
                   log(pi pow 2 * (t pow 2 + x pow 2)))
              has_real_derivative
              (&2 * pi * (exp(&2 * pi * c) - exp(--(&2 * pi * c))) /
               (exp(&2 * pi * c) + exp(--(&2 * pi * c)) -
                &2 * cos(&2 * pi * t)) -
               &2 * c / (t pow 2 + c pow 2))) (atreal c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `&0 < exp(&2 * pi * c) + exp(--(&2 * pi * c)) - &2 * cos(&2 * pi * t)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC POISSON_DENOM_POS THEN
    MP_TAC PI_POS THEN UNDISCH_TAC `&0 < c` THEN
    REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t pow 2 + c pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN
    MP_TAC(SPECL [`c:real`; `2`] REAL_POW_LT) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < pi pow 2` ASSUME_TAC THENL
   [SIMP_TAC[REAL_POW_LT; PI_POS]; ALL_TAC] THEN
  REAL_DIFF_TAC THEN
  ASM_SIMP_TAC[REAL_LT_MUL; REAL_ARITH `&0 < x ==> &0 < x / &4`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_1] THEN
  MAP_EVERY UNDISCH_TAC
   [`&0 < exp(&2 * pi * c) + exp(--(&2 * pi * c)) - &2 * cos(&2 * pi * t)`;
    `&0 < t pow 2 + c pow 2`; `&0 < pi pow 2`] THEN
  CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Termwise differentiation: the symmetric partial sums over 1 <= m.         *)
(* ------------------------------------------------------------------------- *)

let POISSON_KERNEL_SUM_SYM = prove
 (`!t c. &0 < c
         ==> ((\m. inv((&m - t) pow 2 + c pow 2) +
                   inv((&m + t) pow 2 + c pow 2)) real_sums
              (pi / c * (exp(&2 * pi * c) - exp(--(&2 * pi * c))) /
                        (exp(&2 * pi * c) + exp(--(&2 * pi * c)) -
                         &2 * cos(&2 * pi * t)) -
               inv(t pow 2 + c pow 2))) (from 1)`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_TAC `l:real->real`
   (SPECL [`t:real`; `&2 * c`] POISSON_DERIV_SERIES_UNIFORM) THEN
  SUBGOAL_THEN
   `((\m. &2 * c / ((&m - t) pow 2 + c pow 2) +
          &2 * c / ((&m + t) pow 2 + c pow 2)) real_sums l c) (from 1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[real_sums; FROM_INTER_NUMSEG; REALLIM_SEQUENTIALLY] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`real_interval(c / &2,&2 * c)`;
    `\n x. log((&n - t) pow 2 + x pow 2) + log((&n + t) pow 2 + x pow 2) -
           &4 * log(&n)`;
    `\n x. &2 * x / ((&n - t) pow 2 + x pow 2) +
           &2 * x / ((&n + t) pow 2 + x pow 2)`;
    `l:real->real`; `from 1`] HAS_REAL_DERIVATIVE_SERIES) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL;
              FROM_INTER_NUMSEG] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`n:num`; `x:real`] THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MATCH_MP_TAC POISSON_LOG_TERM_DERIV THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `x:real`] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[GSYM GE] THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY EXISTS_TAC
       [`c:real`;
        `log((exp(&2 * pi * c) + exp(--(&2 * pi * c)) -
              &2 * cos(&2 * pi * t)) / &4) -
         log(pi pow 2 * (t pow 2 + c pow 2))`] THEN
      ASM_SIMP_TAC[POISSON_LOG_SERIES] THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_TAC `g:real->real`)] THEN
  SUBGOAL_THEN
   `!x. c / &2 < x /\ x < &2 * c
        ==> g x = log((exp(&2 * pi * x) + exp(--(&2 * pi * x)) -
                       &2 * cos(&2 * pi * t)) / &4) -
                  log(pi pow 2 * (t pow 2 + x pow 2))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SERIES_UNIQUE THEN
    MAP_EVERY EXISTS_TAC
     [`\n. log((&n - t) pow 2 + x pow 2) + log((&n + t) pow 2 + x pow 2) -
           &4 * log(&n)`; `from 1`] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC POISSON_LOG_SERIES THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c / &2 < c /\ c < &2 * c` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(g has_real_derivative l c) (atreal c)` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(g has_real_derivative l c)
      (atreal c within real_interval(c / &2,&2 * c))`
    MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_REAL_OPEN THEN
    ASM_REWRITE_TAC[REAL_OPEN_REAL_INTERVAL; IN_REAL_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `l(c:real) = &2 * pi * (exp(&2 * pi * c) - exp(--(&2 * pi * c))) /
                (exp(&2 * pi * c) + exp(--(&2 * pi * c)) -
                 &2 * cos(&2 * pi * t)) -
                &2 * c / (t pow 2 + c pow 2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
    MAP_EVERY EXISTS_TAC
     [`\x. log((exp(&2 * pi * x) + exp(--(&2 * pi * x)) -
                &2 * cos(&2 * pi * t)) / &4) -
           log(pi pow 2 * (t pow 2 + x pow 2))`; `c:real`] THEN
    ASM_SIMP_TAC[POISSON_LOG_CSIN_DERIV] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    MAP_EVERY EXISTS_TAC [`g:real->real`; `c / &2`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `y:real` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_SUMS_EQ THEN
  EXISTS_TAC
   `\m. inv(&2 * c) * (&2 * c / ((&m - t) pow 2 + c pow 2) +
                       &2 * c / ((&m + t) pow 2 + c pow 2))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pi / c * (exp(&2 * pi * c) - exp(--(&2 * pi * c))) /
             (exp(&2 * pi * c) + exp(--(&2 * pi * c)) -
              &2 * cos(&2 * pi * t)) -
    inv(t pow 2 + c pow 2) = inv(&2 * c) * l c`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC REAL_SERIES_LMUL THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Interlacing the two halves of the sum over the integers.                  *)
(* ------------------------------------------------------------------------- *)

let POISSON_REAL_SUMS_INTERLACE = prove
 (`!f g l. (!n. &0 <= f n) /\ (!n. &0 <= g n) /\
           ((\n. g n + f n) real_sums l) (from 1)
           ==> ((\n. f n + g(n + 1)) real_sums (f 0 + l)) (from 0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?a. (f real_sums a) (from 1)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM real_summable] THEN
    MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
    EXISTS_TAC `\n. (g:num->real) n + (f:num->real) n` THEN CONJ_TAC THENL
     [REWRITE_TAC[real_summable] THEN EXISTS_TAC `l:real` THEN
      ASM_REWRITE_TAC[];
      EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= y ==> abs x <= y + x`) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g real_sums (l - a)) (from 1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_SUMS_EQ THEN
    EXISTS_TAC `\n. ((g:num->real) n + (f:num->real) n) - f n` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `(x + y) - y:real = x`];
      MATCH_MP_TAC REAL_SERIES_SUB THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\n. g(n + 1)) real_sums (l - a)) (from 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_SUMS_REINDEX; ADD_CLAUSES]; ALL_TAC] THEN
  SUBGOAL_THEN `(f real_sums (a + f 0)) (from 0)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:num->real`; `a:real`; `1`; `0`]
     REAL_SUMS_OFFSET_REV) THEN
    ASM_REWRITE_TAC[ARITH; SUM_SING_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:num->real) 0 + l = (a + f 0) + (l - a)` SUBST1_TAC THENL
   [REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_SERIES_ADD THEN ASM_REWRITE_TAC[]]);;

let POISSON_KERNEL_SUM = prove
 (`!t c. &0 < c
        ==> ((\n. inv((&n + t) pow 2 + c pow 2) +
                  inv((t - (&n + &1)) pow 2 + c pow 2)) real_sums
             (pi / c * (exp(&2 * pi * c) - exp(--(&2 * pi * c))) /
                       (exp(&2 * pi * c) + exp(--(&2 * pi * c)) -
                        &2 * cos(&2 * pi * t)))) (from 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\n. inv((&n + t) pow 2 + c pow 2)`;
    `\n. inv((&n - t) pow 2 + c pow 2)`;
    `pi / c * (exp(&2 * pi * c) - exp(--(&2 * pi * c))) /
              (exp(&2 * pi * c) + exp(--(&2 * pi * c)) -
               &2 * cos(&2 * pi * t)) -
     inv(t pow 2 + c pow 2)`] POISSON_REAL_SUMS_INTERLACE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[POISSON_KERNEL_SUM_SYM] THEN
    CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= a + b`) THEN
    REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. (&(n + 1) - t) pow 2 = ((t:real) - (&n + &1)) pow 2`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_LID; REAL_ARITH `a + (v - a):real = v`]);;
