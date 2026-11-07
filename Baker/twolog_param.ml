(* ========================================================================= *)
(* Two logarithms: the numeric parameter choice.                             *)
(*                                                                           *)
(* Purpose: the parameters of the explicit lower bound for linear forms in   *)
(* two logarithms, adapted from Y. Bugeaud, Linear Forms in Logarithms and   *)
(* Applications (EMS 2018), section 11.4. Pure real arithmetic: no           *)
(* determinants are involved. With B the maximum of 10, log of               *)
(* b1 / h2 + b2 / h1 and log of h1 h2, the parameters are                    *)
(*   K = floor of 6000 B h1 h2,       L = floor of 5 B,                      *)
(*   R1 = floor of 4 B h2 plus 1,     S1 = floor of 4 B h1 plus 1,           *)
(*   R2 = floor of 175 B h2 plus 1,   S2 = floor of 175 B h1 plus 1.         *)
(* Route: the product is below 1 iff its logarithm is negative; bound the    *)
(* sums by their maxima, divide by N/2 and compare                           *)
(* 2 log 2 + 2 log N + K log 3 rho0 + 5 L times R h1 + S h2 with N - 1 times *)
(* log 3. All constants come from E_APPROX_32.                               *)
(*                                                                           *)
(* Main results: TWOLOG_PARAMETERS (the parameters satisfy the main          *)
(* hypothesis of TWOLOG_CORE_PARAMETRIC with rho = 3), from TL_PARAM_MAIN    *)
(* (for any B >= 10 dominating both logarithms), TL_PARAM_HYP and            *)
(* TL_PARAM_PRODUCT_LT_1.                                                    *)
(*                                                                           *)
(* Uses: Baker/lemmas.ml (LOG_MUL4), Multivariate/transcendentals.ml         *)
(* (E_APPROX_32), Examples/mangoldt.ml (LOG_2_BOUNDS) and Library/floor.ml   *)
(* (FLOOR_POS).                                                              *)
(* ========================================================================= *)

needs "Baker/lemmas.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Elementary bounds for the logarithm from exp y >= 1 + y.                  *)
(* ------------------------------------------------------------------------- *)

let LOG_LE_EXP = prove
 (`!x y. &0 < x ==> log x <= y - &1 + x / exp y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `log x - y` REAL_EXP_LE_X) THEN
  ASM_SIMP_TAC[REAL_EXP_SUB; EXP_LOG] THEN REAL_ARITH_TAC);;

let LOG_GE_EXP = prove
 (`!x y. &0 < x ==> y + &1 - exp y / x <= log x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `y - log x` REAL_EXP_LE_X) THEN
  ASM_SIMP_TAC[REAL_EXP_SUB; EXP_LOG] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Numerical constants, all derived from E_APPROX_32.                        *)
(* ------------------------------------------------------------------------- *)

let EXP_1_APPROX = prove
 (`&271828 / &100000 <= exp(&1) /\ exp(&1) <= &271829 / &100000`,
  MP_TAC E_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let EXP_NUM_GE_POW = prove
 (`!n. (&271828 / &100000) pow n <= exp(&n)`,
  GEN_TAC THEN
  SUBGOAL_THEN `exp(&n) = exp(&1) pow n` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_N; REAL_MUL_RID]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN
  MP_TAC EXP_1_APPROX THEN REAL_ARITH_TAC);;

let LOG_3_GE = prove
 (`&109 / &100 <= log(&3)`,
  MP_TAC(SPECL [`&3`; `&1`] LOG_GE_EXP) THEN
  MP_TAC EXP_1_APPROX THEN REAL_ARITH_TAC);;

let LOG_537_LE = prove
 (`log(&537) <= &634 / &100`,
  MP_TAC(SPECL [`&537`; `&6`] LOG_LE_EXP) THEN
  SUBGOAL_THEN `&537 / exp(&6) <= &134 / &100` MP_TAC THENL
   [SIMP_TAC[REAL_LE_LDIV_EQ; REAL_EXP_POS_LT] THEN
    MP_TAC(SPEC `6` EXP_NUM_GE_POW) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let LOG_LE_LINEAR = prove
 (`!x. &10 <= x ==> log x <= &24 / &100 * x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `&2`] LOG_LE_EXP) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `x / exp(&2) <= &14 / &100 * x` MP_TAC THENL
   [SIMP_TAC[REAL_LE_LDIV_EQ; REAL_EXP_POS_LT] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&14 / &100 * x) * (&271828 / &100000) pow 2` THEN
    CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[EXP_NUM_GE_POW] THEN
      ASM_REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

let LOG_LE_AFFINE = prove
 (`!x. &0 < x ==> log x <= &9 + x / &22026`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `&10`] LOG_LE_EXP) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> a <= &10 - &1 + y ==> a <= &9 + z`) THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_INV2 THEN
    MP_TAC(SPEC `10` EXP_NUM_GE_POW) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Factorial and triangular numbers.                                         *)
(* ------------------------------------------------------------------------- *)

let LOG_FACT_LE = prove
 (`!n. log(&(FACT n)) <= &n * log(&n)`,
  GEN_TAC THEN REWRITE_TAC[LOG_FACT] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..n) (\d. log(&n))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]]);;

let MULT_PRED_DIV_2 = prove
 (`!n. 2 * ((n * (n - 1)) DIV 2) = n * (n - 1)`,
  GEN_TAC THEN
  SUBGOAL_THEN `EVEN(n * (n - 1))` MP_TAC THENL
   [REWRITE_TAC[EVEN_MULT; EVEN_SUB; ARITH] THEN MESON_TAC[];
    REWRITE_TAC[EVEN_EXISTS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[DIV_MULT; ARITH_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* A product of seven positive reals is below 1 if its logarithm is.         *)
(* ------------------------------------------------------------------------- *)

let LOG_PRODUCT7_LT_1 = prove
 (`!x1 x2 x3 x4 x5 x6 x7:real.
     &0 < x1 /\ &0 < x2 /\ &0 < x3 /\ &0 < x4 /\ &0 < x5 /\ &0 < x6 /\
     &0 < x7 /\
     log x1 + log x2 + log x3 + log x4 + log x5 + log x6 + log x7 < &0
     ==> x1 * x2 * x3 * x4 * x5 * x6 * x7 < &1`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
                       [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC])
   [`&0 < x6 * x7`; `&0 < x5 * x6 * x7`; `&0 < x4 * x5 * x6 * x7`;
    `&0 < x3 * x4 * x5 * x6 * x7`; `&0 < x2 * x3 * x4 * x5 * x6 * x7`;
    `&0 < x1 * x2 * x3 * x4 * x5 * x6 * x7`] THEN
  SUBGOAL_THEN `log(x1 * x2 * x3 * x4 * x5 * x6 * x7) < log(&1)` MP_TAC THENL
   [ASM_SIMP_TAC[LOG_MUL; LOG_1]; ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_MONO_LT; REAL_LT_01]);;

(* ------------------------------------------------------------------------- *)
(* The reduction: the product of TWOLOG_CORE_PARAMETRIC is below 1 as soon   *)
(* as a single inequality between logarithms holds. Here N stands for K L    *)
(* and r, s for R - 1, S - 1.                                                *)
(* ------------------------------------------------------------------------- *)

let TL_PARAM_PRODUCT_LT_1 = prove
 (`!K L N r s b1 b2 h1 h2 l1 l2 q1 q2 Sk Sl Sr Ss.
     1 <= N /\ 1 <= r * b2 + s * b1 /\
     abs(l1:real) <= h1 /\ abs(l2:real) <= h2 /\
     &1 <= q1 /\ log q1 <= h1 /\ &1 <= q2 /\ log q2 <= h2 /\
     2 * Sk <= N * (K - 1) /\ 2 * Sl <= N * (L - 1) /\
     Sr <= N * r /\ Ss <= N * s /\
     &2 * log(&2) + &2 * log(&N) +
     &(K - 1) * log(&3 * &(r * b2 + s * b1)) +
     &5 * &(L - 1) * (&r * h1 + &s * h2) < &(N - 1) * log(&3)
     ==> &2 pow N * &(FACT N) *
         (&3 * &(r * b2 + s * b1)) pow Sk *
         exp(&Sl * &3 * (&r * abs l1 + &s * abs l2)) *
         q1 pow ((L - 1) * Sr) * q2 pow ((L - 1) * Ss) *
         inv(&3 pow ((N * (N - 1)) DIV 2)) < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &3 * &(r * b2 + s * b1)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &1 <= &3 * x`) THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < q1 /\ &0 < q2 /\ &0 <= h1 /\ &0 <= h2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`&1 <= q1`; `&1 <= q2`; `abs(l1:real) <= h1`; `abs(l2:real) <= h2`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC LOG_PRODUCT7_LT_1 THEN
  ASM_SIMP_TAC[REAL_POW_LT; REAL_EXP_POS_LT; REAL_LT_INV_EQ; REAL_OF_NUM_LT;
               FACT_LT; REAL_ARITH `&0 < &2 /\ &0 < &3`;
               REAL_ARITH `&1 <= x ==> &0 < x`] THEN
  ASM_SIMP_TAC[LOG_POW; LOG_EXP; LOG_INV; REAL_POW_LT;
               REAL_ARITH `&0 < &2 /\ &0 < &3`;
               REAL_ARITH `&1 <= x ==> &0 < x`] THEN
  MP_TAC(SPEC `N:num` LOG_FACT_LE) THEN
  SUBGOAL_THEN
   `&2 * (&Sk * log(&3 * &(r * b2 + s * b1))) <=
    (&N * &(K - 1)) * log(&3 * &(r * b2 + s * b1))`
  MP_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[LOG_POS; REAL_OF_NUM_MUL; REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&2 * &Sl) * (&3 * (&r * abs l1 + &s * abs l2)) <=
    (&N * &(L - 1)) * (&3 * (&r * h1 + &s * h2))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_POS];
      ASM_REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE];
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_ABS_POS];
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&((L - 1) * Sr) * log q1 <= (&(L - 1) * &N * &r) * h1 /\
    &((L - 1) * Ss) * log q2 <= (&(L - 1) * &N * &s) * h2`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_POS; LOG_POS; REAL_OF_NUM_MUL; REAL_OF_NUM_LE;
                 LE_MULT_LCANCEL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 * (&((N * (N - 1)) DIV 2) * log(&3)) = (&N * (&N - &1)) * log(&3)`
  MP_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_SUB; MULT_PRED_DIV_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&N * (&2 * log(&2) + &2 * log(&N) +
          &(K - 1) * log(&3 * &(r * b2 + s * b1)) +
          &5 * &(L - 1) * (&r * h1 + &s * h2)) <
    &N * ((&N - &1) * log(&3))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_LMUL THEN
    ASM_SIMP_TAC[REAL_OF_NUM_SUB; REAL_OF_NUM_LT;
                 ARITH_RULE `1 <= n ==> 0 < n`];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Integer parts as natural numbers.                                         *)
(* ------------------------------------------------------------------------- *)

let REAL_NUM_FLOOR = prove
 (`!x. &0 <= x ==> ?n. &n <= x /\ x < &n + &1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FLOOR_POS) THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `n:num` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[FLOOR]);;

let REAL_NUM_CEIL_LT = prove
 (`!x. &0 <= x ==> ?n. x < &n /\ &n <= x + &1`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP REAL_NUM_FLOOR) THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `n + 1` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The logarithm of 3 rho0 is at most 2.9 B.                                 *)
(* ------------------------------------------------------------------------- *)

let TL_PARAM_LOG_A_BOUND = prove
 (`!B h1 h2 b1 b2 r s.
     &10 <= B /\ &1 <= h1 /\ &1 <= h2 /\ 1 <= b1 /\ 1 <= b2 /\
     log(&b1 / h2 + &b2 / h1) <= B /\ log(h1 * h2) <= B /\
     &r <= &179 * B * h2 /\ &s <= &179 * B * h1 /\ 1 <= r * b2 + s * b1
     ==> log(&3 * &(r * b2 + s * b1)) <= &29 / &10 * B`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &b1 /\ &1 <= &b2 /\ &1 <= &(r * b2 + s * b1)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < h1 * h2 /\ &0 < &b1 / h2 + &b2 / h1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `log(&537 * B * (h1 * h2) * (&b1 / h2 + &b2 / h1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LOG_MONO_LE_IMP THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `&537 * B * (h1 * h2) * (&b1 / h2 + &b2 / h1) =
      &3 * ((&179 * B * h2) * &b2 + (&179 * B * h1) * &b1)`
    SUBST1_TAC THENL
     [SUBGOAL_THEN `~(h1 = &0) /\ ~(h2 = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    MATCH_MP_TAC(REAL_ARITH
     `x <= x1 /\ y <= y1 ==> &3 * (x + y) <= &3 * (x1 + y1)`) THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`&537`; `B:real`; `(h1:real) * h2`; `&b1 / h2 + &b2 / h1`]
    LOG_MUL4) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC LOG_537_LE THEN
  MP_TAC(SPEC `B:real` LOG_LE_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The inequality between logarithms for the chosen parameters.              *)
(* ------------------------------------------------------------------------- *)

let TL_PARAM_HYP = prove
 (`!B h1 h2 b1 b2 K L r s.
     &10 <= B /\ &1 <= h1 /\ &1 <= h2 /\ 1 <= b1 /\ 1 <= b2 /\
     log(&b1 / h2 + &b2 / h1) <= B /\ log(h1 * h2) <= B /\
     &6000 * B * h1 * h2 < &K + &1 /\ &K <= &6000 * B * h1 * h2 /\
     &5 * B < &L + &1 /\ &L <= &5 * B /\
     &r <= &179 * B * h2 /\ &s <= &179 * B * h1 /\ 1 <= r * b2 + s * b1
     ==> &2 * log(&2) + &2 * log(&(K * L)) +
         &(K - 1) * log(&3 * &(r * b2 + s * b1)) +
         &5 * &(L - 1) * (&r * h1 + &s * h2) < &(K * L - 1) * log(&3)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= h1 * h2` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&1 * &1 <= x ==> &1 <= x`) THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(B:real) <= B * h1 * h2` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&10 * (B * h1 * h2) <= B * (B * h1 * h2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `1 <= K /\ 1 <= L` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `1 <= K * L` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `1 * 1 <= K * L ==> 1 <= K * L`) THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM REAL_OF_NUM_MUL] THEN
  MP_TAC LOG_2_BOUNDS THEN
  SUBGOAL_THEN `&K * &L <= (&6000 * B * h1 * h2) * (&5 * B)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  MP_TAC(SPEC `&K * &L` LOG_LE_AFFINE) THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    CONJ_TAC THEN MATCH_MP_TAC(ARITH_RULE `1 <= n ==> 0 < n`) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&K - &1) * log(&3 * &(r * b2 + s * b1)) <=
    (&6000 * B * h1 * h2) * (&29 / &10 * B)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[REAL_SUB_LE; REAL_OF_NUM_LE];
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_POS THEN
      MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &1 <= &3 * x`) THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      MP_TAC(SPECL [`B:real`; `h1:real`; `h2:real`; `b1:num`; `b2:num`;
                    `r:num`; `s:num`] TL_PARAM_LOG_A_BOUND) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&L - &1) * (&r * h1 + &s * h2) <= (&5 * B - &1) * (&358 * B * h1 * h2)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[REAL_SUB_LE; REAL_OF_NUM_LE];
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH
       `x <= (&179 * B * h2) * h1 /\ y <= (&179 * B * h1) * h2
        ==> x + y <= &358 * B * h1 * h2`) THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((&6000 * B * h1 * h2 - &1) * (&5 * B - &1) - &1) * (&109 / &100) <=
    (&K * &L - &1) * log(&3)`
  MP_TAC THENL
   [SUBGOAL_THEN
     `&1 * &1 <= (&6000 * B * h1 * h2 - &1) * (&5 * B - &1) /\
      (&6000 * B * h1 * h2 - &1) * (&5 * B - &1) <= &K * &L`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[LOG_3_GE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The parameter choice, for any B >= 10 dominating both logarithms.         *)
(* ------------------------------------------------------------------------- *)

let TL_PARAM_MAIN = prove
 (`!h1 h2 b1 b2 B.
      &1 <= h1 /\ &1 <= h2 /\ 1 <= b1 /\ 1 <= b2 /\
      &10 <= B /\ log(&b1 / h2 + &b2 / h1) <= B /\ log(h1 * h2) <= B
      ==> ?K L R1 S1 R2 S2.
            2 <= K /\ 2 <= L /\ 2 <= R1 /\ 2 <= S1 /\ 1 <= R2 /\ 1 <= S2 /\
            L <= R1 * S1 /\ (K - 1) * L < R2 * S2 /\
            &(K * L) <= &35000 * h1 * h2 * B pow 2 /\
            &(R1 + R2) <= &200 * h2 * B /\
            &(S1 + S2) <= &200 * h1 * B /\
            !l1 l2 q1 q2 Sk Sl Sr Ss.
              abs l1 <= h1 /\ abs l2 <= h2 /\
              &1 <= q1 /\ log q1 <= h1 /\ &1 <= q2 /\ log q2 <= h2 /\
              2 * Sk <= K * L * (K - 1) /\ 2 * Sl <= K * L * (L - 1) /\
              Sr <= K * L * (R1 + R2 - 2) /\ Ss <= K * L * (S1 + S2 - 2)
              ==> &2 pow (K * L) * &(FACT (K * L)) *
                  (&3 * &((R1 + R2 - 2) * b2 + (S1 + S2 - 2) * b1)) pow Sk *
                  exp(&Sl * &3 * (&(R1 + R2 - 2) * abs l1 +
                                   &(S1 + S2 - 2) * abs l2)) *
                  q1 pow ((L - 1) * Sr) * q2 pow ((L - 1) * Ss) *
                  inv(&3 pow (((K * L) * (K * L - 1)) DIV 2)) < &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= h1 * h2` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&1 * &1 <= x ==> &1 <= x`) THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(B:real) <= B * h1 * h2 /\ B <= B * h1 /\ B <= B * h2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&10 * (B * h1 * h2) <= B * (B * h1 * h2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `&6000 * B * h1 * h2` REAL_NUM_FLOOR) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `&5 * B` REAL_NUM_FLOOR) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `&4 * B * h2` REAL_NUM_CEIL_LT) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R1:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `&4 * B * h1` REAL_NUM_CEIL_LT) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `S1:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `&175 * B * h2` REAL_NUM_CEIL_LT) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R2:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `&175 * B * h1` REAL_NUM_CEIL_LT) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `S2:num` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`K:num`; `L:num`; `R1:num`; `S1:num`; `R2:num`; `S2:num`] THEN
  SUBGOAL_THEN
   `2 <= K /\ 2 <= L /\ 2 <= R1 /\ 2 <= S1 /\ 2 <= R2 /\ 2 <= S2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&(R1 + R2 - 2) <= &179 * B * h2 /\ &(S1 + S2 - 2) <= &179 * B * h1`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `2 <= R1 + R2 /\ 2 <= S1 + S2` STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`2 <= R1`; `2 <= S1`] THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM REAL_OF_NUM_ADD] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= (R1 + R2 - 2) * b2 + (S1 + S2 - 2) * b1` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `1 * 1 <= x ==> 1 <= x + y`) THEN
    MATCH_MP_TAC LE_MULT2 THEN
    MAP_EVERY UNDISCH_TAC [`2 <= R1`; `2 <= R2`; `1 <= b2`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&(K - 1) = &K - &1` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
    UNDISCH_TAC `2 <= K` THEN ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `2 <= R2` THEN ARITH_TAC;
    UNDISCH_TAC `2 <= S2` THEN ARITH_TAC;
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_MUL] THEN
    SUBGOAL_THEN `(&4 * B * h2) * (&4 * B * h1) <= &R1 * &S1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_MUL] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(&K - &1) * &L <= (&6000 * B * h1 * h2 - &1) * (&5 * B) /\
      (&175 * B * h2) * (&175 * B * h1) <= &R2 * &S2`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; REAL_POW_2] THEN
    SUBGOAL_THEN `&K * &L <= (&6000 * B * h1 * h2) * (&5 * B)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`l1:real`; `l2:real`; `q1:real`; `q2:real`;
    `Sk:num`; `Sl:num`; `Sr:num`; `Ss:num`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`K:num`; `L:num`; `K * L`; `R1 + R2 - 2`; `S1 + S2 - 2`;
                `b1:num`; `b2:num`; `h1:real`; `h2:real`; `l1:real`;
                `l2:real`; `q1:real`; `q2:real`; `Sk:num`; `Sl:num`;
                `Sr:num`; `Ss:num`] TL_PARAM_PRODUCT_LT_1) THEN
  ANTS_TAC THENL [ALL_TAC; DISCH_THEN ACCEPT_TAC] THEN
  ASM_REWRITE_TAC[GSYM MULT_ASSOC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `2 * 2 <= K * L ==> 1 <= K * L`) THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`B:real`; `h1:real`; `h2:real`; `b1:num`; `b2:num`;
                `K:num`; `L:num`; `R1 + R2 - 2`; `S1 + S2 - 2`]
               TL_PARAM_HYP) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The final statement, with B the maximum of 10 and the two logarithms.     *)
(* ------------------------------------------------------------------------- *)

let TWOLOG_PARAMETERS = prove
 (`!h1 h2 b1 b2.
      &1 <= h1 /\ &1 <= h2 /\ 1 <= b1 /\ 1 <= b2
      ==> ?K L R1 S1 R2 S2.
            2 <= K /\ 2 <= L /\ 2 <= R1 /\ 2 <= S1 /\ 1 <= R2 /\ 1 <= S2 /\
            L <= R1 * S1 /\ (K - 1) * L < R2 * S2 /\
            &(K * L) <= &35000 * h1 * h2 *
              max (&10) (max (log(&b1 / h2 + &b2 / h1)) (log(h1 * h2))) pow 2 /\
            &(R1 + R2) <= &200 * h2 *
              max (&10) (max (log(&b1 / h2 + &b2 / h1)) (log(h1 * h2))) /\
            &(S1 + S2) <= &200 * h1 *
              max (&10) (max (log(&b1 / h2 + &b2 / h1)) (log(h1 * h2))) /\
            !l1 l2 q1 q2 Sk Sl Sr Ss.
              abs l1 <= h1 /\ abs l2 <= h2 /\
              &1 <= q1 /\ log q1 <= h1 /\ &1 <= q2 /\ log q2 <= h2 /\
              2 * Sk <= K * L * (K - 1) /\ 2 * Sl <= K * L * (L - 1) /\
              Sr <= K * L * (R1 + R2 - 2) /\ Ss <= K * L * (S1 + S2 - 2)
              ==> &2 pow (K * L) * &(FACT (K * L)) *
                  (&3 * &((R1 + R2 - 2) * b2 + (S1 + S2 - 2) * b1)) pow Sk *
                  exp(&Sl * &3 * (&(R1 + R2 - 2) * abs l1 +
                                   &(S1 + S2 - 2) * abs l2)) *
                  q1 pow ((L - 1) * Sr) * q2 pow ((L - 1) * Ss) *
                  inv(&3 pow (((K * L) * (K * L - 1)) DIV 2)) < &1`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TL_PARAM_MAIN THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;
