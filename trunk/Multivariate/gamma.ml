(* ========================================================================= *)
(* The real and complex gamma functions and Euler-Mascheroni constant.       *)
(* ========================================================================= *)

needs "Multivariate/cauchy.ml";;

(* ------------------------------------------------------------------------- *)
(* Euler-Macheroni constant.                                                 *)
(* ------------------------------------------------------------------------- *)

let euler_mascheroni = new_definition
  `euler_mascheroni =
   reallim sequentially (\n. sum(1..n) (\k. inv(&k)) - log(&n))`;;

let EULER_MASCHERONI = prove
 (`((\n. sum(1..n) (\k. inv(&k)) - log(&n)) ---> euler_mascheroni)
   sequentially`,
  REWRITE_TAC[euler_mascheroni; reallim] THEN CONV_TAC SELECT_CONV THEN
  SUBGOAL_THEN
   `real_summable (from 1) (\k. inv(&k) + (log(&k) - log(&(k + 1))))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
    EXISTS_TAC `\k. &2 / &k pow 2` THEN CONJ_TAC THENL
     [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_SUMMABLE_LMUL THEN
      MATCH_MP_TAC REAL_SUMMABLE_ZETA_INTEGER THEN REWRITE_TAC[LE_REFL];
      EXISTS_TAC `2` THEN REWRITE_TAC[GE; IN_FROM] THEN
      X_GEN_TAC `n:num` THEN STRIP_TAC THEN
      ONCE_REWRITE_TAC[REAL_ARITH `a + (b - c):real = a - (c - b)`] THEN
      ASM_SIMP_TAC[GSYM LOG_DIV; REAL_OF_NUM_LT; LE_1;
                   ARITH_RULE `0 < n + 1`] THEN
      ASM_SIMP_TAC[GSYM REAL_OF_NUM_ADD; REAL_OF_NUM_LT; LE_1; REAL_FIELD
       `&0 < n ==> (n + &1) / n = &1 + inv(n)`] THEN
      MP_TAC(ISPECL [`1`; `Cx(inv(&n))`] TAYLOR_CLOG)];
    REWRITE_TAC[real_summable; real_sums; FROM_INTER_NUMSEG] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real` THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REALLIM_TRANSFORM) THEN
    REWRITE_TAC[SUM_ADD_NUMSEG; REAL_ARITH
     `(x + y) - (x - z):real = y + z`] THEN
    REWRITE_TAC[SUM_DIFFS; LOG_1; COND_RAND; COND_RATOR] THEN
    REWRITE_TAC[REAL_ARITH `&0 - x + y = --(x - y)`] THEN
    MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
    EXISTS_TAC `\n. &2 / &n` THEN CONJ_TAC THENL
     [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `2` THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      COND_CASES_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
      ASM_SIMP_TAC[REAL_ABS_NEG; GSYM LOG_DIV; REAL_OF_NUM_LT; LE_1;
                   ARITH_RULE `0 < n + 1`] THEN
      ASM_SIMP_TAC[GSYM REAL_OF_NUM_ADD; REAL_OF_NUM_LT; LE_1; REAL_FIELD
       `&0 < n ==> (n + &1) / n = &1 + inv(n)`] THEN
      MP_TAC(ISPECL [`0`; `Cx(inv(&n))`] TAYLOR_CLOG);
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REALLIM_NULL_LMUL THEN
      REWRITE_TAC[REALLIM_1_OVER_N]]] THEN
  REWRITE_TAC[GSYM CX_ADD; VSUM_SING_NUMSEG; COMPLEX_NORM_CX] THEN
  REWRITE_TAC[VSUM_CLAUSES_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NUM; COMPLEX_DIV_1] THEN
  ASM_SIMP_TAC[COMPLEX_POW_1; REAL_INV_LT_1; REAL_OF_NUM_LT;
               ARITH_RULE `1 < n <=> 2 <= n`] THEN
  REWRITE_TAC[COMPLEX_POW_2; COMPLEX_MUL_LNEG; COMPLEX_MUL_LID] THEN
  ASM_SIMP_TAC[COMPLEX_NEG_NEG; GSYM CX_LOG; REAL_LT_ADD; REAL_OF_NUM_LT;
               LE_1; ARITH; REAL_LT_INV_EQ; GSYM CX_SUB] THEN
  REWRITE_TAC[REAL_POW_1; VECTOR_SUB_RZERO] THEN
  REWRITE_TAC[COMPLEX_NORM_CX] THEN REWRITE_TAC[REAL_ABS_SUB] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
  REWRITE_TAC[real_div; REAL_POW_INV] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_ARITH `&1 / &2 <= &1 - &1 / n <=> inv(n) <= inv(&2)`] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Simple-minded estimation of gamma using Euler-Maclaurin summation.        *)
(* ------------------------------------------------------------------------- *)

let LOG2_APPROX_40 = prove
 (`abs(log(&2) - &381061692393 / &549755813888) <= inv(&2 pow 40)`,
  MP_TAC(SPECL [`41`; `Cx(--inv(&2))`] TAYLOR_CLOG) THEN
  SIMP_TAC[GSYM CX_DIV; GSYM CX_POW; GSYM CX_NEG; GSYM CX_ADD; GSYM CX_MUL;
           VSUM_CX; COMPLEX_NORM_CX; GSYM CX_LOG; GSYM CX_SUB;
            REAL_ARITH `&0 < &1 + --inv(&2)`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_ARITH `a * b / c:real = a / c * b`] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_SUM_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[real_div; REAL_MUL_LID] THEN
  SIMP_TAC[LOG_INV; REAL_ARITH `&0 < &2`] THEN REAL_ARITH_TAC);;

let EULER_MASCHERONI_APPROX_32 = prove
 (`abs(euler_mascheroni - &2479122403 / &4294967296) <= inv(&2 pow 32)`,
  let lemma1 = prove
   (`!m n. 1 <= m /\ m <= n
           ==> abs((sum (1..n) (\k. inv(&k)) - log(&n)) -
                   ((sum (1..m - 1) (\k. inv(&k)) - log(&m)) +
                    (inv(&m) + inv(&n)) / &2 +
                    &1 / &12 * (inv(&m pow 2) - inv(&n pow 2)) +
                    -- &1 / &120 * (inv(&m pow 4) - inv(&n pow 4))))
                <= inv(&60 * &m pow 5)`,
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`\k. inv(&k)`; `1:num`; `m - 1`; `n:num`] SUM_COMBINE_R) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= m ==> m - 1 + 1 = m`] THEN
    MP_TAC(ISPECL
     [`\n x. --(&1) pow n * &(FACT n) / x pow (n + 1)`;
      `m:num`; `n:num`; `2`] REAL_EULER_MACLAURIN) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ANTS_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT
      STRIP_TAC THEN REAL_DIFF_TAC THEN
      REWRITE_TAC[REAL_MUL_LZERO; ADD_SUB; REAL_MUL_RID; REAL_SUB_LZERO] THEN
      REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC; REAL_POW_EQ_0;
                  REAL_MUL_LNEG; REAL_MUL_RNEG] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
      ASM_CASES_TAC `x = &0` THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM real_div; REAL_POW_POW] THEN
      ASM_SIMP_TAC[REAL_DIV_POW2_ALT; ARITH_RULE `~((k + 1) * 2 < k)`] THEN
      REWRITE_TAC[ARITH_RULE `(k + 1) * 2 - k = SUC(SUC k)`;
                  ARITH_RULE `(k + 1) + 1 = SUC(SUC k)`] THEN
      REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN
      REWRITE_TAC[REAL_MUL_RNEG; REAL_MUL_LNEG; REAL_MUL_RID] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[real_div] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[GSYM ADD1; FACT; REAL_OF_NUM_MUL; MULT_AC];
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      REWRITE_TAC[real_div; REAL_MUL_LID; real_pow] THEN
      CONV_TAC(ONCE_DEPTH_CONV EXPAND_SUM_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC(ONCE_DEPTH_CONV BERNOULLI_CONV) THEN
      REWRITE_TAC[GSYM(BERNOULLI_CONV `bernoulli 5 x`)] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_LID; REAL_POW_1] THEN
      REWRITE_TAC[real_div; REAL_MUL_LID] THEN DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`\x. log x`; `\x:real. inv x`; `&m`; `&n`]
          REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL; GSYM REAL_OF_NUM_ADD] THEN
      REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
      ASM_REAL_ARITH_TAC;
      DISCH_THEN(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE)] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `&1 / &120 *
      abs(real_integral (real_interval[&m,&n])
                        (\x. bernoulli 5 (frac x) *
                             --(&120 * inv(x pow 6))))` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `b * --(n * inv x):real = --n * b / x`] THEN
    SUBGOAL_THEN
     `(\x. bernoulli 5 (frac x) / x pow 6)
      real_measurable_on real_interval[&m,&n]`
    ASSUME_TAC THENL
     [MATCH_MP_TAC
       REAL_CONTINUOUS_AE_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `integer` THEN
      REWRITE_TAC[REAL_LEBESGUE_MEASURABLE_INTERVAL] THEN
      SIMP_TAC[REAL_NEGLIGIBLE_COUNTABLE; COUNTABLE_INTEGER] THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      REWRITE_TAC[IN_DIFF; IN_REAL_INTERVAL] THEN REWRITE_TAC[IN] THEN
      X_GEN_TAC `x:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
      REAL_DIFFERENTIABLE_TAC THEN ASM_REWRITE_TAC[REAL_POW_EQ_0] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\x. inv(-- &60 * x pow 5)`; `\x. inv(&12 * x pow 6)`;
      `&m`; `&n`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ANTS_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
      SUBGOAL_THEN `~(x = &0)` MP_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
        ASM_REAL_ARITH_TAC;
        CONV_TAC REAL_FIELD];
      REWRITE_TAC[REAL_INV_MUL; REAL_ARITH
       `inv(-- &60) * x - inv(-- &60) * y = (y - x) / &60`] THEN
      REWRITE_TAC[GSYM REAL_INV_MUL] THEN DISCH_TAC] THEN
    SUBGOAL_THEN
     `!x. x IN real_interval[&m,&n]
          ==> abs(bernoulli 5 (frac x) / x pow 6) <= inv(&12 * x pow 6)`
    ASSUME_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[REAL_INV_MUL; real_div; REAL_ABS_MUL] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`5`; `frac x`] BERNOULLI_BOUND) THEN
        SIMP_TAC[IN_REAL_INTERVAL; FLOOR_FRAC; REAL_LT_IMP_LE] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[BERNOULLI_CONV `bernoulli 4 (&0)`] THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[REAL_ARITH `abs x <= x <=> &0 <= x`] THEN
        REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC REAL_POW_LE THEN
        RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\x. bernoulli 5 (frac x) / x pow 6)
      real_integrable_on real_interval[&m,&n]`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
      EXISTS_TAC `\x:real. inv(&12 * x pow 6)` THEN
      ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
      ASM_MESON_TAC[real_integrable_on];
      ASM_SIMP_TAC[REAL_INTEGRAL_LMUL; REAL_ABS_MUL; REAL_MUL_ASSOC]] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_MUL_LID] THEN
    TRANS_TAC REAL_LE_TRANS
     `real_integral (real_interval [&m,&n]) (\x. inv(&12 * x pow 6))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_ABS_BOUND_INTEGRAL THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[real_integrable_on];
      FIRST_ASSUM(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
      REWRITE_TAC[REAL_INV_MUL] THEN
      REWRITE_TAC[REAL_LE_INV_EQ; REAL_ARITH
       `(x - y) / &60 <= inv(&60) * x <=> &0 <= y`] THEN
      SIMP_TAC[REAL_POW_LE; REAL_POS]])
  and lemma2 = prove
   (`!f g l m d e k.
          (f ---> l) sequentially
          ==> (g ---> m) sequentially /\
              eventually (\n. abs(f n - g n) <= d) sequentially /\
              abs(m - k) <= e - d
              ==> abs(l - k) <= e`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MATCH_MP_TAC(REAL_ARITH
     `abs(l - m) <= d ==> abs (m - k) <= e - d ==> abs (l - k) <= e`) THEN
    REWRITE_TAC[REAL_ABS_BOUNDS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LBOUND);
      MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND)] THEN
    EXISTS_TAC `(\n. f n - g n):num->real` THEN
    ASM_SIMP_TAC[REALLIM_SUB; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
       EVENTUALLY_MONO)) THEN
    REAL_ARITH_TAC) in
  MATCH_MP_TAC(MATCH_MP lemma2 EULER_MASCHERONI) THEN
  MATCH_MP_TAC(MESON[]
   `(?a b c m:num. P (a m) (b m) (c m)) ==> ?a b c. P a b c`) THEN
  EXISTS_TAC
    `\m n. (sum(1..m - 1) (\k. inv(&k)) - log(&m)) +
           (inv(&m) + inv(&n)) / &2 +
           &1 / &12 * (inv(&m pow 2) - inv(&n pow 2)) +
           -- &1 / &120 * (inv(&m pow 4) - inv(&n pow 4))` THEN
  EXISTS_TAC
   `\m. (sum(1..m - 1) (\k. inv(&k)) - log(&m)) +
         inv(&m) / &2 +
         &1 / &12 * inv(&m pow 2) +
         -- &1 / &120 * inv(&m pow 4)` THEN
  EXISTS_TAC `\m. inv (&60 * &m pow 5)` THEN REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  MATCH_MP_TAC(MESON[] `(!n. P n) /\ (?n. Q n) ==> (?n. P n /\ Q n)`) THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN
    REPEAT(MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC) THEN
    REWRITE_TAC[REALLIM_CONST] THEN
    REWRITE_TAC[REAL_ARITH `x / &2 = inv(&2) * x`] THEN
    MATCH_MP_TAC REALLIM_LMUL THEN REWRITE_TAC[real_sub] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ADD_RID] THEN
    MATCH_MP_TAC REALLIM_ADD THEN REWRITE_TAC[REALLIM_CONST] THEN
    REWRITE_TAC[REALLIM_NULL_NEG] THEN
    REWRITE_TAC[REALLIM_1_OVER_N] THEN
    MATCH_MP_TAC REALLIM_1_OVER_POW THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  MATCH_MP_TAC(MESON[] `(?a. P a a /\ Q a) ==> ?a. (?b. P a b) /\ Q a`) THEN
  EXISTS_TAC `64` THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma1 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `log(&64) = &6 * log(&2)` SUBST1_TAC THENL
   [SIMP_TAC[GSYM LOG_POW; REAL_ARITH `&0 < &2`] THEN
    AP_TERM_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_SUM_CONV) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MP_TAC LOG2_APPROX_40 THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Start with the log-gamma function. It's otherwise quite tedious to repeat *)
(* essentially the same argument when we want the logarithm of the gamma     *)
(* function, since we can't just take the usual principal value of log.      *)
(* ------------------------------------------------------------------------- *)

let lgamma = new_definition
 `lgamma z = lim sequentially
               (\n. z * clog(Cx(&n)) - clog z -
                    vsum(1..n) (\m. clog((Cx(&m) + z) / Cx(&m))))`;;

let LGAMMA,COMPLEX_DIFFERENTIABLE_AT_LGAMMA = (CONJ_PAIR o prove)
 (`(!z. (!n. ~(z + Cx(&n) = Cx(&0)))
        ==> ((\n. z * clog(Cx(&n)) - clog z -
                  vsum(1..n) (\m. clog((Cx(&m) + z) / Cx(&m))))
             --> lgamma(z)) sequentially) /\
   (!z. (Im z = &0 ==> &0 < Re z) ==> lgamma complex_differentiable at z)`,
  SUBGOAL_THEN `open {z | !n. ~(z + Cx(&n) = Cx(&0))}` ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE `{z | !n. P n z} = UNIV DIFF {z | ?n. ~P n z}`] THEN
    REWRITE_TAC[GSYM closed] THEN MATCH_MP_TAC DISCRETE_IMP_CLOSED THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01; IMP_CONJ] THEN
    REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    SIMP_TAC[COMPLEX_RING `x + y = Cx(&0) <=> x = --y`] THEN
    REWRITE_TAC[COMPLEX_RING `--x - --y:complex = y - x`] THEN
    REWRITE_TAC[COMPLEX_EQ_NEG2; CX_INJ; GSYM CX_SUB; COMPLEX_NORM_CX] THEN
    SIMP_TAC[GSYM REAL_EQ_INTEGERS; INTEGER_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y.  (!n. ~(y + Cx(&n) = Cx(&0)))
         ==> ?d l. &0 < d /\
                   !e. &0 < e
                       ==> ?N. !n z. N <= n /\ z IN cball(y,d)
                                   ==> dist(z * clog(Cx(&n)) -
                                            vsum(1..n)
                                             (\m. clog((Cx(&m) + z) / Cx(&m))),
                                            l z) < e`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
    REWRITE_TAC[OPEN_CONTAINS_CBALL] THEN
    DISCH_THEN(MP_TAC o SPEC `y:complex`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[UNIFORMLY_CONVERGENT_EQ_CAUCHY_ALT] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `summable (from 1)
         (\m. Cx(&2 * ((norm(y:complex) + d) +
                      (norm(y) + d) pow 2)) / Cx(&m) pow 2)`
    MP_TAC THENL
     [REWRITE_TAC[complex_div; COMPLEX_MUL_ASSOC] THEN
      MATCH_MP_TAC SUMMABLE_COMPLEX_LMUL THEN
      MATCH_MP_TAC SUMMABLE_ZETA_INTEGER THEN REWRITE_TAC[LE_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[summable; SERIES_CAUCHY; GE] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `M:num` (LABEL_TAC "M")) THEN
    MP_TAC(SPEC `&2 * (norm(y:complex) + d) + &1` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN
    EXISTS_TAC `MAX (MAX 1 2) (MAX M N)` THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`; `z:complex`] THEN
    REWRITE_TAC[GE; ARITH_RULE `MAX a b <= c <=> a <= c /\ b <= c`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`m + 1`; `n:num`]) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[FROM_INTER_NUMSEG_MAX; ARITH_RULE `MAX 1 (m + 1) = m + 1`] THEN
    REWRITE_TAC[dist] THEN
    SUBGOAL_THEN
     `!n. 1 <= n
          ==> z * clog(Cx(&n)) - vsum(1..n) (\m. clog((Cx(&m) + z) / Cx(&m))) =
              vsum(1..n) (\m. z * (clog(Cx(&(m + 1) - &1)) -
                                   clog(Cx(&m - &1))) -
                              clog((Cx(&m) + z) / Cx(&m))) +
              z * clog(Cx(&0))`
     (fun th -> ASM_SIMP_TAC[th])
    THENL
     [REWRITE_TAC[VSUM_SUB_NUMSEG] THEN
      ASM_SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_NUMSEG; VSUM_DIFFS_ALT] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ARITH `(x + &1) - &1 = x`;
                  REAL_SUB_REFL] THEN
      REPEAT STRIP_TAC THEN CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LET_TRANS) THEN
    SUBGOAL_THEN `1 <= m + 1 /\ m <= n` MP_TAC THENL
     [ASM_ARITH_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP VSUM_COMBINE_R th)])] THEN
    REWRITE_TAC[COMPLEX_RING `(x + a) - ((x + y) + a):complex = --y`] THEN
    REWRITE_TAC[NORM_NEG] THEN MATCH_MP_TAC COMPLEX_NORM_VSUM_BOUND THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `k:num` THEN
    STRIP_TAC THEN REWRITE_TAC[GSYM CX_POW; GSYM CX_DIV; REAL_CX; RE_CX] THEN
    REWRITE_TAC[COMPLEX_RING `z * (a - b) - c:complex = --(z * (b - a) + c)`;
      NORM_NEG; GSYM REAL_OF_NUM_ADD; REAL_ARITH `(x + &1) - &1 = x`] THEN
    SUBGOAL_THEN `1 <= k /\ 1 < k /\ 2 <= k` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `clog(Cx(&k - &1)) - clog(Cx(&k)) = clog(Cx(&1) - inv(Cx(&k)))`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[GSYM CX_LOG; REAL_OF_NUM_LE; REAL_SUB_LT; REAL_INV_LT_1;
                   REAL_ARITH `&2 <= x ==> &0 < x /\ &1 < x /\ &0 < x - &1`;
                   GSYM CX_SUB; GSYM CX_INV; GSYM LOG_DIV] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `2 <= k` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`1`; `z / Cx(&k)`] TAYLOR_CLOG) THEN
    MP_TAC(ISPECL [`1`; `--inv(Cx(&k))`] TAYLOR_CLOG) THEN
    REWRITE_TAC[VSUM_SING_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[GSYM VECTOR_SUB; NORM_NEG] THEN
    REWRITE_TAC[COMPLEX_NORM_INV; COMPLEX_NORM_DIV; COMPLEX_NORM_CX] THEN
    REWRITE_TAC[COMPLEX_POW_NEG; ARITH; REAL_ABS_NUM; COMPLEX_POW_ONE] THEN
    ASM_SIMP_TAC[REAL_INV_LT_1; REAL_OF_NUM_LT; COMPLEX_DIV_1] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; LE_1; COMPLEX_POW_1] THEN
    REWRITE_TAC[REAL_MUL_LID; COMPLEX_MUL_LID] THEN
    DISCH_THEN(MP_TAC o SPEC `norm(z:complex)` o MATCH_MP
      (REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_LMUL)) THEN
    REWRITE_TAC[NORM_POS_LE; GSYM COMPLEX_NORM_MUL] THEN
    SUBGOAL_THEN `norm(z:complex) < &k` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_CBALL]) THEN
      FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl)) THEN
      REPEAT(POP_ASSUM MP_TAC) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD] THEN
      CONV_TAC NORM_ARITH;
      ASM_REWRITE_TAC[COMPLEX_SUB_LDISTRIB]] THEN
    ASM_SIMP_TAC[CX_INJ; REAL_OF_NUM_EQ; LE_1; COMPLEX_FIELD
      `~(k = Cx(&0)) ==> (k + z) / k = Cx(&1) + z / k`] THEN
    MATCH_MP_TAC(NORM_ARITH
     `x' = --y' /\ d + e <= f
      ==> norm(x - x') <= d ==> norm(y - y') <= e
          ==> norm(x + y) <= f`) THEN
    REWRITE_TAC[complex_div; COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG] THEN
    REWRITE_TAC[REAL_POW_DIV; REAL_POW_INV; REAL_ARITH
     `n * inv k / d + n pow 2 / k / e <= (&2 * (x + x pow 2)) / k <=>
      (n * (&1 / d + n / e)) / k <= (x * (&2 + &2 * x)) / k`] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_OF_NUM_LT; LE_1; REAL_POW_LT] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    SUBGOAL_THEN `norm(z:complex) <= norm(y:complex) + d` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_CBALL]) THEN
      CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_CBALL]) THEN
      CONV_TAC NORM_ARITH;
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LE_DIV THEN
      REWRITE_TAC[REAL_SUB_LE; NORM_POS_LE; REAL_POS] THEN
      REWRITE_TAC[REAL_ARITH `inv x = &1 / x`] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1];
      REWRITE_TAC[REAL_ARITH `&2 + &2 * x = &1 * &2 + x * &2`] THEN
      ONCE_REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_REWRITE_TAC[NORM_POS_LE; REAL_POS; REAL_LE_REFL; REAL_LE_INV_EQ] THEN
      REWRITE_TAC[REAL_SUB_LE] THEN
      REWRITE_TAC[REAL_ARITH `inv x = &1 / x`] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
      ASM_REWRITE_TAC[REAL_MUL_LID; REAL_OF_NUM_LE] THEN
      TRY(CONJ_TAC THENL
      [RULE_ASSUM_TAC(REWRITE_RULE
          [GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_ADD]) THEN
       ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
      REWRITE_TAC[real_div; REAL_MUL_LID] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[REAL_ARITH `&1 / &2 <= &1 - x <=> x <= &1 / &2`] THEN
      REWRITE_TAC[real_div; REAL_MUL_LID] THEN REWRITE_TAC[GSYM real_div] THEN
      REWRITE_TAC[REAL_ARITH `inv x = &1 / x`] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1]] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_CBALL]) THEN
    FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl)) THEN
    REPEAT(POP_ASSUM MP_TAC) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD] THEN
    CONV_TAC NORM_ARITH;
    GEN_REWRITE_TAC (LAND_CONV o REDEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
     [`dd:complex->real`; `ll:complex->complex->complex`] THEN
    DISCH_THEN(LABEL_TAC "*")] THEN
  SUBGOAL_THEN
   `!z. (!n. ~(z + Cx(&n) = Cx(&0)))
        ==> ((\n. z * clog(Cx(&n)) -
                  vsum (1..n) (\m. clog((Cx(&m) + z) / Cx(&m)))) --> ll z z)
            sequentially`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN
    ASM_REWRITE_TAC[LIM_SEQUENTIALLY; GSYM SKOLEM_THM] THEN
    MESON_TAC[CENTRE_IN_CBALL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[lgamma; lim] THEN CONV_TAC SELECT_CONV THEN
    EXISTS_TAC `(ll:complex->complex->complex) z z - clog z` THEN
    ONCE_REWRITE_TAC[COMPLEX_RING `w - z - v:complex = (w - v) - z`] THEN
    MATCH_MP_TAC LIM_SUB THEN REWRITE_TAC[LIM_CONST] THEN ASM_MESON_TAC[];
    DISCH_TAC] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!n. ~(z + Cx(&n) = Cx(&0))` ASSUME_TAC THENL
   [GEN_TAC THEN
    REWRITE_TAC[COMPLEX_RING `z + x = Cx(&0) <=> z = --x`] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    REWRITE_TAC[IM_NEG; RE_NEG; IM_CX; RE_CX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_TRANSFORM_AT THEN
  EXISTS_TAC `\z. (ll:complex->complex->complex) z z - clog z` THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; SUBSET; IN_BALL] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `w:complex` THEN ONCE_REWRITE_TAC[DIST_SYM] THEN DISCH_TAC THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    EXISTS_TAC `\n. w * clog(Cx(&n)) - clog w -
                    vsum(1..n) (\m. clog((Cx(&m) + w) / Cx(&m)))` THEN
    ASM_SIMP_TAC[] THEN
    ONCE_REWRITE_TAC[COMPLEX_RING `w - z - v:complex = (w - v) - z`] THEN
    MATCH_MP_TAC LIM_SUB THEN REWRITE_TAC[LIM_CONST] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_SUB THEN
  ASM_SIMP_TAC[COMPLEX_DIFFERENTIABLE_AT_CLOG] THEN
  MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_TRANSFORM_AT THEN
  EXISTS_TAC `(ll:complex->complex->complex) z` THEN
  EXISTS_TAC `min e (dd(z:complex))` THEN
  ASM_SIMP_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
   [X_GEN_TAC `w:complex` THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
    STRIP_TAC THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\n. w * clog(Cx(&n)) -
                    vsum(1..n) (\m. clog((Cx(&m) + w) / Cx(&m)))` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; LIM_SEQUENTIALLY] THEN
    CONJ_TAC THEN X_GEN_TAC `r:real` THEN STRIP_TAC THENL
     [REMOVE_THEN "*" (MP_TAC o SPEC `z:complex`);
      REMOVE_THEN "*" (MP_TAC o SPEC `w:complex`)] THEN
    ASM_SIMP_TAC[] THEN
    REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `r:real`)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[CENTRE_IN_CBALL; REAL_LT_IMP_LE] THEN
    ASM_SIMP_TAC[IN_CBALL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `open {z | Im z = &0 ==> &0 < Re z}` MP_TAC THENL
   [SUBGOAL_THEN
     `{z | Im z = &0 ==> &0 < Re z} =
      (:complex) DIFF ({z | Im z = &0} INTER {z | Re z <= &0})`
     (fun th -> SIMP_TAC[th; CLOSED_HALFSPACE_RE_LE; GSYM closed;
                      CLOSED_HALFSPACE_IM_EQ; CLOSED_INTER]) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV; IN_DIFF; IN_INTER; EXTENSION] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[OPEN_CONTAINS_CBALL; IN_ELIM_THM; SUBSET] THEN
    DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN
   `(ll:complex->complex->complex) z continuous_on cball(z,min r (dd z)) /\
    ll z holomorphic_on ball(z,min r (dd z))`
  MP_TAC THENL
   [MATCH_MP_TAC(ISPEC `sequentially` HOLOMORPHIC_UNIFORM_LIMIT) THEN
    EXISTS_TAC `\n z. z * clog(Cx(&n)) -
                      vsum(1..n) (\m. clog((Cx(&m) + z) / Cx(&m)))` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
    REWRITE_TAC[CBALL_MIN_INTER; IN_INTER] THEN
    CONJ_TAC THENL [ALL_TAC; SIMP_TAC[GSYM dist] THEN ASM_MESON_TAC[]] THEN
    EXISTS_TAC `1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC(MESON[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON;
                       HOLOMORPHIC_ON_SUBSET]
     `t SUBSET s /\ f holomorphic_on s
      ==> f continuous_on s /\ f holomorphic_on t`) THEN
    REWRITE_TAC[BALL_SUBSET_CBALL; GSYM CBALL_MIN_INTER] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_SUB THEN
    SIMP_TAC[HOLOMORPHIC_ON_MUL; HOLOMORPHIC_ON_ID;
             HOLOMORPHIC_ON_CONST] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_VSUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN
    SIMP_TAC[HOLOMORPHIC_ON_ADD; HOLOMORPHIC_ON_ID;
             HOLOMORPHIC_ON_CONST; complex_div; HOLOMORPHIC_ON_MUL] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_CLOG THEN
    REWRITE_TAC[FORALL_IN_IMAGE; GSYM complex_div; IMP_CONJ] THEN
    ASM_SIMP_TAC[RE_DIV_CX; IM_DIV_CX; REAL_DIV_EQ_0; RE_ADD; IM_ADD] THEN
    X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ; REAL_OF_NUM_LT; LE_1] THEN
    REWRITE_TAC[IM_CX; RE_CX; REAL_ADD_LID] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ; REAL_OF_NUM_LT; LE_1] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 < &m + x`) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[CBALL_MIN_INTER; IN_INTER]) THEN
    ASM_MESON_TAC[];
    SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_BALL; complex_differentiable] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    ASM_SIMP_TAC[CENTRE_IN_BALL; REAL_LT_MIN]]);;

let LGAMMA_ALT = prove
 (`!z. (!n. ~(z + Cx(&n) = Cx(&0)))
        ==> ((\n. (z * clog(Cx(&n)) + clog(Cx(&(FACT n)))) -
                  vsum(0..n) (\m. clog(Cx(&m) + z)))
             --> lgamma(z)) sequentially`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP LGAMMA) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM) THEN
  MATCH_MP_TAC LIM_EVENTUALLY THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SIMP_TAC[VECTOR_SUB_EQ; VSUM_CLAUSES_LEFT; LE_0; COMPLEX_ADD_LID] THEN
  MATCH_MP_TAC(COMPLEX_RING
   `a:complex = d - c ==> x - y - a = (x + c) - (y + d)`) THEN
  REWRITE_TAC[GSYM NPRODUCT_FACT; ADD_CLAUSES] THEN
  SIMP_TAC[REAL_OF_NUM_NPRODUCT; FINITE_NUMSEG; GSYM CX_LOG; LOG_PRODUCT;
           PRODUCT_POS_LT; IN_NUMSEG; REAL_OF_NUM_LT; LE_1; GSYM VSUM_CX] THEN
  REWRITE_TAC[GSYM VSUM_SUB_NUMSEG] THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
  REWRITE_TAC[complex_div] THEN ONCE_REWRITE_TAC[COMPLEX_ADD_SYM] THEN
  ASM_SIMP_TAC[CLOG_MUL_CX; REAL_LT_INV_EQ; REAL_OF_NUM_LT; LE_1;
               GSYM CX_INV; LOG_INV; CX_NEG; GSYM complex_sub]);;

let LGAMMA_ALT2 = prove
 (`!z. (!n. ~(z + Cx(&n) = Cx(&0)))
        ==> ((\n. vsum(1..n) (\m. z * clog(Cx(&1) + Cx(&1) / Cx(&m)) -
                                  clog(Cx(&1) + z / Cx(&m))) -
                  clog(z))
             --> lgamma(z)) sequentially`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[CX_INJ; REAL_OF_NUM_EQ; LE_1;
   COMPLEX_FIELD `~(m = Cx(&0)) ==> Cx(&1) + z / m = (z + m) / m`] THEN
  REWRITE_TAC[GSYM CX_ADD; GSYM CX_DIV] THEN
  SIMP_TAC[GSYM CX_LOG; LOG_DIV; REAL_LT_DIV; REAL_ARITH `&0 < &1 + &m`;
           REAL_OF_NUM_LT; LE_1] THEN
  SIMP_TAC[VSUM_SUB_NUMSEG; VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  REWRITE_TAC[CX_SUB; REAL_OF_NUM_ADD; ARITH_RULE `1 + m = m + 1`] THEN
  REWRITE_TAC[VSUM_DIFFS_ALT; LOG_1; COMPLEX_SUB_RZERO] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LGAMMA) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
    LIM_SUBSEQUENCE)) THEN
  DISCH_THEN(MP_TAC o SPEC `\r. r + 1`) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM) THEN
  REWRITE_TAC[o_DEF] THEN
  MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\n. --clog((Cx(&(n + 1)) + z) / Cx(&(n + 1)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM ADD1; VSUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
    REWRITE_TAC[COMPLEX_RING `Cx(&n) + z = z + Cx(&n)`] THEN
    SIMP_TAC[CX_LOG; REAL_OF_NUM_LT; LT_0] THEN
    CONV_TAC COMPLEX_RING;
    REWRITE_TAC[COMPLEX_VEC_0] THEN MATCH_MP_TAC LIM_NULL_COMPLEX_NEG THEN
    SIMP_TAC[REAL_OF_NUM_EQ; CX_INJ; ARITH_EQ; ADD_EQ_0;
      COMPLEX_FIELD `~(y = Cx(&0)) ==> (y + z) / y = Cx(&1) + z / y`] THEN
    SUBGOAL_THEN `Cx(&0) = clog (Cx (&1) + Cx(&0))` SUBST1_TAC THENL
     [REWRITE_TAC[COMPLEX_ADD_RID; CLOG_1]; ALL_TAC] THEN
    MP_TAC(ISPECL [`\z. clog(Cx(&1) + z)`; `sequentially`]
        LIM_CONTINUOUS_FUNCTION) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      COMPLEX_DIFFERENTIABLE_TAC THEN REWRITE_TAC[RE_ADD; RE_CX] THEN
      REWRITE_TAC[REAL_ADD_RID; REAL_LT_01];
      REWRITE_TAC[complex_div] THEN MATCH_MP_TAC LIM_NULL_COMPLEX_LMUL THEN
      MATCH_MP_TAC(REWRITE_RULE[o_DEF]
        (ISPECL [`f:num->complex`; `\n. n + 1`] LIM_SUBSEQUENCE)) THEN
      CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM CX_INV; REWRITE_RULE[o_DEF] (GSYM REALLIM_COMPLEX)] THEN
      REWRITE_TAC[REALLIM_1_OVER_N]]]);;

(* ------------------------------------------------------------------------- *)
(* The complex gamma function (defined using the Gauss/Euler product).       *)
(* Note that this totalizes it with the value zero at the poles.             *)
(* ------------------------------------------------------------------------- *)

let cgamma = new_definition
 `cgamma(z) = lim sequentially (\n. (Cx(&n) cpow z * Cx(&(FACT n))) /
                                    cproduct(0..n) (\m. z + Cx(&m)))`;;

let [CGAMMA;CGAMMA_EQ_0;CGAMMA_LGAMMA] = (CONJUNCTS o prove)
 (`(!z. ((\n. (Cx(&n) cpow z * Cx(&(FACT n))) / cproduct(0..n) (\m. z + Cx(&m)))
         --> cgamma(z)) sequentially) /\
   (!z. cgamma(z) = Cx(&0) <=> ?n. z + Cx(&n) = Cx(&0)) /\
   (!z. cgamma(z) = if ?n. z + Cx(&n) = Cx(&0) then Cx(&0)
                    else cexp(lgamma z))`,
  REWRITE_TAC[AND_FORALL_THM] THEN X_GEN_TAC `y:complex` THEN
  ASM_CASES_TAC `?n. y + Cx(&n) = Cx(&0)` THENL
   [ASM_REWRITE_TAC[GSYM NOT_EXISTS_THM] THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `N:num`) THEN
    REWRITE_TAC[cgamma; lim] THEN MATCH_MP_TAC(MESON[LIM_UNIQUE]
     `~trivial_limit net /\ (f --> a) net
      ==> (f --> @a. (f --> a) net) net /\ (@a. (f --> a) net) = a`) THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    MATCH_MP_TAC LIM_EVENTUALLY THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[GE] THEN
    DISCH_TAC THEN
    SIMP_TAC[COMPLEX_ENTIRE; COMPLEX_DIV_EQ_0; CPRODUCT_EQ_0; FINITE_NUMSEG;
             IN_NUMSEG; LE_0] THEN
    ASM_MESON_TAC[LE_REFL];
    ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM])] THEN
  SUBGOAL_THEN
   `((\n. (Cx(&n) cpow y * Cx(&(FACT n))) / cproduct(0..n) (\m. y + Cx(&m)))
     --> cexp(lgamma y)) sequentially`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC `\n. cexp(y * clog(Cx(&n)) - clog y -
                         vsum(1..n) (\m. clog((Cx(&m) + y) / Cx(&m))))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[CEXP_SUB; cpow; CX_INJ; REAL_OF_NUM_EQ; LE_1] THEN
      REWRITE_TAC[complex_div; GSYM COMPLEX_MUL_ASSOC] THEN AP_TERM_TAC THEN
      SIMP_TAC[GSYM NPRODUCT_FACT; REAL_OF_NUM_NPRODUCT; FINITE_NUMSEG] THEN
      SIMP_TAC[CX_PRODUCT; FINITE_NUMSEG; GSYM CPRODUCT_INV] THEN
      SIMP_TAC[CPRODUCT_CLAUSES_LEFT; LE_0] THEN
      GEN_REWRITE_TAC RAND_CONV [COMPLEX_RING
       `a * b * c:complex = b * a * c`] THEN
      REWRITE_TAC[COMPLEX_ADD_RID] THEN BINOP_TAC THENL
       [ASM_MESON_TAC[COMPLEX_ADD_RID; CEXP_CLOG]; ALL_TAC] THEN
      SIMP_TAC[ADD_CLAUSES; GSYM CPRODUCT_MUL; FINITE_NUMSEG] THEN
      REWRITE_TAC[GSYM CEXP_NEG; GSYM VSUM_NEG] THEN
      SIMP_TAC[CEXP_VSUM; FINITE_NUMSEG] THEN MATCH_MP_TAC CPRODUCT_EQ THEN
      REWRITE_TAC[IN_NUMSEG] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
      REWRITE_TAC[CEXP_NEG] THEN
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [GSYM COMPLEX_INV_INV] THEN
      REWRITE_TAC[GSYM COMPLEX_INV_MUL] THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC RAND_CONV [COMPLEX_MUL_SYM] THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [COMPLEX_ADD_SYM] THEN
      MATCH_MP_TAC CEXP_CLOG THEN
      ONCE_REWRITE_TAC[COMPLEX_ADD_SYM] THEN
      ASM_REWRITE_TAC[COMPLEX_ENTIRE; COMPLEX_INV_EQ_0] THEN
      REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC(ISPEC `cexp` LIM_CONTINUOUS_FUNCTION) THEN
      ASM_SIMP_TAC[LGAMMA; CONTINUOUS_AT_CEXP]];
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [REWRITE_TAC[cgamma; lim] THEN CONV_TAC SELECT_CONV THEN ASM_MESON_TAC[];
      DISCH_TAC] THEN
    MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
      ASM_MESON_TAC[TRIVIAL_LIMIT_SEQUENTIALLY];
      SIMP_TAC[CEXP_NZ]]]);;

let CGAMMA_RECURRENCE_ALT = prove
 (`!z. cgamma(z) = cgamma(z + Cx(&1)) / z`,
  GEN_TAC THEN ASM_CASES_TAC `?n.  z + Cx(&n) = Cx(&0)` THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[REWRITE_RULE[GSYM CGAMMA_EQ_0] th]) THEN
    CONV_TAC SYM_CONV THEN REWRITE_TAC[COMPLEX_DIV_EQ_0] THEN
    ASM_CASES_TAC `z = Cx(&0)` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_exists o concl)) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC[COMPLEX_ADD_RID; CGAMMA_EQ_0] THEN
    REWRITE_TAC[GSYM COMPLEX_ADD_ASSOC; GSYM CX_ADD; REAL_OF_NUM_ADD] THEN
    MESON_TAC[ADD1; ADD_SYM];
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM])] THEN
  SUBGOAL_THEN `!n. ~((z + Cx(&1)) + Cx(&n) = Cx(&0))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM COMPLEX_ADD_ASSOC; GSYM CX_ADD; REAL_OF_NUM_ADD] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(z = Cx(&0))` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPLEX_ADD_LID]; ALL_TAC] THEN
  MATCH_MP_TAC(COMPLEX_FIELD
   `(a * b) / c = Cx(&1) /\ ~(a = Cx(&0)) /\ ~(c = Cx(&0)) ==> b = c / a`) THEN
  ASM_REWRITE_TAC[CGAMMA_EQ_0] THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
  EXISTS_TAC
   `\n. (z * (Cx(&(n + 1)) cpow z * Cx(&(FACT(n + 1)))) /
             cproduct(0..n+1) (\m. z + Cx(&m))) /
        ((Cx(&n) cpow (z + Cx(&1)) * Cx(&(FACT n))) /
         cproduct(0..n) (\m. (z + Cx(&1)) + Cx(&m)))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LIM_COMPLEX_DIV THEN
    ASM_REWRITE_TAC[CGAMMA; CGAMMA_EQ_0] THEN
    MATCH_MP_TAC LIM_COMPLEX_LMUL THEN
    MP_TAC(SPEC `z:complex` CGAMMA) THEN
    DISCH_THEN(MP_TAC o SPEC `1` o MATCH_MP SEQ_OFFSET) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM COMPLEX_ADD_ASSOC; GSYM CX_ADD; REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[ARITH_RULE `1 + n = n + 1`] THEN
  SIMP_TAC[SYM(ISPECL [`f:num->complex`; `m:num`; `1`] CPRODUCT_OFFSET)] THEN
  SIMP_TAC[CPRODUCT_CLAUSES_LEFT; LE_0; ADD_CLAUSES] THEN
  REWRITE_TAC[GSYM ADD1; FACT; CX_MUL; COMPLEX_MUL_ASSOC; GSYM REAL_OF_NUM_MUL;
          ONCE_REWRITE_RULE[COMPLEX_MUL_SYM] (GSYM CPOW_SUC)] THEN
  REWRITE_TAC[complex_div; COMPLEX_INV_MUL; COMPLEX_INV_INV] THEN
  REWRITE_TAC[COMPLEX_ADD_RID; GSYM COMPLEX_MUL_ASSOC] THEN
  REWRITE_TAC[COMPLEX_RING
   `a * b * c * d * e * f * g * h:complex =
    (a * d) * (c * g) * (h * e) * (b * f)`] THEN
  ASM_SIMP_TAC[GSYM complex_div; COMPLEX_DIV_REFL; CX_INJ;
               REAL_OF_NUM_EQ; FACT_NZ; COMPLEX_MUL_LID] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM COMPLEX_MUL_LID] THEN
  MATCH_MP_TAC LIM_COMPLEX_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC LIM_EVENTUALLY THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC COMPLEX_DIV_REFL THEN
    SIMP_TAC[CPRODUCT_EQ_0; FINITE_NUMSEG] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\n. cexp((z + Cx(&1)) * clog(Cx(&1) + inv(Cx(&n))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    SIMP_TAC[cpow; CX_INJ; REAL_OF_NUM_EQ; NOT_SUC; LE_1] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM CEXP_SUB] THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM COMPLEX_SUB_LDISTRIB] THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[CX_INJ; REAL_OF_NUM_EQ; LE_1; COMPLEX_FIELD
     `~(n = Cx(&0)) ==> Cx(&1) + inv n = (n + Cx(&1)) / n`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC; GSYM CX_ADD] THEN
    ASM_SIMP_TAC[REAL_OF_NUM_ADD; GSYM CX_DIV; GSYM CX_LOG; LE_1; LOG_DIV;
                 REAL_OF_NUM_LT; REAL_LT_DIV; ARITH_RULE `0 < n + 1`] THEN
    REWRITE_TAC[CX_SUB];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM CEXP_0] THEN
  MATCH_MP_TAC(ISPEC `cexp` LIM_CONTINUOUS_FUNCTION) THEN
  REWRITE_TAC[CONTINUOUS_AT_CEXP] THEN
  MATCH_MP_TAC LIM_NULL_COMPLEX_LMUL THEN
  MATCH_MP_TAC LIM_NULL_COMPARISON_COMPLEX THEN
  EXISTS_TAC `\n. Cx(&2) * inv(Cx(&n))` THEN
  SIMP_TAC[LIM_INV_N; LIM_NULL_COMPLEX_LMUL] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `2` THEN
  REWRITE_TAC[GE; IN_FROM] THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`0`; `Cx(inv(&n))`] TAYLOR_CLOG) THEN
  SIMP_TAC[VSUM_CLAUSES_NUMSEG; ARITH; VECTOR_SUB_RZERO] THEN
  REWRITE_TAC[REAL_POW_1; GSYM CX_ADD; COMPLEX_NORM_CX] THEN
  REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NUM] THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_INV_LT_1 THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[CX_ADD; CX_INV]] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
  REWRITE_TAC[real_div; COMPLEX_NORM_MUL] THEN
  REWRITE_TAC[COMPLEX_NORM_INV; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_ARITH `&1 / &2 <= &1 - x <=> x <= inv(&2)`] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC);;

let CGAMMA_1 = prove
 (`cgamma(Cx(&1)) = Cx(&1)`,
  MP_TAC(SPEC `Cx(&1)` CGAMMA) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT; TRIVIAL_LIMIT_SEQUENTIALLY]
     (ISPEC `sequentially` LIM_UNIQUE)) THEN
  REWRITE_TAC[GSYM CX_ADD; REAL_OF_NUM_ADD; ARITH_RULE `1 + n = n + 1`] THEN
  SIMP_TAC[SYM(ISPECL [`f:num->complex`; `m:num`; `1`] CPRODUCT_OFFSET)] THEN
  MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\n. Cx(&n / (&n + &1))` THEN CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[CX_DIV] THEN
    ASM_SIMP_TAC[CPOW_N; CX_INJ; REAL_OF_NUM_EQ; LE_1; COMPLEX_POW_1] THEN
    REWRITE_TAC[complex_div; GSYM COMPLEX_MUL_ASSOC] THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC [GSYM COMPLEX_INV_INV] THEN
    AP_TERM_TAC THEN REWRITE_TAC[COMPLEX_INV_INV; COMPLEX_INV_MUL] THEN
    MATCH_MP_TAC(COMPLEX_FIELD
     `a * b = c /\ ~(b = Cx(&0)) ==> a = inv b * c`) THEN
    REWRITE_TAC[GSYM CX_MUL; CX_INJ; REAL_OF_NUM_EQ; FACT_NZ] THEN
    REWRITE_TAC[REAL_OF_NUM_SUC; REAL_OF_NUM_MUL; GSYM(CONJUNCT2 FACT)] THEN
    REWRITE_TAC[ADD_CLAUSES; ADD1] THEN SPEC_TAC(`n + 1`,`m:num`) THEN
    INDUCT_TAC THEN REWRITE_TAC[FACT; CPRODUCT_CLAUSES_NUMSEG; ARITH] THEN
    ASM_REWRITE_TAC[CX_MUL; GSYM REAL_OF_NUM_MUL] THEN
    REWRITE_TAC[ARITH_RULE `1 <= SUC n`; COMPLEX_MUL_SYM];
    ALL_TAC] THEN
  SIMP_TAC[REAL_FIELD `&n / (&n + &1) = &1 - inv(&n + &1)`] THEN
  SUBST1_TAC(COMPLEX_RING `Cx(&1) = Cx(&1) - Cx(&0)`) THEN
  REWRITE_TAC[CX_SUB] THEN MATCH_MP_TAC LIM_SUB THEN
  REWRITE_TAC[LIM_CONST; REAL_OF_NUM_ADD] THEN
  MATCH_MP_TAC(ISPECL [`f:num->complex`; `l:complex`; `1`] SEQ_OFFSET) THEN
  REWRITE_TAC[CX_INV; LIM_INV_N]);;

let CGAMMA_RECURRENCE = prove
 (`!z. cgamma(z + Cx(&1)) = if z = Cx(&0) then Cx(&1) else z * cgamma(z)`,
  GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[COMPLEX_ADD_LID; CGAMMA_1] THEN
  MATCH_MP_TAC(COMPLEX_FIELD `a = b / c /\ ~(c = Cx(&0)) ==> b = c * a`) THEN
  ASM_MESON_TAC[CGAMMA_RECURRENCE_ALT]);;

let CGAMMA_FACT = prove
 (`!n. cgamma(Cx(&(n + 1))) = Cx(&(FACT n))`,
  INDUCT_TAC THEN REWRITE_TAC[FACT; ADD_CLAUSES; CGAMMA_1] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REWRITE_TAC[CX_ADD] THEN
  REWRITE_TAC[CGAMMA_RECURRENCE; CX_INJ; REAL_OF_NUM_EQ; ADD_EQ_0; ARITH] THEN
  ASM_REWRITE_TAC[ADD1; GSYM REAL_OF_NUM_MUL; CX_MUL]);;

let CGAMMA_POLES = prove
 (`!n. cgamma(--(Cx(&n))) = Cx(&0)`,
  REWRITE_TAC[CGAMMA_EQ_0] THEN MESON_TAC[COMPLEX_ADD_LINV]);;

let COMPLEX_DIFFERENTIABLE_AT_CGAMMA = prove
 (`!z. (!n. ~(z + Cx(&n) = Cx(&0))) ==> cgamma complex_differentiable at z`,
  let lemma = prove
   (`!z. (!n. ~(z + Cx(&n) = Cx(&0))) /\
         cgamma complex_differentiable at (z + Cx(&1))
         ==> cgamma complex_differentiable at z`,
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`\z. cgamma(z + Cx(&1)) / z`; `&1`] THEN
    REWRITE_TAC[REAL_LT_01] THEN
    CONJ_TAC THENL [REWRITE_TAC[GSYM CGAMMA_RECURRENCE_ALT]; ALL_TAC] THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_DIV_AT THEN
    REWRITE_TAC[COMPLEX_DIFFERENTIABLE_ID] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[COMPLEX_ADD_RID]] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_COMPOSE_AT THEN
    ASM_REWRITE_TAC[] THEN COMPLEX_DIFFERENTIABLE_TAC) in
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `abs(Re z) + &1` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  SUBGOAL_THEN
   `!n. n <= N ==> cgamma complex_differentiable (at (z + Cx(&N) - Cx(&n)))`
  MP_TAC THENL
   [ALL_TAC; MESON_TAC[LE_REFL; COMPLEX_SUB_REFL; COMPLEX_ADD_RID]] THEN
  INDUCT_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[COMPLEX_SUB_RZERO] THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_TRANSFORM_AT THEN
    EXISTS_TAC `\z. cexp(lgamma z)` THEN
    SUBGOAL_THEN `open {z | !n. ~(z + Cx(&n) = Cx(&0))}` MP_TAC THENL
     [REWRITE_TAC[SET_RULE `{z | !n. P n z} = UNIV DIFF {z | ?n. ~P n z}`] THEN
      REWRITE_TAC[GSYM closed] THEN MATCH_MP_TAC DISCRETE_IMP_CLOSED THEN
      EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01; IMP_CONJ] THEN
      REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
      SIMP_TAC[COMPLEX_RING `x + y = Cx(&0) <=> x = --y`] THEN
      REWRITE_TAC[COMPLEX_RING `--x - --y:complex = y - x`] THEN
      REWRITE_TAC[COMPLEX_EQ_NEG2; CX_INJ; GSYM CX_SUB; COMPLEX_NORM_CX] THEN
      SIMP_TAC[GSYM REAL_EQ_INTEGERS; INTEGER_CLOSED];
      REWRITE_TAC[open_def; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `w:complex` THEN REWRITE_TAC[dist] THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `w - Cx(&N)`) THEN
        ASM_SIMP_TAC[dist; COMPLEX_RING `w - n - z:complex = w - (z + n)`] THEN
        REWRITE_TAC[CGAMMA_LGAMMA] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
        FIRST_X_ASSUM(X_CHOOSE_TAC `n:num`) THEN
        DISCH_THEN(MP_TAC o SPEC `n + N:num`) THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD; CX_ADD] THEN
        ASM_REWRITE_TAC[COMPLEX_RING `w - N + n + N:complex = w + n`];
        GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
        MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_COMPOSE_AT THEN
        REWRITE_TAC[COMPLEX_DIFFERENTIABLE_AT_CEXP] THEN
        MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_AT_LGAMMA THEN
        REWRITE_TAC[RE_ADD; RE_CX] THEN ASM_REAL_ARITH_TAC]];
    DISCH_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_SUC; CX_ADD] THEN
    MATCH_MP_TAC lemma THEN
    REWRITE_TAC[COMPLEX_RING `(z + N - (n + w)) + w:complex = z + N - n`] THEN
    CONJ_TAC THENL
     [ALL_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC] THEN
    X_GEN_TAC `m:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(N + m) - (n + 1)`) THEN
    SUBGOAL_THEN `n + 1 <= N + m`
      (fun th -> SIMP_TAC[th; GSYM REAL_OF_NUM_SUB])
    THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; CX_ADD; CX_SUB] THEN
    CONV_TAC COMPLEX_RING]);;

let COMPLEX_DIFFERENTIABLE_WITHIN_CGAMMA = prove
 (`!z s. (!n. ~(z + Cx(&n) = Cx(&0)))
         ==> cgamma complex_differentiable at z within s`,
  SIMP_TAC[COMPLEX_DIFFERENTIABLE_AT_WITHIN;
           COMPLEX_DIFFERENTIABLE_AT_CGAMMA]);;

let HOLOMORPHIC_ON_CGAMMA = prove
 (`!s. s SUBSET {z | !n. ~(z + Cx(&n) = Cx(&0))}
       ==> cgamma holomorphic_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HOLOMORPHIC_ON_DIFFERENTIABLE] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_WITHIN_CGAMMA THEN
  ASM SET_TAC[]);;

let CONTINUOUS_AT_CGAMMA = prove
 (`!z. (!n. ~(z + Cx(&n) = Cx(&0))) ==> cgamma continuous at z`,
  SIMP_TAC[COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT;
           COMPLEX_DIFFERENTIABLE_AT_CGAMMA]);;

let CONTINUOUS_WITHIN_CGAMMA = prove
 (`!z s. (!n. ~(z + Cx(&n) = Cx(&0)))
         ==> cgamma continuous at z within s`,
  SIMP_TAC[COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN;
           COMPLEX_DIFFERENTIABLE_WITHIN_CGAMMA]);;

let CONTINUOUS_ON_CGAMMA = prove
 (`!s. s SUBSET {z | !n. ~(z + Cx(&n) = Cx(&0))}
       ==> cgamma continuous_on s`,
  SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON; HOLOMORPHIC_ON_CGAMMA]);;

let CGAMMA_SIMPLE_POLES = prove
 (`!n. ((\z. (z + Cx(&n)) * cgamma z) --> --Cx(&1) pow n / Cx(&(FACT n)))
       (at(--Cx(&n)))`,
  INDUCT_TAC THENL
   [REWRITE_TAC[COMPLEX_ADD_RID; COMPLEX_NEG_0; FACT; complex_pow;
                COMPLEX_DIV_1] THEN
    ONCE_REWRITE_TAC[CGAMMA_RECURRENCE_ALT] THEN
    MATCH_MP_TAC LIM_TRANSFORM_AWAY_AT THEN
    MAP_EVERY EXISTS_TAC [`\z. cgamma(z + Cx(&1))`; `Cx(&1)`] THEN
    REWRITE_TAC[CONJ_ASSOC] THEN
    CONJ_TAC THENL [CONV_TAC COMPLEX_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `(\z. cgamma (z + Cx(&1))) continuous at (Cx(&0))`
    MP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
      CONJ_TAC THENL [CONTINUOUS_TAC; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_AT_CGAMMA THEN
      REWRITE_TAC[GSYM CX_ADD; CX_INJ] THEN REAL_ARITH_TAC;
      REWRITE_TAC[CONTINUOUS_AT; COMPLEX_ADD_LID; CGAMMA_1]];
    REWRITE_TAC[FACT; CX_MUL; GSYM REAL_OF_NUM_MUL] THEN
    ONCE_REWRITE_TAC[CGAMMA_RECURRENCE_ALT] THEN
    REWRITE_TAC[complex_div; complex_pow; COMPLEX_INV_MUL] THEN
    REWRITE_TAC[SIMPLE_COMPLEX_ARITH
     `(--Cx(&1) * p) * is * i = (p * i) * --is`] THEN
    REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN MATCH_MP_TAC LIM_COMPLEX_MUL THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o
        ISPECL [`at (--Cx(&(SUC n)))`; `\z.  z + Cx(&1)`] o
        MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
         (REWRITE_RULE[CONJ_ASSOC] LIM_COMPOSE_AT))) THEN
      REWRITE_TAC[o_DEF; GSYM REAL_OF_NUM_SUC; CX_ADD] THEN
      REWRITE_TAC[COMPLEX_RING `(z + Cx(&1)) + w = z + (w + Cx(&1))`] THEN
      REWRITE_TAC[GSYM complex_div] THEN DISCH_THEN MATCH_MP_TAC THEN
      CONJ_TAC THENL
       [LIM_TAC THEN CONV_TAC COMPLEX_RING;
        REWRITE_TAC[EVENTUALLY_AT; GSYM DIST_NZ] THEN
        EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
        CONV_TAC COMPLEX_RING];
      REWRITE_TAC[COMPLEX_NEG_INV; GSYM CONTINUOUS_AT] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
      MATCH_MP_TAC CONTINUOUS_COMPLEX_INV_AT THEN
      REWRITE_TAC[GSYM CX_NEG; CX_INJ; GSYM REAL_OF_NUM_SUC] THEN
      REWRITE_TAC[CONTINUOUS_AT_ID] THEN REAL_ARITH_TAC]]);;

let CNJ_CGAMMA = prove
 (`!z. cnj(cgamma z) = cgamma(cnj z)`,
  GEN_TAC THEN MP_TAC(SPEC `cnj z` CGAMMA) THEN
  MATCH_MP_TAC(REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
        LIM_UNIQUE) THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  GEN_REWRITE_TAC I [GSYM LIM_CNJ] THEN REWRITE_TAC[CNJ_CNJ] THEN
  MP_TAC(SPEC `z:complex` CGAMMA) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
  SIMP_TAC[CNJ_DIV; CNJ_MUL; CNJ_CX; CNJ_CPRODUCT; FINITE_NUMSEG] THEN
  REWRITE_TAC[CNJ_ADD; CNJ_CNJ; CNJ_CX] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[cpow; CNJ_EQ_0] THEN
  DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[CNJ_CX; CNJ_CEXP] THEN
  REWRITE_TAC[CNJ_MUL; CNJ_CNJ] THEN
  ASM_SIMP_TAC[CNJ_CLOG; RE_CX; REAL_OF_NUM_LT; LE_1; CNJ_CX]);;

let REAL_GAMMA = prove
 (`!z. real z ==> real(cgamma z)`,
  SIMP_TAC[REAL_CNJ; CNJ_CGAMMA]);;

let RE_POS_CGAMMA_REAL = prove
 (`!z. real z /\ &0 <= Re z ==> &0 <= Re(cgamma z)`,
  REWRITE_TAC[REAL_EXISTS; LEFT_IMP_EXISTS_THM; IMP_CONJ] THEN
  GEN_TAC THEN X_GEN_TAC `x:real` THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[RE_CX] THEN DISCH_TAC THEN MP_TAC(SPEC `Cx x` CGAMMA) THEN
  MATCH_MP_TAC(REWRITE_RULE[TAUT `p /\ q /\ r ==> s <=> p /\ r ==> q ==> s`]
        LIM_RE_LBOUND) THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[cpow; CX_INJ; REAL_OF_NUM_EQ; LE_1; GSYM CX_LOG; GSYM CX_INV;
               REAL_OF_NUM_LT; GSYM CX_MUL; GSYM CX_EXP; RE_MUL_CX; RE_CX;
               complex_div; GSYM CX_ADD; GSYM CX_PRODUCT; FINITE_NUMSEG] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN
  SIMP_TAC[REAL_LE_MUL; REAL_EXP_POS_LE; REAL_POS; REAL_LE_INV_EQ] THEN
  MATCH_MP_TAC PRODUCT_POS_LE_NUMSEG THEN ASM_REAL_ARITH_TAC);;

let CGAMMA_LEGENDRE_ALT = prove
 (`!z. cgamma(z) * cgamma(z + Cx(&1) / Cx(&2)) =
       Cx(&2) cpow (Cx(&1) - Cx(&2) * z) *
       cgamma(Cx(&1) / Cx(&2)) * cgamma(Cx(&2) * z)`,
  REWRITE_TAC[GSYM CX_DIV] THEN
  SUBGOAL_THEN
   `?f. !z. (!n. ~(Cx(&2) * z + Cx(&n) = Cx(&0)))
            ==> (f --> (cgamma(z) * cgamma(z + Cx(&1 / &2))) /
                     (Cx(&2) cpow (Cx(&1) - Cx(&2) * z) * cgamma(Cx(&2) * z)))
                sequentially`
  CHOOSE_TAC THENL
   [EXISTS_TAC
     `\n. (Cx(&n) cpow Cx(&1 / &2) * inv (Cx(&2))) *
          (Cx(&(FACT n)) pow 2 * inv (Cx(&(FACT (2 * n))))) *
          Cx(&4) pow (n + 1) *
          inv(Cx(&(2 * n + 1)))` THEN
    REPEAT STRIP_TAC THEN MP_TAC(SPEC `Cx(&2) * z` CGAMMA) THEN
    DISCH_THEN(MP_TAC o SPEC `\n. 2 * n` o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT] LIM_SUBSEQUENCE)) THEN
    REWRITE_TAC[o_DEF] THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `Cx(&2) cpow (Cx(&1) - Cx(&2) * z)` o
          MATCH_MP LIM_COMPLEX_LMUL) THEN
    MP_TAC(CONJ (SPEC `z:complex` CGAMMA) (SPEC `z + Cx(&1 / &2)` CGAMMA)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP LIM_COMPLEX_MUL) THEN
    REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP
     (ONCE_REWRITE_RULE[IMP_CONJ]
         (REWRITE_RULE[CONJ_ASSOC] LIM_COMPLEX_DIV))) THEN
    ASM_REWRITE_TAC[COMPLEX_ENTIRE; CPOW_EQ_0; CGAMMA_EQ_0] THEN
    REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ; ARITH_EQ] THEN
    SUBGOAL_THEN `((\n. (Cx(&2) * z + Cx(&(2 * n + 1))) / Cx(&(2 * n + 1)))
                   --> Cx(&1)) sequentially`
    MP_TAC THENL
     [SIMP_TAC[complex_div; COMPLEX_MUL_RINV; CX_INJ; REAL_OF_NUM_EQ;
               COMPLEX_ADD_RDISTRIB; ARITH_RULE `~(2 * n + 1 = 0)`] THEN
      ONCE_REWRITE_TAC[LIM_NULL_COMPLEX] THEN
      REWRITE_TAC[COMPLEX_RING `(a + b) - b:complex = a`] THEN
      MATCH_MP_TAC LIM_NULL_COMPLEX_LMUL THEN
      MP_TAC(SPEC `\n. 2 * n + 1`
       (MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] LIM_SUBSEQUENCE) LIM_INV_N)) THEN
      REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC;
      REWRITE_TAC[IMP_IMP] THEN
      DISCH_THEN(MP_TAC o MATCH_MP LIM_COMPLEX_MUL)] THEN
    REWRITE_TAC[COMPLEX_MUL_LID] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[CPOW_ADD; complex_div; COMPLEX_INV_MUL; COMPLEX_INV_INV] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; CX_MUL] THEN
    SIMP_TAC[CPOW_MUL_REAL; REAL_CX; RE_CX; REAL_POS] THEN
    REWRITE_TAC[CPOW_SUB; CPOW_N; CX_INJ; REAL_OF_NUM_EQ; ARITH_EQ] THEN
    SIMP_TAC[COMPLEX_POW_1; complex_div; COMPLEX_INV_INV; COMPLEX_INV_MUL] THEN
    REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC] THEN REWRITE_TAC[COMPLEX_RING
      `x * y * a * b * c * d * e * f * g * h * i * j * k * l * m:complex =
       (x * y) * (e * h) * ((a * d) * k) *
       ((b * f) * l) * (i * j) * (m * c * g)`] THEN
    REWRITE_TAC[GSYM COMPLEX_POW_2; COMPLEX_MUL_2; CPOW_ADD] THEN
    ASM_SIMP_TAC[COMPLEX_MUL_RINV; COMPLEX_POW_EQ_0; CPOW_EQ_0;
                 CX_INJ; REAL_OF_NUM_EQ; ARITH_EQ; LE_1; COMPLEX_MUL_LID] THEN
    REWRITE_TAC[GSYM COMPLEX_MUL_2; GSYM COMPLEX_INV_MUL] THEN
    SIMP_TAC[GSYM CPRODUCT_MUL; FINITE_NUMSEG] THEN
    REWRITE_TAC[COMPLEX_RING
     `(z + m) * ((z + Cx(&1 / &2)) + m) =
      inv(Cx(&4)) *
      (Cx(&2) * z + Cx(&2) * m) * (Cx(&2) * z + Cx(&2) * m + Cx(&1))`] THEN
    SIMP_TAC[CPRODUCT_MUL; FINITE_NUMSEG; CPRODUCT_CONST_NUMSEG] THEN
    SIMP_TAC[GSYM CPRODUCT_MUL; SUB_0; FINITE_NUMSEG] THEN
    REWRITE_TAC[GSYM CX_ADD; GSYM CX_MUL;
                REAL_OF_NUM_ADD; REAL_OF_NUM_MUL] THEN
    REWRITE_TAC[GSYM CPRODUCT_PAIR] THEN
    SIMP_TAC[GSYM ADD1; CPRODUCT_CLAUSES_NUMSEG] THEN
    REWRITE_TAC[ADD1] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[LE_0; COMPLEX_INV_MUL; COMPLEX_INV_INV; GSYM COMPLEX_POW_INV] THEN
    ONCE_REWRITE_TAC[COMPLEX_RING
     `x * a * b * c * d * e * f:complex = (c * e) * a * b * d * f * x`] THEN
    ASM_SIMP_TAC[COMPLEX_MUL_RINV; CPRODUCT_EQ_0; FINITE_NUMSEG] THEN
    REWRITE_TAC[COMPLEX_MUL_LID; COMPLEX_MUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[GSYM COMPLEX_MUL_ASSOC; COMPLEX_MUL_LINV] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN
  ASM_CASES_TAC `!n. ~(Cx(&2) * z + Cx(&n) = Cx(&0))` THENL
   [FIRST_X_ASSUM(fun th ->
      MP_TAC(SPEC `z:complex` th) THEN MP_TAC(SPEC `Cx(&1 / &2)` th)) THEN
    ASM_REWRITE_TAC[GSYM CX_ADD; GSYM CX_MUL; GSYM CX_SUB; CX_INJ] THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV] THEN
    REWRITE_TAC[CGAMMA_1; CPOW_N; CX_INJ; REAL_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[complex_pow; COMPLEX_MUL_RID; COMPLEX_DIV_1; IMP_IMP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
        LIM_UNIQUE)) THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN MATCH_MP_TAC(COMPLEX_FIELD
     `~(p = Cx(&0)) /\ ~(z2 = Cx(&0))
      ==> a = (z * z') / (p * z2) ==> z * z' = p * a * z2`) THEN
    ASM_REWRITE_TAC[CGAMMA_EQ_0; CPOW_EQ_0; CX_INJ; REAL_OF_NUM_EQ; ARITH_EQ];
    MATCH_MP_TAC(COMPLEX_RING
     `z = Cx(&0) /\ ((w = Cx(&0)) \/ (y = Cx(&0)))
      ==> w * y = p * q * z`) THEN
    REWRITE_TAC[CGAMMA_EQ_0] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[OR_EXISTS_THM; GSYM COMPLEX_ADD_ASSOC] THEN
    ONCE_REWRITE_TAC[COMPLEX_RING
     `z + n = Cx(&0) <=> Cx(&2) * z + Cx(&2) * n = Cx(&0)`] THEN
    REWRITE_TAC[GSYM CX_ADD; GSYM CX_MUL] THEN
    REWRITE_TAC[REAL_ARITH `&2 * (&1 / &2 + n) = &2 * n + &1`] THEN
    REWRITE_TAC[REAL_OF_NUM_SUC; REAL_OF_NUM_MUL] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
    MP_TAC(SPEC `n:num` EVEN_OR_ODD) THEN
    MESON_TAC[ODD_EXISTS; EVEN_EXISTS]]);;

let CGAMMA_REFLECTION = prove
 (`!z. cgamma(z) * cgamma(Cx(&1) - z) = Cx pi / csin(Cx pi * z)`,
  let lemma = prove
   (`!w z. (?n. integer n /\ w = Cx n) /\ (?n. integer n /\ z = Cx n) /\
           dist(w,z) < &1
           ==> w = z`,
    REPEAT GEN_TAC THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    ASM_REWRITE_TAC[DIST_CX] THEN ASM_MESON_TAC[REAL_EQ_INTEGERS_IMP]) in
  ABBREV_TAC
   `g = \z. if ?n. integer n /\ z = Cx n then Cx pi
            else cgamma(z) * cgamma(Cx(&1) - z) * csin(Cx pi * z)` THEN
  SUBGOAL_THEN `!z. g(z + Cx(&1)):complex = g(z)` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "g" THEN
    MATCH_MP_TAC(MESON[] `(p <=> p') /\ a = a' /\ b = b'
                    ==> (if p then a else b) = (if p' then a' else b')`) THEN
    REWRITE_TAC[COMPLEX_RING `z + Cx(&1) = w <=> z = w - Cx(&1)`] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM CX_SUB] THEN
      MESON_TAC[INTEGER_CLOSED; REAL_ARITH `(n + &1) - &1 = n`];
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [CGAMMA_RECURRENCE_ALT] THEN
      REWRITE_TAC[COMPLEX_RING `a - (z + a):complex = --z`] THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV)
       [CGAMMA_RECURRENCE_ALT] THEN
      REWRITE_TAC[COMPLEX_ADD_LDISTRIB; COMPLEX_MUL_RID; CSIN_ADD] THEN
      REWRITE_TAC[GSYM CX_SIN; GSYM CX_COS; SIN_PI; COS_PI] THEN
      REWRITE_TAC[COMPLEX_RING `--z + Cx(&1) = Cx(&1) - z`] THEN
      REWRITE_TAC[complex_div; COMPLEX_INV_NEG; COMPLEX_MUL_AC;
                  CX_NEG; COMPLEX_MUL_LID; COMPLEX_MUL_LZERO] THEN
      REWRITE_TAC[COMPLEX_ADD_RID; COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG] THEN
      REWRITE_TAC[COMPLEX_MUL_LID; COMPLEX_NEG_NEG] THEN
      REWRITE_TAC[COMPLEX_MUL_AC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n z. integer n ==> g(z + Cx n):complex = g z` ASSUME_TAC THENL
   [SUBGOAL_THEN `!n z. g(z + Cx(&n)):complex = g z` ASSUME_TAC THENL
     [INDUCT_TAC THEN
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_SUC; COMPLEX_ADD_RID] THEN
      ASM_REWRITE_TAC[CX_ADD; COMPLEX_ADD_ASSOC];
      REWRITE_TAC[integer] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
       (REAL_ARITH `abs x = a ==> x = a \/ x = --a`)) THEN
      ASM_REWRITE_TAC[CX_NEG; GSYM complex_sub] THEN
      ASM_MESON_TAC[COMPLEX_RING `(z - w) + w:complex = z`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. ~(?n. integer n /\ z = Cx n)
                    ==> g complex_differentiable (at z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_TRANSFORM_AT THEN
    EXISTS_TAC `\z. cgamma z * cgamma(Cx(&1) - z) * csin(Cx pi * z)` THEN
    SUBGOAL_THEN `closed {z | ?n. integer n /\ z = Cx n}` MP_TAC THENL
     [MATCH_MP_TAC DISCRETE_IMP_CLOSED THEN EXISTS_TAC `&1` THEN
      REWRITE_TAC[REAL_LT_01; IN_ELIM_THM] THEN MESON_TAC[lemma; dist];
      REWRITE_TAC[closed; OPEN_CONTAINS_BALL; IN_UNIV; IN_DIFF]] THEN
    DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    REWRITE_TAC[SUBSET; IN_BALL; IN_DIFF; IN_ELIM_THM; IN_UNIV] THEN
    X_GEN_TAC `e:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN EXPAND_TAC "g" THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[] THEN
    REPEAT(MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_MUL_AT THEN CONJ_TAC) THENL
     [ALL_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_COMPOSE_AT THEN
      CONJ_TAC;
      ALL_TAC] THEN
     (MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_AT_CGAMMA ORELSE
      COMPLEX_DIFFERENTIABLE_TAC) THEN
     REWRITE_TAC[COMPLEX_RING `z + a:complex = b <=> z = b - a`;
                 COMPLEX_RING `Cx(&1) - z = a - b <=> z = b - a + Cx(&1)`] THEN
     REWRITE_TAC[GSYM CX_ADD; GSYM CX_SUB] THEN ASM_MESON_TAC[INTEGER_CLOSED];
     ALL_TAC] THEN
  SUBGOAL_THEN `g complex_differentiable at (Cx(&0))` ASSUME_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT THEN
    EXISTS_TAC `ball(Cx(&0),&1)` THEN
    REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL; REAL_LT_01] THEN
    MATCH_MP_TAC NO_ISOLATED_SINGULARITY THEN EXISTS_TAC `{Cx(&0)}` THEN
    REWRITE_TAC[OPEN_BALL; FINITE_SING] THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[HOLOMORPHIC_ON_DIFFERENTIABLE; IN_DIFF; IN_SING] THEN
      X_GEN_TAC `z:complex` THEN REWRITE_TAC[COMPLEX_IN_BALL_0] THEN
      STRIP_TAC THEN MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_AT_WITHIN THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `~(z = Cx(&0))` THEN
      REWRITE_TAC[CONTRAPOS_THM] THEN DISCH_TAC THEN MATCH_MP_TAC lemma THEN
      ASM_REWRITE_TAC[dist; COMPLEX_SUB_RZERO] THEN
      MESON_TAC[INTEGER_CLOSED]] THEN
    REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    X_GEN_TAC `z:complex` THEN REWRITE_TAC[COMPLEX_IN_BALL_0] THEN
    DISCH_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_WITHIN THEN
    ASM_CASES_TAC `z = Cx(&0)` THENL
     [ALL_TAC;
      MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `~(z = Cx(&0))` THEN
      REWRITE_TAC[CONTRAPOS_THM] THEN DISCH_TAC THEN MATCH_MP_TAC lemma THEN
      ASM_REWRITE_TAC[dist; COMPLEX_SUB_RZERO] THEN
      MESON_TAC[INTEGER_CLOSED]] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[CONTINUOUS_AT] THEN
    EXPAND_TAC "g" THEN
    REWRITE_TAC[MESON[INTEGER_CLOSED] `?n. integer n /\ Cx(&0) = Cx(n)`] THEN
    MATCH_MP_TAC LIM_TRANSFORM_WITHIN_OPEN THEN
    EXISTS_TAC `\z. Cx pi * (z * cgamma(z)) * cgamma(Cx(&1) - z) *
                    csin(Cx pi * z) / (Cx pi * z)` THEN
    EXISTS_TAC `ball(Cx(&0),&1)` THEN
    REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL; REAL_LT_01] THEN CONJ_TAC THENL
     [X_GEN_TAC `w:complex` THEN REWRITE_TAC[COMPLEX_IN_BALL_0] THEN
      STRIP_TAC THEN COND_CASES_TAC THENL
       [UNDISCH_TAC `~(w = Cx(&0))` THEN
        MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN MATCH_MP_TAC lemma THEN
        ASM_REWRITE_TAC[dist; COMPLEX_SUB_RZERO] THEN
        MESON_TAC[INTEGER_CLOSED];
        UNDISCH_TAC `~(w = Cx(&0))` THEN MP_TAC PI_NZ THEN
        REWRITE_TAC[GSYM CX_INJ] THEN CONV_TAC COMPLEX_FIELD];
      GEN_REWRITE_TAC LAND_CONV [COMPLEX_RING
       `p = p * Cx(&1) * Cx(&1) * Cx(&1)`] THEN
      MATCH_MP_TAC LIM_COMPLEX_LMUL THEN MATCH_MP_TAC LIM_COMPLEX_MUL THEN
      CONJ_TAC THENL
       [MP_TAC(SPEC `0` CGAMMA_SIMPLE_POLES) THEN
        REWRITE_TAC[FACT; COMPLEX_DIV_1; complex_pow; COMPLEX_ADD_RID] THEN
        REWRITE_TAC[COMPLEX_NEG_0];
        ALL_TAC] THEN
      MATCH_MP_TAC LIM_COMPLEX_MUL THEN CONJ_TAC THENL
       [SUBGOAL_THEN `(cgamma o (\z. Cx(&1) - z)) continuous (at (Cx(&0)))`
        MP_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
          CONJ_TAC THENL [CONTINUOUS_TAC; ALL_TAC] THEN
          MATCH_MP_TAC CONTINUOUS_AT_CGAMMA THEN
          REWRITE_TAC[GSYM CX_ADD; GSYM CX_SUB; CX_INJ] THEN
          REAL_ARITH_TAC;
          REWRITE_TAC[CONTINUOUS_AT; o_DEF; COMPLEX_SUB_RZERO; CGAMMA_1]];
        SUBGOAL_THEN
         `(\z. csin(Cx pi * z) / (Cx pi * z)) =
          (\z. csin z / z) o (\w. Cx pi * w)`
        SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
        MATCH_MP_TAC LIM_COMPOSE_AT THEN
        EXISTS_TAC `Cx(&0)` THEN REWRITE_TAC[LIM_CSIN_OVER_X] THEN
        SIMP_TAC[EVENTUALLY_AT; COMPLEX_ENTIRE; CX_INJ; PI_NZ;
                 GSYM DIST_NZ] THEN
        CONJ_TAC THENL [ALL_TAC; MESON_TAC[REAL_LT_01]] THEN
        LIM_TAC THEN CONV_TAC COMPLEX_RING]];
    ALL_TAC] THEN
  SUBGOAL_THEN `g holomorphic_on (:complex)` ASSUME_TAC THENL
   [REWRITE_TAC[HOLOMORPHIC_ON_DIFFERENTIABLE; WITHIN_UNIV; IN_UNIV] THEN
    X_GEN_TAC `z:complex` THEN ASM_CASES_TAC `?n. integer n /\ z = Cx n` THEN
    ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_TRANSFORM_AT THEN
    EXISTS_TAC `(g:complex->complex) o (\z. z - Cx n)` THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
     [REWRITE_TAC[o_THM] THEN
      ASM_MESON_TAC[COMPLEX_RING `(z - w) + w:complex = z`];
      MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_COMPOSE_AT THEN
      ASM_REWRITE_TAC[COMPLEX_SUB_REFL] THEN
      COMPLEX_DIFFERENTIABLE_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. g(z / Cx(&2)) * g((z + Cx(&1)) / Cx(&2)) =
        cgamma(Cx(&1 / &2)) pow 2 * g(z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!s. s = UNIV /\ (!x. x IN s ==> P x) ==> !x. P x`) THEN
    EXISTS_TAC `closure {z | !n. ~(integer n /\ z = Cx n)}` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[CLOSURE_INTERIOR] THEN
      MATCH_MP_TAC(SET_RULE `s = {} ==> t DIFF s = t`) THEN
      MATCH_MP_TAC COUNTABLE_EMPTY_INTERIOR THEN
      MATCH_MP_TAC DISCRETE_IMP_COUNTABLE THEN
      REWRITE_TAC[IN_DIFF; IN_UNIV; IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN EXISTS_TAC `&1` THEN
      REWRITE_TAC[GSYM REAL_NOT_LT; GSYM dist; REAL_LT_01] THEN
      ASM_MESON_TAC[lemma];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM COMPLEX_SUB_0] THEN REWRITE_TAC[GSYM IN_SING] THEN
    MATCH_MP_TAC FORALL_IN_CLOSURE THEN REWRITE_TAC[CLOSED_SING] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      TRY(GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
          MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC) THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP HOLOMORPHIC_ON_IMP_CONTINUOUS_ON) THEN
      REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      REWRITE_TAC[IN_UNIV; WITHIN_UNIV] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC CONTINUOUS_AT_WITHIN THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[complex_div] THEN MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN
      CONJ_TAC THEN CONTINUOUS_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `z:complex` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SING; COMPLEX_SUB_0] THEN DISCH_TAC THEN
    EXPAND_TAC "g" THEN REWRITE_TAC[] THEN
    REWRITE_TAC[COMPLEX_RING `z / Cx(&2) = w <=> z = Cx(&2) * w`] THEN
    REWRITE_TAC[COMPLEX_RING `z + Cx(&1) = w <=> z = w - Cx(&1)`] THEN
    REWRITE_TAC[GSYM CX_MUL; GSYM CX_SUB] THEN
    REPEAT(COND_CASES_TAC THENL [ASM_MESON_TAC[INTEGER_CLOSED]; ALL_TAC]) THEN
    REWRITE_TAC[COMPLEX_RING
     `(a * b * c) * (d * e * f):complex =
      (a * d) * (e * b) * (c * f)`] THEN
    REWRITE_TAC[COMPLEX_RING
     `Cx(&1) - (z + Cx(&1)) / Cx(&2) = (Cx(&1) - z) / Cx(&2)`] THEN
    REWRITE_TAC[COMPLEX_RING
     `(z + Cx(&1)) / Cx(&2) = z / Cx(&2) + Cx(&1) / Cx(&2) /\
      Cx(&1) - z / Cx(&2) = ((Cx(&1) - z) / Cx(&2)) + Cx(&1) / Cx(&2)`] THEN
    REWRITE_TAC[CGAMMA_LEGENDRE_ALT] THEN
    MP_TAC(ISPEC `Cx(&1 / &2) * z * Cx pi` CSIN_DOUBLE) THEN
    MP_TAC(SPECL [`Cx(&2)`; `z:complex`; `--z:complex`] CPOW_ADD) THEN
    REWRITE_TAC[COMPLEX_ADD_RINV] THEN
    CONV_TAC(DEPTH_BINOP_CONV `==>`
     (BINOP_CONV(DEPTH_BINOP_CONV `complex_mul`
     (RAND_CONV COMPLEX_POLY_CONV)))) THEN
    REWRITE_TAC[CPOW_ADD; CX_NEG; COMPLEX_MUL_LNEG; COMPLEX_MUL_LID] THEN
    REWRITE_TAC[CPOW_N; CX_INJ; REAL_OF_NUM_EQ; ARITH_EQ; CSIN_ADD] THEN
    REWRITE_TAC[GSYM CX_MUL; GSYM CX_SIN; GSYM CX_COS; SIN_PI2; COS_PI2;
                REAL_ARITH `&1 / &2 * x = x / &2`] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?h. h holomorphic_on (:complex) /\
        !z. z IN (:complex) ==> g z = cexp(h z)`
  MP_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
      CONTRACTIBLE_IMP_HOLOMORPHIC_LOG) THEN
    ASM_REWRITE_TAC[CONTRACTIBLE_UNIV; IN_UNIV] THEN
    X_GEN_TAC `z:complex` THEN EXPAND_TAC "g" THEN
    COND_CASES_TAC THEN REWRITE_TAC[CX_INJ; PI_NZ] THEN
    REWRITE_TAC[CGAMMA_EQ_0; CSIN_EQ_0; COMPLEX_ENTIRE] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] CX_MUL] THEN
    REWRITE_TAC[COMPLEX_RING `a - z + b = Cx(&0) <=> z = a + b`] THEN
    REWRITE_TAC[COMPLEX_EQ_MUL_LCANCEL; CX_INJ; PI_NZ] THEN
    REWRITE_TAC[COMPLEX_RING `z + a =  Cx(&0) <=> z = --a`] THEN
    REWRITE_TAC[GSYM CX_ADD; GSYM CX_NEG] THEN ASM_MESON_TAC[INTEGER_CLOSED];
    REWRITE_TAC[IN_UNIV] THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM)] THEN
  MP_TAC(ISPECL [`h:complex->complex`; `(:complex)`]
        HOLOMORPHIC_ON_OPEN) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `h':complex->complex` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!z. (h'(z / Cx(&2)) + h'((z + Cx(&1)) / Cx(&2))) / Cx(&2) = h'(z)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:complex` THEN MATCH_MP_TAC
     (COMPLEX_RING `!a. ~(a = Cx(&0)) /\ a * x = a * y ==> x = y`) THEN
    EXISTS_TAC `g(z / Cx(&2)) * g((z + Cx(&1)) / Cx(&2))` THEN
    REWRITE_TAC[COMPLEX_ENTIRE] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[CEXP_NZ]; ALL_TAC] THEN
    MATCH_MP_TAC COMPLEX_DERIVATIVE_UNIQUE_AT THEN
    EXISTS_TAC `\z. g (z / Cx(&2)) * g ((z + Cx(&1)) / Cx(&2)):complex` THEN
    EXISTS_TAC `z:complex` THEN CONJ_TAC THENL
     [REWRITE_TAC[]; ASM_REWRITE_TAC[]] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o GEN_REWRITE_RULE I [GSYM FUN_EQ_THM]) THEN
    REWRITE_TAC[] THEN
    ASM GEN_COMPLEX_DIFF_TAC [] THEN
    (CONJ_TAC THENL [ASM_REWRITE_TAC[]; CONV_TAC COMPLEX_RING]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:complex->complex`; `h':complex->complex`; `(:complex)`]
        HOLOMORPHIC_DERIVATIVE) THEN
  ASM_REWRITE_TAC[OPEN_UNIV] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`h':complex->complex`; `(:complex)`]
        HOLOMORPHIC_ON_OPEN) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `h'':complex->complex` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!z. (h''(z / Cx(&2)) + h''((z + Cx(&1)) / Cx(&2))) / Cx(&4) = h''(z)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:complex` THEN
    MATCH_MP_TAC COMPLEX_DERIVATIVE_UNIQUE_AT THEN
    EXISTS_TAC `\z. (h'(z / Cx(&2)) + h'((z + Cx(&1)) / Cx(&2))) / Cx(&2)` THEN
    EXISTS_TAC `z:complex` THEN CONJ_TAC THENL
     [REWRITE_TAC[]; ASM_REWRITE_TAC[]] THEN
    ASM GEN_COMPLEX_DIFF_TAC [] THEN
    (CONJ_TAC THENL [ASM_REWRITE_TAC[ETA_AX]; CONV_TAC COMPLEX_RING]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h':complex->complex`; `h'':complex->complex`; `(:complex)`]
        HOLOMORPHIC_DERIVATIVE) THEN
  ASM_REWRITE_TAC[OPEN_UNIV] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!z. z IN (:complex) ==> h''(z) = Cx(&0)` MP_TAC THENL
   [MATCH_MP_TAC ANALYTIC_CONTINUATION THEN
    EXISTS_TAC `cball(Cx(&0),&1)` THEN EXISTS_TAC `Cx(&0)` THEN
    ASM_REWRITE_TAC[CONNECTED_UNIV; SUBSET_UNIV; IN_UNIV] THEN
    SIMP_TAC[INTERIOR_LIMIT_POINT; INTERIOR_CBALL; CENTRE_IN_BALL;
             OPEN_UNIV; REAL_LT_01] THEN
    MP_TAC(ISPECL [`\z. norm((h'':complex->complex) z)`; `cball(Cx(&0),&1)`]
        CONTINUOUS_ATTAINS_SUP) THEN
    ASM_REWRITE_TAC[COMPLEX_IN_CBALL_0; COMPACT_CBALL; CBALL_EQ_EMPTY] THEN
    REWRITE_TAC[o_DEF] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ANTS_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
      ASM_MESON_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON; CONTINUOUS_ON_SUBSET;
                    SUBSET_UNIV];
      DISCH_THEN(X_CHOOSE_THEN `w:complex` STRIP_ASSUME_TAC) THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
      MATCH_MP_TAC(NORM_ARITH
       `!w:complex. norm(w) <= norm(w) / &2 /\ norm(z) <= norm(w)
                    ==> z = vec 0`) THEN
      EXISTS_TAC `(h'':complex->complex) w` THEN ASM_SIMP_TAC[] THEN
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM th]) THEN
      REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
      MATCH_MP_TAC(NORM_ARITH
       `norm(a) <= e /\ norm(b) <= e ==> norm(a + b) / &4 <= e / &2`) THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
      UNDISCH_TAC `norm(w:complex) <= &1` THEN
      MP_TAC(SPEC `&1` COMPLEX_NORM_CX) THEN CONV_TAC NORM_ARITH];
      REWRITE_TAC[IN_UNIV] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`h':complex->complex`; `(:complex)`]
        HAS_COMPLEX_DERIVATIVE_ZERO_CONSTANT) THEN
  REWRITE_TAC[CONVEX_UNIV; IN_UNIV] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[HAS_COMPLEX_DERIVATIVE_AT_WITHIN]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `a:complex`) THEN
  MP_TAC(ISPECL [`\z. (h:complex->complex) z - a * z`; `(:complex)`]
        HAS_COMPLEX_DERIVATIVE_ZERO_CONSTANT) THEN
  REWRITE_TAC[CONVEX_UNIV; IN_UNIV] THEN ANTS_TAC THENL
   [GEN_TAC THEN ASM GEN_COMPLEX_DIFF_TAC[] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC COMPLEX_RING;
    REWRITE_TAC[COMPLEX_RING `a - b:complex = c <=> a = b + c`] THEN
    DISCH_THEN(X_CHOOSE_TAC `b:complex`)] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&1`; `Cx(&0)`]) THEN
  MP_TAC(ASSUME `!z:complex. cexp (h z) = g z`) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[ ASSUME`!x. (h:complex->complex) x = a * x + b`] THEN
  REWRITE_TAC[INTEGER_CLOSED; COMPLEX_ADD_LID; COMPLEX_MUL_RZERO] THEN
  REWRITE_TAC[CEXP_ADD; COMPLEX_MUL_RID] THEN
  REWRITE_TAC[COMPLEX_RING `a * b = b <=> a = Cx(&1) \/ b = Cx(&0)`] THEN
  REWRITE_TAC[CEXP_NZ; CEXP_EQ_1] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `!z:complex. cexp(h z) = g z` THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `n = &0` THENL
   [SUBST1_TAC(SYM(SPEC `a:complex` COMPLEX)) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; GSYM CX_DEF] THEN
    REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_ADD_LID] THEN
    DISCH_THEN(ASSUME_TAC o GSYM) THEN X_GEN_TAC `z:complex` THEN
    ASM_CASES_TAC `?n. integer n /\ z = Cx n` THENL
     [REWRITE_TAC[complex_div] THEN
      MATCH_MP_TAC(COMPLEX_RING
       `z = Cx(&0) /\ ((w = Cx(&0)) \/ (y = Cx(&0)))
        ==> w * y = p * z`) THEN
      REWRITE_TAC[CGAMMA_EQ_0; CSIN_EQ_0; COMPLEX_INV_EQ_0] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[REAL_MUL_SYM; CX_MUL]; ALL_TAC] THEN
      REWRITE_TAC[OR_EXISTS_THM; GSYM COMPLEX_ADD_ASSOC] THEN
      REWRITE_TAC[COMPLEX_RING `c - z + n = Cx(&0) <=> z = n + c`] THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `m:real`
       (CONJUNCTS_THEN2 MP_TAC SUBST1_TAC)) THEN
      REWRITE_TAC[integer] THEN DISCH_THEN(X_CHOOSE_THEN `p:num`
        (MP_TAC o MATCH_MP (REAL_ARITH `abs x = n ==> x = n \/ x = --n`))) THEN
      DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
      REWRITE_TAC[GSYM CX_ADD; CX_INJ; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ;
                  REAL_ARITH `--p + n = &0 <=> p = n`] THEN
      REWRITE_TAC[EXISTS_OR_THM; GSYM EXISTS_REFL] THEN
      REWRITE_TAC[ADD_EQ_0; RIGHT_EXISTS_AND_THM; EXISTS_REFL] THEN
      MESON_TAC[num_CASES; ADD1];
      SUBGOAL_THEN `(g:complex->complex) z = g(Cx(&0))` MP_TAC THENL
       [ASM_REWRITE_TAC[]; EXPAND_TAC "g"] THEN
      ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[INTEGER_CLOSED]] THEN
      MP_TAC PI_NZ THEN REWRITE_TAC[GSYM CX_INJ] THEN CONV_TAC COMPLEX_FIELD];
    DISCH_THEN(fun th ->
      MP_TAC(SPEC `Cx(inv(&4 * n))` th) THEN MP_TAC(SPEC `Cx(&0)` th)) THEN
    REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_ADD_LID] THEN
    SUBGOAL_THEN `g(Cx(&0)) = Cx pi` SUBST1_TAC THENL
     [ASM_MESON_TAC[INTEGER_CLOSED]; ALL_TAC] THEN
    REWRITE_TAC[CEXP_ADD] THEN DISCH_THEN SUBST1_TAC THEN
    SUBST1_TAC(SYM(SPEC `a:complex` COMPLEX)) THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (funpow 3 LAND_CONV o RAND_CONV) [complex_mul] THEN
    REWRITE_TAC[RE; IM; REAL_MUL_LZERO; IM_CX; RE_CX] THEN
    REWRITE_TAC[CEXP_COMPLEX; REAL_ADD_LID] THEN ASM_SIMP_TAC[REAL_FIELD
     `~(n = &0) ==> (&2 * n * pi) * inv(&4 * n) = pi / &2`] THEN
    REWRITE_TAC[SIN_PI2; COS_PI2; GSYM ii] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_REFL; REAL_EXP_0] THEN
    REWRITE_TAC[COMPLEX_MUL_LID] THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN EXPAND_TAC "g" THEN
    ASM_SIMP_TAC[CX_INJ; REAL_FIELD
     `~(n = &0) ==> (inv(&4 * n) = m <=> &4 * m * n = &1)`] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o AP_TERM `abs`) THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
      REPEAT(FIRST_X_ASSUM(CHOOSE_TAC o GEN_REWRITE_RULE I [integer])) THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_EQ; MULT_EQ_1] THEN
      CONV_TAC NUM_REDUCE_CONV;
      MATCH_MP_TAC(MESON[] `real y /\ ~real x ==> ~(x = y)`) THEN
      SIMP_TAC[GSYM CX_SUB; GSYM CX_MUL; REAL_CX; REAL_SIN; REAL_GAMMA;
               REAL_MUL; ONCE_REWRITE_RULE[COMPLEX_MUL_SYM] REAL_MUL_CX] THEN
      REWRITE_TAC[PI_NZ; real; IM_II] THEN ARITH_TAC]]);;

let CGAMMA_HALF = prove
 (`cgamma(Cx(&1) / Cx(&2)) = Cx(sqrt pi)`,
  MP_TAC(SPEC `Cx(&1) / Cx(&2)` CGAMMA_REFLECTION) THEN
  REWRITE_TAC[COMPLEX_RING `Cx(&1) - Cx(&1) / Cx(&2) = Cx(&1) / Cx(&2)`] THEN
  REWRITE_TAC[GSYM CX_DIV; GSYM CX_MUL; GSYM CX_SIN] THEN
  REWRITE_TAC[REAL_ARITH `x * &1 / &2 = x / &2`; SIN_PI2; REAL_DIV_1] THEN
  SUBGOAL_THEN `Cx pi = Cx(sqrt pi) pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM CX_POW] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    REWRITE_TAC[SQRT_POW2; PI_POS_LE];
    REWRITE_TAC[COMPLEX_RING
     `a * a:complex = b pow 2 <=> a = b \/ a = --b`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `Cx(&1 / &2)` RE_POS_CGAMMA_REAL) THEN
    ASM_REWRITE_TAC[REAL_CX; RE_CX; RE_NEG] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    REWRITE_TAC[REAL_ARITH `~(&0 <= --x) <=> &0 < x`] THEN
    MATCH_MP_TAC SQRT_POS_LT THEN REWRITE_TAC[PI_POS]]);;

let CGAMMA_LEGENDRE = prove
 (`!z. cgamma(z) * cgamma(z + Cx(&1) / Cx(&2)) =
       Cx(&2) cpow (Cx(&1) - Cx(&2) * z) * Cx(sqrt pi) * cgamma(Cx(&2) * z)`,
  REWRITE_TAC[CGAMMA_LEGENDRE_ALT; CGAMMA_HALF]);;

(* ------------------------------------------------------------------------- *)
(* Thw Weierstrass product definition.                                       *)
(* ------------------------------------------------------------------------- *)

let CGAMMA_WEIERSTRASS = prove
 (`!z. ((\n. cexp(--(Cx euler_mascheroni) * z) / z *
             cproduct(1..n) (\k. cexp(z / Cx(&k)) / (Cx(&1) + z / Cx(&k))))
       --> cgamma z) sequentially`,
  GEN_TAC THEN SIMP_TAC[complex_div; CPRODUCT_MUL; FINITE_NUMSEG] THEN
  MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\n. (cexp(--Cx euler_mascheroni * z) *
                   cproduct(1..n) (\k. cexp(z * inv(Cx(&k)))) *
                   cexp(--Cx(log(&n)) * z)) *
                  (Cx(&n) cpow z / z *
                   cproduct (1..n) (\k. inv(Cx(&1) + z * inv(Cx(&k)))))` THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN CONJ_TAC THENL
   [EXISTS_TAC `1` THEN REPEAT STRIP_TAC THEN REWRITE_TAC[complex_div] THEN
    MATCH_MP_TAC(COMPLEX_RING
     `c * c' = Cx(&1) ==> (a * b * c) * (c' * d) * e = ((a * d) * b * e)`) THEN
    ASM_SIMP_TAC[cpow; CX_INJ; REAL_OF_NUM_EQ; LE_1; GSYM CEXP_ADD] THEN
    REWRITE_TAC[GSYM CEXP_0] THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[CX_LOG; REAL_OF_NUM_LT; LE_1] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM COMPLEX_MUL_LID] THEN
  MATCH_MP_TAC LIM_COMPLEX_MUL THEN CONJ_TAC THENL
   [SIMP_TAC[GSYM CEXP_VSUM; FINITE_NUMSEG; GSYM CEXP_ADD] THEN
    REWRITE_TAC[GSYM CEXP_0] THEN
    MATCH_MP_TAC(ISPEC `cexp` LIM_CONTINUOUS_FUNCTION) THEN
    SIMP_TAC[CONTINUOUS_AT_CEXP; VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
    REWRITE_TAC[COMPLEX_RING
     `--w * z + z * x + --y * z:complex = z * ((x - y) - w)`] THEN
    MATCH_MP_TAC LIM_NULL_COMPLEX_LMUL THEN
    REWRITE_TAC[GSYM LIM_NULL_COMPLEX] THEN
    REWRITE_TAC[GSYM CX_INV; VSUM_CX] THEN
    REWRITE_TAC[GSYM CX_SUB; REWRITE_RULE[o_DEF] (GSYM REALLIM_COMPLEX)] THEN
    REWRITE_TAC[EULER_MASCHERONI];
    MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN EXISTS_TAC
     `\n. (Cx(&n) cpow z * Cx(&(FACT n))) /
          cproduct(0..n) (\m. z + Cx(&m))` THEN
    REWRITE_TAC[CGAMMA] THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SIMP_TAC[CPRODUCT_CLAUSES_LEFT; LE_0] THEN
    REWRITE_TAC[COMPLEX_ADD_RID; ADD_CLAUSES] THEN
    REWRITE_TAC[complex_div; COMPLEX_INV_MUL; GSYM COMPLEX_MUL_ASSOC] THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC LAND_CONV
     [COMPLEX_RING `a * b * c:complex = b * a * c`] THEN
    AP_TERM_TAC THEN SIMP_TAC[CPRODUCT_INV; FINITE_NUMSEG] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM COMPLEX_INV_INV] THEN
    REWRITE_TAC[GSYM COMPLEX_INV_MUL] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(COMPLEX_FIELD
     `~(z = Cx(&0)) /\ z * x = y ==> inv z * y = x`) THEN
    REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ; FACT_NZ] THEN
    CONV_TAC SYM_CONV THEN SPEC_TAC(`n:num`,`p:num`) THEN
    INDUCT_TAC THEN REWRITE_TAC[FACT; CPRODUCT_CLAUSES_NUMSEG; ARITH] THEN
    REWRITE_TAC[ARITH_RULE `1 <= SUC n`; COMPLEX_MUL_LID] THEN
    ASM_REWRITE_TAC[CX_MUL; GSYM REAL_OF_NUM_MUL] THEN
    MATCH_MP_TAC(COMPLEX_RING
     `d * e:complex = c ==> (a * b) * c = (d * a) * b * e`) THEN
    MATCH_MP_TAC(COMPLEX_FIELD
     `~(p = Cx(&0)) ==> p * (Cx(&1) + z * inv p) = z + p`) THEN
    REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ; NOT_SUC]]);;

(* ------------------------------------------------------------------------- *)
(* Sometimes the reciprocal function is convenient, since it's entire.       *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_DIFFERENTIABLE_AT_RECIP_CGAMMA = prove
 (`!z. (inv o cgamma) complex_differentiable (at z)`,
  GEN_TAC THEN ASM_CASES_TAC `!n. ~(z + Cx(&n) = Cx(&0))` THENL
   [MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_COMPOSE_AT THEN
    ASM_SIMP_TAC[COMPLEX_DIFFERENTIABLE_AT_CGAMMA] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_INV_AT THEN
    REWRITE_TAC[COMPLEX_DIFFERENTIABLE_ID; CGAMMA_EQ_0] THEN
    ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
    REWRITE_TAC[COMPLEX_RING `z + w = Cx(&0) <=> z = --w`] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
    REWRITE_TAC[complex_differentiable; HAS_COMPLEX_DERIVATIVE_AT] THEN
    REWRITE_TAC[o_DEF; CGAMMA_POLES; COMPLEX_INV_0; complex_div;
                COMPLEX_MUL_LZERO; COMPLEX_SUB_RZERO] THEN
    SIMP_TAC[GSYM COMPLEX_INV_MUL; COMPLEX_RING `x - --z:complex = x + z`] THEN
    EXISTS_TAC `inv(--Cx(&1) pow n / Cx(&(FACT n)))` THEN
    MATCH_MP_TAC LIM_COMPLEX_INV THEN
    REWRITE_TAC[COMPLEX_DIV_EQ_0; COMPLEX_POW_EQ_0; CX_INJ] THEN
    REWRITE_TAC[REAL_OF_NUM_EQ; FACT_NZ] THEN
    ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
    REWRITE_TAC[CGAMMA_SIMPLE_POLES] THEN CONV_TAC COMPLEX_RING]);;

let COMPLEX_DIFFERENTIABLE_WITHIN_RECIP_CGAMMA = prove
 (`!z s. (inv o cgamma) complex_differentiable at z within s`,
  SIMP_TAC[COMPLEX_DIFFERENTIABLE_AT_WITHIN;
           COMPLEX_DIFFERENTIABLE_AT_RECIP_CGAMMA]);;

let HOLOMORPHIC_ON_RECIP_CGAMMA = prove
 (`!s. (inv o cgamma) holomorphic_on s`,
  REWRITE_TAC[HOLOMORPHIC_ON_DIFFERENTIABLE] THEN
  REWRITE_TAC[COMPLEX_DIFFERENTIABLE_WITHIN_RECIP_CGAMMA]);;

let CONTINUOUS_AT_RECIP_CGAMMA = prove
 (`!z. (inv o cgamma) continuous at z`,
  SIMP_TAC[COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT;
           COMPLEX_DIFFERENTIABLE_AT_RECIP_CGAMMA]);;

let CONTINUOUS_WITHIN_RECIP_CGAMMA = prove
 (`!z s. (inv o cgamma) continuous at z within s`,
  SIMP_TAC[COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN;
           COMPLEX_DIFFERENTIABLE_WITHIN_RECIP_CGAMMA]);;

let CONTINUOUS_ON_RECIP_CGAMMA = prove
 (`!s. (inv o cgamma) continuous_on s`,
  SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON; HOLOMORPHIC_ON_RECIP_CGAMMA]);;

let RECIP_CGAMMA = prove
 (`!z. ((\n. cproduct(0..n) (\m. z + Cx(&m)) /
            (Cx(&n) cpow z * Cx(&(FACT n)))) --> inv(cgamma z))
       sequentially`,
  GEN_TAC THEN ASM_CASES_TAC `!n. ~(z + Cx(&n) = Cx(&0))` THENL
   [ONCE_REWRITE_TAC[GSYM COMPLEX_INV_INV] THEN
    MATCH_MP_TAC LIM_COMPLEX_INV THEN
    REWRITE_TAC[COMPLEX_INV_INV; CGAMMA; COMPLEX_INV_DIV; CGAMMA_EQ_0] THEN
    ASM_MESON_TAC[];
    SUBGOAL_THEN `cgamma z = Cx(&0)` SUBST1_TAC THENL
     [ASM_MESON_TAC[CGAMMA_EQ_0]; REWRITE_TAC[COMPLEX_INV_0]] THEN
    MATCH_MP_TAC LIM_EVENTUALLY THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY; COMPLEX_DIV_EQ_0; COMPLEX_ENTIRE] THEN
    SIMP_TAC[CPRODUCT_EQ_0; IN_NUMSEG; FINITE_NUMSEG; LE_0] THEN
    ASM_MESON_TAC[]]);;

let RECIP_CGAMMA_WEIERSTRASS = prove
 (`!n. ((\n. (z * cexp(Cx euler_mascheroni * z) *
             cproduct(1..n) (\k. (Cx(&1) + z / Cx(&k)) / cexp(z / Cx(&k)))))
        --> inv(cgamma z)) sequentially`,
  GEN_TAC THEN ASM_CASES_TAC `?n. z + Cx(&n) = Cx(&0)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `N:num`) THEN
    MATCH_MP_TAC LIM_EVENTUALLY THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[GE] THEN
    DISCH_TAC THEN SUBGOAL_THEN `cgamma(z) = Cx(&0)` SUBST1_TAC THENL
     [ASM_MESON_TAC[CGAMMA_EQ_0]; REWRITE_TAC[COMPLEX_INV_0]] THEN
    REWRITE_TAC[COMPLEX_ENTIRE; COMPLEX_DIV_EQ_0] THEN
    ASM_CASES_TAC `N = 0` THENL [ASM_MESON_TAC[COMPLEX_ADD_RID]; ALL_TAC] THEN
    REPEAT DISJ2_TAC THEN
    SIMP_TAC[CPRODUCT_EQ_0; FINITE_NUMSEG; IN_NUMSEG] THEN
    EXISTS_TAC `N:num` THEN ASM_SIMP_TAC[LE_1; COMPLEX_DIV_EQ_0] THEN
    DISJ1_TAC THEN MATCH_MP_TAC(COMPLEX_FIELD
     `x + n = Cx(&0) /\ ~(n = Cx(&0)) ==> Cx(&1) + x / n = Cx(&0)`) THEN
    ASM_REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ];
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ABS_CONV)
     [GSYM COMPLEX_INV_INV] THEN
    MATCH_MP_TAC LIM_COMPLEX_INV THEN
    ASM_REWRITE_TAC[CGAMMA_EQ_0] THEN
    SIMP_TAC[COMPLEX_INV_MUL; GSYM CEXP_NEG; GSYM CPRODUCT_INV;
             FINITE_NUMSEG; GSYM COMPLEX_MUL_LNEG; COMPLEX_INV_DIV] THEN
    REWRITE_TAC[SIMPLE_COMPLEX_ARITH `inv z * a * b:complex = a / z * b`] THEN
    REWRITE_TAC[CGAMMA_WEIERSTRASS]]);;

(* ------------------------------------------------------------------------- *)
(* The real gamma function.                                                  *)
(* ------------------------------------------------------------------------- *)

let gamma = new_definition
 `gamma(x) = Re(cgamma(Cx x))`;;

let CX_GAMMA = prove
 (`!x. Cx(gamma x) = cgamma(Cx x)`,
    REWRITE_TAC[gamma] THEN MESON_TAC[REAL; REAL_CX; REAL_GAMMA]);;

let GAMMA = prove
 (`!x. ((\n. (&n rpow x * &(FACT n)) / product(0..n) (\m. x + &m))
        ---> gamma(x)) sequentially`,
  REWRITE_TAC[REALLIM_COMPLEX; o_DEF; CX_GAMMA; CX_DIV] THEN
  X_GEN_TAC `x:real` THEN MP_TAC(SPEC `Cx x` CGAMMA) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
  SIMP_TAC[CX_MUL; CX_PRODUCT; FINITE_NUMSEG; CX_ADD; cpow; rpow;
           CX_INJ; REAL_OF_NUM_EQ; REAL_OF_NUM_LT; LE_1; CX_LOG; CX_EXP]);;

let GAMMA_EQ_0 = prove
 (`!x. gamma(x) = &0 <=> ?n. x + &n = &0`,
  REWRITE_TAC[GSYM CX_INJ; CX_ADD; CX_GAMMA; CGAMMA_EQ_0]);;

let REAL_DIFFERENTIABLE_AT_GAMMA = prove
 (`!x. (!n. ~(x + &n = &0)) ==> gamma real_differentiable atreal x`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
  REWRITE_TAC[gamma] THEN
  MATCH_MP_TAC (REWRITE_RULE[o_DEF] REAL_DIFFERENTIABLE_FROM_COMPLEX_AT) THEN
  REWRITE_TAC[REAL_GAMMA] THEN
  MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_AT_CGAMMA THEN
  ASM_REWRITE_TAC[GSYM CX_ADD; CX_INJ]);;

let REAL_DIFFERENTIABLE_WITHIN_GAMMA = prove
 (`!x s. (!n. ~(x + &n = &0)) ==> gamma real_differentiable atreal x within s`,
  SIMP_TAC[REAL_DIFFERENTIABLE_AT_GAMMA;
           REAL_DIFFERENTIABLE_ATREAL_WITHIN]);;

let REAL_DIFFERENTIABLE_ON_GAMMA = prove
 (`!s. s SUBSET {x | !n. ~(x + &n = &0)} ==> gamma real_differentiable_on s`,
  SIMP_TAC[SUBSET; IN_ELIM_THM; REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE;
           REAL_DIFFERENTIABLE_WITHIN_GAMMA]);;

let REAL_CONTINUOUS_ATREAL_GAMMA = prove
 (`!x. (!n. ~(x + &n = &0)) ==> gamma real_continuous atreal x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_COMPLEX_CONTINUOUS_ATREAL] THEN
  REWRITE_TAC[o_DEF; CX_GAMMA] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_WITHIN_COMPOSE THEN
  SIMP_TAC[LINEAR_CONTINUOUS_WITHIN; REWRITE_RULE[o_DEF] LINEAR_CX_RE] THEN
  MATCH_MP_TAC CONTINUOUS_AT_WITHIN THEN
  MATCH_MP_TAC CONTINUOUS_AT_CGAMMA THEN
  ASM_REWRITE_TAC[GSYM CX_ADD; RE_CX; CX_INJ]);;

let REAL_CONTINUOUS_WITHIN_GAMMA = prove
 (`!x s. (!n. ~(x + &n = &0)) ==> gamma real_continuous atreal x within s`,
  SIMP_TAC[REAL_CONTINUOUS_ATREAL_WITHINREAL; REAL_CONTINUOUS_ATREAL_GAMMA]);;

let REAL_CONTINUOUS_ON_GAMMA = prove
 (`!s. s SUBSET {x | !n. ~(x + &n = &0)} ==> gamma real_continuous_on s`,
  SIMP_TAC[SUBSET; IN_ELIM_THM; REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
           REAL_CONTINUOUS_WITHIN_GAMMA]);;

let REAL_DIFFERENTIABLE_ATREAL_RECIP_GAMMA = prove
 (`!x. (inv o gamma) real_differentiable (atreal x)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[o_DEF; gamma] THEN
  MATCH_MP_TAC REAL_DIFFERENTIABLE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\x. Re(inv(cgamma(Cx x)))` THEN
  EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM CX_GAMMA; GSYM CX_INV; RE_CX];
    MATCH_MP_TAC (REWRITE_RULE[o_DEF] REAL_DIFFERENTIABLE_FROM_COMPLEX_AT) THEN
    SIMP_TAC[REAL_GAMMA; REAL_INV; GSYM o_DEF] THEN
    REWRITE_TAC[COMPLEX_DIFFERENTIABLE_AT_RECIP_CGAMMA]]);;

let REAL_DIFFERENTIABLE_WITHIN_RECIP_GAMMA = prove
 (`!x s. (inv o gamma) real_differentiable atreal x within s`,
  SIMP_TAC[REAL_DIFFERENTIABLE_ATREAL_WITHIN;
           REAL_DIFFERENTIABLE_ATREAL_RECIP_GAMMA]);;

let REAL_DIFFERENTIABLE_ON_RECIP_GAMMA = prove
 (`!s. (inv o gamma) real_differentiable_on s`,
  REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE;
              REAL_DIFFERENTIABLE_WITHIN_RECIP_GAMMA]);;

let REAL_CONTINUOUS_ATREAL_RECIP_GAMMA = prove
 (`!x. (inv o gamma) real_continuous atreal x`,
  SIMP_TAC[REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL;
           REAL_DIFFERENTIABLE_ATREAL_RECIP_GAMMA]);;

let REAL_CONTINUOUS_WITHINREAL_RECIP_GAMMA = prove
 (`!x s. (inv o gamma) real_continuous atreal x within s`,
  SIMP_TAC[REAL_CONTINUOUS_ATREAL_WITHINREAL;
           REAL_CONTINUOUS_ATREAL_RECIP_GAMMA]);;

let REAL_CONTINUOUS_ON_RECIP_GAMMA = prove
 (`!s. (inv o gamma) real_continuous_on s`,
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
              REAL_CONTINUOUS_WITHINREAL_RECIP_GAMMA]);;

let GAMMA_RECURRENCE_ALT = prove
 (`!x. gamma(x) = gamma(x + &1) / x`,
  REWRITE_TAC[GSYM CX_INJ; CX_DIV; CX_GAMMA; CX_ADD] THEN
  REWRITE_TAC[GSYM CGAMMA_RECURRENCE_ALT]);;

let GAMMA_1 = prove
 (`gamma(&1) = &1`,
  REWRITE_TAC[GSYM CX_INJ; CX_GAMMA; CGAMMA_1]);;

let GAMMA_RECURRENCE = prove
 (`!x. gamma(x + &1) = if x = &0 then &1 else x * gamma(x)`,
  REWRITE_TAC[GSYM CX_INJ; CX_GAMMA] THEN
  GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN
  REWRITE_TAC[CX_MUL; CX_GAMMA; CX_ADD; GSYM CGAMMA_RECURRENCE]);;

let GAMMA_FACT = prove
 (`!n. gamma(&(n + 1)) = &(FACT n)`,
  REWRITE_TAC[GSYM CX_INJ; CX_GAMMA; CGAMMA_FACT]);;

let GAMMA_POLES = prove
 (`!n. gamma(--(&n)) = &0`,
  REWRITE_TAC[GSYM CX_INJ; CX_GAMMA; CGAMMA_POLES; CX_NEG]);;

let GAMMA_SIMPLE_POLES = prove
 (`!n. ((\x. (x + &n) * gamma x) ---> -- &1 pow n / &(FACT n))
       (atreal(-- &n))`,
  REWRITE_TAC[REALLIM_COMPLEX; o_DEF; LIM_ATREAL_ATCOMPLEX] THEN
  GEN_TAC THEN
  REWRITE_TAC[CX_MUL; CX_ADD; CX_GAMMA; CX_DIV; CX_POW; CX_NEG] THEN
  SUBGOAL_THEN
   `(\z. (Cx(Re z) + Cx(&n)) * cgamma(Cx(Re z))) =
    (\z. (z + Cx(&n)) * cgamma z) o (Cx o Re)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC LIM_COMPOSE_WITHIN THEN
  MAP_EVERY EXISTS_TAC [`(:complex)`; `--Cx(&n)`] THEN
  REWRITE_TAC[CGAMMA_SIMPLE_POLES; WITHIN_UNIV] THEN
  REWRITE_TAC[EVENTUALLY_WITHIN; o_DEF; IN_UNIV; GSYM DIST_NZ] THEN
  REWRITE_TAC[real; IN; GSYM CX_NEG; CX_INJ] THEN
  REWRITE_TAC[COMPLEX_EQ; RE_CX; IM_CX] THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[REAL_LT_01]] THEN
  MATCH_MP_TAC LIM_AT_WITHIN THEN LIM_TAC THEN REWRITE_TAC[RE_CX] THEN
  MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
  REWRITE_TAC[REWRITE_RULE[o_DEF] LINEAR_CX_RE]);;

let GAMMA_POS_LE = prove
 (`!x. &0 <= x ==> &0 <= gamma x`,
  SIMP_TAC[gamma; RE_POS_CGAMMA_REAL; RE_CX; REAL_CX]);;

let GAMMA_POS_LT = prove
 (`!x. &0 < x ==> &0 < gamma x`,
  SIMP_TAC[REAL_ARITH `&0 < x <=> &0 <= x /\ ~(x = &0)`; GAMMA_POS_LE] THEN
  REWRITE_TAC[GAMMA_EQ_0] THEN REAL_ARITH_TAC);;

let GAMMA_LEGENDRE_ALT = prove
 (`!x. gamma(x) * gamma(x + &1 / &2) =
       &2 rpow (&1 - &2 * x) *  gamma(&1 / &2) * gamma(&2 * x)`,
  REWRITE_TAC[GSYM CX_INJ; CX_GAMMA; CX_ADD;
              CX_DIV; CGAMMA_LEGENDRE_ALT; CX_MUL] THEN
  REWRITE_TAC[cpow; rpow; CX_INJ; REAL_OF_NUM_LT; REAL_OF_NUM_EQ; ARITH] THEN
  SIMP_TAC[CX_MUL; CX_EXP; CX_SUB; CX_LOG; REAL_OF_NUM_LT; ARITH]);;

let GAMMA_REFLECTION = prove
 (`!x. gamma(x) * gamma(&1 - x) = pi / sin(pi * x)`,
  SIMP_TAC[GSYM CX_INJ; CX_MUL; CX_DIV; CX_GAMMA; CX_SIN; CX_SUB] THEN
  REWRITE_TAC[CGAMMA_REFLECTION]);;

let GAMMA_HALF = prove
 (`gamma(&1 / &2) = sqrt pi`,
  REWRITE_TAC[GSYM CX_INJ; CX_DIV; CX_GAMMA; CGAMMA_HALF]);;

let GAMMA_LEGENDRE = prove
 (`!x. gamma(x) * gamma(x + &1 / &2) =
       &2 rpow (&1 - &2 * x) * sqrt pi * gamma(&2 * x)`,
  REWRITE_TAC[GAMMA_LEGENDRE_ALT; GAMMA_HALF]);;

let GAMMA_WEIERSTRASS = prove
 (`!x. ((\n. exp(--(euler_mascheroni) * x) / x *
             product(1..n) (\k. exp(x / &k) / (&1 + x / &k)))
       ---> gamma x) sequentially`,
  REWRITE_TAC[REALLIM_COMPLEX; o_DEF; CX_GAMMA; CX_DIV] THEN
  X_GEN_TAC `x:real` THEN MP_TAC(SPEC `Cx x` CGAMMA_WEIERSTRASS) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
  SIMP_TAC[CX_MUL; CX_DIV; CX_EXP; CX_NEG; CX_PRODUCT; FINITE_NUMSEG;
           CX_ADD]);;

(* ------------------------------------------------------------------------- *)
(* Characterization of the real gamma function using log-convexity.          *)
(* ------------------------------------------------------------------------- *)

let REAL_LOG_CONVEX_GAMMA = prove
 (`!s. (!x. x IN s ==> &0 < x) ==> gamma real_log_convex_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LOG_CONVEX_ON_SUBSET THEN
  EXISTS_TAC `{x | &0 < x}` THEN
  ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN POP_ASSUM(K ALL_TAC) THEN
  MATCH_MP_TAC(ISPEC `sequentially` REAL_LOG_CONVEX_LIM) THEN
  EXISTS_TAC `\n x. (&n rpow x * &(FACT n)) / product(0..n) (\m. x + &m)` THEN
  REWRITE_TAC[GAMMA; TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  REPEAT(MATCH_MP_TAC REAL_LOG_CONVEX_MUL THEN CONJ_TAC) THEN
  SIMP_TAC[REAL_LOG_CONVEX_CONST; REAL_POS] THEN
  ASM_SIMP_TAC[REAL_LOG_CONVEX_RPOW_RIGHT; REAL_OF_NUM_LT; LE_1] THEN
  SIMP_TAC[GSYM PRODUCT_INV; FINITE_NUMSEG] THEN
  MATCH_MP_TAC REAL_LOG_CONVEX_PRODUCT THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `k:num` THEN
  STRIP_TAC THEN
  MATCH_MP_TAC MIDPOINT_REAL_LOG_CONVEX THEN
  ASM_SIMP_TAC[IN_ELIM_THM; REAL_LT_INV_EQ; REAL_LTE_ADD; REAL_POS] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
    REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_INV_MUL; REAL_POW_INV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_LTE_ADD; REAL_POS] THEN
    REWRITE_TAC[REAL_LE_POW_2; REAL_ARITH
     `(x + &k) * (y + &k) <= ((x + y) / &2 + &k) pow 2 <=>
      &0 <= (x - y) pow 2`]]);;

let GAMMA_REAL_LOG_CONVEX_UNIQUE = prove
 (`!f:real->real.
        f(&1) = &1 /\ (!x. &0 < x ==> f(x + &1) = x * f(x)) /\
        (!x. &0 < x ==> &0 < f x) /\ f real_log_convex_on {x | &0 < x}
        ==> !x. &0 < x ==> f x = gamma x`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. &0 < x /\ x <= &1 ==> f x = gamma x` ASSUME_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN
     `!y. &0 < y /\ y <= &1 ==> !n. f(&n + y) = gamma(&n + y)`
    ASSUME_TAC THENL
     [GEN_TAC THEN STRIP_TAC THEN
      INDUCT_TAC THEN ASM_SIMP_TAC[REAL_ADD_LID] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
      REWRITE_TAC[REAL_ARITH `(n + &1) + x = (n + x) + &1`] THEN
      ASM_SIMP_TAC[GAMMA_RECURRENCE; REAL_LET_ADD; REAL_POS] THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real` THEN DISCH_TAC THEN
      MP_TAC(SPEC `x:real` FLOOR_POS) THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
      MP_TAC(SPEC `x:real` FLOOR_FRAC) THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `frac x = &0` THEN ASM_REWRITE_TAC[REAL_LT_LE] THENL
       [ASM_CASES_TAC `n = 0` THEN
        ASM_SIMP_TAC[REAL_ADD_RID; REAL_LT_IMP_NZ] THEN
        SUBGOAL_THEN `&(n - 1) + &1 = &n`
         (fun th -> ASM_MESON_TAC[th; REAL_LE_REFL; REAL_LT_01]) THEN
        ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; LE_1] THEN REAL_ARITH_TAC;
        STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `frac x`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]]]]] THEN
  X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `x = &1` THEN ASM_REWRITE_TAC[GAMMA_1] THEN
  SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_FIELD `&0 < g /\ f / g = &1 ==> f = g`) THEN
  ASM_SIMP_TAC[GAMMA_POS_LT] THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC
   `\n. f(x) / ((&n rpow x * &(FACT n)) / product (0..n) (\m. x + &m))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  ASM_SIMP_TAC[REALLIM_DIV; REALLIM_CONST; GAMMA_POS_LT;
               GAMMA; REAL_LT_IMP_NZ] THEN
  ONCE_REWRITE_TAC[REALLIM_NULL] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. x * inv(&n)` THEN
  SIMP_TAC[REALLIM_NULL_LMUL; REALLIM_1_OVER_N] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `2` THEN
  SUBGOAL_THEN
   `!n. &2 <= &n
        ==> log(f(&n)) - log(f(&n - &1))
              <= (log(f(&n + x)) - log(f(&n))) / x /\
            (log(f(&n + x)) - log(f(&n))) / x
              <= log(f(&n + &1)) - log(f(&n))`
  MP_TAC THENL
   [MP_TAC(SPECL [`f:real->real`; `{x | &0 < x}`] REAL_LOG_CONVEX_ON) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
     [REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      DISCH_TAC] THEN
    MAP_EVERY (MP_TAC o SPECL [`log o f:real->real`; `{x | &0 < x}`])
     [REAL_CONVEX_ON_LEFT_SECANT; REAL_CONVEX_ON_RIGHT_SECANT] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(LABEL_TAC "L") THEN DISCH_THEN(LABEL_TAC "R") THEN
    REPEAT STRIP_TAC THENL
     [USE_THEN "L" (MP_TAC o SPECL [`&n - &1`; `&n + x`; `&n`]) THEN
      USE_THEN "R" (MP_TAC o SPECL [`&n - &1`; `&n + x`; `&n`]) THEN
      REWRITE_TAC[IN_ELIM_THM; IN_REAL_SEGMENT; o_THM] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `abs(x - (x - &1)) = &1`; REAL_DIV_1] THEN
      DISCH_TAC THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs((n + x) - n) = x`] THEN
      ASM_REAL_ARITH_TAC;
      ASM_CASES_TAC `x = &1` THEN
      ASM_REWRITE_TAC[REAL_LE_REFL; REAL_DIV_1] THEN
      USE_THEN "R" (MP_TAC o SPECL [`&n`; `&n + &1`; `&n + x`]) THEN
      REWRITE_TAC[IN_ELIM_THM; IN_REAL_SEGMENT; o_THM] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `abs((n + &1) - n) = &1`; REAL_DIV_1] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs((n + x) - n) = x`] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM LOG_DIV; REAL_LT_MUL;
    REAL_ARITH `&2 <= x ==> &0 < x /\ &0 < x + &1 /\ &0 < x - &1`;
    REAL_FIELD `&0 < x ==> (n * x) / x = n`] THEN
  SUBGOAL_THEN
   `!n. &2 <= n ==> f(n - &1) = f(n) / (n - &1)` (fun th -> SIMP_TAC[th])
  THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(f:real->real) n = f((n - &1) + &1)` SUBST1_TAC THENL
     [AP_TERM_TAC THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_ARITH `&2 <= n ==> &0 < n - &1`] THEN
      UNDISCH_TAC `&2 <= n` THEN CONV_TAC REAL_FIELD];
    ASM_SIMP_TAC[REAL_ARITH `&2 <= x ==> &0 < x`; REAL_FIELD
     `&0 < x /\ &2 <= y ==> x / (x / (y - &1)) = y - &1`] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ]] THEN
  SIMP_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_SUB;
           ARITH_RULE `2 <= n ==> 1 <= n`] THEN
  REWRITE_TAC[REAL_LE_SUB_LADD; REAL_LE_SUB_RADD] THEN
  SUBGOAL_THEN
   `!n. 0 < n ==> f(&n) = &(FACT(n - 1))`
   (fun th -> SIMP_TAC[ARITH_RULE `2 <= n ==> 0 < n /\ 0 < n - 1`; th])
  THENL
   [INDUCT_TAC THEN REWRITE_TAC[ARITH; LT_0] THEN
    ASM_CASES_TAC `n = 0` THEN
    ASM_REWRITE_TAC[REAL_ADD_LID; FACT; ARITH] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> SUC n - 1 = SUC(n - 1)`] THEN
    ASM_SIMP_TAC[REAL_OF_NUM_LT; GSYM REAL_OF_NUM_SUC; LE_1; FACT] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> SUC(n - 1) = n`] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; MULT_SYM];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o RAND_CONV o BINOP_CONV)
   [GSYM REAL_EXP_MONO_LE] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
  ASM_SIMP_TAC[REAL_EXP_ADD; EXP_LOG; REAL_OF_NUM_LT; LE_1; FACT_NZ;
               ARITH_RULE `&2 <= &n /\ &0 < x ==> &0 < &n + x`] THEN
  REWRITE_TAC[REAL_OF_NUM_LE] THEN
  SUBGOAL_THEN
   `!n. 0 < n ==> f(&n + x) = product(0..n-1) (\k. x + &k) * f(x)`
   (fun th -> SIMP_TAC[ARITH_RULE `2 <= n ==> 0 < n`; th])
  THENL
   [INDUCT_TAC THEN REWRITE_TAC[ARITH] THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
    ASM_CASES_TAC `n = 0` THENL
     [ASM_SIMP_TAC[REAL_ARITH `(&0 + &1) + x = x + &1`; ARITH] THEN
      REWRITE_TAC[PRODUCT_SING_NUMSEG; REAL_ADD_RID];
      ASM_SIMP_TAC[REAL_ARITH `(n + &1) + x = (n + x) + &1`;
                   REAL_LT_ADD; REAL_OF_NUM_LT; LE_1] THEN
      ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> SUC n - 1 = SUC(n - 1)`] THEN
      REWRITE_TAC[PRODUCT_CLAUSES_NUMSEG; LE_0] THEN
      ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> SUC(n - 1) = n`] THEN
      REWRITE_TAC[REAL_MUL_AC; REAL_ADD_AC]];
    DISCH_TAC] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `&1 <= x /\ x <= &1 + e ==> abs(x - &1) <= e`) THEN
  ASM_SIMP_TAC[REAL_OF_NUM_LE; REAL_FIELD
   `&2 <= n ==> &1 + x * inv n = (x + n) / n`] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; REAL_INV_INV] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `f * (r * n) * p:real = (p * f) * r * n`] THEN
  REWRITE_TAC[GSYM REAL_INV_MUL] THEN REWRITE_TAC[GSYM real_div] THEN
  SUBGOAL_THEN `&0 < &n rpow x * &(FACT n)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; REAL_OF_NUM_LT; LE_1; FACT_NZ;
                 RPOW_POS_LT; ARITH_RULE `2 <= x ==> 0 < x`];
    ALL_TAC]  THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n + 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
    REWRITE_TAC[ADD_SUB] THEN
    ASM_SIMP_TAC[rpow; REAL_OF_NUM_LE; REAL_ARITH `&2 <= x ==> &0 < x`] THEN
    REWRITE_TAC[REAL_MUL_AC];
    ASM_SIMP_TAC[PRODUCT_CLAUSES_RIGHT; LE_0;
                 ARITH_RULE `2 <= n ==> 0 < n`] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC LAND_CONV
     [REAL_ARITH `a * b * c * d:real = b * (a * c) * d`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
    SUBGOAL_THEN `FACT n = FACT(SUC(n - 1))` SUBST1_TAC THENL
     [AP_TERM_TAC THEN ASM_ARITH_TAC; REWRITE_TAC[FACT]] THEN
    ASM_SIMP_TAC[ARITH_RULE `2 <= n ==> SUC(n - 1) = n`] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    SUBGOAL_THEN `&0 < &n` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      SIMP_TAC[rpow; GSYM REAL_OF_NUM_MUL; REAL_MUL_AC] THEN
      CONV_TAC REAL_FIELD]]);;

(* ------------------------------------------------------------------------- *)
(* The integral definition, the current usual one and Euler's original one.  *)
(* ------------------------------------------------------------------------- *)

let EULER_HAS_INTEGRAL_CGAMMA = prove
 (`!z. &0 < Re z
       ==> ((\t.  Cx(drop t) cpow (z - Cx(&1)) / cexp(Cx(drop t)))
            has_integral cgamma(z))
           {t | &0 <= drop t}`,
  let lemma0 = prove
   (`!z a b. &0 < Re z /\ &0 <= drop a
             ==> (\t. Cx(drop t) cpow z) continuous_on interval [a,b]`,
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    X_GEN_TAC `t:real^1` THEN REWRITE_TAC[IN_INTERVAL_1] THEN STRIP_TAC THEN
    ASM_CASES_TAC `t:real^1 = vec 0` THENL
     [ASM_SIMP_TAC[CONTINUOUS_WITHIN; cpow; CX_INJ; GSYM LIFT_EQ; LIFT_NUM;
                   LIFT_DROP] THEN
      ONCE_REWRITE_TAC[LIM_NULL_COMPLEX_NORM] THEN
      REWRITE_TAC[NORM_CEXP] THEN
      MATCH_MP_TAC LIM_TRANSFORM_WITHIN THEN
      EXISTS_TAC `\t. Cx(exp(Re z * log(drop t)))` THEN
      EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
       [X_GEN_TAC `u:real^1` THEN
        REWRITE_TAC[IN_INTERVAL_1; DIST_0; NORM_POS_LT; GSYM DROP_EQ;
                    LIFT_DROP; DROP_VEC] THEN
        STRIP_TAC THEN SUBGOAL_THEN `&0 < drop u`
         (fun th -> SIMP_TAC[GSYM CX_LOG; RE_MUL_CX; th]) THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[LIM_WITHIN; IN_INTERVAL_1; DIST_CX; REAL_SUB_RZERO] THEN
        X_GEN_TAC `e:real` THEN DISCH_TAC THEN
        EXISTS_TAC `e rpow inv(Re z)` THEN
        ASM_SIMP_TAC[RPOW_POS_LT; DIST_0; REAL_ABS_EXP] THEN
        X_GEN_TAC `u:real^1` THEN STRIP_TAC THEN
        SUBGOAL_THEN `e = exp(log e)` SUBST1_TAC THENL
         [ASM_MESON_TAC[EXP_LOG]; REWRITE_TAC[REAL_EXP_MONO_LT]] THEN
        ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
        ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ] THEN
        REWRITE_TAC[REAL_ARITH `x / y:real = inv y * x`] THEN
        ASM_SIMP_TAC[GSYM LOG_RPOW] THEN MATCH_MP_TAC LOG_MONO_LT_IMP THEN
        SUBGOAL_THEN `norm u = drop u` (fun th -> ASM_MESON_TAC[th]) THEN
        REWRITE_TAC[NORM_REAL; GSYM drop] THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN THEN
      SUBGOAL_THEN
       `(\a. Cx(drop a) cpow z) = (\w. w cpow z) o Cx o drop`
      SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC DIFFERENTIABLE_CHAIN_WITHIN THEN CONJ_TAC THENL
       [MATCH_MP_TAC DIFFERENTIABLE_LINEAR THEN
        REWRITE_TAC[linear; o_DEF; DROP_ADD; DROP_CMUL; CX_ADD;
                    COMPLEX_CMUL; GSYM CX_MUL];
        MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_IMP_DIFFERENTIABLE THEN
        COMPLEX_DIFFERENTIABLE_TAC THEN DISCH_THEN(K ALL_TAC) THEN
        REWRITE_TAC[o_DEF; RE_CX] THEN
        ASM_REWRITE_TAC[REAL_LT_LE; GSYM LIFT_EQ; LIFT_NUM; LIFT_DROP] THEN
        ASM_REAL_ARITH_TAC]]) in
  let lemma1 = prove
   (`!n z. &0 < Re z
           ==> ((\t. Cx(drop t) cpow (z - Cx(&1)) * Cx(&1 - drop t) pow n)
                has_integral Cx(&(FACT n)) / cproduct (0..n) (\m. z + Cx(&m)))
                (interval[vec 0,vec 1])`,
    INDUCT_TAC THEN X_GEN_TAC `z:complex` THEN
    ASM_CASES_TAC `z = Cx(&0)` THEN ASM_REWRITE_TAC[RE_CX; REAL_LT_REFL] THEN
    DISCH_TAC THENL
     [REWRITE_TAC[complex_pow; COMPLEX_MUL_RID; CPRODUCT_CLAUSES_NUMSEG] THEN
      MP_TAC(ISPECL
       [`\t. Cx(drop t) cpow z / z`;
        `\t. Cx(drop t) cpow (z - Cx(&1))`;
        `vec 0:real^1`; `vec 1:real^1`]
          FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR) THEN
      REWRITE_TAC[DROP_VEC; CPOW_1; CPOW_0; FACT; complex_div] THEN
      REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_ADD_RID; COMPLEX_SUB_RZERO] THEN
      DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[REAL_POS] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_RMUL THEN
        MATCH_MP_TAC lemma0 THEN ASM_REWRITE_TAC[DROP_VEC; REAL_POS];
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN REPEAT STRIP_TAC THEN
        REWRITE_TAC[CX_SUB] THEN
        MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_REAL_COMPLEX THEN
        COMPLEX_DIFF_TAC THEN ASM_REWRITE_TAC[RE_CX] THEN
        UNDISCH_TAC `~(z = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD];
      FIRST_X_ASSUM(MP_TAC o SPEC `z + Cx(&1)`) THEN
      REWRITE_TAC[RE_ADD; RE_CX; COMPLEX_RING `(z + Cx(&1)) - Cx(&1) = z`] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      MP_TAC(ISPECL
       [`complex_mul`;
        `\t. Cx(drop t) cpow z`;
        `\t. Cx(&1) / Cx(&n + &1) * Cx(&1 - drop t) pow (n + 1)`;
        `\t. z *  Cx(drop t) cpow (z - Cx(&1))`;
        `\t. --(Cx(&1 - drop t) pow n)`;
        `vec 0:real^1`; `vec 1:real^1`;
        `{vec 0:real^1}`;
        `Cx(&(FACT n)) / cproduct (0..n) (\m. (z + Cx(&1)) + Cx(&m))`]
        INTEGRATION_BY_PARTS) THEN
      REWRITE_TAC[BILINEAR_COMPLEX_MUL; DROP_VEC;
                  REAL_POS; COUNTABLE_SING] THEN
      REWRITE_TAC[CPOW_0; REAL_SUB_REFL; COMPLEX_POW_ZERO;
                  ADD_EQ_0; ARITH] THEN
      REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO; COMPLEX_SUB_LZERO] THEN
      REWRITE_TAC[COMPLEX_MUL_RNEG; COMPLEX_RING `--Cx(&0) - y = --y`] THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
          ASM_SIMP_TAC[lemma0; DROP_VEC; REAL_POS] THEN
          MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
          MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_POW THEN
          REWRITE_TAC[CONTINUOUS_ON_CX_LIFT; LIFT_SUB; LIFT_DROP] THEN
          SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
          SIMP_TAC[IN_INTERVAL_1; DROP_VEC; IN_DIFF;
                   IN_SING; GSYM DROP_EQ] THEN
          REPEAT STRIP_TAC THEN REWRITE_TAC[CX_SUB] THEN
          MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_REAL_COMPLEX THEN
          COMPLEX_DIFF_TAC THEN
          ASM_REWRITE_TAC[RE_CX; COMPLEX_MUL_LID] THEN
          REWRITE_TAC[REAL_OF_NUM_ADD; ADD_SUB; COMPLEX_MUL_ASSOC] THEN
          MP_TAC(ARITH_RULE `~(n + 1 = 0)`) THEN
          REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM CX_INJ] THEN
          CONV_TAC COMPLEX_FIELD;
          MATCH_MP_TAC HAS_INTEGRAL_NEG THEN ASM_REWRITE_TAC[]];
        DISCH_THEN(MP_TAC o SPEC `Cx(&n + &1) / z` o
          MATCH_MP HAS_INTEGRAL_COMPLEX_LMUL) THEN
        ASM_SIMP_TAC[REAL_ARITH `~(&n + &1 = &0)`; CX_INJ; COMPLEX_FIELD
          `~(n = Cx(&0)) /\ ~(z = Cx(&0))
           ==> n / z * (z * p) * Cx(&1) / n * q = p * q`] THEN
        REWRITE_TAC[GSYM ADD1] THEN MATCH_MP_TAC EQ_IMP THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN
        SIMP_TAC[FACT; GSYM REAL_OF_NUM_MUL; CX_MUL; GSYM REAL_OF_NUM_SUC] THEN
        REWRITE_TAC[complex_div; GSYM COMPLEX_MUL_ASSOC] THEN AP_TERM_TAC THEN
        SIMP_TAC[CPRODUCT_CLAUSES_LEFT; ARITH_RULE `0 <= SUC n`] THEN
        REWRITE_TAC[ADD1; COMPLEX_INV_MUL; COMPLEX_ADD_RID] THEN
        REWRITE_TAC[ISPECL [`f:num->complex`; `m:num`; `1`]
                    CPRODUCT_OFFSET] THEN
        REWRITE_TAC[GSYM COMPLEX_ADD_ASSOC; GSYM CX_ADD; REAL_OF_NUM_ADD] THEN
        REWRITE_TAC[ARITH_RULE `n + 1 = 1 + n`; COMPLEX_MUL_AC]]]) in
  let lemma2 = prove
   (`!z n. &0 < Re z
           ==> ((\t. if drop t <= &n
                     then Cx(drop t) cpow (z - Cx(&1)) *
                          Cx(&1 - drop t / &n) pow n
                     else Cx(&0))
                has_integral (Cx(&n) cpow z * Cx(&(FACT n))) /
                             cproduct (0..n) (\m. z + Cx(&m)))
               {t | &0 <= drop t}`,
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `n = 0` THENL
     [ASM_REWRITE_TAC[CPOW_0; COMPLEX_MUL_LZERO; complex_div] THEN
      MATCH_MP_TAC HAS_INTEGRAL_SPIKE THEN
      MAP_EVERY EXISTS_TAC [`\t:real^1. Cx(&0)`; `{vec 0:real^1}`] THEN
      REWRITE_TAC[GSYM COMPLEX_VEC_0; HAS_INTEGRAL_0; NEGLIGIBLE_SING] THEN
      REWRITE_TAC[IN_DIFF; IN_SING; GSYM DROP_EQ; DROP_VEC; IN_ELIM_THM] THEN
      REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
      ONCE_REWRITE_TAC[SET_RULE `drop x <= b <=> x IN {x | drop x <= b}`] THEN
      REWRITE_TAC[HAS_INTEGRAL_RESTRICT_INTER] THEN
      FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP lemma1) THEN
      DISCH_THEN(MP_TAC o SPECL [`inv(&n)`; `vec 0:real^1`] o
       MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_AFFINITY)) THEN
      REWRITE_TAC[DIMINDEX_1; REAL_POW_1] THEN
      ASM_SIMP_TAC[REAL_INV_EQ_0; REAL_OF_NUM_EQ; LE_1; REAL_ABS_INV] THEN
      REWRITE_TAC[IMAGE_AFFINITY_INTERVAL; REAL_INV_INV; REAL_POS] THEN
      REWRITE_TAC[UNIT_INTERVAL_NONEMPTY; VECTOR_ADD_RID; REAL_ABS_NUM] THEN
      REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_NEG_0; VECTOR_ADD_RID] THEN
      REWRITE_TAC[DROP_CMUL; COMPLEX_CMUL] THEN
      DISCH_THEN(MP_TAC o SPEC `Cx(&n) cpow (z - Cx(&1))` o
            MATCH_MP HAS_INTEGRAL_COMPLEX_LMUL) THEN
      REWRITE_TAC[COMPLEX_MUL_ASSOC;
                  GSYM(ONCE_REWRITE_RULE[COMPLEX_MUL_SYM] CPOW_SUC)] THEN
      REWRITE_TAC[complex_div; GSYM COMPLEX_MUL_ASSOC; GSYM LIFT_EQ_CMUL] THEN
      REWRITE_TAC[ONCE_REWRITE_RULE[INTER_COMM] INTER; IN_ELIM_THM] THEN
      REWRITE_TAC[GSYM DROP_VEC; LIFT_DROP; GSYM IN_INTERVAL_1] THEN
      REWRITE_TAC[DROP_VEC; SET_RULE `{x | x IN s} = s`] THEN
      REWRITE_TAC[COMPLEX_RING `(z - Cx(&1)) + Cx(&1) = z`] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_EQ) THEN
      REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      REWRITE_TAC[COMPLEX_MUL_ASSOC; REAL_ARITH `inv x * y:real = y / x`] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN IMP_REWRITE_TAC[GSYM CPOW_MUL_REAL] THEN
      ASM_SIMP_TAC[REAL_CX; RE_CX; REAL_LE_DIV; REAL_POS; GSYM CX_MUL] THEN
      ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ; LE_1]]) in
  let lemma3 = prove
   (`f integrable_on s
     ==> (\x:real^N. lift(Re(f x))) integrable_on s /\
         integral s (\x. lift(Re(f x))) = lift(Re(integral s f))`,
    SUBGOAL_THEN `!z. lift(Re z) = (lift o Re) z`
     (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM o_DEF] THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_LINEAR; MATCH_MP_TAC INTEGRAL_LINEAR] THEN
    ASM_REWRITE_TAC[linear; COMPLEX_CMUL; o_THM; RE_ADD; RE_MUL_CX] THEN
    REWRITE_TAC[LIFT_CMUL; LIFT_ADD]) in
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\n t. if drop t <= &n
           then Cx(drop t) cpow (z - Cx(&1)) * Cx(&1 - drop t / &n) pow n
           else Cx(&0)`;
    `\t. Cx(drop t) cpow (z - Cx(&1)) / cexp(Cx(drop t))`;
    `\t. lift(Re(Cx(drop t) cpow (Cx(Re z) - Cx(&1)) / cexp(Cx(drop t))))`;
    `{t | &0 <= drop t}`] DOMINATED_CONVERGENCE) THEN
  ASM_SIMP_TAC[REWRITE_RULE[HAS_INTEGRAL_INTEGRABLE_INTEGRAL] lemma2] THEN
  ANTS_TAC THENL
   [ALL_TAC;
    SIMP_TAC[HAS_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
    MESON_TAC[CGAMMA; LIM_UNIQUE; TRIVIAL_LIMIT_SEQUENTIALLY]] THEN
  REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN REPEAT CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[FORALL_LIFT; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `t:real`] THEN DISCH_TAC THEN
    REWRITE_TAC[cpow; CX_INJ] THEN ASM_CASES_TAC `t = &0` THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COND_ID; RE_CX; CEXP_0; COMPLEX_DIV_1;
                    COMPLEX_NORM_0; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[GSYM CX_LOG; REAL_LT_LE; GSYM CX_EXP; GSYM CX_SUB;
                 GSYM CX_MUL; RE_CX; GSYM CX_DIV; GSYM REAL_EXP_SUB] THEN
    COND_CASES_TAC THEN REWRITE_TAC[COMPLEX_NORM_0; REAL_EXP_POS_LE] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; REAL_EXP_SUB; NORM_CEXP] THEN
    REWRITE_TAC[RE_MUL_CX; RE_SUB; RE_CX; COMPLEX_NORM_POW] THEN
    REWRITE_TAC[real_div] THEN SIMP_TAC[REAL_LE_LMUL_EQ; REAL_EXP_POS_LT] THEN
    REWRITE_TAC[COMPLEX_NORM_CX] THEN
    SUBGOAL_THEN `~(&n = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM real_div; REAL_OF_NUM_EQ] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[real_abs; REAL_SUB_LE; REAL_LE_LDIV_EQ; REAL_MUL_LID;
                 REAL_OF_NUM_LT; LE_1] THEN
    TRANS_TAC REAL_LE_TRANS `exp(--t / &n) pow n` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN
      ASM_SIMP_TAC[REAL_SUB_LE; REAL_LE_LDIV_EQ; REAL_MUL_LID;
                   REAL_OF_NUM_LT; LE_1] THEN
      REWRITE_TAC[REAL_ARITH `&1 - t / n = &1 + --t / n`; REAL_EXP_LE_X];
      REWRITE_TAC[GSYM REAL_EXP_N; GSYM REAL_EXP_NEG] THEN
      ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ; REAL_LE_REFL]];
    REWRITE_TAC[FORALL_LIFT; LIFT_DROP] THEN X_GEN_TAC `t:real` THEN
    DISCH_TAC THEN
    MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC `\k. Cx t cpow (z - Cx(&1)) * Cx(&1 - t / &k) pow k` THEN
    CONJ_TAC THENL
     [MP_TAC(SPEC `t + &1` REAL_ARCH_SIMPLE) THEN
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY; GSYM REAL_OF_NUM_LE] THEN
      MATCH_MP_TAC MONO_EXISTS THEN REAL_ARITH_TAC;
      REWRITE_TAC[complex_div] THEN MATCH_MP_TAC LIM_COMPLEX_LMUL THEN
      REWRITE_TAC[CX_SUB; CX_DIV; GSYM CEXP_NEG] THEN
      REWRITE_TAC[SIMPLE_COMPLEX_ARITH `a - x / y:complex = a + --x / y`] THEN
      REWRITE_TAC[CEXP_LIMIT]]] THEN
  MP_TAC(ISPECL
   [`\n t. lift(Re(if drop t <= &n
                   then Cx(drop t) cpow (Cx(Re z) - Cx(&1)) *
                        Cx(&1 - drop t / &n) pow n
                   else Cx(&0)))`;
    `\t. lift(Re(Cx(drop t) cpow (Cx(Re z) - Cx(&1)) / cexp(Cx(drop t))))`;
    `{t | &0 <= drop t}`]
  MONOTONE_CONVERGENCE_INCREASING) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  ASM_SIMP_TAC[lemma3; REWRITE_RULE[HAS_INTEGRAL_INTEGRABLE_INTEGRAL] lemma2;
   RE_CX; bounded; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_UNIV; FORALL_LIFT; LIFT_DROP; NORM_LIFT] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `t:real`] THEN DISCH_TAC THEN
    ASM_CASES_TAC `t = &0` THEN
    ASM_SIMP_TAC[CPOW_0; COMPLEX_MUL_LZERO; COND_ID; REAL_LE_REFL] THEN
    ASM_REWRITE_TAC[cpow; CX_INJ] THEN
    ASM_SIMP_TAC[cpow; CX_INJ; GSYM CX_SUB; GSYM CX_EXP; GSYM CX_LOG;
                 REAL_LT_LE; GSYM CX_MUL; GSYM CX_DIV; RE_CX; GSYM CX_POW] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN ASM_CASES_TAC `t <= &n` THEN
    ASM_SIMP_TAC[REAL_ARITH `x <= n ==> x <= n + &1`] THENL
     [SIMP_TAC[RE_CX; REAL_LE_LMUL_EQ; REAL_EXP_POS_LT] THEN
      REWRITE_TAC[GSYM RPOW_POW; GSYM REAL_OF_NUM_SUC] THEN
      MATCH_MP_TAC REAL_EXP_LIMIT_RPOW_LE THEN ASM_REAL_ARITH_TAC;
      COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL; RE_CX] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_SUB_LE] THEN
      SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
      ASM_REAL_ARITH_TAC];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN EXISTS_TAC
     `\k. lift(Re(Cx t cpow (Cx(Re z) - Cx(&1)) *
                  Cx(&1 - t / &k) pow k))` THEN
    CONJ_TAC THENL
     [MP_TAC(SPEC `t + &1` REAL_ARCH_SIMPLE) THEN
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY; GSYM REAL_OF_NUM_LE] THEN
      MATCH_MP_TAC MONO_EXISTS THEN REAL_ARITH_TAC;
      REWRITE_TAC[cpow; CX_INJ] THEN
      ASM_CASES_TAC `t = &0` THEN
      ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; complex_div; LIM_CONST] THEN
      ASM_SIMP_TAC[cpow; CX_INJ; GSYM CX_SUB; GSYM CX_EXP; GSYM CX_LOG;
              REAL_LT_LE; GSYM CX_MUL; GSYM CX_INV; RE_CX; GSYM CX_POW] THEN
      REWRITE_TAC[real_div; LIFT_CMUL; RE_CX] THEN MATCH_MP_TAC LIM_CMUL THEN
      REWRITE_TAC[REAL_ARITH `&1 - t * inv x = &1 + --t / x`] THEN
      REWRITE_TAC[GSYM REAL_EXP_NEG] THEN
      REWRITE_TAC[GSYM(REWRITE_RULE[o_DEF] TENDSTO_REAL)] THEN
      REWRITE_TAC[EXP_LIMIT]];
    MP_TAC(MATCH_MP CONVERGENT_IMP_BOUNDED (SPEC `Cx(Re z)` CGAMMA)) THEN
    REWRITE_TAC[bounded; FORALL_IN_IMAGE; IN_UNIV] THEN
    MESON_TAC[COMPLEX_NORM_GE_RE_IM; REAL_LE_TRANS]]);;

let EULER_INTEGRAL = prove
 (`!z. &0 < Re z
       ==> integral {t | &0 <= drop t}
                    (\t.  Cx(drop t) cpow (z - Cx(&1)) / cexp(Cx(drop t))) =
           cgamma(z)`,
  MESON_TAC[INTEGRAL_UNIQUE; EULER_HAS_INTEGRAL_CGAMMA]);;

let EULER_INTEGRABLE = prove
 (`!z. &0 < Re z
       ==> (\t.  Cx(drop t) cpow (z - Cx(&1)) / cexp(Cx(drop t))) integrable_on
           {t | &0 <= drop t}`,
  MESON_TAC[EULER_HAS_INTEGRAL_CGAMMA; integrable_on]);;

let EULER_HAS_REAL_INTEGRAL_GAMMA = prove
 (`!x. &0 < x
       ==> ((\t. t rpow (x - &1) / exp t) has_real_integral gamma(x))
           {t | &0 <= t}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_real_integral] THEN
  MP_TAC(SPEC `Cx x` EULER_HAS_INTEGRAL_CGAMMA) THEN
  ASM_REWRITE_TAC[gamma; o_DEF; RE_CX] THEN
  DISCH_THEN(MP_TAC o ISPEC `lift o Re` o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_LINEAR)) THEN
  REWRITE_TAC[o_DEF] THEN ANTS_TAC THENL
   [REWRITE_TAC[linear; RE_ADD; LIFT_ADD; COMPLEX_CMUL; RE_MUL_CX] THEN
    REWRITE_TAC[LIFT_CMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE lift {t | &0 <= t} = {t | &0 <= drop t}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
    REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN MESON_TAC[LIFT_DROP];
    ALL_TAC] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ] (REWRITE_RULE[CONJ_ASSOC]
        HAS_INTEGRAL_SPIKE)) THEN
  EXISTS_TAC `{vec 0:real^1}` THEN
  REWRITE_TAC[NEGLIGIBLE_SING; FORALL_LIFT; IN_DIFF; IN_ELIM_THM;
              LIFT_DROP; IN_SING; GSYM DROP_EQ; DROP_VEC] THEN
  SIMP_TAC[cpow; CX_INJ; rpow; REAL_LT_LE; GSYM CX_LOG; GSYM CX_SUB;
           GSYM CX_EXP; GSYM CX_MUL; RE_CX; GSYM CX_DIV]);;

let EULER_REAL_INTEGRAL = prove
 (`!x. &0 < x
       ==> real_integral {t | &0 <= t} (\t. t rpow (x - &1) / exp t) =
           gamma(x)`,
  MESON_TAC[REAL_INTEGRAL_UNIQUE; EULER_HAS_REAL_INTEGRAL_GAMMA]);;

let EULER_REAL_INTEGRABLE = prove
 (`!x. &0 < x
       ==> (\t. t rpow (x - &1) / exp t) real_integrable_on {t | &0 <= t}`,
  MESON_TAC[EULER_HAS_REAL_INTEGRAL_GAMMA; real_integrable_on]);;

let EULER_ORIGINAL_REAL_INTEGRABLE = prove
 (`!x. &0 < x
       ==> (\t. (--log t) rpow (x - &1))
                real_integrable_on real_interval[&0,&1]`,
  SUBGOAL_THEN
   `!x. &0 < x
        ==> ((\t. (--log t) rpow (x - &1))
             real_integrable_on real_interval[&0,&1] <=>
             (\t. (--log t) rpow x)
             real_integrable_on real_interval[&0,&1])`
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_CASES_TAC `x = &0` THEN
    ASM_REWRITE_TAC[REAL_LT_REFL] THEN DISCH_TAC THEN MP_TAC(ISPECL
     [`\t. inv(x) * (--log t) rpow x`;
      `\t:real. t`;
      `\t. --(&1) / t * (--log t) rpow (x - &1)`;
      `\t:real. &1`; `&0`; `&1`; `{&0,&1}`]
        REAL_INTEGRABLE_BY_PARTS_EQ) THEN
    REWRITE_TAC[COUNTABLE_INSERT; COUNTABLE_EMPTY; REAL_MUL_RID] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
        REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
        X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
        STRIP_TAC THEN
        FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (REAL_ARITH
         `&0 <= x ==> &0 < x \/ x = &0`))
        THENL
         [MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN
          REWRITE_TAC[REAL_CONTINUOUS_WITHIN_ID] THEN
          MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
          SUBGOAL_THEN
           `(\y. --log(y) rpow x) = (\y. y rpow x) o (\x. --x) o log`
          SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
          REPEAT(MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_COMPOSE THEN
                 CONJ_TAC) THEN
          ASM_SIMP_TAC[REAL_CONTINUOUS_NEG; REAL_CONTINUOUS_AT_ID;
                       REAL_CONTINUOUS_AT_LOG] THEN
          MATCH_MP_TAC REAL_CONTINUOUS_AT_RPOW THEN
          ASM_SIMP_TAC[REAL_LE_LT];
          FIRST_X_ASSUM SUBST_ALL_TAC THEN
          REWRITE_TAC[REAL_CONTINUOUS_WITHINREAL; REAL_MUL_RZERO] THEN
          MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
          EXISTS_TAC `\y. (--x * log(y rpow inv x) * y rpow inv x) rpow x` THEN
          CONJ_TAC THENL
           [REWRITE_TAC[EVENTUALLY_WITHINREAL] THEN
            REWRITE_TAC[REAL_ARITH `&0 < abs(x - a) <=> ~(x = a)`] THEN
            EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
            X_GEN_TAC `y:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
            STRIP_TAC THEN
            SUBGOAL_THEN `&0 < y` ASSUME_TAC THENL
             [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
            ASM_SIMP_TAC[LOG_RPOW; REAL_LT_INV_EQ; REAL_FIELD
              `~(x = &0) ==> --x * (inv x * y) * z = --y * z`] THEN
            ASM_SIMP_TAC[RPOW_MUL; RPOW_RPOW; REAL_MUL_LINV] THEN
            REWRITE_TAC[RPOW_POW; REAL_POW_1];
            SUBGOAL_THEN `&0 = &0 rpow x`
             (fun th -> GEN_REWRITE_TAC LAND_CONV [th])
            THENL [ASM_SIMP_TAC[rpow; REAL_LT_IMP_NZ; REAL_LT_REFL];
                   ALL_TAC] THEN
            MATCH_MP_TAC(REWRITE_RULE[] (ISPEC `\y. y rpow x`
                REALLIM_REAL_CONTINUOUS_FUNCTION)) THEN
            ASM_SIMP_TAC[REAL_CONTINUOUS_AT_RPOW; REAL_LT_IMP_LE] THEN
            MATCH_MP_TAC REALLIM_NULL_LMUL THEN
            SUBGOAL_THEN
             `(\y. log (y rpow inv x) * y rpow inv x) =
              (\y. log y * y) o (\y. y rpow inv x)`
            SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
            MATCH_MP_TAC REALLIM_COMPOSE_WITHIN THEN
            EXISTS_TAC `{x | &0 <= x}` THEN EXISTS_TAC `&0 rpow inv x` THEN
            ASM_REWRITE_TAC[REAL_ENTIRE; RPOW_EQ_0; REAL_INV_EQ_0] THEN
            REPEAT CONJ_TAC THENL
             [MATCH_MP_TAC(REWRITE_RULE[] (ISPEC `\y. y rpow x`
                REALLIM_REAL_CONTINUOUS_FUNCTION)) THEN
              ASM_SIMP_TAC[REAL_CONTINUOUS_AT_RPOW; REAL_LT_IMP_LE;
                           REAL_LE_INV_EQ] THEN
              MP_TAC(ISPEC `&0` REAL_CONTINUOUS_AT_ID) THEN
              SIMP_TAC[REAL_CONTINUOUS_ATREAL; REALLIM_ATREAL_WITHINREAL];
              REWRITE_TAC[EVENTUALLY_WITHINREAL] THEN
              SIMP_TAC[RPOW_POS_LE; IN_REAL_INTERVAL; IN_ELIM_THM] THEN
              MESON_TAC[REAL_LT_01];
              ASM_REWRITE_TAC[RPOW_ZERO; REAL_INV_EQ_0] THEN
              ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
              REWRITE_TAC[REALLIM_X_TIMES_LOG]]]];
        REWRITE_TAC[IN_REAL_INTERVAL; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
        X_GEN_TAC `t:real` THEN REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
        CONJ_TAC THEN REAL_DIFF_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[GSYM LOG_INV; REAL_INV_1_LT; LOG_POS_LT] THEN
        REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD];
      ASM_REWRITE_TAC[REAL_INTEGRABLE_LMUL_EQ; REAL_INV_EQ_0] THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
      REWRITE_TAC[REAL_INTEGRABLE_LMUL_EQ] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC REAL_INTEGRABLE_SPIKE_EQ THEN EXISTS_TAC `{&0}` THEN
      REWRITE_TAC[REAL_NEGLIGIBLE_SING; IN_DIFF; IN_SING] THEN
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (\t. --log t pow n) real_integrable_on real_interval[&0,&1]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC num_INDUCTION THEN
    REWRITE_TAC[CONJUNCT1 real_pow; REAL_INTEGRABLE_CONST] THEN
    REWRITE_TAC[GSYM RPOW_POW] THEN X_GEN_TAC `n:num` THEN
    SUBGOAL_THEN `&n = &(SUC n) - &1` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC EQ_IMP THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[REAL_OF_NUM_LT; LT_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. &0 < x
        ==> (\t. --log t rpow x) real_integrable_on real_interval[&0,&1]`
   (fun th -> ASM_MESON_TAC[th]) THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `x:real` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_AE_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\t. max (&1) (--log t pow n)` THEN EXISTS_TAC `{&0}` THEN
  REWRITE_TAC[REAL_NEGLIGIBLE_SING] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_MEASURABLE_ON_RPOW THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_IMP_REAL_MEASURABLE THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `1`) THEN REWRITE_TAC[REAL_POW_1];
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_MAX THEN
    REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN MATCH_MP_TAC
      ABSOLUTELY_REAL_INTEGRABLE_ABSOLUTELY_REAL_INTEGRABLE_LBOUND THEN
    EXISTS_TAC `\x:real. min (--log(&0) pow n) (&0)` THEN
    ASM_REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `t:real` THEN
    STRIP_TAC THEN ASM_CASES_TAC `t = &0` THEN ASM_REWRITE_TAC[] THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> min a b <= c`) THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_SIMP_TAC[GSYM LOG_INV] THEN
    MATCH_MP_TAC LOG_POS THEN MATCH_MP_TAC REAL_INV_1_LE THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_REAL_INTERVAL; IN_DIFF; IN_SING] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= --log t` ASSUME_TAC THENL
     [ASM_SIMP_TAC[GSYM LOG_INV] THEN MATCH_MP_TAC LOG_POS THEN
      MATCH_MP_TAC REAL_INV_1_LE THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[real_abs; RPOW_POS_LE]] THEN
    ASM_CASES_TAC `--(log t) <= &1` THENL
     [MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= max y z`) THEN
      MATCH_MP_TAC RPOW_1_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x <= z ==> x <= max y z`) THEN
      REWRITE_TAC[GSYM RPOW_POW] THEN MATCH_MP_TAC RPOW_MONO THEN
      ASM_REAL_ARITH_TAC]]);;

let EULER_ORIGINAL_INTEGRABLE = prove
 (`!z. &0 < Re z
       ==> (\t. (--clog(Cx(drop t))) cpow (z - Cx(&1)))
           integrable_on interval[vec 0,vec 1]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_AE_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\t. lift((--log(drop t)) rpow (Re z - &1))` THEN
  EXISTS_TAC `{vec 0:real^1,vec 1}` THEN
  REWRITE_TAC[NEGLIGIBLE_INSERT; NEGLIGIBLE_EMPTY] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC
     CONTINUOUS_AE_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `{vec 0:real^1,vec 1}` THEN
    REWRITE_TAC[NEGLIGIBLE_INSERT; NEGLIGIBLE_EMPTY;
                LEBESGUE_MEASURABLE_INTERVAL] THEN
    SUBGOAL_THEN
     `(\t. --clog (Cx(drop t)) cpow (z - Cx(&1))) =
      ((\w. w cpow (z - Cx(&1))) o (--) o clog) o (\x. Cx(drop x))`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_CX_DROP; CONTINUOUS_ON_ID] THEN
    MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM;
                IMP_CONJ; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP; DROP_VEC; o_DEF] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    COMPLEX_DIFFERENTIABLE_TAC THEN
    ASM_SIMP_TAC[GSYM CX_LOG; RE_CX; REAL_LT_LE; RE_NEG; GSYM LOG_INV] THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM REAL_LT_LE] THEN
    MATCH_MP_TAC LOG_POS_LT THEN MATCH_MP_TAC REAL_INV_1_LT THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[INTERVAL_REAL_INTERVAL; DROP_VEC;
                REWRITE_RULE[o_DEF] (GSYM REAL_INTEGRABLE_ON)] THEN
    MATCH_MP_TAC EULER_ORIGINAL_REAL_INTEGRABLE THEN ASM_REWRITE_TAC[];

    REWRITE_TAC[FORALL_LIFT; IN_DIFF; IN_INSERT; GSYM DROP_EQ; LIFT_DROP;
                IN_INTERVAL_1; DROP_VEC; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < x /\ x < &1` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM CX_LOG; cpow; rpow; GSYM CX_NEG; REAL_LT_IMP_NZ; RE_CX;
          REAL_LT_IMP_LE; COMPLEX_NORM_MUL; NORM_CEXP; RE_SUB; CX_INJ;
          REAL_LE_REFL; RE_MUL_CX; GSYM LOG_INV; LOG_POS_LT; REAL_INV_1_LT]]);;

let EULER_ORIGINAL_HAS_INTEGRAL_CGAMMA = prove
 (`!z. &0 < Re z
       ==> ((\t. (--clog(Cx(drop t))) cpow (z - Cx(&1)))
            has_integral cgamma(z)) (interval[vec 0,vec 1])`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP EULER_ORIGINAL_INTEGRABLE) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP INDEFINITE_INTEGRAL_CONTINUOUS_LEFT) THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0:real^1`) THEN
  REWRITE_TAC[ENDS_IN_UNIT_INTERVAL; CONTINUOUS_WITHIN] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[HAS_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE
   [TAUT `a /\ b /\ c ==> d <=> b ==> a /\ c ==> d`] LIM_UNIQUE)) THEN
  REWRITE_TAC[TRIVIAL_LIMIT_WITHIN] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_IMP_PERFECT THEN
    REWRITE_TAC[ENDS_IN_UNIT_INTERVAL; CONNECTED_INTERVAL] THEN
    MATCH_MP_TAC(SET_RULE
     `{a,b} SUBSET interval[a,b] /\ ~(a = b)
      ==> ~(?x. interval[a,b] = {x})`) THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; ENDS_IN_UNIT_INTERVAL] THEN
    REWRITE_TAC[VEC_EQ; ARITH_EQ];
    ALL_TAC] THEN
  MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\x. integral(interval[vec 0,lift(--log(drop x))])
          (\t. Cx(drop t) cpow (z - Cx(&1)) / cexp(Cx(drop t)))` THEN
  REWRITE_TAC[EVENTUALLY_WITHIN] THEN CONJ_TAC THENL
   [EXISTS_TAC `&1` THEN
    REWRITE_TAC[REAL_LT_01; DIST_0; NORM_POS_LT; IN_INTERVAL_1; DROP_VEC;
                GSYM DROP_EQ; DROP_VEC; FORALL_LIFT; LIFT_DROP] THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\t. (--clog(Cx(drop(--t)))) cpow (z - Cx(&1))`;
      `\t. --lift(exp(--drop t))`;
      `\t. lift(exp(--drop t))`;
      `vec 0:real^1`; `lift(--log x):real^1`; `--vec 1:real^1`; `vec 0:real^1`;
      `{vec 0:real^1,vec 1}`]
          HAS_INTEGRAL_SUBSTITUTION_STRONG) THEN
    REWRITE_TAC[LIFT_DROP; DROP_VEC; GSYM DROP_NEG] THEN
    REWRITE_TAC[GSYM REFLECT_INTERVAL; GSYM INTEGRAL_REFLECT_GEN] THEN
    REWRITE_TAC[DROP_NEG; LIFT_DROP; REAL_LE_NEG2; REAL_EXP_MONO_LE] THEN
    REWRITE_TAC[REAL_NEG_NEG; DROP_VEC; REAL_EXP_0; REAL_NEG_0] THEN
    SIMP_TAC[GSYM CX_LOG; REAL_EXP_POS_LT; LOG_EXP] THEN ANTS_TAC THENL
     [REWRITE_TAC[REAL_POS; COUNTABLE_INSERT; COUNTABLE_EMPTY] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_SIMP_TAC[GSYM LOG_INV; LOG_POS; REAL_INV_1_LE] THEN
      REWRITE_TAC[GSYM DROP_NEG; INTEGRABLE_REFLECT_GEN] THEN
      REWRITE_TAC[REFLECT_INTERVAL; VECTOR_NEG_NEG; VECTOR_NEG_0] THEN
      ASM_SIMP_TAC[EULER_ORIGINAL_INTEGRABLE] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[GSYM LIFT_NEG; DROP_NEG] THEN
        REWRITE_TAC[GSYM LIFT_NUM; GSYM IMAGE_LIFT_REAL_INTERVAL] THEN
        REWRITE_TAC[REWRITE_RULE[o_DEF] (GSYM REAL_CONTINUOUS_ON)] THEN
        MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
        REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
        REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC;
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; DROP_VEC;
                    FORALL_LIFT; LIFT_DROP; DROP_NEG] THEN
        X_GEN_TAC `y:real` THEN STRIP_TAC THEN
        REWRITE_TAC[REAL_ARITH `--x <= &0 <=> &0 <= x`; REAL_EXP_POS_LE] THEN
        REWRITE_TAC[REAL_EXP_NEG; REAL_LE_NEG2] THEN
        MATCH_MP_TAC REAL_INV_LE_1 THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN
        ASM_REWRITE_TAC[REAL_EXP_MONO_LE];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; DROP_VEC;
                    FORALL_LIFT; LIFT_DROP; DROP_NEG; IN_DIFF; IN_INSERT;
                    NOT_IN_EMPTY; GSYM DROP_EQ; DE_MORGAN_THM] THEN
        X_GEN_TAC `y:real` THEN REPEAT STRIP_TAC THENL
         [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
          REWRITE_TAC[GSYM LIFT_NEG; REWRITE_RULE[o_DEF]
           (GSYM HAS_REAL_VECTOR_DERIVATIVE_AT)] THEN
          REAL_DIFF_TAC THEN REAL_ARITH_TAC;
          MATCH_MP_TAC CONTINUOUS_AT_WITHIN THEN
          SUBGOAL_THEN
           `(\t. --clog(Cx(--drop t)) cpow (z - Cx(&1))) =
            (\w. --clog w cpow (z - Cx(&1))) o (\t. Cx(drop(--t)))`
          SUBST1_TAC THENL [REWRITE_TAC[o_DEF; DROP_NEG]; ALL_TAC] THEN
          MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN CONJ_TAC THENL
           [MATCH_MP_TAC CONTINUOUS_CX_DROP THEN
            GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
            SIMP_TAC[CONTINUOUS_NEG; CONTINUOUS_AT_ID];
            MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
            COMPLEX_DIFFERENTIABLE_TAC THEN
            REWRITE_TAC[RE_CX; VECTOR_NEG_NEG; LIFT_DROP] THEN
            SIMP_TAC[REAL_EXP_POS_LT; GSYM CX_LOG; LOG_EXP] THEN
            REWRITE_TAC[RE_NEG; RE_CX; REAL_NEG_NEG] THEN
            ASM_REAL_ARITH_TAC]]];
      DISCH_THEN(MP_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
      ASM_SIMP_TAC[EXP_LOG; LIFT_NUM; COMPLEX_CMUL; CX_EXP; CEXP_NEG; CX_NEG;
                   COMPLEX_NEG_NEG] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN REWRITE_TAC[complex_div]];
   FIRST_ASSUM(MP_TAC o MATCH_MP EULER_HAS_INTEGRAL_CGAMMA) THEN
   GEN_REWRITE_TAC LAND_CONV [HAS_INTEGRAL_ALT] THEN
   REWRITE_TAC[INTEGRABLE_RESTRICT_INTER; INTEGRAL_RESTRICT_INTER] THEN
   DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN REWRITE_TAC[LIM_WITHIN] THEN
   X_GEN_TAC `e:real` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `exp(--B)` THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT] THEN
   REWRITE_TAC[REAL_LT_01; DIST_0; NORM_POS_LT; IN_INTERVAL_1; DROP_VEC;
               GSYM DROP_EQ; DROP_VEC; FORALL_LIFT; LIFT_DROP; NORM_LIFT] THEN
   X_GEN_TAC `x:real` THEN STRIP_TAC THEN
   SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`--lift B`; `lift(--log x)`]) THEN
   ANTS_TAC THENL
    [REWRITE_TAC[BALL_1; SUBSET_INTERVAL_1; DROP_ADD; DROP_SUB; DROP_VEC] THEN
     REWRITE_TAC[LIFT_DROP; DROP_NEG] THEN DISJ2_TAC THEN
     REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
     REWRITE_TAC[REAL_ADD_LID] THEN
     ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN
     ASM_SIMP_TAC[REAL_EXP_NEG; EXP_LOG] THEN
     GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN
     ONCE_REWRITE_TAC[GSYM REAL_EXP_NEG] THEN
     MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
     MATCH_MP_TAC(NORM_ARITH
      `i = j ==> norm(i - g) < e ==> dist(j,g) < e`) THEN
     AP_THM_TAC THEN AP_TERM_TAC THEN
     REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_INTERVAL_1] THEN
     REWRITE_TAC[DROP_NEG; LIFT_DROP; DROP_VEC] THEN ASM_REAL_ARITH_TAC]]);;

let EULER_ORIGINAL_INTEGRAL = prove
 (`!z. &0 < Re z
       ==> integral (interval[vec 0,vec 1])
                    (\t. (--clog(Cx(drop t))) cpow (z - Cx(&1))) =
           cgamma(z)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC EULER_ORIGINAL_HAS_INTEGRAL_CGAMMA THEN
  ASM_REWRITE_TAC[]);;

let EULER_ORIGINAL_HAS_REAL_INTEGRAL_GAMMA = prove
 (`!x. &0 < x
       ==> ((\t. (--log t) rpow (x - &1)) has_real_integral gamma(x))
           (real_interval[&0,&1])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_real_integral] THEN
  MP_TAC(SPEC `Cx x` EULER_ORIGINAL_HAS_INTEGRAL_CGAMMA) THEN
  ASM_REWRITE_TAC[gamma; o_DEF; RE_CX] THEN
  DISCH_THEN(MP_TAC o ISPEC `lift o Re` o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_LINEAR)) THEN
  REWRITE_TAC[o_DEF] THEN ANTS_TAC THENL
   [REWRITE_TAC[linear; RE_ADD; LIFT_ADD; COMPLEX_CMUL; RE_MUL_CX] THEN
    REWRITE_TAC[LIFT_CMUL];
    REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL; LIFT_NUM]] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ] (REWRITE_RULE[CONJ_ASSOC]
        HAS_INTEGRAL_SPIKE)) THEN
  EXISTS_TAC `{vec 0:real^1,vec 1}` THEN
  REWRITE_TAC[NEGLIGIBLE_INSERT; FORALL_LIFT; IN_INTERVAL_1; DE_MORGAN_THM;
    LIFT_DROP; IN_INSERT; NOT_IN_EMPTY; GSYM DROP_EQ; DROP_VEC; IN_DIFF] THEN
  REWRITE_TAC[NEGLIGIBLE_EMPTY] THEN X_GEN_TAC `y:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < y` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < --log y` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM LOG_INV] THEN MATCH_MP_TAC LOG_POS_LT THEN
    MATCH_MP_TAC REAL_INV_1_LT THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[GSYM CX_LOG; cpow; rpow; COMPLEX_NEG_EQ_0; CX_INJ;
                 REAL_LT_IMP_NZ] THEN
    ASM_SIMP_TAC[GSYM CX_NEG; GSYM CX_LOG; GSYM CX_SUB; GSYM CX_MUL] THEN
    COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM CX_EXP; RE_CX]]);;

let EULER_ORIGINAL_REAL_INTEGRAL = prove
 (`!x. &0 < x
       ==> real_integral (real_interval[&0,&1])
                         (\t. (--log t) rpow (x - &1)) =
           gamma(x)`,
  MESON_TAC[REAL_INTEGRAL_UNIQUE; EULER_ORIGINAL_HAS_REAL_INTEGRAL_GAMMA]);;

(* ------------------------------------------------------------------------- *)
(* Stirling's approximation.                                                 *)
(* ------------------------------------------------------------------------- *)

let LGAMMA_STIRLING_INTEGRALS_EXIST,LGAMMA_STIRLING = (CONJ_PAIR o prove)
 (`(!z n. 1 <= n /\ (Im z = &0 ==> &0 < Re z)
          ==> (\t. Cx(bernoulli n (frac (drop t))) / (z + Cx(drop t)) pow n)
              integrable_on {t | &0 <= drop t}) /\
   (!z p.
      (Im z = &0 ==> &0 < Re z)
      ==> lgamma(z) =
          ((z - Cx(&1) / Cx(&2)) * clog(z) - z + Cx(log(&2 * pi) / &2)) +
          vsum(1..p) (\k. Cx(bernoulli (2 * k) (&0) /
                             (&4 * &k pow 2 - &2 * &k)) / z pow (2 * k - 1)) -
          integral {t | &0 <= drop t}
                   (\t. Cx(bernoulli (2 * p + 1) (frac(drop t))) /
                        (z + Cx(drop t)) pow (2 * p + 1)) /
          Cx(&(2 * p + 1)))`,
  let lemma1 = prove
   (`!p n z. (Im z = &0 ==> &0 < Re z)
             ==> (\x. Cx(bernoulli (2 * p + 1) (frac(drop x))) *
                   Cx(&(FACT(2 * p))) / (z + Cx(drop x)) pow (2 * p + 1))
                 integrable_on interval [lift(&0),lift(&n)] /\
                 vsum(0..n) (\m. clog(Cx(&m) + z)) =
                 (z + Cx(&n) + Cx(&1) / Cx(&2)) * clog(z + Cx(&n)) -
                 (z - Cx(&1) / Cx(&2)) * clog(z) - Cx(&n) +
                 vsum(1..p)
                  (\k. Cx(bernoulli (2 * k) (&0) / &(FACT(2 * k))) *
                       (Cx(&(FACT(2 * k - 2))) / (z + Cx(&n)) pow (2 * k - 1) -
                        Cx(&(FACT(2 * k - 2))) / z pow (2 * k - 1))) +
                 integral (interval[lift(&0),lift(&n)])
                   (\x. Cx(bernoulli (2 * p + 1) (frac(drop x))) *
                        Cx(&(FACT(2 * p))) / (z + Cx(drop x)) pow (2 * p + 1)) /
                 Cx(&(FACT(2 * p + 1)))`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[COMPLEX_RING `Cx(&n) + z = z + Cx(&n)`] THEN MP_TAC(ISPECL
     [`\n w. if n = 0 then (z + w) * clog(z + w) - (z + w)
             else if n = 1 then clog(z + w)
             else Cx(--(&1) pow n * &(FACT(n - 2))) /
                  (z + w) pow (n - 1)`;
      `0`; `n:num`; `p:num`] COMPLEX_EULER_MACLAURIN_ANTIDERIVATIVE) THEN
    ASM_REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; MULT_EQ_1] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ANTS_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL; LE_0] THEN
      MAP_EVERY X_GEN_TAC [`k:num`; `x:real`] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `~(z + Cx x = Cx(&0))` ASSUME_TAC THENL
       [REWRITE_TAC[COMPLEX_EQ; IM_ADD; RE_ADD; IM_CX; RE_CX] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[o_THM; ARITH_RULE `k + 1 = 1 <=> k = 0`] THEN
      ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[] THENL
       [COMPLEX_DIFF_TAC THEN CONJ_TAC THENL
         [REWRITE_TAC[RE_ADD; IM_ADD; RE_CX; IM_CX] THEN ASM_REAL_ARITH_TAC;
          UNDISCH_TAC `~(z + Cx x = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD];
        ALL_TAC] THEN
      ASM_CASES_TAC `k = 1` THEN ASM_REWRITE_TAC[] THEN COMPLEX_DIFF_TAC THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[complex_div; COMPLEX_ADD_LID; COMPLEX_MUL_LID;
                  COMPLEX_POW_1; IM_ADD; RE_ADD; IM_CX; RE_CX] THEN
      (CONJ_TAC ORELSE ASM_REAL_ARITH_TAC) THEN
      ASM_REWRITE_TAC[COMPLEX_POW_EQ_0] THEN
      REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; COMPLEX_MUL_LZERO] THEN
      REWRITE_TAC[REAL_MUL_RNEG; REAL_MUL_RID; REAL_NEG_NEG; REAL_MUL_LNEG] THEN
      REWRITE_TAC[COMPLEX_MUL_RID; CX_NEG; COMPLEX_POW_POW] THEN
      REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC; COMPLEX_SUB_LZERO; COMPLEX_NEG_NEG;
                  COMPLEX_MUL_LNEG] THEN
      REWRITE_TAC[GSYM complex_div] THEN AP_TERM_TAC THEN
      FIRST_X_ASSUM(K ALL_TAC o check (is_imp o concl)) THEN
      ASM_SIMP_TAC[GSYM complex_div; COMPLEX_DIV_POW2] THEN COND_CASES_TAC THENL
       [MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[ADD_SUB; ARITH_RULE
       `~(k = 0) /\ ~(k = 1) ==> (k - 1) * 2 - (k - 1 - 1) = k`] THEN
      REWRITE_TAC[COMPLEX_MUL_ASSOC; complex_div] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM CX_MUL] THEN
      AP_TERM_TAC THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> (k + 1) - 2 = k - 1`] THEN
      ASM_SIMP_TAC[ARITH_RULE
       `~(k = 0) /\ ~(k = 1) ==> k - 1 = SUC(k - 2)`] THEN
      REWRITE_TAC[FACT; REAL_OF_NUM_MUL] THEN REWRITE_TAC[MULT_SYM];
      REWRITE_TAC[ARITH_RULE `~(2 * p + 2 = 1)`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC SUBST1_TAC)] THEN
    SIMP_TAC[LE_1] THEN
    REWRITE_TAC[ARITH_RULE `(2 * p + 2) - 1 = 2 * p + 1`; ADD_SUB] THEN
    REWRITE_TAC[REAL_POW_NEG; EVEN_ADD; EVEN_MULT; ARITH_EVEN] THEN
    REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[COMPLEX_ADD_RID] THEN
    CONV_TAC COMPLEX_RING) in
  let lemma2 = prove
   (`!z n. 2 <= n /\ (Im z = &0 ==> &0 < Re z)
           ==> (\t. inv(z + Cx(drop t)) pow n)
               absolutely_integrable_on {t | &0 <= drop t}`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[COMPLEX_POW_INV] THEN
    MATCH_MP_TAC
      MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
    EXISTS_TAC `\t. lift(inv(max (abs(Im z)) (Re z + drop t)) pow n)` THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_INV THEN
        SIMP_TAC[CONTINUOUS_ON_COMPLEX_POW; CONTINUOUS_ON_ADD;
          CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID; CONTINUOUS_ON_CX_DROP] THEN
        REWRITE_TAC[IN_ELIM_THM; GSYM FORALL_DROP] THEN
        REWRITE_TAC[COMPLEX_POW_EQ_0] THEN
        REWRITE_TAC[COMPLEX_EQ; RE_ADD; IM_ADD; RE_CX; IM_CX] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC LEBESGUE_MEASURABLE_CONVEX THEN
        MATCH_MP_TAC IS_INTERVAL_CONVEX THEN
        REWRITE_TAC[IS_INTERVAL_1; IN_ELIM_THM] THEN REAL_ARITH_TAC];
      ALL_TAC;
      REWRITE_TAC[FORALL_IN_GSPEC; GSYM FORALL_DROP; LIFT_DROP] THEN
      X_GEN_TAC `x:real` THEN DISCH_TAC THEN
     REWRITE_TAC[GSYM COMPLEX_POW_INV; COMPLEX_NORM_POW] THEN
     MATCH_MP_TAC REAL_POW_LE2 THEN
     REWRITE_TAC[NORM_POS_LE; COMPLEX_NORM_INV] THEN
     MATCH_MP_TAC REAL_LE_INV2 THEN
     MP_TAC(SPEC `z + Cx x` COMPLEX_NORM_GE_RE_IM) THEN
     REWRITE_TAC[RE_ADD; IM_ADD; RE_CX; IM_CX] THEN ASM_REAL_ARITH_TAC] THEN
    REWRITE_TAC[REAL_ARITH `max m n = if n <= m then m else n`] THEN
    REWRITE_TAC[COND_RAND; COND_RATOR] THEN
    MATCH_MP_TAC INTEGRABLE_CASES THEN REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `{t | &0 <= drop t /\ Re z + drop t <= abs (Im z)} =
        interval[vec 0,lift(abs(Im z) - Re z)]`
       (fun th -> REWRITE_TAC[th; INTEGRABLE_CONST]) THEN
      SIMP_TAC[EXTENSION; IN_ELIM_THM; IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE_SET) THEN
    EXISTS_TAC
     `{t | abs(Im z) - Re z <= drop t} INTER {t | &0 <= drop t}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
      EXISTS_TAC `{lift(abs(Im z) - Re z)}` THEN
      REWRITE_TAC[NEGLIGIBLE_SING] THEN
      REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION;
                  IN_ELIM_THM; IN_SING; IN_INTER] THEN
      REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM INTEGRABLE_RESTRICT_INTER] THEN
    REWRITE_TAC[integrable_on] THEN
    ONCE_REWRITE_TAC[HAS_INTEGRAL_LIM_AT_POSINFINITY] THEN
    REWRITE_TAC[INTEGRABLE_RESTRICT_INTER; INTEGRAL_RESTRICT_INTER] THEN
    SUBGOAL_THEN
     `!a. {t | abs(Im z) - Re z <= drop t} INTER interval[vec 0,a] =
          interval[lift(max (&0) (abs (Im z) - Re z)),a]`
     (fun th -> REWRITE_TAC[th])
    THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_INTERVAL_1] THEN
      REWRITE_TAC[LIFT_DROP; DROP_VEC] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!b. &0 <= drop b /\ abs (Im z) - Re z <= drop b
           ==> ((\x. lift(inv (Re z + drop x) pow n)) has_integral
                lift
                (inv((&1 - &n) * (Re z + drop b) pow (n - 1)) -
                 inv((&1 - &n) *
                     (Re z + max(&0) (abs(Im z) - Re z)) pow (n - 1))))
               (interval[lift(max (&0) (abs (Im z) - Re z)),b])`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL
       [`\x. lift(inv((&1 - &n) * (Re z + drop x) pow (n - 1)))`;
        `\x. lift(inv(Re z + drop x) pow n)`;
        `lift(max (&0) (abs (Im z) - Re z))`;
        `b:real^1`] FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
      ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; REAL_MAX_LE] THEN
      ANTS_TAC THENL
       [REWRITE_TAC[FORALL_LIFT; LIFT_DROP; INTERVAL_REAL_INTERVAL] THEN
        REWRITE_TAC[REWRITE_RULE[o_DEF]
         (GSYM HAS_REAL_VECTOR_DERIVATIVE_WITHIN)] THEN
        REWRITE_TAC[REAL_INV_MUL; REAL_INV_POW] THEN REPEAT STRIP_TAC THEN
        REAL_DIFF_TAC THEN
        ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE `2 <= n ==> 1 <= n`] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[real_div; REAL_OF_NUM_LE; REAL_FIELD
         `&2 <= x ==> inv(&1 - x) * (x - &1) * y * --(&0 + &1) * p =
                     y * p`] THEN
        REWRITE_TAC[GSYM REAL_INV_MUL; GSYM REAL_INV_POW] THEN
        AP_TERM_TAC THEN REWRITE_TAC[GSYM REAL_POW_ADD] THEN
        AP_TERM_TAC THEN ASM_ARITH_TAC;
        REWRITE_TAC[LIFT_DROP; GSYM LIFT_SUB]];
      ALL_TAC] THEN
    EXISTS_TAC `lift(inv
                  ((&n - &1) *
                   (Re z + max (&0) (abs(Im z) - Re z)) pow (n - 1)))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `b:real^1` THEN
      ASM_CASES_TAC `&0 <= drop b /\ abs (Im z) - Re z <= drop b` THENL
       [ASM_MESON_TAC[integrable_on]; MATCH_MP_TAC INTEGRABLE_ON_NULL] THEN
      REWRITE_TAC[CONTENT_EQ_0_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC
     `\b. lift(inv((&1 - &n) * (Re z + b) pow (n - 1)) -
               inv((&1 - &n) *
                   (Re z + max (&0) (abs(Im z) - Re z)) pow (n - 1)))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[EVENTUALLY_AT_POSINFINITY; real_ge] THEN
      EXISTS_TAC `max(&0) (abs(Im z) - Re z)` THEN
      REWRITE_TAC[FORALL_DROP; LIFT_DROP] THEN
      REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC INTEGRAL_UNIQUE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[LIFT_SUB; VECTOR_SUB] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM VECTOR_ADD_LID] THEN
    MATCH_MP_TAC LIM_ADD THEN
    REWRITE_TAC[GSYM LIFT_NEG; GSYM REAL_INV_NEG; GSYM REAL_MUL_LNEG] THEN
    REWRITE_TAC[REAL_NEG_SUB; LIM_CONST] THEN
    REWRITE_TAC[REAL_INV_MUL; LIFT_CMUL] THEN
    MATCH_MP_TAC LIM_NULL_CMUL THEN
    REWRITE_TAC[GSYM LIFT_NUM; GSYM LIM_CX_LIFT] THEN
    REWRITE_TAC[CX_INV; CX_POW; GSYM COMPLEX_POW_INV; CX_ADD] THEN
    ONCE_REWRITE_TAC[COMPLEX_ADD_SYM] THEN
    MATCH_MP_TAC LIM_INV_X_POW_OFFSET THEN ASM_ARITH_TAC) in
  let lemma3 = prove
   (`!z n. 2 <= n /\ (Im z = &0 ==> &0 < Re z)
           ==> (\t. Cx(bernoulli n (frac (drop t))) / (z + Cx(drop t)) pow n)
               integrable_on {t | &0 <= drop t}`,
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[complex_div; GSYM COMPLEX_CMUL] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_MUL_BERNOULLI_FRAC THEN
    ASM_SIMP_TAC[GSYM COMPLEX_POW_INV; lemma2]) in
  let lemma4 = prove
   (`!z p. (Im z = &0 ==> &0 < Re z) /\ 1 <= p
           ==> ((\t. Cx(bernoulli 1 (frac(drop t))) / (z + Cx(drop t)))
                has_integral
                (integral {t | &0 <= drop t}
                          (\t. Cx(bernoulli (2 * p + 1) (frac(drop t))) /
                               (z + Cx(drop t)) pow (2 * p + 1)) /
                 Cx(&(2 * p + 1)) -
                 vsum(1..p) (\k. Cx(bernoulli (2 * k) (&0) /
                                    (&4 * &k pow 2 - &2 * &k)) /
                                 z pow (2 * k - 1))))
                {t | &0 <= drop t}`,
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HAS_INTEGRAL_LIM_SEQUENTIALLY THEN CONJ_TAC THENL
     [REWRITE_TAC[o_DEF; LIFT_DROP; complex_div; COMPLEX_VEC_0] THEN
      MATCH_MP_TAC LIM_NULL_COMPLEX_LMUL_BOUNDED THEN
      EXISTS_TAC `&1 / &2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `x:real` THEN
        REWRITE_TAC[BERNOULLI_CONV `bernoulli 1 x`] THEN DISJ1_TAC THEN
        REWRITE_TAC[COMPLEX_NORM_CX] THEN
        MP_TAC(SPEC `x:real` FLOOR_FRAC) THEN REAL_ARITH_TAC;
        MATCH_MP_TAC(REWRITE_RULE[o_DEF] LIM_INFINITY_POSINFINITY_CX) THEN
        ONCE_REWRITE_TAC[COMPLEX_ADD_SYM] THEN REWRITE_TAC[LIM_INV_Z_OFFSET]];
      ALL_TAC] THEN
    MP_TAC(GEN `n:num` (CONJ
     (SPECL [`0`; `n:num`; `z:complex`] lemma1)
     (SPECL [`p:num`; `n:num`; `z:complex`] lemma1))) THEN
    ASM_REWRITE_TAC[FORALL_AND_THM] THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
    REWRITE_TAC[VSUM_CLAUSES_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[SIMPLE_COMPLEX_ARITH `a * Cx(&1) / b = a / b`] THEN
    REWRITE_TAC[LIFT_NUM; COMPLEX_POW_1; COMPLEX_DIV_1] THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
    REWRITE_TAC[VECTOR_ARITH `a + vec 0 + x:real^N = a + y <=> x = y`] THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
    GEN_REWRITE_TAC LAND_CONV [COMPLEX_RING `a - b:complex = --b + a`] THEN
    MATCH_MP_TAC LIM_ADD THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM VSUM_NEG] THEN MATCH_MP_TAC LIM_VSUM THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      REWRITE_TAC[CX_DIV; complex_div; GSYM COMPLEX_MUL_RNEG] THEN
      REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC] THEN
      MATCH_MP_TAC LIM_COMPLEX_LMUL THEN
      REWRITE_TAC[SIMPLE_COMPLEX_ARITH
       `inv x * (y * w - y * z):complex = y / x * (w - z)`] THEN
      SUBGOAL_THEN
       `Cx(&(FACT(2 * k - 2))) / Cx(&(FACT(2 * k))) =
        inv(Cx(&4 * &k pow 2 - &2 * &k))`
       (fun th -> ONCE_REWRITE_TAC[th])
      THENL
       [MATCH_MP_TAC(COMPLEX_FIELD
         `~(y = Cx(&0)) /\ ~(z = Cx(&0)) /\ x * z = y
          ==> x / y = inv(z)`) THEN
        REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ; FACT_NZ] THEN
        REWRITE_TAC[REAL_ENTIRE; REAL_ARITH
         `&4 * x pow 2 - &2 * x = (&2 * x) * (&2 * x - &1)`] THEN
        ASM_SIMP_TAC[ARITH_RULE `1 <= k ==> 1 <= 2 * k`; REAL_OF_NUM_SUB;
                     REAL_OF_NUM_MUL; GSYM CX_MUL; CX_INJ; REAL_OF_NUM_EQ] THEN
        CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `1 <= k` THEN SPEC_TAC(`k:num`,`k:num`) THEN
        INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
        CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN (K ALL_TAC) THEN
        REWRITE_TAC[ARITH_RULE `(2 + k) - 2 = k /\ (2 + k) - 1 = k + 1`] THEN
        REWRITE_TAC[ARITH_RULE `2 + k = SUC(SUC k)`; FACT] THEN ARITH_TAC;
        MATCH_MP_TAC LIM_COMPLEX_LMUL THEN
        ONCE_REWRITE_TAC[COMPLEX_RING `--z = Cx(&0) - z`] THEN
        MATCH_MP_TAC LIM_SUB THEN REWRITE_TAC[LIM_CONST] THEN
        REWRITE_TAC[GSYM COMPLEX_POW_INV] THEN
        ONCE_REWRITE_TAC[COMPLEX_ADD_SYM] THEN
        MATCH_MP_TAC LIM_INV_N_POW_OFFSET THEN ASM_ARITH_TAC];
      MP_TAC(SPECL [`z:complex`; `2 * p + 1`] lemma3) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPEC `Cx(&(FACT(2 * p)))` o
          MATCH_MP INTEGRABLE_COMPLEX_LMUL) THEN
      DISCH_THEN(MP_TAC o MATCH_MP INTEGRABLE_INTEGRAL) THEN
      ASM_SIMP_TAC[INTEGRAL_COMPLEX_LMUL] THEN
      REWRITE_TAC[HAS_INTEGRAL_LIM_AT_POSINFINITY] THEN
      DISCH_THEN(MP_TAC o
          MATCH_MP LIM_POSINFINITY_SEQUENTIALLY o CONJUNCT2) THEN
      DISCH_THEN(MP_TAC o SPEC `inv(Cx(&(FACT(2 * p + 1))))` o
          MATCH_MP LIM_COMPLEX_RMUL) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THENL
       [REWRITE_TAC[LIFT_NUM; FUN_EQ_THM] THEN
        X_GEN_TAC `n:num` THEN REWRITE_TAC[complex_div] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN
        REWRITE_TAC[complex_div; COMPLEX_MUL_AC];

        REWRITE_TAC[complex_div] THEN MATCH_MP_TAC(COMPLEX_RING
         `x * y:complex = z ==> (x * i) * y = i * z`) THEN
        REWRITE_TAC[GSYM ADD1; FACT; GSYM REAL_OF_NUM_MUL; CX_MUL] THEN
        MATCH_MP_TAC(COMPLEX_FIELD
         `~(a = Cx(&0)) /\ ~(b = Cx(&0)) ==> a * inv(b * a) = inv b`) THEN
        REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ; FACT_NZ; NOT_SUC]]]) in
  let lemma5 = prove
   (`!z n. 1 <= n /\ (Im z = &0 ==> &0 < Re z)
           ==> (\t. Cx(bernoulli n (frac (drop t))) / (z + Cx(drop t)) pow n)
               integrable_on {t | &0 <= drop t}`,
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
     `1 <= n ==> n = 1 \/ 2 <= n`)) THEN
    ASM_SIMP_TAC[lemma3; COMPLEX_POW_1] THEN
    REWRITE_TAC[integrable_on] THEN
    ASM_MESON_TAC[LE_REFL; lemma4]) in
  let lemma6 = prove
   (`!z. (Im z = &0 ==> &0 < Re z)
         ==> lgamma(z) =
             ((z - Cx(&1) / Cx(&2)) * clog(z) - z + Cx(&1)) +
             (integral {t | &0 <= drop t}
                       (\t. Cx(bernoulli 1 (frac(drop t))) /
                            (Cx(&1) + Cx(drop t))) -
              integral {t | &0 <= drop t}
                       (\t. Cx(bernoulli 1 (frac(drop t))) /
                            (z + Cx(drop t))))`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `!n. ~(z + Cx(&n) = Cx(&0))` ASSUME_TAC THENL
     [REWRITE_TAC[COMPLEX_EQ; IM_ADD; RE_ADD; IM_CX; RE_CX] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~(z = Cx(&0))` ASSUME_TAC THENL
     [ASM_MESON_TAC[COMPLEX_ADD_RID]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP LGAMMA_ALT) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT]
     (REWRITE_RULE[TRIVIAL_LIMIT_SEQUENTIALLY]
          (ISPEC `sequentially` LIM_UNIQUE))) THEN
    MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN EXISTS_TAC
     `\n. z * clog (Cx(&n)) - clog (Cx(&n + &1)) +
          ((Cx(&1) + Cx(&n) + Cx(&1) / Cx(&2)) * clog (Cx(&1) + Cx(&n)) -
           (Cx(&1) - Cx(&1) / Cx(&2)) * clog (Cx(&1)) -
           Cx(&n) +
           integral (interval [lift (&0),lift (&n)])
           (\x. Cx(bernoulli 1 (frac (drop x))) *
                Cx(&1) / (Cx(&1) + Cx(drop x)) pow 1) /
           Cx(&1)) -
          ((z + Cx(&n) + Cx(&1) / Cx(&2)) * clog (z + Cx(&n)) -
           (z - Cx(&1) / Cx(&2)) * clog z -
           Cx(&n) +
           integral (interval [lift (&0),lift (&n)])
           (\x. Cx(bernoulli 1 (frac (drop x))) *
                Cx(&1) / (z + Cx(drop x)) pow 1) /
           Cx(&1))` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      EXISTS_TAC `1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `clog(Cx(&(FACT n))) =
        vsum(0..n) (\m. clog(Cx(&m) + Cx(&1))) - clog(Cx(&n + &1))`
      SUBST1_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_ADD; GSYM CX_ADD] THEN
        REWRITE_TAC[GSYM(SPEC `1` VSUM_OFFSET); ADD_CLAUSES] THEN
        SIMP_TAC[GSYM NPRODUCT_FACT; REAL_OF_NUM_NPRODUCT; FINITE_NUMSEG;
                 GSYM CX_LOG; LOG_PRODUCT; PRODUCT_POS_LT; IN_NUMSEG;
                 REAL_OF_NUM_LT; LE_1; GSYM VSUM_CX] THEN
        REWRITE_TAC[GSYM ADD1; VSUM_CLAUSES_NUMSEG] THEN
        REWRITE_TAC[ARITH_RULE `1 <= SUC n`; REAL_OF_NUM_SUC] THEN
        SIMP_TAC[CX_LOG; REAL_OF_NUM_LT; LT_0] THEN
        REWRITE_TAC[COMPLEX_RING `(a + b) - b:complex = a`];
        ONCE_REWRITE_TAC[COMPLEX_RING
         `(a + b - c) - d:complex = (a - c) + (b - d)`]] THEN
      MP_TAC(SPECL [`0`; `n:num`] lemma1) THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[VSUM_CLAUSES_NUMSEG; ARITH; VECTOR_ADD_LID] THEN
      ASM_SIMP_TAC[RE_CX; REAL_LT_01];
      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_POW_1; COMPLEX_DIV_1] THEN
    ONCE_REWRITE_TAC[COMPLEX_RING
     `a + (b - c - n + x) - (d - e - n + y):complex =
      (a + (b - c) - (d - e)) + (x - y)`] THEN
    MATCH_MP_TAC LIM_ADD THEN CONJ_TAC THENL
     [REWRITE_TAC[CLOG_1; COMPLEX_MUL_RZERO; COMPLEX_SUB_RZERO] THEN
      ONCE_REWRITE_TAC[LIM_NULL_COMPLEX] THEN REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN REWRITE_TAC[CX_ADD] THEN
      MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN EXISTS_TAC
       `\n. z * (clog(Cx(&n)) - clog(z + Cx(&n))) +
                (Cx(&n) + Cx(&1) / Cx(&2)) *
                (clog(Cx(&1) + Cx(&n)) - clog(z + Cx(&n))) -
                (Cx(&1) - z)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN CONV_TAC COMPLEX_RING;
        ALL_TAC] THEN
      MATCH_MP_TAC LIM_NULL_COMPLEX_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC LIM_NULL_COMPLEX_LMUL THEN
        GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o BINDER_CONV o
                         LAND_CONV o RAND_CONV) [GSYM COMPLEX_ADD_LID] THEN
        ONCE_REWRITE_TAC[COMPLEX_ADD_SYM] THEN REWRITE_TAC[LIM_SUB_CLOG];
        ONCE_REWRITE_TAC[COMPLEX_RING
         `(a + h) * x - y:complex = h * x + a * x - y`] THEN
        MATCH_MP_TAC LIM_NULL_COMPLEX_ADD THEN REWRITE_TAC[] THEN
        ONCE_REWRITE_TAC[COMPLEX_ADD_SYM] THEN
        SIMP_TAC[LIM_NULL_COMPLEX_LMUL; LIM_SUB_CLOG] THEN
        REWRITE_TAC[GSYM LIM_NULL_COMPLEX; LIM_N_MUL_SUB_CLOG]];
      REWRITE_TAC[complex_div; COMPLEX_MUL_LID] THEN
      REWRITE_TAC[LIFT_NUM] THEN MATCH_MP_TAC LIM_SUB THEN
      CONJ_TAC THEN REWRITE_TAC[GSYM LIFT_NUM] THEN
      MATCH_MP_TAC LIM_POSINFINITY_SEQUENTIALLY THEN
      REWRITE_TAC[LIFT_NUM] THEN
      MATCH_MP_TAC(MATCH_MP (TAUT `(p <=> q /\ r) ==> (p ==> r)`)
          (SPEC_ALL HAS_INTEGRAL_LIM_AT_POSINFINITY)) THEN
      REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL; GSYM complex_div] THEN
      ONCE_REWRITE_TAC[COMPLEX_RING `z + x:complex = (z + x) pow 1`] THEN
      MATCH_MP_TAC lemma5 THEN
      ASM_REWRITE_TAC[LE_REFL; RE_CX; REAL_LT_01]]) in
  let lemma7 = prove
   (`((\y. integral {t | &0 <= drop t}
            (\t. Cx (bernoulli 1 (frac (drop t))) / (ii * Cx y + Cx(drop t))))
      --> Cx(&0)) at_posinfinity`,
    MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC
     `\y. integral {t | &0 <= drop t}
                   (\t. Cx(bernoulli 3 (frac (drop t))) /
                        (ii * Cx y + Cx(drop t)) pow 3) / Cx(&3) -
          Cx(bernoulli 2 (&0) / &2) / (ii * Cx y)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[EVENTUALLY_AT_POSINFINITY; real_ge] THEN
      EXISTS_TAC `&1` THEN X_GEN_TAC `y:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 < y` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`ii * Cx y`; `1`] lemma4) THEN
      ASM_SIMP_TAC[IM_MUL_II; RE_CX; REAL_LT_IMP_NZ; LE_REFL] THEN
      REWRITE_TAC[VSUM_SING_NUMSEG] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[COMPLEX_POW_1] THEN
      DISCH_THEN(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN REFL_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC LIM_NULL_COMPLEX_SUB THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[complex_div] THEN MATCH_MP_TAC LIM_NULL_COMPLEX_LMUL THEN
      REWRITE_TAC[COMPLEX_INV_MUL] THEN MATCH_MP_TAC LIM_NULL_COMPLEX_LMUL THEN
      REWRITE_TAC[LIM_INV_X]] THEN
    ONCE_REWRITE_TAC[complex_div] THEN MATCH_MP_TAC LIM_NULL_COMPLEX_RMUL THEN
    MATCH_MP_TAC LIM_NULL_COMPARISON_COMPLEX THEN
    EXISTS_TAC
     `\y. Cx(&1 / &2 / y) *
          integral {t | &0 <= drop t}
                  (\t. inv(Cx(&1) + Cx(drop t)) pow 2)` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC LIM_NULL_COMPLEX_RMUL THEN
      REWRITE_TAC[real_div; CX_MUL] THEN
      MATCH_MP_TAC LIM_NULL_COMPLEX_LMUL THEN
      REWRITE_TAC[LIM_INV_X; CX_INV]] THEN
    REWRITE_TAC[EVENTUALLY_AT_POSINFINITY; real_ge] THEN
    EXISTS_TAC `&1` THEN X_GEN_TAC `y:real` THEN DISCH_TAC THEN
    SIMP_TAC[GSYM INTEGRAL_COMPLEX_LMUL; lemma2;
             ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; ARITH;
             RE_CX; REAL_OF_NUM_LT] THEN
    MATCH_MP_TAC(REAL_ARITH
      `abs(Re z) <= norm z /\ x <= Re z ==> x <= norm z`) THEN
    REWRITE_TAC[COMPLEX_NORM_GE_RE_IM] THEN REWRITE_TAC[RE_DEF] THEN
    MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL_COMPONENT THEN
    REWRITE_TAC[DIMINDEX_2; ARITH] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC lemma5 THEN
      REWRITE_TAC[ARITH; IM_MUL_II; RE_CX] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC INTEGRABLE_COMPLEX_LMUL THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC lemma2 THEN
      REWRITE_TAC[RE_CX; REAL_LT_01] THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_LIFT; IN_ELIM_THM; LIFT_DROP; GSYM RE_DEF] THEN
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM CX_ADD; GSYM CX_INV; GSYM CX_MUL; GSYM CX_POW] THEN
    REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; RE_CX] THEN
    REWRITE_TAC[REAL_ARITH `&1 / &2 / y * x = (&1 / &4) * (&2 / y * x)`] THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_ABS_POS; REAL_LE_INV_EQ; NORM_POS_LE] THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`3`; `frac x`] BERNOULLI_BOUND) THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[BERNOULLI_CONV `bernoulli 2 (&0)`] THEN
      ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
      SIMP_TAC[IN_REAL_INTERVAL; REAL_LT_IMP_LE; FLOOR_FRAC];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_INV; GSYM REAL_INV_MUL; GSYM REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [GSYM REAL_INV_INV] THEN
    REWRITE_TAC[GSYM REAL_INV_MUL] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC REAL_LT_MUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LT] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_NORM_POW; REAL_ARITH
       `x pow 3 = (x:real) * x pow 2`] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `inv(&2) * y * x = y * x / &2`] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      W(MP_TAC o PART_MATCH (rand o rand) COMPLEX_NORM_GE_RE_IM o
        rand o snd) THEN
      REWRITE_TAC[IM_ADD; IM_MUL_II; RE_CX; IM_CX] THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `&0 <= x / &2 <=> &0 <= x`] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;

      REWRITE_TAC[COMPLEX_SQNORM] THEN
      REWRITE_TAC[RE_ADD; IM_ADD; RE_MUL_II; IM_MUL_II; IM_CX; RE_CX] THEN
      REWRITE_TAC[REAL_ADD_LID; REAL_ADD_RID; REAL_NEG_0] THEN
      MATCH_MP_TAC(REAL_ARITH
       `&1 pow 2 <= y pow 2 /\ &0 <= (x - &1) pow 2
       ==> (&1 + x) pow 2 / &2 <= x pow 2 + y pow 2`) THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      ASM_REAL_ARITH_TAC]) in
  let lemma8 = prove
   (`integral {t | &0 <= drop t}
              (\t. Cx (bernoulli 1 (frac (drop t))) / (Cx(&1) + Cx(drop t))) =
     Cx(log(&2 * pi) / &2 - &1)`,
    MATCH_MP_TAC(MESON[REAL]
     `real z /\ Re z = y ==> z = Cx y`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_COMPLEX_INTEGRAL THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[COMPLEX_RING `z + x:complex = (z + x) pow 1`] THEN
        MATCH_MP_TAC lemma5 THEN
        ASM_REWRITE_TAC[LE_REFL; RE_CX; REAL_LT_01];
        REWRITE_TAC[GSYM CX_ADD; GSYM CX_DIV; REAL_CX]];
      GEN_REWRITE_TAC I [GSYM CX_INJ]] THEN
    MATCH_MP_TAC(ISPEC `at_posinfinity` LIM_UNIQUE) THEN
    EXISTS_TAC
     `\y:real. Cx(Re(integral {t | &0 <= drop t}
          (\t. Cx(bernoulli 1 (frac (drop t))) / (Cx(&1) + Cx(drop t)))))` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_AT_POSINFINITY; LIM_CONST] THEN
    MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC
     `\y. Cx(Re(lgamma(ii * Cx y) -
          ((ii * Cx y - Cx(&1) / Cx(&2)) * clog(ii * Cx y) -
           ii * Cx y + Cx(&1)) +
          integral {t | &0 <= drop t}
                   (\t. Cx(bernoulli 1 (frac(drop t))) /
                        (ii * Cx y + Cx(drop t)))))` THEN
    REWRITE_TAC[EVENTUALLY_AT_POSINFINITY; real_ge] THEN CONJ_TAC THENL
     [EXISTS_TAC `&1` THEN X_GEN_TAC `y:real` THEN DISCH_TAC THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      MP_TAC(SPEC `ii * Cx y` lemma6) THEN
      ASM_SIMP_TAC[IM_MUL_II; RE_CX; REAL_LT_IMP_NZ] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[COMPLEX_RING `(s + i - j) - s + j:complex = i`];
      ALL_TAC] THEN
    REWRITE_TAC[RE_ADD; RE_SUB; CX_ADD; CX_SUB] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM COMPLEX_ADD_RID] THEN
    MATCH_MP_TAC LIM_ADD THEN CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC LIM_NULL_COMPARISON_COMPLEX THEN
      EXISTS_TAC `\y. integral {t | &0 <= drop t}
         (\t. Cx(bernoulli 1 (frac(drop t))) / (ii * Cx y + Cx(drop t)))` THEN
      REWRITE_TAC[lemma7] THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
      REWRITE_TAC[COMPLEX_NORM_CX; COMPLEX_NORM_GE_RE_IM]] THEN
    REWRITE_TAC[RE_MUL_II; IM_CX; REAL_NEG_0; COMPLEX_SUB_RZERO; RE_CX] THEN
    MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC
     `\y. Cx(log(norm(cgamma(ii * Cx y)))) -
          (Cx(--(pi * y + log y) / &2) + Cx(&1))` THEN
    REWRITE_TAC[EVENTUALLY_AT_POSINFINITY; real_ge] THEN CONJ_TAC THENL
     [EXISTS_TAC `&1` THEN X_GEN_TAC `y:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 < y` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      BINOP_TAC THENL
       [MP_TAC(SPEC `ii * Cx y` CGAMMA_LGAMMA) THEN COND_CASES_TAC THENL
         [FIRST_X_ASSUM(CHOOSE_THEN (MP_TAC o AP_TERM `Im`)) THEN
          REWRITE_TAC[IM_ADD; IM_MUL_II; IM_CX; RE_CX] THEN ASM_REAL_ARITH_TAC;
          DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NORM_CEXP; LOG_EXP]];
        AP_THM_TAC THEN AP_TERM_TAC THEN
        AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
        REWRITE_TAC[COMPLEX_SUB_RDISTRIB; RE_SUB; GSYM CX_DIV] THEN
        REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC; RE_MUL_II; IM_MUL_II; RE_MUL_CX;
                    IM_MUL_CX] THEN
        ASM_SIMP_TAC[RE_CX; IM_CX; REAL_LT_IMP_LE; CX_INJ; REAL_LT_IMP_NZ;
                     GSYM CX_LOG; CLOG_MUL_II] THEN
        REWRITE_TAC[RE_ADD; IM_ADD; RE_CX; IM_CX; RE_MUL_II; IM_MUL_II] THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC
     `\y. Cx((log(&2 * pi) - log(&1 - inv(exp(pi * y) pow 2))) / &2 - &1)` THEN
    REWRITE_TAC[EVENTUALLY_AT_POSINFINITY; real_ge] THEN CONJ_TAC THENL
     [EXISTS_TAC `&1` THEN X_GEN_TAC `y:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 < y` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPEC `ii * Cx y + Cx(&1)` CGAMMA_REFLECTION) THEN
      REWRITE_TAC[CGAMMA_RECURRENCE; COMPLEX_ENTIRE; II_NZ; CX_INJ] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN
      REWRITE_TAC[COMPLEX_RING `Cx(&1) - (z + Cx(&1)) = --z`] THEN
      MP_TAC(SPEC `cgamma(ii * Cx y)` COMPLEX_NORM_POW_2) THEN
      REWRITE_TAC[CNJ_MUL; CNJ_II; CNJ_CX; CNJ_CGAMMA] THEN
      REWRITE_TAC[COMPLEX_MUL_LNEG; GSYM COMPLEX_MUL_ASSOC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[COMPLEX_RING `w * (z + Cx(&1)) = w * z + w`] THEN
      REWRITE_TAC[CSIN_ADD; GSYM CX_SIN; GSYM CX_COS; SIN_PI; COS_PI] THEN
      REWRITE_TAC[COMPLEX_MUL_RZERO; CX_NEG; COMPLEX_MUL_RNEG] THEN
      REWRITE_TAC[COMPLEX_ADD_RID; COMPLEX_MUL_RID] THEN
      REWRITE_TAC[csin; COMPLEX_RING `--ii * x * ii * y = x * y`] THEN
      REWRITE_TAC[COMPLEX_RING `ii * x * ii * y = --(x * y)`] THEN
      REWRITE_TAC[complex_div; COMPLEX_INV_INV; COMPLEX_INV_MUL;
                  COMPLEX_INV_NEG; COMPLEX_MUL_RNEG] THEN
      ASM_SIMP_TAC[CX_INJ; REAL_LT_IMP_NZ; COMPLEX_FIELD
       `~(y = Cx(&0))
        ==> (ii * y * z = --(p * i * Cx(&2) * ii) <=>
             z = --(Cx(&2) * p) * inv y * i)`] THEN
      REWRITE_TAC[GSYM COMPLEX_INV_MUL; GSYM CX_MUL;
                  GSYM CX_EXP; CEXP_NEG] THEN
      REWRITE_TAC[COMPLEX_MUL_LNEG; GSYM COMPLEX_MUL_RNEG;
                  COMPLEX_NEG_INV] THEN
      REWRITE_TAC[COMPLEX_NEG_SUB] THEN
      REWRITE_TAC[GSYM CX_INV; GSYM CX_SUB; GSYM CX_MUL; GSYM CX_INV] THEN
      REWRITE_TAC[CX_INJ; GSYM CX_POW] THEN
      DISCH_THEN(MP_TAC o AP_TERM `sqrt`) THEN
      REWRITE_TAC[POW_2_SQRT_ABS; REAL_ABS_NORM] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_INV_MUL] THEN
      SUBGOAL_THEN `&0 < exp(pi * y) - inv(exp(pi * y))` ASSUME_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `x < &1 /\ &1 < y ==> &0 < y - x`) THEN
        CONJ_TAC THENL [MATCH_MP_TAC REAL_INV_LT_1; ALL_TAC] THEN
        MATCH_MP_TAC REAL_EXP_LT_1 THEN MATCH_MP_TAC REAL_LT_MUL THEN
        ASM_REWRITE_TAC[PI_POS];
        ASM_SIMP_TAC[LOG_MUL; REAL_LT_INV_EQ; PI_POS; REAL_LT_MUL;
                 REAL_ARITH `&0 < &2 * x <=> &0 < x`; LOG_SQRT; LOG_INV]] THEN
      REWRITE_TAC[GSYM CX_ADD; GSYM CX_SUB] THEN
      REWRITE_TAC[REAL_ARITH
      `(l2 + --l + x) / &2 - (--(py + l) / &2 + &1) =
       (l2 + py + x) / &2 - &1`] THEN
      SIMP_TAC[REAL_EXP_NZ; REAL_FIELD
       `~(e = &0) ==> e - inv e = e * (&1 - inv(e pow 2))`] THEN
      SUBGOAL_THEN `inv (exp (pi * y) pow 2) < &1` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_INV_LT_1 THEN
        MATCH_MP_TAC REAL_POW_LT_1 THEN
        REWRITE_TAC[ARITH] THEN
        MATCH_MP_TAC REAL_EXP_LT_1 THEN
        MATCH_MP_TAC REAL_LT_MUL THEN
        ASM_SIMP_TAC[REAL_LT_MUL; PI_POS];
        ASM_SIMP_TAC[LOG_MUL; REAL_EXP_POS_LT; REAL_SUB_LT; LOG_EXP]] THEN
      REWRITE_TAC[CX_INJ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[CX_SUB; CX_DIV] THEN MATCH_MP_TAC LIM_SUB THEN
    REWRITE_TAC[LIM_CONST] THEN
    MATCH_MP_TAC LIM_COMPLEX_DIV THEN REWRITE_TAC[LIM_CONST] THEN
    CONJ_TAC THENL [ALL_TAC; CONV_TAC COMPLEX_RING] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM COMPLEX_SUB_RZERO] THEN
    MATCH_MP_TAC LIM_SUB THEN REWRITE_TAC[LIM_CONST] THEN
    MP_TAC(ISPECL
     [`clog`; `at_posinfinity`;
      `\y. Cx(&1 - inv(exp(pi * y) pow 2))`;
      `Cx(&1)`] LIM_CONTINUOUS_FUNCTION) THEN
    REWRITE_TAC[CLOG_1] THEN ANTS_TAC THENL
     [SIMP_TAC[CONTINUOUS_AT_CLOG; RE_CX; REAL_LT_01; CX_SUB] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM COMPLEX_SUB_RZERO] THEN
      MATCH_MP_TAC LIM_SUB THEN REWRITE_TAC[LIM_CONST] THEN
      REWRITE_TAC[CX_INV; CX_EXP; CX_POW; GSYM COMPLEX_POW_INV] THEN
      MATCH_MP_TAC LIM_NULL_COMPLEX_POW THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[LIM_AT_POSINFINITY] THEN
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      EXISTS_TAC `&1 + inv(e)` THEN REWRITE_TAC[dist; real_ge] THEN
      X_GEN_TAC `x:real` THEN DISCH_TAC THEN
      REWRITE_TAC[COMPLEX_SUB_RZERO; COMPLEX_NORM_INV] THEN
      MATCH_MP_TAC REAL_LT_LINV THEN ASM_REWRITE_TAC[NORM_CEXP; RE_CX] THEN
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
       `&1 + e <= x
        ==> &1 + pi * x <= z /\ &0 <= x * (pi - &1)  ==> e < z`)) THEN
      REWRITE_TAC[REAL_EXP_LE_X] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      MP_TAC(SPEC `e:real` REAL_LT_INV_EQ) THEN
      MP_TAC PI_APPROX_32 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
      REWRITE_TAC[EVENTUALLY_AT_POSINFINITY; real_ge] THEN
      EXISTS_TAC `&1` THEN X_GEN_TAC `y:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 < y` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(GSYM CX_LOG) THEN REWRITE_TAC[REAL_SUB_LT] THEN
      MATCH_MP_TAC REAL_INV_LT_1 THEN MATCH_MP_TAC REAL_POW_LT_1 THEN
      REWRITE_TAC[ARITH] THEN MATCH_MP_TAC REAL_EXP_LT_1 THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_MUL; PI_POS]]) in
  CONJ_TAC THENL [MATCH_ACCEPT_TAC lemma5; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[lemma6] THEN
  REWRITE_TAC[lemma8; CX_SUB] THEN
  REWRITE_TAC[COMPLEX_RING
   `(x + Cx(&1)) + (a - Cx(&1)) - b = (x + a) - b`] THEN
  REWRITE_TAC[complex_sub; GSYM COMPLEX_ADD_ASSOC] THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN  ASM_CASES_TAC `p = 0` THENL
   [ASM_REWRITE_TAC[VSUM_CLAUSES_NUMSEG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[COMPLEX_POW_1; COMPLEX_DIV_1; VECTOR_ADD_LID];
    MP_TAC(SPECL [`z:complex`; `p:num`] lemma4) THEN
    ASM_SIMP_TAC[LE_1] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
    REWRITE_TAC[complex_sub; COMPLEX_NEG_ADD; VECTOR_NEG_NEG] THEN
    REWRITE_TAC[COMPLEX_ADD_SYM]]);;

let LOG_GAMMA_STIRLING = prove
 (`!x p. &0 < x
         ==> log(gamma x) =
             ((x - &1 / &2) * log(x) - x + log(&2 * pi) / &2) +
             sum(1..p) (\k. bernoulli (2 * k) (&0) /
                            (&4 * &k pow 2 - &2 * &k) / x pow (2 * k - 1)) -
             real_integral {t | &0 <= t}
                           (\t. bernoulli (2 * p + 1) (frac t) /
                                (x + t) pow (2 * p + 1)) /
             &(2 * p + 1)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [GSYM REAL_EXP_INJ] THEN
  ASM_SIMP_TAC[EXP_LOG; GAMMA_POS_LT] THEN
  GEN_REWRITE_TAC I [GSYM CX_INJ] THEN REWRITE_TAC[CX_GAMMA] THEN
  MP_TAC(ISPEC `Cx x` CGAMMA_LGAMMA) THEN
  COND_CASES_TAC THENL
   [FIRST_ASSUM(CHOOSE_THEN (MP_TAC o AP_TERM `Re`)) THEN
    REWRITE_TAC[RE_ADD; RE_CX] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CX_EXP] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`Cx x`; `p:num`] LGAMMA_STIRLING) THEN
  ASM_REWRITE_TAC[RE_CX; CX_GAMMA] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[CX_ADD; CX_SUB; CX_DIV; CX_MUL; GSYM VSUM_CX] THEN
  ASM_SIMP_TAC[GSYM CX_LOG; CX_POW] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[COMPLEX_EQ; RE_CX; IM_CX] THEN
  REWRITE_TAC[RE_DEF; IM_DEF] THEN CONJ_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) INTEGRAL_COMPONENT o lhand o snd) THEN
  ASM_SIMP_TAC[LGAMMA_STIRLING_INTEGRALS_EXIST;
               ARITH_RULE `1 <= 2 * p + 1`; RE_CX] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF] THEN
  REWRITE_TAC[GSYM CX_ADD; GSYM CX_POW; GSYM CX_DIV; RE_CX; IM_CX] THEN
  REWRITE_TAC[LIFT_NUM; INTEGRAL_0; DROP_VEC] THEN
  SUBGOAL_THEN
   `{t | &0 <= drop t} = IMAGE lift {t | &0 <= t}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[LIFT_DROP];
    MATCH_MP_TAC(GSYM(REWRITE_RULE[o_DEF] REAL_INTEGRAL))] THEN
  REWRITE_TAC[REAL_INTEGRABLE_ON; o_DEF] THEN
  MP_TAC(SPECL [`Cx x`; `2 * p + 1`] LGAMMA_STIRLING_INTEGRALS_EXIST) THEN
  ASM_REWRITE_TAC[RE_CX; ARITH_RULE `1 <= 2 * p + 1`] THEN
  GEN_REWRITE_TAC LAND_CONV [INTEGRABLE_COMPONENTWISE] THEN
  DISCH_THEN(MP_TAC o SPEC `1`) THEN REWRITE_TAC[DIMINDEX_2; ARITH] THEN
  REWRITE_TAC[GSYM CX_ADD; GSYM CX_POW; GSYM CX_DIV; RE_CX; GSYM RE_DEF] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[LIFT_DROP]);;

(* ------------------------------------------------------------------------- *)
(* Some other mathematical facts that don't directly involve the gamma       *)
(* function can now be proved relatively easily: Euler's product for sin,    *)
(* Wallis's product for pi, and the Gaussian integral.                       *)
(* ------------------------------------------------------------------------- *)

let CSIN_PRODUCT = prove
 (`!z. ((\n. z * cproduct(1..n) (\m. Cx(&1) - (z / Cx(pi * &m)) pow 2))
       --> csin(z)) sequentially`,
  GEN_TAC THEN REWRITE_TAC[CX_MUL; complex_div; COMPLEX_INV_MUL] THEN
  REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN REWRITE_TAC[GSYM complex_div] THEN
  ABBREV_TAC `w = z / Cx pi` THEN
  SUBGOAL_THEN `Cx pi * w = z` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN MP_TAC PI_NZ THEN REWRITE_TAC[GSYM CX_INJ] THEN
    CONV_TAC COMPLEX_FIELD;
    EXPAND_TAC "z" THEN
    SUBGOAL_THEN `csin (Cx pi * w) = Cx pi * csin(Cx pi * w) / Cx pi`
    SUBST1_TAC THENL
     [MP_TAC PI_NZ THEN REWRITE_TAC[GSYM CX_INJ] THEN CONV_TAC COMPLEX_FIELD;
      REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC] THEN
      MATCH_MP_TAC LIM_COMPLEX_LMUL THEN
      ONCE_REWRITE_TAC[GSYM COMPLEX_INV_DIV] THEN
      REWRITE_TAC[GSYM CGAMMA_REFLECTION] THEN
      REWRITE_TAC[COMPLEX_INV_DIV; COMPLEX_INV_MUL] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN SPEC_TAC(`w:complex`,`z:complex`)]] THEN
  X_GEN_TAC `z:complex` THEN
  MP_TAC(SPEC `z:complex` RECIP_CGAMMA) THEN
  MP_TAC(SPEC `Cx(&1) - z` RECIP_CGAMMA) THEN
  REWRITE_TAC[COMPLEX_RING `Cx(&1) - z + m = (m + Cx(&1)) - z`] THEN
  REWRITE_TAC[GSYM CX_ADD; REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[GSYM
   (ISPECL [`f:num->complex`; `m:num`; `1`] CPRODUCT_OFFSET)] THEN
  SIMP_TAC[CPRODUCT_CLAUSES_LEFT; LE_0] THEN
  REWRITE_TAC[ADD_CLAUSES; COMPLEX_ADD_RID; GSYM IMP_CONJ_ALT] THEN
  SIMP_TAC[CPRODUCT_CLAUSES_RIGHT; ARITH_RULE `0 < n + 1 /\ 1 <= n + 1`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_COMPLEX_MUL) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; CX_ADD; ADD_SUB] THEN
  SUBGOAL_THEN `((\n. Cx(&n) / (Cx(&n) + Cx(&1) - z)) --> Cx(&1)) sequentially`
  MP_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM COMPLEX_INV_1] THEN
    ONCE_REWRITE_TAC[GSYM COMPLEX_INV_DIV] THEN
    MATCH_MP_TAC LIM_COMPLEX_INV THEN
    CONJ_TAC THENL [ALL_TAC; CONV_TAC COMPLEX_RING] THEN
    REWRITE_TAC[complex_div; COMPLEX_ADD_RDISTRIB] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM COMPLEX_ADD_RID] THEN
    MATCH_MP_TAC LIM_ADD THEN
    SIMP_TAC[LIM_INV_N; LIM_NULL_COMPLEX_LMUL] THEN
    MATCH_MP_TAC LIM_EVENTUALLY THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `1` THEN
    SIMP_TAC[COMPLEX_MUL_RINV; CX_INJ; REAL_OF_NUM_EQ; LE_1];
    REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP LIM_COMPLEX_MUL)] THEN
  REWRITE_TAC[COMPLEX_MUL_LID] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  MP_TAC(ISPEC `norm(z:complex)` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `MAX 1 N` THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[ARITH_RULE `MAX a b <= c <=> a <= c /\ b <= c`] THEN
  STRIP_TAC THEN REWRITE_TAC[CPOW_SUB; CPOW_N; COMPLEX_POW_1] THEN
  ASM_SIMP_TAC[CX_INJ; REAL_OF_NUM_EQ; LE_1] THEN
  REWRITE_TAC[complex_div; COMPLEX_INV_MUL; COMPLEX_INV_INV] THEN
  REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC] THEN REWRITE_TAC[COMPLEX_RING
   `a * b * c * d * e * f * g * h * i * j * k :complex =
    (a * i) * (j * e) * (h * b) * c * (d * g) * (f * k)`] THEN
  SUBGOAL_THEN `~((Cx(&n) + Cx(&1)) - z = Cx(&0))` ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_SUB_0; GSYM CX_ADD] THEN
    DISCH_THEN(MP_TAC o AP_TERM `norm:complex->real`) THEN
    REWRITE_TAC[COMPLEX_NORM_CX] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[COMPLEX_RING `n + Cx(&1) - z = (n + Cx(&1)) - z`]] THEN
  ASM_SIMP_TAC[COMPLEX_MUL_RINV; CX_INJ; REAL_OF_NUM_EQ; CPOW_EQ_0; LE_1] THEN
  REWRITE_TAC[COMPLEX_MUL_LID] THEN AP_TERM_TAC THEN
  SIMP_TAC[GSYM NPRODUCT_FACT; REAL_OF_NUM_NPRODUCT; CX_PRODUCT; FINITE_NUMSEG;
           GSYM CPRODUCT_INV; GSYM CPRODUCT_MUL] THEN
  MATCH_MP_TAC CPRODUCT_EQ THEN X_GEN_TAC `k:num` THEN
  REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(Cx(&k) = Cx(&0))` MP_TAC THENL
   [ASM_SIMP_TAC[CX_INJ; REAL_OF_NUM_EQ; LE_1];
    CONV_TAC COMPLEX_FIELD]);;

let SIN_PRODUCT = prove
 (`!x. ((\n. x * product(1..n) (\m. &1 - (x / (pi * &m)) pow 2)) ---> sin(x))
       sequentially`,
  GEN_TAC THEN MP_TAC(SPEC `Cx x` CSIN_PRODUCT) THEN
  REWRITE_TAC[REALLIM_COMPLEX; o_DEF] THEN
  SIMP_TAC[CX_MUL; CX_PRODUCT; FINITE_NUMSEG; CX_SIN] THEN
  REWRITE_TAC[CX_SUB; CX_DIV; CX_POW; CX_MUL]);;

let WALLIS_ALT = prove
 (`((\n. product(1..n) (\k. (&2 * &k) / (&2 * &k - &1) *
                            (&2 * &k) / (&2 * &k + &1))) ---> pi / &2)
   sequentially`,
  ONCE_REWRITE_TAC[GSYM REAL_INV_INV] THEN MATCH_MP_TAC REALLIM_INV THEN
  CONJ_TAC THENL [ALL_TAC; MP_TAC PI_POS THEN CONV_TAC REAL_FIELD] THEN
  MP_TAC(SPEC `pi / &2` SIN_PRODUCT) THEN REWRITE_TAC[SIN_PI2] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_ASSOC; REAL_INV_INV] THEN
  DISCH_THEN(MP_TAC o SPEC `inv pi * &2` o MATCH_MP REALLIM_LMUL) THEN
  SIMP_TAC[REAL_MUL_RID; PI_NZ; REAL_FIELD
   `~(pi = &0) ==> (pi * x) * inv pi = x /\
                   (inv pi * &2) * (pi * inv(&2)) * y = y`] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REALLIM_TRANSFORM_EVENTUALLY) THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SIMP_TAC[GSYM PRODUCT_INV; FINITE_NUMSEG] THEN
  MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
  CONV_TAC REAL_FIELD);;

let WALLIS = prove
 (`((\n. (&2 pow n * &(FACT n)) pow 4 / (&(FACT(2 * n)) * &(FACT(2 * n + 1))))
    ---> pi / &2) sequentially`,
  MP_TAC WALLIS_ALT THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REALLIM_TRANSFORM_EVENTUALLY) THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC[PRODUCT_CLAUSES_NUMSEG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= SUC n`] THEN
  REWRITE_TAC[GSYM ADD1; ARITH_RULE `2 * SUC n = SUC(SUC(2 * n))`] THEN
  REWRITE_TAC[FACT; real_pow; GSYM REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; GSYM REAL_OF_NUM_MUL] THEN
  MAP_EVERY (MP_TAC o C SPEC FACT_NZ) [`n:num`; `2 * n`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN CONV_TAC REAL_FIELD);;

let GAUSSIAN_INTEGRAL = prove
 (`((\x. exp(--(x pow 2))) has_real_integral sqrt pi) (:real)`,
  SUBGOAL_THEN
   `((\x. exp(--(x pow 2))) has_real_integral gamma(&1 / &2) / &2)
    {x | &0 <= x}`
  ASSUME_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN
     `(:real) = {x | &0 <= x} UNION IMAGE (--) {x | &0 <= x}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
      REWRITE_TAC[REAL_ARITH `x:real = --y <=> --x = y`; UNWIND_THM1] THEN
      REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[REAL_ARITH `sqrt x = sqrt x / &2 + sqrt x / &2`]] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_UNION THEN
    REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_REFLECT_GEN] THEN
    ASM_SIMP_TAC[REAL_POW_NEG; ARITH; GSYM GAMMA_HALF] THEN
    MATCH_MP_TAC REAL_NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{&0}` THEN
    REWRITE_TAC[REAL_NEGLIGIBLE_SING; IN_ELIM_THM; SET_RULE
    `s INTER IMAGE f s SUBSET {a} <=> !x. x IN s /\ f x IN s ==> f x = a`] THEN
    REAL_ARITH_TAC] THEN
  MP_TAC(SPEC `&1 / &2` EULER_HAS_REAL_INTEGRAL_GAMMA) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(MP_TAC o SPEC `inv(&2)` o MATCH_MP HAS_REAL_INTEGRAL_RMUL) THEN
  REWRITE_TAC[GSYM real_div] THEN
  ONCE_REWRITE_TAC[HAS_REAL_INTEGRAL_ALT] THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_INTER;
           REAL_INTEGRABLE_RESTRICT_INTER; REAL_INTEGRAL_RESTRICT_INTER] THEN
  REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
  REWRITE_TAC[TAUT `p /\ q <=> ~(p ==> ~q)`] THEN
  SIMP_TAC[REAL_ARITH `&0 < B ==> --B <= B /\ ~(B <= --B)`] THEN
  REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC; INTER; IN_REAL_INTERVAL] THEN
  REWRITE_TAC[IN_ELIM_THM; REAL_ARITH
   `&0 <= x /\ (a <= x /\ x <= b) <=> max (&0) a <= x /\ x <= b`] THEN
  REWRITE_TAC[GSYM real_interval] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `a <= --B /\ --B < B /\ B <= b <=>
    max (&0) a = &0 /\ &0 < B /\ a <= --B /\ B <= b`] THEN
  SIMP_TAC[] THEN
  REWRITE_TAC[REAL_ARITH
   `max (&0) a = &0 /\ &0 < B /\ a <= --B /\ B <= b <=>
    a <= --B /\ &0 < B /\ B <= b`] THEN
  GEN_REWRITE_TAC (BINOP_CONV o ONCE_DEPTH_CONV) [IMP_CONJ] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; LEFT_FORALL_IMP_THM] THEN
  REWRITE_TAC[MESON[REAL_LE_REFL] `?a. a <= B`] THEN
  ONCE_REWRITE_TAC[
   MESON[REAL_ARITH `a <= max a b /\ (&0 <= a ==> max (&0) a = a)`]
   `(!a. P (max (&0) a)) <=> (!a. &0 <= a ==> P a)`] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b. &0 <= a /\ a <= b
          ==> ((\x. exp(--(x pow 2))) has_real_integral
               real_integral (real_interval[a pow 2,b pow 2])
                             (\t. t rpow (-- &1 / &2) / exp t / &2))
              (real_interval[a,b])`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL
     [`\t. t rpow (&1 / &2 - &1) / exp t / &2`;
      `\x:real. x pow 2`; `\x. &2 * x`;
      `a:real`; `b:real`; `(a:real) pow 2`; `(b:real) pow 2`; `{&0}`]
     HAS_REAL_INTEGRAL_SUBSTITUTION_STRONG) THEN
    REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_SIMP_TAC[REAL_LE_REFL; REAL_LE_POW_2; COUNTABLE_SING;
                 REAL_POW_LE2] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
        REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
        REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC;
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
        SIMP_TAC[REAL_LE_POW_2; GSYM REAL_LE_SQUARE_ABS] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_DIFF; IN_SING; IN_REAL_INTERVAL] THEN
        REPEAT STRIP_TAC THENL
         [REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
          REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_WITHINREAL THEN
          REAL_DIFFERENTIABLE_TAC THEN
          ASM_REWRITE_TAC[REAL_LT_POW_2; REAL_EXP_NZ]]];
      MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
       (REWRITE_RULE[CONJ_ASSOC] HAS_REAL_INTEGRAL_SPIKE)) THEN
      EXISTS_TAC `{&0}` THEN REWRITE_TAC[REAL_NEGLIGIBLE_SING] THEN
      X_GEN_TAC `x:real` THEN
      REWRITE_TAC[IN_REAL_INTERVAL; IN_DIFF; IN_SING] THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 <= x` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_EXP_NEG; GSYM RPOW_POW] THEN
      ASM_SIMP_TAC[RPOW_RPOW] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[RPOW_NEG; RPOW_POW; REAL_POW_1] THEN
      MP_TAC(SPEC `(x:real) pow 2` REAL_EXP_NZ) THEN
      UNDISCH_TAC `~(x = &0)` THEN CONV_TAC REAL_FIELD];
    FIRST_X_ASSUM(K ALL_TAC o SPECL [`a:real`; `b:real`]) THEN
    DISCH_THEN(LABEL_TAC "*")] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
    DISJ_CASES_TAC(REAL_ARITH `b <= a \/ a <= b`) THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_ON_NULL] THEN
    REWRITE_TAC[real_integrable_on] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REMOVE_THEN "*" (MP_TAC o SPEC `&0`) THEN
  REWRITE_TAC[REAL_LE_REFL; HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `&0 < B /\ B <= b <=> &0 < B /\ B <= b /\ &0 <= b`] THEN
  SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `max B (&1)` THEN
  ASM_REWRITE_TAC[REAL_LT_MAX; REAL_MAX_LE] THEN
  X_GEN_TAC `b:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN TRANS_TAC REAL_LE_TRANS `(b:real) pow 1` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[ARITH]);;
