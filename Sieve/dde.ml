(* ========================================================================= *)
(* The functions F and f of the linear sieve on their initial ranges         *)
(* ([N] Lemmas 9.10-9.11, Theorem 9.8, without the value A = 2 e^gamma):     *)
(*                                                                           *)
(*   s F(s) = A           for 1 <= s <= 3,  A = 3 F(3) (>= 3),               *)
(*   s f(s) = A log(s-1)  for 2 <= s <= 4,  in particular f(2) = 0.          *)
(*                                                                           *)
(* Everything is proved term by term on the f_n and then summed as numeric   *)
(* series, so no interchange of sums and integrals is needed; f(2) = 0 uses  *)
(* the adjoint function q(s) = s - 1 the same way.                           *)
(* ========================================================================= *)

needs "Sieve/linear.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* F on [1,3].                                                               *)
(* ------------------------------------------------------------------------- *)

let sieve_A = new_definition
 `sieve_A = &3 * sieve_F(&3)`;;

let SIEVE_F_SMALL = prove
 (`!s. &1 <= s /\ s <= &3 ==> s * sieve_F s = sieve_A`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sieve_A; sieve_F] THEN
  MP_TAC(SPEC `s:real` SIEVE_FODD_SERIES) THEN
  MP_TAC(SPEC `&3` SIEVE_FODD_SERIES) THEN
  ASM_REWRITE_TAC[REAL_ARITH `&1 <= &3`] THEN
  REWRITE_TAC[GSYM REAL_SUMS_INFSUM] THEN STRIP_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Sa = real_infsum (from 0) (\k. sieve_fn (2 * k + 1) s)` THEN
  ABBREV_TAC `Sb = real_infsum (from 0) (\k. sieve_fn (2 * k + 1) (&3))` THEN
  MP_TAC(ISPECL [`\k. sieve_fn (2 * k + 1) s`; `Sa:real`; `0`; `1`]
         REAL_SUMS_OFFSET) THEN
  MP_TAC(ISPECL [`\k. sieve_fn (2 * k + 1) (&3)`; `Sb:real`; `0`; `1`]
         REAL_SUMS_OFFSET) THEN
  ASM_REWRITE_TAC[ARITH; SUM_SING_NUMSEG] THEN
  REWRITE_TAC[ARITH_RULE `2 * 0 + 1 = 1`; SIEVE_FN_1] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_LT_CONV) THEN
    REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `&3` o MATCH_MP REAL_SERIES_LMUL) THEN
  DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o SPEC `s:real` o
    MATCH_MP REAL_SERIES_LMUL) THEN ASSUME_TAC th) THEN
  DISCH_TAC THEN RULE_ASSUM_TAC BETA_RULE THEN
  SUBGOAL_THEN
   `((\k. &3 * sieve_fn (2 * k + 1) (&3)) real_sums
     (s * (Sa - (if s < &3 then (&3 - s) / s else &0)))) (from 1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_SUMS_EQ THEN
    EXISTS_TAC `\k. s * sieve_fn (2 * k + 1) s` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_FROM] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    REWRITE_TAC[ARITH_RULE `2 * k + 1 = SUC(2 * k)`] THEN
    MATCH_MP_TAC SIEVE_FN_ODD_SMALL THEN
    ASM_REWRITE_TAC[EVEN_MULT; ARITH] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `s * (Sa - (if s < &3 then (&3 - s) / s else &0)) = &3 * Sb`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_SERIES_UNIQUE THEN
    EXISTS_TAC `\k. &3 * sieve_fn (2 * k + 1) (&3)` THEN
    EXISTS_TAC `from 1` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `s * (if s < &3 then (&3 - s) / s else &0) = &3 - s`
  MP_TAC THENL
   [COND_CASES_TAC THENL
     [MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `c = if s < &3 then (&3 - s) / s else &0` THEN
  CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* f on [2,4].                                                               *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_INTEGRAL_INV_SHIFT = prove
 (`!c s. &1 < s /\ s <= &4
         ==> ((\t. c / (t - &1)) has_real_integral
              (c * (log(&3) - log(s - &1)))) (real_interval[s,&4])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\t. c * log(t - &1)`; `\t. c / (t - &1)`; `s:real`; `&4`]
         REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  REWRITE_TAC[REAL_ARITH `&4 - &1 = &3`] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real` THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    MP_TAC(DISCH_ALL(REAL_DIFF_CONV
     `((\t. c * log(t - &1)) has_real_derivative f) (atreal x)`)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC]);;

let SIEVE_FN_EVEN_24 = prove
 (`!k s. 1 <= k /\ &2 <= s /\ s <= &4
         ==> s * sieve_fn (2 * k) s =
             &4 * sieve_fn (2 * k) (&4) +
             &3 * (sieve_fn (2 * k - 1) (&3) + (if k = 1 then &1 else &0)) *
             (log(&3) - log(s - &1)) -
             (if k = 1 then &4 - s else &0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?n. 2 * k = SUC n /\ 1 <= n /\ ~EVEN n` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `2 * (k - 1) + 1` THEN REWRITE_TAC[EVEN_ADD; EVEN_MULT;
    ARITH] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `SUC n - 1 = n`] THEN
  ASM_SIMP_TAC[SIEVE_FN_SUC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&2 <= s ==> max s (&2) = s`;
               REAL_ARITH `max (&4) (&2) = &4`] THEN
  ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_ARITH `&2 <= s ==> ~(s = &0)`;
               REAL_ARITH `~(&4 = &0)`] THEN
  SUBGOAL_THEN `&4 <= &(n + 3)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. sieve_fn n (t - &1)`; `s:real`; `&(n + 3)`; `&4`]
         REAL_INTEGRAL_COMBINE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SIEVE_FN_SHIFT_INTEGRABLE;
                 REAL_ARITH `&2 <= s ==> &1 < s`];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC(REAL_ARITH `a = c - d ==> a + b = b + c - (d:real)`) THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  ASM_CASES_TAC `k = 1` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `n = 1` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SIEVE_FN_1] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_LT_CONV) THEN
    REWRITE_TAC[REAL_ADD_LID; REAL_MUL_LID] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
    EXISTS_TAC `\t. &3 / (t - &1) - &1` THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN COND_CASES_TAC THENL
       [UNDISCH_TAC `&2 <= s` THEN UNDISCH_TAC `s <= t` THEN
        CONV_TAC REAL_FIELD;
        SUBGOAL_THEN `t = &4` SUBST1_TAC THENL
         [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\t. &3 / (t - &1)`; `\t:real. &1`;
                   `&3 * (log(&3) - log(s - &1))`; `&4 - s`;
                   `real_interval[s,&4]`] HAS_REAL_INTEGRAL_SUB) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_INTEGRAL_INV_SHIFT THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`s:real`; `&4`; `&1`] HAS_REAL_INTEGRAL_CONST) THEN
      ASM_REWRITE_TAC[REAL_MUL_LID]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RID; REAL_SUB_RZERO] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
  EXISTS_TAC `\t. (&3 * sieve_fn n (&3)) / (t - &1)` THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `?m. n = SUC m /\ 1 <= m /\ EVEN m` STRIP_ASSUME_TAC THENL
     [EXISTS_TAC `n - 1` THEN
      SUBGOAL_THEN `n = SUC(n - 1)` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `~EVEN n` THEN
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THEN
      REWRITE_TAC[EVEN];
      ALL_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(t - &1) * sieve_fn (SUC m) (t - &1) =
                  &3 * sieve_fn (SUC m) (&3)` MP_TAC THENL
     [MATCH_MP_TAC SIEVE_FN_ODD_SMALL THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `&2 <= s` THEN UNDISCH_TAC `s <= t` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_INV_SHIFT THEN ASM_REAL_ARITH_TAC);;

let SUMS_DELTA_1 = prove
 (`!c. ((\k. if k = 1 then c else &0) real_sums c) (from 1)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`\k. if k = 1 then c else &0`; `{1}`; `from 1`]
         REAL_SERIES_FINITE_SUPPORT) THEN
  SUBGOAL_THEN `{1} INTER from 1 = {1}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_SING; IN_FROM] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[FINITE_SING; SUM_SING; IN_SING] THEN
  DISCH_THEN MATCH_MP_TAC THEN SIMP_TAC[]);;

let SIEVE_SF_24 = prove
 (`!s. &2 <= s /\ s <= &4
       ==> s * sieve_f s =
           &4 * sieve_f(&4) - sieve_A * (log(&3) - log(s - &1))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sieve_f; sieve_A; sieve_F] THEN
  MP_TAC(SPEC `s:real` SIEVE_FEVEN_SERIES) THEN
  MP_TAC(SPEC `&4` SIEVE_FEVEN_SERIES) THEN
  MP_TAC(SPEC `&3` SIEVE_FODD_SERIES) THEN
  ASM_REWRITE_TAC[REAL_ARITH `&2 <= &4 /\ &1 <= &3`] THEN
  REWRITE_TAC[GSYM REAL_SUMS_INFSUM] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN DISCH_TAC) THEN
  ABBREV_TAC `Is = real_infsum (from 1) (\k. sieve_fn (2 * k) s)` THEN
  ABBREV_TAC `I4 = real_infsum (from 1) (\k. sieve_fn (2 * k) (&4))` THEN
  ABBREV_TAC `Sb = real_infsum (from 0) (\k. sieve_fn (2 * k + 1) (&3))` THEN
  ABBREV_TAC `L = log(&3) - log(s - &1)` THEN
  SUBGOAL_THEN `((\k. sieve_fn (2 * k - 1) (&3)) real_sums Sb) (from 1)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`1`; `\k. sieve_fn (2 * k - 1) (&3)`; `Sb:real`; `0`]
           REAL_SUMS_REINDEX) THEN
    REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `2 * (x + 1) - 1 = 2 * x + 1`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\k. &4 * sieve_fn (2 * k) (&4) +
          &3 * (sieve_fn (2 * k - 1) (&3) + (if k = 1 then &1 else &0)) * L -
          (if k = 1 then &4 - s else &0))
     real_sums (&4 * I4 + &3 * (Sb + &1) * L - (&4 - s))) (from 1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_SERIES_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_SERIES_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_SERIES_SUB THEN REWRITE_TAC[SUMS_DELTA_1] THEN
    MATCH_MP_TAC REAL_SUMS_EQ THEN
    EXISTS_TAC `\k. (&3 * L) * (sieve_fn (2 * k - 1) (&3) +
                                (if k = 1 then &1 else &0))` THEN
    CONJ_TAC THENL [REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&3 * (Sb + &1) * L = (&3 * L) * (Sb + &1)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_SERIES_LMUL THEN
    MATCH_MP_TAC REAL_SERIES_ADD THEN ASM_REWRITE_TAC[SUMS_DELTA_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\k. s * sieve_fn (2 * k) s) real_sums
                 (&4 * I4 + &3 * (Sb + &1) * L - (&4 - s))) (from 1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_SUMS_EQ THEN
    EXISTS_TAC `\k. &4 * sieve_fn (2 * k) (&4) +
          &3 * (sieve_fn (2 * k - 1) (&3) + (if k = 1 then &1 else &0)) * L -
          (if k = 1 then &4 - s else &0)` THEN
    ASM_REWRITE_TAC[IN_FROM] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN EXPAND_TAC "L" THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SIEVE_FN_EVEN_24 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `s * Is = &4 * I4 + &3 * (Sb + &1) * L - (&4 - s)` MP_TAC THENL
   [MATCH_MP_TAC REAL_SERIES_UNIQUE THEN
    EXISTS_TAC `\k. s * sieve_fn (2 * k) s` THEN EXISTS_TAC `from 1` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_SERIES_LMUL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Continuity of the f_n, and the adjoint identity of [N] (9.44) for         *)
(* q(s) = s - 1 in integrated form, applied to each f_n:                     *)
(*   Phi_n(s) = (s-1) s f_n(s) - int_{s-1}^s t f_(n-1)(t) dt,                *)
(*   int_{s1}^{s2} t (f_n - f_(n-1)) = Phi_n(s2) - Phi_n(s1)  (s1 >= 3).     *)
(* ------------------------------------------------------------------------- *)

let SIEVE_FN_CONTINUOUS = prove
 (`!n a b. 1 <= n /\ &0 < a
           ==> sieve_fn n real_continuous_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n = 1` THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\s. max (&0) ((&3 - s) / s)` THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL; SIEVE_FN_1] THEN X_GEN_TAC `s:real` THEN
      STRIP_TAC THEN SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      COND_CASES_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> max (&0) x = x`) THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `x <= &0 ==> max (&0) x = &0`) THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_CONTINUOUS_ON_MAX THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_DIV THEN
      SIMP_TAC[REAL_CONTINUOUS_ON_SUB; REAL_CONTINUOUS_ON_CONST;
               REAL_CONTINUOUS_ON_ID; IN_REAL_INTERVAL] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?m. n = SUC m /\ 1 <= m` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `n - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = if EVEN m then &3 else &2` THEN
  SUBGOAL_THEN `&2 <= c /\ c <= &(m + 3)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_POS] THEN
    MP_TAC(SPEC `m:num` REAL_POS) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\s. ((\x. real_integral (real_interval[x,&(m + 3)])
                                     (\t. sieve_fn m (t - &1))) o
                   (\s. min (max s c) (&(m + 3)))) s / s` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL; o_THM] THEN X_GEN_TAC `s:real` THEN
    STRIP_TAC THEN ASM_SIMP_TAC[SIEVE_FN_SUC] THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN ASM_CASES_TAC `max s c <= &(m + 3)` THENL
     [ASM_SIMP_TAC[REAL_ARITH `x <= y ==> min x y = x`];
      ASM_SIMP_TAC[REAL_ARITH `~(x <= y) ==> min x y = y`] THEN
      SUBGOAL_THEN `&(m + 3) <= max s c` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_INTEGRAL_NULL; REAL_LE_REFL]]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_DIV THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON_ID; IN_REAL_INTERVAL] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_MIN THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_MAX THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_CONST; REAL_CONTINUOUS_ON_ID];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `real_interval[c,&(m + 3)]` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INDEFINITE_INTEGRAL_CONTINUOUS_LEFT THEN
    MATCH_MP_TAC SIEVE_FN_SHIFT_INTEGRABLE THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC]);;

let SIEVE_FN_TAIL_INTEGRAL = prove
 (`!n s. 1 <= n /\ &3 <= s
         ==> s * sieve_fn n s =
             real_integral (real_interval[s,&(n + 2)])
                           (\t. sieve_fn (n - 1) (t - &1))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n = 1` THENL
   [ASM_REWRITE_TAC[SIEVE_FN_1; ARITH; sieve_fn; REAL_INTEGRAL_0] THEN
    ASM_SIMP_TAC[GSYM REAL_NOT_LE; REAL_MUL_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `?m. n = SUC m /\ 1 <= m` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `n - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SIEVE_FN_SUC; ARITH_RULE `SUC m - 1 = m`;
               ARITH_RULE `SUC m + 2 = m + 3`] THEN
  SUBGOAL_THEN `max s (if EVEN m then &3 else &2) = s` SUBST1_TAC THENL
   [COND_CASES_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REAL_ARITH_TAC);;

let ADJOINT_IDENTITY = prove
 (`!(g:real->real) h C B s1 s2.
        &3 <= s1 /\ s1 <= s2 /\ s2 <= B /\
        g real_continuous_on real_interval[&2,B] /\
        (!s. s1 <= s /\ s <= s2
             ==> h s = C - real_integral (real_interval[&3,s])
                                         (\t. g(t - &1)))
        ==> ((\t. h t - t * g t) has_real_integral
             (((s2 - &1) * h s2 -
               real_integral (real_interval[s2 - &1,s2]) (\t. t * g t)) -
              ((s1 - &1) * h s1 -
               real_integral (real_interval[s1 - &1,s1]) (\t. t * g t))))
            (real_interval[s1,s2])`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `J = \s. real_integral (real_interval[&3,s]) (\t. g(t - &1))` THEN
  ABBREV_TAC `K = \x. real_integral (real_interval[&2,x]) (\t. t * g t)` THEN
  SUBGOAL_THEN `(\t. g(t - &1)) real_continuous_on real_interval[&3,B]`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM o_DEF] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[REAL_CONTINUOUS_ON_SUB; REAL_CONTINUOUS_ON_ID;
             REAL_CONTINUOUS_ON_CONST] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      REAL_CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\t. t * g t) real_continuous_on real_interval[&2,B]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN
    ASM_REWRITE_TAC[REAL_CONTINUOUS_ON_ID; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s1 <= s /\ s <= s2
        ==> real_integral (real_interval[s - &1,s]) (\t. t * g t) =
            K s - K(s - &1)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "K" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `a + b = c ==> b = c - (a:real)`) THEN
    MATCH_MP_TAC REAL_INTEGRAL_COMBINE THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      REAL_CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s. (s - &1) * (C - (J:real->real) s) - ((K:real->real) s - K(s - &1))`;
    `\t. (h:real->real) t - t * g t`; `s1:real`; `s2:real`]
   REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real` THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `real_interval[s1,s2] SUBSET real_interval[&3,B] /\
                  real_interval[s1,s2] SUBSET real_interval[&2,B] /\
                  IMAGE (\s. s - &1) (real_interval[s1,s2]) SUBSET
                  real_interval[&2,B]`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET_REAL_INTERVAL; SUBSET; FORALL_IN_IMAGE;
                  IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `((J:real->real) has_real_derivative g(x - &1))
      (atreal x within real_interval[s1,s2])`
    ASSUME_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
      EXISTS_TAC `real_interval[&3,B]` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "J" THEN
      MP_TAC(ISPECL [`\t. (g:real->real)(t - &1)`; `&3`; `B:real`]
             REAL_INTEGRAL_HAS_REAL_DERIVATIVE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:real`) THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!y. &2 <= y /\ y <= B
          ==> ((K:real->real) has_real_derivative y * g y)
              (atreal y within real_interval[&2,B])`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "K" THEN
      MP_TAC(ISPECL [`\t. t * (g:real->real) t`; `&2`; `B:real`]
             REAL_INTEGRAL_HAS_REAL_DERIVATIVE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:real`) THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `((K:real->real) has_real_derivative x * g x)
      (atreal x within real_interval[s1,s2])`
    ASSUME_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
      EXISTS_TAC `real_interval[&2,B]` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `((\s. (K:real->real)(s - &1)) has_real_derivative
       ((x - &1) * g(x - &1)) * &1)
      (atreal x within real_interval[s1,s2])`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `(\s. (K:real->real)(s - &1)) = K o (\s. s - &1)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_DIFF_CHAIN_WITHIN THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
        MP_TAC(REAL_DIFF_CONV
         `((\s. s - &1) has_real_derivative f') (atreal x)`) THEN
        REWRITE_TAC[REAL_SUB_RZERO];
        REWRITE_TAC[] THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
        EXISTS_TAC `real_interval[&2,B]` THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(h:real->real) x - x * g x =
      ((x - &1) * (&0 - g(x - &1)) + &1 * (C - J x)) -
      (x * g x - ((x - &1) * g(x - &1)) * &1)`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `h:real->real`))
        (concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      EXPAND_TAC "J" THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_WITHIN THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
        MP_TAC(REAL_DIFF_CONV
         `((\x. x - &1) has_real_derivative f') (atreal x)`) THEN
        REWRITE_TAC[REAL_SUB_RZERO];
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN
        ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST]];
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  EXPAND_TAC "J" THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(h:real->real) s1 =
    C - real_integral (real_interval[&3,s1]) (\t. g(t - &1)) /\
    h s2 = C - real_integral (real_interval[&3,s2]) (\t. g(t - &1))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[s1 - &1,s1]) (\t. t * g t) =
    (K:real->real) s1 - K(s1 - &1) /\
    real_integral (real_interval[s2 - &1,s2]) (\t. t * g t) =
    K s2 - K(s2 - &1)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

let SIEVE_FN_0 = prove
 (`sieve_fn 0 = \s. &0`,
  REWRITE_TAC[FUN_EQ_THM; sieve_fn]);;

let SIEVE_FN_CONTINUOUS_ALL = prove
 (`!n a b. &0 < a ==> sieve_fn n real_continuous_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[SIEVE_FN_0; REAL_CONTINUOUS_ON_CONST];
    MATCH_MP_TAC SIEVE_FN_CONTINUOUS THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC]);;

let SIEVE_FN_ZERO_BEYOND = prove
 (`!m x. &(m + 2) <= x ==> sieve_fn m x = &0`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `m = 0` THENL
   [ASM_REWRITE_TAC[sieve_fn]; ALL_TAC] THEN
  MP_TAC(SPEC `m:num` SIEVE_FN_PROPS) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[]]);;

let SIEVE_FN_SHIFT_INTEGRABLE_ALL = prove
 (`!m a b. &1 < a
           ==> (\t. sieve_fn m (t - &1)) real_integrable_on
               real_interval[a,b]`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `m = 0` THENL
   [ASM_REWRITE_TAC[SIEVE_FN_0; REAL_INTEGRABLE_CONST];
    MATCH_MP_TAC SIEVE_FN_SHIFT_INTEGRABLE THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC]);;

let SIEVE_FN_TAIL_INTEGRAL_B = prove
 (`!n s B. 1 <= n /\ &3 <= s /\ s <= B /\ &(n + 2) <= B
           ==> s * sieve_fn n s =
               real_integral (real_interval[s,B])
                             (\t. sieve_fn (n - 1) (t - &1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!x y. &(n + 2) <= x
          ==> real_integral (real_interval[x,y])
                            (\t. sieve_fn (n - 1) (t - &1)) = &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `real_integral (real_interval[x,y]) (\t:real. &0)` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[REAL_INTEGRAL_0]] THEN
    MATCH_MP_TAC REAL_INTEGRAL_EQ THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SIEVE_FN_ZERO_BEYOND THEN
    UNDISCH_TAC `&(n + 2) <= x` THEN UNDISCH_TAC `x <= x'` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    SUBGOAL_THEN `&(n - 1) = &n - &1` SUBST1_TAC THENL
     [ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `s <= &(n + 2)` THENL
   [ASM_SIMP_TAC[SIEVE_FN_TAIL_INTEGRAL] THEN
    MP_TAC(ISPECL [`\t. sieve_fn (n - 1) (t - &1)`; `s:real`; `B:real`;
                   `&(n + 2)`] REAL_INTEGRAL_COMBINE) THEN
    ASM_SIMP_TAC[SIEVE_FN_SHIFT_INTEGRABLE_ALL; REAL_LE_REFL;
                 REAL_ARITH `&3 <= s ==> &1 < s`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `~(s <= x) ==> x <= s`] THEN
  SUBGOAL_THEN `sieve_fn n s = &0` SUBST1_TAC THENL
   [MATCH_MP_TAC SIEVE_FN_ZERO_BEYOND THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_MUL_RZERO]]);;

let sieve_phi = new_definition
 `sieve_phi n s =
    (s - &1) * (s * sieve_fn n s) -
    real_integral (real_interval[s - &1,s]) (\t. t * sieve_fn (n - 1) t)`;;

let SIEVE_PHI_DIFF = prove
 (`!n s1 s2. 1 <= n /\ &3 <= s1 /\ s1 <= s2
             ==> ((\t. t * sieve_fn n t - t * sieve_fn (n - 1) t)
                  has_real_integral (sieve_phi n s2 - sieve_phi n s1))
                 (real_interval[s1,s2])`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `B = max s2 (&(n + 2))` THEN
  SUBGOAL_THEN `s2 <= B /\ &(n + 2) <= B` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`sieve_fn (n - 1)`; `\s. s * sieve_fn n s`;
                 `real_integral (real_interval[&3,B])
                                (\t. sieve_fn (n - 1) (t - &1))`;
                 `B:real`; `s1:real`; `s2:real`] ADJOINT_IDENTITY) THEN
  REWRITE_TAC[sieve_phi] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[SIEVE_FN_CONTINUOUS_ALL; REAL_ARITH `&0 < &2`] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `s:real`; `B:real`] SIEVE_FN_TAIL_INTEGRAL_B) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `a + b = c ==> b = c - (a:real)`) THEN
  MATCH_MP_TAC REAL_INTEGRAL_COMBINE THEN
  ASM_SIMP_TAC[SIEVE_FN_SHIFT_INTEGRABLE_ALL; REAL_ARITH `&1 < &3`] THEN
  ASM_REAL_ARITH_TAC);;

let SIEVE_PSI_DIFF = prove
 (`!N s1 s2. &3 <= s1 /\ s1 <= s2
             ==> ((\t. t * sieve_fn N t) has_real_integral
                  (sum(1..N) (\n. sieve_phi n s2) -
                   sum(1..N) (\n. sieve_phi n s1)))
                 (real_interval[s1,s2])`,
  INDUCT_TAC THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH; REAL_SUB_REFL] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN EXISTS_TAC `\t:real. &0` THEN
    REWRITE_TAC[HAS_REAL_INTEGRAL_0; SIEVE_FN_0; REAL_MUL_RZERO];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC N`] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s1:real`; `s2:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`SUC N`; `s1:real`; `s2:real`] SIEVE_PHI_DIFF) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= SUC N`; ARITH_RULE `SUC N - 1 = N`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`\t. t * sieve_fn N t`;
                 `\t. t * sieve_fn (SUC N) t - t * sieve_fn N t`;
                 `sum(1..N) (\n. sieve_phi n s2) -
                  sum(1..N) (\n. sieve_phi n s1)`;
                 `sieve_phi (SUC N) s2 - sieve_phi (SUC N) s1`;
                 `real_interval[s1,s2]`] HAS_REAL_INTEGRAL_ADD) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[]
   `f = g /\ a = b
    ==> (f has_real_integral a) s ==> (g has_real_integral b) s`) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN CONJ_TAC THEN REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* Decay: the partial sums Psi_N = sum_{n<=N} Phi_n are O(s^2 e^-s)          *)
(* uniformly in N, and Psi_N(s) - Psi_N(3) = int_3^s t f_N -> 0.             *)
(* ------------------------------------------------------------------------- *)

let SIEVE_FN_EXP_BOUND = prove
 (`!n t. 1 <= n /\ &2 <= t
         ==> &0 <= sieve_fn n t /\
             sieve_fn n t <= &2 * exp(&2) * sieve_a pow (n - 1) * exp(--t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC SIEVE_FN_POS THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * exp(&2) * sieve_a pow (n - 1) * sieve_h t` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SIEVE_FN_BOUND THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC) THEN
  ASM_SIMP_TAC[REAL_POS; REAL_EXP_POS_LE; SIEVE_H_LE_EXP] THEN
  MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[SIEVE_A_BOUNDS] THEN
  MP_TAC SIEVE_A_BOUNDS THEN REAL_ARITH_TAC);;

let SIEVE_A_GEOMETRIC = prove
 (`!N. sum(1..N) (\n. sieve_a pow (n - 1)) <= &100`,
  SUBGOAL_THEN
   `!N. sum(1..N) (\n. sieve_a pow (n - 1)) = &100 * (&1 - sieve_a pow N)`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN
    ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH; ARITH_RULE `1 <= SUC N`;
                    real_pow; ARITH_RULE `SUC N - 1 = N`] THEN
    REWRITE_TAC[sieve_a] THEN REAL_ARITH_TAC;
    GEN_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> &100 * (&1 - y) <= &100`) THEN
    MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[sieve_a] THEN REAL_ARITH_TAC]);;

let SIEVE_TFN_INTEGRABLE = prove
 (`!m a b. &0 < a
           ==> (\t. t * sieve_fn m t) real_integrable_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN
  ASM_SIMP_TAC[REAL_CONTINUOUS_ON_ID; ETA_AX; SIEVE_FN_CONTINUOUS_ALL]);;

let SIEVE_TFN_INTEGRAL_BOUND = prove
 (`!m x. &2 <= x
         ==> &0 <= real_integral (real_interval[x,x + &1])
                                 (\t. t * sieve_fn m t) /\
             real_integral (real_interval[x,x + &1]) (\t. t * sieve_fn m t)
             <= (x + &1) * (if m = 0 then &0
                            else &2 * exp(&2) * sieve_a pow (m - 1)) *
                exp(--x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `m = 0` THENL
   [ASM_REWRITE_TAC[SIEVE_FN_0; REAL_MUL_RZERO; REAL_MUL_LZERO;
                    REAL_INTEGRAL_0; REAL_LE_REFL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\t. t * sieve_fn m t) real_integrable_on
                real_interval[x,x + &1]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SIEVE_TFN_INTEGRABLE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_POS THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SIEVE_FN_POS THEN CONJ_TAC THENL
     [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[x,x + &1])
               (\t:real. (x + &1) * (&2 * exp(&2) * sieve_a pow (m - 1)) *
                         exp(--x))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_LE THEN
    ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST; IN_REAL_INTERVAL] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`m:num`; `t:real`] SIEVE_FN_EXP_BOUND) THEN
    ANTS_TAC THENL [CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
                    STRIP_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
                           ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * exp(&2) * sieve_a pow (m - 1) * exp(--t)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC) THEN
    REWRITE_TAC[REAL_POS; REAL_EXP_POS_LE; REAL_EXP_MONO_LE] THEN
    TRY(MATCH_MP_TAC REAL_POW_LE THEN MP_TAC SIEVE_A_BOUNDS THEN
        REAL_ARITH_TAC) THEN
    ASM_REAL_ARITH_TAC;
    SIMP_TAC[REAL_INTEGRAL_CONST; REAL_ARITH `x <= x + &1`] THEN
    REAL_ARITH_TAC]);;

let SIEVE_TFN_SHIFTED_BOUND = prove
 (`!n s. 1 <= n /\ &3 <= s
         ==> &0 <= real_integral (real_interval[s - &1,s])
                                 (\t. t * sieve_fn (n - 1) t) /\
             real_integral (real_interval[s - &1,s])
                           (\t. t * sieve_fn (n - 1) t) <=
             (s * &2 * (exp(&2) * exp(&1)) * &100 / &99 * exp(--s)) *
             sieve_a pow (n - 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC SIEVE_A_BOUNDS THEN STRIP_TAC THEN
  MP_TAC(SPECL [`n - 1`; `s - &1`] SIEVE_TFN_INTEGRAL_BOUND) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `s - &1 + &1 = s`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `s * (if n - 1 = 0 then &0
                   else &2 * exp(&2) * sieve_a pow (n - 1 - 1)) *
              exp(--(s - &1))` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `exp(--(s - &1)) = exp(&1) * exp(--s)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LE) THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sieve_a pow (n - 1) = sieve_a * sieve_a pow (n - 1 - 1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sieve_a pow (n - 1 - 1)` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= s * exp(&2) * exp(&1) * exp(--s)` MP_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[REAL_EXP_POS_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `q = sieve_a pow (n - 1 - 1)` THEN
  ABBREV_TAC `E = exp(&2)` THEN ABBREV_TAC `e1 = exp(&1)` THEN
  ABBREV_TAC `es = exp(--s)` THEN
  REWRITE_TAC[sieve_a] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (s * E * e1 * es) * q` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let SIEVE_PSI_BOUND = prove
 (`!N s. &3 <= s
         ==> abs(sum(1..N) (\n. sieve_phi n s)) <=
             &6000 * s pow 2 * exp(--s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sieve_phi; SUM_SUB_NUMSEG] THEN
  MP_TAC SIEVE_A_BOUNDS THEN STRIP_TAC THEN
  MP_TAC(SPEC `N:num` SIEVE_A_GEOMETRIC) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= sum(1..N) (\n. sieve_a pow (n - 1))` ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `G = sum(1..N) (\n. sieve_a pow (n - 1))` THEN
  SUBGOAL_THEN `&0 < exp(--s) /\ &0 < exp(&2) /\ exp(&2) <= &7393 / &1000 /\
                exp(&2) * exp(&1) <= &21`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT; GSYM REAL_EXP_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC[EXP_3_LE] THEN
    SUBGOAL_THEN `exp(&2) = exp(&1) * exp(&1)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC E_BOUNDS THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2719 / &1000 * &2719 / &1000` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= sum(1..N) (\n. (s - &1) * s * sieve_fn n s) /\
    sum(1..N) (\n. (s - &1) * s * sieve_fn n s) <=
    (s pow 2 * &2 * exp(&2) * exp(--s)) * G`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[] THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      TRY(ASM_REAL_ARITH_TAC) THEN MATCH_MP_TAC SIEVE_FN_POS THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    EXPAND_TAC "G" THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(SPECL [`n:num`; `s:real`] SIEVE_FN_EXP_BOUND) THEN
    ANTS_TAC THENL [CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
                    STRIP_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `s pow 2 * sieve_fn n s` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `s pow 2 * &2 * exp(&2) * sieve_a pow (n - 1) * exp(--s)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      REWRITE_TAC[REAL_MUL_AC; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= sum(1..N) (\n. real_integral (real_interval[s - &1,s])
                                       (\t. t * sieve_fn (n - 1) t)) /\
    sum(1..N) (\n. real_integral (real_interval[s - &1,s])
                                 (\t. t * sieve_fn (n - 1) t)) <=
    (s * &2 * (exp(&2) * exp(&1)) * &100 / &99 * exp(--s)) * G`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!n. 1 <= n /\ n <= N
          ==> &0 <= real_integral (real_interval[s - &1,s])
                                  (\t. t * sieve_fn (n - 1) t) /\
              real_integral (real_interval[s - &1,s])
                            (\t. t * sieve_fn (n - 1) t) <=
              (s * &2 * (exp(&2) * exp(&1)) * &100 / &99 * exp(--s)) *
              sieve_a pow (n - 1)`
    ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN
      MATCH_MP_TAC SIEVE_TFN_SHIFTED_BOUND THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_SIMP_TAC[];
      EXPAND_TAC "G" THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
      MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= exp(&2) * exp(&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
  ABBREV_TAC `SA = sum(1..N) (\n. (s - &1) * s * sieve_fn n s)` THEN
  ABBREV_TAC `SB = sum(1..N) (\n. real_integral (real_interval[s - &1,s])
                                        (\t. t * sieve_fn (n - 1) t))` THEN
  ABBREV_TAC `E1 = exp(&2) * exp(&1)` THEN ABBREV_TAC `E = exp(&2)` THEN
  ABBREV_TAC `es = exp(--s)` THEN
  SUBGOAL_THEN `(s pow 2 * es) * (E * G) <= (s pow 2 * es) * (&7393 / &10)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH
       `e * g <= &7393 / &1000 * &100 ==> e * g <= &7393 / &10`) THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s * es) * (E1 * G) <= (s * es) * &2100` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `e * g <= &21 * &100 ==> e * g <= &2100`) THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `s * es <= s pow 2 * es` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let SIEVE_PSI_3_BOUND = prove
 (`!N s. 1 <= N /\ &3 <= s
         ==> abs(sum(1..N) (\n. sieve_phi n (&3))) <=
             &6000 * s pow 2 * exp(--s) +
             s * (s - &3) * &2 * exp(&2) * sieve_a pow (N - 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `&3`; `s:real`] SIEVE_PSI_DIFF) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`N:num`; `s:real`] SIEVE_PSI_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `&0 <= sum(1..N) (\n. sieve_phi n s) - sum(1..N) (\n. sieve_phi n (&3)) /\
    sum(1..N) (\n. sieve_phi n s) - sum(1..N) (\n. sieve_phi n (&3)) <=
    s * (s - &3) * &2 * exp(&2) * sieve_a pow (N - 1)`
  MP_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_INTEGRAL_POS THEN
      EXISTS_TAC `\t. t * sieve_fn N t` THEN
      EXISTS_TAC `real_interval[&3,s]` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC SIEVE_FN_POS THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_LE THEN
    EXISTS_TAC `\t. t * sieve_fn N t` THEN
    EXISTS_TAC `\t:real. s * &2 * exp(&2) * sieve_a pow (N - 1)` THEN
    EXISTS_TAC `real_interval[&3,s]` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`&3`; `s:real`; `s * &2 * exp(&2) * sieve_a pow (N - 1)`]
             HAS_REAL_INTEGRAL_CONST) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
      AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`N:num`; `t:real`] SIEVE_FN_EXP_BOUND) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `exp(--t) <= &1` ASSUME_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &2 * exp(&2) * sieve_a pow (N - 1)` ASSUME_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      REWRITE_TAC[REAL_POS; REAL_EXP_POS_LE] THEN
      MATCH_MP_TAC REAL_POW_LE THEN MP_TAC SIEVE_A_BOUNDS THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 * exp(&2) * sieve_a pow (N - 1)) * exp(--t)` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC]; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* Evaluation at s = 3: the pair series sum_k (Phi_(2k+1) + Phi_(2k+2))(3)   *)
(* sums to -2 f(2), using the explicit forms of the f_n on [2,3].            *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_INTEGRAL_LOG_SHIFT = prove
 (`((\t. log(t - &1)) has_real_integral (&2 * log(&2) - &1))
   (real_interval[&2,&3])`,
  MP_TAC(ISPECL [`\t. (t - &1) * log(t - &1) - t`; `\t. log(t - &1)`;
                 `&2`; `&3`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN X_GEN_TAC `x:real` THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    MP_TAC(DISCH_ALL(REAL_DIFF_CONV
     `((\t. (t - &1) * log(t - &1) - t) has_real_derivative f') (atreal x)`))
    THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&2 <= x` THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC[LOG_1] THEN REAL_ARITH_TAC]);;

let HAS_REAL_INTEGRAL_3_MINUS = prove
 (`((\t. &3 - t) has_real_integral (&1 / &2)) (real_interval[&2,&3])`,
  MP_TAC(ISPECL [`\t. &3 * t - t pow 2 / &2`; `\t:real. &3 - t`; `&2`; `&3`]
                REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    MP_TAC(REAL_DIFF_CONV
     `((\t. &3 * t - t pow 2 / &2) has_real_derivative f') (atreal x)`) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_1] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

let SIEVE_W_ODD = prove
 (`!k. real_integral (real_interval[&2,&3]) (\t. t * sieve_fn (2 * k + 1) t) =
       &3 * sieve_fn (2 * k + 1) (&3) + (if k = 0 then &1 / &2 else &0)`,
  GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[ARITH; SIEVE_FN_1] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_LT_CONV) THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN EXISTS_TAC `\t:real. &3 - t` THEN
    REWRITE_TAC[HAS_REAL_INTEGRAL_3_MINUS] THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THENL
     [UNDISCH_TAC `&2 <= t` THEN CONV_TAC REAL_FIELD;
      SUBGOAL_THEN `t = &3` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RID] THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
  EXISTS_TAC `\t:real. &3 * sieve_fn (2 * k + 1) (&3)` THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    REWRITE_TAC[ARITH_RULE `2 * k + 1 = SUC(2 * k)`] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SIEVE_FN_ODD_SMALL THEN
    REWRITE_TAC[EVEN_MULT; ARITH] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
    MP_TAC(ISPECL [`&2`; `&3`; `&3 * sieve_fn (2 * k + 1) (&3)`]
           HAS_REAL_INTEGRAL_CONST) THEN
    REWRITE_TAC[REAL_ARITH `&2 <= &3`] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC]);;

let HAS_REAL_INTEGRAL_EVEN_PROFILE = prove
 (`!a b c.
        ((\t. a + b * (log(&3) - log(t - &1)) - c * (&4 - t)) has_real_integral
         (a + b * (&1 + log(&3) - &2 * log(&2)) - c * (&3 / &2)))
        (real_interval[&2,&3])`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `((\t. &4 - t) has_real_integral (&3 / &2))
                (real_interval[&2,&3])` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\t:real. &3 - t`; `\t:real. &1`; `&1 / &2`; `&1`;
                   `real_interval[&2,&3]`] HAS_REAL_INTEGRAL_ADD) THEN
    REWRITE_TAC[HAS_REAL_INTEGRAL_3_MINUS] THEN
    MP_TAC(ISPECL [`&2`; `&3`; `&1`] HAS_REAL_INTEGRAL_CONST) THEN
    REWRITE_TAC[REAL_ARITH `&2 <= &3`] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(MESON[] `f = g /\ a = b ==> (f has_real_integral a) s
                          ==> (g has_real_integral b) s`) THEN
    REWRITE_TAC[FUN_EQ_THM] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((\t. log(&3) - log(t - &1)) has_real_integral
                 (&1 + log(&3) - &2 * log(&2))) (real_interval[&2,&3])`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\t:real. log(&3)`; `\t. log(t - &1)`; `log(&3)`;
                   `&2 * log(&2) - &1`; `real_interval[&2,&3]`]
           HAS_REAL_INTEGRAL_SUB) THEN
    REWRITE_TAC[HAS_REAL_INTEGRAL_LOG_SHIFT] THEN
    MP_TAC(ISPECL [`&2`; `&3`; `log(&3)`] HAS_REAL_INTEGRAL_CONST) THEN
    REWRITE_TAC[REAL_ARITH `&2 <= &3`] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC[REAL_MUL_RID] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t:real. a + b * (log(&3) - log(t - &1))`;
                 `\t:real. c * (&4 - t)`;
                 `a + b * (&1 + log(&3) - &2 * log(&2))`; `c * &3 / &2`;
                 `real_interval[&2,&3]`] HAS_REAL_INTEGRAL_SUB) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`\t:real. (a:real)`; `\t. b * (log(&3) - log(t - &1))`;
                     `a:real`; `b * (&1 + log(&3) - &2 * log(&2))`;
                     `real_interval[&2,&3]`] HAS_REAL_INTEGRAL_ADD) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`&2`; `&3`; `a:real`] HAS_REAL_INTEGRAL_CONST) THEN
        REWRITE_TAC[REAL_ARITH `&2 <= &3`] THEN
        CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
        REWRITE_TAC[REAL_MUL_RID];
        MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[REAL_ARITH `c * &3 / &2 = c * (&3 / &2)`] THEN
      MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC(MESON[] `f = g /\ a = b ==> (f has_real_integral a) s
                          ==> (g has_real_integral b) s`) THEN
    REWRITE_TAC[FUN_EQ_THM] THEN CONJ_TAC THEN REAL_ARITH_TAC]);;

let SIEVE_W_EVEN = prove
 (`!k. 1 <= k
       ==> real_integral (real_interval[&2,&3]) (\t. t * sieve_fn (2 * k) t) =
           &4 * sieve_fn (2 * k) (&4) +
           &3 * (sieve_fn (2 * k - 1) (&3) + (if k = 1 then &1 else &0)) *
           (&1 + log(&3) - &2 * log(&2)) -
           (if k = 1 then &3 / &2 else &0)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  ABBREV_TAC `c = if k = 1 then &1 else &0` THEN
  SUBGOAL_THEN `(if k = 1 then &3 / &2 else &0) = c * (&3 / &2) /\
                (!s. (if k = 1 then &4 - s else &0) = c * (&4 - s))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN COND_CASES_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
  EXISTS_TAC `\t. &4 * sieve_fn (2 * k) (&4) +
                  (&3 * (sieve_fn (2 * k - 1) (&3) + c)) *
                  (log(&3) - log(t - &1)) - c * (&4 - t)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(SPECL [`k:num`; `t:real`] SIEVE_FN_EVEN_24) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    MP_TAC(SPECL [`&4 * sieve_fn (2 * k) (&4)`;
                  `&3 * (sieve_fn (2 * k - 1) (&3) + c)`; `c:real`]
           HAS_REAL_INTEGRAL_EVEN_PROFILE) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC]);;

let SUMS_DELTA_0 = prove
 (`!c. ((\k. if k = 0 then c else &0) real_sums c) (from 0)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`\k. if k = 0 then c else &0`; `{0}`; `from 0`]
         REAL_SERIES_FINITE_SUPPORT) THEN
  SUBGOAL_THEN `{0} INTER from 0 = {0}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_SING; IN_FROM] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[FINITE_SING; SUM_SING; IN_SING] THEN
  DISCH_THEN MATCH_MP_TAC THEN SIMP_TAC[]);;

let SIEVE_PHI_3 = prove
 (`!n. sieve_phi n (&3) =
       &6 * sieve_fn n (&3) -
       real_integral (real_interval[&2,&3]) (\t. t * sieve_fn (n - 1) t)`,
  REWRITE_TAC[sieve_phi] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)
  THEN REAL_ARITH_TAC);;

let SIEVE_PSI_PAIRS = prove
 (`!M. sum(1..2 * M + 2) (\n. sieve_phi n (&3)) =
       sum(0..M) (\k. sieve_phi (2 * k + 1) (&3) +
                      sieve_phi (2 * k + 2) (&3))`,
  INDUCT_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 * 0 + 2 = SUC(SUC 0)`; SUM_CLAUSES_NUMSEG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `2 * SUC M + 2 = SUC(SUC(2 * M + 2))`] THEN
  ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`; LE_0] THEN
  REWRITE_TAC[ARITH_RULE `SUC(2 * M + 2) = 2 * SUC M + 1 /\
                          SUC(SUC(2 * M + 2)) = 2 * SUC M + 2`] THEN
  REAL_ARITH_TAC);;

let SIEVE_PAIR_SERIES = prove
 (`((\k. sieve_phi (2 * k + 1) (&3) + sieve_phi (2 * k + 2) (&3)) real_sums
    (-- &2 * sieve_f(&2))) (from 0)`,
  REWRITE_TAC[SIEVE_PHI_3; ARITH_RULE `(2 * k + 1) - 1 = 2 * k`;
              ARITH_RULE `(2 * k + 2) - 1 = 2 * k + 1`] THEN
  MP_TAC(SPEC `&3` SIEVE_FODD_SERIES) THEN
  MP_TAC(SPEC `&3` SIEVE_FEVEN_SERIES) THEN
  MP_TAC(SPEC `&4` SIEVE_FEVEN_SERIES) THEN
  REWRITE_TAC[REAL_ARITH `&1 <= &3 /\ &2 <= &3 /\ &2 <= &4`] THEN
  REWRITE_TAC[GSYM REAL_SUMS_INFSUM] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN DISCH_TAC) THEN
  ABBREV_TAC `Sb = real_infsum (from 0) (\k. sieve_fn (2 * k + 1) (&3))` THEN
  ABBREV_TAC `I3 = real_infsum (from 1) (\k. sieve_fn (2 * k) (&3))` THEN
  ABBREV_TAC `I4 = real_infsum (from 1) (\k. sieve_fn (2 * k) (&4))` THEN
  ABBREV_TAC `lam = &1 + log(&3) - &2 * log(&2)` THEN
  SUBGOAL_THEN `((\k. sieve_fn (2 * k + 2) (&3)) real_sums I3) (from 0)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`1`; `\k. sieve_fn (2 * k) (&3)`; `I3:real`; `0`]
           REAL_SUMS_REINDEX) THEN
    REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `2 * (x + 1) = 2 * x + 2`] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\k. sieve_fn (2 * k - 1) (&3)) real_sums Sb) (from 1)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`1`; `\k. sieve_fn (2 * k - 1) (&3)`; `Sb:real`; `0`]
           REAL_SUMS_REINDEX) THEN
    REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `2 * (x + 1) - 1 = 2 * x + 1`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\k. real_integral (real_interval[&2,&3]) (\t. t * sieve_fn (2 * k) t))
     real_sums (&4 * I4 + &3 * (Sb + &1) * lam - &3 / &2)) (from 0)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`\k. real_integral (real_interval[&2,&3]) (\t. t * sieve_fn (2 * k) t)`;
      `&4 * I4 + &3 * (Sb + &1) * lam - &3 / &2`; `1`; `0`]
     REAL_SUMS_OFFSET_REV) THEN
    REWRITE_TAC[ARITH; SUM_SING_NUMSEG; MULT_CLAUSES; SIEVE_FN_0;
                REAL_MUL_RZERO; REAL_INTEGRAL_0; REAL_ADD_RID] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC REAL_SUMS_EQ THEN
    EXISTS_TAC `\k. &4 * sieve_fn (2 * k) (&4) +
                    &3 * (sieve_fn (2 * k - 1) (&3) +
                          (if k = 1 then &1 else &0)) * lam -
                    (if k = 1 then &3 / &2 else &0)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_FROM] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN EXPAND_TAC "lam" THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC SIEVE_W_EVEN THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_SERIES_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_SERIES_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_SERIES_SUB THEN REWRITE_TAC[SUMS_DELTA_1] THEN
    MATCH_MP_TAC REAL_SUMS_EQ THEN
    EXISTS_TAC `\k. (&3 * lam) * (sieve_fn (2 * k - 1) (&3) +
                                  (if k = 1 then &1 else &0))` THEN
    CONJ_TAC THENL [REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&3 * (Sb + &1) * lam = (&3 * lam) * (Sb + &1)` SUBST1_TAC
    THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_SERIES_LMUL THEN
    MATCH_MP_TAC REAL_SERIES_ADD THEN ASM_REWRITE_TAC[SUMS_DELTA_1];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\k. real_integral (real_interval[&2,&3])
                        (\t. t * sieve_fn (2 * k + 1) t))
     real_sums (&3 * Sb + &1 / &2)) (from 0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SIEVE_W_ODD] THEN MATCH_MP_TAC REAL_SERIES_ADD THEN
    REWRITE_TAC[SUMS_DELTA_0] THEN MATCH_MP_TAC REAL_SERIES_LMUL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `-- &2 * sieve_f(&2) =
    (&6 * Sb - (&4 * I4 + &3 * (Sb + &1) * lam - &3 / &2)) +
    (&6 * I3 - (&3 * Sb + &1 / &2))`
  SUBST1_TAC THENL
   [MP_TAC(SPEC `&2` SIEVE_SF_24) THEN MP_TAC(SPEC `&3` SIEVE_SF_24) THEN
    REWRITE_TAC[REAL_ARITH `&2 <= &2 /\ &2 <= &4 /\ &2 <= &3 /\ &3 <= &4`] THEN
    REWRITE_TAC[sieve_A; sieve_F] THEN
    REWRITE_TAC[REAL_ARITH `&2 - &1 = &1 /\ &3 - &1 = &2`; LOG_1] THEN
    SUBGOAL_THEN `sieve_f(&3) = &1 - I3 /\ sieve_f(&4) = &1 - I4`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[sieve_f] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "lam" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_SERIES_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC REAL_SERIES_SUB THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_SERIES_LMUL THEN ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* f(2) = 0, hence F(s) = A/s on [1,3] and f(s) = A log(s - 1)/s on          *)
(* [2,4] ([N] Theorem 9.8 without the value of A).                           *)
(* ------------------------------------------------------------------------- *)

let S2_EXP_BOUND = prove
 (`!s. &0 < s ==> s pow 2 * exp(--s) <= &27 / s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(s / &3) pow 3 <= exp(s)` ASSUME_TAC THENL
   [SUBGOAL_THEN `exp s = exp(s / &3) pow 3` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_N] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `s / &3` REAL_EXP_LE_X) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < exp s` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `(s pow 2 * exp(--s)) * s = (s pow 3) / exp s` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_EXP_NEG] THEN UNDISCH_TAC `&0 < exp s` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `s pow 3 = &27 * (s / &3) pow 3` SUBST1_TAC THENL
   [CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_ARITH `&0 < &27`]);;

let REALLIM_SUB_ZERO = prove
 (`!(net:A net) (f:A->real) g l.
        (f ---> l) net /\ (g ---> &0) net ==> ((\x. f x - g x) ---> l) net`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`net:A net`; `f:A->real`; `g:A->real`; `l:real`; `&0`]
         REALLIM_SUB) THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO]);;

let SIEVE_F_2 = prove
 (`sieve_f(&2) = &0`,
  ABBREV_TAC `L = -- &2 * sieve_f(&2)` THEN
  SUBGOAL_THEN `L = &0` MP_TAC THENL [ALL_TAC; EXPAND_TAC "L" THEN
    REAL_ARITH_TAC] THEN
  MP_TAC SIEVE_PAIR_SERIES THEN ASM_REWRITE_TAC[real_sums] THEN
  REWRITE_TAC[FROM_INTER_NUMSEG; GSYM SIEVE_PSI_PAIRS] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!s. &3 <= s ==> abs L <= &6000 * s pow 2 * exp(--s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
    EXISTS_TAC `\M. abs(sum(1..2 * M + 2) (\n. sieve_phi n (&3))) -
                    (s * (s - &3) * &2 * exp(&2) * sieve_a) *
                    (sieve_a pow 2) pow M` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REALLIM_SUB_ZERO THEN CONJ_TAC THENL
       [MATCH_MP_TAC REALLIM_ABS THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REALLIM_NULL_LMUL THEN MATCH_MP_TAC REALLIM_POWN THEN
        REWRITE_TAC[sieve_a] THEN CONV_TAC REAL_RAT_REDUCE_CONV];
      ALL_TAC] THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
    X_GEN_TAC `M:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(SPECL [`2 * M + 2`; `s:real`] SIEVE_PSI_3_BOUND) THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= 2 * M + 2`;
                    ARITH_RULE `(2 * M + 2) - 1 = SUC(2 * M)`] THEN
    REWRITE_TAC[real_pow; GSYM REAL_POW_POW; GSYM REAL_POW_MUL] THEN
    REWRITE_TAC[REAL_POW_POW] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `~(&0 < abs L) ==> L = &0`) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `max (&3) (&324000 / abs L)`) THEN
  REWRITE_TAC[REAL_ARITH `&3 <= max (&3) x`] THEN
  ABBREV_TAC `s = max (&3) (&324000 / abs L)` THEN
  SUBGOAL_THEN `&3 <= s /\ &324000 / abs L <= s` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `s:real` S2_EXP_BOUND) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&27 / s <= abs L / &12000` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&3 <= s ==> &0 < s`] THEN
    UNDISCH_TAC `&324000 / abs L <= s` THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let SIEVE_LOWER_24 = prove
 (`!s. &2 <= s /\ s <= &4 ==> s * sieve_f s = sieve_A * log(s - &1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `&2` SIEVE_SF_24) THEN MP_TAC(SPEC `s:real` SIEVE_SF_24) THEN
  ASM_REWRITE_TAC[REAL_ARITH `&2 <= &2 /\ &2 <= &4`; SIEVE_F_2;
                  REAL_ARITH `&2 - &1 = &1`; LOG_1] THEN
  REAL_ARITH_TAC);;

let SIEVE_A_GE_3 = prove
 (`&3 <= sieve_A`,
  REWRITE_TAC[sieve_A; sieve_F] THEN MP_TAC(SPEC `&3` SIEVE_FODD_SERIES) THEN
  REWRITE_TAC[REAL_ARITH `&1 <= &3`] THEN REAL_ARITH_TAC);;

let SIEVE_UPPER_13 = prove
 (`!s. &1 <= s /\ s <= &3 ==> sieve_F s = sieve_A / s`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_EQ_RDIV_EQ; REAL_ARITH `&1 <= s ==> &0 < s`] THEN
  ASM_SIMP_TAC[GSYM SIEVE_F_SMALL] THEN REAL_ARITH_TAC);;

let SIEVE_LOWER_24_EXPLICIT = prove
 (`!s. &2 <= s /\ s <= &4 ==> sieve_f s = (sieve_A * log(s - &1)) / s`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_EQ_RDIV_EQ; REAL_ARITH `&2 <= s ==> &0 < s`] THEN
  ASM_SIMP_TAC[GSYM SIEVE_LOWER_24] THEN REAL_ARITH_TAC);;
