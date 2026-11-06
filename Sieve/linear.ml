(* ========================================================================= *)
(* The Jurkat-Richert linear sieve: the functions f_n, F and f.              *)
(*                                                                           *)
(* f_1(s) = (3 - s)/s for s < 3 and 0 beyond; for m >= 2                     *)
(*                                                                           *)
(*   f_m(s) = (1/s) int_{max(s,c)}^{m+2} f_(m-1)(t - 1) dt,                  *)
(*                                                                           *)
(* with c = 3 for m odd and c = 2 for m even, which combines Nathanson's     *)
(* recursions (9.21) and (9.22).  Each f_m is nonnegative, decreasing and    *)
(* vanishes for s >= m + 2.  Integrability comes from monotonicity.          *)
(* ========================================================================= *)

needs "Sieve/sieve.ml";;

prioritize_num(); prioritize_complex();;

let sieve_fn = new_recursive_definition num_RECURSION
 `(sieve_fn 0 (s:real) = &0) /\
  (sieve_fn (SUC n) s =
     if n = 0 then (if s < &3 then (&3 - s) / s else &0)
     else real_integral
            (real_interval[max s (if EVEN n then &3 else &2), &(n + 3)])
            (\t. sieve_fn n (t - &1)) / s)`;;

let INTEGRAL_TAIL_MONO = prove
 (`!(g:real->real) c M.
        (!s t. c <= s /\ s <= t ==> g t <= g s) /\
        (!t. c <= t ==> &0 <= g t)
        ==> !x y. c <= x /\ x <= y
                  ==> &0 <= real_integral (real_interval[y,M]) g /\
                      real_integral (real_interval[y,M]) g <=
                      real_integral (real_interval[x,M]) g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!a b. c <= a ==> (g:real->real) real_integrable_on
                                  real_interval[a,b]`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_DECREASING THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!a. c <= a ==> &0 <= real_integral (real_interval[a,M]) g`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `M <= a` THENL
     [ASM_SIMP_TAC[REAL_INTEGRAL_NULL; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_INTEGRAL_POS THEN ASM_SIMP_TAC[IN_REAL_INTERVAL] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
                  ALL_TAC] THEN
  ASM_CASES_TAC `M <= y` THENL
   [ASM_SIMP_TAC[REAL_INTEGRAL_NULL] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real->real`; `x:real`; `M:real`; `y:real`]
         REAL_INTEGRAL_COMBINE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> b <= a + b:real`) THEN
  MATCH_MP_TAC REAL_INTEGRAL_POS THEN ASM_SIMP_TAC[IN_REAL_INTERVAL] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let SIEVE_FN_1 = prove
 (`!s. sieve_fn 1 s = if s < &3 then (&3 - s) / s else &0`,
  REWRITE_TAC[num_CONV `1`; sieve_fn]);;

let SIEVE_FN_SUC = prove
 (`!n s. 1 <= n
         ==> sieve_fn (SUC n) s =
             real_integral
              (real_interval[max s (if EVEN n then &3 else &2), &(n + 3)])
              (\t. sieve_fn n (t - &1)) / s`,
  SIMP_TAC[sieve_fn; ARITH_RULE `1 <= n ==> ~(n = 0)`]);;

let SIEVE_FN_PROPS = prove
 (`!m. 1 <= m
       ==> (!s. &0 < s ==> &0 <= sieve_fn m s) /\
           (!s t. &0 < s /\ s <= t ==> sieve_fn m t <= sieve_fn m s) /\
           (!s. &(m + 2) <= s ==> sieve_fn m s = &0)`,
  INDUCT_TAC THEN REWRITE_TAC[ARITH] THEN
  ASM_CASES_TAC `m = 0` THENL
   [ASM_REWRITE_TAC[GSYM(num_CONV `1`); SIEVE_FN_1; ARITH] THEN
    REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
     [DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      STRIP_TAC THEN REPEAT COND_CASES_TAC THEN
      ASM_SIMP_TAC[REAL_LE_REFL; REAL_LE_DIV; REAL_ARITH
        `&0 < s /\ s < &3 ==> &0 <= &3 - s`; REAL_LT_IMP_LE] THENL
       [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      SUBGOAL_THEN `(&3 - t) / t = &3 / t - &1 /\ (&3 - s) / s = &3 / s - &1`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [CONJ_TAC THEN REWRITE_TAC[real_div] THEN
        REWRITE_TAC[REAL_SUB_RDISTRIB] THEN
        AP_TERM_TAC THEN MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `a - &1 <= b - &1 <=> a <= b`] THEN
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  ASM_SIMP_TAC[SIEVE_FN_SUC; ARITH_RULE `~(m = 0) ==> 1 <= m`] THEN
  ABBREV_TAC `c = if EVEN m then &3 else &2` THEN
  SUBGOAL_THEN `&2 <= c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN COND_CASES_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. sieve_fn m (t - &1)`; `c:real`; `&(m + 3)`]
         INTEGRAL_TAIL_MONO) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "I") THEN
  REWRITE_TAC[ARITH_RULE `1 <= SUC m`] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    USE_THEN "I" (MP_TAC o SPECL [`c:real`; `max s c`]) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN STRIP_TAC THEN
    USE_THEN "I" (MP_TAC o SPECL [`max s c`; `max t c`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `real_integral (real_interval[max s c,&(m + 3)])
                   (\t. sieve_fn m (t - &1)) / t` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `&0 < t` (fun th -> SIMP_TAC[REAL_LE_DIV2_EQ; th]) THENL
       [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL
     [USE_THEN "I" (MP_TAC o SPECL [`c:real`; `max s c`]) THEN
      ANTS_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[]];
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    REWRITE_TAC[real_div; REAL_ENTIRE] THEN DISJ1_TAC THEN
    MATCH_MP_TAC REAL_INTEGRAL_NULL THEN
    REWRITE_TAC[ADD1; GSYM REAL_OF_NUM_ADD] THEN
    UNDISCH_TAC `&(SUC m + 2) <= s` THEN
    REWRITE_TAC[ADD1; GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC]);;

let SIEVE_FN_POS = prove
 (`!m s. 1 <= m /\ &0 < s ==> &0 <= sieve_fn m s`,
  MESON_TAC[SIEVE_FN_PROPS]);;

let SIEVE_FN_SHIFT_INTEGRABLE = prove
 (`!m a b. 1 <= m /\ &1 < a
           ==> (\t. sieve_fn m (t - &1)) real_integrable_on
               real_interval[a,b]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_DECREASING THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `m:num` SIEVE_FN_PROPS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let SIEVE_FN_INTEGRAL_LE = prove
 (`!m s M. 1 <= m /\ (if EVEN m then &3 else &2) <= s
           ==> real_integral (real_interval[s,M]) (\t. sieve_fn m (t - &1))
               <= s * sieve_fn (SUC m) s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&2 <= s` ASSUME_TAC THENL
   [UNDISCH_TAC `(if EVEN m then &3 else &2) <= s` THEN COND_CASES_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SIEVE_FN_SUC] THEN
  SUBGOAL_THEN `max s (if EVEN m then &3 else &2) = s` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_ARITH `&2 <= s ==> ~(s = &0)`] THEN
  MP_TAC(SPEC `m:num` SIEVE_FN_PROPS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[s,max M (&(m + 3))])
                            (\t. sieve_fn m (t - &1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_UPPER_MONO_POS THEN
    ASM_SIMP_TAC[SIEVE_FN_SHIFT_INTEGRABLE; REAL_ARITH `&2 <= s ==> &1 < s`;
                 REAL_ARITH `M <= max M x`] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&(m + 3) <= s` THENL
   [SUBGOAL_THEN
     `real_integral (real_interval[s,max M (&(m + 3))])
                    (\t. sieve_fn m (t - &1)) =
      real_integral (real_interval[s,max M (&(m + 3))]) (\t. &0)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
      UNDISCH_TAC `&(m + 3) <= s` THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_INTEGRAL_0; REAL_INTEGRAL_NULL; REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. sieve_fn m (t - &1)`; `s:real`;
                 `max M (&(m + 3))`; `&(m + 3)`] REAL_INTEGRAL_COMBINE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SIEVE_FN_SHIFT_INTEGRABLE;
                 REAL_ARITH `&2 <= s ==> &1 < s`] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC(REAL_ARITH `y = &0 ==> x + y <= x`) THEN
  SUBGOAL_THEN
   `real_integral (real_interval[&(m + 3),max M (&(m + 3))])
                  (\t. sieve_fn m (t - &1)) =
    real_integral (real_interval[&(m + 3),max M (&(m + 3))]) (\t. &0)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `&(m + 3) <= x` THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[REAL_INTEGRAL_0]]);;

let SIEVE_FN_ODD_SMALL = prove
 (`!m s. 1 <= m /\ EVEN m /\ &0 < s /\ s <= &3
         ==> s * sieve_fn (SUC m) s = &3 * sieve_fn (SUC m) (&3)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SIEVE_FN_SUC] THEN
  ASM_SIMP_TAC[REAL_ARITH `s <= &3 ==> max s (&3) = &3`; REAL_LE_REFL] THEN
  ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_ARITH `~(&3 = &0)`]);;


(* ------------------------------------------------------------------------- *)
(* The comparison function h.  This is [N] (9.23) raised to 3 e^-3 on        *)
(* s < 23/20, so that s h(s) >= 3 e^-3 = 3 h(3) on [1,3]; that repairs the   *)
(* odd case 1 <= s < 3 of [N] Theorem 9.5.  Lemma 9.6 then holds with        *)
(* a = 99/100, using only the crude bound                                    *)
(* int_3^inf e^-x / x dx <= 8 e^-3 / 27.  All integrals have finite upper    *)
(* limits.                                                                   *)
(* ------------------------------------------------------------------------- *)

let sieve_h = new_definition
 `sieve_h s = if s < &23 / &20 then &3 * exp(-- &3)
              else if s <= &2 then exp(-- &2)
              else if s <= &3 then exp(--s)
              else &3 / s * exp(--s)`;;

let sieve_a = new_definition
 `sieve_a = &99 / &100`;;

let SIEVE_A_BOUNDS = prove
 (`&0 < sieve_a /\ sieve_a < &1 /\ sieve_a <= &99 / &100 /\
   exp(&1) <= &3 * sieve_a`,
  REWRITE_TAC[sieve_a] THEN MP_TAC E_BOUNDS THEN REAL_ARITH_TAC);;

let EXP_3_LE = prove
 (`exp(&3) <= &21`,
  SUBGOAL_THEN `exp(&3) = exp(&1) * exp(&1) * exp(&1)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC E_BOUNDS THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2719 / &1000 * &2719 / &1000 * &2719 / &1000` THEN
  CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC) THEN
  TRY(MATCH_MP_TAC REAL_LE_MUL) THEN ASM_REAL_ARITH_TAC);;

let SIEVE_H_NUMERICS = prove
 (`&0 < exp(-- &3) /\
   exp(-- &2) <= &3 * exp(-- &3) /\
   &3 * exp(-- &3) <= &23 / &20 * exp(-- &2) /\
   &37 / &20 * exp(-- &2) + &61 / &180 * exp(-- &3) <=
   &2 * sieve_a * exp(-- &2) /\
   &17 / &20 * exp(-- &2) + &61 / &180 * exp(-- &3) <=
   &3 * sieve_a * exp(-- &3)`,
  SUBGOAL_THEN `exp(-- &2) = exp(&1) * exp(-- &3)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[sieve_a] THEN MP_TAC E_BOUNDS THEN
  MP_TAC(SPEC `-- &3:real` REAL_EXP_POS_LT) THEN
  ABBREV_TAC `E = exp(-- &3)` THEN ABBREV_TAC `e = exp(&1)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&2718 / &1000 * E <= e * E /\ e * E <= &2719 / &1000 * E`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let SIEVE_H_POS = prove
 (`!s. &0 < sieve_h s`,
  GEN_TAC THEN REWRITE_TAC[sieve_h] THEN MP_TAC SIEVE_H_NUMERICS THEN
  STRIP_TAC THEN REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[REAL_EXP_POS_LT] THEN TRY(ASM_REAL_ARITH_TAC) THEN
  MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
  MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC);;

let SIEVE_H_POS_LE = prove
 (`!s. &0 <= sieve_h s`,
  SIMP_TAC[SIEVE_H_POS; REAL_LT_IMP_LE]);;

let SIEVE_H_LE_EXP = prove
 (`!s. &2 <= s ==> sieve_h s <= exp(--s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sieve_h] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL; REAL_EXP_MONO_LE] THEN
  TRY(ASM_REAL_ARITH_TAC) THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

let SIEVE_H_LE_EXP2 = prove
 (`!s. &23 / &20 <= s ==> sieve_h s <= exp(-- &2)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s <= &2` THENL
   [ASM_REWRITE_TAC[sieve_h; GSYM REAL_NOT_LE; REAL_LE_REFL]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(--s)` THEN
  ASM_SIMP_TAC[SIEVE_H_LE_EXP; REAL_ARITH `~(s <= &2) ==> &2 <= s`] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC);;

let SIEVE_H_DECREASING = prove
 (`!s t. s <= t ==> sieve_h t <= sieve_h s`,
  REPEAT STRIP_TAC THEN MP_TAC SIEVE_H_NUMERICS THEN STRIP_TAC THEN
  ASM_CASES_TAC `s < &23 / &20` THENL
   [ASM_CASES_TAC `t < &23 / &20` THENL
     [ASM_REWRITE_TAC[sieve_h; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(-- &2)` THEN
    ASM_SIMP_TAC[SIEVE_H_LE_EXP2; REAL_ARITH `~(t < a) ==> a <= t`] THEN
    ASM_REWRITE_TAC[sieve_h];
    ALL_TAC] THEN
  ASM_CASES_TAC `s <= &2` THENL
   [SUBGOAL_THEN `sieve_h s = exp(-- &2)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[sieve_h]; ALL_TAC] THEN
    MATCH_MP_TAC SIEVE_H_LE_EXP2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `s <= &3` THENL
   [SUBGOAL_THEN `sieve_h s = exp(--s)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[sieve_h]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(--t)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SIEVE_H_LE_EXP THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(t < &23 / &20) /\ ~(t <= &2) /\ ~(t <= &3)`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[sieve_h] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  REWRITE_TAC[REAL_EXP_POS_LE; REAL_EXP_MONO_LE] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let SIEVE_H_3 = prove
 (`sieve_h(&3) = exp(-- &3)`,
  REWRITE_TAC[sieve_h; REAL_ARITH
   `~(&3 < &23 / &20) /\ ~(&3 <= &2) /\ &3 <= &3`]);;

let SIEVE_H_GE_EXP3 = prove
 (`!s. s <= &3 ==> exp(-- &3) <= sieve_h s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SIEVE_H_3] THEN
  MATCH_MP_TAC SIEVE_H_DECREASING THEN ASM_REWRITE_TAC[]);;

let SIEVE_H_LE_1 = prove
 (`!s. sieve_h s <= &1`,
  GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sieve_h(min s (&0))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SIEVE_H_DECREASING THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[sieve_h; REAL_ARITH `min s (&0) < &23 / &20`] THEN
  REWRITE_TAC[REAL_EXP_NEG] THEN
  SUBGOAL_THEN `&4 <= exp(&3)` ASSUME_TAC THENL
   [MP_TAC(SPEC `&3` REAL_EXP_LE_X) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&4 <= x ==> &0 < x`] THEN
  ASM_REAL_ARITH_TAC);;

let SIEVE_H_SMALL = prove
 (`!s. &1 <= s /\ s <= &3 ==> &3 * exp(-- &3) <= s * sieve_h s`,
  REPEAT STRIP_TAC THEN MP_TAC SIEVE_H_NUMERICS THEN STRIP_TAC THEN
  REWRITE_TAC[sieve_h] THEN COND_CASES_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&23 / &20 * exp(-- &2)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[REAL_EXP_POS_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `exp(--s) = exp(&3 - s) * exp(-- &3)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `s * ((&1 + (&3 - s)) * exp(-- &3))` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MP_TAC(SPECL [`s - &1`; `&3 - s`] REAL_LE_MUL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_EXP_LE_X] THEN
    ASM_REAL_ARITH_TAC]);;

let SIEVE_H_SMALL_INV = prove
 (`!s. &1 <= s /\ s <= &3 ==> &3 / s <= exp(&3) * sieve_h s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MP_TAC(SPEC `s:real` SIEVE_H_SMALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `exp(&3) * (&3 * exp(-- &3)) <= exp(&3) * (s * sieve_h s)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `e * (&3 * f) = &3 * (e * f)`; REAL_EXP_NEG_MUL] THEN
  REAL_ARITH_TAC);;

let SIEVE_H_SHIFT = prove
 (`!s. &2 <= s ==> sieve_h(s - &1) <= &4 * sieve_h s`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s - &1 < &23 / &20` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 * exp(-- &3)` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[sieve_h] THEN MP_TAC SIEVE_H_NUMERICS THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC SIEVE_H_GE_EXP3 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC E_BOUNDS THEN STRIP_TAC THEN
  SUBGOAL_THEN `exp(--(s - &1)) = exp(&1) * exp(--s)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `--s:real` REAL_EXP_POS_LT) THEN DISCH_TAC THEN
  ASM_SIMP_TAC[sieve_h; REAL_ARITH `&2 <= s ==> ~(s < &23 / &20)`] THEN
  ASM_CASES_TAC `s <= &3` THENL
   [ASM_SIMP_TAC[REAL_ARITH `s <= &3 ==> s - &1 <= &2`] THEN
    COND_CASES_TAC THENL
     [MP_TAC(SPEC `-- &2:real` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `exp(-- &2) = exp(s - &2) * exp(--s)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(&1)` THEN
    CONJ_TAC THENL [REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
                    ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `~(s <= &3) ==> ~(s - &1 <= &2) /\ ~(s <= &2)`] THEN
  SUBGOAL_THEN `&0 < s /\ &0 < s - &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `&4 * &3 / s * e = (&12 / s) * e`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2719 / &1000 * &4` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
                    REAL_ARITH_TAC];
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(&3 * exp(&1)) / (s - &1) <= &12 / s` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      REWRITE_TAC[REAL_ARITH `&12 / s * (s - &1) = (&12 * (s - &1)) / s`] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
      SUBGOAL_THEN `exp(&1) * s <= &2719 / &1000 * s` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `~(s - &1 <= &3)` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    REWRITE_TAC[REAL_ARITH `&3 / x * e * f = ((&3 * e) / x) * f`;
                REAL_ARITH `&4 * &3 / s * f = (&12 / s) * f`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

let SIEVE_H_TAIL_4 = prove
 (`!M. real_integral (real_interval[&4,M]) (\t. sieve_h(t - &1))
       <= &8 / &9 * exp(-- &3)`,
  GEN_TAC THEN
  SUBGOAL_THEN `&0 <= &8 / &9 * exp(-- &3)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_CASES_TAC `M <= &4` THENL
   [ASM_SIMP_TAC[REAL_INTEGRAL_NULL]; ALL_TAC] THEN
  ABBREV_TAC `q = \u. (&8 - u + u pow 2) / &9` THEN
  SUBGOAL_THEN
   `((\t. exp(&1 - t) * (&1 - (t - &4) / &3 + (t - &4) pow 2 / &9))
     has_real_integral
     (exp(&1 - &4) * q(&4 - &4) - exp(&1 - M) * q(M - &4)))
    (real_interval[&4,M])`
  ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN
    MP_TAC(ISPECL
     [`\t. --(exp(&1 - t) * (&8 - (t - &4) + (t - &4) pow 2) / &9)`;
      `\t. exp(&1 - t) * (&1 - (t - &4) / &3 + (t - &4) pow 2 / &9)`;
      `&4`; `M:real`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MP_TAC(REAL_DIFF_CONV
       `((\t. --(exp(&1 - t) * (&8 - (t - &4) + (t - &4) pow 2) / &9))
         has_real_derivative f') (atreal t)`) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_1] THEN
      CONV_TAC REAL_RING;
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC REAL_RING];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(&1 - &4) * q(&4 - &4) - exp(&1 - M) * q(M - &4)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HAS_REAL_INTEGRAL_LE THEN
    EXISTS_TAC `\t. sieve_h(t - &1)` THEN
    EXISTS_TAC `\t. exp(&1 - t) * (&1 - (t - &4) / &3 + (t - &4) pow 2 / &9)`
    THEN EXISTS_TAC `real_interval[&4,M]` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL] THEN
      MATCH_MP_TAC REAL_INTEGRABLE_DECREASING THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC SIEVE_H_DECREASING THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    REWRITE_TAC[sieve_h] THEN
    REPEAT(COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[REAL_ARITH `--(t - &1) = &1 - t`] THEN
    COND_CASES_TAC THENL
     [SUBGOAL_THEN `t = &4` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[REAL_MUL_RID; REAL_LE_REFL];
      ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    SUBGOAL_THEN `&0 < t - &1` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_LDIV_EQ]] THEN
    SUBGOAL_THEN
     `(&1 - (t - &4) / &3 + (t - &4) pow 2 / &9) * (t - &1) =
      &3 + (t - &4) pow 3 / &9`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &3 <= &3 + x`) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXPAND_TAC "q" THEN REWRITE_TAC[REAL_SUB_REFL] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[REAL_ARITH `&1 - &4 = -- &3`] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x * &8 / &9 - y <= &8 / &9 * x`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
  REWRITE_TAC[REAL_ARITH
   `&8 - u + u pow 2 = (u - &1 / &2) pow 2 + &31 / &4`] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let SIEVE_H_SHIFT_INTEGRABLE = prove
 (`!a b. (\t. sieve_h(t - &1)) real_integrable_on real_interval[a,b]`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_DECREASING THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC SIEVE_H_DECREASING THEN
  ASM_REAL_ARITH_TAC);;

let SIEVE_H_INTEGRAL_POS = prove
 (`!x y. &0 <= real_integral (real_interval[x,y]) (\t. sieve_h(t - &1))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `y <= x` THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_NULL; REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_INTEGRAL_POS THEN
  SIMP_TAC[SIEVE_H_SHIFT_INTEGRABLE; SIEVE_H_POS; REAL_LT_IMP_LE]);;

let SIEVE_H_INTEGRAL_COMBINE = prove
 (`!a b c. a <= b /\ b <= c
           ==> real_integral (real_interval[a,c]) (\t. sieve_h(t - &1)) =
               real_integral (real_interval[a,b]) (\t. sieve_h(t - &1)) +
               real_integral (real_interval[b,c]) (\t. sieve_h(t - &1))`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC REAL_INTEGRAL_COMBINE THEN
  ASM_REWRITE_TAC[SIEVE_H_SHIFT_INTEGRABLE]);;

let SIEVE_H_INTEGRAL_UPPER_MONO = prove
 (`!a M M'. M <= M'
            ==> real_integral (real_interval[a,M]) (\t. sieve_h(t - &1)) <=
                real_integral (real_interval[a,M']) (\t. sieve_h(t - &1))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `M <= a` THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_NULL; SIEVE_H_INTEGRAL_POS] THEN
  MP_TAC(SPECL [`a:real`; `M:real`; `M':real`] SIEVE_H_INTEGRAL_COMBINE) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`M:real`; `M':real`] SIEVE_H_INTEGRAL_POS) THEN
  REAL_ARITH_TAC);;

let HAS_REAL_INTEGRAL_EXP_SHIFT = prove
 (`!a b. a <= b
         ==> ((\t. exp(&1 - t)) has_real_integral (exp(&1 - a) - exp(&1 - b)))
             (real_interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\t. --exp(&1 - t)`; `\t. exp(&1 - t)`; `a:real`; `b:real`]
         REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  REWRITE_TAC[REAL_ARITH `--x - --y = y - x:real`] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
  MP_TAC(REAL_DIFF_CONV
   `((\t. --exp(&1 - t)) has_real_derivative f') (atreal t)`) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let SIEVE_H_INTEGRAL_34 = prove
 (`real_integral (real_interval[&3,&4]) (\t. sieve_h(t - &1)) =
   exp(-- &2) - exp(-- &3)`,
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
  EXISTS_TAC `\t. exp(&1 - t)` THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL; sieve_h] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THENL
     [SUBGOAL_THEN `x = &3` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    COND_CASES_TAC THENL
     [AP_TERM_TAC THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    MP_TAC(SPECL [`&3`; `&4`] HAS_REAL_INTEGRAL_EXP_SHIFT) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[]]);;

let SIEVE_H_INTEGRAL_EXP = prove
 (`!s M. &3 <= s
         ==> real_integral (real_interval[s,M]) (\t. sieve_h(t - &1))
             <= exp(&1 - s)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `M <= s` THENL
   [ASM_SIMP_TAC[REAL_INTEGRAL_NULL; REAL_EXP_POS_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(&1 - s) - exp(&1 - M)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HAS_REAL_INTEGRAL_LE THEN
    EXISTS_TAC `\t. sieve_h(t - &1)` THEN EXISTS_TAC `\t. exp(&1 - t)` THEN
    EXISTS_TAC `real_interval[s,M]` THEN
    REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL; SIEVE_H_SHIFT_INTEGRABLE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_INTEGRAL_EXP_SHIFT THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      MP_TAC(SPEC `x - &1` SIEVE_H_LE_EXP) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `--(x - &1) = &1 - x`]];
    MP_TAC(SPEC `&1 - M` REAL_EXP_POS_LE) THEN REAL_ARITH_TAC]);;

let SIEVE_H_GE3 = prove
 (`!s. &3 <= s ==> s * sieve_h s = &3 * exp(--s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sieve_h] THEN
  REPEAT(COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `s = &3` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC];
    SUBGOAL_THEN `&0 < s` MP_TAC THENL [ASM_REAL_ARITH_TAC;
     CONV_TAC REAL_FIELD]]);;

let SIEVE_H_23 = prove
 (`!s. &2 <= s /\ s <= &3 ==> sieve_h s = exp(--s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sieve_h] THEN
  COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `s = &2` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[]]);;

let SIEVE_H_INTEGRAL_LE_CONST = prove
 (`!a b c. a <= b /\ (!t. a <= t /\ t <= b ==> sieve_h(t - &1) <= c)
           ==> real_integral (real_interval[a,b]) (\t. sieve_h(t - &1)) <=
               c * (b - a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real`; `b:real`; `c:real`] REAL_INTEGRAL_CONST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_INTEGRAL_LE THEN
  REWRITE_TAC[SIEVE_H_SHIFT_INTEGRABLE; REAL_INTEGRABLE_CONST;
              IN_REAL_INTERVAL] THEN
  FIRST_ASSUM ACCEPT_TAC);;

let SIEVE_H_INTEGRAL_GE_CONST = prove
 (`!a b c. a <= b /\ (!t. a <= t /\ t <= b ==> c <= sieve_h(t - &1))
           ==> c * (b - a) <=
               real_integral (real_interval[a,b]) (\t. sieve_h(t - &1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real`; `b:real`; `c:real`] REAL_INTEGRAL_CONST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_INTEGRAL_LE THEN
  REWRITE_TAC[SIEVE_H_SHIFT_INTEGRABLE; REAL_INTEGRABLE_CONST;
              IN_REAL_INTERVAL] THEN
  FIRST_ASSUM ACCEPT_TAC);;

let SIEVE_H_23_INEQ = prove
 (`!s. &2 <= s /\ s <= &3
       ==> &37 / &20 * exp(-- &2) + &61 / &180 * exp(-- &3) -
           (s - &2) * exp(-- &2) <= sieve_a * s * exp(--s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC SIEVE_A_BOUNDS THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. &2 <= x /\ x <= &3 ==> --exp(-- &2) <= (&1 - x) * exp(--x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\x. (&1 - x) * exp(--x)`; `\x. (x - &2) * exp(--x)`;
                   `real_interval[&2,&3]`; `&2`; `x:real`]
           HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
    REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `y:real` THEN STRIP_TAC THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
        MP_TAC(REAL_DIFF_CONV
         `((\x. (&1 - x) * exp(--x)) has_real_derivative f') (atreal y)`) THEN
        MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        REAL_ARITH_TAC;
        X_GEN_TAC `y:real` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
        REWRITE_TAC[REAL_EXP_POS_LE] THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x. sieve_a * x * exp(--x) -
         (&37 / &20 * exp(-- &2) + &61 / &180 * exp(-- &3) -
          (x - &2) * exp(-- &2))`;
    `\x. sieve_a * (&1 - x) * exp(--x) + exp(-- &2)`;
    `real_interval[&2,&3]`; `&2`; `s:real`]
   HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `y:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MP_TAC(REAL_DIFF_CONV
       `((\x. sieve_a * x * exp(--x) -
              (&37 / &20 * exp(-- &2) + &61 / &180 * exp(-- &3) -
               (x - &2) * exp(-- &2)))
        has_real_derivative f') (atreal y)`) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REAL_ARITH_TAC;
      X_GEN_TAC `y:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `sieve_a * --exp(-- &2) <= sieve_a * (&1 - y) * exp(--y)`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ALL_TAC] THEN
      MP_TAC(SPEC `-- &2:real` REAL_EXP_POS_LT) THEN
      SUBGOAL_THEN `sieve_a * exp(-- &2) <= exp(-- &2)` MP_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_EXP_POS_LE];
        ALL_TAC] THEN
      REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC SIEVE_H_NUMERICS THEN REAL_ARITH_TAC);;

let SIEVE_H_INTEGRAL_UPTO = prove
 (`!s M. &2 <= s /\ s <= &3
         ==> real_integral (real_interval[s,M]) (\t. sieve_h(t - &1)) <=
             &37 / &20 * exp(-- &2) + &61 / &180 * exp(-- &3) -
             (s - &2) * exp(-- &2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[s,max M (&4)])
                            (\t. sieve_h(t - &1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SIEVE_H_INTEGRAL_UPPER_MONO THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `M' = max M (&4)` THEN
  SUBGOAL_THEN `&4 <= M'` ASSUME_TAC THENL
   [EXPAND_TAC "M'" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC SIEVE_H_NUMERICS THEN STRIP_TAC THEN
  MP_TAC(SPECL [`&2`; `s:real`; `M':real`] SIEVE_H_INTEGRAL_COMBINE) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`&2`; `&43 / &20`; `M':real`] SIEVE_H_INTEGRAL_COMBINE) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`&43 / &20`; `&3`; `M':real`] SIEVE_H_INTEGRAL_COMBINE) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`&3`; `&4`; `M':real`] SIEVE_H_INTEGRAL_COMBINE) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `M':real` SIEVE_H_TAIL_4) THEN
  MP_TAC SIEVE_H_INTEGRAL_34 THEN
  MP_TAC(SPECL [`&2`; `&43 / &20`; `&3 * exp(-- &3)`]
         SIEVE_H_INTEGRAL_LE_CONST) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[sieve_h] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`&43 / &20`; `&3`; `exp(-- &2)`]
         SIEVE_H_INTEGRAL_LE_CONST) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[sieve_h] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`&2`; `s:real`; `exp(-- &2)`] SIEVE_H_INTEGRAL_GE_CONST) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[sieve_h] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

let SIEVE_H_INTEGRAL_A = prove
 (`!s M. &2 <= s
         ==> real_integral (real_interval[s,M]) (\t. sieve_h(t - &1)) <=
             sieve_a * s * sieve_h s`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&3 <= s` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(&1 - s)` THEN
    ASM_SIMP_TAC[SIEVE_H_INTEGRAL_EXP; SIEVE_H_GE3] THEN
    SUBGOAL_THEN `exp(&1 - s) = exp(&1) * exp(--s)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `a * &3 * e = (&3 * a) * e:real`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    REWRITE_TAC[SIEVE_A_BOUNDS];
    ASM_SIMP_TAC[SIEVE_H_23; REAL_LT_IMP_LE; GSYM REAL_NOT_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&37 / &20 * exp(-- &2) + &61 / &180 * exp(-- &3) -
                (s - &2) * exp(-- &2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SIEVE_H_INTEGRAL_UPTO THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SIEVE_H_23_INEQ THEN ASM_REAL_ARITH_TAC]]);;

let SIEVE_H_INTEGRAL_B = prove
 (`!s M. &1 <= s /\ s <= &3
         ==> real_integral (real_interval[&3,M]) (\t. sieve_h(t - &1)) <=
             sieve_a * s * sieve_h s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sieve_a * &3 * exp(-- &3)` THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`&3`; `M:real`] SIEVE_H_INTEGRAL_UPTO) THEN
    MP_TAC SIEVE_H_NUMERICS THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[SIEVE_A_BOUNDS; REAL_LT_IMP_LE; SIEVE_H_SMALL]]);;

(* ------------------------------------------------------------------------- *)
(* [N] Lemma 9.7: f_m(s) <= 2 e^2 a^(m-1) h(s), and the functions            *)
(* F(s) = 1 + sum f_odd(s) (s >= 1) and f(s) = 1 - sum f_even(s) (s >= 2).   *)
(* ------------------------------------------------------------------------- *)

let SIEVE_FN_1_BOUND = prove
 (`!s. &1 <= s ==> sieve_fn 1 s <= &2 * exp(&2) * sieve_h s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SIEVE_FN_1] THEN
  SUBGOAL_THEN `&0 <= &2 * exp(&2) * sieve_h s` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_EXP_POS_LE; SIEVE_H_POS_LE];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MP_TAC(SPEC `s:real` SIEVE_H_SMALL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&2 * exp(&2) * (&3 * exp(-- &3)) = &6 / exp(&1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `&2 * a * (&3 * b) = &6 * (a * b)`;
                GSYM REAL_EXP_ADD] THEN
    REWRITE_TAC[REAL_ARITH `&2 + -- &3 = -- &1`; REAL_EXP_NEG; real_div];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= &6 / exp(&1)` ASSUME_TAC THENL
   [SIMP_TAC[REAL_LE_RDIV_EQ; REAL_EXP_POS_LT] THEN
    MP_TAC E_BOUNDS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * exp(&2)) * (&3 * exp(-- &3)) <=
                (&2 * exp(&2)) * (s * sieve_h s)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_EXP_POS_LE];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let SIEVE_FN_BOUND = prove
 (`!m s. 1 <= m /\ (if ODD m then &1 else &2) <= s
         ==> sieve_fn m s <= &2 * exp(&2) * sieve_a pow (m - 1) * sieve_h s`,
  INDUCT_TAC THEN REWRITE_TAC[ARITH] THEN
  ASM_CASES_TAC `m = 0` THENL
   [ASM_REWRITE_TAC[GSYM(num_CONV `1`); ARITH; real_pow; REAL_MUL_LID] THEN
    REWRITE_TAC[SIEVE_FN_1_BOUND];
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
  ASM_SIMP_TAC[ARITH_RULE `~(m = 0) ==> 1 <= m`] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[SIEVE_FN_SUC; ARITH_RULE `~(m = 0) ==> 1 <= m`] THEN
  REWRITE_TAC[ARITH_RULE `SUC m - 1 = m`] THEN
  MP_TAC SIEVE_A_BOUNDS THEN STRIP_TAC THEN
  ABBREV_TAC `C = &2 * exp(&2) * sieve_a pow (m - 1)` THEN
  SUBGOAL_THEN `&0 <= C` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_EXP_POS_LE] THEN MATCH_MP_TAC REAL_POW_LE THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * exp(&2) * sieve_a pow m * sieve_h s =
                (C * sieve_a) * sieve_h s`
  SUBST1_TAC THENL
   [EXPAND_TAC "C" THEN
    SUBGOAL_THEN `m = SUC(m - 1)` (fun th ->
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o LAND_CONV o
                       RAND_CONV) [th])
    THENL [ASM_ARITH_TAC; REWRITE_TAC[real_pow] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `c = if EVEN m then &3 else &2` THEN
  SUBGOAL_THEN
   `!x. c <= x
        ==> real_integral (real_interval[x,&(m + 3)])
                          (\t. sieve_fn m (t - &1)) <=
            C * real_integral (real_interval[x,&(m + 3)])
                              (\t. sieve_h(t - &1))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `&(m + 3) <= x` THENL
     [ASM_SIMP_TAC[REAL_INTEGRAL_NULL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&2 <= c` ASSUME_TAC THENL
     [EXPAND_TAC "c" THEN COND_CASES_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `C * real_integral (real_interval[x,&(m + 3)]) (\t. sieve_h(t - &1)) =
      real_integral (real_interval[x,&(m + 3)]) (\t. C * sieve_h(t - &1))`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INTEGRAL_LMUL THEN
      REWRITE_TAC[SIEVE_H_SHIFT_INTEGRABLE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_INTEGRAL_LE THEN
    SIMP_TAC[REAL_INTEGRABLE_LMUL; SIEVE_H_SHIFT_INTEGRABLE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_DECREASING THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      MP_TAC(SPEC `m:num` SIEVE_FN_PROPS) THEN
      ASM_SIMP_TAC[ARITH_RULE `~(m = 0) ==> 1 <= m`] THEN
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    EXPAND_TAC "C" THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(if EVEN m then &3 else &2) = c` THEN
    REWRITE_TAC[GSYM NOT_ODD] THEN COND_CASES_TAC THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
   [UNDISCH_TAC `(if ODD (SUC m) then &1 else &2) <= s` THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  REWRITE_TAC[REAL_ARITH `((C * a) * h) * s = C * a * s * h:real`] THEN
  ASM_CASES_TAC `c <= s` THENL
   [ASM_SIMP_TAC[REAL_ARITH `c <= s ==> max s c = s`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C * real_integral (real_interval[s,&(m + 3)])
                                  (\t. sieve_h(t - &1))` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SIEVE_H_INTEGRAL_A THEN
    UNDISCH_TAC `(if EVEN m then &3 else &2) = c` THEN COND_CASES_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c = &3 /\ &1 <= s /\ s <= &3` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(if ODD (SUC m) then &1 else &2) <= s` THEN
    UNDISCH_TAC `(if EVEN m then &3 else &2) = c` THEN
    REWRITE_TAC[ODD; NOT_ODD] THEN COND_CASES_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `s <= &3 ==> max s (&3) = &3`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `C * real_integral (real_interval[&3,&(m + 3)])
                                (\t. sieve_h(t - &1))` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SIEVE_H_INTEGRAL_B THEN ASM_REWRITE_TAC[]);;

let sieve_F = new_definition
 `sieve_F s = &1 + real_infsum (from 0) (\k. sieve_fn (2 * k + 1) s)`;;

let sieve_f = new_definition
 `sieve_f s = &1 - real_infsum (from 1) (\k. sieve_fn (2 * k) s)`;;

let SIEVE_FODD_SERIES = prove
 (`!s. &1 <= s
       ==> real_summable (from 0) (\k. sieve_fn (2 * k + 1) s) /\
           &0 <= real_infsum (from 0) (\k. sieve_fn (2 * k + 1) s) /\
           real_infsum (from 0) (\k. sieve_fn (2 * k + 1) s) <=
           &2 * exp(&2) * sieve_h s / (&1 - sieve_a)`,
  GEN_TAC THEN DISCH_TAC THEN MP_TAC SIEVE_A_BOUNDS THEN STRIP_TAC THEN
  ABBREV_TAC `C = &2 * exp(&2) * sieve_h s` THEN
  SUBGOAL_THEN `&0 <= C` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN MATCH_MP_TAC REAL_LE_MUL THEN
     REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_EXP_POS_LE; SIEVE_H_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\k. C * sieve_a pow k) real_sums (C * &1 / (&1 - sieve_a))) (from 0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_SERIES_LMUL THEN
    MP_TAC(SPECL [`0`; `sieve_a`] REAL_SUMS_GP) THEN
    REWRITE_TAC[real_pow] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. &0 <= sieve_fn (2 * k + 1) s /\
        sieve_fn (2 * k + 1) s <= C * sieve_a pow k`
  ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(SPEC `2 * k + 1` SIEVE_FN_PROPS) THEN
    ANTS_TAC THENL [ARITH_TAC; STRIP_TAC] THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
                    ALL_TAC] THEN
    MP_TAC(SPECL [`2 * k + 1`; `s:real`] SIEVE_FN_BOUND) THEN
    ASM_REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH; ARITH_RULE `1 <= 2 * k + 1`;
                    ARITH_RULE `(2 * k + 1) - 1 = 2 * k`] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    EXPAND_TAC "C" THEN
    REWRITE_TAC[REAL_ARITH `(&2 * e * h) * p = &2 * e * p * h`] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_POS; REAL_EXP_POS_LE]; ALL_TAC]) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_MONO_INV THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ARITH_TAC;
      REWRITE_TAC[SIEVE_H_POS_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_summable (from 0) (\k. sieve_fn (2 * k + 1) s)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
    EXISTS_TAC `\k. C * sieve_a pow k` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[real_summable]; ALL_TAC] THEN
    EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_SERIES_LE THEN
    EXISTS_TAC `\k:num. &0` THEN
    EXISTS_TAC `\k. sieve_fn (2 * k + 1) s` THEN
    EXISTS_TAC `from 0` THEN ASM_REWRITE_TAC[REAL_SERIES_0] THEN
    ASM_REWRITE_TAC[REAL_SUMS_INFSUM];
    MATCH_MP_TAC REAL_SERIES_LE THEN
    EXISTS_TAC `\k. sieve_fn (2 * k + 1) s` THEN
    EXISTS_TAC `\k. C * sieve_a pow k` THEN
    EXISTS_TAC `from 0` THEN ASM_REWRITE_TAC[REAL_SUMS_INFSUM] THEN
    SUBGOAL_THEN `&2 * exp(&2) * sieve_h s / (&1 - sieve_a) =
                  C * &1 / (&1 - sieve_a)` SUBST1_TAC THENL
     [EXPAND_TAC "C" THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]]]);;

let SIEVE_FEVEN_SERIES = prove
 (`!s. &2 <= s
       ==> real_summable (from 1) (\k. sieve_fn (2 * k) s) /\
           &0 <= real_infsum (from 1) (\k. sieve_fn (2 * k) s) /\
           real_infsum (from 1) (\k. sieve_fn (2 * k) s) <=
           &2 * exp(&2) * sieve_h s / (&1 - sieve_a)`,
  GEN_TAC THEN DISCH_TAC THEN MP_TAC SIEVE_A_BOUNDS THEN STRIP_TAC THEN
  ABBREV_TAC `C = &2 * exp(&2) * sieve_h s` THEN
  SUBGOAL_THEN `&0 <= C` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN MATCH_MP_TAC REAL_LE_MUL THEN
     REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_EXP_POS_LE; SIEVE_H_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\k. C * sieve_a pow k) real_sums (C * sieve_a / (&1 - sieve_a)))
    (from 1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_SERIES_LMUL THEN
    MP_TAC(SPECL [`1`; `sieve_a`] REAL_SUMS_GP) THEN
    REWRITE_TAC[REAL_POW_1] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. 1 <= k
        ==> &0 <= sieve_fn (2 * k) s /\
            sieve_fn (2 * k) s <= C * sieve_a pow k`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MP_TAC(SPEC `2 * k` SIEVE_FN_PROPS) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
                    ALL_TAC] THEN
    MP_TAC(SPECL [`2 * k`; `s:real`] SIEVE_FN_BOUND) THEN
    ASM_REWRITE_TAC[ODD_MULT; ARITH] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    EXPAND_TAC "C" THEN
    REWRITE_TAC[REAL_ARITH `(&2 * e * h) * p = &2 * e * p * h`] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_POS; REAL_EXP_POS_LE]; ALL_TAC]) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_MONO_INV THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_ARITH_TAC;
      REWRITE_TAC[SIEVE_H_POS_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_summable (from 1) (\k. sieve_fn (2 * k) s)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
    EXISTS_TAC `\k. C * sieve_a pow k` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[real_summable]; ALL_TAC] THEN
    EXISTS_TAC `1` THEN REWRITE_TAC[GE; IN_FROM] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_SERIES_LE THEN
    EXISTS_TAC `\k:num. &0` THEN
    EXISTS_TAC `\k. sieve_fn (2 * k) s` THEN
    EXISTS_TAC `from 1` THEN ASM_REWRITE_TAC[REAL_SERIES_0] THEN
    ASM_REWRITE_TAC[REAL_SUMS_INFSUM; IN_FROM] THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C * sieve_a / (&1 - sieve_a)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_SERIES_LE THEN
      EXISTS_TAC `\k. sieve_fn (2 * k) s` THEN
      EXISTS_TAC `\k. C * sieve_a pow k` THEN
      EXISTS_TAC `from 1` THEN ASM_REWRITE_TAC[REAL_SUMS_INFSUM; IN_FROM] THEN
      ASM_SIMP_TAC[];
      EXPAND_TAC "C" THEN REWRITE_TAC[real_div] THEN
      REWRITE_TAC[REAL_ARITH
       `(&2 * e * h) * a * i <= &2 * e * h * i <=>
        &0 <= (&2 * e * h * i) * (&1 - a)`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[SIEVE_H_POS_LE] THEN
      MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC]]);;
