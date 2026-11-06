(* ========================================================================= *)
(* Dirichlet L-functions L(s,c) = dseries c s for complex s.                 *)
(*                                                                           *)
(* For a nonprincipal character c mod d the partial sums of c are bounded by *)
(* d (NONPRINCIPAL_PARTIAL_SUM_BOUND), so L is holomorphic on Re s > 0       *)
(* (HOLOMORPHIC_LFUN).  Bounds uniform in d, for d (|Im s| + 3) <= N:        *)
(*   LFUN_BOUND        |L(s,c)| <= 12 (1 + log N) if Re s >= 1 - 1/log N,    *)
(*   LFUN_DERIV_BOUND  |L'(s,c)| <= 24 (1 + log N)^2 if Re s >= 1 -          *)
(*                     1/(2 log N), d (|Im s| + 4) <= N and N >= 16          *)
(*                     (Cauchy's inequality on a circle, CAUCHY_INEQUALITY). *)
(* THREE_FOUR_ONE: for real x > 1 and every character c                      *)
(*   |zeta(x)|^3 |L(x + it,c)|^4 |L(x + 2it,c^2)| >= 1                       *)
(* (DSERIES_EXP and Re(3 + 4z + z^2) >= 0 for |z| <= 1, TRIG_341_LEMMA).     *)
(* Bounds on Re s > 1 for zeta (ZETA_REAL_BOUND, ZETA_LINE_BOUND) and for    *)
(* the principal character (PRINCIPAL_LFUN_BOUND, via L(s,chi_0) = zeta(s)   *)
(* sum_{e | d} mu(e) e^-s).  LFUN_LOWER_ABSTRACT: if |L(y + 2it,c^2)| <= M2  *)
(* for 1 < y <= 2 and |L'| <= M1 on the line Im z = t, then |L(x + it,c)|    *)
(* >= 2 eta M1 for 1 - eta <= x <= 2, where eta = 1/(2048 M1^4 M2) (the      *)
(* 3-4-1 inequality at x = 1 + eta and the mean value theorem along the      *)
(* line).  Real characters: L(x,c) is real and positive for x > 1            *)
(* (LFUN_REAL_GT1, from DSERIES_EXP) and for x = 1 (LFUN_1_POS, by           *)
(* continuity and LFUNCTION_NONZERO_NONPRINCIPAL; DSERIES_AT_1 identifies    *)
(* dseries c (Cx(&1)) with the library's Lfunction c).                       *)
(* ========================================================================= *)

needs "Sieve/dseries.ml";;
needs "Sieve/characters.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Nonprincipal characters: partial sums and holomorphy.                     *)
(* ------------------------------------------------------------------------- *)

let NONPRINCIPAL_PARTIAL_SUM_BOUND = prove
 (`!d c K. dirichlet_character d c /\ ~(c = chi_0 d)
           ==> norm(vsum(1..K) c) <= &d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(INST [`K:num`,`n:num`]
    (ISPECL [`d:num`; `c:num->complex`] DIRICHLET_CHARACTER_SUM_MOD)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..K MOD d) (\n. &1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    ASM_MESON_TAC[DIRICHLET_CHARACTER_NORM_LE];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_MUL_RID; REAL_OF_NUM_LE] THEN
  ASM_CASES_TAC `d = 0` THENL
   [ASM_MESON_TAC[DIRICHLET_CHARACTER_0]; ALL_TAC] THEN
  MATCH_MP_TAC LT_IMP_LE THEN ASM_SIMP_TAC[MOD_LT_EQ]);;

let DIRICHLET_CHARACTER_DSERIES_HYPS = prove
 (`!d c. dirichlet_character d c
         ==> (!m n. c(m * n) = c m * c n) /\ c 1 = Cx(&1) /\
             (!n. norm(c n) <= &1)`,
  MESON_TAC[DIRICHLET_CHARACTER_MUL; DIRICHLET_CHARACTER_EQ_1;
            DIRICHLET_CHARACTER_NORM_LE]);;

let HOLOMORPHIC_LFUN = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> (dseries c) holomorphic_on {s | Re s > &0}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOLOMORPHIC_DSERIES THEN
  EXISTS_TAC `&d` THEN ASM_MESON_TAC[NONPRINCIPAL_PARTIAL_SUM_BOUND]);;

(* ------------------------------------------------------------------------- *)
(* Bounds for L and L' near the line Re s = 1.                               *)
(* ------------------------------------------------------------------------- *)

let RPOW_NEG_LE_E = prove
 (`!n N x. 1 <= n /\ n <= N /\ 2 <= N /\ &1 - inv(log(&N)) <= x
           ==> &n rpow (--x) <= exp(&1) * inv(&n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &n /\ &0 < log(&N) /\ log(&n) <= log(&N) /\
                &0 <= log(&n)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[rpow] THEN
  SUBGOAL_THEN `exp(&1) * inv(&n) = exp(&1 - log(&n))` SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_EXP_SUB; EXP_LOG; real_div]; ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE] THEN
  SUBGOAL_THEN `log(&n) * inv(log(&N)) <= &1` MP_TAC THENL
   [ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_MUL_LID]; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - inv(log(&N))) * log(&n) <= x * log(&n)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let LFUN_BOUND = prove
 (`!d c s N. dirichlet_character d c /\ ~(c = chi_0 d) /\
             &d * (abs(Im s) + &3) <= &N /\
             &1 - inv(log(&N)) <= Re s /\ &1 / &2 <= Re s
             ==> norm(dseries c s) <= &12 * (&1 + log(&N))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= d` ASSUME_TAC THENL
   [ASM_CASES_TAC `d = 0` THENL
     [ASM_MESON_TAC[DIRICHLET_CHARACTER_0]; ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `3 <= N` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&d * (abs(Im s) + &3)` THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_POS] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&N)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH
   `!x y:complex a b e. norm(y) <= a /\ norm(x - y) <= b /\ a + b <= e
                        ==> norm x <= e`) THEN
  EXISTS_TAC `vsum(1..N) (\n. c n / Cx(&n) cpow s)` THEN
  EXISTS_TAC `exp(&1) * (&1 + log(&N))` THEN
  EXISTS_TAC `&2 * exp(&1)` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..N) (\n. exp(&1) * inv(&n))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `n:num` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[NORM_DIV_CPOW_NUM] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * &n rpow --Re s` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_SIMP_TAC[RPOW_POS_LE; REAL_POS] THEN
        ASM_MESON_TAC[DIRICHLET_CHARACTER_NORM_LE];
        REWRITE_TAC[REAL_MUL_LID] THEN MATCH_MP_TAC RPOW_NEG_LE_E THEN
        EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
      REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_EXP_POS_LE] THEN MATCH_MP_TAC HARMONIC_LE_LOG THEN
      ASM_ARITH_TAC];
    MP_TAC(ISPECL [`c:num->complex`; `s:complex`; `&d`; `N:num`]
      DSERIES_TAIL) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[NONPRINCIPAL_PARTIAL_SUM_BOUND] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z:real`) THEN
    MP_TAC(SPECL [`N:num`; `N:num`; `Re s`] RPOW_NEG_LE_E) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL] THEN ASM_ARITH_TAC;
                    DISCH_TAC] THEN
    SUBGOAL_THEN `&0 < &N` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&d * (&2 + norm s / Re s) <= &2 * &N` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&d * (&2 * (abs(Im s) + &3))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
        SUBGOAL_THEN `norm(s:complex) / Re s <= &1 + &2 * abs(Im s)`
        MP_TAC THENL
         [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 / &2 <= x ==> &0 < x`]
          THEN MP_TAC(SPEC `s:complex` COMPLEX_NORM_LE_RE_IM) THEN
          SUBGOAL_THEN `abs(Im s) <= &2 * abs(Im s) * Re s` MP_TAC THENL
           [ONCE_REWRITE_TAC[REAL_ARITH `&2 * a * r = a * (&2 * r)`] THEN
            GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
            MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
            ASM_REAL_ARITH_TAC];
          REAL_ARITH_TAC];
        ONCE_REWRITE_TAC[REAL_ARITH `d * (&2 * x) = &2 * d * x:real`] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 * &N) * (exp(&1) * inv(&N))` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
      ONCE_REWRITE_TAC[REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &2 + x:real`) THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[NORM_POS_LE] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < &N` THEN
      CONV_TAC REAL_FIELD];
    SUBGOAL_THEN `exp(&1) * (&1 + log(&N)) <= &4 * (&1 + log(&N))`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_EXP_1_LE_4] THEN
      ASM_REAL_ARITH_TAC;
      MP_TAC REAL_EXP_1_LE_4 THEN ASM_REAL_ARITH_TAC]]);;

let LOG_16_GE_2 = prove
 (`&2 <= log(&16)`,
  SUBGOAL_THEN `log(&16) = &4 * log(&2)` SUBST1_TAC THENL
   [SIMP_TAC[GSYM LOG_POW; REAL_ARITH `&0 < &2`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    MP_TAC LOG_2_BOUNDS THEN REAL_ARITH_TAC]);;

let LFUN_DERIV_BOUND = prove
 (`!d c s N. dirichlet_character d c /\ ~(c = chi_0 d) /\ 16 <= N /\
             &d * (abs(Im s) + &4) <= &N /\
             &1 - inv(&2 * log(&N)) <= Re s
             ==> norm(complex_derivative (dseries c) s)
                 <= &24 * (&1 + log(&N)) pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&2 <= log(&N)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&16)` THEN
    REWRITE_TAC[LOG_16_GE_2] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `r = inv(&2 * log(&N))` THEN
  SUBGOAL_THEN `&0 < r /\ r <= &1 / &4` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM REAL_INV_DIV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(log(&N)) = &2 * r` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN REWRITE_TAC[REAL_INV_MUL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(s,r) SUBSET {z | Re z > &0}` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL; IN_ELIM_THM; real_gt] THEN
    X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    MP_TAC(SPEC `s - z:complex` COMPLEX_NORM_GE_RE_IM) THEN
    UNDISCH_TAC `dist(s:complex,z) <= r` THEN REWRITE_TAC[dist; RE_SUB] THEN
    SUBGOAL_THEN `inv(&2 * log(&N)) <= &1 / &4` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`dseries c`; `s:complex`; `r:real`;
                 `&12 * (&1 + log(&N))`; `1`] CAUCHY_INEQUALITY) THEN
  REWRITE_TAC[HIGHER_COMPLEX_DERIVATIVE_1; NUM_FACT_CONV `FACT 1`;
              REAL_MUL_LID; REAL_POW_1] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_ON_IMP_CONTINUOUS_ON THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
      EXISTS_TAC `{z | Re z > &0}` THEN ASM_MESON_TAC[HOLOMORPHIC_LFUN];
      MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
      EXISTS_TAC `{z | Re z > &0}` THEN
      ASM_MESON_TAC[HOLOMORPHIC_LFUN; BALL_SUBSET_CBALL; SUBSET_TRANS];
      X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
      MATCH_MP_TAC LFUN_BOUND THEN EXISTS_TAC `d:num` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `s - z:complex` COMPLEX_NORM_GE_RE_IM) THEN
      REWRITE_TAC[RE_SUB; IM_SUB] THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `&d * (abs(Im s) + &4)` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z:real`) THEN
  EXPAND_TAC "r" THEN REWRITE_TAC[real_div; REAL_INV_INV] THEN
  REWRITE_TAC[REAL_POW_2] THEN
  REWRITE_TAC[REAL_ARITH `(&12 * a) * &2 * l = &24 * a * l:real`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The 3-4-1 inequality.                                                     *)
(* ------------------------------------------------------------------------- *)

let TRIG_341_LEMMA = prove
 (`!z. norm z <= &1 ==> &0 <= Re(Cx(&3) + Cx(&4) * z + z pow 2)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[COMPLEX_POW_2; RE_ADD; RE_MUL_CX; RE_CX] THEN
  REWRITE_TAC[complex_mul; RE] THEN
  SUBGOAL_THEN `Re z pow 2 + Im z pow 2 <= &1` MP_TAC THENL
   [REWRITE_TAC[GSYM COMPLEX_SQNORM] THEN
    MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  MP_TAC(SPEC `Re z + &1` REAL_LE_SQUARE) THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

let TERM_341 = prove
 (`!w a n x t. &0 <= w /\ norm a <= &1 /\ 1 <= n
     ==> &0 <= Re(Cx(&3) * (Cx w * Cx(&1)) / Cx(&n) cpow Cx x +
                 Cx(&4) * (Cx w * a) / Cx(&n) cpow (Cx x + ii * Cx t) +
                 (Cx w * a pow 2) / Cx(&n) cpow (Cx x + Cx(&2) * ii * Cx t))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `Cx(&n) cpow (Cx x + ii * Cx t) =
    Cx(&n) cpow Cx x * Cx(&n) cpow (ii * Cx t) /\
    Cx(&n) cpow (Cx x + Cx(&2) * ii * Cx t) =
    Cx(&n) cpow Cx x * Cx(&n) cpow (ii * Cx t) * Cx(&n) cpow (ii * Cx t)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM CPOW_ADD] THEN AP_TERM_TAC THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  ABBREV_TAC `u = Cx(&n) cpow (ii * Cx t)` THEN
  SUBGOAL_THEN `Cx(&n) cpow Cx x = Cx(exp(x * log(&n)))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CPOW_REAL_REAL; REAL_CX; RE_CX]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(u:complex) = &1` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN ASM_SIMP_TAC[NORM_CPOW_NUM] THEN
    REWRITE_TAC[RE_MUL_II; IM_CX; REAL_NEG_0; RPOW_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(u = Cx(&0))` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `norm(Cx(&0)) = &1` THEN
    REWRITE_TAC[COMPLEX_NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `P = exp(x * log(&n))` THEN
  SUBGOAL_THEN `&0 < P` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `Cx(&3) * (Cx w * Cx(&1)) / Cx P +
    Cx(&4) * (Cx w * a) / (Cx P * u) +
    (Cx w * a pow 2) / (Cx P * u * u) =
    Cx(w / P) * (Cx(&3) + Cx(&4) * (a / u) + (a / u) pow 2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[CX_DIV] THEN
    SUBGOAL_THEN `~(Cx P = Cx(&0))` MP_TAC THENL
     [REWRITE_TAC[CX_INJ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `~(u = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[RE_MUL_CX] THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC TRIG_341_LEMMA THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_DIV; REAL_DIV_1]);;

let DSERIES_LOG_SUMS = prove
 (`!a z. (!n. norm(a n) <= &1) /\ &1 < Re z
         ==> ((\n. (Cx(mangoldt n / log(&n)) * a n) / Cx(&n) cpow z) sums
              dseries_log a z) (from 1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dseries_log] THEN
  MATCH_MP_TAC DSERIES_SUMS_ABS THEN
  MAP_EVERY EXISTS_TAC [`&1`; `0`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[real_pow; REAL_MUL_LID; COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE;
   REAL_ABS_POS] THEN
  MP_TAC(SPEC `n:num` MANGOLDT_DIV_LOG_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let THREE_FOUR_ONE = prove
 (`!d c x t. dirichlet_character d c /\ &1 < x
     ==> &1 <= norm(dseries (\n. Cx(&1)) (Cx x)) pow 3 *
                norm(dseries c (Cx x + ii * Cx t)) pow 4 *
                norm(dseries (\n. c n pow 2) (Cx x + Cx(&2) * ii * Cx t))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP DIRICHLET_CHARACTER_DSERIES_HYPS)
    THEN
  SUBGOAL_THEN
   `(!m n. (\n. Cx(&1)) (m * n) = (\n. Cx(&1)) m * (\n. Cx(&1)) n) /\
    (\n. Cx(&1)) 1 = Cx(&1) /\ (!n. norm((\n:num. Cx(&1)) n) <= &1) /\
    (!m n. (\n. (c:num->complex) n pow 2) (m * n) =
           (\n. c n pow 2) m * (\n. c n pow 2) n) /\
    (\n. (c:num->complex) n pow 2) 1 = Cx(&1) /\
    (!n. norm((\n. (c:num->complex) n pow 2) n) <= &1)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_MUL_LID; COMPLEX_NORM_CX; REAL_ABS_NUM;
                    REAL_LE_REFL; COMPLEX_POW_ONE; COMPLEX_POW_MUL;
                    COMPLEX_NORM_POW] THEN
    GEN_TAC THEN MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n:num. Cx(&1)`; `Cx x`] NORM_DSERIES_EXP) THEN
  MP_TAC(ISPECL [`c:num->complex`; `Cx x + ii * Cx t`] NORM_DSERIES_EXP) THEN
  MP_TAC(ISPECL [`\n. (c:num->complex) n pow 2`; `Cx x + Cx(&2) * ii * Cx t`]
    NORM_DSERIES_EXP) THEN
  ASM_REWRITE_TAC[RE_ADD; RE_CX; RE_MUL_II; IM_CX; RE_MUL_CX; IM_MUL_CX;
                  REAL_NEG_0; REAL_ADD_RID; REAL_MUL_RZERO; ETA_AX;
                  COMPLEX_MUL_LID] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[GSYM REAL_EXP_N; GSYM REAL_EXP_ADD] THEN
  MATCH_MP_TAC(REAL_ARITH `!y. &1 + y <= z /\ &0 <= y ==> &1 <= z:real`) THEN
  EXISTS_TAC `&3 * Re(dseries_log (\n. Cx(&1)) (Cx x)) +
              &4 * Re(dseries_log c (Cx x + ii * Cx t)) +
              Re(dseries_log (\n. c n pow 2) (Cx x + Cx(&2) * ii * Cx t))` THEN
  REWRITE_TAC[REAL_EXP_LE_X] THEN
  MP_TAC(ISPECL [`\n:num. Cx(&1)`; `Cx x`] DSERIES_LOG_SUMS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[RE_CX]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`c:num->complex`; `Cx x + ii * Cx t`] DSERIES_LOG_SUMS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[RE_ADD; RE_CX; RE_MUL_II; IM_CX; REAL_NEG_0;
                    REAL_ADD_RID];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`\n. (c:num->complex) n pow 2`;
                 `Cx x + Cx(&2) * ii * Cx t`] DSERIES_LOG_SUMS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[RE_ADD; RE_CX; RE_MUL_CX; RE_MUL_II; IM_CX; REAL_NEG_0;
                    REAL_MUL_RZERO; REAL_ADD_RID];
    DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  ABBREV_TAC `A = dseries_log (\n. Cx(&1)) (Cx x)` THEN
  ABBREV_TAC `B = dseries_log c (Cx x + ii * Cx t)` THEN
  ABBREV_TAC
    `C2 = dseries_log (\n. c n pow 2) (Cx x + Cx(&2) * ii * Cx t)` THEN
  SUBGOAL_THEN
   `((\n. Cx(&3) * (Cx(mangoldt n / log(&n)) * Cx(&1)) / Cx(&n) cpow Cx x +
          Cx(&4) * (Cx(mangoldt n / log(&n)) * c n) /
                   Cx(&n) cpow (Cx x + ii * Cx t) +
          (Cx(mangoldt n / log(&n)) * c n pow 2) /
          Cx(&n) cpow (Cx x + Cx(&2) * ii * Cx t)) sums
     (Cx(&3) * A + Cx(&4) * B + C2)) (from 1)`
  MP_TAC THENL
   [MATCH_MP_TAC SERIES_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC SERIES_COMPLEX_LMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SERIES_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC SERIES_COMPLEX_LMUL THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_SUMS_RE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] REAL_SERIES_POS)) THEN
  REWRITE_TAC[RE_ADD; RE_MUL_CX; o_DEF; IN_FROM] THEN
  DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[RE_ADD; RE_MUL_CX] TERM_341) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `n:num` MANGOLDT_DIV_LOG_BOUNDS) THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* zeta and the principal character on Re s > 1.                             *)
(* ------------------------------------------------------------------------- *)

let DSERIES_ZETA = prove
 (`!s. &1 < Re s ==> dseries (\n. Cx(&1)) s = zeta s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dseries] THEN
  MATCH_MP_TAC INFSUM_UNIQUE THEN ASM_SIMP_TAC[ZETA_CONVERGES]);;

let ZETA_REAL_BOUND = prove
 (`!x. &1 < x ==> norm(zeta(Cx x)) <= x / (x - &1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zeta] THEN
  MP_TAC(SPECL [`1`; `Cx x`] GENZETA_BOUND) THEN
  ASM_REWRITE_TAC[RE_CX; ARITH; LOG_1; REAL_MUL_RZERO; REAL_EXP_0] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> x <= a ==> x <= b:real`) THEN
  UNDISCH_TAC `&1 < x` THEN CONV_TAC REAL_FIELD);;

let ZETA_LINE_BOUND = prove
 (`!s N. &1 < Re s /\ 1 <= N /\ norm s <= &N /\ ~(Im s = &0)
         ==> norm(zeta s) <= &3 + log(&N) + inv(abs(Im s))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `zeta s = vsum(1..N) (\k. Cx(&1) / Cx(&k) cpow s) +
                         genzeta (N + 1) s` SUBST1_TAC THENL
   [MP_TAC(SPECL [`1`; `N:num`; `s:complex`] GENZETA_OFFSET) THEN
    ASM_REWRITE_TAC[zeta] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH
   `!x y:complex a b e. norm x <= a /\ norm y <= b /\ a + b <= e
                        ==> norm(x + y) <= e`) THEN
  EXISTS_TAC `&1 + log(&N)` THEN EXISTS_TAC `&2 + inv(abs(Im s))` THEN
  REWRITE_TAC[CONJ_ASSOC] THEN
  CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..N) (\k. inv(&k))` THEN
    ASM_SIMP_TAC[HARMONIC_LE_LOG] THEN
    MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[NORM_DIV_CPOW_NUM; COMPLEX_NORM_CX; REAL_ABS_NUM;
                 REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&k rpow (-- &1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[RPOW_NEG; RPOW_POW; REAL_POW_1; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(s = Cx(&1))` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~(Im(Cx(&1)) = &0)` THEN
    REWRITE_TAC[IM_CX];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[genzeta] THEN
  SUBGOAL_THEN `abs(Im s) <= norm(s - Cx(&1))` ASSUME_TAC THENL
   [MP_TAC(SPEC `s - Cx(&1)` COMPLEX_NORM_GE_RE_IM) THEN
    REWRITE_TAC[IM_SUB; IM_CX; REAL_SUB_RZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < abs(Im s)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(s - Cx(&1))` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_FIELD `(a + b) / c = a / c + b / c:complex`] THEN
  MATCH_MP_TAC(NORM_ARITH
   `!x y:complex a b. norm x <= a /\ norm y <= b ==> norm(x + y) <= a + b`)
     THEN
  ASM_SIMP_TAC[COMPLEX_NORM_DIV] THEN
  SUBGOAL_THEN `&0 < &(N + 1)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    MP_TAC(SPECL [`N + 1`; `s:complex`] NEARZETA_BOUND_SHARP) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ARITH_TAC; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z:real`) THEN
    REWRITE_TAC[COMPLEX_NORM_MUL] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(a * b) * c / d = (a * c / d) * b:real`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    SUBGOAL_THEN `&(N + 1) <= exp(Re s * log(&(N + 1)))` ASSUME_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM(MATCH_MP EXP_LOG
        (ASSUME `&0 < &(N + 1)`))] THEN
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 / &(N + 1) + &1 / Re s <= &2` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `a <= &1 /\ b <= &1 ==> a + b <= &2:real`) THEN
      CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH `x < &1 ==> x <= &1:real`) THENL
       [SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH_RULE `0 < N + 1`] THEN
        REWRITE_TAC[REAL_MUL_LID; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&1 < x ==> &0 < x`] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(s:complex) * &2 / &(N + 1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      MATCH_MP_TAC REAL_LE_DIV_BOTH THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_DIV
      THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `norm(s:complex) <= &(N + 1)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_FIELD `&0 < n ==> a * &2 / n = &2 * (a / n)`] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= &1 ==> &2 * x <= &2:real`) THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM real_div] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC REAL_LE_DIV_BOTH THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM COMPLEX_NORM_DIV; NORM_DIV_CPOW_NUM;
               ARITH_RULE `1 <= N + 1`; COMPLEX_NORM_CX; REAL_ABS_NUM;
               REAL_MUL_LID] THEN
  REWRITE_TAC[RE_SUB; RE_CX; RPOW_NEG] THEN
  MATCH_MP_TAC REAL_INV_LE_1 THEN MATCH_MP_TAC RPOW_LE_1 THEN
  REWRITE_TAC[REAL_OF_NUM_LE] THEN CONJ_TAC THENL
   [ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let PRINCIPAL_CONV = prove
 (`!d n. 1 <= n /\ 1 <= d
         ==> vsum {e | e divides n}
               (\e. (if e divides d then Cx(mobius e) else Cx(&0)) * Cx(&1)) =
             chi_0 d n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[chi_0; COMPLEX_MUL_RID] THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
  ASM_SIMP_TAC[GSYM VSUM_RESTRICT_SET; FINITE_DIVISORS] THEN
  REWRITE_TAC[COMPLEX_VEC_0] THEN
  SUBGOAL_THEN `{e | e IN {e | e divides n} /\ e divides d} =
                {e | e divides gcd(n,d)}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; DIVIDES_GCD]; ALL_TAC] THEN
  REWRITE_TAC[VSUM_CX] THEN
  SUBGOAL_THEN `1 <= gcd(n,d)` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; GCD_ZERO] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REWRITE_RULE[ETA_AX] DIVISORSUM_MOBIUS; COPRIME_GCD] THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

let DSERIES_DIVISOR_SUPPORT_BOUND = prove
 (`!a d s. 1 <= d /\ &1 <= Re s /\ (!e. norm(a e) <= &1) /\
           (!e. ~(e divides d) ==> a e = Cx(&0)) /\ &1 < Re s
           ==> norm(dseries a s) <= &1 + log(&d)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:num->complex`; `&1`; `0`;
   `s:complex`] DSERIES_SUMS_ABS) THEN
  ASM_REWRITE_TAC[real_pow; REAL_MUL_LID; sums; FROM_INTER_NUMSEG] THEN
  DISCH_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
  EXISTS_TAC `\N. vsum(1..N) (\n. (a:num->complex) n / Cx(&n) cpow s)` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `0` THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..N) (\e. if e <= d then inv(&e) else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `e:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(e:num) divides d` THENL
     [SUBGOAL_THEN `e <= d:num` ASSUME_TAC THENL
       [MP_TAC(SPECL [`e:num`; `d:num`] DIVIDES_LE) THEN
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[NORM_DIV_CPOW_NUM] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * &e rpow (-- &1)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN
        ASM_SIMP_TAC[NORM_POS_LE; RPOW_POS_LE; REAL_POS] THEN
        MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_MUL_LID; RPOW_NEG; RPOW_POW; REAL_POW_1;
                    REAL_LE_REFL]];
      ASM_SIMP_TAC[complex_div; COMPLEX_MUL_LZERO; COMPLEX_NORM_0] THEN
      COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL; REAL_LE_INV_EQ; REAL_POS]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..d) (\e. inv(&e))` THEN
  ASM_SIMP_TAC[HARMONIC_LE_LOG] THEN
  ASM_CASES_TAC `N <= d:num` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..N) (\e. inv(&e))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL; REAL_LE_INV_EQ; REAL_POS];
      MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; REAL_LE_INV_EQ; REAL_POS]
      THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `d <= N:num` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` SUBST1_TAC o
    GEN_REWRITE_RULE I [LE_EXISTS]) THEN
  SIMP_TAC[SUM_ADD_SPLIT; ARITH_RULE `1 <= d + 1`] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y /\ z = &0 ==> x + z <= y:real`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[];
    MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let PRINCIPAL_LFUN_BOUND = prove
 (`!d s. 1 <= d /\ &1 < Re s
         ==> norm(dseries (chi_0 d) s) <= (&1 + log(&d)) * norm(zeta s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\e. if e divides d then Cx(mobius e) else Cx(&0)`;
                 `\n:num. Cx(&1)`; `&1`; `&1`; `0`; `s:complex`]
    DSERIES_MUL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[real_pow; REAL_MUL_LID; COMPLEX_NORM_CX; REAL_ABS_NUM;
                    REAL_LE_REFL] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_MOBIUS; REAL_ABS_NUM; REAL_POS];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `dseries (\n. vsum {e | e divides n}
                   (\e. (if e divides d then Cx(mobius e) else Cx(&0)) *
                        Cx(&1))) s = dseries (chi_0 d) s`
  SUBST1_TAC THENL
   [MATCH_MP_TAC DSERIES_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PRINCIPAL_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[DSERIES_ZETA; COMPLEX_NORM_MUL] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  MATCH_MP_TAC DSERIES_DIVISOR_SUPPORT_BOUND THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REPEAT CONJ_TAC THEN GEN_TAC THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_MOBIUS; REAL_ABS_NUM; REAL_POS]);;

(* ------------------------------------------------------------------------- *)
(* A lower bound for |L| near the line Re s = 1.                             *)
(* ------------------------------------------------------------------------- *)

let LFUN_LOWER_RIGHT = prove
 (`!d c t M2 y.
     dirichlet_character d c /\ &1 < y /\ y <= &2 /\
     norm(dseries (\n. c n pow 2) (Cx y + Cx(&2) * ii * Cx t)) <= M2
     ==> (y - &1) pow 3 <= &8 * M2 * norm(dseries c (Cx y + ii * Cx t)) pow 4`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`; `y:real`; `t:real`]
    THREE_FOUR_ONE) THEN
  ASM_SIMP_TAC[DSERIES_ZETA; RE_CX] THEN
  ABBREV_TAC `Z = norm(zeta(Cx y))` THEN
  ABBREV_TAC `B = norm(dseries c (Cx y + ii * Cx t))` THEN
  ABBREV_TAC `C = norm(dseries (\n. c n pow 2) (Cx y + Cx(&2) * ii * Cx t))`
    THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (Z:real) /\ &0 <= (B:real) /\ &0 <= (C:real)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Z"; "B"; "C"] THEN REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < y - &1:real` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `Z <= &2 / (y - &1):real` ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `y / (y - &1):real` THEN ASM_SIMP_TAC[ZETA_REAL_BOUND] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= (&2 / (y - &1):real) pow 3 * B pow 4 * M2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(Z:real) pow 3 * B pow 4 * C` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LE];
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_LE]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_DIV] THEN
  ASM_SIMP_TAC[REAL_POW_LT; REAL_FIELD
   `&0 < a ==> (b / a) * c = (b * c) / a`] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT; REAL_MUL_LID] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let LFUN_LOWER_ABSTRACT = prove
 (`!d c t M1 M2 x.
     dirichlet_character d c /\ ~(c = chi_0 d) /\ &1 <= M1 /\ &1 <= M2 /\
     (!y. &1 < y /\ y <= &2
          ==> norm(dseries (\n. c n pow 2) (Cx y + Cx(&2) * ii * Cx t))
              <= M2) /\
     (!z. Im z = t /\ &1 - inv(&2048 * M1 pow 4 * M2) <= Re z /\ Re z <= &2
          ==> norm(complex_derivative (dseries c) z) <= M1) /\
     &1 - inv(&2048 * M1 pow 4 * M2) <= x /\ x <= &2
     ==> &2 * inv(&2048 * M1 pow 4 * M2) * M1
         <= norm(dseries c (Cx x + ii * Cx t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `e = inv(&2048 * M1 pow 4 * M2)` THEN
  SUBGOAL_THEN `&0 < e /\ e <= &1 / &2048 /\ &2048 * e * M1 pow 4 * M2 = &1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN
    SUBGOAL_THEN `&1 <= M1 pow 4` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&1 <= &2048 * M1 pow 4 * M2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2048 * &1 * &1` THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC]
      THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[GSYM REAL_INV_DIV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2048 * &1 * &1` THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC]
      THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `a * i * b * c = i * (a * b * c):real`] THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. &1 + e <= y /\ y <= &2
        ==> &4 * e * M1 <= norm(dseries c (Cx y + ii * Cx t))`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `4` THEN
    REWRITE_TAC[NORM_POS_LE; ARITH] THEN
    MP_TAC(SPECL [`d:num`; `c:num->complex`; `t:real`; `M2:real`; `y:real`]
      LFUN_LOWER_RIGHT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `e pow 3 <= (y - &1) pow 3` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `B = norm(dseries c (Cx y + ii * Cx t))` THEN
    SUBGOAL_THEN `(&4 * e * M1) pow 4 * (&8 * M2) = e pow 3` ASSUME_TAC THENL
     [UNDISCH_TAC `&2048 * e * M1 pow 4 * M2 = &1` THEN
      CONV_TAC REAL_RING;
      ALL_TAC] THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `&0 < &8 * M2` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&4 * e * M1) pow 4 * (&8 * M2) <= B pow 4 * (&8 * M2)`
    MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ];
    ALL_TAC] THEN
  ASM_CASES_TAC `&1 + e <= x` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 * e * M1` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&1 + e`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`dseries c`; `complex_derivative (dseries c)`;
                 `segment[Cx x + ii * Cx t,Cx(&1 + e) + ii * Cx t]`; `M1:real`]
    COMPLEX_DIFFERENTIABLE_BOUND) THEN
  REWRITE_TAC[CONVEX_SEGMENT] THEN ANTS_TAC THENL
   [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `Im z = t /\ x <= Re z /\ Re z <= &1 + e` STRIP_ASSUME_TAC
    THENL
     [UNDISCH_TAC `z IN segment[Cx x + ii * Cx t,Cx(&1 + e) + ii * Cx t]` THEN
      REWRITE_TAC[IN_SEGMENT] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[RE_ADD; IM_ADD; RE_CMUL; IM_CMUL; RE_CX; IM_CX;
                  RE_MUL_II; IM_MUL_II] THEN
      MP_TAC(SPECL [`u:real`; `(&1 + e) - x`] REAL_LE_MUL) THEN
      MP_TAC(SPECL [`&1 - u`; `(&1 + e) - x`] REAL_LE_MUL) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_AT_WITHIN THEN
      REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT THEN
      EXISTS_TAC `{z | Re z > &0}` THEN
      REWRITE_TAC[OPEN_HALFSPACE_RE_GT; IN_ELIM_THM] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[HOLOMORPHIC_LFUN]; ASM_REAL_ARITH_TAC];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`Cx x + ii * Cx t`;
   `Cx(&1 + e) + ii * Cx t`]) THEN
  REWRITE_TAC[ENDS_IN_SEGMENT] THEN
  REWRITE_TAC[COMPLEX_RING `(a + b) - (c + b):complex = a - c`] THEN
  REWRITE_TAC[GSYM CX_SUB; COMPLEX_NORM_CX] THEN
  SUBGOAL_THEN `abs(x - (&1 + e)) <= &2 * e` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `L0 = norm(dseries c (Cx(&1 + e) + ii * Cx t))` THEN
  SUBGOAL_THEN `&0 <= M1` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `M1 * abs(x - (&1 + e)) <= M1 * (&2 * e)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC(NORM_ARITH
   `!a b:complex p q. norm(a - b) <= p /\ &4 * q <= norm b /\ p <= &2 * q
                      ==> &2 * q <= norm a`) THEN
  MAP_EVERY EXISTS_TAC [`dseries c (Cx(&1 + e) + ii * Cx t)`;
                        `M1 * abs(x - (&1 + e))`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `M1 * abs(x - (&1 + e)) <= M1 * (&2 * e)` THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Real characters: L(x) > 0 for real x >= 1.                                *)
(* ------------------------------------------------------------------------- *)

let SUMS_REAL = prove
 (`!f l s. (f sums l) s /\ (!n. n IN s ==> real(f n)) ==> real l`,
  REWRITE_TAC[sums] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LIM_SEQUENTIALLY THEN
  EXISTS_TAC `\n. vsum(s INTER (0..n)) f :complex` THEN
  ASM_SIMP_TAC[REAL_VSUM; FINITE_INTER; FINITE_NUMSEG; IN_INTER]);;

let DIRICHLET_CHARACTER_MUL_MOD = prove
 (`!q1 q2 c1 c2. dirichlet_character q1 c1 /\ dirichlet_character q2 c2
                 ==> dirichlet_character (q1 * q2) (\n. c1 n * c2 n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dirichlet_character] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
    BINOP_TAC THENL [ONCE_REWRITE_TAC[MULT_SYM]; ALL_TAC] THEN
    ASM_MESON_TAC[DIRICHLET_CHARACTER_PERIODIC_GEN];
    X_GEN_TAC `n:num` THEN REWRITE_TAC[COMPLEX_ENTIRE; COPRIME_RMUL] THEN
    ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_0];
    REPEAT GEN_TAC THEN
    FIRST_X_ASSUM(fun th ->
      REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_MUL th]) THEN
    FIRST_X_ASSUM(fun th ->
      REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_MUL th]) THEN
    CONV_TAC COMPLEX_RING]);;

let DSERIES_TERM_REAL = prove
 (`!a n x. real a ==> real(a / Cx(&n) cpow Cx x)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[cpow; complex_div; COMPLEX_INV_0; COMPLEX_MUL_RZERO;
                    REAL_CX];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_DIV THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[CPOW_REAL_REAL; REAL_CX; RE_CX]);;

let DSERIES_REAL = prove
 (`!a B k x. (!n. 1 <= n ==> norm(a n) <= B * (&1 + log(&n)) pow k) /\
             (!n. 1 <= n ==> real(a n)) /\ &1 < x
             ==> real(dseries a (Cx x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUMS_REAL THEN
  EXISTS_TAC `\n. (a:num->complex) n / Cx(&n) cpow Cx x` THEN
  EXISTS_TAC `from 1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC DSERIES_SUMS_ABS THEN
    MAP_EVERY EXISTS_TAC [`B:real`; `k:num`] THEN ASM_REWRITE_TAC[RE_CX];
    REWRITE_TAC[IN_FROM] THEN ASM_SIMP_TAC[DSERIES_TERM_REAL]]);;

let DSERIES_REAL_BOUNDED = prove
 (`!a Q x. (!n. norm(vsum(1..n) a) <= Q) /\ (!n. real(a n)) /\ &0 < x
           ==> real(dseries a (Cx x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUMS_REAL THEN
  EXISTS_TAC `\n. (a:num->complex) n / Cx(&n) cpow Cx x` THEN
  EXISTS_TAC `from 1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC DSERIES_SUMS THEN EXISTS_TAC `Q:real` THEN
    ASM_REWRITE_TAC[RE_CX];
    ASM_SIMP_TAC[DSERIES_TERM_REAL]]);;

let CEXP_REAL_POS = prove
 (`!z. real z ==> real(cexp z) /\ &0 < Re(cexp z)`,
  GEN_TAC THEN REWRITE_TAC[REAL] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM CX_EXP; REAL_CX; RE_CX; REAL_EXP_POS_LT]);;

let LFUN_REAL_GT1 = prove
 (`!d c x. dirichlet_character d c /\ (!n. real(c n)) /\ &1 < x
           ==> real(dseries c (Cx x)) /\ &0 < Re(dseries c (Cx x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP DIRICHLET_CHARACTER_DSERIES_HYPS)
    THEN
  MP_TAC(ISPECL [`c:num->complex`; `Cx x`] DSERIES_EXP) THEN
  ASM_REWRITE_TAC[RE_CX] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC CEXP_REAL_POS THEN REWRITE_TAC[dseries_log] THEN
  MATCH_MP_TAC DSERIES_REAL THEN
  MAP_EVERY EXISTS_TAC [`&1`; `0`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THENL
   [REWRITE_TAC[real_pow; REAL_MUL_RID; COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    MP_TAC(SPEC `n:num` MANGOLDT_DIV_LOG_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * &1` THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
    ASM_SIMP_TAC[REAL_MUL; REAL_CX]]);;

let RIGHT_LIMIT_AT_1 = prove
 (`!f. f continuous at (Cx(&1)) /\
       (!x. &1 < x ==> real(f(Cx x)) /\ &0 <= Re(f(Cx x)))
       ==> real(f(Cx(&1))) /\ &0 <= Re(f(Cx(&1)))`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((\n. (f:complex->complex)(Cx(&1 + inv(&n + &1)))) --> f(Cx(&1)))
    sequentially`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o
      GEN_REWRITE_RULE I [CONTINUOUS_AT_SEQUENTIALLY]) THEN
    DISCH_THEN(MP_TAC o SPEC `\n. Cx(&1 + inv(&n + &1))`) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[CX_ADD; CX_INV] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM COMPLEX_ADD_RID] THEN
    MATCH_MP_TAC LIM_ADD THEN REWRITE_TAC[LIM_CONST] THEN
    REWRITE_TAC[LIM_INV_N_OFFSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. &1 < &1 + inv(&n + &1)` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_LT_ADDR; REAL_LT_INV_EQ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LIM_SEQUENTIALLY THEN
    EXISTS_TAC `\n. (f:complex->complex)(Cx(&1 + inv(&n + &1)))` THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC(ISPEC `sequentially` LIM_RE_LBOUND) THEN
    EXISTS_TAC `\n. (f:complex->complex)(Cx(&1 + inv(&n + &1)))` THEN
    ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_TRUE]]);;

let CPOW_ONE_RIGHT = prove
 (`!z. z cpow Cx(&1) = z`,
  GEN_TAC THEN REWRITE_TAC[CPOW_N; COMPLEX_POW_1] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let DSERIES_AT_1 = prove
 (`!c. dseries c (Cx(&1)) = Lfunction c`,
  REWRITE_TAC[dseries; Lfunction_DEF; CPOW_ONE_RIGHT]);;

let LFUN_CONTINUOUS_AT = prove
 (`!d c s. dirichlet_character d c /\ ~(c = chi_0 d) /\ &0 < Re s
           ==> (dseries c) continuous at s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT THEN
  EXISTS_TAC `{s | Re s > &0}` THEN
  REWRITE_TAC[OPEN_HALFSPACE_RE_GT; IN_ELIM_THM] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[HOLOMORPHIC_LFUN]; ASM_REWRITE_TAC[real_gt]]);;

let LFUN_1_POS = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d) /\ (!n. real(c n))
         ==> real(dseries c (Cx(&1))) /\ &0 < Re(dseries c (Cx(&1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `dseries c` RIGHT_LIMIT_AT_1) THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LFUN_CONTINUOUS_AT THEN EXISTS_TAC `d:num` THEN
      ASM_REWRITE_TAC[RE_CX] THEN REAL_ARITH_TAC;
      ASM_MESON_TAC[LFUN_REAL_GT1; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REAL_LT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`] LFUNCTION_NONZERO_NONPRINCIPAL) THEN
  ASM_REWRITE_TAC[GSYM DSERIES_AT_1] THEN ASM_MESON_TAC[REAL]);;
