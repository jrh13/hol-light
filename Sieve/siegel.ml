(* ========================================================================= *)
(* Siegel's theorem.                                                         *)
(*                                                                           *)
(* SIEGEL: for every e > 0 there is kap > 0 such that L(1,c) >= kap q^-e     *)
(* for every real nonprincipal character c mod q, stated as                  *)
(*   kap * exp(--(e * log(&q))) <= Re(dseries c (Cx(&1))).                   *)
(*                                                                           *)
(* Method (Estermann; [Davenport, ch. 21], without primitive characters).    *)
(* For real nonprincipal c1 mod q1, c2 mod q2 with c1 c2 nonprincipal let    *)
(* F = zeta L1 L2 L12 (L12 = L(s,c1 c2)) and lambda = L1(1) L2(1) L12(1).    *)
(*  * F = cexp(H) on Re s > 1, where H has the coefficients                  *)
(*    (Lambda(n) / log n) (1 + c1(n)) (1 + c2(n)) in [0,4] (SIEGEL_EXP,      *)
(*    SIEGEL_COEFF), so (-1)^m F^(m)(x) >= 0 for x > 1                       *)
(*    (CEXP_DSERIES_HIGHER_NONNEG: Leibniz rule and induction).              *)
(*  * P(s) = (nearzeta 1 s + 1) L1 L2 L12 = (s - 1) F(s) is holomorphic on   *)
(*    Re s > 0 (SIEGEL_P_HOLOMORPHIC), and g = (P(s) - P(1)) / (s - 1) =     *)
(*    F - lambda / (s - 1) is bounded by 2^17 (q1 q2)^2 on |s - 2| = 3/2.    *)
(*    The Taylor series of g at 2 (HOLOMORPHIC_POWER_SERIES) with Cauchy's   *)
(*    inequality gives, for 7/8 <= x < 1 and M >= 1 (ESTERMANN_ABSTRACT,     *)
(*    SIEGEL_F_LOWER),                                                       *)
(*      F(x) >= 1 - lambda (2 - x)^M / (1 - x) - 2^19 (q1 q2)^2 (3/4)^M.     *)
(*  * Hence F(b) <= 0 for some 7/8 <= b < 1 forces                           *)
(*      lambda >= (1 - b) (q1 q2)^(-8 (1 - b)) / 4096 (SIEGEL_LAMBDA_LOWER). *)
(*  * SIEGEL_FIXED: if c1 is fixed and F(b) <= 0 for all such c2, with       *)
(*    16 (1 - b) <= e, then L(1,c2) >> q2^-e (L(1,c1), L(1,c1 c2) <=         *)
(*    12 (1 + log 3d) by LFUN_1_UPPER).  When c1 c2 is principal, c2 = c1    *)
(*    at the primes not dividing q1 q2 and LFUN_1_PRINCIPAL_PRODUCT gives    *)
(*    L(1,c2) >= exp(-2 sum_{p | q1 q2} 1/(p - 1)) L(1,c1), where            *)
(*    sum_{p | m} 1/(p - 1) <= C(e) + e log m (PRIME_DIVISOR_RECIP_BOUND).   *)
(*  * SIEGEL: either some real nonprincipal c1 has a zero b in               *)
(*    [1 - eta, 1), and F(b) = 0 for every c2; or none has, and then         *)
(*    F(1 - eta) <= 0 for every c2 (SIEGEL_F_NONPOS: zeta < 0 just left of   *)
(*    1 by NEARZETA_NEAR_1, and the L-values are positive by the             *)
(*    intermediate value theorem, LFUN_POS_LEFT).                            *)
(* ========================================================================= *)

needs "Sieve/lfun.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Real characters near s = 1.                                               *)
(* ------------------------------------------------------------------------- *)

let RE_CONTINUOUS_ON_REAL = prove
 (`!f s. (!x. x IN s ==> f continuous at (Cx x))
         ==> (\x. Re(f(Cx x))) real_continuous_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_continuous_on] THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN
  ASM_REWRITE_TAC[continuous_at] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `Cx y`) THEN
  ASM_REWRITE_TAC[dist; GSYM CX_SUB; COMPLEX_NORM_CX] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> b < e ==> a < e`) THEN
  REWRITE_TAC[GSYM RE_SUB] THEN MESON_TAC[COMPLEX_NORM_GE_RE_IM]);;

let LFUN_POS_LEFT = prove
 (`!d c b. dirichlet_character d c /\ ~(c = chi_0 d) /\ (!n. real(c n)) /\
           &0 < b /\ b <= &1 /\
           (!x. b <= x /\ x < &1 ==> ~(dseries c (Cx x) = Cx(&0)))
           ==> &0 < Re(dseries c (Cx b))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`] LFUN_1_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. Re(dseries c (Cx x))`; `b:real`; `&1`; `&0`]
    REAL_IVT_INCREASING) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC RE_CONTINUOUS_ON_REAL THEN
    REWRITE_TAC[IN_REAL_INTERVAL; ETA_AX] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC LFUN_CONTINUOUS_AT THEN EXISTS_TAC `d:num` THEN
    ASM_REWRITE_TAC[RE_CX] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `x = &1` THENL
   [UNDISCH_TAC `Re(dseries c (Cx x)) = &0` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `real(dseries c (Cx x))` MP_TAC THENL
   [MATCH_MP_TAC DSERIES_REAL_BOUNDED THEN EXISTS_TAC `&d` THEN
    ASM_SIMP_TAC[NONPRINCIPAL_PARTIAL_SUM_BOUND] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[]);;

let RPOW_NUM_NEG_LE_1 = prove
 (`!n x. 1 <= n /\ &0 <= x ==> &n rpow (--x) <= &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`1`; `n:num`; `x:real`] RPOW_NUM_MONO) THEN
  ASM_REWRITE_TAC[LE_REFL; RPOW_ONE]);;

let LFUN_CRUDE_BOUND = prove
 (`!d c s. dirichlet_character d c /\ ~(c = chi_0 d) /\
           &1 / &2 <= Re s /\ norm s <= &4
           ==> norm(dseries c s) <= &11 * &d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`]
    DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= d` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Re s` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:num->complex`; `s:complex`; `&d`; `d:num`]
    DSERIES_TAIL) THEN
  ASM_SIMP_TAC[NONPRINCIPAL_PARTIAL_SUM_BOUND] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&d rpow (--Re s) <= &1 /\ &0 <= &d rpow (--Re s)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RPOW_NUM_NEG_LE_1; RPOW_NUM_POS; REAL_LT_IMP_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(s:complex) / Re s <= &8 /\ &0 <= norm(s:complex) / Re s`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 / &2 <= x ==> &0 < x`;
                 REAL_LE_DIV; NORM_POS_LE;
                 REAL_ARITH `&1 / &2 <= x ==> &0 <= x`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&d * (&2 + norm(s:complex) / Re s) * &d rpow (--Re s) <= &d * &10 * &1`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(vsum(1..d) (\n. c n / Cx(&n) cpow s)) <= &d`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..d) (\n. &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `n:num` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[NORM_DIV_CPOW_NUM] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * &1` THEN
      CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[NORM_POS_LE; RPOW_NUM_POS; REAL_LT_IMP_LE;
                   RPOW_NUM_NEG_LE_1;
                    REAL_ARITH `&1 / &2 <= x ==> &0 <= x`] THEN
      ASM_MESON_TAC[DIRICHLET_CHARACTER_NORM_LE];
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_MUL_RID; REAL_LE_REFL]];
    ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH
   `!l v:complex a b. norm(l - v) <= a /\ a <= b * &10 * &1 /\ norm v <= b
                      ==> norm l <= &11 * b`) THEN
  EXISTS_TAC `vsum(1..d) (\n. c n / Cx(&n) cpow s)` THEN
  EXISTS_TAC `&d * (&2 + norm(s:complex) / Re s) * &d rpow (--Re s)` THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* zeta L1 L2 L12 as an exponential with nonnegative coefficients.           *)
(* ------------------------------------------------------------------------- *)

let SIEGEL_EXP = prove
 (`!q1 q2 c1 c2 s.
     dirichlet_character q1 c1 /\ dirichlet_character q2 c2 /\ &1 < Re s
     ==> zeta s * dseries c1 s * dseries c2 s *
         dseries (\n. c1 n * c2 n) s =
         cexp(dseries (\n. Cx(mangoldt n / log(&n)) *
                           (Cx(&1) + c1 n) * (Cx(&1) + c2 n)) s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`q1:num`; `q2:num`; `c1:num->complex`; `c2:num->complex`]
    DIRICHLET_CHARACTER_MUL_MOD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(!n. norm((c1:num->complex) n) <= &1) /\
    (!n. norm((c2:num->complex) n) <= &1) /\
    (!n. norm((c1:num->complex) n * c2 n) <= &1)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[DIRICHLET_CHARACTER_NORM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `dseries (\n. Cx(&1)) s = cexp(dseries_log (\n. Cx(&1)) s) /\
    dseries c1 s = cexp(dseries_log c1 s) /\
    dseries c2 s = cexp(dseries_log c2 s) /\
    dseries (\n. c1 n * c2 n) s = cexp(dseries_log (\n. c1 n * c2 n) s)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC DSERIES_EXP THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[COMPLEX_MUL_LID; COMPLEX_NORM_CX] THEN REAL_ARITH_TAC;
      ASM_MESON_TAC[DIRICHLET_CHARACTER_DSERIES_HYPS];
      ASM_MESON_TAC[DIRICHLET_CHARACTER_DSERIES_HYPS];
      ASM_MESON_TAC[DIRICHLET_CHARACTER_DSERIES_HYPS]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM DSERIES_ZETA] THEN ASM_REWRITE_TAC[GSYM CEXP_ADD] THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN REWRITE_TAC[dseries] THEN
  MATCH_MP_TAC INFSUM_UNIQUE THEN MATCH_MP_TAC SUMS_EQ THEN
  EXISTS_TAC
   `\n. (Cx(mangoldt n / log(&n)) * Cx(&1)) / Cx(&n) cpow s +
        (Cx(mangoldt n / log(&n)) * c1 n) / Cx(&n) cpow s +
        (Cx(mangoldt n / log(&n)) * c2 n) / Cx(&n) cpow s +
        (Cx(mangoldt n / log(&n)) * c1 n * c2 n) / Cx(&n) cpow s` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_FROM; complex_div] THEN REPEAT STRIP_TAC THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC SERIES_ADD THEN CONJ_TAC) THEN
  MATCH_MP_TAC DSERIES_LOG_SUMS THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM; REAL_LE_REFL]);;

let REAL_CHARACTER_PLUS1 = prove
 (`!d c n. dirichlet_character d c /\ (!n. real(c n))
           ==> Cx(&1) + c n = Cx(&1 + Re(c n)) /\ &0 <= &1 + Re(c n) /\
               &1 + Re(c n) <= &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[CX_ADD] THEN AP_TERM_TAC THEN ASM_MESON_TAC[REAL];
    MP_TAC(ISPEC `(c:num->complex) n` COMPLEX_NORM_GE_RE_IM) THEN
    MP_TAC(SPECL [`d:num`; `c:num->complex`; `n:num`]
      DIRICHLET_CHARACTER_NORM_LE) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let SIEGEL_COEFF = prove
 (`!q1 q2 c1 c2 n.
     dirichlet_character q1 c1 /\ dirichlet_character q2 c2 /\
     (!n. real(c1 n)) /\ (!n. real(c2 n)) /\ 1 <= n
     ==> ?r. &0 <= r /\ r <= &4 /\
             Cx(mangoldt n / log(&n)) * (Cx(&1) + c1 n) * (Cx(&1) + c2 n) =
             Cx r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`q1:num`; `c1:num->complex`; `n:num`]
    REAL_CHARACTER_PLUS1) THEN
  MP_TAC(SPECL [`q2:num`; `c2:num->complex`; `n:num`]
    REAL_CHARACTER_PLUS1) THEN
  MP_TAC(SPEC `n:num` MANGOLDT_DIV_LOG_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `mangoldt n / log(&n) * (&1 + Re(c1 n)) * (&1 + Re(c2 n))` THEN
  REWRITE_TAC[CX_MUL] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * &2 * &2` THEN
  CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]);;

let REAL_NONNEG_MUL = prove
 (`!a b. real a /\ &0 <= Re a /\ real b /\ &0 <= Re b
         ==> real(a * b) /\ &0 <= Re(a * b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `a * b = Cx(Re a * Re b)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[CX_MUL]; ALL_TAC] THEN
  REWRITE_TAC[RE_CX] THEN ASM_SIMP_TAC[REAL_LE_MUL]);;

let NEG_ONE_POW_LOG = prove
 (`!j l. Cx(--(&1)) pow j * (--Cx l) pow j = Cx(l pow j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM COMPLEX_POW_MUL; CX_POW] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[CX_NEG] THEN
  CONV_TAC COMPLEX_RING);;

let DSERIES_HIGHER_NONNEG = prove
 (`!h j x. (!n. 1 <= n ==> ?r. &0 <= r /\ r <= &4 /\ h n = Cx r) /\ &1 < x
           ==> real(Cx(--(&1)) pow j *
                    higher_complex_derivative j (dseries h) (Cx x)) /\
               &0 <= Re(Cx(--(&1)) pow j *
                        higher_complex_derivative j (dseries h) (Cx x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `r:num->real`) ASSUME_TAC) THEN
  SUBGOAL_THEN `!n. 1 <= n ==> norm((h:num->complex) n) <=
                              &4 * (&1 + log(&n)) pow 0`
  ASSUME_TAC THENL
   [REWRITE_TAC[real_pow; REAL_MUL_RID] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[COMPLEX_NORM_CX] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &4 ==> abs x <= &4`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:num->complex`; `&4`; `0`; `j:num`; `Cx x`]
    HIGHER_DSERIES) THEN
  ASM_REWRITE_TAC[RE_CX] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`h:num->complex`; `&4`; `0`; `j:num`]
    HIGHER_DSERIES_COEFF_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\n. (--Cx(log(&n))) pow j * (h:num->complex) n`;
                 `Cx(--(&1)) pow j`; `&4`; `0 + j`; `Cx x`] DSERIES_LMUL) THEN
  ASM_REWRITE_TAC[RE_CX] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC DSERIES_REAL_NONNEG THEN
  MAP_EVERY EXISTS_TAC [`&4`; `0 + j`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW; COMPLEX_NORM_CX] THEN
    REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_NUM; REAL_POW_ONE; REAL_MUL_LID] THEN
    REWRITE_TAC[GSYM COMPLEX_NORM_MUL; GSYM COMPLEX_NORM_POW] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[COMPLEX_MUL_ASSOC; NEG_ONE_POW_LOG; GSYM CX_MUL;
               REAL_CX; RE_CX] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC REAL_POW_LE THEN
  MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]);;

let CEXP_DSERIES_HIGHER_NONNEG = prove
 (`!h x. (!n. 1 <= n ==> ?r. &0 <= r /\ r <= &4 /\ h n = Cx r) /\ &1 < x
         ==> !m. real(Cx(--(&1)) pow m *
                      higher_complex_derivative m (cexp o dseries h) (Cx x)) /\
                 &0 <= Re(Cx(--(&1)) pow m *
                          higher_complex_derivative m (cexp o dseries h)
                            (Cx x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. 1 <= n ==> norm((h:num->complex) n) <=
                              &4 * (&1 + log(&n)) pow 0`
  ASSUME_TAC THENL
   [REWRITE_TAC[real_pow; REAL_MUL_RID] THEN X_GEN_TAC `n:num` THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Cx x IN {s | Re s > &1}` ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; RE_CX; real_gt] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(dseries h) holomorphic_on {s | Re s > &1}` ASSUME_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_DSERIES_ABS THEN
    MAP_EVERY EXISTS_TAC [`&4`; `0`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(complex_derivative (dseries h)) holomorphic_on
                {s | Re s > &1}` ASSUME_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_COMPLEX_DERIVATIVE THEN
    ASM_REWRITE_TAC[OPEN_HALFSPACE_RE_GT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(cexp o dseries h) holomorphic_on {s | Re s > &1}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN
    ASM_REWRITE_TAC[HOLOMORPHIC_ON_CEXP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN {s | Re s > &1}
        ==> complex_derivative (cexp o dseries h) w =
            complex_derivative (dseries h) w * (cexp o dseries h) w`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`dseries (h:num->complex)`; `cexp`; `w:complex`]
      COMPLEX_DERIVATIVE_CHAIN) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT THEN
        EXISTS_TAC `{s | Re s > &1}` THEN
        ASM_REWRITE_TAC[OPEN_HALFSPACE_RE_GT];
        MESON_TAC[HAS_COMPLEX_DERIVATIVE_CEXP; complex_differentiable]];
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(SPEC `dseries h w` HAS_COMPLEX_DERIVATIVE_CEXP) THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP HAS_COMPLEX_DERIVATIVE_DERIVATIVE) THEN
    REWRITE_TAC[o_THM] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `m:num` THEN
  DISCH_THEN(LABEL_TAC "ih") THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `n:num` SUBST_ALL_TAC)
   (SPEC `m:num` num_CASES) THENL
   [REWRITE_TAC[higher_complex_derivative; complex_pow; COMPLEX_MUL_LID;
                o_THM] THEN
    MP_TAC(SPEC `dseries h (Cx x)` CEXP_REAL_POS) THEN ANTS_TAC THENL
     [MATCH_MP_TAC DSERIES_REAL THEN
      MAP_EVERY EXISTS_TAC [`&4`; `0`] THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[REAL_CX];
      SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  REWRITE_TAC[higher_complex_derivative_alt] THEN
  SUBGOAL_THEN
   `higher_complex_derivative n (complex_derivative (cexp o dseries h))
      (Cx x) =
    higher_complex_derivative n
      (\w. complex_derivative (dseries h) w * (cexp o dseries h) w) (Cx x)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC HIGHER_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    EXISTS_TAC `{s | Re s > &1}` THEN
    ASM_REWRITE_TAC[OPEN_HALFSPACE_RE_GT] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_COMPLEX_DERIVATIVE THEN
      ASM_REWRITE_TAC[OPEN_HALFSPACE_RE_GT];
      MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN ASM_REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`complex_derivative (dseries (h:num->complex))`;
                 `cexp o dseries (h:num->complex)`; `{s | Re s > &1}`;
                 `n:num`; `Cx x`] HIGHER_COMPLEX_DERIVATIVE_MUL) THEN
  ASM_REWRITE_TAC[OPEN_HALFSPACE_RE_GT] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM higher_complex_derivative_alt] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  SUBGOAL_THEN
   `!i. i IN 0..n
        ==> real(Cx(--(&1)) pow SUC n *
                 Cx(&(binom(n,i))) *
                 higher_complex_derivative (SUC i) (dseries h) (Cx x) *
                 higher_complex_derivative (n - i) (cexp o dseries h)
                   (Cx x)) /\
            &0 <= Re(Cx(--(&1)) pow SUC n *
                     Cx(&(binom(n,i))) *
                     higher_complex_derivative (SUC i) (dseries h) (Cx x) *
                     higher_complex_derivative (n - i) (cexp o dseries h)
                       (Cx x))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`h:num->complex`; `SUC i`; `x:real`]
      DSERIES_HIGHER_NONNEG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    REMOVE_THEN "ih" (MP_TAC o SPEC `n - i:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `SUC n = SUC i + (n - i)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_POW_ADD] THEN
    ONCE_REWRITE_TAC[COMPLEX_RING
     `(a * b) * c * d * e = c * (a * d) * (b * e):complex`] THEN
    MATCH_MP_TAC REAL_NONNEG_MUL THEN REWRITE_TAC[REAL_CX; RE_CX;
     REAL_POS] THEN
    MATCH_MP_TAC REAL_NONNEG_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_VSUM THEN ASM_SIMP_TAC[FINITE_NUMSEG];
    SIMP_TAC[RE_VSUM; FINITE_NUMSEG] THEN MATCH_MP_TAC SUM_POS_LE THEN
    ASM_SIMP_TAC[FINITE_NUMSEG]]);;

(* ------------------------------------------------------------------------- *)
(* Estermann's lower bound.                                                  *)
(* ------------------------------------------------------------------------- *)

let TAYLOR_TAIL_BOUND = prove
 (`!g Mg x M.
     g holomorphic_on {s | Re s > &0} /\ &7 / &8 <= x /\ x <= &2 /\
     1 <= M /\
     (!m. norm(higher_complex_derivative m g (Cx(&2))) <=
          &(FACT m) * Mg / (&3 / &2) pow m)
     ==> norm(g(Cx x) -
              vsum(0..M-1) (\m. higher_complex_derivative m g (Cx(&2)) /
                                Cx(&(FACT m)) * (Cx x - Cx(&2)) pow m))
         <= &4 * Mg * (&3 / &4) pow M`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= Mg` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
    REWRITE_TAC[FACT; real_pow; REAL_DIV_1; REAL_MUL_LID] THEN
    MP_TAC(ISPEC `higher_complex_derivative 0 g (Cx(&2))` NORM_POS_LE) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:complex->complex`; `Cx(&2)`; `Cx x`; `&2`]
    HOLOMORPHIC_POWER_SERIES) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
      EXISTS_TAC `{s | Re s > &0}` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM; real_gt] THEN
      X_GEN_TAC `z:complex` THEN
      MP_TAC(SPEC `Cx(&2) - z` COMPLEX_NORM_GE_RE_IM) THEN
      REWRITE_TAC[dist; RE_SUB; RE_CX] THEN REAL_ARITH_TAC;
      REWRITE_TAC[IN_BALL; dist; GSYM CX_SUB; COMPLEX_NORM_CX] THEN
      ASM_REAL_ARITH_TAC];
    DISCH_TAC] THEN
  MP_TAC(ISPECL
   [`\m. higher_complex_derivative m g (Cx(&2)) / Cx(&(FACT m)) *
         (Cx x - Cx(&2)) pow m`;
    `(g:complex->complex)(Cx x)`; `0`; `M:num`] SUMS_OFFSET) THEN
  ASM_REWRITE_TAC[LE_0] THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MATCH_MP_TAC SERIES_BOUND THEN
  EXISTS_TAC
   `\m. higher_complex_derivative m g (Cx(&2)) / Cx(&(FACT m)) *
        (Cx x - Cx(&2)) pow m` THEN
  EXISTS_TAC `\m. Mg * (&3 / &4) pow m` THEN EXISTS_TAC `from M` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_SUMS] THEN
    SUBGOAL_THEN `&4 * Mg * (&3 / &4) pow M =
                  Mg * ((&3 / &4) pow M / (&1 - &3 / &4))`
    SUBST1_TAC THENL [CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_SERIES_LMUL THEN MATCH_MP_TAC REAL_SUMS_GP THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_DIV; COMPLEX_NORM_POW;
              COMPLEX_NORM_CX; GSYM CX_SUB; REAL_ABS_NUM] THEN
  SUBGOAL_THEN `&0 < &(FACT i)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; FACT_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `(&3 / &4) pow i = (&9 / &8) pow i / (&3 / &2) pow i`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_DIV] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a * b / c = (a / c) * b:real`] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE];
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    MATCH_MP_TAC(REAL_ARITH `y = z ==> x <= y ==> x <= z`) THEN
    REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING]);;

let HIGHER_DERIV_POLE = prove
 (`!a n. higher_complex_derivative n (\w. a * inv(w - Cx(&1))) (Cx(&2)) =
         a * Cx(&(FACT n)) * (--Cx(&1)) pow n`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\w. a * inv(w - Cx(&1))`; `\i. a * (--Cx(&1)) pow i`;
                 `&1`; `n:num`]
    (INST [`from 0`,`k:num->bool`; `Cx(&2)`,`z:complex`]
      HIGHER_COMPLEX_DERIVATIVE_POWER_SERIES)) THEN
  REWRITE_TAC[REAL_LT_01; IN_FROM; LE_0] THEN ANTS_TAC THENL
   [X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`0`; `Cx(&2) - w`] SUMS_GP) THEN ANTS_TAC THENL
     [ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[GSYM dist];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `a:complex` o MATCH_MP SERIES_COMPLEX_LMUL) THEN
    REWRITE_TAC[complex_pow; COMPLEX_RING
     `Cx(&1) - (Cx(&2) - w) = w - Cx(&1)`] THEN
    REWRITE_TAC[complex_div; COMPLEX_MUL_LID] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SUMS_EQ) THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC; GSYM COMPLEX_POW_MUL] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(Cx(&(FACT n)) = Cx(&0))` MP_TAC THENL
   [REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ; FACT_NZ]; ALL_TAC] THEN
  CONV_TAC COMPLEX_FIELD);;

let TAYLOR_TERM_RE = prove
 (`!D P1 x m.
     real(Cx(--(&1)) pow m * D)
     ==> Re((D - P1 * Cx(&(FACT m)) * (--Cx(&1)) pow m) / Cx(&(FACT m)) *
            (Cx x - Cx(&2)) pow m) =
         Re(Cx(--(&1)) pow m * D) * (&2 - x) pow m / &(FACT m) -
         Re P1 * (&2 - x) pow m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL] THEN
  ABBREV_TAC `e = Re(Cx(--(&1)) pow m * D)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `Cx(--(&1)) pow m * Cx(--(&1)) pow m = Cx(&1)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM COMPLEX_POW_MUL; GSYM CX_MUL] THEN
    REWRITE_TAC[REAL_ARITH `--(&1) * --(&1) = &1`; COMPLEX_POW_ONE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Cx x - Cx(&2)) pow m = Cx(--(&1)) pow m * Cx((&2 - x) pow m)`
  SUBST1_TAC THENL
   [REWRITE_TAC[CX_POW; GSYM COMPLEX_POW_MUL] THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM CX_SUB; GSYM CX_MUL; CX_INJ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Cx(&(FACT m)) = Cx(&0))` ASSUME_TAC THENL
   [REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ; FACT_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(D - P1 * Cx(&(FACT m)) * (--Cx(&1)) pow m) / Cx(&(FACT m)) *
    Cx(--(&1)) pow m * Cx((&2 - x) pow m) =
    Cx e * Cx((&2 - x) pow m) / Cx(&(FACT m)) - P1 * Cx((&2 - x) pow m)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM CX_NEG] THEN
    MAP_EVERY UNDISCH_TAC
     [`Cx(--(&1)) pow m * Cx(--(&1)) pow m = Cx(&1)`;
      `Cx e = Cx(--(&1)) pow m * D`; `~(Cx(&(FACT m)) = Cx(&0))`] THEN
    CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[RE_SUB; RE_MUL_CX; GSYM CX_MUL; GSYM CX_DIV; RE_CX]);;

let RE_NORM_SUB_LE = prove
 (`!a b e. norm(a - b) <= e ==> Re b - e <= Re a`,
  REPEAT GEN_TAC THEN MP_TAC(SPEC `a - b:complex` COMPLEX_NORM_GE_RE_IM) THEN
  REWRITE_TAC[RE_SUB] THEN REAL_ARITH_TAC);;

let ESTERMANN_ABSTRACT = prove
 (`!P h Mg x M.
     P holomorphic_on {s | Re s > &0} /\
     (!n. 1 <= n ==> ?r. &0 <= r /\ r <= &4 /\ h n = Cx r) /\
     (!z. &1 < Re z ==> P z = (z - Cx(&1)) * cexp(dseries h z)) /\
     (!z. norm(Cx(&2) - z) = &3 / &2
          ==> norm((P z - P(Cx(&1))) / (z - Cx(&1))) <= Mg) /\
     &7 / &8 <= x /\ x < &1 /\ 1 <= M
     ==> &1 - Re(P(Cx(&1))) * (&2 - x) pow M / (&1 - x) -
         &4 * Mg * (&3 / &4) pow M <= Re(P(Cx x)) / (x - &1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?g. g holomorphic_on {s | Re s > &0} /\
        !z. ~(z = Cx(&1)) ==> g z = (P z - P(Cx(&1))) / (z - Cx(&1))`
  (X_CHOOSE_THEN `g:complex->complex` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `\z. if z = Cx(&1) then complex_derivative P (Cx(&1))
                    else ((P:complex->complex) z - P(Cx(&1))) /
                         (z - Cx(&1))` THEN
    SIMP_TAC[] THEN MATCH_MP_TAC POLE_LEMMA_OPEN THEN
    ASM_REWRITE_TAC[OPEN_HALFSPACE_RE_GT];
    ALL_TAC] THEN
  ABBREV_TAC `P1 = (P:complex->complex)(Cx(&1))` THEN
  SUBGOAL_THEN `!n. 1 <= n ==> norm((h:num->complex) n) <=
                              &4 * (&1 + log(&n)) pow 0`
  ASSUME_TAC THENL
   [REWRITE_TAC[real_pow; REAL_MUL_RID] THEN X_GEN_TAC `n:num` THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(cexp o dseries h) holomorphic_on {s | Re s > &1}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN
    REWRITE_TAC[HOLOMORPHIC_ON_CEXP] THEN
    MATCH_MP_TAC HOLOMORPHIC_DSERIES_ABS THEN
    MAP_EVERY EXISTS_TAC [`&4`; `0`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\w. P1 * inv(w - Cx(&1))) holomorphic_on {s | Re s > &1}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_LMUL THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_INV THEN
    SIMP_TAC[HOLOMORPHIC_ON_SUB; HOLOMORPHIC_ON_ID; HOLOMORPHIC_ON_CONST] THEN
    REWRITE_TAC[IN_ELIM_THM; real_gt; COMPLEX_SUB_0] THEN
    GEN_TAC THEN DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `&1 < Re(Cx(&1))` THEN REWRITE_TAC[RE_CX] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. higher_complex_derivative m g (Cx(&2)) =
        higher_complex_derivative m (cexp o dseries h) (Cx(&2)) -
        P1 * Cx(&(FACT m)) * (--Cx(&1)) pow m`
  ASSUME_TAC THENL
   [X_GEN_TAC `m:num` THEN
    MP_TAC(ISPECL [`cexp o dseries (h:num->complex)`;
                   `\w. P1 * inv(w - Cx(&1))`; `{s | Re s > &1}`;
                   `m:num`; `Cx(&2)`] HIGHER_COMPLEX_DERIVATIVE_SUB) THEN
    ASM_REWRITE_TAC[OPEN_HALFSPACE_RE_GT; IN_ELIM_THM; RE_CX; real_gt] THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[HIGHER_DERIV_POLE] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC HIGHER_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    EXISTS_TAC `{s | Re s > &1}` THEN REWRITE_TAC[OPEN_HALFSPACE_RE_GT] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
      EXISTS_TAC `{s | Re s > &0}` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC HOLOMORPHIC_ON_SUB THEN ASM_REWRITE_TAC[ETA_AX];
      REWRITE_TAC[IN_ELIM_THM; real_gt] THEN X_GEN_TAC `z:complex` THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `~(z = Cx(&1))` ASSUME_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `&1 < Re(Cx(&1))` THEN REWRITE_TAC[RE_CX] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[o_THM] THEN
      UNDISCH_TAC `~(z = Cx(&1))` THEN CONV_TAC COMPLEX_FIELD;
      REWRITE_TAC[IN_ELIM_THM; RE_CX; real_gt] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. norm(higher_complex_derivative m g (Cx(&2))) <=
        &(FACT m) * Mg / (&3 / &2) pow m`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CAUCHY_INEQUALITY THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_ON_IMP_CONTINUOUS_ON THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
      EXISTS_TAC `{s | Re s > &0}` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_CBALL; IN_ELIM_THM; real_gt; dist] THEN
      X_GEN_TAC `z:complex` THEN
      MP_TAC(SPEC `Cx(&2) - z` COMPLEX_NORM_GE_RE_IM) THEN
      REWRITE_TAC[RE_SUB; RE_CX] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
      EXISTS_TAC `{s | Re s > &0}` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM; real_gt; dist] THEN
      X_GEN_TAC `z:complex` THEN
      MP_TAC(SPEC `Cx(&2) - z` COMPLEX_NORM_GE_RE_IM) THEN
      REWRITE_TAC[RE_SUB; RE_CX] THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(z = Cx(&1))` ASSUME_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `norm(Cx(&2) - Cx(&1)) = &3 / &2` THEN
        REWRITE_TAC[GSYM CX_SUB; COMPLEX_NORM_CX] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:complex->complex`; `Mg:real`; `x:real`; `M:num`]
    TAYLOR_TAIL_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`h:num->complex`; `&2`] CEXP_DSERIES_HIGHER_NONNEG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `&1 <= Re(Cx(--(&1)) pow 0 *
             higher_complex_derivative 0 (cexp o dseries h) (Cx(&2)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[complex_pow; COMPLEX_MUL_LID; higher_complex_derivative;
                o_THM] THEN
    MP_TAC(ISPECL [`h:num->complex`; `&4`; `0`; `&2`]
      DSERIES_REAL_NONNEG) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[REAL_CX; RE_CX]; REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[REAL] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM CX_EXP; RE_CX] THEN
    MP_TAC(SPEC `Re(dseries h (Cx(&2)))` REAL_EXP_LE_X) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP RE_NORM_SUB_LE) THEN
  SIMP_TAC[RE_VSUM; FINITE_NUMSEG] THEN ASM_SIMP_TAC[TAYLOR_TERM_RE] THEN
  REWRITE_TAC[SUM_SUB_NUMSEG; SUM_LMUL] THEN
  SUBGOAL_THEN
   `&1 <= sum(0..M-1)
           (\m. Re(Cx(--(&1)) pow m *
                   higher_complex_derivative m (cexp o dseries h) (Cx(&2))) *
                (&2 - x) pow m / &(FACT m))`
  ASSUME_TAC THENL
   [SIMP_TAC[SUM_CLAUSES_LEFT; LE_0] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= a /\ &0 <= b ==> &1 <= a + b`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[real_pow; FACT; REAL_DIV_1; REAL_MUL_RID] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(0..M-1) (\m. (&2 - x) pow m) = ((&2 - x) pow M - &1) / (&1 - x)`
  SUBST1_TAC THENL
   [REWRITE_TAC[SUM_GP; LT] THEN
    ASM_SIMP_TAC[REAL_ARITH `x < &1 ==> ~(&2 - x = &1)`;
                 ARITH_RULE `1 <= M ==> SUC(M - 1) = M`] THEN
    REWRITE_TAC[real_pow] THEN
    MATCH_MP_TAC(REAL_FIELD
     `~(x = &1) ==> (&1 - y) / (&1 - (&2 - x)) = (y - &1) / (&1 - x)`) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Cx x = Cx(&1))` ASSUME_TAC THENL
   [REWRITE_TAC[CX_INJ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `Re((P:complex->complex)(Cx x)) =
                (x - &1) * Re(g(Cx x)) + Re P1`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `(P:complex->complex)(Cx x) = Cx(x - &1) * g(Cx x) + P1`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[CX_SUB] THEN UNDISCH_TAC `~(Cx x = Cx(&1))` THEN
      CONV_TAC COMPLEX_FIELD;
      REWRITE_TAC[RE_ADD; RE_MUL_CX]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((x - &1) * Re(g(Cx x)) + Re P1) / (x - &1) =
    Re((g:complex->complex)(Cx x)) - Re P1 / (&1 - x) /\
    Re P1 * ((&2 - x) pow M - &1) / (&1 - x) =
    Re P1 * (&2 - x) pow M / (&1 - x) - Re P1 / (&1 - x)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [MATCH_MP_TAC(REAL_FIELD
     `~(x = &1) ==> ((x - &1) * a + b) / (x - &1) = a - b / (&1 - x) /\
                    b * (y - &1) / (&1 - x) =
                    b * y / (&1 - x) - b / (&1 - x)`) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!s a b c g. &1 <= s
                ==> s - (a - b) - c <= g ==> &1 - a - c <= g - b`) THEN
  ASM_REWRITE_TAC[]);;

let ZETA_NEARZETA = prove
 (`!s. ~(s = Cx(&1)) ==> zeta s = (nearzeta 1 s + Cx(&1)) / (s - Cx(&1))`,
  SIMP_TAC[zeta; genzeta; CPOW_1; COMPLEX_DIV_1]);;

let NEARZETA_CIRCLE_BOUND = prove
 (`!z. norm(Cx(&2) - z) = &3 / &2 ==> norm(nearzeta 1 z + Cx(&1)) <= &28`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `Cx(&2) - z` COMPLEX_NORM_GE_RE_IM) THEN
  REWRITE_TAC[RE_SUB; RE_CX] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`1`; `z:complex`] NEARZETA_BOUND_SHARP) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  REWRITE_TAC[LOG_1; REAL_MUL_RZERO; REAL_EXP_0; REAL_DIV_1] THEN
  SUBGOAL_THEN `norm(z:complex) <= &7 / &2 /\ norm(z - Cx(&1)) <= &5 / &2 /\
                &1 / &2 <= Re z`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `norm(Cx(&2)) = &2 /\ norm(Cx(&2) - Cx(&1)) = &1`
    MP_TAC THENL
     [REWRITE_TAC[GSYM CX_SUB; COMPLEX_NORM_CX] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `norm(Cx(&2) - z) = &3 / &2` THEN
      UNDISCH_TAC `abs(&2 - Re z) <= norm(Cx(&2) - z)` THEN
      CONV_TAC NORM_ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &1 + &1 / Re z <= &3` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= &2 ==> &1 / &1 + x <= &3`) THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 / &2 <= x ==> &0 < x`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(z * (z - Cx(&1))) * (&1 / &1 + &1 / Re z) <= &27`
  ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_MUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&7 / &2 * &5 / &2) * &3` THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[REAL_LE_MUL; NORM_POS_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
      MATCH_MP_TAC REAL_LE_ADD THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS;
       REAL_ARITH `&1 / &2 <= x ==> &0 <= x`]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`nearzeta 1 z`; `Cx(&1)`] NORM_TRIANGLE) THEN
  REWRITE_TAC[COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC);;

let NORM_MUL4_LE = prove
 (`!a b c d A B C D.
     norm a <= A /\ norm b <= B /\ norm c <= C /\ norm d <= D
     ==> norm(a * b * c * d:complex) <= A * B * C * D`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[COMPLEX_NORM_MUL] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL2 THEN
         ASM_SIMP_TAC[NORM_POS_LE; REAL_LE_MUL]));;

let SIEGEL_P_HOLOMORPHIC = prove
 (`!q1 q2 c1 c2.
     dirichlet_character q1 c1 /\ ~(c1 = chi_0 q1) /\
     dirichlet_character q2 c2 /\ ~(c2 = chi_0 q2) /\
     ~((\n. c1 n * c2 n) = chi_0(q1 * q2))
     ==> (\s. (nearzeta 1 s + Cx(&1)) * dseries c1 s * dseries c2 s *
              dseries (\n. c1 n * c2 n) s) holomorphic_on {s | Re s > &0}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`q1:num`; `q2:num`; `c1:num->complex`; `c2:num->complex`]
    DIRICHLET_CHARACTER_MUL_MOD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REPEAT(MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN CONJ_TAC) THEN
  REWRITE_TAC[ETA_AX] THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_ADD THEN
    SIMP_TAC[HOLOMORPHIC_NEARZETA; LE_REFL; ETA_AX; HOLOMORPHIC_ON_CONST];
    ASM_MESON_TAC[HOLOMORPHIC_LFUN];
    ASM_MESON_TAC[HOLOMORPHIC_LFUN];
    ASM_MESON_TAC[HOLOMORPHIC_LFUN]]);;

let SIEGEL_F_LOWER = prove
 (`!q1 q2 c1 c2 x M.
     dirichlet_character q1 c1 /\ ~(c1 = chi_0 q1) /\ (!n. real(c1 n)) /\
     dirichlet_character q2 c2 /\ ~(c2 = chi_0 q2) /\ (!n. real(c2 n)) /\
     ~((\n. c1 n * c2 n) = chi_0(q1 * q2)) /\
     &7 / &8 <= x /\ x < &1 /\ 1 <= M
     ==> &1 - Re(dseries c1 (Cx(&1)) * dseries c2 (Cx(&1)) *
                 dseries (\n. c1 n * c2 n) (Cx(&1))) *
             (&2 - x) pow M / (&1 - x) -
         &4 * (&2 pow 17 * (&q1 * &q2) pow 2) * (&3 / &4) pow M
         <= Re(zeta(Cx x) * dseries c1 (Cx x) * dseries c2 (Cx x) *
               dseries (\n. c1 n * c2 n) (Cx x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`q1:num`; `q2:num`; `c1:num->complex`; `c2:num->complex`]
    DIRICHLET_CHARACTER_MUL_MOD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\s. (nearzeta 1 s + Cx(&1)) * dseries c1 s * dseries c2 s *
         dseries (\n. c1 n * c2 n) s`;
    `\n. Cx(mangoldt n / log(&n)) * (Cx(&1) + c1 n) * (Cx(&1) + c2 n)`;
    `&2 pow 17 * (&q1 * &q2) pow 2`; `x:real`; `M:num`]
   ESTERMANN_ABSTRACT) THEN
  REWRITE_TAC[] THEN
  REWRITE_TAC[REWRITE_RULE[LE_REFL] (SPEC `1` NEARZETA_1);
              COMPLEX_ADD_LID; COMPLEX_MUL_LID] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SIEGEL_P_HOLOMORPHIC THEN
      MAP_EVERY EXISTS_TAC [`q1:num`; `q2:num`] THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SIEGEL_COEFF THEN
      MAP_EVERY EXISTS_TAC [`q1:num`; `q2:num`] THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(z = Cx(&1))` ASSUME_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `&1 < Re(Cx(&1))` THEN REWRITE_TAC[RE_CX] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(SPECL [`q1:num`; `q2:num`; `c1:num->complex`;
                    `c2:num->complex`; `z:complex`] SIEGEL_EXP) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[ZETA_NEARZETA] THEN
      UNDISCH_TAC `~(z = Cx(&1))` THEN CONV_TAC COMPLEX_FIELD;
      X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
      SUBGOAL_THEN `&1 / &2 <= Re z /\ norm(z:complex) <= &4 /\
                    &1 / &2 <= norm(z - Cx(&1))`
      STRIP_ASSUME_TAC THENL
       [MP_TAC(SPEC `Cx(&2) - z` COMPLEX_NORM_GE_RE_IM) THEN
        REWRITE_TAC[RE_SUB; RE_CX] THEN
        SUBGOAL_THEN `norm(Cx(&2)) = &2 /\ norm(Cx(&2) - Cx(&1)) = &1`
        MP_TAC THENL
         [REWRITE_TAC[GSYM CX_SUB; COMPLEX_NORM_CX] THEN REAL_ARITH_TAC;
          UNDISCH_TAC `norm(Cx(&2) - z) = &3 / &2` THEN
          CONV_TAC NORM_ARITH];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `norm((nearzeta 1 z + Cx(&1)) * dseries c1 z * dseries c2 z *
             dseries (\n. c1 n * c2 n) z) <=
        &28 * (&11 * &q1) * (&11 * &q2) * (&11 * &(q1 * q2)) /\
        norm(dseries c1 (Cx(&1)) * dseries c2 (Cx(&1)) *
             dseries (\n. c1 n * c2 n) (Cx(&1))) <=
        (&11 * &q1) * (&11 * &q2) * (&11 * &(q1 * q2))`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC NORM_MUL4_LE THEN
          ASM_SIMP_TAC[NEARZETA_CIRCLE_BOUND] THEN
          REPEAT CONJ_TAC THEN MATCH_MP_TAC LFUN_CRUDE_BOUND THEN
          ASM_REWRITE_TAC[];
          REWRITE_TAC[COMPLEX_NORM_MUL] THEN
          REPEAT(MATCH_MP_TAC REAL_LE_MUL2 THEN
                 SIMP_TAC[NORM_POS_LE; REAL_LE_MUL] THEN CONJ_TAC) THEN
          MATCH_MP_TAC LFUN_CRUDE_BOUND THEN
          ASM_REWRITE_TAC[RE_CX; COMPLEX_NORM_CX] THEN REAL_ARITH_TAC];
        ALL_TAC] THEN
      REWRITE_TAC[COMPLEX_NORM_DIV] THEN
      SUBGOAL_THEN `&0 < norm(z - Cx(&1))` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&29 * &1331 * (&q1 * &q2) pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC(NORM_ARITH
         `!a b:complex A B. norm a <= A /\ norm b <= B /\ A + B <= C
                            ==> norm(a - b) <= C`) THEN
        MAP_EVERY EXISTS_TAC
         [`&28 * (&11 * &q1) * (&11 * &q2) * (&11 * &(q1 * q2))`;
          `(&11 * &q1) * (&11 * &q2) * (&11 * &(q1 * q2))`] THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&2 pow 17 * (&q1 * &q2) pow 2) * &1 / &2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH
         `&0 <= y ==> &29 * &1331 * y <= (&2 pow 17 * y) * &1 / &2`) THEN
        REWRITE_TAC[REAL_LE_POW_2];
        MATCH_MP_TAC REAL_LE_LMUL THEN
        SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_LE_POW_2; REAL_POS] THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b = c ==> a <= b ==> a <= c`) THEN
  SUBGOAL_THEN `~(Cx x = Cx(&1))` ASSUME_TAC THENL
   [REWRITE_TAC[CX_INJ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[ZETA_NEARZETA] THEN
  SUBGOAL_THEN
   `(nearzeta 1 (Cx x) + Cx(&1)) * dseries c1 (Cx x) * dseries c2 (Cx x) *
    dseries (\n. c1 n * c2 n) (Cx x) =
    Cx(x - &1) *
    ((nearzeta 1 (Cx x) + Cx(&1)) / (Cx x - Cx(&1)) * dseries c1 (Cx x) *
     dseries c2 (Cx x) * dseries (\n. c1 n * c2 n) (Cx x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[CX_SUB] THEN UNDISCH_TAC `~(Cx x = Cx(&1))` THEN
    CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[RE_MUL_CX] THEN
  MATCH_MP_TAC(REAL_FIELD `~(x = &1) ==> ((x - &1) * a) / (x - &1) = a`) THEN
  ASM_REAL_ARITH_TAC);;

let LOG_4_3_LOWER = prove
 (`&1 / &4 <= log(&4 / &3)`,
  SUBGOAL_THEN `&4 / &3 = inv(&1 + --(&1 / &4))` SUBST1_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SIMP_TAC[LOG_INV; REAL_ARITH `&0 < &1 + --(&1 / &4)`] THEN
  MP_TAC(SPEC `--(&1 / &4)` LOG_LE_STRONG) THEN REAL_ARITH_TAC);;

let POW_LE_EXP = prove
 (`!x n. &0 <= x ==> (&1 + x) pow n <= exp(&n * x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_EXP_N] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_EXP_LE_X] THEN
  ASM_REAL_ARITH_TAC);;

let LAMBDA_ARITH = prove
 (`!lam A w E. &0 < w /\ &0 < A /\ &0 < E /\ A <= &2048 * E /\
               &1 / &2 <= lam * A / w
               ==> w * inv E / &4096 <= lam`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `w / &2 <= lam * A` ASSUME_TAC THENL
   [UNDISCH_TAC `&1 / &2 <= lam * A / w` THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < lam` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`--lam:real`; `A:real`] REAL_LE_MUL) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `lam * A <= lam * (&2048 * E)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `w * inv E / &4096 = (w / E) / &4096` SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &4096`] THEN
  ASM_REAL_ARITH_TAC);;

let SIEGEL_LAMBDA_LOWER = prove
 (`!q1 q2 c1 c2 b.
     dirichlet_character q1 c1 /\ ~(c1 = chi_0 q1) /\ (!n. real(c1 n)) /\
     dirichlet_character q2 c2 /\ ~(c2 = chi_0 q2) /\ (!n. real(c2 n)) /\
     ~((\n. c1 n * c2 n) = chi_0(q1 * q2)) /\
     &7 / &8 <= b /\ b < &1 /\
     Re(zeta(Cx b) * dseries c1 (Cx b) * dseries c2 (Cx b) *
        dseries (\n. c1 n * c2 n) (Cx b)) <= &0
     ==> (&1 - b) * exp(--(&8 * (&1 - b) * log(&q1 * &q2))) / &4096 <=
         Re(dseries c1 (Cx(&1)) * dseries c2 (Cx(&1)) *
            dseries (\n. c1 n * c2 n) (Cx(&1)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&4 <= &q1 * &q2` ASSUME_TAC THENL
   [MP_TAC(SPECL [`q1:num`; `c1:num->complex`]
      DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL) THEN
    MP_TAC(SPECL [`q2:num`; `c2:num->complex`]
      DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL) THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `2 * 2 <= a ==> 4 <= a`) THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?M. &2 pow 20 * (&q1 * &q2) pow 2 <= (&4 / &3) pow M /\
        !m. m < M ==> ~(&2 pow 20 * (&q1 * &q2) pow 2 <= (&4 / &3) pow m)`
  (X_CHOOSE_THEN `M:num` STRIP_ASSUME_TAC) THENL
   [REWRITE_TAC[GSYM num_WOP] THEN
    MP_TAC(SPECL [`&4 / &3`; `&2 pow 20 * (&q1 * &q2) pow 2`]
      REAL_ARCH_POW) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; MESON_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= (&q1 * &q2) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(M = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `&2 pow 20 * (&q1 * &q2) pow 2 <= (&4 / &3) pow 0` THEN
    REWRITE_TAC[real_pow] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `M:num` num_CASES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
  REWRITE_TAC[LT; REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`q1:num`; `q2:num`; `c1:num->complex`; `c2:num->complex`;
                `b:real`; `SUC N`] SIEGEL_F_LOWER) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= SUC N`] THEN
  ABBREV_TAC `lam = Re(dseries c1 (Cx(&1)) * dseries c2 (Cx(&1)) *
                      dseries (\n. c1 n * c2 n) (Cx(&1)))` THEN
  ABBREV_TAC `Q = &q1 * &q2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= log(&2) /\ &0 <= log Q` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&4 * (&2 pow 17 * Q pow 2) * (&3 / &4) pow SUC N <= &1 / &2`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(&3 / &4) pow SUC N = inv((&4 / &3) pow SUC N)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_POW_INV] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (&4 / &3) pow SUC N` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&4 * (&2 pow 17 * Q pow 2) * inv((&4 / &3) pow SUC N) =
                  (&2 pow 19 * Q pow 2) / (&4 / &3) pow SUC N`
    SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&N < &80 * log(&2) + &8 * log Q` ASSUME_TAC THENL
   [SUBGOAL_THEN `exp(&N / &4) < &2 pow 20 * Q pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(&4 / &3) pow N` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(&4 / &3) pow N = exp(&N * log(&4 / &3))`
      SUBST1_TAC THENL
       [REWRITE_TAC[REAL_EXP_N] THEN
        SIMP_TAC[EXP_LOG; REAL_ARITH `&0 < &4 / &3`];
        ALL_TAC] THEN
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `x / &4 = x * (&1 / &4)`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS; LOG_4_3_LOWER];
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`exp(&N / &4)`; `&2 pow 20 * Q pow 2`] LOG_MONO_LT_IMP) THEN
    ASM_REWRITE_TAC[REAL_EXP_POS_LT; LOG_EXP] THEN
    SUBGOAL_THEN `&0 < Q` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_MUL; REAL_POW_LT; LOG_POW; REAL_ARITH `&0 < &2`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 - b) pow SUC N <= &2048 * exp(&8 * (&1 - b) * log Q)`
  ASSUME_TAC THENL
   [REWRITE_TAC[real_pow] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * exp(&N * (&1 - b))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
        ONCE_REWRITE_TAC[REAL_ARITH `&2 - b = &1 + (&1 - b)`] THEN
        MATCH_MP_TAC POW_LE_EXP THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&2048 * exp(&8 * (&1 - b) * log Q) =
                  &2 * exp(&10 * log(&2) + &8 * (&1 - b) * log Q)`
    SUBST1_TAC THENL
     [REWRITE_TAC[REAL_EXP_ADD; REAL_EXP_N] THEN
      SIMP_TAC[EXP_LOG; REAL_ARITH `&0 < &2`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC;
     ALL_TAC] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    SUBGOAL_THEN `&0 <= (&80 * log(&2) + &8 * log Q - &N) * (&1 - b) /\
                  &0 <= (&1 / &8 - (&1 - b)) * log(&2)`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_NEG] THEN MATCH_MP_TAC LAMBDA_ARITH THEN
  EXISTS_TAC `(&2 - b) pow SUC N` THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Products of two characters that are principal.                            *)
(* ------------------------------------------------------------------------- *)

let GEOMETRIC_RECIP_PRIME = prove
 (`!p N. 2 <= p ==> sum(1..N) (\k. inv(&p) pow k) <= inv(&p - &1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&2 <= &p` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  REWRITE_TAC[SUM_GP] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [UNDISCH_TAC `inv(&p) = &1` THEN
    ASM_SIMP_TAC[REAL_INV_EQ_1; REAL_ARITH `&2 <= x ==> ~(x = &1)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&p) /\ inv(&p) < &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= inv(&p) pow SUC N` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_SUB_LT; REAL_POW_1] THEN
  SUBGOAL_THEN `inv(&p - &1) * (&1 - inv(&p)) = inv(&p)` SUBST1_TAC THENL
   [UNDISCH_TAC `&2 <= &p` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let PRIME_POWER_RECIP_SUM = prove
 (`!m N. ~(m = 0)
         ==> sum {n | n IN 1..N /\
                      ?p k. prime p /\ p divides m /\ 1 <= k /\ n = p EXP k}
                 (\n. inv(&n))
             <= sum {p | prime p /\ p divides m} (\p. inv(&p - &1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {p | prime p /\ p divides m}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{p | p divides m}` THEN ASM_SIMP_TAC[FINITE_DIVISORS] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `P = {p | prime p /\ p divides m}` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum P (\p. sum(1..N) (\k. inv(&p) pow k))` THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "P" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC GEOMETRIC_RECIP_PRIME THEN ASM_SIMP_TAC[PRIME_GE_2]] THEN
  ASM_SIMP_TAC[SUM_SUM_PRODUCT; FINITE_NUMSEG] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (IMAGE (\(p,k). p EXP k) {p,k | p IN P /\ k IN 1..N})
                  (\n. inv(&n))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FINITE_PRODUCT_DEPENDENT; FINITE_NUMSEG] THEN
    REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE; EXISTS_PAIR_THM] THEN
    X_GEN_TAC `n:num` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC
     (X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC))) THEN
    ASM_REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`p:num`; `k:num`] THEN REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`p:num`; `k:num`] THEN REWRITE_TAC[IN_NUMSEG] THEN
    EXPAND_TAC "P" THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `p EXP k` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LT_IMP_LE THEN
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP k` THEN
    REWRITE_TAC[LT_POW2_REFL; EXP_MONO_LE] THEN
    ASM_SIMP_TAC[PRIME_GE_2];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {p,k | p IN P /\ k IN 1..N}
                  ((\n. inv(&n)) o (\(p,k). p EXP k))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_IMAGE_LE THEN
    ASM_SIMP_TAC[FINITE_PRODUCT_DEPENDENT; FINITE_NUMSEG] THEN
    REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
  REWRITE_TAC[FORALL_PAIR_THM; o_THM] THEN
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_POW_INV]);;

let PRIME_RECIP_TERM_BOUND = prove
 (`!e N0 p. &0 < e /\ &2 / e <= &N0 /\ prime p
            ==> inv(&p - &1) <= (if p <= N0 + 1 then &1 else &0) +
                                e * log(&p)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
  SUBGOAL_THEN `&2 <= &p` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &2 <= log(&p)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&2)` THEN
    REWRITE_TAC[LOG_2_BOUNDS] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= e * log(&p)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= &1 /\ &0 <= y ==> x <= &1 + y`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 / e <= &p - &1` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_LE]) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_ADD] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2 / e)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT;
                                                ARITH];
    REWRITE_TAC[REAL_INV_DIV; REAL_ADD_LID] THEN
    MATCH_MP_TAC(REAL_ARITH `e / &2 = e * &1 / &2 /\ e * &1 / &2 <= y
                             ==> e / &2 <= y`) THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]);;

let PRIME_DIVISOR_RECIP_BOUND = prove
 (`!e. &0 < e
       ==> ?C. !m. ~(m = 0)
               ==> sum {p | prime p /\ p divides m} (\p. inv(&p - &1))
                   <= C + e * log(&m)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `&2 / e` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN
  EXISTS_TAC `&N0 + &2` THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `FINITE {p | prime p /\ p divides m}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{p | p divides m}` THEN ASM_SIMP_TAC[FINITE_DIVISORS] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {p | prime p /\ p divides m}
                  (\p. (if p <= N0 + 1 then &1 else &0) + e * log(&p))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PRIME_RECIP_TERM_BOUND THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_ADD; SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
    SUBGOAL_THEN
     `{x | x IN {p | prime p /\ p divides m} /\ x <= N0 + 1} SUBSET
      0..N0+1`
    ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`{x | x IN {p | prime p /\ p divides m} /\ x <= N0 + 1}`;
                   `0..N0+1`] CARD_SUBSET) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; CARD_NUMSEG] THEN
    SUBGOAL_THEN
     `FINITE {x | x IN {p | prime p /\ p divides m} /\ x <= N0 + 1}`
    ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..N0+1` THEN
      ASM_REWRITE_TAC[FINITE_NUMSEG];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_CONST; REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `m:num` LOG_MANGOLDT_SUM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {p | prime p /\ p divides m} (\d. mangoldt d)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`x:num`; `1`] MANGOLDT_PRIMEPOW) THEN
    ASM_REWRITE_TAC[EXP_1; LE_REFL] THEN MESON_TAC[];
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    ASM_SIMP_TAC[FINITE_DIVISORS; MANGOLDT_POS_LE] THEN SET_TAC[]]);;

let REAL_CHARACTER_PRODUCT_PRINCIPAL = prove
 (`!q1 q2 c1 c2 n.
     dirichlet_character q1 c1 /\ (!n. real(c1 n)) /\
     dirichlet_character q2 c2 /\ (!n. real(c2 n)) /\
     (\n. c1 n * c2 n) = chi_0(q1 * q2) /\ coprime(n,q1 * q2)
     ==> c1 n = c2 n`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
  ASM_REWRITE_TAC[chi_0] THEN
  MP_TAC(SPECL [`q1:num`; `c1:num->complex`]
    DIRICHLET_CHARACTER_REAL_CASES) THEN
  MP_TAC(SPECL [`q2:num`; `c2:num->complex`]
    DIRICHLET_CHARACTER_REAL_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC COMPLEX_RING);;

let MANGOLDT_NZ_PRIMEPOW = prove
 (`!n. ~(mangoldt n = &0) ==> ?p k. prime p /\ 1 <= k /\ n = p EXP k`,
  GEN_TAC THEN REWRITE_TAC[mangoldt] THEN MESON_TAC[]);;

let PRINCIPAL_PRODUCT_DIFF_BOUND = prove
 (`!q1 q2 c1 c2 n.
     dirichlet_character q1 c1 /\ (!n. real(c1 n)) /\
     dirichlet_character q2 c2 /\ (!n. real(c2 n)) /\
     (\n. c1 n * c2 n) = chi_0(q1 * q2) /\ 1 <= n
     ==> norm(Cx(mangoldt n / log(&n)) * (c2 n - c1 n)) <=
         if ?p k. prime p /\ p divides (q1 * q2) /\ 1 <= k /\ n = p EXP k
         then &2 else &0`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `mangoldt n = &0` THENL
   [ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; COMPLEX_MUL_LZERO;
                    COMPLEX_NORM_0] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MANGOLDT_NZ_PRIMEPOW) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `k:num`
    STRIP_ASSUME_TAC)) THEN
  ASM_CASES_TAC `p divides (q1 * q2)` THENL
   [COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    MP_TAC(SPEC `n:num` MANGOLDT_DIV_LOG_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * &2` THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(a:complex) <= &1 /\ norm(b:complex) <= &1 ==> norm(a - b) <= &2`)
       THEN
    ASM_MESON_TAC[DIRICHLET_CHARACTER_NORM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c1:num->complex) n = c2 n` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_CHARACTER_PRODUCT_PRINCIPAL THEN
    MAP_EVERY EXISTS_TAC [`q1:num`; `q2:num`] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[COPRIME_LEXP; PRIME_COPRIME_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_MUL_RZERO; COMPLEX_NORM_0] THEN
  COND_CASES_TAC THEN REAL_ARITH_TAC);;

let PRINCIPAL_PRODUCT_DLOG_DIFF = prove
 (`!q1 q2 c1 c2 x.
     dirichlet_character q1 c1 /\ (!n. real(c1 n)) /\
     dirichlet_character q2 c2 /\ (!n. real(c2 n)) /\
     (\n. c1 n * c2 n) = chi_0(q1 * q2) /\ ~(q1 * q2 = 0) /\ &1 < x
     ==> norm(dseries (\n. Cx(mangoldt n / log(&n)) * (c2 n - c1 n))
                      (Cx x)) <=
         &2 * sum {p | prime p /\ p divides (q1 * q2)} (\p. inv(&p - &1))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC DSERIES_NORM_BOUND THEN
  MAP_EVERY EXISTS_TAC [`&2`; `0`] THEN ASM_REWRITE_TAC[RE_CX] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`q1:num`; `q2:num`; `c1:num->complex`;
                  `c2:num->complex`; `n:num`]
      PRINCIPAL_PRODUCT_DIFF_BOUND) THEN
    ASM_REWRITE_TAC[real_pow; REAL_MUL_RID] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `N:num` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..N) (\n. &2 * (if ?p k. prime p /\ p divides (q1 * q2) /\
                                  1 <= k /\ n = p EXP k
                         then inv(&n) else &0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(SPECL [`q1:num`; `q2:num`; `c1:num->complex`;
                  `c2:num->complex`; `n:num`]
      PRINCIPAL_PRODUCT_DIFF_BOUND) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&n rpow (--x) <= inv(&n) /\ &0 <= &n rpow (--x)`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[RPOW_NUM_POS; REAL_LT_IMP_LE] THEN
      MP_TAC(SPECL [`--x:real`; `--(&1):real`; `&n:real`] RPOW_MONO_LE) THEN
      REWRITE_TAC[RPOW_NEG; RPOW_POW; REAL_POW_1] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN DISCH_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * &n rpow (--x)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        REAL_ARITH_TAC];
      MATCH_MP_TAC(REAL_ARITH `x = &0 ==> x <= &2 * &0`) THEN
      REWRITE_TAC[REAL_ENTIRE] THEN DISJ1_TAC THEN
      MP_TAC(ISPEC `Cx(mangoldt n / log(&n)) * (c2 n - c1 n)`
        NORM_POS_LE) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  MP_TAC(SPECL [`q1 * q2:num`; `N:num`] PRIME_POWER_RECIP_SUM) THEN
  ASM_REWRITE_TAC[IN_NUMSEG]);;

let LFUN_1_PRINCIPAL_PRODUCT = prove
 (`!q1 q2 c1 c2.
     dirichlet_character q1 c1 /\ ~(c1 = chi_0 q1) /\ (!n. real(c1 n)) /\
     dirichlet_character q2 c2 /\ ~(c2 = chi_0 q2) /\ (!n. real(c2 n)) /\
     (\n. c1 n * c2 n) = chi_0(q1 * q2)
     ==> exp(--(&2 * sum {p | prime p /\ p divides (q1 * q2)}
                          (\p. inv(&p - &1)))) *
         Re(dseries c1 (Cx(&1))) <= Re(dseries c2 (Cx(&1)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(q1 * q2 = 0)` ASSUME_TAC THENL
   [REWRITE_TAC[MULT_EQ_0] THEN
    ASM_MESON_TAC[DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL];
    ALL_TAC] THEN
  ABBREV_TAC `Bm = sum {p | prime p /\ p divides (q1 * q2)}
                       (\p. inv(&p - &1))` THEN
  MP_TAC(ISPEC `\s. dseries c2 s - Cx(exp(--(&2 * Bm))) * dseries c1 s`
    RIGHT_LIMIT_AT_1) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ALL_TAC; REWRITE_TAC[RE_SUB; RE_MUL_CX] THEN REAL_ARITH_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_SUB THEN CONJ_TAC THENL
     [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC LFUN_CONTINUOUS_AT THEN
      EXISTS_TAC `q2:num` THEN ASM_REWRITE_TAC[RE_CX] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_COMPLEX_LMUL THEN
      REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC LFUN_CONTINUOUS_AT THEN
      EXISTS_TAC `q1:num` THEN ASM_REWRITE_TAC[RE_CX] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!n. 1 <= n
        ==> norm(Cx(mangoldt n / log(&n)) * (c1:num->complex) n) <= &1 /\
            norm(Cx(mangoldt n / log(&n)) * (c2:num->complex) n) <= &1`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(SPEC `n:num` MANGOLDT_DIV_LOG_BOUNDS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1 * &1` THEN
    (CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC]) THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
    ASM_MESON_TAC[DIRICHLET_CHARACTER_NORM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `real(dseries_log c1 (Cx x)) /\ real(dseries_log c2 (Cx x))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[dseries_log] THEN CONJ_TAC THEN MATCH_MP_TAC DSERIES_REAL THEN
    MAP_EVERY EXISTS_TAC [`&1`; `0`] THEN
    ASM_SIMP_TAC[real_pow; REAL_MUL_RID; REAL_MUL; REAL_CX];
    ALL_TAC] THEN
  SUBGOAL_THEN `dseries c1 (Cx x) = cexp(dseries_log c1 (Cx x)) /\
                dseries c2 (Cx x) = cexp(dseries_log c2 (Cx x))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC DSERIES_EXP THEN ASM_REWRITE_TAC[RE_CX] THEN
    ASM_MESON_TAC[DIRICHLET_CHARACTER_DSERIES_HYPS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `dseries_log c2 (Cx x) =
    dseries_log c1 (Cx x) +
    dseries (\n. Cx(mangoldt n / log(&n)) * (c2 n - c1 n)) (Cx x)`
  ASSUME_TAC THENL
   [REWRITE_TAC[dseries_log] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `dseries (\n. Cx(mangoldt n / log(&n)) * c1 n +
                   Cx(mangoldt n / log(&n)) * (c2 n - c1 n)) (Cx x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC DSERIES_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    MATCH_MP_TAC DSERIES_ADD THEN MAP_EVERY EXISTS_TAC [`&2`; `0`] THEN
    ASM_REWRITE_TAC[RE_CX; real_pow; REAL_MUL_RID] THEN CONJ_TAC THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1` THEN
      ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
      MP_TAC(SPECL [`q1:num`; `q2:num`; `c1:num->complex`;
                    `c2:num->complex`; `n:num`]
        PRINCIPAL_PRODUCT_DIFF_BOUND) THEN
      ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`q1:num`; `q2:num`; `c1:num->complex`; `c2:num->complex`;
                `x:real`] PRINCIPAL_PRODUCT_DLOG_DIFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC
   `D = dseries (\n. Cx(mangoldt n / log(&n)) * (c2 n - c1 n)) (Cx x)` THEN
  SUBGOAL_THEN `real D` ASSUME_TAC THENL
   [SUBGOAL_THEN `D = dseries_log c2 (Cx x) - dseries_log c1 (Cx x)`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC COMPLEX_RING;
      ASM_SIMP_TAC[REAL_SUB]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `real(dseries_log c1 (Cx x))` THEN UNDISCH_TAC `real D` THEN
  REWRITE_TAC[REAL] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM CX_ADD; GSYM CX_EXP; GSYM CX_MUL; GSYM CX_SUB;
              REAL_CX; RE_CX] THEN
  REWRITE_TAC[REAL_EXP_ADD; REAL_SUB_LE] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE] THEN
  MP_TAC(SPEC `D:complex` COMPLEX_NORM_GE_RE_IM) THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Siegel's theorem.                                                         *)
(* ------------------------------------------------------------------------- *)

let NEARZETA_NEAR_1 = prove
 (`?d. &0 < d /\ d <= &1 / &8 /\
       !x. &1 - d <= x /\ x <= &1 ==> &0 < Re(nearzeta 1 (Cx x) + Cx(&1))`,
  SUBGOAL_THEN `(nearzeta 1) continuous at (Cx(&1))` MP_TAC THENL
   [MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT THEN
    EXISTS_TAC `{s | Re s > &0}` THEN
    SIMP_TAC[HOLOMORPHIC_NEARZETA; LE_REFL; OPEN_HALFSPACE_RE_GT] THEN
    REWRITE_TAC[IN_ELIM_THM; RE_CX; real_gt] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `&1 / &2`) THEN
  REWRITE_TAC[REWRITE_RULE[LE_REFL] (SPEC `1` NEARZETA_1)] THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min (d / &2) (&1 / &8)` THEN
  REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `Cx x`) THEN
  REWRITE_TAC[dist; GSYM CX_SUB; COMPLEX_NORM_CX; COMPLEX_SUB_RZERO] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `nearzeta 1 (Cx x)` COMPLEX_NORM_GE_RE_IM) THEN
  REWRITE_TAC[RE_ADD; RE_CX] THEN REAL_ARITH_TAC);;

let LFUN_REAL_POS_ARG = prove
 (`!d c x. dirichlet_character d c /\ ~(c = chi_0 d) /\ (!n. real(c n)) /\
           &0 < x
           ==> real(dseries c (Cx x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DSERIES_REAL_BOUNDED THEN
  EXISTS_TAC `&d` THEN ASM_SIMP_TAC[NONPRINCIPAL_PARTIAL_SUM_BOUND]);;

let SIEGEL_F_NONPOS = prove
 (`!q1 q2 c1 c2 b.
     dirichlet_character q1 c1 /\ ~(c1 = chi_0 q1) /\ (!n. real(c1 n)) /\
     dirichlet_character q2 c2 /\ ~(c2 = chi_0 q2) /\ (!n. real(c2 n)) /\
     ~((\n. c1 n * c2 n) = chi_0(q1 * q2)) /\
     &0 < b /\ b < &1 /\ &0 < Re(nearzeta 1 (Cx b) + Cx(&1)) /\
     &0 < Re(dseries c1 (Cx b)) /\ &0 < Re(dseries c2 (Cx b)) /\
     &0 < Re(dseries (\n. c1 n * c2 n) (Cx b))
     ==> Re(zeta(Cx b) * dseries c1 (Cx b) * dseries c2 (Cx b) *
            dseries (\n. c1 n * c2 n) (Cx b)) <= &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`q1:num`; `q2:num`; `c1:num->complex`; `c2:num->complex`]
    DIRICHLET_CHARACTER_MUL_MOD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `real(dseries c1 (Cx b)) /\ real(dseries c2 (Cx b)) /\
    real(dseries (\n. c1 n * c2 n) (Cx b))`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC LFUN_REAL_POS_ARG THENL
     [EXISTS_TAC `q1:num`; EXISTS_TAC `q2:num`; EXISTS_TAC `q1 * q2:num`] THEN
    ASM_SIMP_TAC[REAL_MUL];
    ALL_TAC] THEN
  REWRITE_TAC[REAL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (CONJUNCTS_THEN2
    (SUBST1_TAC o SYM) (SUBST1_TAC o SYM))) THEN
  SUBGOAL_THEN `~(Cx b = Cx(&1))` ASSUME_TAC THENL
   [REWRITE_TAC[CX_INJ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[ZETA_NEARZETA] THEN
  ABBREV_TAC `r1 = Re(dseries c1 (Cx b))` THEN
  ABBREV_TAC `r2 = Re(dseries c2 (Cx b))` THEN
  ABBREV_TAC `r3 = Re(dseries (\n. c1 n * c2 n) (Cx b))` THEN
  SUBGOAL_THEN
   `(nearzeta 1 (Cx b) + Cx(&1)) / (Cx b - Cx(&1)) * Cx r1 * Cx r2 * Cx r3 =
    (nearzeta 1 (Cx b) + Cx(&1)) * Cx((r1 * r2 * r3) / (b - &1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[CX_MUL; CX_DIV; CX_SUB] THEN
    UNDISCH_TAC `~(Cx b = Cx(&1))` THEN CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[RE_MUL_CX] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x * --t ==> x * t <= &0`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--((r1 * r2 * r3) / (b - &1)) = (r1 * r2 * r3) / (&1 - b)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_FIELD
     `~(b = &1) ==> --(x / (b - &1)) = x / (&1 - b)`) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
   [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC);;

let LE_EXP_DIV = prove
 (`!a y. &0 < a ==> y <= exp(a * y) / a`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  MP_TAC(SPEC `a * y:real` REAL_EXP_LE_X) THEN REAL_ARITH_TAC);;

let LFUN_1_UPPER = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> norm(dseries c (Cx(&1))) <= &12 * (&1 + log(&3 * &d))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`]
    DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`; `Cx(&1)`; `3 * d`] LFUN_BOUND) THEN
  ASM_REWRITE_TAC[RE_CX; IM_CX; GSYM REAL_OF_NUM_MUL] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  SUBGOAL_THEN `&0 <= log(&3 * &d)` MP_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN
    SUBGOAL_THEN `&1 <= &d` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_INV) THEN REAL_ARITH_TAC);;

let SIEGEL_ARITH_NONPRINCIPAL = prove
 (`!A1 R2 R12 b E X Y e W.
     &0 < A1 /\ &0 < R12 /\
     (&1 - b) * E / &4096 <= A1 * R2 * R12 /\ &0 <= &1 - b /\
     exp(--(e / &2 * X)) * exp(--(e / &2 * Y)) <= E /\
     R12 <= &12 * W * exp(e / &2 * Y) /\ &0 < W
     ==> ((&1 - b) * exp(--(e / &2 * X)) / (&4096 * A1 * &12 * W)) *
         exp(--(e * Y)) <= R2`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `A1 * R12:real` THEN
  ASM_SIMP_TAC[REAL_LT_MUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 - b) * E / &4096` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(((&1 - b) * exp(--(e / &2 * X)) / (&4096 * A1 * &12 * W)) *
               exp(--(e * Y))) * (A1 * (&12 * W * exp(e / &2 * Y)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(--(e * Y)) * exp(e / &2 * Y) = exp(--(e / &2 * Y))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(((&1 - b) * exp(--(e / &2 * X)) / (&4096 * A1 * &12 * W)) *
     exp(--(e * Y))) * (A1 * (&12 * W * exp(e / &2 * Y))) =
    (&1 - b) * (exp(--(e / &2 * X)) * (exp(--(e * Y)) * exp(e / &2 * Y))) /
    &4096`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `~(A1 = &0) /\ ~(W = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ARITH `&0 < &4096`]);;

let SIEGEL_ARITH_PRINCIPAL = prove
 (`!A1 R2 B C X Y e.
     exp(--(&2 * B)) * A1 <= R2 /\ &0 <= A1 /\
     B <= C + e / &2 * (X + Y)
     ==> (A1 * exp(--(&2 * C)) * exp(--(e * X))) * exp(--(e * Y)) <= R2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(--(&2 * B)) * A1` THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(a * b * c) * d = (b * c * d) * a:real`] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[GSYM REAL_EXP_ADD] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC);;

let RE_MUL3_REAL = prove
 (`!a b c. real a /\ real b /\ real c ==> Re(a * b * c) = Re a * Re b * Re c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (CONJUNCTS_THEN2
    (SUBST1_TAC o SYM) (SUBST1_TAC o SYM))) THEN
  REWRITE_TAC[GSYM CX_MUL; RE_CX]);;

let SIEGEL_FIXED = prove
 (`!q1 c1 b e.
     dirichlet_character q1 c1 /\ ~(c1 = chi_0 q1) /\ (!n. real(c1 n)) /\
     &7 / &8 <= b /\ b < &1 /\ &0 < e /\ &16 * (&1 - b) <= e /\
     (!q2 c2. dirichlet_character q2 c2 /\ ~(c2 = chi_0 q2) /\
              (!n. real(c2 n)) /\ ~((\n. c1 n * c2 n) = chi_0(q1 * q2))
              ==> Re(zeta(Cx b) * dseries c1 (Cx b) * dseries c2 (Cx b) *
                     dseries (\n. c1 n * c2 n) (Cx b)) <= &0)
     ==> ?kap. &0 < kap /\
               !q2 c2. dirichlet_character q2 c2 /\ ~(c2 = chi_0 q2) /\
                       (!n. real(c2 n))
                       ==> kap * exp(--(e * log(&q2))) <=
                           Re(dseries c2 (Cx(&1)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`q1:num`; `c1:num->complex`] LFUN_1_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `A1 = Re(dseries c1 (Cx(&1)))` THEN
  MP_TAC(SPECL [`q1:num`; `c1:num->complex`]
    DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `e / &2` PRIME_DIVISOR_RECIP_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_THEN `Cb:real` (LABEL_TAC "cb"))]
     THEN
  ABBREV_TAC `X = log(&q1)` THEN
  SUBGOAL_THEN `&0 <= X` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN MATCH_MP_TAC LOG_POS THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&3)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 / e` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &2`]; ALL_TAC] THEN
  ABBREV_TAC `W = &1 + log(&3) + X + &2 / e` THEN
  SUBGOAL_THEN `&0 < W` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `min ((&1 - b) * exp(--(e / &2 * X)) / (&4096 * A1 * &12 * W))
                  (A1 * exp(--(&2 * Cb)) * exp(--(e * X)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
      REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[REAL_EXP_POS_LT]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`q2:num`; `c2:num->complex`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`q2:num`; `c2:num->complex`]
    DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `Y = log(&q2)` THEN
  SUBGOAL_THEN `&0 <= Y` ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN MATCH_MP_TAC LOG_POS THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&q1 * &q2) = X + Y` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN MATCH_MP_TAC LOG_MUL THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `(\n. (c1:num->complex) n * c2 n) = chi_0(q1 * q2)` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(A1 * exp(--(&2 * Cb)) * exp(--(e * X))) * exp(--(e * Y))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC SIEGEL_ARITH_PRINCIPAL THEN
    EXISTS_TAC `sum {p | prime p /\ p divides (q1 * q2)}
                    (\p. inv(&p - &1))` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONJ_TAC THENL
     [EXPAND_TAC "A1" THEN MATCH_MP_TAC LFUN_1_PRINCIPAL_PRODUCT THEN
      ASM_REWRITE_TAC[];
      USE_THEN "cb" (MP_TAC o SPEC `q1 * q2:num`) THEN
      REWRITE_TAC[MULT_EQ_0; GSYM REAL_OF_NUM_MUL] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `((&1 - b) * exp(--(e / &2 * X)) / (&4096 * A1 * &12 * W)) *
              exp(--(e * Y))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`q1:num`; `q2:num`; `c1:num->complex`; `c2:num->complex`]
    DIRICHLET_CHARACTER_MUL_MOD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!n. real((c1:num->complex) n * c2 n)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_MUL]; ALL_TAC] THEN
  MP_TAC(SPECL [`q1 * q2:num`; `\n. (c1:num->complex) n * c2 n`]
    LFUN_1_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`q2:num`; `c2:num->complex`] LFUN_1_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC SIEGEL_ARITH_NONPRINCIPAL THEN
  MAP_EVERY EXISTS_TAC
   [`Re(dseries (\n. (c1:num->complex) n * c2 n) (Cx(&1)))`;
    `exp(--(&8 * (&1 - b) * (X + Y)))`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(SPECL [`q1:num`; `q2:num`; `c1:num->complex`; `c2:num->complex`;
                  `b:real`] SIEGEL_LAMBDA_LOWER) THEN
    ASM_SIMP_TAC[RE_MUL3_REAL] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `q2:num` THEN
    ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN
    SUBGOAL_THEN `&0 <= (e / &2 - &8 * (&1 - b)) * (X + Y)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(dseries (\n. (c1:num->complex) n * c2 n) (Cx(&1)))` THEN
  CONJ_TAC THENL
   [MP_TAC(SPEC `dseries (\n. (c1:num->complex) n * c2 n) (Cx(&1))`
      COMPLEX_NORM_GE_RE_IM) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&12 * (&1 + log(&3 * &(q1 * q2)))` THEN
  CONJ_TAC THENL [MATCH_MP_TAC LFUN_1_UPPER THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  SUBGOAL_THEN `log(&3 * &q1 * &q2) = log(&3) + X + Y` SUBST1_TAC THENL
   [SUBGOAL_THEN `&0 < &q1 * &q2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_MUL; REAL_ARITH `&0 < &3`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`e / &2`; `Y:real`] LE_EXP_DIV) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exp(e / &2 * Y) / (e / &2) = &2 / e * exp(e / &2 * Y)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < e` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MP_TAC(SPEC `e / &2 * Y` REAL_EXP_LE_X) THEN
  SUBGOAL_THEN `&0 <= e / &2 * Y` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 + log(&3) + X) * (exp(e / &2 * Y) - &1)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN
    MP_TAC(SPEC `e / &2 * Y` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXPAND_TAC "W" THEN REAL_ARITH_TAC);;

let SIEGEL = prove
 (`!e. &0 < e
       ==> ?kap. &0 < kap /\
                 !q c. dirichlet_character q c /\ ~(c = chi_0 q) /\
                       (!n. real(c n))
                       ==> kap * exp(--(e * log(&q))) <=
                           Re(dseries c (Cx(&1)))`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_THEN `d0:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    ASSUME_TAC (LABEL_TAC "nz"))) NEARZETA_NEAR_1 THEN
  ABBREV_TAC `eta = min d0 (e / &16)` THEN
  SUBGOAL_THEN `&0 < eta /\ eta <= &1 / &8 /\ eta <= d0 /\ &16 * eta <= e`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC
   `?q1 c1 b1. dirichlet_character q1 c1 /\ ~(c1 = chi_0 q1) /\
               (!n. real(c1 n)) /\ &1 - eta <= b1 /\ b1 < &1 /\
               dseries c1 (Cx b1) = Cx(&0)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `q1:num` (X_CHOOSE_THEN `c1:num->complex`
      (X_CHOOSE_THEN `b1:real` STRIP_ASSUME_TAC))) THEN
    MATCH_MP_TAC SIEGEL_FIXED THEN
    MAP_EVERY EXISTS_TAC [`q1:num`; `c1:num->complex`; `b1:real`] THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO; RE_CX;
                    REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC
   `?q1 c1. dirichlet_character q1 c1 /\ ~(c1 = chi_0 q1) /\
            (!n. real(c1 n))` THENL
   [ALL_TAC;
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN ASM_MESON_TAC[]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `q1:num` (X_CHOOSE_THEN `c1:num->complex`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!q c. dirichlet_character q c /\ ~(c = chi_0 q) /\ (!n. real(c n))
          ==> &0 < Re(dseries c (Cx(&1 - eta)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LFUN_POS_LEFT THEN
    EXISTS_TAC `q:num` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SIEGEL_FIXED THEN
  MAP_EVERY EXISTS_TAC [`q1:num`; `c1:num->complex`; `&1 - eta`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`q2:num`; `c2:num->complex`] THEN STRIP_TAC THEN
  MATCH_MP_TAC SIEGEL_F_NONPOS THEN
  MAP_EVERY EXISTS_TAC [`q1:num`; `q2:num`] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`q1:num`; `q2:num`; `c1:num->complex`; `c2:num->complex`]
    DIRICHLET_CHARACTER_MUL_MOD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    USE_THEN "nz" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `q1:num` THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `q2:num` THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `q1 * q2:num` THEN
    ASM_SIMP_TAC[REAL_MUL]]);;
