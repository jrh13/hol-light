(* ========================================================================= *)
(* Two logarithms, the Laurent bound: the analytic upper bound for           *)
(* the binomial interpolation determinant (mu = 1).                          *)
(*                                                                           *)
(* Purpose: M. Laurent, Linear forms in two logarithms and interpolation     *)
(* determinants II, Acta Arith. 133 (2008), Lemma 2 at mu = 1 (= Laurent,    *)
(* Acta Arith. 66 (1994), Lemmas 6-8), real case: the centred binomial       *)
(* interpolation determinant is bounded by 2^N N! rho^(-N(N-1)/2)            *)
(* prod (rho b / 2)^k / k! times the column factor and                       *)
(* exp(rho (G1 l1 + G2 l2)), where G1, G2 bound the oscillation sums along   *)
(* permutations (the g-lemma). The interpolation lemma                       *)
(* INTERPOLATION_DETERMINANT_PERTURBED_PERM (Baker/twolog_interp.ml) needs   *)
(* only a bound for the products along permutations on the circle |w| = rho, *)
(* instead of row maxima.                                                    *)
(*                                                                           *)
(* Main results: TWOLOG_LAURENT_ANALYTIC; helper names TL_LAURENT_INTERP_*.  *)
(*                                                                           *)
(* Uses: Baker/twolog_interp.ml (INTERPOLATION_DETERMINANT_PERTURBED_PERM),  *)
(* Baker/twolog_core.ml (TL_CORE_EXP_SUB_1_LE, TL_CORE_TH_NORM,              *)
(* TL_CORE_TH_ENTRY, TL_CORE_PH_CX, TL_PH_HOLOMORPHIC), Baker/twolog.ml      *)
(* (NSUM_NUMSEG_PRED_DIV), Baker/twolog_det.ml (CDET_CX),                    *)
(* Library/ring_det.ml (RING_DET_ROWS_MUL, RING_DET_COLUMNS_MUL),            *)
(* Library/ringtheory.ml (REAL_RING_PRODUCT), Baker/laurent_binom.ml         *)
(* (BINOM_RDET_ROW_CHANGE).                                                  *)
(* ========================================================================= *)

needs "Baker/twolog.ml";;
needs "Baker/laurent_binom.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Elementary facts for the analytic bound: the centred row indices          *)
(* lambda_i = (i - 1) DIV K - (L - 1) / 2 sum to 0 and are at most           *)
(* (L - 1) / 2 in absolute value, scaling of rows and columns of a real      *)
(* determinant, the triangular row change from binomials to centred powers,  *)
(* the splitting of the entries, and the bounds for the perturbation         *)
(* factors.                                                                  *)
(* ------------------------------------------------------------------------- *)

let TL_LAURENT_INTERP_SUM_LAMBDA = prove
 (`!K L. 1 <= K /\ 1 <= L
         ==> sum(1..K * L) (\i. &((i - 1) DIV K) - (&L - &1) / &2) = &0`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SUM_SUB_NUMSEG; SUM_CONST_NUMSEG; ADD_SUB] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUM_NUMSEG] THEN
  MP_TAC(SPECL [`K:num`; `L:num`] NSUM_NUMSEG_PRED_DIV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `real_of_num`) THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_MUL; REAL_OF_NUM_SUB] THEN
  REAL_ARITH_TAC);;

let TL_LAURENT_INTERP_LAMBDA_BOUND = prove
 (`!K L i. 1 <= K /\ i IN 1..K * L
           ==> abs(&((i - 1) DIV K) - (&L - &1) / &2) <= (&L - &1) / &2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(i - 1) DIV K < L` MP_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `1 <= K ==> ~(K = 0)`] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `a < b <=> a + 1 <= b`; GSYM REAL_OF_NUM_LE;
              GSYM REAL_OF_NUM_ADD] THEN
  MP_TAC(SPEC `(i - 1) DIV K` REAL_POS) THEN REAL_ARITH_TAC);;

let TL_LAURENT_INTERP_RDET_SCALE = prove
 (`!n (a:num->real) (b:num->real) (f:num->num->real).
     ring_det real_ring (1..n) (\i j. a i * b j * f i j) =
     product(1..n) a * product(1..n) b * ring_det real_ring (1..n) f`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `(\i j. (a:num->real) i * (b:num->real) j * (f:num->num->real) i j) =
    (\i j. a i * (f i j * b j))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; REAL_MUL_AC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`real_ring`; `1..n`; `a:num->real`;
                 `\i j. (f:num->num->real) i j * (b:num->real) j`]
         RING_DET_ROWS_MUL) THEN
  MP_TAC(ISPECL [`real_ring`; `1..n`; `b:num->real`; `f:num->num->real`]
         RING_DET_COLUMNS_MUL) THEN
  REWRITE_TAC[FINITE_NUMSEG; REAL_RING_CLAUSES; IN_UNIV; REAL_RING_PRODUCT] THEN
  DISCH_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let TL_LAURENT_INTERP_ENTRY = prove
 (`!l r s L l1 l2 b1 b2 eta.
     1 <= b2
     ==> exp(&l * (&r * l1 + &s * l2)) =
         exp((&l - (&L - &1) / &2) * l1 * eta) *
         exp((&L - &1) / &2 * (&r * l1 + &s * l2)) *
         exp(((&l - (&L - &1) / &2) * l1) * (&(r * b2 + s * b1) / &b2 - eta)) *
         exp((&l - (&L - &1) / &2) * &s * (&b2 * l2 - &b1 * l1) / &b2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `~(&b2 = &0)` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
  CONV_TAC REAL_FIELD);;

let TL_LAURENT_INTERP_CC_ZERO = prove
 (`!L S b2 Lam.
     1 <= L /\ 1 <= S /\ 1 <= b2 /\
     &(L * S) * abs Lam / (&2 * &b2) *
     exp(&(L * S) * abs Lam / (&2 * &b2)) = &0
     ==> Lam = &0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_ENTIRE; REAL_EXP_NZ; REAL_DIV_EQ_0; REAL_ABS_ZERO;
              REAL_OF_NUM_EQ; MULT_EQ_0; ARITH_EQ] THEN
  ARITH_TAC);;

let TL_LAURENT_INTERP_TH_BOUND = prove
 (`!lam s Lam b2 L S.
     1 <= b2 /\ abs lam <= (&L - &1) / &2 /\ s < S
     ==> abs(exp(lam * &s * Lam / &b2) - &1) <=
         abs(&(L * S) * abs Lam / (&2 * &b2) *
             exp(&(L * S) * abs Lam / (&2 * &b2)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &b2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &(L * S) * abs Lam / (&2 * &b2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_ABS_POS] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(lam * &s * Lam / &b2) <= &(L * S) * abs Lam / (&2 * &b2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_NUM] THEN
    TRANS_TAC REAL_LE_TRANS `(&L / &2 * &S) * (abs Lam / &b2)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN
        REWRITE_TAC[REAL_ABS_POS; REAL_POS; REAL_OF_NUM_LE] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_ABS_POS] THEN
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
      UNDISCH_TAC `&0 < &b2` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `abs(lam * &s * Lam / &b2) * exp(abs(lam * &s * Lam / &b2))` THEN
  REWRITE_TAC[TL_CORE_EXP_SUB_1_LE] THEN
  SUBGOAL_THEN
   `abs(&(L * S) * abs Lam / (&2 * &b2) *
        exp(&(L * S) * abs Lam / (&2 * &b2))) =
    (&(L * S) * abs Lam / (&2 * &b2)) * exp(&(L * S) * abs Lam / (&2 * &b2))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_MUL_ASSOC; REAL_ABS_REFL] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[REAL_EXP_POS_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_REWRITE_TAC[REAL_ABS_POS; REAL_EXP_POS_LE; REAL_EXP_MONO_LE]);;

(* ------------------------------------------------------------------------- *)
(* The products along permutations on the circle |w| = rho: the points       *)
(* x_j / b2 - eta lie in [-eta, eta], and the oscillation sums along a       *)
(* permutation are bounded by G1 + (b1 / b2) G2 (centring and the            *)
(* bounds G1, G2 of the g-lemma).                                            *)
(* ------------------------------------------------------------------------- *)

let TL_LAURENT_INTERP_ZETA_BOUND = prove
 (`!b1 b2 R S r s.
     1 <= b2 /\ r < R /\ s < S
     ==> abs(&(r * b2 + s * b1) / &b2 -
             &((R - 1) * b2 + (S - 1) * b1) / (&2 * &b2)) <=
         &((R - 1) * b2 + (S - 1) * b1) / (&2 * &b2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &b2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r * b2 + s * b1 <= (R - 1) * b2 + (S - 1) * b1` MP_TAC THENL
   [MATCH_MP_TAC LE_ADD2 THEN REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
  MP_TAC(SPEC `r * b2 + s * b1` REAL_POS) THEN
  SPEC_TAC(`&((R - 1) * b2 + (S - 1) * b1):real`,`X:real`) THEN
  SPEC_TAC(`&(r * b2 + s * b1):real`,`x:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= u /\ u <= &2 * e ==> abs(u - e) <= e`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * X / (&2 * &b2) = X / &b2` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < &b2` THEN CONV_TAC REAL_FIELD;
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ]]);;

let TL_LAURENT_INTERP_OSC = prove
 (`!K L N b1 b2 eta (rr:num->num) (ss:num->num) (p:num->num).
     1 <= K /\ 1 <= L /\ N = K * L /\ 1 <= b2
     ==> sum(1..N) (\i. (&((i - 1) DIV K) - (&L - &1) / &2) *
                        (&(rr(p i) * b2 + ss(p i) * b1) / &b2 - eta)) =
         sum(1..N) (\i. (&((i - 1) DIV K) - (&L - &1) / &2) * &(rr(p i))) +
         &b1 / &b2 *
         sum(1..N) (\i. (&((i - 1) DIV K) - (&L - &1) / &2) * &(ss(p i)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(&b2 = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `sum(1..N) (\i. (&((i - 1) DIV K) - (&L - &1) / &2) *
                   &((rr:num->num)((p:num->num) i)) +
                   &b1 / &b2 *
                   ((&((i - 1) DIV K) - (&L - &1) / &2) *
                    &((ss:num->num)(p i))) -
                   eta * (&((i - 1) DIV K) - (&L - &1) / &2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
    UNDISCH_TAC `~(&b2 = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG] THEN ONCE_REWRITE_TAC[SUM_SUB_NUMSEG] THEN
  REWRITE_TAC[SUM_LMUL] THEN
  MP_TAC(SPECL [`K:num`; `L:num`] TL_LAURENT_INTERP_SUM_LAMBDA) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check
    (fun th -> concl th = `N = K * L`)) THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN REAL_ARITH_TAC);;

let TL_LAURENT_INTERP_EXP_ARITH = prove
 (`!l1 l2 u A C G1 G2 rho b1 b2.
     &0 <= l1 /\ &0 < b2 /\ &0 <= b1 /\ b1 * l1 <= b2 * l2 /\
     abs u <= rho /\ abs A <= G1 /\ abs C <= G2
     ==> (l1 * u) * (A + b1 / b2 * C) <= rho * (G1 * l1 + G2 * l2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= b1 / b2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `b1 / b2 * l1 <= l2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `(a:real) / b * c = (a * c) / b`] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(A + b1 / b2 * C) <= G1 + b1 / b2 * G2` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `abs(A:real) <= G1 /\ abs(y:real) <= z ==> abs(A + y) <= G1 + z`) THEN
    ASM_REWRITE_TAC[REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= rho /\ &0 <= G2` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `l1 * rho * (G1 + b1 / b2 * G2)` THEN CONJ_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `abs((l1 * u) * (A + b1 / b2 * C))` THEN
    REWRITE_TAC[REAL_ABS_LE] THEN REWRITE_TAC[REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `rho * (G1 * l1 + G2 * (b1 / b2 * l1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_LADD] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

let TL_LAURENT_INTERP_PERM_BOUND = prove
 (`!b1 b2 K L R S N (rr:num->num) (ss:num->num) l1 l2 rho G1 G2 eta
    (w:complex) (p:num->num).
     1 <= b2 /\ 1 <= K /\ 1 <= L /\ N = K * L /\
     (!j. j IN 1..N ==> rr j < R /\ ss j < S) /\
     &((R - 1) * b2 + (S - 1) * b1) / (&2 * &b2) = eta /\
     &0 <= l1 /\ &b1 * l1 <= &b2 * l2 /\
     abs(sum(1..N) (\i. (&((i - 1) DIV K) - (&L - &1) / &2) * &(rr(p i))))
     <= G1 /\
     abs(sum(1..N) (\i. (&((i - 1) DIV K) - (&L - &1) / &2) * &(ss(p i))))
     <= G2 /\
     norm w = rho /\ p permutes 1..N
     ==> product(1..N)
           (\i. norm((w * Cx(&(rr(p i) * b2 + ss(p i) * b1) / &b2 - eta)) pow
                     ((i - 1) MOD K) *
                     cexp(Cx((&((i - 1) DIV K) - (&L - &1) / &2) * l1) *
                          w * Cx(&(rr(p i) * b2 + ss(p i) * b1) / &b2 - eta))))
         <= product(1..N) (\i. (rho * eta) pow ((i - 1) MOD K)) *
            exp(rho * (G1 * l1 + G2 * l2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= rho` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check
     (fun th -> concl th = `norm(w:complex) = rho`)) THEN
    REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &b2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN UNDISCH_TAC `1 <= b2` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW; NORM_CEXP; RE_MUL_CX;
              COMPLEX_NORM_CX] THEN
  FIRST_ASSUM(SUBST1_TAC o check
   (fun th -> concl th = `norm(w:complex) = rho`)) THEN
  REWRITE_TAC[PRODUCT_MUL_NUMSEG] THEN
  SIMP_TAC[GSYM REAL_EXP_SUM; FINITE_NUMSEG] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[REAL_ABS_POS];
    MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    SUBGOAL_THEN `(p:num->num) i IN 1..N` ASSUME_TAC THENL
     [ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG]; ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 <= rho * abs(&((rr:num->num)((p:num->num) i) * b2 +
                        (ss:num->num)(p i) * b1) / &b2 - eta)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    EXPAND_TAC "eta" THEN MATCH_MP_TAC TL_LAURENT_INTERP_ZETA_BOUND THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[REAL_EXP_POS_LE];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE] THEN
  SUBGOAL_THEN
   `sum(1..N) (\i. ((&((i - 1) DIV K) - (&L - &1) / &2) * l1) * Re w *
                   (&((rr:num->num)((p:num->num) i) * b2 +
                      (ss:num->num)(p i) * b1) / &b2 - eta)) =
    (l1 * Re w) *
    sum(1..N) (\i. (&((i - 1) DIV K) - (&L - &1) / &2) *
                   (&(rr(p i) * b2 + ss(p i) * b1) / &b2 - eta))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`K:num`; `L:num`; `N:num`; `b1:num`; `b2:num`; `eta:real`;
                `rr:num->num`; `ss:num->num`; `p:num->num`]
         TL_LAURENT_INTERP_OSC) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC TL_LAURENT_INTERP_EXP_ARITH THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[REAL_POS];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM(SUBST1_TAC o SYM o check
     (fun th -> concl th = `norm(w:complex) = rho`)) THEN
    REWRITE_TAC[COMPLEX_NORM_GE_RE_IM];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC]);;

let TL_LAURENT_INTERP_PRODUCT_SPLIT = prove
 (`!N K b2 rho X eta.
     1 <= b2 /\ &X / (&2 * &b2) = eta
     ==> product(1..N) (\i. (rho * &X / &2) pow ((i - 1) MOD K) /
                            &(FACT((i - 1) MOD K))) =
         product(1..N) (\i. &b2 pow ((i - 1) MOD K) /
                            &(FACT((i - 1) MOD K))) *
         product(1..N) (\i. (rho * eta) pow ((i - 1) MOD K))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM PRODUCT_MUL_NUMSEG] THEN
  MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  SUBGOAL_THEN `rho * &X / &2 = &b2 * (rho * eta)` SUBST1_TAC THENL
   [EXPAND_TAC "eta" THEN
    SUBGOAL_THEN `~(&b2 = &0)` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; CONV_TAC REAL_FIELD];
    REWRITE_TAC[REAL_POW_MUL; real_div; REAL_MUL_AC]]);;

(* ------------------------------------------------------------------------- *)
(* The interpolation lemma for the centred matrix: entries                   *)
(* z_j^k_i exp(lambda_i l1 z_j) exp(lambda_i s_j Lam / b2) with the centred  *)
(* points z_j = x_j / b2 - eta, |z_j| <= eta = X / (2 b2) (Laurent 1994,     *)
(* Lemmas 7-8 at mu = 1, real case).                                         *)
(* ------------------------------------------------------------------------- *)

let TL_LAURENT_INTERP_CENTRED_BOUND = prove
 (`!b1 b2 K L R S N (rr:num->num) (ss:num->num) l1 l2 rho G1 G2 eta.
     1 <= b2 /\ 1 <= K /\ 1 <= L /\ 1 <= S /\ N = K * L /\
     (!j. j IN 1..N ==> rr j < R /\ ss j < S) /\
     &((R - 1) * b2 + (S - 1) * b1) / (&2 * &b2) = eta /\
     &0 <= l1 /\ &b1 * l1 <= &b2 * l2 /\ &1 <= rho /\
     (!p. p permutes 1..N
          ==> abs(sum(1..N) (\i. (&((i - 1) DIV K) - (&L - &1) / &2) *
                                 &(rr(p i)))) <= G1) /\
     (!p. p permutes 1..N
          ==> abs(sum(1..N) (\i. (&((i - 1) DIV K) - (&L - &1) / &2) *
                                 &(ss(p i)))) <= G2) /\
     &(L * S) * abs(&b2 * l2 - &b1 * l1) / (&2 * &b2) *
     exp(&(L * S) * abs(&b2 * l2 - &b1 * l1) / (&2 * &b2)) <= inv(rho pow N)
     ==> abs(ring_det real_ring (1..N)
               (\i j. (&(rr j * b2 + ss j * b1) / &b2 - eta)
                      pow ((i - 1) MOD K) *
                      exp(((&((i - 1) DIV K) - (&L - &1) / &2) * l1) *
                          (&(rr j * b2 + ss j * b1) / &b2 - eta)) *
                      exp((&((i - 1) DIV K) - (&L - &1) / &2) *
                          &(ss j) * (&b2 * l2 - &b1 * l1) / &b2))) <=
         &2 pow N * &(FACT N) * inv(rho pow ((N * (N - 1)) DIV 2)) *
         product(1..N) (\i. (rho * eta) pow ((i - 1) MOD K)) *
         exp(rho * (G1 * l1 + G2 * l2))`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `cc = &(L * S) * abs(&b2 * l2 - &b1 * l1) / (&2 * &b2) *
                   exp(&(L * S) * abs(&b2 * l2 - &b1 * l1) / (&2 * &b2))` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= cc` ASSUME_TAC THENL
   [EXPAND_TAC "cc" THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
   [`N:num`;
    `\i:num z:complex. z pow ((i - 1) MOD K) *
         cexp(Cx((&((i - 1) DIV K) - (&L - &1) / &2) * l1) * z)`;
    `\i:num j:num. Cx(if cc = &0 then &0
         else (exp((&((i - 1) DIV K) - (&L - &1) / &2) *
                   &((ss:num->num) j) *
                   (&b2 * l2 - &b1 * l1) / &b2) - &1) / cc)`;
    `\j:num. Cx(&((rr:num->num) j * b2 + (ss:num->num) j * b1) / &b2 -
                eta)`;
    `rho:real`;
    `product(1..N) (\i. (rho * eta) pow ((i - 1) MOD K)) *
     exp(rho * (G1 * l1 + G2 * l2))`;
    `Cx cc`] INTERPOLATION_DETERMINANT_PERTURBED_PERM)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[TL_PH_HOLOMORPHIC];
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      MATCH_MP_TAC TL_CORE_TH_NORM THEN EXPAND_TAC "cc" THEN
      MATCH_MP_TAC TL_LAURENT_INTERP_TH_BOUND THEN
      REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC TL_LAURENT_INTERP_LAMBDA_BOUND THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check
          (fun th -> concl th = `N = K * L`)) THEN
        FIRST_ASSUM ACCEPT_TAC;
        ASM_MESON_TAC[]];
      MAP_EVERY X_GEN_TAC [`w:complex`; `p:num->num`] THEN STRIP_TAC THEN
      MP_TAC(SPECL [`b1:num`; `b2:num`; `K:num`; `L:num`; `R:num`;
                    `S:num`; `N:num`; `rr:num->num`; `ss:num->num`;
                    `l1:real`; `l2:real`; `rho:real`; `G1:real`;
                    `G2:real`; `eta:real`; `w:complex`; `p:num->num`]
             TL_LAURENT_INTERP_PERM_BOUND) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
        FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        DISCH_THEN ACCEPT_TAC];
      REWRITE_TAC[COMPLEX_NORM_CX] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(x:real) = y ==> y <= z ==> x <= z`) THEN
  REWRITE_TAC[GSYM COMPLEX_NORM_CX; GSYM CDET_CX] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
  REWRITE_TAC[TL_CORE_PH_CX] THEN
  MP_TAC(SPECL
   [`cc:real`;
    `exp((&((i - 1) DIV K) - (&L - &1) / &2) * &((ss:num->num) j) *
         (&b2 * l2 - &b1 * l1) / &b2)`] TL_CORE_TH_ENTRY) THEN
  ANTS_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(SPECL [`L:num`; `S:num`; `b2:num`; `&b2 * l2 - &b1 * l1`]
           TL_LAURENT_INTERP_CC_ZERO) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(fun th -> REWRITE_TAC[th; real_div; REAL_MUL_LZERO;
                                       REAL_MUL_RZERO; REAL_EXP_0])];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM CX_MUL; CX_INJ; REAL_MUL_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* The analytic upper bound for the binomial interpolation determinant       *)
(* (Laurent 2008, Lemma 2 at mu = 1, real case): triangular row change       *)
(* to (b2^k / k!) (x / b2 - eta)^k, column factors                           *)
(* exp((L - 1) / 2 (r l1 + s l2)), row factors of product 1, and the         *)
(* interpolation lemma for the centred matrix.                               *)
(* ------------------------------------------------------------------------- *)

let TWOLOG_LAURENT_ANALYTIC = prove
 (`!b1 b2 K L R S N (rr:num->num) (ss:num->num) l1 l2 rho G1 G2.
     1 <= b1 /\ 1 <= b2 /\ 1 <= K /\ 1 <= L /\ 2 <= R /\ 1 <= S /\
     N = K * L /\
     (!j. j IN 1..N ==> rr j < R /\ ss j < S) /\
     &0 <= l1 /\ &0 <= l2 /\ &b1 * l1 <= &b2 * l2 /\ &1 < rho /\
     (!p. p permutes 1..N
          ==> abs(sum(1..N) (\i. (&((i - 1) DIV K) - (&L - &1) / &2) *
                                 &(rr(p i)))) <= G1) /\
     (!p. p permutes 1..N
          ==> abs(sum(1..N) (\i. (&((i - 1) DIV K) - (&L - &1) / &2) *
                                 &(ss(p i)))) <= G2) /\
     &(L * S) * abs(&b2 * l2 - &b1 * l1) / (&2 * &b2) *
     exp(&(L * S) * abs(&b2 * l2 - &b1 * l1) / (&2 * &b2)) <= inv(rho pow N)
     ==> abs(ring_det real_ring (1..N)
               (\i j. &(binom(rr j * b2 + ss j * b1,(i - 1) MOD K)) *
                      exp(&((i - 1) DIV K) *
                          (&(rr j) * l1 + &(ss j) * l2)))) <=
         &2 pow N * &(FACT N) * inv(rho pow ((N * (N - 1)) DIV 2)) *
         product(1..N)
           (\i. (rho * &((R - 1) * b2 + (S - 1) * b1) / &2)
                pow ((i - 1) MOD K) / &(FACT((i - 1) MOD K))) *
         exp((&L - &1) / &2 * (&(nsum(1..N) rr) * l1 + &(nsum(1..N) ss) * l2) +
             rho * (G1 * l1 + G2 * l2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `eta = &((R - 1) * b2 + (S - 1) * b1) / (&2 * &b2)` THEN
  MP_TAC(BETA_RULE(ISPECL
   [`K:num`; `L:num`; `b2:num`; `eta:real`;
    `\j. (rr:num->num) j * b2 + (ss:num->num) j * b1`;
    `\l j. exp(&l * (&((rr:num->num) j) * l1 + &((ss:num->num) j) * l2))`]
   BINOM_RDET_ROW_CHANGE)) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `N = K * L`)) THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `ring_det real_ring (1..N)
      (\i j. (&((rr:num->num) j * b2 + (ss:num->num) j * b1) / &b2 -
              eta) pow ((i - 1) MOD K) *
             exp(&((i - 1) DIV K) * (&(rr j) * l1 + &(ss j) * l2))) =
    product(1..N) (\i. exp((&((i - 1) DIV K) - (&L - &1) / &2) * l1 * eta)) *
    product(1..N) (\j. exp((&L - &1) / &2 *
                           (&((rr:num->num) j) * l1 +
                            &((ss:num->num) j) * l2))) *
    ring_det real_ring (1..N)
      (\i j. (&(rr j * b2 + ss j * b1) / &b2 - eta) pow ((i - 1) MOD K) *
             exp(((&((i - 1) DIV K) - (&L - &1) / &2) * l1) *
                 (&(rr j * b2 + ss j * b1) / &b2 - eta)) *
             exp((&((i - 1) DIV K) - (&L - &1) / &2) * &(ss j) *
                 (&b2 * l2 - &b1 * l1) / &b2))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM TL_LAURENT_INTERP_RDET_SCALE] THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
    MP_TAC(SPECL [`(i - 1) DIV K`; `(rr:num->num) j`; `(ss:num->num) j`;
                  `L:num`; `l1:real`; `l2:real`; `b1:num`; `b2:num`;
                  `eta:real`] TL_LAURENT_INTERP_ENTRY) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[REAL_MUL_AC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `product(1..N) (\i. exp((&((i - 1) DIV K) - (&L - &1) / &2) * l1 * eta)) =
    &1`
  SUBST1_TAC THENL
   [SIMP_TAC[GSYM REAL_EXP_SUM; FINITE_NUMSEG; SUM_RMUL] THEN
    MP_TAC(SPECL [`K:num`; `L:num`] TL_LAURENT_INTERP_SUM_LAMBDA) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check
      (fun th -> concl th = `N = K * L`)) THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_MUL_LZERO; REAL_EXP_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `product(1..N) (\j. exp((&L - &1) / &2 *
                           (&((rr:num->num) j) * l1 +
                            &((ss:num->num) j) * l2))) =
    exp((&L - &1) / &2 * (&(nsum(1..N) rr) * l1 + &(nsum(1..N) ss) * l2))`
  SUBST1_TAC THENL
   [SIMP_TAC[GSYM REAL_EXP_SUM; FINITE_NUMSEG] THEN AP_TERM_TAC THEN
    REWRITE_TAC[SUM_LMUL; SUM_ADD_NUMSEG; SUM_RMUL; REAL_OF_NUM_SUM_NUMSEG];
    ALL_TAC] THEN
  MP_TAC(SPECL [`b1:num`; `b2:num`; `K:num`; `L:num`; `R:num`; `S:num`;
                `N:num`; `rr:num->num`; `ss:num->num`; `l1:real`; `l2:real`;
                `rho:real`; `G1:real`; `G2:real`; `eta:real`]
         TL_LAURENT_INTERP_CENTRED_BOUND) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_TAC] THEN
  MP_TAC(SPECL [`N:num`; `K:num`; `b2:num`; `rho:real`;
                `(R - 1) * b2 + (S - 1) * b1`; `eta:real`]
         TL_LAURENT_INTERP_PRODUCT_SPLIT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[REAL_EXP_ADD] THEN
  SUBGOAL_THEN
   `&0 <= product(1..N) (\i. &b2 pow ((i - 1) MOD K) /
                             &(FACT((i - 1) MOD K)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
    SIMP_TAC[REAL_POW_LE; REAL_POS];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM; REAL_ABS_EXP; REAL_MUL_LID] THEN
  SUBGOAL_THEN
   `abs(product(1..N) (\i. &b2 pow ((i - 1) MOD K) /
                           &(FACT((i - 1) MOD K)))) =
    product(1..N) (\i. &b2 pow ((i - 1) MOD K) / &(FACT((i - 1) MOD K)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_REFL] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `product(1..N) (\i. &b2 pow ((i - 1) MOD K) / &(FACT((i - 1) MOD K))) *
    exp((&L - &1) / &2 * (&(nsum(1..N) rr) * l1 + &(nsum(1..N) ss) * l2)) *
    (&2 pow N * &(FACT N) * inv(rho pow ((N * (N - 1)) DIV 2)) *
     product(1..N) (\i. (rho * eta) pow ((i - 1) MOD K)) *
     exp(rho * (G1 * l1 + G2 * l2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[REAL_MUL_AC]]);;
