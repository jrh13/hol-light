(* ========================================================================= *)
(* Two logarithms: the interpolation determinant argument.                   *)
(*                                                                           *)
(* Purpose: Theorem 11.4 of Y. Bugeaud, Linear Forms in Logarithms and       *)
(* Applications (EMS 2018) in the rational case D = 1 (powers of b2 r + b1 s *)
(* instead of binomial coefficients), with the non-vanishing of the chosen   *)
(* N x N determinant as a hypothesis (supplied in Baker/twolog.ml by         *)
(* TWOLOG_ZERO_MINOR of Baker/twolog_zero.ml).                               *)
(*                                                                           *)
(* Main results: TWOLOG_CORE_PARAMETRIC, from TL_CORE_ANALYTIC (upper bound  *)
(* for the determinant by INTERPOLATION_DETERMINANT_PERTURBED) and           *)
(* TL_CORE_INTEGRAL (the determinant times a power of q1 and q2 is a         *)
(* non-zero integer, so at least 1 in absolute value).                       *)
(*                                                                           *)
(* Uses: Baker/twolog_det.ml (CDET_CX, RDET_INTEGER_COLUMNS),                *)
(* Baker/twolog_interp.ml (INTERPOLATION_DETERMINANT_PERTURBED),             *)
(* REAL_ABS_INTEGER_LEMMA of Library/floor.ml.                               *)
(* ========================================================================= *)

needs "Baker/twolog_interp.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Elementary facts: integrality of (p/q)^a q^b for a <= b, bounds for       *)
(* |exp t - 1|, the entries of the interpolation matrix as products of       *)
(* exponentials, and holomorphy of z^k exp(c z).                             *)
(* ------------------------------------------------------------------------- *)

let TL_INTEGER_RATIO_POW = prove
 (`!p q a b. 1 <= q /\ a <= b ==> integer((&p / &q) pow a * &q pow b)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:num` SUBST1_TAC o GEN_REWRITE_RULE I
    [LE_EXISTS]) THEN
  SUBGOAL_THEN `~(&q = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_POW_DIV; REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_POW_NZ] THEN
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; INTEGER_CLOSED]);;

let TL_EXP_SUB_1_ABS = prove
 (`!t. abs(exp t - &1) <= exp(abs t) - &1`,
  GEN_TAC THEN ASM_CASES_TAC `&0 <= t` THENL
   [ASM_SIMP_TAC[REAL_ARITH `&0 <= t ==> abs t = t`] THEN
    MP_TAC(SPEC `t:real` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_ARITH `~(&0 <= t) ==> abs t = --t`] THEN
    MP_TAC(SPEC `t:real` REAL_EXP_LE_X) THEN
    MP_TAC(SPEC `--t:real` REAL_EXP_LE_X) THEN
    MP_TAC(SPEC `t:real` REAL_EXP_POS_LT) THEN
    MP_TAC(SPECL [`t:real`; `&0`] REAL_EXP_MONO_LT) THEN
    REWRITE_TAC[REAL_EXP_0] THEN ASM_REAL_ARITH_TAC]);;

let TL_ENTRY_EXP = prove
 (`!p1 q1 p2 q2 b1 b2 l r s.
     1 <= p1 /\ 1 <= q1 /\ 1 <= p2 /\ 1 <= q2 /\ 1 <= b2
     ==> (&p1 / &q1) pow (l * r) * (&p2 / &q2) pow (l * s) =
         exp(&l * log(&p1 / &q1) * &(r * b2 + s * b1) / &b2) *
         exp(&l * &s * (&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1)) / &b2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &p1 / &q1 /\ &0 < &p2 / &q2 /\ ~(&b2 = &0)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LT_DIV) THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x n. &0 < x ==> x pow n = exp(&n * log x)` ASSUME_TAC THENL
   [SIMP_TAC[REAL_EXP_N; EXP_LOG]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
  UNDISCH_TAC `~(&b2 = &0)` THEN CONV_TAC REAL_FIELD);;

let TL_PH_HOLOMORPHIC = prove
 (`!k c. (\z. z pow k * cexp(Cx c * z)) holomorphic_on (:complex)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HOLOMORPHIC_ON_DIFFERENTIABLE; IN_UNIV] THEN
  GEN_TAC THEN COMPLEX_DIFFERENTIABLE_TAC);;

(* ------------------------------------------------------------------------- *)
(* Further helpers for the main argument.                                    *)
(* ------------------------------------------------------------------------- *)

let TL_CORE_EXP_SUB_1_LE = prove
 (`!t. abs(exp t - &1) <= abs t * exp(abs t)`,
  GEN_TAC THEN TRANS_TAC REAL_LE_TRANS `exp(abs t) - &1` THEN
  REWRITE_TAC[TL_EXP_SUB_1_ABS] THEN
  MP_TAC(SPECL [`exp(abs t)`; `&1 - abs t`; `exp(--abs t)`] REAL_LE_LMUL) THEN
  REWRITE_TAC[REAL_EXP_NEG_MUL; REAL_EXP_POS_LE] THEN
  MP_TAC(SPEC `--abs t` REAL_EXP_LE_X) THEN REAL_ARITH_TAC);;

let TL_CORE_TH_BOUND = prove
 (`!Lam b2 L S l s.
     1 <= b2 /\ l < L /\ s < S
     ==> abs(exp(&l * &s * Lam / &b2) - &1) <=
         abs(Lam * &(L * S) * exp(&(L * S) * abs Lam / &b2) / &b2)`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS
   `abs(&l * &s * Lam / &b2) * exp(abs(&l * &s * Lam / &b2))` THEN
  REWRITE_TAC[TL_CORE_EXP_SUB_1_LE] THEN
  SUBGOAL_THEN `abs(&l * &s * Lam / &b2) <= &(L * S) * abs Lam / &b2`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_NUM] THEN
    REWRITE_TAC[real_div; GSYM REAL_OF_NUM_MUL; REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    SIMP_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(Lam * &(L * S) * exp(&(L * S) * abs Lam / &b2) / &b2) =
    (&(L * S) * abs Lam / &b2) * exp(&(L * S) * abs Lam / &b2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_NUM; REAL_ABS_EXP] THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_REWRITE_TAC[REAL_ABS_POS; REAL_EXP_POS_LE; REAL_EXP_MONO_LE]);;

let TL_CORE_TH_NORM = prove
 (`!c E. abs(E - &1) <= abs c
         ==> norm(Cx(if c = &0 then &0 else (E - &1) / c)) <= &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[COMPLEX_NORM_CX] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_ABS_NUM; REAL_POS] THEN
  REWRITE_TAC[REAL_ABS_DIV] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; GSYM REAL_ABS_NZ; REAL_MUL_LID]);;

let TL_CORE_TH_ENTRY = prove
 (`!c E. (c = &0 ==> E = &1)
         ==> Cx(&1) + Cx c * Cx(if c = &0 then &0 else (E - &1) / c) = Cx E`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM CX_MUL; GSYM CX_ADD; CX_INJ] THEN
  ASM_CASES_TAC `c = &0` THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(c = &0)` THEN CONV_TAC REAL_FIELD]);;

let TL_CORE_PH_CX = prove
 (`!x k a. Cx x pow k * cexp(Cx a * Cx x) = Cx(x pow k * exp(a * x))`,
  REWRITE_TAC[CX_MUL; CX_POW; CX_EXP]);;

let TL_CORE_PH_NORM_BOUND = prove
 (`!k l a B X z.
     norm z <= B /\ abs a * B <= X
     ==> norm(z pow k * cexp(Cx(&l * a) * z)) <= B pow k * exp(&l * X)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW; NORM_CEXP; RE_MUL_CX] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[NORM_POS_LE];
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
    REWRITE_TAC[REAL_EXP_POS_LE];
    REWRITE_TAC[REAL_EXP_MONO_LE; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    TRANS_TAC REAL_LE_TRANS `abs a * B` THEN ASM_REWRITE_TAC[] THEN
    TRANS_TAC REAL_LE_TRANS `abs a * norm(z:complex)` THEN CONJ_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `abs(a * Re z)` THEN CONJ_TAC THENL
       [REAL_ARITH_TAC;
        REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        REWRITE_TAC[REAL_ABS_POS; COMPLEX_NORM_GE_RE_IM]];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]]]);;

let TL_CORE_LAM_BOUND = prove
 (`!b1 b2 R S x y.
     1 <= b2 /\ &b1 * abs x <= &b2 * abs y
     ==> abs(x / &b2) * &((R - 1) * b2 + (S - 1) * b1) <=
         &(R - 1) * abs x + &(S - 1) * abs y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &b2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NUM;
               REAL_ARITH `(a:real) / b * c = (a * c) / b`;
               REAL_LE_LDIV_EQ] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
  MP_TAC(SPECL [`&(S - 1)`; `&b1 * abs(x:real)`; `&b2 * abs(y:real)`]
    REAL_LE_LMUL) THEN
  ASM_REWRITE_TAC[REAL_POS] THEN REAL_ARITH_TAC);;

let TL_CORE_PRODUCT_M = prove
 (`!N (kk:num->num) (ll:num->num) B Y.
     product(1..N) (\i. B pow (kk i) * exp(&(ll i) * Y)) =
     B pow (nsum(1..N) kk) * exp(&(nsum(1..N) ll) * Y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PRODUCT_MUL_NUMSEG] THEN BINOP_TAC THENL
   [SIMP_TAC[REAL_POW_NSUM; FINITE_NUMSEG];
    SIMP_TAC[GSYM REAL_EXP_SUM; FINITE_NUMSEG; SUM_RMUL;
             REAL_OF_NUM_SUM_NUMSEG]]);;

let TL_CORE_PRODUCT_D = prove
 (`!N (rr:num->num) (ss:num->num) x y m.
     product(1..N) (\j. x pow (m * rr j) * y pow (m * ss j)) =
     x pow (m * nsum(1..N) rr) * y pow (m * nsum(1..N) ss)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PRODUCT_MUL_NUMSEG; GSYM NSUM_LMUL] THEN
  SIMP_TAC[REAL_POW_NSUM; FINITE_NUMSEG]);;

let TL_CORE_INTEGRAL = prove
 (`!p1 q1 p2 q2 b1 b2 L N (kk:num->num) (ll:num->num) (rr:num->num)
    (ss:num->num).
     1 <= q1 /\ 1 <= q2 /\ (!i. i IN 1..N ==> ll i < L) /\
     ~(ring_det real_ring (1..N)
         (\i j. &(rr j * b2 + ss j * b1) pow (kk i) *
                (&p1 / &q1) pow (ll i * rr j) *
                (&p2 / &q2) pow (ll i * ss j)) = &0)
     ==> &1 <= abs(ring_det real_ring (1..N)
                     (\i j. &(rr j * b2 + ss j * b1) pow (kk i) *
                            (&p1 / &q1) pow (ll i * rr j) *
                            (&p2 / &q2) pow (ll i * ss j))) *
               &q1 pow ((L - 1) * nsum(1..N) rr) *
               &q2 pow ((L - 1) * nsum(1..N) ss)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`N:num`;
    `\i j. &((rr:num->num) j * b2 + (ss:num->num) j * b1) pow
           ((kk:num->num) i) *
           (&p1 / &q1) pow ((ll:num->num) i * rr j) *
           (&p2 / &q2) pow (ll i * ss j)`;
    `\j. &q1 pow ((L - 1) * (rr:num->num) j) *
         &q2 pow ((L - 1) * (ss:num->num) j)`]
   RDET_INTEGER_COLUMNS) THEN
  REWRITE_TAC[TL_CORE_PRODUCT_D] THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH
     `((x:real) * a * b) * (c * d) = x * (a * c) * (b * d)`] THEN
    SUBGOAL_THEN `(ll:num->num) i <= L - 1` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC INTEGER_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_POW; INTEGER_CLOSED]; ALL_TAC] THEN
    MATCH_MP_TAC INTEGER_MUL THEN
    CONJ_TAC THEN MATCH_MP_TAC TL_INTEGER_RATIO_POW THEN
    ASM_REWRITE_TAC[LE_MULT_RCANCEL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < &q1 pow ((L - 1) * nsum(1..N) (rr:num->num)) /\
    &0 < &q2 pow ((L - 1) * nsum(1..N) (ss:num->num))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o
    MATCH_MP (REWRITE_RULE[IMP_CONJ] REAL_ABS_INTEGER_LEMMA)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_NUM]]);;

(* ------------------------------------------------------------------------- *)
(* The analytic upper bound (interpolation determinant with perturbation),   *)
(* for general real points 0 <= x j <= r.                                    *)
(* ------------------------------------------------------------------------- *)

let TL_CORE_ANALYTIC_GEN = prove
 (`!N (x:num->real) (kk:num->num) (ll:num->num) (ss:num->num)
    a Lam b2 L S r rho Y.
     1 <= b2 /\ 1 <= L /\ 1 <= S /\ &0 < r /\ &1 <= rho /\
     (!j. j IN 1..N ==> &0 <= x j /\ x j <= r) /\
     (!i. i IN 1..N ==> ll i < L) /\
     (!j. j IN 1..N ==> ss j < S) /\
     abs a * rho * r <= Y /\
     abs Lam * &(L * S) * exp(&(L * S) * abs Lam / &b2) / &b2
     <= inv(rho pow N)
     ==> abs(ring_det real_ring (1..N)
               (\i j. x j pow (kk i) * exp(&(ll i) * a * x j) *
                      exp(&(ll i) * &(ss j) * Lam / &b2))) <=
         &2 pow N * &(FACT N) * inv(rho pow ((N * (N - 1)) DIV 2)) *
         (rho * r) pow (nsum(1..N) kk) * exp(&(nsum(1..N) ll) * Y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `c = Lam * &(L * S) * exp(&(L * S) * abs Lam / &b2) / &b2` THEN
  SUBGOAL_THEN `abs c <= inv(rho pow N)` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_NUM; REAL_ABS_EXP] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. Cx(&1) + Cx c *
          Cx(if c = &0 then &0
             else (exp(&((ll:num->num) i) * &((ss:num->num) j) * Lam / &b2) -
                   &1) / c) =
          Cx(exp(&(ll i) * &(ss j) * Lam / &b2))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC TL_CORE_TH_ENTRY THEN
    EXPAND_TAC "c" THEN
    REWRITE_TAC[REAL_ENTIRE; real_div; REAL_INV_EQ_0; REAL_EXP_NZ;
                REAL_OF_NUM_EQ; MULT_EQ_0] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= n ==> ~(n = 0)`] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_EXP_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `r / (rho * r) = inv rho` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < r` THEN UNDISCH_TAC `&1 <= rho` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`N:num`;
    `\i:num z:complex. z pow ((kk:num->num) i) *
                       cexp(Cx(&((ll:num->num) i) * a) * z)`;
    `\i:num j:num. Cx(if c = &0 then &0
                      else (exp(&((ll:num->num) i) * &((ss:num->num) j) *
                                Lam / &b2) - &1) / c)`;
    `\j:num. Cx((x:num->real) j)`;
    `r:real`; `(rho:real) * r`;
    `\i:num. ((rho:real) * r) pow ((kk:num->num) i) *
             exp(&((ll:num->num) i) * Y)`;
    `Cx c`] INTERPOLATION_DETERMINANT_PERTURBED) THEN
  REWRITE_TAC[TL_PH_HOLOMORPHIC; COMPLEX_NORM_CX] THEN
  ASM_REWRITE_TAC[REAL_POW_INV] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC TL_CORE_PH_NORM_BOUND THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 <= (x:num->real) j /\ x j <= r` MP_TAC THENL
       [ASM_MESON_TAC[]; REAL_ARITH_TAC];
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      REWRITE_TAC[GSYM COMPLEX_NORM_CX] THEN MATCH_MP_TAC TL_CORE_TH_NORM THEN
      EXPAND_TAC "c" THEN MATCH_MP_TAC TL_CORE_TH_BOUND THEN ASM_MESON_TAC[]];
    REWRITE_TAC[TL_CORE_PH_CX] THEN
    REWRITE_TAC[GSYM CX_MUL; CDET_CX; COMPLEX_NORM_CX; TL_CORE_PRODUCT_M;
                GSYM REAL_MUL_ASSOC]]);;

(* ------------------------------------------------------------------------- *)
(* The analytic upper bound for the matrix of the main theorem.              *)
(* ------------------------------------------------------------------------- *)

let TL_CORE_ANALYTIC = prove
 (`!p1 q1 p2 q2 b1 b2 L R S N (kk:num->num) (ll:num->num) (rr:num->num)
    (ss:num->num) rho.
     1 <= p1 /\ 1 <= q1 /\ 1 <= p2 /\ 1 <= q2 /\ 1 <= b2 /\
     1 <= L /\ 2 <= R /\ 1 <= S /\
     (!i. i IN 1..N ==> ll i < L) /\
     (!j. j IN 1..N ==> rr j < R /\ ss j < S) /\
     &b1 * abs(log(&p1 / &q1)) <= &b2 * abs(log(&p2 / &q2)) /\
     &1 <= rho /\
     abs(&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1)) * &(L * S) *
     exp(&(L * S) * abs(&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1)) /
         &b2) / &b2 <= inv(rho pow N)
     ==> abs(ring_det real_ring (1..N)
               (\i j. &(rr j * b2 + ss j * b1) pow (kk i) *
                      (&p1 / &q1) pow (ll i * rr j) *
                      (&p2 / &q2) pow (ll i * ss j))) <=
         &2 pow N * &(FACT N) * inv(rho pow ((N * (N - 1)) DIV 2)) *
         (rho * &((R - 1) * b2 + (S - 1) * b1)) pow (nsum(1..N) kk) *
         exp(&(nsum(1..N) ll) * rho *
             (&(R - 1) * abs(log(&p1 / &q1)) +
              &(S - 1) * abs(log(&p2 / &q2))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`N:num`; `\j. &((rr:num->num) j * b2 + (ss:num->num) j * b1)`;
    `kk:num->num`; `ll:num->num`; `ss:num->num`;
    `log(&p1 / &q1) / &b2`;
    `&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1)`;
    `b2:num`; `L:num`; `S:num`;
    `&((R - 1) * b2 + (S - 1) * b1)`; `rho:real`;
    `rho * (&(R - 1) * abs(log(&p1 / &q1)) +
            &(S - 1) * abs(log(&p2 / &q2)))`]
   TL_CORE_ANALYTIC_GEN) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN
      MATCH_MP_TAC(ARITH_RULE `0 < a ==> 0 < a + b`) THEN
      REWRITE_TAC[LT_MULT] THEN
      MAP_EVERY UNDISCH_TAC [`2 <= R`; `1 <= b2`] THEN ARITH_TAC;
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN
      SUBGOAL_THEN `(rr:num->num) j <= R - 1 /\ (ss:num->num) j <= S - 1`
      STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[ARITH_RULE `a < b ==> a <= b - 1`];
        MATCH_MP_TAC LE_ADD2 THEN ASM_REWRITE_TAC[LE_MULT_RCANCEL]];
      ASM_MESON_TAC[];
      MP_TAC(SPECL [`b1:num`; `b2:num`; `R:num`; `S:num`;
                    `log(&p1 / &q1)`; `log(&p2 / &q2)`] TL_CORE_LAM_BOUND) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      GEN_REWRITE_TAC LAND_CONV
       [REAL_ARITH `(a:real) * rho * r = rho * a * r`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC(REAL_ARITH `(a:real) = b ==> a <= c ==> b <= c`) THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
    MP_TAC(SPECL [`p1:num`; `q1:num`; `p2:num`; `q2:num`; `b1:num`;
                  `b2:num`; `(ll:num->num) i`; `(rr:num->num) j`;
                  `(ss:num->num) j`] TL_ENTRY_EXP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[real_div; REAL_MUL_AC]]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem (Bugeaud, Theorem 11.4, rational case D = 1, with the    *)
(* non-vanishing of the chosen N x N minor as hypothesis).                   *)
(* ------------------------------------------------------------------------- *)

let TWOLOG_CORE_PARAMETRIC = prove
 (`!p1 q1 p2 q2 b1 b2 K L R S N kk ll rr ss rho.
     1 <= p1 /\ 1 <= q1 /\ 1 <= p2 /\ 1 <= q2 /\ 1 <= b1 /\ 1 <= b2 /\
     1 <= K /\ 1 <= L /\ 2 <= R /\ 1 <= S /\
     (!i. i IN 1..N ==> kk i < K /\ ll i < L) /\
     (!j. j IN 1..N ==> rr j < R /\ ss j < S) /\
     ~(ring_det real_ring (1..N)
         (\i j. &(rr j * b2 + ss j * b1) pow (kk i) *
                (&p1 / &q1) pow (ll i * rr j) *
                (&p2 / &q2) pow (ll i * ss j)) = &0) /\
     &b1 * abs(log(&p1 / &q1)) <= &b2 * abs(log(&p2 / &q2)) /\
     &1 <= rho /\
     &2 pow N * &(FACT N) *
     (rho * &((R - 1) * b2 + (S - 1) * b1)) pow (nsum(1..N) kk) *
     exp(&(nsum(1..N) ll) * rho *
         (&(R - 1) * abs(log(&p1 / &q1)) + &(S - 1) * abs(log(&p2 / &q2)))) *
     &q1 pow ((L - 1) * nsum(1..N) rr) * &q2 pow ((L - 1) * nsum(1..N) ss) *
     inv(rho pow ((N * (N - 1)) DIV 2)) < &1
     ==> inv(rho pow N) <
         abs(&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1)) * &(L * S) *
         exp(&(L * S) * abs(&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1)) /
             &b2) / &b2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!i. i IN 1..N ==> (ll:num->num) i < L` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`p1:num`; `q1:num`; `p2:num`; `q2:num`; `b1:num`; `b2:num`;
                `L:num`; `R:num`; `S:num`; `N:num`; `kk:num->num`;
                `ll:num->num`; `rr:num->num`; `ss:num->num`; `rho:real`]
    TL_CORE_ANALYTIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC
   `&q1 pow ((L - 1) * nsum(1..N) (rr:num->num)) *
    &q2 pow ((L - 1) * nsum(1..N) (ss:num->num))` o
   MATCH_MP (REWRITE_RULE[IMP_CONJ] REAL_LE_RMUL)) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  MP_TAC(SPECL [`p1:num`; `q1:num`; `p2:num`; `q2:num`; `b1:num`; `b2:num`;
                `L:num`; `N:num`; `kk:num->num`; `ll:num->num`;
                `rr:num->num`; `ss:num->num`] TL_CORE_INTEGRAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_comb(concl th) && rand(concl th) = `&1:real`)) THEN
  REAL_ARITH_TAC);;
