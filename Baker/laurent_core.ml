(* ========================================================================= *)
(* Two logarithms, the Laurent bound: the arithmetic lower bound             *)
(* and the core for rationals (D = 1, mu = 1).                               *)
(*                                                                           *)
(* Purpose: M. Laurent, Linear forms in two logarithms and interpolation     *)
(* determinants II, Acta Arith. 133 (2008), Lemma 1 (= Laurent, Acta Arith.  *)
(* 66 (1994), Lemma 5, with the 1/a trick) and Theorem 1 at mu = 1, D = 1,   *)
(* for binomial rows C(r b2 + s b1, k) and rational a_i = p_i / q_i >= 1.    *)
(*                                                                           *)
(* Main results: TWOLOG_LAURENT_ARITH (log of the non-zero determinant is at *)
(* least (M1 + G1) log a1 - 2 G1 log p1 + (M2 + G2) log a2 - 2 G2 log p2:    *)
(* every permutation exponent lies in the window [M - G, M + G], so the      *)
(* determinant times q1^V1 p1^-U1 q2^V2 p2^-U2 is a non-zero integer) and    *)
(* TWOLOG_LAURENT_CORE (the main inequality at mu = 1, D = 1 forces          *)
(* rho^-N < Lambda prime = L S |Lambda| / (2 b2) exp(L S |Lambda| / (2 b2)), *)
(* by the g-lemma, the analytic upper bound and the arithmetic lower bound); *)
(* the general forms LAURENT_EXP_MATRIX, LAURENT_GLEMMA_BOTH (for any real   *)
(* x1, x2) and LAURENT_CORE_FINAL (for a degree factor nn), also used by     *)
(* Baker/laurent_alg.ml; helper names TL_LAURENT_CORE_*.                     *)
(*                                                                           *)
(* Uses: Baker/laurent_det.ml (RDET_INTEGER_PERMUTATIONS,                    *)
(* SUM_NUMSEG_PRED_MOD), Baker/laurent_binom.ml                              *)
(* (BINOM_MINOR_COLUMNS_DISTINCT), Baker/laurent_glemma.ml (TWOLOG_G_LEMMA), *)
(* Baker/laurent_interp.ml (TWOLOG_LAURENT_ANALYTIC), Baker/twolog.ml        *)
(* (NSUM_NUMSEG_PRED_MOD), Baker/twolog_param.ml (MULT_PRED_DIV_2),          *)
(* Baker/lemmas.ml (LOG_MUL4), REAL_ABS_INTEGER_LEMMA of Library/floor.ml.   *)
(* ========================================================================= *)

needs "Baker/laurent_glemma.ml";;
needs "Baker/laurent_interp.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The arithmetic lower bound (Laurent Lemma 1, D = 1): exponent windows     *)
(* U <= E(p) <= V of all permutation terms, the integer multiple of the      *)
(* determinant, and the resulting logarithmic inequality.                    *)
(* ------------------------------------------------------------------------- *)

let TL_LAURENT_CORE_RATIO_INTEGER = prove
 (`!p q U E V.
     1 <= p /\ 1 <= q /\ U <= E /\ E <= V
     ==> integer(&q pow V / &p pow U * (&p / &q) pow E)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `e:num` SUBST1_TAC o
    GEN_REWRITE_RULE I [LE_EXISTS]) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:num` SUBST1_TAC o
    GEN_REWRITE_RULE I [LE_EXISTS]) THEN
  SUBGOAL_THEN `~(&p = &0) /\ ~(&q = &0)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&q pow ((U + d) + e) / &p pow U * (&p / &q) pow (U + d) =
    &p pow d * &q pow e`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_ADD; REAL_POW_DIV] THEN
    MP_TAC(SPECL [`&p`; `U:num`] REAL_POW_NZ) THEN
    MP_TAC(SPECL [`&q`; `U:num`] REAL_POW_NZ) THEN
    MP_TAC(SPECL [`&q`; `d:num`] REAL_POW_NZ) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; INTEGER_CLOSED]]);;

let TL_LAURENT_CORE_WINDOW = prove
 (`!(P:A->bool) (E:A->num) M G.
     (?x. P x) /\ (!x. P x ==> abs(&(E x) - M) <= G)
     ==> ?U V. (!x. P x ==> U <= E x /\ E x <= V) /\
               M - G <= &U /\ &V <= M + G`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_TAC `x0:A`) (LABEL_TAC "hb")) THEN
  SUBGOAL_THEN
   `?U. (?x. (P:A->bool) x /\ (E:A->num) x = U) /\ (!x. P x ==> U <= E x)`
  (X_CHOOSE_THEN `U:num` (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `xu:A` STRIP_ASSUME_TAC) ASSUME_TAC))
  THENL
   [MP_TAC(ISPEC `\n. ?x. (P:A->bool) x /\ (E:A->num) x = n` num_WOP) THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
    STRIP_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN REWRITE_TAC[GSYM NOT_LT] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?V. (?x. (P:A->bool) x /\ (E:A->num) x = V) /\ (!x. P x ==> E x <= V)`
  (X_CHOOSE_THEN `V:num` (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `xv:A` STRIP_ASSUME_TAC) ASSUME_TAC))
  THENL
   [X_CHOOSE_TAC `m:num` (SPEC `M + G:real` REAL_ARCH_SIMPLE) THEN
    MP_TAC(ISPEC `\n. ?x. (P:A->bool) x /\ (E:A->num) x = n` num_MAX) THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN
    CONJ_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      EXISTS_TAC `m:num` THEN X_GEN_TAC `n:num` THEN
      DISCH_THEN(X_CHOOSE_THEN `x:A` (CONJUNCTS_THEN2 ASSUME_TAC
        (SUBST1_TAC o SYM))) THEN
      SUBGOAL_THEN `abs(&((E:A->num) x) - M) <= G` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `M + G <= &m` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
    STRIP_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`U:num`; `V:num`] THEN
  REMOVE_THEN "hb" (fun th ->
    MP_TAC(SPEC `xu:A` th) THEN MP_TAC(SPEC `xv:A` th)) THEN
  ASM_SIMP_TAC[] THEN REAL_ARITH_TAC);;

let TL_LAURENT_CORE_CENTRED_SUM = prove
 (`!N K L (rr:num->num) p.
     p permutes 1..N
     ==> &(nsum(1..N) (\i. ((i - 1) DIV K) * rr(p i))) -
         (&L - &1) / &2 * &(nsum(1..N) rr) =
         sum(1..N) (\i. (&((i - 1) DIV K) - (&L - &1) / &2) * &(rr(p i)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_OF_NUM_SUM_NUMSEG; GSYM REAL_OF_NUM_MUL;
              REAL_SUB_RDISTRIB; SUM_SUB_NUMSEG; SUM_LMUL] THEN
  MP_TAC(ISPECL [`\i. &((rr:num->num) i)`; `p:num->num`; `1`; `N:num`]
    SUM_PERMUTE_NUMSEG) THEN
  ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

let TL_LAURENT_CORE_ARITH_GEN = prove
 (`!p1 q1 p2 q2 N (c:num->num->real) (ll:num->num) (rr:num->num)
    (ss:num->num) U1 V1 U2 V2.
     1 <= p1 /\ 1 <= q1 /\ 1 <= p2 /\ 1 <= q2 /\
     (!i j. integer(c i j)) /\
     (!p. p permutes 1..N
          ==> U1 <= nsum(1..N) (\i. ll i * rr(p i)) /\
              nsum(1..N) (\i. ll i * rr(p i)) <= V1 /\
              U2 <= nsum(1..N) (\i. ll i * ss(p i)) /\
              nsum(1..N) (\i. ll i * ss(p i)) <= V2) /\
     ~(ring_det real_ring (1..N)
         (\i j. c i j * (&p1 / &q1) pow (ll i * rr j) *
                (&p2 / &q2) pow (ll i * ss j)) = &0)
     ==> &U1 * log(&p1) - &V1 * log(&q1) + &U2 * log(&p2) - &V2 * log(&q2)
         <= log(abs(ring_det real_ring (1..N)
                      (\i j. c i j * (&p1 / &q1) pow (ll i * rr j) *
                             (&p2 / &q2) pow (ll i * ss j))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `integer((&q1 pow V1 / &p1 pow U1 * &q2 pow V2 / &p2 pow U2) *
            ring_det real_ring (1..N)
              (\i j. (c:num->num->real) i j *
                     (&p1 / &q1) pow (ll i * rr j) *
                     (&p2 / &q2) pow (ll i * ss j)))`
  MP_TAC THENL
   [MATCH_MP_TAC RDET_INTEGER_PERMUTATIONS THEN
    X_GEN_TAC `p:num->num` THEN DISCH_TAC THEN
    REWRITE_TAC[PRODUCT_MUL_NUMSEG] THEN
    SIMP_TAC[GSYM REAL_POW_NSUM; FINITE_NUMSEG] THEN
    REWRITE_TAC[REAL_ARITH
     `(a / b * c / d) * (x * y * z:real) = x * (a / b * y) * (c / d * z)`] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num->num`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN MATCH_MP_TAC INTEGER_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGER_PRODUCT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC INTEGER_MUL THEN CONJ_TAC THEN
      MATCH_MP_TAC TL_LAURENT_CORE_RATIO_INTEGER THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC
   `D = ring_det real_ring (1..N)
          (\i j. (c:num->num->real) i j *
                 (&p1 / &q1) pow (ll i * rr j) *
                 (&p2 / &q2) pow (ll i * ss j))` THEN
  SUBGOAL_THEN `&0 < &p1 /\ &0 < &q1 /\ &0 < &p2 /\ &0 < &q2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN
    MAP_EVERY UNDISCH_TAC [`1 <= p1`; `1 <= q1`; `1 <= p2`; `1 <= q2`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `c0 = &q1 pow V1 / &p1 pow U1 * &q2 pow V2 / &p2 pow U2` THEN
  SUBGOAL_THEN `&0 < c0` ASSUME_TAC THENL
   [EXPAND_TAC "c0" THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o
    MATCH_MP (REWRITE_RULE[IMP_CONJ] REAL_ABS_INTEGER_LEMMA)) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_ENTIRE; DE_MORGAN_THM; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_MUL; REAL_ARITH `&0 < x ==> abs x = x`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < abs D` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_ABS_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(c0 * abs D)` MP_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_MUL] THEN EXPAND_TAC "c0" THEN
  ASM_SIMP_TAC[LOG_MUL; LOG_DIV; REAL_LT_DIV; REAL_POW_LT; LOG_POW] THEN
  REAL_ARITH_TAC);;

let TL_LAURENT_CORE_ARITH_REAL = prove
 (`!M1 G1 U1 V1 x1 y1 M2 G2 U2 V2 x2 y2 D:real.
     &0 <= x1 /\ &0 <= y1 /\ &0 <= x2 /\ &0 <= y2 /\
     M1 - G1 <= U1 /\ V1 <= M1 + G1 /\ M2 - G2 <= U2 /\ V2 <= M2 + G2 /\
     U1 * x1 - V1 * y1 + U2 * x2 - V2 * y2 <= D
     ==> (M1 + G1) * (x1 - y1) - &2 * G1 * x1 +
         (M2 + G2) * (x2 - y2) - &2 * G2 * x2 <= D`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `&0 <= (U1 - (M1 - G1)) * x1 /\ &0 <= ((M1 + G1) - V1) * y1 /\
    &0 <= (U2 - (M2 - G2)) * x2 /\ &0 <= ((M2 + G2) - V2) * y2`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `U1 * x1 - V1 * y1 + U2 * x2 - V2 * y2 <= D:real` THEN
  REAL_ARITH_TAC);;

let TWOLOG_LAURENT_ARITH = prove
 (`!p1 q1 p2 q2 b1 b2 K L N (rr:num->num) (ss:num->num) G1 G2.
     1 <= q1 /\ q1 <= p1 /\ 1 <= q2 /\ q2 <= p2 /\ 1 <= K /\ 1 <= L /\
     N = K * L /\
     (!p. p permutes 1..N
          ==> abs(sum(1..N) (\i. (&((i - 1) DIV K) - (&L - &1) / &2) *
                                 &(rr(p i)))) <= G1) /\
     (!p. p permutes 1..N
          ==> abs(sum(1..N) (\i. (&((i - 1) DIV K) - (&L - &1) / &2) *
                                 &(ss(p i)))) <= G2) /\
     ~(ring_det real_ring (1..N)
         (\i j. &(binom(rr j * b2 + ss j * b1,(i - 1) MOD K)) *
                (&p1 / &q1) pow (((i - 1) DIV K) * rr j) *
                (&p2 / &q2) pow (((i - 1) DIV K) * ss j)) = &0)
     ==> ((&L - &1) / &2 * &(nsum(1..N) rr) + G1) * log(&p1 / &q1) -
         &2 * G1 * log(&p1) +
         ((&L - &1) / &2 * &(nsum(1..N) ss) + G2) * log(&p2 / &q2) -
         &2 * G2 * log(&p2)
         <= log(abs(ring_det real_ring (1..N)
                      (\i j. &(binom(rr j * b2 + ss j * b1,(i - 1) MOD K)) *
                             (&p1 / &q1) pow (((i - 1) DIV K) * rr j) *
                             (&p2 / &q2) pow (((i - 1) DIV K) * ss j))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_THEN `N = K * L` (K ALL_TAC) THEN
  SUBGOAL_THEN `1 <= p1 /\ 1 <= p2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`1 <= q1`; `q1 <= p1`; `1 <= q2`; `q2 <= p2`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\p:num->num. p permutes 1..N`;
    `\p. nsum(1..N) (\i. ((i - 1) DIV K) * (rr:num->num)(p i))`;
    `(&L - &1) / &2 * &(nsum(1..N) (rr:num->num))`; `G1:real`]
   TL_LAURENT_CORE_WINDOW) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [MESON_TAC[PERMUTES_I]; ALL_TAC] THEN
    X_GEN_TAC `p:num->num` THEN DISCH_TAC THEN
    SIMP_TAC[TL_LAURENT_CORE_CENTRED_SUM;
             ASSUME `(p:num->num) permutes 1..N`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U1:num` (X_CHOOSE_THEN `V1:num`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL
   [`\p:num->num. p permutes 1..N`;
    `\p. nsum(1..N) (\i. ((i - 1) DIV K) * (ss:num->num)(p i))`;
    `(&L - &1) / &2 * &(nsum(1..N) (ss:num->num))`; `G2:real`]
   TL_LAURENT_CORE_WINDOW) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [MESON_TAC[PERMUTES_I]; ALL_TAC] THEN
    X_GEN_TAC `p:num->num` THEN DISCH_TAC THEN
    SIMP_TAC[TL_LAURENT_CORE_CENTRED_SUM;
             ASSUME `(p:num->num) permutes 1..N`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U2:num` (X_CHOOSE_THEN `V2:num`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL
   [`p1:num`; `q1:num`; `p2:num`; `q2:num`; `N:num`;
    `\i j. &(binom((rr:num->num) j * b2 + (ss:num->num) j * b1,
                   (i - 1) MOD K))`;
    `\i. (i - 1) DIV K`; `rr:num->num`; `ss:num->num`;
    `U1:num`; `V1:num`; `U2:num`; `V2:num`] TL_LAURENT_CORE_ARITH_GEN) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_SIMP_TAC[INTEGER_CLOSED]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &p1 /\ &0 < &q1 /\ &0 < &p2 /\ &0 < &q2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN
    MAP_EVERY UNDISCH_TAC [`1 <= p1`; `1 <= q1`; `1 <= p2`; `1 <= q2`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&p1 / &q1) = log(&p1) - log(&q1) /\
                log(&p2 / &q2) = log(&p2) - log(&q2)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC LOG_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC TL_LAURENT_CORE_ARITH_REAL THEN
  MAP_EVERY EXISTS_TAC [`&U1:real`; `&V1:real`; `&U2:real`; `&V2:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC LOG_POS THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_LE]);;

(* ------------------------------------------------------------------------- *)
(* Sums over the rows i = 1..K L of functions of (i - 1) MOD K, and the      *)
(* logarithm of the upper bound of TWOLOG_LAURENT_ANALYTIC.                  *)
(* ------------------------------------------------------------------------- *)

let TL_LAURENT_CORE_SUM_PRED_MOD = prove
 (`!K L. 1 <= K
         ==> sum(1..K * L) (\i. &((i - 1) MOD K)) =
             &(K * L) * (&K - &1) / &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_SUM_NUMSEG] THEN
  MP_TAC(SPECL [`K:num`; `L:num`] NSUM_NUMSEG_PRED_MOD) THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL;
               GSYM REAL_OF_NUM_SUB] THEN
  REAL_ARITH_TAC);;

let TL_LAURENT_CORE_SUM_LOG_FACT_MOD = prove
 (`!K L. 1 <= K
         ==> sum(1..K * L) (\i. log(&(FACT((i - 1) MOD K)))) =
             &L * sum(1..K - 1) (\k. log(&(FACT k)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`K:num`; `L:num`; `\k. log(&(FACT k))`]
    SUM_NUMSEG_PRED_MOD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ADD_CLAUSES] THEN
  REWRITE_TAC[FACT; LOG_1; REAL_ADD_LID]);;

let TL_LAURENT_CORE_TRIANGLE = prove
 (`!n. &((n * (n - 1)) DIV 2) = &n * (&n - &1) / &2`,
  GEN_TAC THEN MP_TAC(SPEC `n:num` MULT_PRED_DIV_2) THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL;
               GSYM REAL_OF_NUM_SUB; ARITH_RULE `~(n = 0) ==> 1 <= n`] THEN
  REAL_ARITH_TAC);;

let TL_LAURENT_CORE_LOG_MUL5 = prove
 (`!a b c d e.
     &0 < a /\ &0 < b /\ &0 < c /\ &0 < d /\ &0 < e
     ==> log(a * b * c * d * e) = log a + log b + log c + log d + log e`,
  SIMP_TAC[LOG_MUL; LOG_MUL4; REAL_LT_MUL]);;

let TL_LAURENT_CORE_LOG_UPPER = prove
 (`!K L rho x E.
     1 <= K /\ &0 < rho /\ &0 < x
     ==> log(&2 pow (K * L) * &(FACT(K * L)) *
             inv(rho pow (((K * L) * (K * L - 1)) DIV 2)) *
             product(1..K * L)
               (\i. (rho * x) pow ((i - 1) MOD K) / &(FACT((i - 1) MOD K))) *
             exp E) =
         &(K * L) * log(&2) + log(&(FACT(K * L))) -
         &(K * L) * (&(K * L) - &1) / &2 * log rho +
         (&(K * L) * (&K - &1) / &2 * (log rho + log x) -
          &L * sum(1..K - 1) (\k. log(&(FACT k)))) + E`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. &0 < (rho * x) pow ((i - 1) MOD K) / &(FACT((i - 1) MOD K))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN
    REWRITE_TAC[REAL_OF_NUM_LT; FACT_LT] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_SIMP_TAC[REAL_LT_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `log(product(1..K * L)
          (\i. (rho * x) pow ((i - 1) MOD K) / &(FACT((i - 1) MOD K)))) =
    &(K * L) * (&K - &1) / &2 * (log rho + log x) -
    &L * sum(1..K - 1) (\k. log(&(FACT k)))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[LOG_PRODUCT; FINITE_NUMSEG] THEN
    ASM_SIMP_TAC[LOG_DIV; REAL_POW_LT; REAL_LT_MUL; REAL_OF_NUM_LT; FACT_LT;
                 LOG_POW; LOG_MUL] THEN
    REWRITE_TAC[SUM_SUB_NUMSEG; SUM_RMUL] THEN
    ASM_SIMP_TAC[TL_LAURENT_CORE_SUM_PRED_MOD;
                 TL_LAURENT_CORE_SUM_LOG_FACT_MOD] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < product(1..K * L)
          (\i. (rho * x) pow ((i - 1) MOD K) / &(FACT((i - 1) MOD K)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LT_NUMSEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < &2 pow (K * L) /\ &0 < &(FACT(K * L)) /\
    &0 < inv(rho pow (((K * L) * (K * L - 1)) DIV 2)) /\ &0 < exp E`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; FACT_LT; REAL_LT_INV;
                 REAL_EXP_POS_LT; ARITH];
    ALL_TAC] THEN
  ASM_SIMP_TAC[TL_LAURENT_CORE_LOG_MUL5] THEN
  ASM_SIMP_TAC[LOG_POW; REAL_OF_NUM_LT; ARITH; LOG_INV; REAL_POW_LT;
               LOG_EXP; TL_LAURENT_CORE_TRIANGLE] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Ingredients of the core: exponential entries are powers of x1, x2 > 0,    *)
(* the g-lemma for both coordinates (columns distinct by the non-zero        *)
(* minor), log(p / q) >= 0.                                                  *)
(* ------------------------------------------------------------------------- *)

let TL_LAURENT_CORE_EXP_ENTRY = prove
 (`!x y l r s.
     &0 < x /\ &0 < y
     ==> exp(&l * (&r * log x + &s * log y)) = x pow (l * r) * y pow (l * s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_MUL_ASSOC; REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[REAL_EXP_ADD; REAL_EXP_N] THEN ASM_SIMP_TAC[EXP_LOG]);;

let LAURENT_EXP_MATRIX = prove
 (`!x1 x2 b1 b2 K (rr:num->num) (ss:num->num).
     &0 < x1 /\ &0 < x2
     ==> (\i j. &(binom(rr j * b2 + ss j * b1,(i - 1) MOD K)) *
                exp(&((i - 1) DIV K) * (&(rr j) * log x1 + &(ss j) * log x2))) =
         (\i j. &(binom(rr j * b2 + ss j * b1,(i - 1) MOD K)) *
                x1 pow (((i - 1) DIV K) * rr j) *
                x2 pow (((i - 1) DIV K) * ss j))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC TL_LAURENT_CORE_EXP_ENTRY THEN ASM_REWRITE_TAC[]);;

let LAURENT_GLEMMA_BOTH = prove
 (`!(x1:real) (x2:real) b1 b2 K L R S N (rr:num->num) (ss:num->num).
     1 <= K /\ 1 <= L /\ N = K * L /\
     (!j. j IN 1..N ==> rr j < R /\ ss j < S) /\
     ~(ring_det real_ring (1..N)
         (\i j. &(binom(rr j * b2 + ss j * b1,(i - 1) MOD K)) *
                x1 pow (((i - 1) DIV K) * rr j) *
                x2 pow (((i - 1) DIV K) * ss j)) = &0)
     ==> (!p. p permutes 1..N
              ==> abs(sum(1..N) (\i. (&((i - 1) DIV K) - (&L - &1) / &2) *
                                     &(rr(p i)))) <=
                  &L * &R * &N / &2 * (&1 / &4 - &N / (&12 * &R * &S))) /\
         (!p. p permutes 1..N
              ==> abs(sum(1..N) (\i. (&((i - 1) DIV K) - (&L - &1) / &2) *
                                     &(ss(p i)))) <=
                  &L * &S * &N / &2 * (&1 / &4 - &N / (&12 * &R * &S))) /\
         &0 <= &L * &R * &N / &2 * (&1 / &4 - &N / (&12 * &R * &S)) /\
         &0 <= &L * &S * &N / &2 * (&1 / &4 - &N / (&12 * &R * &S))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP BINOM_MINOR_COLUMNS_DISTINCT) THEN
  UNDISCH_THEN `N = K * L` SUBST_ALL_TAC THEN
  MATCH_MP_TAC(TAUT `(a /\ b) /\ (a /\ b ==> c /\ d) ==> a /\ b /\ c /\ d`) THEN
  CONJ_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `p:num->num` THEN DISCH_TAC THENL
     [MATCH_MP_TAC TWOLOG_G_LEMMA THEN EXISTS_TAC `ss:num->num` THEN
      ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[REAL_ARITH `&12 * &R * &S = &12 * &S * &R`] THEN
      MATCH_MP_TAC TWOLOG_G_LEMMA THEN EXISTS_TAC `rr:num->num` THEN
      ASM_MESON_TAC[]];
    DISCH_THEN(CONJUNCTS_THEN (MP_TAC o SPEC `I:num->num`)) THEN
    REWRITE_TAC[PERMUTES_I] THEN REAL_ARITH_TAC]);;

let TL_LAURENT_CORE_LOG_RATIO_POS = prove
 (`!p q. 1 <= q /\ q <= p ==> &0 <= log(&p / &q)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LOG_POS THEN
  SUBGOAL_THEN `&0 < &q` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID; REAL_OF_NUM_LE]);;

(* ------------------------------------------------------------------------- *)
(* The core (Laurent Theorem 1 at mu = 1): the final real inequality for a   *)
(* degree factor nn (nn = 1 here, nn = n in Baker/laurent_alg.ml) and the    *)
(* assembly for D = 1.                                                       *)
(* ------------------------------------------------------------------------- *)

let LAURENT_CORE_FINAL = prove
 (`!nn N k l r s g rho A2 AF Lr Lx SLF S1 S2 l1 l2 H1 H2 a1 a2 D G1 G2.
     &0 < k /\ &0 < l /\ N = k * l /\
     G1 = l * r * N / &2 * g /\ G2 = l * s * N / &2 * g /\
     &0 <= G1 /\ &0 <= G2 /\
     (rho - &1) * l1 + &2 * H1 <= a1 /\ (rho - &1) * l2 + &2 * H2 <= a2 /\
     ((l - &1) / &2 * S1 + G1) * l1 - &2 * G1 * H1 +
     ((l - &1) / &2 * S2 + G2) * l2 - &2 * G2 * H2 -
     (nn - &1) * (AF + N / &2 * ((k - &1) * Lx - &2 / k * SLF)) <= D /\
     D <= N * A2 + AF - N * (N - &1) / &2 * Lr +
          (N * (k - &1) / &2 * (Lr + Lx) - l * SLF) +
          ((l - &1) / &2 * (S1 * l1 + S2 * l2) + rho * (G1 * l1 + G2 * l2))
     ==> ~(&2 * A2 + &2 * nn / N * AF +
           nn * ((k - &1) * Lx - &2 / k * SLF) +
           g * l * (r * a1 + s * a2) < k * (l - &1) * Lr)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `G1 * ((rho - &1) * l1 + &2 * H1) <= G1 * a1 /\
    G2 * ((rho - &1) * l2 + &2 * H2) <= G2 * a2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < N / &2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[REAL_LT_MUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `N * (k - &1) / &2 * (Lr + Lx) - l * SLF =
    N * (k - &1) / &2 * Lr + N / &2 * ((k - &1) * Lx - &2 / k * SLF)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < k` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_LMUL o CONJ
    (ASSUME `&0 < N / &2`)) THEN
  SUBGOAL_THEN
   `N / &2 * (&2 * A2 + &2 * nn / N * AF +
              nn * ((k - &1) * Lx - &2 / k * SLF) +
              g * l * (r * a1 + s * a2)) =
    N * A2 + nn * AF + nn * (N / &2 * ((k - &1) * Lx - &2 / k * SLF)) +
    G1 * a1 + G2 * a2`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < k` THEN UNDISCH_TAC `&0 < l` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `N / &2 * (k * (l - &1) * Lr) =
    (N * (N - &1) / &2 - N * (k - &1) / &2) * Lr`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `Q = (k - &1) * Lx - &2 / k * SLF` THEN
  MAP_EVERY UNDISCH_TAC
   [`((l - &1) / &2 * S1 + G1) * l1 - &2 * G1 * H1 +
     ((l - &1) / &2 * S2 + G2) * l2 - &2 * G2 * H2 -
     (nn - &1) * (AF + N / &2 * Q) <= D`;
    `D <= N * A2 + AF - N * (N - &1) / &2 * Lr +
          (N * (k - &1) / &2 * (Lr + Lx) - l * SLF) +
          ((l - &1) / &2 * (S1 * l1 + S2 * l2) + rho * (G1 * l1 + G2 * l2))`;
    `N * (k - &1) / &2 * (Lr + Lx) - l * SLF =
     N * (k - &1) / &2 * Lr + N / &2 * Q`;
    `G1 * ((rho - &1) * l1 + &2 * H1) <= G1 * a1`;
    `G2 * ((rho - &1) * l2 + &2 * H2) <= G2 * a2`] THEN
  REAL_ARITH_TAC);;

let TWOLOG_LAURENT_CORE = prove
 (`!p1 q1 p2 q2 b1 b2 K L R S N (rr:num->num) (ss:num->num) rho a1 a2.
     1 <= q1 /\ q1 <= p1 /\ 1 <= q2 /\ q2 <= p2 /\ 1 <= b1 /\ 1 <= b2 /\
     1 <= K /\ 1 <= L /\ 2 <= R /\ 1 <= S /\ N = K * L /\
     (!j. j IN 1..N ==> rr j < R /\ ss j < S) /\
     ~(ring_det real_ring (1..N)
         (\i j. &(binom(rr j * b2 + ss j * b1,(i - 1) MOD K)) *
                (&p1 / &q1) pow (((i - 1) DIV K) * rr j) *
                (&p2 / &q2) pow (((i - 1) DIV K) * ss j)) = &0) /\
     &b1 * log(&p1 / &q1) <= &b2 * log(&p2 / &q2) /\
     &1 < rho /\
     (rho - &1) * log(&p1 / &q1) + &2 * log(&p1) <= a1 /\
     (rho - &1) * log(&p2 / &q2) + &2 * log(&p2) <= a2 /\
     &2 * log(&2) + &2 / &N * log(&(FACT N)) +
     (&K - &1) * log(&((R - 1) * b2 + (S - 1) * b1) / &2) -
     &2 / &K * sum(1..K - 1) (\k. log(&(FACT k))) +
     (&1 / &4 - &N / (&12 * &R * &S)) * &L * (&R * a1 + &S * a2)
     < &K * (&L - &1) * log rho
     ==> inv(rho pow N) <
         &(L * S) *
         abs(&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1)) / (&2 * &b2) *
         exp(&(L * S) * abs(&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1)) /
             (&2 * &b2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_THEN `N = K * L` SUBST_ALL_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &K` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN UNDISCH_TAC `1 <= K` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &L` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN UNDISCH_TAC `1 <= L` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL
   [UNDISCH_TAC `&1 < rho` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &((R - 1) * b2 + (S - 1) * b1) / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
    REWRITE_TAC[ARITH_RULE `0 < x + y <=> ~(x = 0) \/ ~(y = 0)`;
                MULT_EQ_0] THEN
    MAP_EVERY UNDISCH_TAC [`2 <= R`; `1 <= b2`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&p1 / &q1) /\ &0 <= log(&p2 / &q2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC TL_LAURENT_CORE_LOG_RATIO_POS THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`&p1 / &q1`; `&p2 / &q2`; `b1:num`; `b2:num`; `K:num`;
                `L:num`; `R:num`; `S:num`; `K * L`; `rr:num->num`;
                `ss:num->num`] LAURENT_GLEMMA_BOTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `g = &1 / &4 - &(K * L) / (&12 * &R * &S)` THEN
  ABBREV_TAC `G1 = &L * &R * &(K * L) / &2 * g` THEN
  ABBREV_TAC `G2 = &L * &S * &(K * L) / &2 * g` THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`p1:num`; `q1:num`; `p2:num`; `q2:num`; `b1:num`; `b2:num`;
                `K:num`; `L:num`; `K * L`; `rr:num->num`; `ss:num->num`;
                `G1:real`; `G2:real`] TWOLOG_LAURENT_ARITH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`b1:num`; `b2:num`; `K:num`; `L:num`; `R:num`; `S:num`;
                `K * L`; `rr:num->num`; `ss:num->num`; `log(&p1 / &q1)`;
                `log(&p2 / &q2)`; `rho:real`; `G1:real`; `G2:real`]
    TWOLOG_LAURENT_ANALYTIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`&p1 / &q1`; `&p2 / &q2`; `b1:num`; `b2:num`; `K:num`;
                `rr:num->num`; `ss:num->num`] LAURENT_EXP_MATRIX) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    MAP_EVERY UNDISCH_TAC [`1 <= q1`; `q1 <= p1`; `1 <= q2`; `q2 <= p2`] THEN
    ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  DISCH_TAC THEN
  ABBREV_TAC
   `Dt = ring_det real_ring (1..K * L)
          (\i j. &(binom(rr j * b2 + ss j * b1,(i - 1) MOD K)) *
                 (&p1 / &q1) pow (((i - 1) DIV K) * rr j) *
                 (&p2 / &q2) pow (((i - 1) DIV K) * ss j))` THEN
  SUBGOAL_THEN `&0 < abs Dt` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_ABS_NZ]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LOG_MONO_LE_IMP o
    CONJ (ASSUME `&0 < abs Dt`)) THEN
  SIMP_TAC[TL_LAURENT_CORE_LOG_UPPER; ASSUME `1 <= K`; ASSUME `&0 < rho`;
           ASSUME `&0 < &((R - 1) * b2 + (S - 1) * b1) / &2`] THEN
  DISCH_TAC THEN
  MP_TAC(REWRITE_RULE[REAL_SUB_REFL; REAL_MUL_LZERO; REAL_SUB_RZERO;
                      REAL_MUL_LID; REAL_ARITH `&2 * &1 / x * y = &2 / x * y`]
   (SPECL [`&1`; `&(K * L)`; `&K`; `&L`; `&R`; `&S`; `g:real`; `rho:real`;
           `log(&2)`; `log(&(FACT(K * L)))`; `log rho`;
           `log(&((R - 1) * b2 + (S - 1) * b1) / &2)`;
           `sum(1..K - 1) (\k. log(&(FACT k)))`;
           `&(nsum(1..K * L) rr)`; `&(nsum(1..K * L) ss)`;
           `log(&p1 / &q1)`; `log(&p2 / &q2)`; `log(&p1)`; `log(&p2)`;
           `a1:real`; `a2:real`; `log(abs Dt)`; `G1:real`; `G2:real`]
    LAURENT_CORE_FINAL)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE FIRST_ASSUM(ACCEPT_TAC o SYM) ORELSE
     REWRITE_TAC[REAL_OF_NUM_MUL]);
    REWRITE_TAC[TAUT `~p ==> F <=> p`] THEN FIRST_ASSUM ACCEPT_TAC]);;
