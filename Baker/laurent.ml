(* ========================================================================= *)
(* Two logarithms, the Laurent bound: the lower bounds for linear            *)
(* forms in two logarithms of rationals.                                     *)
(*                                                                           *)
(* Purpose: M. Laurent, Linear forms in two logarithms and interpolation     *)
(* determinants II, Acta Arith. 133 (2008), Theorem 2 at mu = 1 and          *)
(* Corollary 2 (with the constant 32 instead of 25.2) for                    *)
(*   Lambda = b2 log(p2/q2) - b1 log(p1/q1),                                 *)
(* and the corresponding bound for coefficients of any sign.                 *)
(*                                                                           *)
(* Main results (helper names with the prefix TL_LAURENT_FINAL_):            *)
(*  - LAURENT_RATIONAL_PARAM (Theorem-2 form, rho in [4, 8], h >= 10): log   *)
(*    |Lambda| >= -laurent_bound rho h a1 a2;                                *)
(*  - LAURENT_RATIONAL_PARAM_LARGE (the same in the regime a_i >= rho + 1,   *)
(*    threshold log b + log log rho + 3/2 instead of 5/2);                   *)
(*  - LAURENT_RATIONAL (Corollary 2, D = 1): |Lambda| >= exp(-32 max(10,     *)
(*    log(b1/A2 + b2/A1) + 0.38)^2 A1 A2);                                   *)
(*  - LAURENT_RATIONAL_GENERAL (all positive rationals, nonzero integer      *)
(*    coefficients of any sign, A_i >= max(1, log max(p_i, q_i))).           *)
(*                                                                           *)
(* Route: the parameters K, L, R1, S1, R2, S2 come from LAURENT_PARAMETERS   *)
(* (_LARGE) with D = 1. If the multiplicative grid map (r, s) -> a1^r a2^s   *)
(* on R1 x S1 or the additive grid map (r, s) -> r b2 + s b1 on R2 x S2 has  *)
(* a collision, Liouville with small coefficients (TL_FINAL_MCOLL,           *)
(* TL_FINAL_ACOLL of Baker/twolog.ml, with the heights h_i = log p_i) gives  *)
(* a much better bound, by the export R a1 + S a2 <= C X / 2. Otherwise      *)
(* TWOLOG_ZERO_MINOR_BINOM gives a non-zero minor and TWOLOG_LAURENT_CORE    *)
(* gives rho^(-N) < t e^t, t = L S |Lambda| / (2 b2), in the ordered case    *)
(* b1 log a1 <= b2 log a2; with N log rho <= M and L S <= 1.86 P this        *)
(* yields |Lambda| >= e^-M / P (TL_LAURENT_FINAL_LAMBDA_PRIME: t is tiny,    *)
(* e^t <= 1 + 2 t). The other order follows by exchanging the two logarithms *)
(* (laurent_main is symmetric). The corollary takes rho = 5, a_i = 6 A_i,    *)
(* h = max(10, log b + 0.38) in the large regime and the corner constant     *)
(* LAURENT_BOUND_CORNER_5_10; the general form reduces to it via             *)
(* |log(p/q)| = log(max/min) and the sign pattern of the two terms.          *)
(*                                                                           *)
(* Uses: Baker/laurent_binom.ml (TWOLOG_ZERO_MINOR_BINOM),                   *)
(* Baker/laurent_core.ml (TWOLOG_LAURENT_CORE), Baker/laurent_param.ml       *)
(* (LAURENT_PARAMETERS, LAURENT_PARAMETERS_LARGE), Baker/laurent_corner.ml   *)
(* (LAURENT_BOUND_CORNER_5_10, LAURENT_CORNER_LOG_BOUNDS,                    *)
(* LAURENT_CORNER_EXP_8_5, LAURENT_CORNER_LOG_5), Baker/laurent_defs.ml      *)
(* (laurent_bound, laurent_main), Baker/twolog.ml (CARD_IMAGE_INJ_GRID,      *)
(* TL_FINAL_MCOLL, TL_FINAL_ACOLL, LOG_RATIO_LOWER_HEIGHT, LOG_LE_SUB_1),    *)
(* Baker/lemmas.ml (INV_POW_EXP_NEG).                                        *)
(*                                                                           *)
(* Contents.                                                                 *)
(*  1. Elementary facts about exp and log.                                   *)
(*  2. From the conclusion of the core (Lambda prime) to Lambda.             *)
(*  3. The numeric layer: symmetry of laurent_main, the D = 1 form,          *)
(*     laurent_bound unfolded.                                               *)
(*  4. The main case: both grid maps injective.                              *)
(*  5. Collisions and the ordered theorem; symmetry.                         *)
(*  6. The Theorem-2 forms LAURENT_RATIONAL_PARAM(_LARGE).                   *)
(*  7. Corollary 2: LAURENT_RATIONAL.                                        *)
(*  8. All signs: LAURENT_RATIONAL_GENERAL.                                  *)
(* ========================================================================= *)

needs "Baker/laurent_core.ml";;
needs "Baker/laurent_param.ml";;
needs "Baker/laurent_corner.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* 1. Elementary facts about exp and log.                                    *)
(* ------------------------------------------------------------------------- *)

let TL_LAURENT_FINAL_EXP_8 = prove
 (`&81 <= exp(&8)`,
  SUBGOAL_THEN `exp(&8) = exp(&2) pow 4` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_N] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 pow 4` THEN
  CONJ_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN
  MP_TAC(SPEC `&2` REAL_EXP_LE_X) THEN REAL_ARITH_TAC);;

let EXP_LE_IMP_LE_LOG = prove
 (`!x y. exp x <= y ==> x <= log y`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
  MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT]);;

let LOG_RATIO_ABS_MAX_MIN = prove
 (`!p q. 1 <= p /\ 1 <= q
         ==> abs(log(&p / &q)) = log(&(MAX p q) / &(MIN p q))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &p /\ &0 < &q` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN
    MAP_EVERY UNDISCH_TAC [`1 <= p`; `1 <= q`] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MAX; MIN] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[LOG_DIV] THENL
   [MP_TAC(SPECL [`&p:real`; `&q:real`] LOG_MONO_LE_IMP) THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    MP_TAC(SPECL [`&q:real`; `&p:real`] LOG_MONO_LE_IMP) THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; REAL_ARITH_TAC]]);;

let INTEGER_NONZERO_ABS_NUM = prove
 (`!x. integer x /\ ~(x = &0) ==> ?n. 1 <= n /\ abs x = &n`,
  GEN_TAC THEN REWRITE_TAC[integer] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `n:num`) ASSUME_TAC) THEN
  EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN DISCH_TAC THEN
  UNDISCH_TAC `~(x = &0)` THEN REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM REAL_ABS_ZERO] THEN ASM_REWRITE_TAC[]);;

let TL_LAURENT_FINAL_LOG_6 = prove
 (`&1774 / &1000 <= log(&6)`,
  MP_TAC(SPECL [`&6`; `&8 / &5`; `&4953 / &1000`; `&4954 / &1000`]
    LAURENT_CORNER_LOG_BOUNDS) THEN
  REWRITE_TAC[LAURENT_CORNER_EXP_8_5] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let TL_LAURENT_FINAL_LOG_LOG_5 = prove
 (`log(log(&5)) <= &61 / &100`,
  MP_TAC LAURENT_CORNER_LOG_5 THEN STRIP_TAC THEN
  MP_TAC(SPEC `log(&5)` LOG_LE_SUB_1) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 2. From the conclusion of the core to Lambda: if rho^(-N) <= x and        *)
(*    x < u e^u with u = m t / (2 b), m <= 1.86 P, N log rho <= M,           *)
(*    M >= 8, then t >= e^(-M) / P (Laurent 2008, section 3.4).              *)
(*    Proof by contradiction: otherwise u <= 0.93 P t < 1/80, so             *)
(*    e^u <= 1 + 2 u and u e^u <= P t < e^(-M) <= x.                         *)
(* ------------------------------------------------------------------------- *)

let TL_LAURENT_FINAL_LAMBDA_PRIME = prove
 (`!t m b x M P.
     &0 <= t /\ &0 <= m /\ &1 <= b /\ &0 < P /\
     m <= &186 / &100 * P /\ &8 <= M /\
     exp(--M) <= x /\ x < m * t / (&2 * b) * exp(m * t / (&2 * b))
     ==> exp(--(M + log P)) <= t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `exp(--(M + log P)) = exp(--M) / P` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_NEG_ADD; REAL_EXP_ADD; REAL_EXP_NEG] THEN
    ASM_SIMP_TAC[EXP_LOG; real_div; REAL_INV_MUL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `exp(--M) <= inv(&81)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_NEG] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(&8)` THEN
    REWRITE_TAC[TL_LAURENT_FINAL_EXP_8; REAL_EXP_MONO_LE] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `u = m * t / (&2 * b)` THEN
  SUBGOAL_THEN `m * t / (&2 * b) * exp u = u * exp u` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[REAL_MUL_ASSOC]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= u` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `u * (&2 * b) = m * t` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= u * (b - &1) /\ m * t <= (&186 / &100 * P) * t`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `u <= &93 / &100 * (t * P)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`&0 <= u * (b - &1)`; `m * t <= (&186 / &100 * P) * t`;
      `u * (&2 * b) = m * t`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `u <= &93 / &100 * inv(&81)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`u <= &93 / &100 * (t * P)`; `t * P < exp(--M)`;
      `exp(--M) <= inv(&81)`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp u <= &1 + &2 * (&93 / &100 * inv(&81))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + &2 * u` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EXP_BOUND_LEMMA THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `u <= &93 / &100 * inv(&81)` THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      UNDISCH_TAC `u <= &93 / &100 * inv(&81)` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `u * exp u <= (&93 / &100 * (t * P)) * (&1 + &2 * (&93 / &100 * inv(&81)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= t * P` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`u * exp u <= (&93 / &100 * (t * P)) *
                  (&1 + &2 * (&93 / &100 * inv(&81)))`;
    `&0 <= t * P`; `t * P < exp(--M)`; `exp(--M) <= x`;
    `x < m * t / (&2 * b) * exp u`;
    `m * t / (&2 * b) * exp u = u * exp u`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 3. The numeric layer: laurent_main is symmetric under the exchange        *)
(*    of the two logarithms; at D = 1 it is the main hypothesis of           *)
(*    TWOLOG_LAURENT_CORE; laurent_bound = M + log P with the exported       *)
(*    M and P of LAURENT_PARAMETERS; the sqrt term of M is >= 0.             *)
(* ------------------------------------------------------------------------- *)

let LAURENT_MAIN_SYM = prove
 (`!D rho b1 b2 a1 a2 K L R S.
     laurent_main D rho b1 b2 a1 a2 K L R S <=>
     laurent_main D rho b2 b1 a2 a1 K L S R`,
  REPEAT GEN_TAC THEN REWRITE_TAC[laurent_main] THEN
  SUBGOAL_THEN `(S - 1) * b1 + (R - 1) * b2 = (R - 1) * b2 + (S - 1) * b1`
  SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&12 * &S * &R = &12 * &R * (&S:real) /\
                &S * a2 + &R * a1 = &R * a1 + &S * (a2:real)`
   (fun th -> REWRITE_TAC[th]) THEN
  REAL_ARITH_TAC);;

let TL_LAURENT_FINAL_MAIN_D1 = prove
 (`!rho b1 b2 a1 a2 K L R S N.
     N = K * L /\ laurent_main 1 rho b1 b2 a1 a2 K L R S
     ==> &2 * log(&2) + &2 / &N * log(&(FACT N)) +
         (&K - &1) * log(&((R - 1) * b2 + (S - 1) * b1) / &2) -
         &2 / &K * sum(1..K - 1) (\k. log(&(FACT k))) +
         (&1 / &4 - &N / (&12 * &R * &S)) * &L * (&R * a1 + &S * a2)
         < &K * (&L - &1) * log rho`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
  REWRITE_TAC[laurent_main] THEN REAL_ARITH_TAC);;

let TL_LAURENT_FINAL_BOUND_EQ = prove
 (`!rho h a1 a2.
     laurent_bound rho h a1 a2 =
     (laurent_C rho h a1 a2 * (h + log rho) pow 2 * a1 * a2 +
      sqrt(laurent_omega (h / log rho + &1) *
           laurent_theta (h / log rho + &1)) * (h + log rho)) +
     log(laurent_Cp rho h a1 a2 * (h + log rho) pow 2 * a1 * a2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[laurent_bound] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[REAL_ADD_ASSOC]);;

let TL_LAURENT_FINAL_SQRT_TERM_POS = prove
 (`!rho h. &1 < rho /\ &0 <= h
           ==> &0 <= sqrt(laurent_omega (h / log rho + &1) *
                          laurent_theta (h / log rho + &1)) * (h + log rho)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < log rho` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `H = h / log rho + &1` THEN
  SUBGOAL_THEN `&1 <= H` ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= x + &1`) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(&1 + inv(&4 * H pow 2))` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    REWRITE_TAC[REAL_LE_INV_EQ] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN
  REWRITE_TAC[laurent_omega; laurent_theta] THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= y ==> &0 <= x + y`) THEN
  ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 4. The main case: both grid maps injective. The cardinality               *)
(*    conditions of TWOLOG_ZERO_MINOR_BINOM hold, TWOLOG_LAURENT_CORE        *)
(*    applies (ordered case), and section 2 concludes.                       *)
(* ------------------------------------------------------------------------- *)

let TL_LAURENT_FINAL_MAIN_CASE = prove
 (`!p1 q1 p2 q2 b1 b2 rho a1 a2 K L R1 S1 R2 S2 M P.
     1 <= q1 /\ q1 < p1 /\ 1 <= q2 /\ q2 < p2 /\ 1 <= b1 /\ 1 <= b2 /\
     &1 < rho /\
     (rho - &1) * log(&p1 / &q1) + &2 * log(&p1) <= a1 /\
     (rho - &1) * log(&p2 / &q2) + &2 * log(&p2) <= a2 /\
     2 <= K /\ 2 <= L /\ 2 <= (R1 + R2) - 1 /\ 2 <= (S1 + S2) - 1 /\
     L <= R1 * S1 /\ (K - 1) * L < R2 * S2 /\
     laurent_main 1 rho b1 b2 a1 a2 K L ((R1 + R2) - 1) ((S1 + S2) - 1) /\
     &(K * L) * log rho <= M /\ &8 <= M /\ &0 < P /\
     &(L * ((S1 + S2) - 1)) <= &186 / &100 * P /\
     &b1 * log(&p1 / &q1) <= &b2 * log(&p2 / &q2) /\
     (!r s r' s'. r < R1 /\ s < S1 /\ r' < R1 /\ s' < S1 /\
                  (&p1 / &q1) pow r * (&p2 / &q2) pow s =
                  (&p1 / &q1) pow r' * (&p2 / &q2) pow s'
                  ==> r = r' /\ s = s') /\
     (!r s r' s'. r < R2 /\ s < S2 /\ r' < R2 /\ s' < S2 /\
                  r * b2 + s * b1 = r' * b2 + s' * b1
                  ==> r = r' /\ s = s')
     ==> exp(--(M + log P)) <=
         abs(&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `1 <= p1 /\ 1 <= p2 /\ 1 <= K /\ 1 <= L /\ q1 <= p1 /\ q2 <= p2 /\
    1 <= (S1 + S2) - 1`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`1 <= q1`; `q1 < p1`; `1 <= q2`; `q2 < p2`; `2 <= K`; `2 <= L`;
      `2 <= (S1 + S2) - 1`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL
   [UNDISCH_TAC `&1 < rho` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\r s. (&p1 / &q1) pow r * (&p2 / &q2) pow s`;
                 `R1:num`; `S1:num`] CARD_IMAGE_INJ_GRID) THEN
  BETA_TAC THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`\r s. r * b2 + s * b1`; `R2:num`; `S2:num`]
    CARD_IMAGE_INJ_GRID) THEN
  BETA_TAC THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`p1:num`; `q1:num`; `p2:num`; `q2:num`; `b1:num`; `b2:num`;
                `K:num`; `L:num`; `R1:num`; `S1:num`; `R2:num`; `S2:num`]
    TWOLOG_ZERO_MINOR_BINOM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rr:num->num`
   (X_CHOOSE_THEN `ss:num->num` STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`p1:num`; `q1:num`; `p2:num`; `q2:num`; `b1:num`; `b2:num`;
                `K:num`; `L:num`; `(R1 + R2) - 1`; `(S1 + S2) - 1`; `K * L`;
                `rr:num->num`; `ss:num->num`; `rho:real`; `a1:real`;
                `a2:real`] TWOLOG_LAURENT_CORE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC TL_LAURENT_FINAL_MAIN_D1 THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MATCH_MP_TAC TL_LAURENT_FINAL_LAMBDA_PRIME THEN
  MAP_EVERY EXISTS_TAC
   [`&(L * ((S1 + S2) - 1))`; `&b2`; `inv(rho pow (K * L))`] THEN
  ASM_REWRITE_TAC[REAL_ABS_POS; REAL_POS; REAL_OF_NUM_LE] THEN
  MP_TAC(SPECL [`rho:real`; `K * L`] INV_POW_EXP_NEG) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 5. Collisions of the grid maps (Liouville with small coefficients,        *)
(*    heights h_i = log p_i; the cost 2 (R a1 + S a2) <= M is the            *)
(*    export of the numeric layer), the ordered theorem, and the             *)
(*    general key theorem by exchanging the two logarithms.                  *)
(* ------------------------------------------------------------------------- *)

let TL_LAURENT_FINAL_COLL_NUMERIC = prove
 (`!a1 a2 l1 l2 R S R1 R2 S2 M.
     &1 <= a1 /\ &1 <= a2 /\ &0 <= l1 /\ &0 <= l2 /\
     &2 * l1 <= a1 /\ &2 * l2 <= a2 /\
     1 <= R /\ 1 <= S /\ R1 <= R /\ R2 <= R /\ S2 <= S /\
     &2 * (&R * a1 + &S * a2) <= M
     ==> &2 * l1 + &2 * l2 + &R1 <= M /\
         &2 * (&S2 * l2 + &R2 * l1) + &R2 <= M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &R /\ &1 <= &S /\ &R1 <= &R /\ &R2 <= &R /\ &S2 <= &S`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&1 * a1 <= &R * a1 /\ &1 * a2 <= &S * a2 /\ &R * &1 <= &R * a1 /\
    &R2 * (&2 * l1) <= &R2 * a1 /\ &S2 * (&2 * l2) <= &S2 * a2 /\
    &R2 * a1 <= &R * a1 /\ &S2 * a2 <= &S * a2`
  MP_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let TL_LAURENT_FINAL_ORDERED = prove
 (`!p1 q1 p2 q2 b1 b2 rho a1 a2 K L R1 S1 R2 S2 M P.
     1 <= q1 /\ q1 < p1 /\ 1 <= q2 /\ q2 < p2 /\ 1 <= b1 /\ 1 <= b2 /\
     &1 < rho /\
     &1 <= a1 /\ (rho - &1) * log(&p1 / &q1) + &2 * log(&p1) <= a1 /\
     &1 <= a2 /\ (rho - &1) * log(&p2 / &q2) + &2 * log(&p2) <= a2 /\
     2 <= K /\ 2 <= L /\ 1 <= R1 /\ 1 <= S1 /\ 1 <= R2 /\ 1 <= S2 /\
     2 <= (R1 + R2) - 1 /\ 2 <= (S1 + S2) - 1 /\
     L <= R1 * S1 /\ (K - 1) * L < R2 * S2 /\
     laurent_main 1 rho b1 b2 a1 a2 K L ((R1 + R2) - 1) ((S1 + S2) - 1) /\
     &(K * L) * log rho <= M /\
     &(L * ((S1 + S2) - 1)) <= &186 / &100 * P /\
     &2 * (&((R1 + R2) - 1) * a1 + &((S1 + S2) - 1) * a2) <= M /\
     &b1 * log(&p1 / &q1) <= &b2 * log(&p2 / &q2) /\
     ~(&b2 * log(&p2 / &q2) = &b1 * log(&p1 / &q1))
     ==> exp(--(M + log P)) <=
         abs(&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= p1 /\ 1 <= p2 /\ q1 <= p1 /\ q2 <= p2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`1 <= q1`; `q1 < p1`; `1 <= q2`; `q2 < p2`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= log(&p1) /\ &0 <= log(&p2) /\
    log(&q1) <= log(&p1) /\ log(&q2) <= log(&p2) /\
    &0 <= log(&p1 / &q1) /\ &0 <= log(&p2 / &q2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC LOG_POS) THEN
    TRY(MATCH_MP_TAC LOG_MONO_LE_IMP) THEN
    ASM_SIMP_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT; REAL_LE_RDIV_EQ;
                 ARITH_RULE `1 <= q ==> 0 < q`; REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * log(&p1) <= a1 /\ &2 * log(&p2) <= a2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= (rho - &1) * log(&p1 / &q1) /\
                  &0 <= (rho - &1) * log(&p2 / &q2)`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY UNDISCH_TAC
       [`(rho - &1) * log(&p1 / &q1) + &2 * log(&p1) <= a1`;
        `(rho - &1) * log(&p2 / &q2) + &2 * log(&p2) <= a2`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= P /\ &8 <= M` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 <= &((R1 + R2) - 1) /\ &2 <= &((S1 + S2) - 1) /\
                  &4 <= &(L * ((S1 + S2) - 1))`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(ARITH_RULE `2 * 2 <= x ==> 4 <= x`) THEN
      MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&2 * &1 <= &((R1 + R2) - 1) * a1 /\
                  &2 * &1 <= &((S1 + S2) - 1) * a2`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`&4 <= &(L * ((S1 + S2) - 1))`;
      `&(L * ((S1 + S2) - 1)) <= &186 / &100 * P`;
      `&2 * (&((R1 + R2) - 1) * a1 + &((S1 + S2) - 1) * a2) <= M`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < P /\ &0 <= log P` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC LOG_POS] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`a1:real`; `a2:real`; `log(&p1)`; `log(&p2)`;
                `(R1 + R2) - 1`; `(S1 + S2) - 1`; `R1:num`; `R2:num`;
                `S2:num`; `M:real`] TL_LAURENT_FINAL_COLL_NUMERIC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`1 <= R1`; `1 <= R2`; `1 <= S1`; `1 <= S2`] THEN
    ARITH_TAC;
    STRIP_TAC] THEN
  ASM_CASES_TAC
   `!r s r' s'. r < R1 /\ s < S1 /\ r' < R1 /\ s' < S1 /\
                (&p1 / &q1) pow r * (&p2 / &q2) pow s =
                (&p1 / &q1) pow r' * (&p2 / &q2) pow s'
                ==> r = r' /\ s = s'`
  THENL
   [ALL_TAC;
    POP_ASSUM(MP_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`r:num`; `s:num`; `r':num`; `s':num`] THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(--(&2 * log(&p1) + &2 * log(&p2) + &R1))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= m /\ &0 <= l ==> --(m + l) <= --x`) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC TL_FINAL_MCOLL THEN
      MAP_EVERY EXISTS_TAC [`r:num`; `s:num`; `r':num`; `s':num`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL; REAL_SUB_0]]] THEN
  ASM_CASES_TAC
   `!r s r' s'. r < R2 /\ s < S2 /\ r' < R2 /\ s' < S2 /\
                r * b2 + s * b1 = r' * b2 + s' * b1
                ==> r = r' /\ s = s'`
  THENL
   [ALL_TAC;
    POP_ASSUM(MP_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`r:num`; `s:num`; `r':num`; `s':num`] THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(--(&2 * (&S2 * log(&p2) + &R2 * log(&p1)) + &R2))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= m /\ &0 <= l ==> --(m + l) <= --x`) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC TL_FINAL_ACOLL THEN
      MAP_EVERY EXISTS_TAC [`r:num`; `s:num`; `r':num`; `s':num`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL; REAL_SUB_0]]] THEN
  MATCH_MP_TAC TL_LAURENT_FINAL_MAIN_CASE THEN
  MAP_EVERY EXISTS_TAC [`rho:real`; `a1:real`; `a2:real`; `K:num`; `L:num`;
                        `R1:num`; `S1:num`; `R2:num`; `S2:num`] THEN
  ASM_REWRITE_TAC[]);;

let TL_LAURENT_FINAL_KEY = prove
 (`!p1 q1 p2 q2 b1 b2 rho a1 a2 K L R1 S1 R2 S2 M P.
     1 <= q1 /\ q1 < p1 /\ 1 <= q2 /\ q2 < p2 /\ 1 <= b1 /\ 1 <= b2 /\
     &1 < rho /\
     &1 <= a1 /\ (rho - &1) * log(&p1 / &q1) + &2 * log(&p1) <= a1 /\
     &1 <= a2 /\ (rho - &1) * log(&p2 / &q2) + &2 * log(&p2) <= a2 /\
     2 <= K /\ 2 <= L /\ 1 <= R1 /\ 1 <= S1 /\ 1 <= R2 /\ 1 <= S2 /\
     2 <= (R1 + R2) - 1 /\ 2 <= (S1 + S2) - 1 /\
     L <= R1 * S1 /\ (K - 1) * L < R2 * S2 /\
     laurent_main 1 rho b1 b2 a1 a2 K L ((R1 + R2) - 1) ((S1 + S2) - 1) /\
     &(K * L) * log rho <= M /\
     &(L * ((R1 + R2) - 1)) <= &186 / &100 * P /\
     &(L * ((S1 + S2) - 1)) <= &186 / &100 * P /\
     &2 * (&((R1 + R2) - 1) * a1 + &((S1 + S2) - 1) * a2) <= M /\
     ~(&b2 * log(&p2 / &q2) = &b1 * log(&p1 / &q1))
     ==> exp(--(M + log P)) <=
         abs(&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `&b1 * log(&p1 / &q1) <= &b2 * log(&p2 / &q2)` THENL
   [MATCH_MP_TAC TL_LAURENT_FINAL_ORDERED THEN
    MAP_EVERY EXISTS_TAC [`rho:real`; `a1:real`; `a2:real`; `K:num`;
                          `L:num`; `R1:num`; `S1:num`; `R2:num`; `S2:num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `L <= S1 * R1 /\ (K - 1) * L < S2 * R2 /\
    &2 * (&((S1 + S2) - 1) * a2 + &((R1 + R2) - 1) * a1) <= M /\
    &b2 * log(&p2 / &q2) <= &b1 * log(&p1 / &q1) /\
    ~(&b1 * log(&p1 / &q1) = &b2 * log(&p2 / &q2))`
  STRIP_ASSUME_TAC THENL
   [SUBST1_TAC(SPECL [`S1:num`; `R1:num`] MULT_SYM) THEN
    SUBST1_TAC(SPECL [`S2:num`; `R2:num`] MULT_SYM) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`~(&b1 * log(&p1 / &q1) <= &b2 * log(&p2 / &q2))`;
      `~(&b2 * log(&p2 / &q2) = &b1 * log(&p1 / &q1))`;
      `&2 * (&((R1 + R2) - 1) * a1 + &((S1 + S2) - 1) * a2) <= M`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_ABS_SUB] THEN
  MATCH_MP_TAC TL_LAURENT_FINAL_ORDERED THEN
  MAP_EVERY EXISTS_TAC [`rho:real`; `a2:real`; `a1:real`; `K:num`;
                        `L:num`; `S1:num`; `R1:num`; `S2:num`; `R2:num`] THEN
  ONCE_REWRITE_TAC[LAURENT_MAIN_SYM] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 6. The Theorem-2 forms (Laurent 2008, Theorem 2 at mu = 1, D = 1):        *)
(*    the regime a_i >= 1, a1 a2 >= (log rho)^2 with threshold 5/2           *)
(*    (LAURENT_PARAMETERS) and the regime a_i >= rho + 1 with                *)
(*    threshold 3/2 (LAURENT_PARAMETERS_LARGE).                              *)
(* ------------------------------------------------------------------------- *)

let TL_LAURENT_FINAL_FROM_EXPORTS = prove
 (`!p1 q1 p2 q2 b1 b2 rho h a1 a2 K L R1 S1 R2 S2.
     1 <= q1 /\ q1 < p1 /\ 1 <= q2 /\ q2 < p2 /\ 1 <= b1 /\ 1 <= b2 /\
     &4 <= rho /\ &10 <= h /\
     &1 <= a1 /\ (rho - &1) * log(&p1 / &q1) + &2 * log(&p1) <= a1 /\
     &1 <= a2 /\ (rho - &1) * log(&p2 / &q2) + &2 * log(&p2) <= a2 /\
     ~(&b2 * log(&p2 / &q2) = &b1 * log(&p1 / &q1)) /\
     2 <= K /\ 2 <= L /\ 1 <= R1 /\ 1 <= S1 /\ 1 <= R2 /\ 1 <= S2 /\
     2 <= (R1 + R2) - 1 /\ 2 <= (S1 + S2) - 1 /\
     L <= R1 * S1 /\ (K - 1) * L < R2 * S2 /\
     laurent_main 1 rho b1 b2 a1 a2 K L ((R1 + R2) - 1) ((S1 + S2) - 1) /\
     &(K * L) * log rho <=
       laurent_C rho h a1 a2 * (h + log rho) pow 2 * a1 * a2 +
       sqrt(laurent_omega (h / log rho + &1) *
            laurent_theta (h / log rho + &1)) * (h + log rho) /\
     &(L * ((R1 + R2) - 1)) <=
       &186 / &100 * laurent_Cp rho h a1 a2 * (h + log rho) pow 2 * a1 * a2 /\
     &(L * ((S1 + S2) - 1)) <=
       &186 / &100 * laurent_Cp rho h a1 a2 * (h + log rho) pow 2 * a1 * a2 /\
     &((R1 + R2) - 1) * a1 + &((S1 + S2) - 1) * a2 <=
       laurent_C rho h a1 a2 * (h + log rho) pow 2 * a1 * a2 / &2
     ==> --(laurent_bound rho h a1 a2) <=
         log(abs(&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`rho:real`; `h:real`] TL_LAURENT_FINAL_SQRT_TERM_POS) THEN
  ANTS_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&4 <= rho`; `&10 <= h`] THEN REAL_ARITH_TAC;
    DISCH_TAC] THEN
  REWRITE_TAC[TL_LAURENT_FINAL_BOUND_EQ] THEN
  MATCH_MP_TAC EXP_LE_IMP_LE_LOG THEN
  MATCH_MP_TAC TL_LAURENT_FINAL_KEY THEN
  MAP_EVERY EXISTS_TAC [`rho:real`; `a1:real`; `a2:real`; `K:num`; `L:num`;
                        `R1:num`; `S1:num`; `R2:num`; `S2:num`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `&4 <= rho` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`&((R1 + R2) - 1) * a1 + &((S1 + S2) - 1) * a2 <=
       laurent_C rho h a1 a2 * (h + log rho) pow 2 * a1 * a2 / &2`;
    `&0 <= sqrt(laurent_omega (h / log rho + &1) *
                laurent_theta (h / log rho + &1)) * (h + log rho)`] THEN
  REAL_ARITH_TAC);;

let LAURENT_RATIONAL_PARAM = prove
 (`!p1 q1 p2 q2 b1 b2 rho h a1 a2.
     1 <= q1 /\ q1 < p1 /\ 1 <= q2 /\ q2 < p2 /\ 1 <= b1 /\ 1 <= b2 /\
     &4 <= rho /\ rho <= &8 /\ &10 <= h /\
     &1 <= a1 /\ (rho - &1) * log(&p1 / &q1) + &2 * log(&p1) <= a1 /\
     &1 <= a2 /\ (rho - &1) * log(&p2 / &q2) + &2 * log(&p2) <= a2 /\
     log rho pow 2 <= a1 * a2 /\
     log(&b1 / a2 + &b2 / a1) + log(log rho) + &5 / &2 <= h /\
     ~(&b2 * log(&p2 / &q2) = &b1 * log(&p1 / &q1))
     ==> --(laurent_bound rho h a1 a2) <=
         log(abs(&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`1`; `rho:real`; `h:real`; `a1:real`; `a2:real`;
                `b1:num`; `b2:num`] LAURENT_PARAMETERS) THEN
  ASM_REWRITE_TAC[LE_REFL; REAL_MUL_LID] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:num` (X_CHOOSE_THEN `L:num`
   (X_CHOOSE_THEN `R1:num` (X_CHOOSE_THEN `S1:num`
   (X_CHOOSE_THEN `R2:num` (X_CHOOSE_THEN `S2:num` STRIP_ASSUME_TAC)))))) THEN
  MATCH_MP_TAC TL_LAURENT_FINAL_FROM_EXPORTS THEN
  MAP_EVERY EXISTS_TAC [`K:num`; `L:num`; `R1:num`; `S1:num`; `R2:num`;
                        `S2:num`] THEN
  ASM_REWRITE_TAC[]);;

let LAURENT_RATIONAL_PARAM_LARGE = prove
 (`!p1 q1 p2 q2 b1 b2 rho h a1 a2.
     1 <= q1 /\ q1 < p1 /\ 1 <= q2 /\ q2 < p2 /\ 1 <= b1 /\ 1 <= b2 /\
     &4 <= rho /\ rho <= &8 /\ &10 <= h /\
     rho + &1 <= a1 /\ (rho - &1) * log(&p1 / &q1) + &2 * log(&p1) <= a1 /\
     rho + &1 <= a2 /\ (rho - &1) * log(&p2 / &q2) + &2 * log(&p2) <= a2 /\
     log(&b1 / a2 + &b2 / a1) + log(log rho) + &3 / &2 <= h /\
     ~(&b2 * log(&p2 / &q2) = &b1 * log(&p1 / &q1))
     ==> --(laurent_bound rho h a1 a2) <=
         log(abs(&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= a1 /\ &1 <= a2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&4 <= rho`; `rho + &1 <= a1`; `rho + &1 <= a2`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`1`; `rho:real`; `h:real`; `a1:real`; `a2:real`;
                `b1:num`; `b2:num`] LAURENT_PARAMETERS_LARGE) THEN
  ASM_REWRITE_TAC[LE_REFL; REAL_MUL_LID] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:num` (X_CHOOSE_THEN `L:num`
   (X_CHOOSE_THEN `R1:num` (X_CHOOSE_THEN `S1:num`
   (X_CHOOSE_THEN `R2:num` (X_CHOOSE_THEN `S2:num` STRIP_ASSUME_TAC)))))) THEN
  MATCH_MP_TAC TL_LAURENT_FINAL_FROM_EXPORTS THEN
  MAP_EVERY EXISTS_TAC [`K:num`; `L:num`; `R1:num`; `S1:num`; `R2:num`;
                        `S2:num`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 7. Corollary 2 (D = 1): rho = 5, a_i = 6 A_i, h = max(10, log b + 0.38).  *)
(*    The large regime needs log log 5 - log 6 + 3/2 <= 0.38 (0.336);        *)
(*    LAURENT_BOUND_CORNER_5_10 gives laurent_bound <= 32/36 h^2 a1 a2.      *)
(* ------------------------------------------------------------------------- *)

let TL_LAURENT_FINAL_A_LARGE = prove
 (`!p q A. 1 <= q /\ q < p /\ log(&p) <= A
           ==> (&5 - &1) * log(&p / &q) + &2 * log(&p) <= &6 * A`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &p /\ &0 < &q /\ &1 <= &q` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
    MAP_EVERY UNDISCH_TAC [`1 <= q`; `q < p`] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_DIV] THEN
  MP_TAC(SPEC `&q:real` LOG_POS) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `log(&p) <= A` THEN REAL_ARITH_TAC);;

let TL_LAURENT_FINAL_H_LARGE = prove
 (`!b1 b2 A1 A2 h.
     1 <= b1 /\ 1 <= b2 /\ &1 <= A1 /\ &1 <= A2 /\
     log(&b1 / A2 + &b2 / A1) + &38 / &100 <= h
     ==> log(&b1 / (&6 * A2) + &b2 / (&6 * A1)) + log(log(&5)) + &3 / &2
         <= h`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &b1 / A2 + &b2 / A1` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &b1 /\ &0 < &b2` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN
      MAP_EVERY UNDISCH_TAC [`1 <= b1`; `1 <= b2`] THEN ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&b1 / (&6 * A2) + &b2 / (&6 * A1) = (&b1 / A2 + &b2 / A1) / &6`
  SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_DIV; REAL_ARITH `&0 < &6`] THEN
  MP_TAC TL_LAURENT_FINAL_LOG_6 THEN MP_TAC TL_LAURENT_FINAL_LOG_LOG_5 THEN
  UNDISCH_TAC `log(&b1 / A2 + &b2 / A1) + &38 / &100 <= h` THEN
  REAL_ARITH_TAC);;

let LAURENT_RATIONAL = prove
 (`!p1 q1 p2 q2 b1 b2 A1 A2.
     1 <= q1 /\ q1 < p1 /\ 1 <= q2 /\ q2 < p2 /\ 1 <= b1 /\ 1 <= b2 /\
     &1 <= A1 /\ log(&p1) <= A1 /\ &1 <= A2 /\ log(&p2) <= A2 /\
     ~(&b2 * log(&p2 / &q2) = &b1 * log(&p1 / &q1))
     ==> exp(--(&32 * max (&10) (log(&b1 / A2 + &b2 / A1) + &38 / &100) pow 2 *
                A1 * A2))
         <= abs(&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `h = max (&10) (log(&b1 / A2 + &b2 / A1) + &38 / &100)` THEN
  SUBGOAL_THEN `&10 <= h /\ log(&b1 / A2 + &b2 / A1) + &38 / &100 <= h`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`p1:num`; `q1:num`; `p2:num`; `q2:num`; `b1:num`; `b2:num`;
                `&5`; `h:real`; `&6 * A1`; `&6 * A2`]
    LAURENT_RATIONAL_PARAM_LARGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `&1 <= A1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC TL_LAURENT_FINAL_A_LARGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `&1 <= A2` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC TL_LAURENT_FINAL_A_LARGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC TL_LAURENT_FINAL_H_LARGE THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MP_TAC(SPECL [`h:real`; `&6 * A1`; `&6 * A2`] LAURENT_BOUND_CORNER_5_10) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`&1 <= A1`; `&1 <= A2`] THEN REAL_ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `&0 < abs(&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_ABS_NZ; REAL_SUB_0] THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(log(abs(&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1))))` THEN
  CONJ_TAC THENL
   [ALL_TAC; ASM_SIMP_TAC[EXP_LOG; REAL_LE_REFL]] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE] THEN
  MAP_EVERY UNDISCH_TAC
   [`--laurent_bound (&5) h (&6 * A1) (&6 * A2) <=
     log(abs(&b2 * log(&p2 / &q2) - &b1 * log(&p1 / &q1)))`;
    `laurent_bound (&5) h (&6 * A1) (&6 * A2) <=
     &32 / &36 * h pow 2 * (&6 * A1) * (&6 * A2)`] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 8. All signs: b2 log(p2/q2) + b1 log(p1/q1) with nonzero integers b_i     *)
(*    and positive rationals. If both terms have the same sign (or one       *)
(*    logarithm vanishes) the form is at least one term, >= exp(-2 A_i)      *)
(*    by Liouville; otherwise it is |b2| log(max/min) - |b1| log(max/min)    *)
(*    up to sign, and LAURENT_RATIONAL applies.                              *)
(* ------------------------------------------------------------------------- *)

let TL_LAURENT_FINAL_TRIVIAL_EXP = prove
 (`!m A1 A2. &10 <= m /\ &1 <= A1 /\ &1 <= A2
             ==> exp(--(&32 * m pow 2 * A1 * A2)) <= exp(--(&2 * A1)) /\
                 exp(--(&32 * m pow 2 * A1 * A2)) <= exp(--(&2 * A2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
  SUBGOAL_THEN `&10 pow 2 <= m pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (m pow 2 - &10 pow 2) * (A1 * A2) /\
                &0 <= A1 * (A2 - &1) /\ &0 <= A2 * (A1 - &1) /\
                &0 <= (A1 - &1) * (A2 - &1)`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC [`&1 <= A1`; `&1 <= A2`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let TL_LAURENT_FINAL_SAME_SIGN = prove
 (`!u v. (&0 <= u /\ &0 <= v) \/ (u <= &0 /\ v <= &0)
         ==> abs u <= abs(u + v) /\ abs v <= abs(u + v)`,
  REAL_ARITH_TAC);;

let TL_LAURENT_FINAL_OPPOSITE_SIGN = prove
 (`!u v. ~((&0 <= u /\ &0 <= v) \/ (u <= &0 /\ v <= &0))
         ==> ~(u = &0) /\ ~(v = &0) /\ abs(u + v) = abs(abs u - abs v)`,
  REAL_ARITH_TAC);;

let TL_LAURENT_FINAL_ONE_LOG = prove
 (`!p q b A n.
     1 <= p /\ 1 <= q /\ &1 <= A /\ log(&(MAX p q)) <= A /\ abs b = &n /\
     1 <= n /\ ~(log(&p / &q) = &0)
     ==> exp(--(&2 * A)) <= abs(b * log(&p / &q))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `log(&p) <= A /\ log(&q) <= A` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `log(&(MAX p q))` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
    MAP_EVERY UNDISCH_TAC [`1 <= p`; `1 <= q`] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(log(&p / &q))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LOG_RATIO_LOWER_HEIGHT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC(REAL_ARITH `&1 * x <= y ==> x <= y`) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_REWRITE_TAC[REAL_ABS_POS; REAL_OF_NUM_LE]);;

let TL_LAURENT_FINAL_NE_OF_LOG = prove
 (`!p q b. 1 <= q /\ ~(b * log(&p / &q) = &0) ==> ~(p = q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  UNDISCH_TAC `~(b * log(&p / &q) = &0)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&q / &q = &1`
   (fun th -> REWRITE_TAC[th; LOG_1; REAL_MUL_RZERO]) THEN
  MATCH_MP_TAC REAL_DIV_REFL THEN REWRITE_TAC[REAL_OF_NUM_EQ] THEN
  UNDISCH_TAC `1 <= q` THEN ARITH_TAC);;

let TL_LAURENT_FINAL_GENERAL_COMBINE = prove
 (`!u v x1 x2 E e1 e2 c1 c2.
     ~(u + v = &0) /\
     (x1 = &0 ==> v = &0) /\ (x2 = &0 ==> u = &0) /\
     (~(x1 = &0) ==> e1 <= abs v) /\ (~(x2 = &0) ==> e2 <= abs u) /\
     E <= e1 /\ E <= e2 /\ abs u = c2 /\ abs v = c1 /\
     (~(u = &0) /\ ~(v = &0) /\ ~(c2 = c1) ==> E <= abs(c2 - c1))
     ==> E <= abs((u:real) + v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `(&0 <= u /\ &0 <= v) \/ (u <= &0 /\ v <= &0:real)` THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP TL_LAURENT_FINAL_SAME_SIGN) THEN
    ASM_CASES_TAC `x1:real = &0` THENL
     [ASM_CASES_TAC `x2:real = &0` THENL
       [UNDISCH_TAC `~((u:real) + v = &0)` THEN ASM_SIMP_TAC[REAL_ADD_LID];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e2:real` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `abs(u:real)` THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e1:real` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `abs(v:real)` THEN ASM_SIMP_TAC[]];
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP TL_LAURENT_FINAL_OPPOSITE_SIGN) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((u:real) + v = &0)` THEN
    UNDISCH_TAC `abs((u:real) + v) = abs(abs u - abs v)` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let LAURENT_RATIONAL_GENERAL = prove
 (`!p1 q1 p2 q2 b1 b2 A1 A2.
     1 <= p1 /\ 1 <= q1 /\ 1 <= p2 /\ 1 <= q2 /\
     integer b1 /\ integer b2 /\ ~(b1 = &0) /\ ~(b2 = &0) /\
     &1 <= A1 /\ log(&(MAX p1 q1)) <= A1 /\
     &1 <= A2 /\ log(&(MAX p2 q2)) <= A2 /\
     ~(b2 * log(&p2 / &q2) + b1 * log(&p1 / &q1) = &0)
     ==> exp(--(&32 *
                max (&10) (log(abs b1 / A2 + abs b2 / A1) + &38 / &100) pow 2 *
                A1 * A2))
         <= abs(b2 * log(&p2 / &q2) + b1 * log(&p1 / &q1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `b1:real` INTEGER_NONZERO_ABS_NUM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `b2:real` INTEGER_NONZERO_ABS_NUM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n2:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`max (&10) (log(&n1 / A2 + &n2 / A1) + &38 / &100)`;
                `A1:real`; `A2:real`] TL_LAURENT_FINAL_TRIVIAL_EXP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; STRIP_TAC] THEN
  MATCH_MP_TAC TL_LAURENT_FINAL_GENERAL_COMBINE THEN
  MAP_EVERY EXISTS_TAC
   [`log(&p1 / &q1)`; `log(&p2 / &q2)`; `exp(--(&2 * A1))`;
    `exp(--(&2 * A2))`; `&n1 * log(&(MAX p1 q1) / &(MIN p1 q1))`;
    `&n2 * log(&(MAX p2 q2) / &(MIN p2 q2))`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    SIMP_TAC[REAL_MUL_RZERO];
    SIMP_TAC[REAL_MUL_RZERO];
    DISCH_TAC THEN MATCH_MP_TAC TL_LAURENT_FINAL_ONE_LOG THEN
    EXISTS_TAC `n1:num` THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC TL_LAURENT_FINAL_ONE_LOG THEN
    EXISTS_TAC `n2:num` THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    ASM_SIMP_TAC[REAL_ABS_MUL; LOG_RATIO_ABS_MAX_MIN];
    ASM_SIMP_TAC[REAL_ABS_MUL; LOG_RATIO_ABS_MAX_MIN];
    STRIP_TAC] THEN
  SUBGOAL_THEN `~(p1:num = q1) /\ ~(p2:num = q2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC TL_LAURENT_FINAL_NE_OF_LOG THENL
     [EXISTS_TAC `b1:real`; EXISTS_TAC `b2:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC LAURENT_RATIONAL THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`1 <= p1`; `1 <= q1`; `1 <= p2`; `1 <= q2`; `~(p1:num = q1)`;
    `~(p2:num = q2)`] THEN
  ARITH_TAC);;
