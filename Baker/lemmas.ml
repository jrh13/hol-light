(* ========================================================================= *)
(* Generic lemmas shared by several parts of the development.                *)
(*                                                                           *)
(* Purpose: elementary facts about real and complex numbers, finite sums and *)
(* products, polynomial functions and subrings of C that are used in more    *)
(* than one part of the development (the Baker core, Sharpening I, Tijdeman, *)
(* two logarithms, number fields, Catalan). The file needs only              *)
(* 100/transcendence.ml and Examples/mangoldt.ml, so every part, in          *)
(* particular the two logarithm files with Library/ring_det.ml, can use it   *)
(* without the other Baker files.                                            *)
(*                                                                           *)
(* Main results: real numbers: REAL_LE_1_MUL, REAL_INV_LE_FROM_MUL,          *)
(*   REAL_FRAC_LE_CROSS, REAL_ABS_SUB_NUM_GE_1, REAL_POW_PRED, FINITE_ARGMIN *)
(*   (a real function on a finite nonempty set has a minimum point),         *)
(*   REAL_MIN_INDEX_NUMSEG, LOG_MUL4, LOG_2_LE_1, LOG_NUM_GE_HALF,           *)
(*   EXP_1_LE_3, LOG_NUM_GE_1, LOG_SUC_SUB_LE_INV (the increment of log on   *)
(*   [x,x+1] is at most inv x), REAL_TWO_POW_LE_EXP, REAL_POW_DIV_LE_EXP     *)
(*   ((x/n)^n <= exp x), EXP_NEG_LE_RATIO, INV_POW_EXP_NEG, LOG_POLY_BOUND   *)
(*   (t <= c (log t)^k ==> t <= M), POLYLOG_BOUND, REAL_POW_LE_BOUND_HALF,   *)
(*   REAL_POW_BOUND_CHAIN, REAL_LINEAR_BOUND_ABS; natural numbers and finite *)
(*   sets: EXP_ADD_ONE_LT, ODD_PRIME_GE_3, PIGEONHOLE_CARD_LT; complex exp   *)
(*   and log: CEXP_LOG_RATIO, CEXP_2PI_II, UNITY_ROOT_CEXP,                  *)
(*   COMPLEX_ONE_PLUS_NZ, CLOG_ONE_PLUS_NZ, CLOG_ONE_PLUS_SMALL,             *)
(*   IM_CLOG_ABS_LE_PI, CLOG_MUL_CPRODUCT_POW; sums and polynomials:         *)
(*   CPRODUCT_POW_NSUM, VSUM_CROSS, VSUM_DELTA_FUN,                          *)
(*   COMPLEX_BINOMIAL_THEOREM, COMPLEX_POLYFUN_SHIFT (the shift x |-> x +    *)
(*   beta of a polynomial function), COMPLEX_POLYFUN_AT_0,                   *)
(*   COMPLEX_POLYFUN_TRUNCATE, VSUM_DEGREE_1_ROOT, VSUM_POLY_SHIFT,          *)
(*   COMPLEX_POLYFUN_POLY (a polynomial function vsum(0..n) (\k. c k * z pow *)
(*   k) as the value of a univariate polynomial over complex_ring of degree  *)
(*   at most n with the coefficients c k, for the polynomial machinery of    *)
(*   Library/ringtheory.ml and 100/transcendence.ml); subrings and subfields *)
(*   of C (s subring_of complex_ring, s subfield_of complex_ring):           *)
(*   COMPLEX_SUBRING_OF, COMPLEX_SUBFIELD_OF (the closure conditions),       *)
(*   COMPLEX_SUBRING_CLOSED, COMPLEX_SUBRING_VSUM, COMPLEX_SUBRING_CPRODUCT, *)
(*   COMPLEX_SUBRING_POLY_DIVISION_DEGREE (division by a monic polynomial of *)
(*   degree d with coefficients in a subring: a polynomial of degree d + m   *)
(*   has a quotient of degree m).                                            *)
(*                                                                           *)
(* Uses: 100/transcendence.ml and the files it loads: Library/ringtheory.ml  *)
(*   (RING_BINOMIAL_THEOREM, subring_of, IN_SUBRING_SUM, IN_SUBRING_PRODUCT, *)
(*   poly_ring, POLY_EVAL_COEFF) and Library/fieldtheory.ml (subfield_of)    *)
(*   with the bridges COMPLEX_RING_CLAUSES, COMPLEX_RING_SUM,                *)
(*   COMPLEX_RING_PRODUCT, COMPLEX_RING_POW (of                              *)
(*   Multivariate/complex_ring.ml), complex_field_clauses of                 *)
(*   100/transcendence.ml, Examples/mangoldt.ml (LOG_2_BOUNDS),              *)
(*   Multivariate/cauchy.ml (TAYLOR_CLOG).                                   *)
(* ========================================================================= *)

needs "100/transcendence.ml";;
needs "Examples/mangoldt.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Real numbers: elementary inequalities, exponentials and logarithms.       *)
(* ------------------------------------------------------------------------- *)

let REAL_LE_1_MUL = prove
 (`!x y. &1 <= x /\ &1 <= y ==> &1 <= x * y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`&1`; `x:real`; `&1`; `y:real`] REAL_LE_MUL2) THEN
  ASM_REWRITE_TAC[REAL_MUL_LID; REAL_POS]);;

let REAL_INV_LE_FROM_MUL = prove
 (`!c y. &0 < c /\ &1 <= c * y ==> inv c <= y`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

let REAL_FRAC_LE_CROSS = prove
 (`!a b c d. &0 < b /\ &0 < d /\ a * d <= c * b ==> a / b <= c / d`,
  SIMP_TAC[RAT_LEMMA4]);;

let REAL_ABS_SUB_NUM_GE_1 = prove
 (`!m n. ~(m = n) ==> &1 <= abs(&m - &n)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP
   (ARITH_RULE `~(m = n) ==> m + 1 <= n \/ n + 1 <= m`)) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC);;

let REAL_POW_PRED = prove
 (`!(x:real) n. 1 <= n ==> x pow n = x pow (n - 1) * x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n = SUC(n - 1)`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
   [ASM_ARITH_TAC; REWRITE_TAC[real_pow; REAL_MUL_SYM]]);;

let FINITE_ARGMIN = prove
 (`!s (f:A->real).
        FINITE s /\ ~(s = {}) ==> ?x. x IN s /\ !y. y IN s ==> f x <= f y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `IMAGE (f:A->real) s` INF_FINITE) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE; IN_IMAGE] THEN
  MESON_TAC[]);;

let REAL_MIN_INDEX_NUMSEG = prove
 (`!n (f:num->real). 1 <= n ==> ?i. i IN 1..n /\ !k. k IN 1..n ==> f i <= f k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_ARGMIN THEN
  REWRITE_TAC[FINITE_NUMSEG; NUMSEG_EMPTY] THEN ASM_ARITH_TAC);;

let LOG_MUL4 = prove
 (`!a b c w. &0 < a /\ &0 < b /\ &0 < c /\ &0 < w
             ==> log(a * b * c * w) = log a + log b + log c + log w`,
  SIMP_TAC[LOG_MUL; REAL_LT_MUL]);;

let LOG_2_LE_1 = prove
 (`&0 <= log(&2) /\ log(&2) <= &1`,
  MP_TAC LOG_2_BOUNDS THEN REAL_ARITH_TAC);;

let LOG_NUM_GE_HALF = prove
 (`!t. 2 <= t ==> &1 / &2 <= log(&t)`,
  REPEAT STRIP_TAC THEN TRANS_TAC REAL_LE_TRANS `log(&2)` THEN
  REWRITE_TAC[LOG_2_BOUNDS] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ARITH_TAC);;

let EXP_1_LE_3 = prove
 (`exp(&1) <= &3`,
  MP_TAC E_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let LOG_NUM_GE_1 = prove
 (`!n. 3 <= n ==> &1 <= log(&n)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
  MATCH_MP_TAC LOG_MONO_LE_IMP THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
  TRANS_TAC REAL_LE_TRANS `&3` THEN REWRITE_TAC[EXP_1_LE_3] THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_LE]);;

let LOG_SUC_SUB_LE_INV = prove
 (`!x. &0 < x ==> log(x + &1) - log x <= inv x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x + &1 = x * (&1 + inv x)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < x` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + inv x` ASSUME_TAC THENL
   [MP_TAC(SPEC `x:real` REAL_LT_INV) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_MUL] THEN
  MP_TAC(SPEC `inv x` LOG_LE) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_INV] THEN REAL_ARITH_TAC);;

let REAL_TWO_POW_LE_EXP = prove
 (`!a. &2 pow a <= exp(&a)`,
  GEN_TAC THEN MP_TAC(SPECL [`a:num`; `&1:real`] REAL_EXP_N) THEN
  REWRITE_TAC[REAL_MUL_RID] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN
  MP_TAC(SPEC `&1:real` REAL_EXP_LE_X) THEN REAL_ARITH_TAC);;

(* exp x >= (x/n)^n for x >= 0 (exp(x/n) >= 1 + x/n >= x/n).                 *)

let REAL_POW_DIV_LE_EXP = prove
 (`!x n. &0 <= x ==> (x / &n) pow n <= exp x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[real_pow] THEN MP_TAC(SPEC `x:real` REAL_EXP_LE_X) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp x = exp(x / &n) pow n` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_N] THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REWRITE_TAC[REAL_POS];
    MP_TAC(SPEC `x / &n` REAL_EXP_LE_X) THEN REAL_ARITH_TAC]);;

let EXP_NEG_LE_RATIO = prove
 (`!X N D. &0 < N /\ &0 < D /\ exp(--X) <= N / D ==> log D <= log N + X`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `log(exp(--X)) <= log(N / D)` MP_TAC THENL
   [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
    ASM_SIMP_TAC[LOG_EXP; LOG_DIV] THEN REAL_ARITH_TAC]);;

let INV_POW_EXP_NEG = prove
 (`!y n. &0 < y ==> inv(y pow n) = exp(--(&n * log y))`,
  SIMP_TAC[REAL_EXP_NEG; REAL_EXP_N; EXP_LOG]);;

let LOG_POLY_BOUND = prove
 (`!c k. ?M. !t. &1 <= t /\ t <= c * log t pow k ==> t <= M`,
  REPEAT GEN_TAC THEN EXISTS_TAC `c pow 2 * (&2 * &k) pow (2 * k)` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `log t pow (2 * k) <= (&2 * &k) pow (2 * k) * t`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `k = 0` THENL
     [ASM_REWRITE_TAC[MULT_CLAUSES; real_pow; REAL_MUL_LID]; ALL_TAC] THEN
    MP_TAC(SPECL [`log t`; `2 * k`] REAL_POW_DIV_LE_EXP) THEN
    ASM_SIMP_TAC[LOG_POS; EXP_LOG; REAL_ARITH `&1 <= t ==> &0 < t`] THEN
    ASM_SIMP_TAC[REAL_POW_DIV; REAL_LE_LDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT;
                 ARITH_RULE `~(k = 0) ==> 0 < 2 * k`] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_MUL_AC];
    ALL_TAC] THEN
  SUBGOAL_THEN `t * t <= (c pow 2 * (&2 * &k) pow (2 * k)) * t` MP_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `c pow 2 * log t pow (2 * k)` THEN CONJ_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `(c * log t pow k) pow 2` THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_POW_MUL; REAL_POW_POW] THEN
        REWRITE_TAC[ARITH_RULE `k * 2 = 2 * k`; REAL_LE_REFL]];
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[REAL_LE_POW_2]];
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ; REAL_ARITH `&1 <= t ==> &0 < t`]]);;

let POLYLOG_BOUND = prove
 (`!a b c n k.
     &0 <= a /\ &0 <= b /\ &0 <= c /\ 1 <= n
     ==> ?Y. !y. &1 <= y /\ y pow n <= a * (b + c * log y) pow k ==> y <= Y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a * (b + c) pow k`; `k:num`] LOG_POLY_BOUND) THEN
  DISCH_THEN(X_CHOOSE_TAC `Y0:real`) THEN
  EXISTS_TAC `max (&3) Y0` THEN X_GEN_TAC `y:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `y <= &3` THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(y:real) <= Y0 ==> y <= max (&3) Y0`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&1 <= log y` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `log(&3)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LOG_NUM_GE_1 THEN ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `y pow n` THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `a * (b + c * log y) pow k` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_POW_MUL] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`b:real`; `&1`; `log y`] REAL_LE_LMUL) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let REAL_POW_LE_BOUND_HALF = prove
 (`!e yy n K2. &1 / &2 < e /\ &1 <= yy /\ 1 <= n /\ e * yy pow n <= K2
               ==> yy <= &2 * K2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `yy <= yy pow n` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 / &2) * yy pow n <= e * yy pow n` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

let REAL_POW_BOUND_CHAIN = prove
 (`!yy B C e Lam K2 bb cc n.
        &1 <= yy /\ &2 <= B /\ &0 <= e /\ inv(B pow C) <= Lam /\
        Lam <= &2 * e /\ e * yy pow n <= K2 /\ B <= bb + cc * log yy
        ==> yy pow n <= (&2 * K2) * (bb + cc * log yy) pow C`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < B pow C` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= yy pow n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= K2` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `e * yy pow n` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= (&2 * e) * B pow C` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(B pow C) * B pow C` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_LE_REFL];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `B pow C <= (bb + cc * log yy) pow C` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `yy pow n * &1 <= yy pow n * ((&2 * e) * B pow C)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * B pow C) * (e * yy pow n) <= (&2 * B pow C) * K2`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * K2) * B pow C <= (&2 * K2) * (bb + cc * log yy) pow C`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

let REAL_LINEAR_BOUND_ABS = prove
 (`!N C2 m L1 L2.
        &N <= C2 * (&1 + &m * (L1 + L2)) /\ &0 <= L1 /\ &0 <= L2
        ==> &2 + &N <= (&2 + abs C2 * (&1 + &m * L1)) + (abs C2 * &m) * L2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `C2 * (&1 + &m * (L1 + L2)) <= abs C2 * (&1 + &m * (L1 + L2))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      ASM_REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Natural numbers and finite sets.                                          *)
(* ------------------------------------------------------------------------- *)

let EXP_ADD_ONE_LT = prove
 (`!z n. 1 <= z /\ 2 <= n ==> z EXP n + 1 < (z + 1) EXP n`,
  SUBGOAL_THEN `!z n. 1 <= z ==> z EXP (n + 2) + 1 < (z + 1) EXP (n + 2)`
  ASSUME_TAC THENL
   [GEN_TAC THEN INDUCT_TAC THEN DISCH_TAC THENL
     [REWRITE_TAC[ADD_CLAUSES; EXP_2; LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB;
                  MULT_CLAUSES] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[ARITH_RULE `SUC n + 2 = SUC(n + 2)`; EXP] THEN
    TRANS_TAC LTE_TRANS `(z + 1) * (z EXP (n + 2) + 1)` THEN CONJ_TAC THENL
     [REWRITE_TAC[RIGHT_ADD_DISTRIB; LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`z:num`; `n - 2`]) THEN
    ASM_SIMP_TAC[SUB_ADD]]);;

let ODD_PRIME_GE_3 = prove
 (`!p. prime p /\ ODD p ==> 3 <= p`,
  MESON_TAC[ODD_PRIME]);;

let PIGEONHOLE_CARD_LT = prove
 (`!(f:A->B) s t.
        FINITE s /\ FINITE t /\ CARD t < CARD s /\
        (!x. x IN s ==> f x IN t)
        ==> ?x y. x IN s /\ y IN s /\ ~(x = y) /\ f x = f y`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `CARD(IMAGE (f:A->B) s) = CARD s` ASSUME_TAC THENL
   [MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `CARD(IMAGE (f:A->B) s) <= CARD(t:B->bool)` MP_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The complex exponential and logarithm.                                    *)
(* ------------------------------------------------------------------------- *)

let CEXP_LOG_RATIO = prove
 (`!u v. 1 <= u /\ 1 <= v
         ==> cexp(Cx(log(&u / &v))) = Cx(&u / &v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM CX_EXP; CX_INJ] THEN
  MATCH_MP_TAC EXP_LOG THEN MATCH_MP_TAC REAL_LT_DIV THEN
  REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC);;

let CEXP_2PI_II = prove
 (`cexp(Cx(&2 * pi) * ii) = Cx(&1)`,
  MP_TAC(SPEC `&1` CEXP_INTEGER_2PI) THEN
  REWRITE_TAC[INTEGER_CLOSED; REAL_MUL_LID]);;

let UNITY_ROOT_CEXP_POW = prove
 (`!p j. cexp(Cx(&2) * Cx pi * ii * Cx(&1 / &p)) pow j =
         cexp(Cx(&2) * Cx pi * ii * Cx(&j / &p))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM CEXP_N] THEN AP_TERM_TAC THEN
  REWRITE_TAC[CX_DIV; complex_div] THEN CONV_TAC COMPLEX_RING);;

let UNITY_ROOT_CEXP = prove
 (`!p. ~(p = 0)
       ==> cexp(Cx(&2) * Cx pi * ii * Cx(&1 / &p)) pow p = Cx(&1) /\
           (!j k. j < p /\ k < p /\
                  cexp(Cx(&2) * Cx pi * ii * Cx(&1 / &p)) pow j =
                  cexp(Cx(&2) * Cx pi * ii * Cx(&1 / &p)) pow k
                  ==> j = k)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[COMPLEX_ROOT_UNITY] THEN
  UNDISCH_TAC
   `cexp(Cx(&2) * Cx pi * ii * Cx(&1 / &p)) pow j =
    cexp(Cx(&2) * Cx pi * ii * Cx(&1 / &p)) pow k` THEN
  ASM_SIMP_TAC[UNITY_ROOT_CEXP_POW; COMPLEX_ROOT_UNITY_EQ] THEN
  ASM_MESON_TAC[CONG_IMP_EQ]);;

let COMPLEX_ONE_PLUS_NZ = prove
 (`!z. norm z <= &1 / &2 ==> ~(Cx(&1) + z = Cx(&0))`,
  GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `z = --Cx(&1)` SUBST_ALL_TAC THENL
   [POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  UNDISCH_TAC `norm(--Cx(&1)) <= &1 / &2` THEN
  REWRITE_TAC[NORM_NEG; COMPLEX_NORM_CX] THEN REAL_ARITH_TAC);;

let CLOG_ONE_PLUS_NZ = prove
 (`!z. ~(z = Cx(&0)) /\ norm z <= &1 / &2 ==> ~(clog(Cx(&1) + z) = Cx(&0))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP COMPLEX_ONE_PLUS_NZ) THEN
  MP_TAC(SPEC `Cx(&1) + z` CEXP_CLOG) THEN ASM_REWRITE_TAC[CEXP_0] THEN
  UNDISCH_TAC `~(z = Cx(&0))` THEN CONV_TAC COMPLEX_RING);;

let CLOG_ONE_PLUS_SMALL = prove
 (`!z. norm z <= &1 / &2 ==> norm(clog(Cx(&1) + z)) <= &2 * norm z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`0`; `z:complex`] TAYLOR_CLOG) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[VSUM_TRIV_NUMSEG; ARITH; COMPLEX_VEC_0; COMPLEX_SUB_RZERO;
           REAL_POW_1; ADD_CLAUSES] THEN
  MATCH_MP_TAC(REAL_ARITH `(b:real) <= c ==> (a:real) <= b ==> a <= c`) THEN
  SUBGOAL_THEN `&0 < &1 - norm(z:complex)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MP_TAC(SPECL [`norm(z:complex)`; `&1 - &2 * norm(z:complex)`]
    REAL_LE_MUL) THEN
  REWRITE_TAC[NORM_POS_LE] THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

let IM_CLOG_ABS_LE_PI = prove
 (`!z. ~(z = Cx(&0)) ==> abs(Im(clog z)) <= pi`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT2 o MATCH_MP CLOG_WORKS) THEN
  REAL_ARITH_TAC);;

let CLOG_MUL_CPRODUCT_POW = prove
 (`!(S:A->bool) (g:A->complex) (mm:A->num) alpha w.
     FINITE S /\ ~(alpha = Cx(&0)) /\ (!x. x IN S ==> ~(g x = Cx(&0))) /\
     ~(w = Cx(&0)) /\ w = alpha * cproduct S (\x. g x pow mm x)
     ==> ?t0. integer t0 /\ abs t0 <= &(nsum S mm) + &1 /\
              clog w = Cx(&1) * clog alpha + Cx t0 * (Cx(&2 * pi) * ii) +
                       vsum S (\x. Cx(&(mm x)) * clog(g x))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  SUBGOAL_THEN
   `cexp(clog(alpha * cproduct S (\x. (g:A->complex) x pow mm x))) =
    cexp(clog alpha + vsum S (\x. Cx(&(mm x)) * clog(g x)))`
  MP_TAC THENL
   [ASM_SIMP_TAC[CEXP_CLOG; CEXP_ADD; CEXP_VSUM; CEXP_N] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC CPRODUCT_EQ THEN
    ASM_SIMP_TAC[CEXP_CLOG];
    REWRITE_TAC[CEXP_EQ] THEN
    DISCH_THEN(X_CHOOSE_THEN `t0:real` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `t0:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING] THEN
  SUBGOAL_THEN
   `Im(clog(alpha * cproduct S (\x. (g:A->complex) x pow mm x))) =
    Im(clog alpha) + sum S (\x. &(mm x) * Im(clog(g x))) + &2 * t0 * pi`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[IM_ADD; IM_VSUM; IM_MUL_CX; IM_MUL_II; RE_CX; IM_II;
                 REAL_MUL_RID] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(sum S (\x. &(mm x) * Im(clog((g:A->complex) x)))) <=
    &(nsum S mm) * pi`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_OF_NUM_SUM; GSYM SUM_RMUL] THEN
    MATCH_MP_TAC SUM_ABS_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC IM_CLOG_ABS_LE_PI THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(Im(clog(alpha * cproduct S (\x. (g:A->complex) x pow mm x)))) <= pi /\
    abs(Im(clog alpha)) <= pi`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC IM_CLOG_ABS_LE_PI THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < pi /\ &0 <= &(nsum S (mm:A->num)) * pi`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[PI_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_POS] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(&(nsum S (mm:A->num)) + &1) * pi < abs t0 * pi`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(&2 * t0 * pi) = &2 * abs t0 * pi` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
    SUBGOAL_THEN `abs pi = pi` (fun th -> REWRITE_TAC[th]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Finite sums and products; polynomial functions.                           *)
(* ------------------------------------------------------------------------- *)

let CPRODUCT_POW_NSUM = prove
 (`!s (z:complex) m.
        FINITE s ==> cproduct s (\r:A. z pow (m r)) = z pow (nsum s m)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN SPEC_TAC(`s:A->bool`,`s:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[CPRODUCT_CLAUSES; NSUM_CLAUSES; complex_pow; COMPLEX_POW_ADD]);;

let VSUM_CROSS = prove
 (`!s t (f:A#B->complex).
        FINITE s /\ FINITE t
        ==> vsum (s CROSS t) f = vsum s (\i. vsum t (\j. f(i,j)))`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_VSUM_PRODUCT o rand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[CROSS] THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM]);;

let VSUM_DELTA_FUN = prove
 (`!s (f:A->complex) a.
        vsum s (\x. if x = a then f x else Cx(&0)) =
        if a IN s then f a else Cx(&0)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(\x. if x = a then (f:A->complex) x else Cx(&0)) =
                (\x. if x = a then f a else vec 0)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; COMPLEX_VEC_0] THEN GEN_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[VSUM_DELTA; COMPLEX_VEC_0]]);;

let COMPLEX_BINOMIAL_THEOREM = prove
 (`!n x y.
     (x + y) pow n =
     vsum(0..n) (\k. Cx(&(binom(n,k))) * x pow k * y pow (n - k))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`complex_ring`; `n:num`; `x:complex`; `y:complex`]
    RING_BINOMIAL_THEOREM) THEN
  REWRITE_TAC[complex_field_clauses; IN_UNIV] THEN
  SIMP_TAC[COMPLEX_RING_SUM; FINITE_NUMSEG]);;

let COMPLEX_POLYFUN_SHIFT = prove
 (`!m (c:num->complex) beta x.
        vsum(0..m) (\k. c k * (x + beta) pow k) =
        vsum(0..m) (\t. vsum(0..m) (\k. Cx(&(binom(k,t))) *
                                        beta pow (k - t) * c k) * x pow t)`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; FINITE_NUMSEG] THEN
  GEN_REWRITE_TAC RAND_CONV [VSUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[COMPLEX_BINOMIAL_THEOREM] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  TRANS_TAC EQ_TRANS
   `vsum(0..k) (\t. (Cx(&(binom(k,t))) * beta pow (k - t) * c k) * x pow t)`
  THEN CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
    CONV_TAC COMPLEX_RING;
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN
    ASM_REWRITE_TAC[SUBSET_NUMSEG; LE_REFL; IN_NUMSEG; NOT_LE; LE_0] THEN
    SIMP_TAC[BINOM_LT; COMPLEX_MUL_LZERO; COMPLEX_VEC_0]]);;

let COMPLEX_POLYFUN_AT_0 = prove
 (`!n (c:num->complex). vsum(0..n) (\t. c t * Cx(&0) pow t) = c 0`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[VSUM_CLAUSES_LEFT; LE_0; complex_pow; COMPLEX_MUL_RID] THEN
  MATCH_MP_TAC(COMPLEX_RING `y = Cx(&0) ==> x + y = x`) THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN MATCH_MP_TAC VSUM_EQ_0 THEN
  REWRITE_TAC[IN_NUMSEG; COMPLEX_POW_ZERO; COMPLEX_VEC_0] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `0 + 1 <= k ==> ~(k = 0)`; COMPLEX_MUL_RZERO]);;

let COMPLEX_POLYFUN_TRUNCATE = prove
 (`!M n (c:num->complex) x.
     n <= M
     ==> vsum(0..M) (\t. (if t <= n then c t else Cx(&0)) * x pow t) =
         vsum(0..n) (\t. c t * x pow t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VSUM_EQ_SUPERSET THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; SUBSET_NUMSEG; LE_REFL; IN_NUMSEG; LE_0] THEN
  SIMP_TAC[COMPLEX_MUL_LZERO; COMPLEX_VEC_0]);;

let VSUM_DEGREE_1_ROOT = prove
 (`!b. vsum(0..1) (\i. Cx(if i = 0 then --b else if i = 1 then &1 else &0) *
                       Cx b pow i) = Cx(&0)`,
  GEN_TAC THEN SIMP_TAC[VSUM_CLAUSES_LEFT; LE_0] THEN
  REWRITE_TAC[ARITH; VSUM_SING_NUMSEG] THEN
  REWRITE_TAC[complex_pow; COMPLEX_POW_1; CX_NEG] THEN
  CONV_TAC COMPLEX_RING);;

let VSUM_POLY_SHIFT = prove
 (`!e d (g:num->complex) z.
        vsum(0..e+d) (\k. (if e <= k then g(k - e) else Cx(&0)) * z pow k) =
        z pow e * vsum(0..d) (\k. g k * z pow k)`,
  REPEAT GEN_TAC THEN
  TRANS_TAC EQ_TRANS
   `vsum(0+e..d+e) (\k. (if e <= k then (g:num->complex)(k - e)
                         else Cx(&0)) * z pow k)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_SUPERSET THEN
    REWRITE_TAC[SUBSET; IN_NUMSEG; COMPLEX_VEC_0] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(e <= k)` (fun th -> REWRITE_TAC[th; COMPLEX_MUL_LZERO]) THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[VSUM_OFFSET; LE_ADDR; ADD_SUB] THEN
    SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[COMPLEX_POW_ADD] THEN CONV_TAC COMPLEX_RING]);;

(* A coefficient function c and a degree bound n give the univariate         *)
(* polynomial over complex_ring with the coefficients c k (k <= n), of       *)
(* degree at most n, whose value is the polynomial function                  *)
(* vsum(0..n) (\k. c k * z pow k).                                           *)

let COMPLEX_POLYFUN_POLY = prove
 (`!n (c:num->complex).
        ?p. p IN ring_carrier(poly_ring complex_ring (:1)) /\
            (!k. coeff k p = if k <= n then c k else Cx(&0)) /\
            poly_deg complex_ring p <= n /\
            (!z. poly_eval complex_ring p z = vsum(0..n) (\k. c k * z pow k))`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `p = \x:1->num. if x one <= n then (c:num->complex)(x one)
                             else Cx(&0)` THEN
  EXISTS_TAC `p:(1->num)->complex` THEN
  SUBGOAL_THEN `!k. coeff k (p:(1->num)->complex) =
                    if k <= n then c k else Cx(&0)`
  ASSUME_TAC THENL [EXPAND_TAC "p" THEN REWRITE_TAC[COEFF]; ALL_TAC] THEN
  SUBGOAL_THEN `ring_polynomial complex_ring (p:(1->num)->complex) /\
                poly_deg complex_ring p <= n`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC RING_POLYNOMIAL_COEFF_BOUND;
      SIMP_TAC[POLY_DEG_LE_COEFF_EQ]] THEN
    TRY(EXISTS_TAC `n:num`) THEN
    ASM_REWRITE_TAC[RING_POWERSERIES_COEFF; COMPLEX_RING_CLAUSES; IN_UNIV] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_POLY_RING_CARRIER; SUBSET_UNIV] THEN
  X_GEN_TAC `z:complex` THEN
  ASM_SIMP_TAC[POLY_EVAL_COEFF; IN_UNIV; COMPLEX_RING_CLAUSES;
               COMPLEX_RING_POW; COMPLEX_RING_SUM; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Subrings and subfields of C.                                              *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_SUBRING_OF = prove
 (`!s. s subring_of complex_ring <=>
       Cx(&0) IN s /\ Cx(&1) IN s /\
       (!x y. x IN s /\ y IN s ==> x + y IN s /\ x * y IN s) /\
       (!x. x IN s ==> --x IN s)`,
  REWRITE_TAC[subring_of; COMPLEX_RING_CLAUSES; SUBSET_UNIV] THEN
  MESON_TAC[]);;

let COMPLEX_SUBFIELD_OF = prove
 (`!s. s subfield_of complex_ring <=>
       s subring_of complex_ring /\
       (!x. x IN s /\ ~(x = Cx(&0)) ==> inv x IN s)`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN ASM_SIMP_TAC[SUBFIELD_IMP_SUBRING_OF] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`complex_ring`; `s:complex->bool`; `x:complex`]
      IN_SUBFIELD_INV) THEN
    ASM_REWRITE_TAC[complex_field_clauses];
    STRIP_TAC THEN MATCH_MP_TAC SUBFIELD_OF_FIELD_INV THEN
    ASM_REWRITE_TAC[FIELD_COMPLEX_RING; complex_field_clauses] THEN
    X_GEN_TAC `x:complex` THEN ASM_CASES_TAC `x = Cx(&0)` THEN
    ASM_SIMP_TAC[COMPLEX_INV_0] THEN
    ASM_MESON_TAC[COMPLEX_SUBRING_OF]]);;

let COMPLEX_SUBRING_CLOSED = prove
 (`!s. s subring_of complex_ring
       ==> Cx(&0) IN s /\ Cx(&1) IN s /\
           (!x y. x IN s /\ y IN s ==> x + y IN s) /\
           (!x y. x IN s /\ y IN s ==> x - y IN s) /\
           (!x y. x IN s /\ y IN s ==> x * y IN s) /\
           (!x. x IN s ==> --x IN s) /\
           (!x n. x IN s ==> x pow n IN s)`,
  GEN_TAC THEN REWRITE_TAC[COMPLEX_SUBRING_OF] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[complex_sub] THEN GEN_TAC THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[complex_pow]);;

let COMPLEX_SUBRING_VSUM = prove
 (`!s (f:A->complex) k.
        s subring_of complex_ring /\ FINITE k /\ (!i. i IN k ==> f i IN s)
        ==> vsum k f IN s`,
  SIMP_TAC[GSYM COMPLEX_RING_SUM; IN_SUBRING_SUM]);;

let COMPLEX_SUBRING_CPRODUCT = prove
 (`!s (f:A->complex) k.
        s subring_of complex_ring /\ FINITE k /\ (!i. i IN k ==> f i IN s)
        ==> cproduct k f IN s`,
  SIMP_TAC[GSYM COMPLEX_RING_PRODUCT; IN_SUBRING_PRODUCT]);;

(* ------------------------------------------------------------------------- *)
(* Division by a monic polynomial over a subring of C, with the degree of    *)
(* the quotient: a polynomial of degree d + m divided by a monic polynomial  *)
(* of degree d has a quotient of degree m.                                   *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_SUBRING_POLY_DIVISION_DEGREE = prove
 (`!s d (g:num->complex).
        s subring_of complex_ring /\ 1 <= d /\ (!k. g k IN s) /\ g d = Cx(&1)
        ==> !m f. (!k. f k IN s)
                  ==> ?q r. (!k. q k IN s) /\ (!k. r k IN s) /\
                            !z. vsum(0..d+m) (\k. f k * z pow k) =
                                vsum(0..m) (\k. q k * z pow k) *
                                vsum(0..d) (\k. g k * z pow k) +
                                vsum(0..d-1) (\k. r k * z pow k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP COMPLEX_SUBRING_CLOSED) THEN
  SUBGOAL_THEN
   `!(h:num->complex) z. vsum(0..d) (\k. h k * z pow k) =
                         vsum(0..d-1) (\k. h k * z pow k) + h d * z pow d`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC VSUM_CLAUSES_RIGHT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [X_GEN_TAC `f:num->complex` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`\k:num. (f:num->complex) d`;
      `\k. (f:num->complex) k - f d * g k`] THEN
    ASM_SIMP_TAC[] THEN X_GEN_TAC `z:complex` THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; VSUM_SING_NUMSEG; complex_pow;
                    COMPLEX_MUL_RID; COMPLEX_MUL_LID] THEN
    REWRITE_TAC[COMPLEX_SUB_RDISTRIB; VSUM_SUB_NUMSEG] THEN
    SIMP_TAC[GSYM COMPLEX_MUL_ASSOC; VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  X_GEN_TAC `f:num->complex` THEN DISCH_TAC THEN
  ABBREV_TAC `ft = (f:num->complex)(SUC(d + m))` THEN
  SUBGOAL_THEN `(ft:complex) IN s` ASSUME_TAC THENL
   [EXPAND_TAC "ft" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `\k. (f:num->complex) k -
        ft * (if SUC m <= k then g(k - SUC m) else Cx(&0))`) THEN
  ANTS_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num->complex` (X_CHOOSE_THEN `r:num->complex`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`\k. if k = SUC m then ft else (q:num->complex) k`; `r:num->complex`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN
  MP_TAC(SPECL [`SUC m`; `d:num`; `g:num->complex`; `z:complex`]
    VSUM_POLY_SHIFT) THEN
  REWRITE_TAC[ARITH_RULE `SUC m + d = SUC(d + m)`;
              ARITH_RULE `d + SUC m = SUC(d + m)`] THEN
  REWRITE_TAC[VSUM_CLAUSES_NUMSEG; LE_0] THEN
  SUBGOAL_THEN `SUC m <= SUC(d + m) /\ SUC(d + m) - SUC m = d`
  (fun th -> REWRITE_TAC[th]) THENL [ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(k = SUC m) <=> ~(SUC m = k)`] THEN
  REWRITE_TAC[COMPLEX_MUL_RID] THEN
  SUBGOAL_THEN
   `vsum(0..m) (\k. (if k = SUC m then ft else (q:num->complex) k) *
                    z pow k) =
    vsum(0..m) (\k. q k * z pow k)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
    SIMP_TAC[ARITH_RULE `k <= m ==> ~(k = SUC m)`];
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_SUB_RDISTRIB; VSUM_SUB_NUMSEG] THEN
  SIMP_TAC[GSYM COMPLEX_MUL_ASSOC; VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  CONV_TAC COMPLEX_RING);;
