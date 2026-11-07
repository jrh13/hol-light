(* ========================================================================= *)
(* The values of L(1, chi) for k = 21 and k = 33 as finite cyclotomic        *)
(* identities.                                                               *)
(*                                                                           *)
(* Purpose: the sums over a = 1, .., k - 1 of (a | k) log sin(pi a / k) are  *)
(* -2 log eps_21 for k = 21 and -2 log eps_33 for k = 33,                    *)
(* eps_21 = (5 + sqrt 21) / 2 and eps_33 = 23 + 4 sqrt 33 the fundamental    *)
(* units (CLASSNO_SIN_IDENTITIES); with the class number formula             *)
(* CLASSNO_L1_EVEN this gives abs L(1, chi_21) = 2 log eps_21 / sqrt 21 and  *)
(* abs L(1, chi_33) = 2 log eps_33 / sqrt 33 (CLASSNO_L1_REAL), the formulas *)
(* of Dirichlet for the real quadratic fields of class number one Q(sqrt 21) *)
(* and Q(sqrt 33) used in Baker, Transcendental Number Theory, Ch. 5,        *)
(* sec. 4.                                                                   *)
(*                                                                           *)
(* Method: with s(a) = sin(pi a / k), the products p = s(1) s(4) s(5),       *)
(* q = s(2) s(8) s(10) (k = 21) and p = s(1) s(2) s(4) s(8) s(16),           *)
(* q = s(5) s(7) s(10) s(13) s(14) (k = 33) satisfy p^2 + q^2 = 5 p q (resp. *)
(* 46 p q) and 0 < p < q, hence q / p = eps_21 (resp. eps_33). The quadratic *)
(* identity is a polynomial identity in the root of unity                    *)
(* y = exp(2 pi i / k): 2 i s(a) z^a = y^a - 1 with z = exp(pi i / k), and   *)
(* after clearing powers of z it reads F(y) = Phi_k(y) G(y) with explicit    *)
(* integer polynomials (the quotient G is checked by COMPLEX_RING);          *)
(* Phi_k(y) = 0 follows from                                                 *)
(* (y^k - 1) (y - 1) = (y^3 - 1) (y^m - 1) Phi_k(y), m = 7 (resp. 11), and   *)
(* y^3, y^m <> 1. The inequality p < q comes from the monotonicity of sin on *)
(* [0, pi/2] (plus sin(pi/6) = 1/2, sin(pi/3) = sqrt 3 / 2 for k = 33). The  *)
(* character values qchar k a = jacobi(a,k) are evaluated by a conversion    *)
(* (multiplicativity in the modulus, Euler criterion for the prime factors   *)
(* 3, 7, 11).                                                                *)
(*                                                                           *)
(* Main results: CLASSNO_SIN_IDENTITIES, CLASSNO_L1_REAL;                    *)
(* CLASSNO_CYCLO_RATIO21, CLASSNO_CYCLO_RATIO33, CLASSNO_CYCLO_SUM21,        *)
(* CLASSNO_CYCLO_SUM33 (the identities for coefficients with the character   *)
(* values), CLASSNO_CYCLO_JACOBI_CONV, CLASSNO_CYCLO_QCHAR_CONV (conversions *)
(* evaluating Jacobi symbols); helper names CLASSNO_CYCLO_*.                 *)
(*                                                                           *)
(* Uses: Baker/classno_chardefs.ml (qchar), Baker/classno_gauss.ml           *)
(* (CLASSNO_L1_EVEN, CLASSNO_GAUSS_SIN_POS, CLASSNO_GAUSS_ROOT_EQ_1),        *)
(* Baker/classno_limit.ml (CLASSNO_LIMIT_PRIMES);                            *)
(* Library/jacobi.ml (JACOBI_EULER, JACOBI_CASES,                            *)
(* JACOBI_RMUL).                                                             *)
(*                                                                           *)
(* The library files come first, in the order of Baker/make.ml               *)
(* (Library/jacobi.ml before the Multivariate files, 100/dirichlet.ml before *)
(* Multivariate/gamma.ml), so that the file also loads alone.                *)
(* ========================================================================= *)

needs "Library/jacobi.ml";;
needs "100/transcendence.ml";;
needs "Examples/mangoldt.ml";;
needs "100/dirichlet.ml";;
needs "Multivariate/gamma.ml";;
needs "Baker/classno_limit.ml";;
needs "Baker/classno_gauss.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Sines as values of roots of unity.                                        *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_CYCLO_CEXP_POW = prove
 (`!n x. cexp(ii * Cx x) pow n = cexp(ii * Cx(&n * x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM CEXP_N] THEN AP_TERM_TAC THEN
  REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING);;

let CLASSNO_CYCLO_SIN_CEXP = prove
 (`!x. cexp(ii * Cx(&2 * x)) - Cx(&1) =
       (Cx(&2) * ii) * Cx(sin x) * cexp(ii * Cx x)`,
  GEN_TAC THEN REWRITE_TAC[CX_SIN; csin; GSYM CLASSNO_CYCLO_CEXP_POW] THEN
  REWRITE_TAC[COMPLEX_MUL_LNEG; CEXP_NEG] THEN
  MP_TAC(SPEC `ii * Cx x` CEXP_NZ) THEN MP_TAC II_NZ THEN
  CONV_TAC COMPLEX_FIELD);;

let CLASSNO_CYCLO_SIN_ROOT = prove
 (`!a k. cexp(ii * Cx(&2 * pi / &k)) pow a - Cx(&1) =
         (Cx(&2) * ii) * Cx(sin(pi * &a / &k)) * cexp(ii * Cx(pi / &k)) pow a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLASSNO_CYCLO_CEXP_POW] THEN
  MP_TAC(SPEC `&a * pi / &k` CLASSNO_CYCLO_SIN_CEXP) THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN
  REPEAT AP_TERM_TAC THEN REWRITE_TAC[] THEN
  REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN REAL_ARITH_TAC);;

let CLASSNO_CYCLO_CEXP_DOUBLE = prove
 (`!k. cexp(ii * Cx(&2 * pi / &k)) = cexp(ii * Cx(pi / &k)) pow 2`,
  REWRITE_TAC[CLASSNO_CYCLO_CEXP_POW]);;

let CLASSNO_CYCLO_ROOT_1 = prove
 (`!k. ~(k = 0) ==> cexp(ii * Cx(&2 * pi / &k)) pow k = Cx(&1)`,
  REWRITE_TAC[CLASSNO_CYCLO_CEXP_POW; real_div; REAL_ARITH
   `&k * &2 * pi * inv(&k) = &2 * pi * &k * inv(&k)`] THEN
  REWRITE_TAC[GSYM real_div; CLASSNO_GAUSS_ROOT_EQ_1; DIVIDES_REFL]);;

let CLASSNO_CYCLO_ROOT_NE_1 = prove
 (`!k m. 0 < m /\ m < k ==> ~(cexp(ii * Cx(&2 * pi / &k)) pow m = Cx(&1))`,
  REWRITE_TAC[CLASSNO_CYCLO_CEXP_POW; real_div; REAL_ARITH
   `&m * &2 * pi * inv(&k) = &2 * pi * &m * inv(&k)`] THEN
  REWRITE_TAC[GSYM real_div; CLASSNO_GAUSS_ROOT_EQ_1; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC);;

let CLASSNO_CYCLO_SIN_SYM = prove
 (`!a b k. a + b = k ==> sin(pi * &b / &k) = sin(pi * &a / &k)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_TAC `a + b = k` THEN ASM_REWRITE_TAC[ADD_EQ_0] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pi * &b / &k = pi - pi * &a / &k` SUBST1_TAC THENL
   [SUBGOAL_THEN `&b = &k - &a` SUBST1_TAC THENL
     [FIRST_X_ASSUM(K ALL_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o AP_TERM `real_of_num`) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `~(k = 0)` THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
      CONV_TAC REAL_FIELD];
    REWRITE_TAC[SIN_SUB; SIN_PI; COS_PI] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Elementary real algebra: the larger root of t^2 - c t + 1 = 0, products.  *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_CYCLO_QUADRATIC = prove
 (`!p q c d. &0 < p /\ p < q /\ p pow 2 + q pow 2 = c * p * q /\
             &0 <= d /\ d pow 2 = c pow 2 - &4
             ==> q / p = (c + d) / &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 < q / p` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LID]; ALL_TAC] THEN
  SUBGOAL_THEN `(q / p) pow 2 - c * (q / p) + &1 = &0` MP_TAC THENL
   [UNDISCH_TAC `p pow 2 + q pow 2 = c * p * q` THEN
    UNDISCH_TAC `&0 < p` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  UNDISCH_TAC `d pow 2 = c pow 2 - &4` THEN UNDISCH_TAC `&0 <= d` THEN
  SPEC_TAC(`q / p`,`t:real`) THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(t - (c + d) / &2) * (t - (c - d) / &2) = &0` MP_TAC THENL
   [UNDISCH_TAC `d pow 2 = c pow 2 - &4` THEN
    UNDISCH_TAC `t pow 2 - c * t + &1 = &0` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ENTIRE; REAL_SUB_0] THEN STRIP_TAC THEN
  SUBGOAL_THEN `t * (t + d) = &1` MP_TAC THENL
   [UNDISCH_TAC `d pow 2 = c pow 2 - &4` THEN
    UNDISCH_TAC `t = (c - d) / &2` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MP_TAC(SPECL [`&1`; `t:real`; `&1`; `t + d:real`] REAL_LT_MUL2) THEN
  ASM_REAL_ARITH_TAC);;

let CLASSNO_CYCLO_PROD3_LT = prove
 (`!a1 a2 a3 b1 b2 b3:real.
     &0 < a1 /\ a1 < b1 /\ &0 < a2 /\ a2 < b2 /\ &0 < a3 /\ a3 < b3
     ==> a1 * a2 * a3 < b1 * b2 * b3`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_MUL2 THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_MUL] THEN
  MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let CLASSNO_CYCLO_LT33_ALG = prove
 (`!s1 s2 s4 s8 s16 s5 s7 s10 s13 s14 w:real.
     &0 < s1 /\ &0 < s2 /\ &0 < s4 /\ &0 < s8 /\ &0 < s16 /\
     s2 < s5 /\ s4 < s7 /\ s8 < s10 /\ s1 < &1 / &2 /\ s16 <= &1 /\
     &0 <= w /\ w * w = &3 / &4 /\ w < s13 /\ w < s14
     ==> s1 * s2 * s4 * s8 * s16 < s5 * s7 * s10 * s13 * s14`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(s1:real) * s16 < s13 * s14` ASSUME_TAC THENL
   [SUBGOAL_THEN `(w:real) * w < s13 * s14` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(s1:real) * s16 <= s1` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x * y <= x * &1 ==> x * y <= x`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    UNDISCH_TAC `(w:real) * w = &3 / &4` THEN
    UNDISCH_TAC `(s1:real) < &1 / &2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(s1:real) * s2 * s4 * s8 * s16 = s2 * s4 * s8 * (s1 * s16) /\
                (s5:real) * s7 * s10 * s13 * s14 = s5 * s7 * s10 * (s13 * s14)`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MATCH_MP_TAC CLASSNO_CYCLO_PROD3_LT THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_LT_MUL] THEN MATCH_MP_TAC REAL_LT_MUL2 THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_MUL]);;

(* ------------------------------------------------------------------------- *)
(* k = 21: Phi_21 vanishes at exp(2 pi i / 21); the quadratic identity.      *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_CYCLO_POLY21 = prove
 (`!y:complex.
     y pow 10 * ((y pow 1 - Cx(&1)) * (y pow 4 - Cx(&1))
     * (y pow 5 - Cx(&1))) pow 2 + ((y pow 2 - Cx(&1)) * (y pow 8 - Cx(&1))
     * (y pow 10 - Cx(&1))) pow 2 - Cx(&5) * y pow 5
     * ((y pow 1 - Cx(&1)) * (y pow 4 - Cx(&1)) * (y pow 5 - Cx(&1)))
     * ((y pow 2 - Cx(&1)) * (y pow 8 - Cx(&1)) * (y pow 10 - Cx(&1))) =
     (Cx(&1) - y + y pow 3 - y pow 4 + y pow 6 - y pow 8 + y pow 9 - y pow 11
      + y pow 12) *
     (Cx(&1) + y - y pow 2 - Cx(&2) * y pow 3 - y pow 4 - Cx(&4) * y pow 5
      + y pow 6 + Cx(&4) * y pow 7 + Cx(&2) * y pow 8 + Cx(&4) * y pow 9
      + Cx(&3) * y pow 10 - Cx(&3) * y pow 11 - Cx(&2) * y pow 12 - Cx(&6)
      * y pow 14 - Cx(&2) * y pow 16 - Cx(&3) * y pow 17 + Cx(&3) * y pow 18
      + Cx(&4) * y pow 19 + Cx(&2) * y pow 20 + Cx(&4) * y pow 21 + y pow 22
      - Cx(&4) * y pow 23 - y pow 24 - Cx(&2) * y pow 25 - y pow 26 + y pow 27
      + y pow 28)`,
  CONV_TAC COMPLEX_RING);;

let CLASSNO_CYCLO_PHI21 = prove
 (`Cx(&1) - cexp(ii * Cx(&2 * pi / &21)) + cexp(ii * Cx(&2 * pi / &21)) pow 3
   - cexp(ii * Cx(&2 * pi / &21)) pow 4 + cexp(ii * Cx(&2 * pi / &21)) pow 6
   - cexp(ii * Cx(&2 * pi / &21)) pow 8 + cexp(ii * Cx(&2 * pi / &21)) pow 9
   - cexp(ii * Cx(&2 * pi / &21)) pow 11 + cexp(ii * Cx(&2 * pi / &21)) pow 12
   = Cx(&0)`,
  MP_TAC(MATCH_MP CLASSNO_CYCLO_ROOT_1 (ARITH_RULE `~(21 = 0)`)) THEN
  MP_TAC(MATCH_MP CLASSNO_CYCLO_ROOT_NE_1 (ARITH_RULE `0 < 3 /\ 3 < 21`)) THEN
  MP_TAC(MATCH_MP CLASSNO_CYCLO_ROOT_NE_1 (ARITH_RULE `0 < 7 /\ 7 < 21`)) THEN
  SPEC_TAC(`cexp(ii * Cx(&2 * pi / &21))`,`y:complex`) THEN
  GEN_TAC THEN REPEAT DISCH_TAC THEN
  MP_TAC(COMPLEX_RING
   `(y pow 3 - Cx(&1)) * (y pow 7 - Cx(&1)) *
    (Cx(&1) - y + y pow 3 - y pow 4 + y pow 6 - y pow 8 + y pow 9 - y pow 11
     + y pow 12) =
    (y pow 21 - Cx(&1)) * (y - Cx(&1))`) THEN
  ASM_REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_MUL_LZERO; COMPLEX_ENTIRE;
                  COMPLEX_SUB_0]);;

let CLASSNO_CYCLO_FZERO21 = prove
 (`cexp(ii * Cx(&2 * pi / &21)) pow 10
   * ((cexp(ii * Cx(&2 * pi / &21)) pow 1 - Cx(&1))
   * (cexp(ii * Cx(&2 * pi / &21)) pow 4 - Cx(&1))
   * (cexp(ii * Cx(&2 * pi / &21)) pow 5 - Cx(&1))) pow 2
   + ((cexp(ii * Cx(&2 * pi / &21)) pow 2 - Cx(&1))
   * (cexp(ii * Cx(&2 * pi / &21)) pow 8 - Cx(&1))
   * (cexp(ii * Cx(&2 * pi / &21)) pow 10 - Cx(&1))) pow 2 - Cx(&5)
   * cexp(ii * Cx(&2 * pi / &21)) pow 5
   * ((cexp(ii * Cx(&2 * pi / &21)) pow 1 - Cx(&1))
   * (cexp(ii * Cx(&2 * pi / &21)) pow 4 - Cx(&1))
   * (cexp(ii * Cx(&2 * pi / &21)) pow 5 - Cx(&1)))
   * ((cexp(ii * Cx(&2 * pi / &21)) pow 2 - Cx(&1))
   * (cexp(ii * Cx(&2 * pi / &21)) pow 8 - Cx(&1))
   * (cexp(ii * Cx(&2 * pi / &21)) pow 10 - Cx(&1))) = Cx(&0)`,
  REWRITE_TAC[CLASSNO_CYCLO_POLY21; CLASSNO_CYCLO_PHI21; COMPLEX_MUL_LZERO]);;

let CLASSNO_CYCLO_ALG21 = prove
 (`!z w s1 s4 s5 s2 s8 s10:complex.
     (z pow 2) pow 10 * ((w * s1 * z pow 1) * (w * s4 * z pow 4)
     * (w * s5 * z pow 5)) pow 2 + ((w * s2 * z pow 2) * (w * s8 * z pow 8)
     * (w * s10 * z pow 10)) pow 2 - Cx(&5) * (z pow 2) pow 5
     * ((w * s1 * z pow 1) * (w * s4 * z pow 4) * (w * s5 * z pow 5))
     * ((w * s2 * z pow 2) * (w * s8 * z pow 8) * (w * s10 * z pow 10))
     = Cx(&0)
     ==> ~(z = Cx(&0)) ==> ~(w = Cx(&0))
     ==> (s1 * s4 * s5) pow 2 + (s2 * s8 * s10) pow 2 =
         Cx(&5) * (s1 * s4 * s5) * (s2 * s8 * s10)`,
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM COMPLEX_SUB_0] THEN
  MATCH_MP_TAC(MESON[COMPLEX_ENTIRE]
   `!a x:complex. ~(a = Cx(&0)) /\ a * x = Cx(&0) ==> x = Cx(&0)`) THEN
  EXISTS_TAC `(w:complex) pow 6 * (z:complex) pow 40` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_ENTIRE; COMPLEX_POW_EQ_0; ARITH_EQ];
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    CONV_TAC COMPLEX_RING]);;

let CLASSNO_CYCLO_QUAD21 = prove
 (`(sin(pi * &1 / &21) * sin(pi * &4 / &21) * sin(pi * &5 / &21)) pow 2 +
   (sin(pi * &2 / &21) * sin(pi * &8 / &21) * sin(pi * &10 / &21)) pow 2 =
   &5 * (sin(pi * &1 / &21) * sin(pi * &4 / &21) * sin(pi * &5 / &21)) *
   (sin(pi * &2 / &21) * sin(pi * &8 / &21) * sin(pi * &10 / &21))`,
  MP_TAC CLASSNO_CYCLO_FZERO21 THEN
  REWRITE_TAC[CLASSNO_CYCLO_SIN_ROOT] THEN
  REWRITE_TAC[CLASSNO_CYCLO_CEXP_DOUBLE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CLASSNO_CYCLO_ALG21) THEN
  REWRITE_TAC[CEXP_NZ; COMPLEX_ENTIRE; II_NZ; CX_INJ; REAL_OF_NUM_EQ;
              ARITH_EQ] THEN
  REWRITE_TAC[GSYM CX_INJ; CX_ADD; CX_MUL; CX_POW]);;

let CLASSNO_CYCLO_LT21 = prove
 (`&0 < sin(pi * &1 / &21) * sin(pi * &4 / &21) * sin(pi * &5 / &21) /\
   sin(pi * &1 / &21) * sin(pi * &4 / &21) * sin(pi * &5 / &21) <
   sin(pi * &2 / &21) * sin(pi * &8 / &21) * sin(pi * &10 / &21)`,
  SUBGOAL_THEN `!a. 0 < a /\ a < 21 ==> &0 < sin(pi * &a / &21)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CLASSNO_GAUSS_SIN_POS THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN CONV_TAC NUM_REDUCE_CONV;
    MATCH_MP_TAC CLASSNO_CYCLO_PROD3_LT THEN REPEAT CONJ_TAC THEN
    TRY(FIRST_X_ASSUM MATCH_MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
        NO_TAC) THEN
    MATCH_MP_TAC SIN_MONO_LT THEN MP_TAC PI_POS THEN REAL_ARITH_TAC]);;

let CLASSNO_CYCLO_RATIO21 = prove
 (`(sin(pi * &2 / &21) * sin(pi * &8 / &21) * sin(pi * &10 / &21)) /
   (sin(pi * &1 / &21) * sin(pi * &4 / &21) * sin(pi * &5 / &21)) =
   (&5 + sqrt(&21)) / &2`,
  MATCH_MP_TAC CLASSNO_CYCLO_QUADRATIC THEN
  REWRITE_TAC[CLASSNO_CYCLO_LT21; CLASSNO_CYCLO_QUAD21] THEN
  SIMP_TAC[SQRT_POS_LE; SQRT_POW_2; REAL_POS] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* The sum over a = 1 .. 20, for coefficients with the values (a | 21).      *)

let CLASSNO_CYCLO_SUM21 = prove
 (`!c. c 1 = &1 /\ c 2 = -- &1 /\ c 3 = &0 /\ c 4 = &1 /\ c 5 = &1 /\
       c 6 = &0 /\ c 7 = &0 /\ c 8 = -- &1 /\ c 9 = &0 /\ c 10 = -- &1 /\
       c 11 = -- &1 /\ c 12 = &0 /\ c 13 = -- &1 /\ c 14 = &0 /\
       c 15 = &0 /\ c 16 = &1 /\ c 17 = &1 /\ c 18 = &0 /\ c 19 = -- &1 /\
       c 20 = &1
       ==> sum(1..20) (\a. c a * log(sin(pi * &a / &21))) =
           --(&2 * log((&5 + sqrt(&21)) / &2))`,
  GEN_TAC THEN STRIP_TAC THEN
  CONV_TAC(LAND_CONV EXPAND_SUM_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM CLASSNO_CYCLO_RATIO21] THEN
  REWRITE_TAC(map (MATCH_MP CLASSNO_CYCLO_SIN_SYM o ARITH_RULE)
   [`10 + 11 = 21`; `8 + 13 = 21`; `5 + 16 = 21`; `4 + 17 = 21`;
    `2 + 19 = 21`; `1 + 20 = 21`]) THEN
  SIMP_TAC(LOG_DIV :: LOG_MUL :: REAL_LT_MUL_EQ ::
           map (MATCH_MP CLASSNO_GAUSS_SIN_POS o ARITH_RULE)
   [`1 <= 1 /\ 1 < 21`; `1 <= 2 /\ 2 < 21`; `1 <= 4 /\ 4 < 21`;
    `1 <= 5 /\ 5 < 21`; `1 <= 8 /\ 8 < 21`; `1 <= 10 /\ 10 < 21`]) THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* k = 33: Phi_33 vanishes at exp(2 pi i / 33); the quadratic identity.      *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_CYCLO_POLY33 = prove
 (`!y:complex.
     y pow 18 * ((y pow 1 - Cx(&1)) * (y pow 2 - Cx(&1)) * (y pow 4 - Cx(&1))
     * (y pow 8 - Cx(&1)) * (y pow 16 - Cx(&1))) pow 2
     + ((y pow 5 - Cx(&1)) * (y pow 7 - Cx(&1)) * (y pow 10 - Cx(&1))
     * (y pow 13 - Cx(&1)) * (y pow 14 - Cx(&1))) pow 2 - Cx(&46) * y pow 9
     * ((y pow 1 - Cx(&1)) * (y pow 2 - Cx(&1)) * (y pow 4 - Cx(&1))
     * (y pow 8 - Cx(&1)) * (y pow 16 - Cx(&1)))
     * ((y pow 5 - Cx(&1)) * (y pow 7 - Cx(&1)) * (y pow 10 - Cx(&1))
     * (y pow 13 - Cx(&1)) * (y pow 14 - Cx(&1))) =
     (Cx(&1) - y + y pow 3 - y pow 4 + y pow 6 - y pow 7 + y pow 9 - y pow 10
      + y pow 11 - y pow 13 + y pow 14 - y pow 16 + y pow 17 - y pow 19
      + y pow 20) *
     (Cx(&1) + y + y pow 2 - Cx(&2) * y pow 5 - Cx(&2) * y pow 6 - Cx(&4)
      * y pow 7 - Cx(&2) * y pow 8 - Cx(&48) * y pow 9 - y pow 10 + Cx(&44)
      * y pow 11 + Cx(&48) * y pow 12 + Cx(&47) * y pow 13 + y pow 14
      - Cx(&45) * y pow 15 - Cx(&41) * y pow 16 + Cx(&8) * y pow 17 - Cx(&35)
      * y pow 18 + Cx(&9) * y pow 19 + Cx(&9) * y pow 20 - Cx(&35) * y pow 21
      + Cx(&44) * y pow 23 - Cx(&5) * y pow 24 + Cx(&35) * y pow 25 - Cx(&21)
      * y pow 26 - Cx(&109) * y pow 27 - Cx(&12) * y pow 28 + Cx(&77)
      * y pow 29 + Cx(&69) * y pow 30 + Cx(&67) * y pow 31 + Cx(&21)
      * y pow 32 - Cx(&89) * y pow 33 - y pow 34 + Cx(&20) * y pow 35
      - Cx(&16) * y pow 36 + Cx(&38) * y pow 37 - Cx(&14) * y pow 38
      - Cx(&116) * y pow 39 - Cx(&14) * y pow 40 + Cx(&38) * y pow 41
      - Cx(&16) * y pow 42 + Cx(&20) * y pow 43 - y pow 44 - Cx(&89)
      * y pow 45 + Cx(&21) * y pow 46 + Cx(&67) * y pow 47 + Cx(&69)
      * y pow 48 + Cx(&77) * y pow 49 - Cx(&12) * y pow 50 - Cx(&109)
      * y pow 51 - Cx(&21) * y pow 52 + Cx(&35) * y pow 53 - Cx(&5) * y pow 54
      + Cx(&44) * y pow 55 - Cx(&35) * y pow 57 + Cx(&9) * y pow 58 + Cx(&9)
      * y pow 59 - Cx(&35) * y pow 60 + Cx(&8) * y pow 61 - Cx(&41) * y pow 62
      - Cx(&45) * y pow 63 + y pow 64 + Cx(&47) * y pow 65 + Cx(&48)
      * y pow 66 + Cx(&44) * y pow 67 - y pow 68 - Cx(&48) * y pow 69 - Cx(&2)
      * y pow 70 - Cx(&4) * y pow 71 - Cx(&2) * y pow 72 - Cx(&2) * y pow 73
      + y pow 76 + y pow 77 + y pow 78)`,
  CONV_TAC COMPLEX_RING);;

let CLASSNO_CYCLO_PHI33 = prove
 (`Cx(&1) - cexp(ii * Cx(&2 * pi / &33)) + cexp(ii * Cx(&2 * pi / &33)) pow 3
   - cexp(ii * Cx(&2 * pi / &33)) pow 4 + cexp(ii * Cx(&2 * pi / &33)) pow 6
   - cexp(ii * Cx(&2 * pi / &33)) pow 7 + cexp(ii * Cx(&2 * pi / &33)) pow 9
   - cexp(ii * Cx(&2 * pi / &33)) pow 10 + cexp(ii * Cx(&2 * pi / &33)) pow 11
   - cexp(ii * Cx(&2 * pi / &33)) pow 13 + cexp(ii * Cx(&2 * pi / &33)) pow 14
   - cexp(ii * Cx(&2 * pi / &33)) pow 16 + cexp(ii * Cx(&2 * pi / &33)) pow 17
   - cexp(ii * Cx(&2 * pi / &33)) pow 19 + cexp(ii * Cx(&2 * pi / &33)) pow 20
   = Cx(&0)`,
  MP_TAC(MATCH_MP CLASSNO_CYCLO_ROOT_1 (ARITH_RULE `~(33 = 0)`)) THEN
  MP_TAC(MATCH_MP CLASSNO_CYCLO_ROOT_NE_1 (ARITH_RULE `0 < 3 /\ 3 < 33`)) THEN
  MP_TAC(MATCH_MP CLASSNO_CYCLO_ROOT_NE_1 (ARITH_RULE `0 < 11 /\ 11 < 33`)) THEN
  SPEC_TAC(`cexp(ii * Cx(&2 * pi / &33))`,`y:complex`) THEN
  GEN_TAC THEN REPEAT DISCH_TAC THEN
  MP_TAC(COMPLEX_RING
   `(y pow 3 - Cx(&1)) * (y pow 11 - Cx(&1)) *
    (Cx(&1) - y + y pow 3 - y pow 4 + y pow 6 - y pow 7 + y pow 9 - y pow 10
     + y pow 11 - y pow 13 + y pow 14 - y pow 16 + y pow 17 - y pow 19
     + y pow 20) =
    (y pow 33 - Cx(&1)) * (y - Cx(&1))`) THEN
  ASM_REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_MUL_LZERO; COMPLEX_ENTIRE;
                  COMPLEX_SUB_0]);;

let CLASSNO_CYCLO_FZERO33 = prove
 (`cexp(ii * Cx(&2 * pi / &33)) pow 18
   * ((cexp(ii * Cx(&2 * pi / &33)) pow 1 - Cx(&1))
   * (cexp(ii * Cx(&2 * pi / &33)) pow 2 - Cx(&1))
   * (cexp(ii * Cx(&2 * pi / &33)) pow 4 - Cx(&1))
   * (cexp(ii * Cx(&2 * pi / &33)) pow 8 - Cx(&1))
   * (cexp(ii * Cx(&2 * pi / &33)) pow 16 - Cx(&1))) pow 2
   + ((cexp(ii * Cx(&2 * pi / &33)) pow 5 - Cx(&1))
   * (cexp(ii * Cx(&2 * pi / &33)) pow 7 - Cx(&1))
   * (cexp(ii * Cx(&2 * pi / &33)) pow 10 - Cx(&1))
   * (cexp(ii * Cx(&2 * pi / &33)) pow 13 - Cx(&1))
   * (cexp(ii * Cx(&2 * pi / &33)) pow 14 - Cx(&1))) pow 2 - Cx(&46)
   * cexp(ii * Cx(&2 * pi / &33)) pow 9
   * ((cexp(ii * Cx(&2 * pi / &33)) pow 1 - Cx(&1))
   * (cexp(ii * Cx(&2 * pi / &33)) pow 2 - Cx(&1))
   * (cexp(ii * Cx(&2 * pi / &33)) pow 4 - Cx(&1))
   * (cexp(ii * Cx(&2 * pi / &33)) pow 8 - Cx(&1))
   * (cexp(ii * Cx(&2 * pi / &33)) pow 16 - Cx(&1)))
   * ((cexp(ii * Cx(&2 * pi / &33)) pow 5 - Cx(&1))
   * (cexp(ii * Cx(&2 * pi / &33)) pow 7 - Cx(&1))
   * (cexp(ii * Cx(&2 * pi / &33)) pow 10 - Cx(&1))
   * (cexp(ii * Cx(&2 * pi / &33)) pow 13 - Cx(&1))
   * (cexp(ii * Cx(&2 * pi / &33)) pow 14 - Cx(&1))) = Cx(&0)`,
  REWRITE_TAC[CLASSNO_CYCLO_POLY33; CLASSNO_CYCLO_PHI33; COMPLEX_MUL_LZERO]);;

let CLASSNO_CYCLO_ALG33 = prove
 (`!z w s1 s2 s4 s8 s16 s5 s7 s10 s13 s14:complex.
     (z pow 2) pow 18 * ((w * s1 * z pow 1) * (w * s2 * z pow 2)
     * (w * s4 * z pow 4) * (w * s8 * z pow 8) * (w * s16 * z pow 16)) pow 2
     + ((w * s5 * z pow 5) * (w * s7 * z pow 7) * (w * s10 * z pow 10)
     * (w * s13 * z pow 13) * (w * s14 * z pow 14)) pow 2 - Cx(&46)
     * (z pow 2) pow 9 * ((w * s1 * z pow 1) * (w * s2 * z pow 2)
     * (w * s4 * z pow 4) * (w * s8 * z pow 8) * (w * s16 * z pow 16))
     * ((w * s5 * z pow 5) * (w * s7 * z pow 7) * (w * s10 * z pow 10)
     * (w * s13 * z pow 13) * (w * s14 * z pow 14)) = Cx(&0)
     ==> ~(z = Cx(&0)) ==> ~(w = Cx(&0))
     ==> (s1 * s2 * s4 * s8 * s16) pow 2 + (s5 * s7 * s10 * s13 * s14) pow 2 =
         Cx(&46) * (s1 * s2 * s4 * s8 * s16) * (s5 * s7 * s10 * s13 * s14)`,
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM COMPLEX_SUB_0] THEN
  MATCH_MP_TAC(MESON[COMPLEX_ENTIRE]
   `!a x:complex. ~(a = Cx(&0)) /\ a * x = Cx(&0) ==> x = Cx(&0)`) THEN
  EXISTS_TAC `(w:complex) pow 10 * (z:complex) pow 98` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_ENTIRE; COMPLEX_POW_EQ_0; ARITH_EQ];
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    CONV_TAC COMPLEX_RING]);;

let CLASSNO_CYCLO_QUAD33 = prove
 (`(sin(pi * &1 / &33) * sin(pi * &2 / &33) * sin(pi * &4 / &33)
    * sin(pi * &8 / &33) * sin(pi * &16 / &33)) pow 2 +
   (sin(pi * &5 / &33) * sin(pi * &7 / &33) * sin(pi * &10 / &33)
    * sin(pi * &13 / &33) * sin(pi * &14 / &33)) pow 2 =
   &46 * (sin(pi * &1 / &33) * sin(pi * &2 / &33) * sin(pi * &4 / &33)
         * sin(pi * &8 / &33) * sin(pi * &16 / &33)) *
   (sin(pi * &5 / &33) * sin(pi * &7 / &33) * sin(pi * &10 / &33)
    * sin(pi * &13 / &33) * sin(pi * &14 / &33))`,
  MP_TAC CLASSNO_CYCLO_FZERO33 THEN
  REWRITE_TAC[CLASSNO_CYCLO_SIN_ROOT] THEN
  REWRITE_TAC[CLASSNO_CYCLO_CEXP_DOUBLE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CLASSNO_CYCLO_ALG33) THEN
  REWRITE_TAC[CEXP_NZ; COMPLEX_ENTIRE; II_NZ; CX_INJ; REAL_OF_NUM_EQ;
              ARITH_EQ] THEN
  REWRITE_TAC[GSYM CX_INJ; CX_ADD; CX_MUL; CX_POW]);;

let CLASSNO_CYCLO_LT33 = prove
 (`&0 < sin(pi * &1 / &33) * sin(pi * &2 / &33) * sin(pi * &4 / &33) *
        sin(pi * &8 / &33) * sin(pi * &16 / &33) /\
   sin(pi * &1 / &33) * sin(pi * &2 / &33) * sin(pi * &4 / &33) *
   sin(pi * &8 / &33) * sin(pi * &16 / &33) <
   sin(pi * &5 / &33) * sin(pi * &7 / &33) * sin(pi * &10 / &33) *
   sin(pi * &13 / &33) * sin(pi * &14 / &33)`,
  SUBGOAL_THEN `!a. 0 < a /\ a < 33 ==> &0 < sin(pi * &a / &33)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CLASSNO_GAUSS_SIN_POS THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MATCH_MP_TAC CLASSNO_CYCLO_LT33_ALG THEN EXISTS_TAC `sqrt(&3) / &2` THEN
  REPEAT CONJ_TAC THEN
  TRY(FIRST_X_ASSUM MATCH_MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN NO_TAC) THEN
  REWRITE_TAC[SIN_BOUNDS] THEN
  TRY(MATCH_MP_TAC REAL_LE_DIV THEN SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN
      NO_TAC) THEN
  TRY(MP_TAC(SPEC `&3` SQRT_POW_2) THEN REWRITE_TAC[REAL_POS] THEN
      CONV_TAC REAL_RING) THEN
  REWRITE_TAC[GSYM SIN_PI6; GSYM SIN_PI3] THEN
  MATCH_MP_TAC SIN_MONO_LT THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let CLASSNO_CYCLO_RATIO33 = prove
 (`(sin(pi * &5 / &33) * sin(pi * &7 / &33) * sin(pi * &10 / &33) *
    sin(pi * &13 / &33) * sin(pi * &14 / &33)) /
   (sin(pi * &1 / &33) * sin(pi * &2 / &33) * sin(pi * &4 / &33) *
    sin(pi * &8 / &33) * sin(pi * &16 / &33)) =
   &23 + &4 * sqrt(&33)`,
  MATCH_MP_TAC(REAL_ARITH `x = (&46 + &8 * s) / &2 ==> x = &23 + &4 * s`) THEN
  MATCH_MP_TAC CLASSNO_CYCLO_QUADRATIC THEN
  REWRITE_TAC[CLASSNO_CYCLO_LT33; CLASSNO_CYCLO_QUAD33] THEN
  SIMP_TAC[REAL_LE_MUL; SQRT_POS_LE; REAL_POS; REAL_POW_MUL; SQRT_POW_2] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* The sum over a = 1 .. 32, for coefficients with the values (a | 33).      *)

let CLASSNO_CYCLO_SUM33 = prove
 (`!c. c 1 = &1 /\ c 2 = &1 /\ c 3 = &0 /\ c 4 = &1 /\ c 5 = -- &1 /\
       c 6 = &0 /\ c 7 = -- &1 /\ c 8 = &1 /\ c 9 = &0 /\ c 10 = -- &1 /\
       c 11 = &0 /\ c 12 = &0 /\ c 13 = -- &1 /\ c 14 = -- &1 /\
       c 15 = &0 /\ c 16 = &1 /\ c 17 = &1 /\ c 18 = &0 /\ c 19 = -- &1 /\
       c 20 = -- &1 /\ c 21 = &0 /\ c 22 = &0 /\ c 23 = -- &1 /\
       c 24 = &0 /\ c 25 = &1 /\ c 26 = -- &1 /\ c 27 = &0 /\
       c 28 = -- &1 /\ c 29 = &1 /\ c 30 = &0 /\ c 31 = &1 /\ c 32 = &1
       ==> sum(1..32) (\a. c a * log(sin(pi * &a / &33))) =
           --(&2 * log(&23 + &4 * sqrt(&33)))`,
  GEN_TAC THEN STRIP_TAC THEN
  CONV_TAC(LAND_CONV EXPAND_SUM_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM CLASSNO_CYCLO_RATIO33] THEN
  REWRITE_TAC(map (MATCH_MP CLASSNO_CYCLO_SIN_SYM o ARITH_RULE)
   [`16 + 17 = 33`; `14 + 19 = 33`; `13 + 20 = 33`; `10 + 23 = 33`;
    `8 + 25 = 33`; `7 + 26 = 33`; `5 + 28 = 33`; `4 + 29 = 33`;
    `2 + 31 = 33`; `1 + 32 = 33`]) THEN
  SIMP_TAC(LOG_DIV :: LOG_MUL :: REAL_LT_MUL_EQ ::
           map (MATCH_MP CLASSNO_GAUSS_SIN_POS o ARITH_RULE)
   [`1 <= 1 /\ 1 < 33`; `1 <= 2 /\ 2 < 33`; `1 <= 4 /\ 4 < 33`;
    `1 <= 5 /\ 5 < 33`; `1 <= 7 /\ 7 < 33`; `1 <= 8 /\ 8 < 33`;
    `1 <= 10 /\ 10 < 33`; `1 <= 13 /\ 13 < 33`; `1 <= 14 /\ 14 < 33`;
    `1 <= 16 /\ 16 < 33`]) THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The two fundamental units exceed 1.                                       *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_CYCLO_LOG_POS = prove
 (`&0 < log((&5 + sqrt(&21)) / &2) /\ &0 < log(&23 + &4 * sqrt(&33))`,
  CONJ_TAC THEN MATCH_MP_TAC LOG_POS_LT THEN
  MP_TAC(SPEC `&21` SQRT_POS_LE) THEN MP_TAC(SPEC `&33` SQRT_POS_LE) THEN
  REWRITE_TAC[REAL_POS] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Evaluation of the real characters qchar 21 and qchar 33: Jacobi symbols   *)
(* (a | m) for numerals a and odd squarefree m, from multiplicativity in m   *)
(* and the Euler criterion for the prime factors.                            *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_CYCLO_JACOBI_EULER = prove
 (`!a p (v:int).
     prime p /\ 3 <= p /\ (v = -- &1 \/ v = &0 \/ v = &1) /\
     (v == &a pow ((p - 1) DIV 2)) (mod &p)
     ==> jacobi(a,p) = v`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`a:num`; `p:num`] JACOBI_EULER) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `3 <= p` THEN ARITH_TAC;
    DISCH_TAC] THEN
  MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `&p:int` THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`a:num`; `p:num`] JACOBI_CASES) THEN
    UNDISCH_TAC `(v:int) = -- &1 \/ v = &0 \/ v = &1` THEN
    UNDISCH_TAC `3 <= p` THEN REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
    INT_ARITH_TAC;
    MATCH_MP_TAC(INTEGER_RULE
     `!x y z n:int. (x == z) (mod n) /\ (y == z) (mod n)
                    ==> (x == y) (mod n)`) THEN
    EXISTS_TAC `(&a pow ((p - 1) DIV 2)):int` THEN ASM_REWRITE_TAC[]]);;

let CLASSNO_CYCLO_JACOBI_CONV =
  let rec powmod b e m =
    if e = 0 then 1 mod m else
    let h = powmod b (e / 2) m in
    let h2 = (h * h) mod m in
    if e mod 2 = 0 then h2 else (h2 * b) mod m in
  let rec least_factor n d =
    if d * d > n then n else if n mod d = 0 then d
    else least_factor n (d + 2) in
  let side_conv =
    REWRITE_CONV[CLASSNO_LIMIT_PRIMES] THENC
    ONCE_DEPTH_CONV PRIME_CONV THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV [GSYM INT_REM_EQ] THENC
    NUM_REDUCE_CONV THENC INT_REDUCE_CONV THENC REWRITE_CONV[] in
  let rec conv tm =
    let jac,ap = dest_comb tm in
    if fst(dest_const jac) <> "jacobi" then failwith "CLASSNO_CYCLO_JACOBI_CONV"
    else
    let atm,mtm = dest_pair ap in
    let a = dest_small_numeral atm and m = dest_small_numeral mtm in
    if m < 3 || m mod 2 = 0 then failwith "CLASSNO_CYCLO_JACOBI_CONV" else
    let p = least_factor m 3 in
    if p = m then
      let r = powmod (a mod p) ((p - 1) / 2) p in
      let v = if r = 0 then `&0:int` else if r = 1 then `&1:int`
              else `-- &1:int` in
      let th = SPECL [atm; mtm; v] CLASSNO_CYCLO_JACOBI_EULER in
      MP th (EQT_ELIM(side_conv(lhand(concl th))))
    else
      let th = SPECL [atm; mk_small_numeral p; mk_small_numeral(m / p)]
                     JACOBI_RMUL in
      let th1 = CONV_RULE(LAND_CONV(RAND_CONV(RAND_CONV NUM_MULT_CONV))) th in
      CONV_RULE(RAND_CONV(BINOP_CONV conv THENC INT_MUL_CONV)) th1 in
  conv;;

let CLASSNO_CYCLO_QCHAR_CONV =
  GEN_REWRITE_CONV I [qchar] THENC RAND_CONV CLASSNO_CYCLO_JACOBI_CONV THENC
  REWRITE_CONV[int_of_num_th; int_neg_th];;

(* ------------------------------------------------------------------------- *)
(* The main results: the cyclotomic identities with the characters qchar 21, *)
(* qchar 33, and the values of L(1, chi) via CLASSNO_L1_EVEN.                *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_SIN_IDENTITIES = prove
 (`sum(1..20) (\a. qchar 21 a * log(sin(pi * &a / &21))) =
  --(&2 * log((&5 + sqrt(&21)) / &2)) /\
  sum(1..32) (\a. qchar 33 a * log(sin(pi * &a / &33))) =
  --(&2 * log(&23 + &4 * sqrt(&33)))`,
  CONJ_TAC THENL
   [MATCH_MP_TAC CLASSNO_CYCLO_SUM21; MATCH_MP_TAC CLASSNO_CYCLO_SUM33] THEN
  CONV_TAC(ONCE_DEPTH_CONV CLASSNO_CYCLO_QCHAR_CONV) THEN REWRITE_TAC[]);;

let CLASSNO_CYCLO_SQUAREFREE = prove
 (`squarefree 21 /\ squarefree 33`,
  SUBGOAL_THEN `21 = 3 * 7 /\ 33 = 3 * 11` (CONJUNCTS_THEN SUBST1_TAC) THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SQUAREFREE_MUL] THEN
  SIMP_TAC[PRIME_IMP_SQUAREFREE; CLASSNO_LIMIT_PRIMES] THEN
  CONV_TAC(ONCE_DEPTH_CONV COPRIME_CONV) THEN REWRITE_TAC[]);;

let CLASSNO_L1_REAL = prove
 (`norm(Lfunction (\n. Cx(qchar 21 n))) =
  &2 * log((&5 + sqrt(&21)) / &2) / sqrt(&21) /\
  norm(Lfunction (\n. Cx(qchar 33 n))) =
  &2 * log(&23 + &4 * sqrt(&33)) / sqrt(&33)`,
  MP_TAC(SPEC `33` CLASSNO_L1_EVEN) THEN MP_TAC(SPEC `21` CLASSNO_L1_EVEN) THEN
  REWRITE_TAC[CLASSNO_CYCLO_SQUAREFREE] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[CLASSNO_SIN_IDENTITIES] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_MUL; REAL_ABS_NUM] THEN
  SIMP_TAC[CLASSNO_CYCLO_LOG_POS; REAL_ARITH `&0 < x ==> abs x = x`] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC]);;
