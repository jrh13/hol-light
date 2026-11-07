(* ========================================================================= *)
(* Gauss sums of real characters and the class number formulas of Dirichlet  *)
(* in absolute value.                                                        *)
(*                                                                           *)
(* Purpose: for squarefree q = 3 mod 4,                                      *)
(* abs L(1, chi_q) = pi T / ((2 - chi_q(2)) sqrt q) with T the absolute      *)
(* value of the sum of chi_q(a) over 0 < a <= (q - 1)/2 (CLASSNO_L1_ODD),    *)
(* and for squarefree q = 1 mod 4, q > 1, abs L(1, chi_q) = abs(sum over     *)
(* 0 < a < q of chi_q(a) log sin(pi a / q)) / sqrt q (CLASSNO_L1_EVEN),      *)
(* where chi_q = qchar q is the Jacobi symbol (. | q): the class number      *)
(* formulas of Dirichlet in the form used by Baker (Transcendental Number    *)
(* Theory, Ch. 5, sec. 4), without the sign of the Gauss sum and without the *)
(* class numbers themselves.                                                 *)
(*                                                                           *)
(* Method: for a general Dirichlet character c modulo m with the Gauss sum   *)
(* property (the sum over a < m of c(a) e(a n/m) is c(n) gs for all n), the  *)
(* boundary series of log(1 - e^(i t)) (CLASSNO_GAUSS_SUMS_CEXP, from        *)
(* CLOG_CONVERGES_STRONG) gives the finite expansion of L(1,c)               *)
(* (LFUNCTION_GAUSS_EXPANSION) and its even and odd evaluations              *)
(* (LFUNCTION_GAUSS_EVEN, LFUNCTION_GAUSS_ODD); abs gs = sqrt m for real c   *)
(* (CLASSNO_GAUSS_NORM), so abs L(1,c) = pi abs S / m^(3/2) for real odd c,  *)
(* S the sum of a c(a) over 0 < a < m (CLASSNO_GAUSS_LFUNCTION_ODD_NORM, any *)
(* modulus); for odd m the moment identity S (1 - 2 c(2)) = c(2) m T         *)
(* (CLASSNO_GAUSS_ODD_MOMENT) gives the form with T                          *)
(* (LFUNCTION_GAUSS_ODD_NORM). The Gauss sum property holds for real         *)
(* non-principal characters modulo primes and is multiplicative in the       *)
(* modulus (Chinese remainder theorem: the bijection CLASSNO_GAUSS_CRT_IMAGE *)
(* and the reindexing CLASSNO_GAUSS_CRT_VSUM), hence holds for every family  *)
(* of real characters, multiplicative in an odd squarefree modulus           *)
(* (CLASSNO_GAUSS_PROPERTY_SQUAREFREE); this gives the general class number  *)
(* formulas CLASSNO_GAUSS_L1_ODD_GEN, CLASSNO_GAUSS_L1_EVEN_GEN, and the     *)
(* last section instantiates them with qchar.                                *)
(*                                                                           *)
(* Main results: CLASSNO_L1_ODD, CLASSNO_L1_EVEN; QCHAR_GAUSS_PROPERTY (the  *)
(* Gauss sum property of qchar m for odd squarefree m), QCHAR_NONPRINCIPAL   *)
(* (qchar m is nonprincipal for odd squarefree m > 1); for general Dirichlet *)
(* characters LFUNCTION_GAUSS_EXPANSION, LFUNCTION_GAUSS_EVEN,               *)
(* LFUNCTION_GAUSS_ODD, LFUNCTION_GAUSS_EVEN_NORM,                           *)
(* CLASSNO_GAUSS_LFUNCTION_ODD_NORM, LFUNCTION_GAUSS_ODD_NORM,               *)
(* CLASSNO_GAUSS_SUMS_CEXP, CLASSNO_GAUSS_NORM, CLASSNO_GAUSS_ODD_MOMENT,    *)
(* CLASSNO_GAUSS_PROPERTY_SQUAREFREE, CLASSNO_GAUSS_L1_ODD_GEN,              *)
(* CLASSNO_GAUSS_L1_EVEN_GEN, SERIES_VSUM_FAMILY (a finite sum of series);   *)
(* CLASSNO_GAUSS_ROOT_EQ_1 (the roots of unity e(a/m) equal to 1),           *)
(* CLASSNO_GAUSS_CRT_IMAGE, CLASSNO_GAUSS_CRT_VSUM (used for the products    *)
(* and sums of section 22); helper names CLASSNO_GAUSS_*.                    *)
(*                                                                           *)
(* Uses: Baker/classno_chardefs.ml (qchar), Baker/classno_series.ml          *)
(* (QCHAR_DIRICHLET, CLASSNO_SERIES_QCHAR_RMUL); 100/dirichlet.ml            *)
(* (dirichlet_character, Lfunction),                                         *)
(* Library/jacobi.ml (JACOBI_PRIME, JACOBI_RMUL, JACOBI_MINUS1_CASES),       *)
(* Library/primitive.ml (QUADRATIC_NONRESIDUE_EXISTS),                       *)
(* Library/floor.ml (INTEGER_DIV), Multivariate/cauchy.ml                    *)
(* (CLOG_CONVERGES_STRONG), Multivariate/transcendentals.ml (CEXP_II_NE_1),  *)
(* Multivariate/vectors.ml (VSUM_INJECTION).                                 *)
(*                                                                           *)
(* The library files come first, in the order of Baker/make.ml               *)
(* (Library/jacobi.ml before the Multivariate files), so that the file also  *)
(* loads alone.                                                              *)
(* ========================================================================= *)

needs "Library/jacobi.ml";;
needs "Examples/mangoldt.ml";;
needs "100/dirichlet.ml";;
needs "Multivariate/cauchy.ml";;
needs "Baker/classno_series.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The boundary series: for 0 < t < 2 pi, sum_{n>=1} e^(i n t)/n =           *)
(* -log(2 sin(t/2)) + i (pi - t)/2, from CLOG_CONVERGES_STRONG (Abel up to   *)
(* the boundary circle) and the principal branch of clog(1 - e^(i t)).       *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_GAUSS_ONE_SUB_CEXP = prove
 (`!t. &0 < t /\ t < &2 * pi
       ==> Cx(&1) - cexp(ii * Cx t) =
           cexp(Cx(log(&2 * sin(t / &2))) + ii * Cx((t - pi) / &2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sin(t / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SIN_POS_PI THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[CEXP_ADD; GSYM CX_EXP] THEN
  ASM_SIMP_TAC[EXP_LOG; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[CEXP_EULER; GSYM CX_SIN; GSYM CX_COS] THEN
  REWRITE_TAC[REAL_ARITH `(t - pi) / &2 = t / &2 - pi / &2`] THEN
  REWRITE_TAC[COS_SUB; SIN_SUB; COS_PI2; SIN_PI2] THEN
  SUBGOAL_THEN `t = &2 * t / &2` (fun th ->
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
  THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SIN_DOUBLE; COS_DOUBLE_SIN] THEN
  REWRITE_TAC[COMPLEX_EQ; RE_MUL_CX; IM_MUL_CX; RE_ADD; IM_ADD; RE_SUB;
              IM_SUB; RE_MUL_II; IM_MUL_II; RE_CX; IM_CX] THEN
  CONV_TAC REAL_RING);;

let CLASSNO_GAUSS_CLOG_ONE_SUB_CEXP = prove
 (`!t. &0 < t /\ t < &2 * pi
       ==> clog(Cx(&1) - cexp(ii * Cx t)) =
           Cx(log(&2 * sin(t / &2))) + ii * Cx((t - pi) / &2)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CLASSNO_GAUSS_ONE_SUB_CEXP] THEN
  MATCH_MP_TAC CLOG_CEXP THEN
  REWRITE_TAC[IM_ADD; IM_CX; IM_MUL_II; RE_CX; REAL_ADD_LID] THEN
  MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC);;

let CLASSNO_GAUSS_SUMS_CEXP = prove
 (`!t. &0 < t /\ t < &2 * pi
       ==> ((\n. cexp(ii * Cx(&n * t)) / Cx(&n)) sums
            (Cx(--log(&2 * sin(t / &2))) + ii * Cx((pi - t) / &2))) (from 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `--cexp(ii * Cx t)` CLOG_CONVERGES_STRONG) THEN
  REWRITE_TAC[NORM_NEG; NORM_CEXP_II; REAL_LE_REFL] THEN
  ASM_SIMP_TAC[COMPLEX_RING `--(a:complex) = --b <=> a = b`;
               CEXP_II_NE_1] THEN
  REWRITE_TAC[GSYM complex_sub] THEN
  ASM_SIMP_TAC[CLASSNO_GAUSS_CLOG_ONE_SUB_CEXP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SERIES_NEG) THEN
  MATCH_MP_TAC(MESON[]
   `(f:num->complex) = g /\ (l:complex) = l'
    ==> (f sums l) s ==> (g sums l') s`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
    SUBGOAL_THEN
     `!n w. --Cx(&1) pow (n + 1) * (--w) pow n = --(w pow n)`
     (fun th -> REWRITE_TAC[complex_div; COMPLEX_MUL_ASSOC; th])
    THENL
     [INDUCT_TAC THEN GEN_TAC THEN
      REWRITE_TAC[ADD_CLAUSES; complex_pow; COMPLEX_POW_1] THENL
       [CONV_TAC COMPLEX_RING;
        FIRST_X_ASSUM(MP_TAC o SPEC `w:complex`) THEN CONV_TAC COMPLEX_RING];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM CEXP_N; CX_MUL] THEN
    REWRITE_TAC[COMPLEX_MUL_LNEG; COMPLEX_NEG_NEG] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC COMPLEX_RING;
    REWRITE_TAC[COMPLEX_EQ; RE_NEG; IM_NEG; RE_ADD; IM_ADD; RE_CX; IM_CX;
                RE_MUL_II; IM_MUL_II] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The finite Fourier expansion of L(1,c) under the Gauss sum property       *)
(* sum_{a<m} c(a) e(a n/m) = c(n) gs for all n, with gs <> 0 and e(x) =      *)
(* cexp(2 pi i x); the general series of a finite sum of series.             *)
(* ------------------------------------------------------------------------- *)

let SERIES_VSUM_FAMILY = prove
 (`!f:A->num->real^N l s k.
        FINITE s /\ (!i. i IN s ==> (f i sums l i) k)
        ==> ((\n. vsum s (\i. f i n)) sums vsum s l) k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sums] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. vsum (k INTER (0..n)) (\n. vsum s (\i. (f:A->num->real^N) i n)) =
        vsum s (\i. vsum (k INTER (0..n)) (f i))`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN MATCH_MP_TAC(GSYM VSUM_SWAP) THEN
    ASM_REWRITE_TAC[FINITE_INTER_NUMSEG];
    MATCH_MP_TAC LIM_VSUM THEN ASM_REWRITE_TAC[]]);;

let CLASSNO_GAUSS_ANGLE_BOUNDS = prove
 (`!m a. 1 <= a /\ a < m ==> &0 < pi * &a / &m /\ pi * &a / &m < pi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &a /\ &a < &m /\ &0 < &m` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &a / &m /\ &a / &m < &1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ; REAL_MUL_LID]; ALL_TAC] THEN
  MP_TAC PI_POS THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < pi * &a / &m /\ pi * &a / &m < pi * &1`
   MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_LMUL]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let CLASSNO_GAUSS_SUMS_ROOT = prove
 (`!m a. 1 <= a /\ a < m
         ==> ((\n. cexp(ii * Cx(&2 * pi * &a * &n / &m)) / Cx(&n)) sums
              (Cx(--log(&2 * sin(pi * &a / &m))) +
               ii * Cx(pi / &2 - pi * &a / &m))) (from 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `&2 * pi * &a / &m` CLASSNO_GAUSS_SUMS_CEXP) THEN
  ANTS_TAC THENL
   [MP_TAC(SPECL [`m:num`; `a:num`] CLASSNO_GAUSS_ANGLE_BOUNDS) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[]
   `(f:num->complex) = g /\ (l:complex) = l'
    ==> (f sums l) s ==> (g sums l') s`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[real_div; REAL_ARITH
     `&n * &2 * pi * &a * inv(&m) = &2 * pi * &a * &n * inv(&m)`];
    REWRITE_TAC[real_div; REAL_ARITH
     `(&2 * pi * &a * inv(&m)) * inv(&2) = pi * &a * inv(&m)`;
     REAL_ARITH `(pi - &2 * pi * &a * inv(&m)) * inv(&2) =
                 pi * inv(&2) - pi * &a * inv(&m)`]]);;

let LFUNCTION_GAUSS_EXPANSION = prove
 (`!m c gs.
        dirichlet_character m c /\ ~(c = chi_0 m) /\ ~(gs = Cx(&0)) /\
        (!n. vsum(0..m-1) (\a. c a * cexp(ii * Cx(&2 * pi * &a * &n / &m))) =
             c n * gs)
        ==> Lfunction c =
            vsum(1..m-1) (\a. c a * (Cx(--log(&2 * sin(pi * &a / &m))) +
                                     ii * Cx(pi / &2 - pi * &a / &m))) / gs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `c:num->complex`]
    DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(c:num->complex) 0 = Cx(&0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_0; COPRIME_0]; ALL_TAC] THEN
  MATCH_MP_TAC SERIES_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`\n. (c:num->complex) n / Cx(&n)`; `from 1`] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[LFUNCTION]; ALL_TAC] THEN
  MATCH_MP_TAC SUMS_EQ THEN
  EXISTS_TAC
   `\n. vsum(1..m-1) (\a. (c:num->complex) a *
          (cexp(ii * Cx(&2 * pi * &a * &n / &m)) / Cx(&n))) / gs` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    SIMP_TAC[VSUM_CLAUSES_LEFT; LE_0] THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_ADD_LID; ADD_CLAUSES] THEN
    REWRITE_TAC[complex_div; COMPLEX_MUL_ASSOC] THEN
    SIMP_TAC[VSUM_COMPLEX_RMUL; FINITE_NUMSEG] THEN
    DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `~(gs = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD;
    MATCH_MP_TAC SERIES_COMPLEX_DIV THEN
    MATCH_MP_TAC SERIES_VSUM_FAMILY THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC SERIES_COMPLEX_LMUL THEN
    MATCH_MP_TAC CLASSNO_GAUSS_SUMS_ROOT THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Even and odd evaluations of the expansion: c(m - a) = c(m - 1) c(a), and  *)
(* the reflection a |-> m - a of 1..m-1.                                     *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_GAUSS_VSUM_REFLECT = prove
 (`!f:num->real^N m. vsum(1..m-1) f = vsum(1..m-1) (\a. f(m - a))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
  MATCH_MP_TAC VSUM_BIJECTION THEN REWRITE_TAC[IN_NUMSEG] THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `y:num` THEN DISCH_TAC THEN REWRITE_TAC[EXISTS_UNIQUE] THEN
  EXISTS_TAC `m - y:num` THEN ASM_ARITH_TAC);;

let CLASSNO_GAUSS_VSUM_ANTI = prove
 (`!f:num->complex m.
        (!a. 1 <= a /\ a <= m - 1 ==> f(m - a) = --(f a))
        ==> vsum(1..m-1) f = Cx(&0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:num->complex`; `m:num`] CLASSNO_GAUSS_VSUM_REFLECT) THEN
  SUBGOAL_THEN `vsum(1..m-1) (\a. (f:num->complex)(m - a)) =
                vsum(1..m-1) (\a. --(f a))` SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN ASM_SIMP_TAC[];
    REWRITE_TAC[VSUM_NEG] THEN CONV_TAC COMPLEX_RING]);;

let CLASSNO_GAUSS_CHAR_REFLECT = prove
 (`!m c a. dirichlet_character m c /\ 1 <= a /\ a <= m
           ==> c(m - a) = c(m - 1) * c a`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[GSYM(MATCH_MP DIRICHLET_CHARACTER_MUL th)]) THEN
  SUBGOAL_THEN `(m - 1) * a = (a - 1) * m + (m - a)` SUBST1_TAC THENL
   [SUBGOAL_THEN `1 <= m` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_ADD;
                 GSYM INT_OF_NUM_SUB] THEN
    INT_ARITH_TAC;
    ASM_MESON_TAC[DIRICHLET_CHARACTER_PERIODIC_GEN]]);;

let CLASSNO_GAUSS_CHAR_SUM_0 = prove
 (`!m c. dirichlet_character m c /\ ~(c = chi_0 m)
         ==> vsum(1..m-1) c = Cx(&0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `c:num->complex`]
    DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL) THEN
  MP_TAC(ISPECL [`m:num`; `c:num->complex`] DIRICHLET_CHARACTER_ZEROSUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(c:num->complex) m = Cx(&0)` MP_TAC THENL
   [ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_0; COPRIME_REFL]; ALL_TAC] THEN
  UNDISCH_TAC `vsum (1..m) c = Cx(&0)` THEN
  ASM_SIMP_TAC[VSUM_CLAUSES_RIGHT; LE_1] THEN CONV_TAC COMPLEX_RING);;

let CLASSNO_GAUSS_SIN_POS = prove
 (`!m a. 1 <= a /\ a < m ==> &0 < sin(pi * &a / &m)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SIN_POS_PI THEN
  ASM_SIMP_TAC[CLASSNO_GAUSS_ANGLE_BOUNDS]);;

let CLASSNO_GAUSS_PI_REFLECT = prove
 (`!m a. ~(m = 0) /\ a <= m ==> pi * &(m - a) / &m = pi - pi * &a / &m`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
  UNDISCH_TAC `~(m = 0)` THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
  CONV_TAC REAL_FIELD);;

let LFUNCTION_GAUSS_EVEN = prove
 (`!m c gs.
        dirichlet_character m c /\ ~(c = chi_0 m) /\ c(m - 1) = Cx(&1) /\
        ~(gs = Cx(&0)) /\
        (!n. vsum(0..m-1) (\a. c a * cexp(ii * Cx(&2 * pi * &a * &n / &m))) =
             c n * gs)
        ==> Lfunction c =
            --vsum(1..m-1) (\a. c a * Cx(log(sin(pi * &a / &m)))) / gs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `c:num->complex`; `gs:complex`]
    LFUNCTION_GAUSS_EXPANSION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`m:num`; `c:num->complex`]
    DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `vsum(1..m-1) (\a. (c:num->complex) a * Cx(pi / &2 - pi * &a / &m)) =
    Cx(&0)`
  MP_TAC THENL
   [MATCH_MP_TAC CLASSNO_GAUSS_VSUM_ANTI THEN X_GEN_TAC `a:num` THEN
    STRIP_TAC THEN
    ASM_SIMP_TAC[CLASSNO_GAUSS_CHAR_REFLECT; CLASSNO_GAUSS_PI_REFLECT;
                 ARITH_RULE `a <= m - 1 ==> a <= m`] THEN
    REWRITE_TAC[REAL_ARITH `pi / &2 - (pi - x) = --(pi / &2 - x)`; CX_NEG] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `c:num->complex`] CLASSNO_GAUSS_CHAR_SUM_0) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `vsum(1..m-1) (\a. (c:num->complex) a *
       (Cx(--log(&2 * sin(pi * &a / &m))) + ii * Cx(pi / &2 - pi * &a / &m))) =
    vsum(1..m-1) (\a. --Cx(log(&2)) * c a -
                      c a * Cx(log(sin(pi * &a / &m))) +
                      ii * (c a * Cx(pi / &2 - pi * &a / &m)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < sin(pi * &a / &m)` ASSUME_TAC THENL
     [MATCH_MP_TAC CLASSNO_GAUSS_SIN_POS THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_MUL; REAL_OF_NUM_LT; ARITH] THEN
    REWRITE_TAC[CX_NEG; CX_ADD] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SIMP_TAC[VSUM_ADD; VSUM_SUB; VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC COMPLEX_RING);;

let LFUNCTION_GAUSS_ODD = prove
 (`!m c gs.
        dirichlet_character m c /\ c(m - 1) = --Cx(&1) /\
        ~(gs = Cx(&0)) /\
        (!n. vsum(0..m-1) (\a. c a * cexp(ii * Cx(&2 * pi * &a * &n / &m))) =
             c n * gs)
        ==> Lfunction c =
            --(ii * Cx(pi / &m) * vsum(1..m-1) (\a. Cx(&a) * c a)) / gs`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(c = chi_0 m)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[chi_0] THEN COND_CASES_TAC THEN
    REWRITE_TAC[COMPLEX_EQ; RE_NEG; RE_CX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `c:num->complex`; `gs:complex`]
    LFUNCTION_GAUSS_EXPANSION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`m:num`; `c:num->complex`]
    DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `vsum(1..m-1) (\a. (c:num->complex) a *
                      Cx(--log(&2 * sin(pi * &a / &m)))) = Cx(&0)`
  MP_TAC THENL
   [MATCH_MP_TAC CLASSNO_GAUSS_VSUM_ANTI THEN X_GEN_TAC `a:num` THEN
    STRIP_TAC THEN
    ASM_SIMP_TAC[CLASSNO_GAUSS_CHAR_REFLECT; CLASSNO_GAUSS_PI_REFLECT;
                 ARITH_RULE `a <= m - 1 ==> a <= m`] THEN
    REWRITE_TAC[SIN_SUB; SIN_PI; COS_PI] THEN
    REWRITE_TAC[REAL_ARITH `&0 * (x:real) - -- &1 * y = y`] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `c:num->complex`] CLASSNO_GAUSS_CHAR_SUM_0) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `vsum(1..m-1) (\a. (c:num->complex) a *
       (Cx(--log(&2 * sin(pi * &a / &m))) + ii * Cx(pi / &2 - pi * &a / &m))) =
    vsum(1..m-1) (\a. c a * Cx(--log(&2 * sin(pi * &a / &m))) +
                      ii * (Cx(pi / &2) * c a -
                            Cx(pi / &m) * (Cx(&a) * c a)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    REWRITE_TAC[real_div; REAL_ARITH `pi * &a * inv(&m) = (pi * inv(&m)) * &a`;
                CX_SUB; CX_MUL] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SIMP_TAC[VSUM_ADD; VSUM_SUB; VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC COMPLEX_RING);;

(* ------------------------------------------------------------------------- *)
(* Odd characters mod odd m: S (1 - 2 c(2)) = c(2) m T, where S is the       *)
(* sum of a c(a) over 0 < a < m and T the sum of c(a) over 0 < a <= (m - 1)  *)
(* DIV 2.                                                                    *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_GAUSS_VSUM_HALVES = prove
 (`!f:num->real^N h.
        vsum(1..2 * h) f = vsum(1..h) (\b. f b + f((2 * h + 1) - b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MULT_2] THEN
  SIMP_TAC[VSUM_ADD_SPLIT; ARITH_RULE `1 <= h + 1`] THEN
  SUBGOAL_THEN
   `vsum(h + 1..h + h) (f:num->real^N) = vsum(1..h) (\i. f(i + h))`
  SUBST1_TAC THENL [REWRITE_TAC[GSYM VSUM_OFFSET; ADD_AC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\i. (f:num->real^N)(i + h)`; `h + 1`]
    CLASSNO_GAUSS_VSUM_REFLECT) THEN
  REWRITE_TAC[ADD_SUB] THEN DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[GSYM VSUM_ADD; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let CLASSNO_GAUSS_ODD_MOMENT = prove
 (`!m c. ODD m /\ dirichlet_character m c /\ c(m - 1) = --Cx(&1)
         ==> vsum(1..m-1) (\a. Cx(&a) * c a) * (Cx(&1) - Cx(&2) * c 2) =
             c 2 * Cx(&m) * vsum(1..(m - 1) DIV 2) c`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `h:num` SUBST_ALL_TAC o
    REWRITE_RULE[ODD_EXISTS; ADD1]) THEN
  REWRITE_TAC[ADD_SUB] THEN SIMP_TAC[DIV_MULT; ARITH_EQ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_SUB]) THEN
  ASM_CASES_TAC `h = 0` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; VSUM_CLAUSES_NUMSEG; ARITH] THEN
    REWRITE_TAC[COMPLEX_VEC_0] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:num->complex) 0 = Cx(&0) /\ c(2 * h + 1) = Cx(&0)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_EQ_0 th]) THEN
    REWRITE_TAC[COPRIME_0; COPRIME_REFL] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. 1 <= a /\ a <= 2 * h + 1
        ==> c((2 * h + 1) - a) = --((c:num->complex) a)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`2 * h + 1`; `c:num->complex`; `a:num`]
      CLASSNO_GAUSS_CHAR_REFLECT) THEN
    ASM_REWRITE_TAC[ADD_SUB] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  ABBREV_TAC `ss = vsum(1..2 * h) (\a. Cx(&a) * (c:num->complex) a)` THEN
  ABBREV_TAC `uu = vsum(1..h) (\a. Cx(&a) * (c:num->complex) a)` THEN
  ABBREV_TAC `tt = vsum(1..h) (c:num->complex)` THEN
  SUBGOAL_THEN `ss = Cx(&2) * uu - Cx(&(2 * h + 1)) * tt` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ss"; "uu"; "tt"] THEN
    REWRITE_TAC[CLASSNO_GAUSS_VSUM_HALVES] THEN
    SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; GSYM VSUM_SUB; FINITE_NUMSEG] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `b:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE
      `b <= h ==> b <= 2 * h + 1`; CX_SUB] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `ss = c 2 * (Cx(&4) * uu - Cx(&(2 * h + 1)) * tt)`
  ASSUME_TAC THENL
   [ALL_TAC;
    UNDISCH_TAC `ss = c 2 * (Cx(&4) * uu - Cx(&(2 * h + 1)) * tt)` THEN
    UNDISCH_TAC `ss = Cx(&2) * uu - Cx(&(2 * h + 1)) * tt` THEN
    CONV_TAC COMPLEX_RING] THEN
  MAP_EVERY EXPAND_TAC ["ss"; "uu"; "tt"] THEN
  SUBGOAL_THEN
   `vsum(1..2 * h) (\a. Cx(&a) * (c:num->complex) a) =
    vsum(0..2 * h + 1) (\a. Cx(&a) * c a)`
  SUBST1_TAC THENL
   [SIMP_TAC[VSUM_CLAUSES_LEFT; LE_0; ADD_CLAUSES] THEN
    REWRITE_TAC[GSYM ADD1; VSUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
    ASM_REWRITE_TAC[ADD1; COMPLEX_MUL_RZERO; COMPLEX_ADD_LID;
                    COMPLEX_ADD_RID];
    ALL_TAC] THEN
  REWRITE_TAC[VSUM_PAIR_0] THEN SIMP_TAC[VSUM_ADD; FINITE_NUMSEG] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [VSUM_REFLECT] THEN
  REWRITE_TAC[ARITH_RULE `~(h < 0)`; SUB_0] THEN
  SIMP_TAC[GSYM VSUM_ADD; FINITE_NUMSEG] THEN
  SUBGOAL_THEN
   `!g:num->complex. vsum(1..h) g = vsum(0..h) g - g 0`
   (fun th -> ONCE_REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN SIMP_TAC[VSUM_CLAUSES_LEFT; LE_0] THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_SUB_RZERO] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; GSYM VSUM_SUB; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE
   `i <= h ==> 2 * (h - i) + 1 = (2 * h + 1) - 2 * i`] THEN
  ASM_CASES_TAC `i = 0` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; SUB_0] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `2 * i`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_MUL th]) THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE
    `i <= h ==> 2 * i <= 2 * h + 1`; CX_SUB; GSYM REAL_OF_NUM_MUL; CX_MUL] THEN
  CONV_TAC COMPLEX_RING);;

(* ------------------------------------------------------------------------- *)
(* Orthogonality of the roots of unity, and |gs| = sqrt m for real           *)
(* characters with the Gauss sum property.                                   *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_GAUSS_CEXP_EQ_1 = prove
 (`!x. cexp(ii * Cx(&2 * pi * x)) = Cx(&1) <=> integer x`,
  GEN_TAC THEN REWRITE_TAC[CEXP_EQ_1; RE_MUL_II; IM_MUL_II; RE_CX; IM_CX] THEN
  REWRITE_TAC[REAL_NEG_0] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `x:real = n` (fun th -> ASM_REWRITE_TAC[th]) THEN
    POP_ASSUM MP_TAC THEN MP_TAC PI_NZ THEN CONV_TAC REAL_FIELD;
    DISCH_TAC THEN EXISTS_TAC `x:real` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC]);;

let CLASSNO_GAUSS_ROOT_EQ_1 = prove
 (`!m a. cexp(ii * Cx(&2 * pi * &a / &m)) = Cx(&1) <=> m = 0 \/ m divides a`,
  REWRITE_TAC[CLASSNO_GAUSS_CEXP_EQ_1; INTEGER_DIV]);;

let CLASSNO_GAUSS_ORTHO = prove
 (`!m k. ~(m = 0) /\ integer k
         ==> vsum(0..m-1) (\b. cexp(ii * Cx(&2 * pi * k * &b / &m))) =
             if integer(k / &m) then Cx(&m) else Cx(&0)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `z = cexp(ii * Cx(&2 * pi * k / &m))` THEN
  SUBGOAL_THEN
   `!b. cexp(ii * Cx(&2 * pi * k * &b / &m)) = z pow b`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN EXPAND_TAC "z" THEN REWRITE_TAC[GSYM CEXP_N] THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM CX_MUL] THEN
    REWRITE_TAC[real_div; REAL_ARITH
     `&2 * pi * k * &b * inv(&m) = &b * &2 * pi * k * inv(&m)`] THEN
    REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  REWRITE_TAC[VSUM_GP] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(m = 0) ==> ~(m - 1 < 0) /\ (m - 1 + 1) - 0 = m /\
                                        SUC(m - 1) = m`] THEN
  SUBGOAL_THEN `z = Cx(&1) <=> integer(k / &m)` SUBST1_TAC THENL
   [EXPAND_TAC "z" THEN REWRITE_TAC[CLASSNO_GAUSS_CEXP_EQ_1];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(z:complex) pow m = Cx(&1)` SUBST1_TAC THENL
   [EXPAND_TAC "z" THEN REWRITE_TAC[GSYM CEXP_N] THEN
    SUBGOAL_THEN `Cx(&m) * ii * Cx(&2 * pi * k / &m) = ii * Cx(&2 * pi * k)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM CX_MUL; COMPLEX_RING `a * ii * b = ii * a * b`] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `~(m = 0)` THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
      CONV_TAC REAL_FIELD;
      ASM_REWRITE_TAC[CLASSNO_GAUSS_CEXP_EQ_1]];
    REWRITE_TAC[complex_pow; COMPLEX_SUB_REFL; complex_div;
                COMPLEX_MUL_LZERO]]);;

let CLASSNO_GAUSS_INTEGER_DIV = prove
 (`!m a. 2 <= m /\ a < m ==> (integer((&a - &1) / &m) <=> a = 1)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC;
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_SUB_REFL; real_div; REAL_MUL_LZERO; INTEGER_CLOSED]] THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC `(&a - &1) / &m` REAL_ABS_INTEGER_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < &m /\ &2 <= &m /\ &a < &m` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_DIV_EQ_0; REAL_ABS_DIV; REAL_LE_RDIV_EQ; REAL_SUB_0;
               REAL_ARITH `&0 < (m:real) ==> abs m = m`; REAL_MUL_LID;
               REAL_OF_NUM_EQ; ARITH_RULE `2 <= m ==> ~(m = 0)`] THEN
  ASM_CASES_TAC `a = 1` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `a:num` REAL_POS) THEN ASM_REAL_ARITH_TAC);;

let CLASSNO_GAUSS_NORM_SQ = prove
 (`!m c gs.
        dirichlet_character m c /\ ~(c = chi_0 m) /\ (!n. cnj(c n) = c n) /\
        (!n. vsum(0..m-1) (\a. c a * cexp(ii * Cx(&2 * pi * &a * &n / &m))) =
             c n * gs)
        ==> gs * cnj gs = Cx(&m)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `c:num->complex`]
    DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `2 <= m` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIRICHLET_CHARACTER_EQ_1) THEN
  SUBGOAL_THEN
   `gs = vsum(0..m-1) (\b. (c:num->complex) b *
                           cexp(ii * Cx(&2 * pi * &b * &1 / &m)))`
  (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THENL
   [ASM_REWRITE_TAC[COMPLEX_MUL_LID]; ALL_TAC] THEN
  SIMP_TAC[CNJ_VSUM; FINITE_NUMSEG; CNJ_MUL] THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  REWRITE_TAC[COMPLEX_RING `g * c * e:complex = (c * g) * e`] THEN
  SUBGOAL_THEN
   `!n. (c:num->complex) n * gs =
        vsum(0..m-1) (\a. c a * cexp(ii * Cx(&2 * pi * &a * &n / &m)))`
   (fun th -> REWRITE_TAC[th])
  THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; FINITE_NUMSEG] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) VSUM_SWAP o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC] THEN
  SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  SUBGOAL_THEN
   `!a b. cexp(ii * Cx(&2 * pi * &a * &b / &m)) *
          cnj(cexp(ii * Cx(&2 * pi * &b * &1 / &m))) =
          cexp(ii * Cx(&2 * pi * (&a - &1) * &b / &m))`
   (fun th -> REWRITE_TAC[th])
  THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[CNJ_CEXP; CNJ_MUL; CNJ_II; CNJ_CX; GSYM CEXP_ADD] THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[COMPLEX_RING `ii * x + --ii * y = ii * (x - y)`] THEN
    REWRITE_TAC[GSYM CX_SUB] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[CLASSNO_GAUSS_ORTHO; INTEGER_CLOSED] THEN
  SUBGOAL_THEN
   `vsum(0..m-1) (\a. (c:num->complex) a *
       (if integer((&a - &1) / &m) then Cx(&m) else Cx(&0))) =
    vsum(0..m-1) (\a. if a = 1 then Cx(&m) else vec 0)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[CLASSNO_GAUSS_INTEGER_DIV;
                 ARITH_RULE `2 <= m /\ a <= m - 1 ==> a < m`] THEN
    ASM_CASES_TAC `a = 1` THEN
    ASM_REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_RZERO; COMPLEX_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[VSUM_DELTA; IN_NUMSEG] THEN
  ASM_SIMP_TAC[LE_0; ARITH_RULE `2 <= m ==> 1 <= m - 1`]);;

let CLASSNO_GAUSS_NORM = prove
 (`!m c gs.
        dirichlet_character m c /\ ~(c = chi_0 m) /\ (!n. cnj(c n) = c n) /\
        (!n. vsum(0..m-1) (\a. c a * cexp(ii * Cx(&2 * pi * &a * &n / &m))) =
             c n * gs)
        ==> norm gs = sqrt(&m)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CLASSNO_GAUSS_NORM_SQ) THEN
  REWRITE_TAC[COMPLEX_MUL_CNJ; GSYM CX_POW; CX_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SIMP_TAC[POW_2_SQRT; NORM_POS_LE]);;

(* ------------------------------------------------------------------------- *)
(* The absolute values of L(1,c) for real characters c = Cx o f with the     *)
(* Gauss sum property (the shape of CLASSNO_L1_ODD and CLASSNO_L1_EVEN,      *)
(* f = qchar q).                                                             *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_GAUSS_ODD_NONPRINCIPAL = prove
 (`!m c. dirichlet_character m c /\ c(m - 1) = --Cx(&1) ==> ~(c = chi_0 m)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[chi_0] THEN COND_CASES_TAC THEN
  REWRITE_TAC[COMPLEX_EQ; RE_NEG; RE_CX] THEN REAL_ARITH_TAC);;

let LFUNCTION_GAUSS_EVEN_NORM = prove
 (`!m f gs.
        dirichlet_character m (\n. Cx(f n)) /\ ~((\n. Cx(f n)) = chi_0 m) /\
        f(m - 1) = &1 /\
        (!n. vsum(0..m-1)
               (\a. Cx(f a) * cexp(ii * Cx(&2 * pi * &a * &n / &m))) =
             Cx(f n) * gs)
        ==> norm(Lfunction (\n. Cx(f n))) =
            abs(sum(1..m-1) (\a. f a * log(sin(pi * &a / &m)))) / sqrt(&m)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `\n. Cx((f:num->real) n)`; `gs:complex`]
    CLASSNO_GAUSS_NORM) THEN
  ASM_REWRITE_TAC[CNJ_CX] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`m:num`; `\n. Cx((f:num->real) n)`]
    DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&m)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `\n. Cx((f:num->real) n)`; `gs:complex`]
    LFUNCTION_GAUSS_EVEN) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM COMPLEX_NORM_ZERO] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM CX_MUL; VSUM_CX; COMPLEX_NORM_DIV; NORM_NEG;
              COMPLEX_NORM_CX] THEN
  ASM_REWRITE_TAC[]);;

(* The odd-character formula for a general modulus m with the Gauss sum      *)
(* property: abs L(1,f) = pi abs(sum of a f(a) over 0 < a < m) / m^(3/2);    *)
(* for odd m the moment identity turns it into the form with T.              *)

let CLASSNO_GAUSS_LFUNCTION_ODD_NORM = prove
 (`!m f gs.
        dirichlet_character m (\n. Cx(f n)) /\ f(m - 1) = -- &1 /\
        (!n. vsum(0..m-1)
               (\a. Cx(f a) * cexp(ii * Cx(&2 * pi * &a * &n / &m))) =
             Cx(f n) * gs)
        ==> norm(Lfunction (\n. Cx(f n))) =
            pi * abs(sum(1..m-1) (\a. &a * f a)) / (&m * sqrt(&m))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~((\n. Cx(f n)) = chi_0 m)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLASSNO_GAUSS_ODD_NONPRINCIPAL THEN
    ASM_REWRITE_TAC[CX_NEG];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `\n. Cx((f:num->real) n)`; `gs:complex`]
    CLASSNO_GAUSS_NORM) THEN
  ASM_REWRITE_TAC[CNJ_CX] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`m:num`; `\n. Cx((f:num->real) n)`]
    DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&m) /\ &0 < &m` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LT; ALL_TAC] THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `\n. Cx((f:num->real) n)`; `gs:complex`]
    LFUNCTION_GAUSS_ODD) THEN
  ASM_REWRITE_TAC[CX_NEG] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM COMPLEX_NORM_ZERO] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM CX_MUL; VSUM_CX] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; NORM_NEG; COMPLEX_NORM_MUL; COMPLEX_NORM_II;
              COMPLEX_NORM_CX; REAL_ABS_MUL] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `abs(pi / &m) = pi / &m` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    REWRITE_TAC[REAL_POS] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `&0 < sqrt(&m)` THEN UNDISCH_TAC `&0 < &m` THEN
  CONV_TAC REAL_FIELD);;

let LFUNCTION_GAUSS_ODD_NORM = prove
 (`!m f gs.
        ODD m /\ dirichlet_character m (\n. Cx(f n)) /\ f(m - 1) = -- &1 /\
        (!n. vsum(0..m-1)
               (\a. Cx(f a) * cexp(ii * Cx(&2 * pi * &a * &n / &m))) =
             Cx(f n) * gs)
        ==> norm(Lfunction (\n. Cx(f n))) =
            pi * abs(sum(1..(m - 1) DIV 2) f) / ((&2 - f 2) * sqrt(&m))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `f:num->real`; `gs:complex`]
    CLASSNO_GAUSS_LFUNCTION_ODD_NORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&m) /\ &0 < &m` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~(m = 0)` MP_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[ODD]; ALL_TAC] THEN
    REWRITE_TAC[GSYM LT_NZ; GSYM REAL_OF_NUM_LT] THEN SIMP_TAC[SQRT_POS_LT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `\n. Cx((f:num->real) n)`]
    CLASSNO_GAUSS_ODD_MOMENT) THEN
  ASM_REWRITE_TAC[CX_NEG] THEN
  REWRITE_TAC[GSYM CX_MUL; VSUM_CX; GSYM CX_SUB] THEN
  REWRITE_TAC[CX_MUL; GSYM CX_SUB; CX_INJ] THEN
  REWRITE_TAC[GSYM CX_MUL; CX_INJ] THEN
  SUBGOAL_THEN `f 2 = &1 \/ f 2 = -- &1` MP_TAC THENL
   [MP_TAC(ISPECL [`m:num`; `\n. Cx((f:num->real) n)`; `2`]
      DIRICHLET_CHARACTER_NORM) THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_CX] THEN
    SUBGOAL_THEN `coprime(m,2)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REWRITE_TAC[COPRIME_2; GSYM NOT_EVEN; NOT_EVEN]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `s = sum(1..m-1) (\a. &a * f a)` THEN
  ABBREV_TAC `t = sum(1..(m - 1) DIV 2) f` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
   [SUBGOAL_THEN `abs(s:real) = &m * abs(t:real)` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
       `(s:real) * (&1 - &2 * &1) = &1 * m * t ==> s = --(m * t)`)) THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_MUL; REAL_ABS_NUM];
      ALL_TAC];
    SUBGOAL_THEN `abs(s:real) = &m * abs(t:real) / &3` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
       `(s:real) * (&1 - &2 * -- &1) = -- &1 * m * t
        ==> s = --(m * t / &3)`)) THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_NUM];
      ALL_TAC]] THEN
  UNDISCH_TAC `&0 < sqrt(&m)` THEN UNDISCH_TAC `&0 < &m` THEN
  CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* The Gauss sum property, part 1: the Chinese remainder reindexing of a     *)
(* periodic sum, and the product of the Gauss sum properties for coprime     *)
(* moduli.                                                                   *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_GAUSS_PERIODIC_MOD = prove
 (`!f:num->real^N m. (!a. f(a + m) = f a) ==> !x. f(x MOD m) = f x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[MOD_ZERO] THEN
  SUBGOAL_THEN `!q r. (f:num->real^N)(q * m + r) = f r` ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    GEN_TAC THEN
    ONCE_REWRITE_TAC[ARITH_RULE `(q * m + m) + r = (q * m + r) + m`] THEN
    ASM_REWRITE_TAC[];
    GEN_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `x:num` o MATCH_MP DIVISION) THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
      [CONJUNCT1 th]) THEN
    ASM_REWRITE_TAC[]]);;

(* The Chinese remainder bijection (a1,a2) |-> (a1 m2 + a2 m1) MOD (m1 m2)   *)
(* of {0..m1-1} x {0..m2-1} onto 0..m1 m2 - 1 (in the form of VSUM_IMAGE,    *)
(* CPRODUCT_IMAGE), and the reindexing of a periodic vsum.                   *)

let CLASSNO_GAUSS_CRT_IMAGE = prove
 (`!m1 m2.
        coprime(m1,m2) /\ ~(m1 = 0) /\ ~(m2 = 0)
        ==> (!x y. x IN {i,j | i IN 0..m1-1 /\ j IN 0..m2-1} /\
                   y IN {i,j | i IN 0..m1-1 /\ j IN 0..m2-1} /\
                   (\(i,j). (i * m2 + j * m1) MOD (m1 * m2)) x =
                   (\(i,j). (i * m2 + j * m1) MOD (m1 * m2)) y
                   ==> x = y) /\
            IMAGE (\(i,j). (i * m2 + j * m1) MOD (m1 * m2))
                  {i,j | i IN 0..m1-1 /\ j IN 0..m2-1} =
            0..m1 * m2 - 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_NUMSEG; PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`; `i':num`; `j':num`] THEN
    REWRITE_TAC[GSYM CONG] THEN STRIP_TAC THEN
    CONJ_TAC THEN MATCH_MP_TAC CONG_IMP_EQ THENL
     [EXISTS_TAC `m1:num`; EXISTS_TAC `m2:num`] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(m = 0) /\ x <= m - 1 ==> x < m`] THEN
    UNDISCH_TAC `(i * m2 + j * m1 == i' * m2 + j' * m1) (mod (m1 * m2))` THEN
    UNDISCH_TAC `coprime(m1:num,m2)` THEN CONV_TAC NUMBER_RULE;
    DISCH_TAC] THEN
  MATCH_MP_TAC CARD_SUBSET_EQ THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_ELIM_PAIR_THM;
                IN_NUMSEG; LE_0] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `x < n ==> x <= n - 1`) THEN
    ASM_REWRITE_TAC[MOD_LT_EQ; MULT_EQ_0];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) CARD_IMAGE_INJ o lhand o snd) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[FINITE_PRODUCT; FINITE_NUMSEG]];
    DISCH_THEN SUBST1_TAC] THEN
  SIMP_TAC[CARD_PRODUCT; FINITE_NUMSEG; CARD_NUMSEG] THEN
  UNDISCH_TAC `~(m1 = 0)` THEN UNDISCH_TAC `~(m2 = 0)` THEN
  REWRITE_TAC[ARITH_RULE `((n - 1) + 1) - 0 = if n = 0 then 1 else n`] THEN
  SIMP_TAC[MULT_EQ_0]);;

let CLASSNO_GAUSS_CRT_VSUM = prove
 (`!f:num->real^N m1 m2.
        coprime(m1,m2) /\ ~(m1 = 0) /\ ~(m2 = 0) /\
        (!a. f(a + m1 * m2) = f a)
        ==> vsum(0..m1 * m2 - 1) f =
            vsum(0..m1 - 1)
                (\a1. vsum(0..m2 - 1) (\a2. f(a1 * m2 + a2 * m1)))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP CLASSNO_GAUSS_PERIODIC_MOD) THEN
  MP_TAC(SPECL [`m1:num`; `m2:num`] CLASSNO_GAUSS_CRT_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [SIMP_TAC[FINITE_PRODUCT; FINITE_NUMSEG]; FIRST_ASSUM ACCEPT_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  SIMP_TAC[VSUM_VSUM_PRODUCT; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ THEN ASM_REWRITE_TAC[FORALL_PAIR_THM; o_THM]);;

let CLASSNO_GAUSS_CEXP_ADD = prove
 (`!x y. cexp(ii * Cx(x + y)) = cexp(ii * Cx x) * cexp(ii * Cx y)`,
  REWRITE_TAC[GSYM CEXP_ADD; CX_ADD; COMPLEX_ADD_LDISTRIB]);;

let CLASSNO_GAUSS_CEXP_INTEGER = prove
 (`!x k. integer k
         ==> cexp(ii * Cx(&2 * pi * (x + k))) = cexp(ii * Cx(&2 * pi * x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `cexp(ii * Cx(&2 * pi * k)) = Cx(&1)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CLASSNO_GAUSS_CEXP_EQ_1]; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_ARITH `&2 * pi * (x + k) = &2 * pi * x + &2 * pi * k`;
                  CLASSNO_GAUSS_CEXP_ADD; COMPLEX_MUL_RID]);;

let CLASSNO_GAUSS_PROPERTY_MUL = prove
 (`!m1 m2 c c1 c2 g1 g2.
        coprime(m1,m2) /\ ~(m1 = 0) /\ ~(m2 = 0) /\
        dirichlet_character m1 c1 /\ dirichlet_character m2 c2 /\
        (!n. c n = c1 n * c2 n) /\
        (!n. vsum(0..m1-1)
               (\a. c1 a * cexp(ii * Cx(&2 * pi * &a * &n / &m1))) =
             c1 n * g1) /\
        (!n. vsum(0..m2-1)
               (\a. c2 a * cexp(ii * Cx(&2 * pi * &a * &n / &m2))) =
             c2 n * g2)
        ==> !n. vsum(0..m1 * m2 - 1)
                  (\a. c a * cexp(ii * Cx(&2 * pi * &a * &n / &(m1 * m2)))) =
                c n * (c1 m2 * c2 m1 * g1 * g2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `n:num` THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CLASSNO_GAUSS_CRT_VSUM o
    lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `a:num` THEN
    BINOP_TAC THENL
     [ASM_REWRITE_TAC[] THEN BINOP_TAC THENL
       [MP_TAC(ISPECL [`m1:num`; `c1:num->complex`; `m2:num`; `a:num`]
          DIRICHLET_CHARACTER_PERIODIC_GEN);
        MP_TAC(ISPECL [`m2:num`; `c2:num->complex`; `m1:num`; `a:num`]
          DIRICHLET_CHARACTER_PERIODIC_GEN)] THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      AP_TERM_TAC THEN ARITH_TAC;
      ONCE_REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
      SUBGOAL_THEN
       `&2 * pi * (&a + &(m1 * m2)) * &n / &(m1 * m2) =
        &2 * pi * (&a * &n / &(m1 * m2) + &n)`
      SUBST1_TAC THENL
       [UNDISCH_TAC `~(m1 = 0)` THEN UNDISCH_TAC `~(m2 = 0)` THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL] THEN
        CONV_TAC REAL_FIELD;
        SIMP_TAC[CLASSNO_GAUSS_CEXP_INTEGER; INTEGER_CLOSED] THEN
        AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[real_div] THEN REAL_ARITH_TAC]];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `!a1 a2. c(a1 * m2 + a2 * m1) *
            cexp(ii * Cx(&2 * pi * &(a1 * m2 + a2 * m1) * &n / &(m1 * m2))) =
            (c1 m2 * c1 a1 * cexp(ii * Cx(&2 * pi * &a1 * &n / &m1))) *
            (c2 m1 * c2 a2 * cexp(ii * Cx(&2 * pi * &a2 * &n / &m2)))`
   (fun th -> REWRITE_TAC[th])
  THENL
   [REPEAT GEN_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(c1:num->complex)(a1 * m2 + a2 * m1) = c1 m2 * c1 a1 /\
      (c2:num->complex)(a1 * m2 + a2 * m1) = c2 m1 * c2 a2`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THENL
       [MP_TAC(ONCE_REWRITE_RULE[ADD_SYM]
         (ISPECL [`m1:num`; `c1:num->complex`; `a2:num`; `a1 * m2`]
           DIRICHLET_CHARACTER_PERIODIC_GEN)) THEN
        MP_TAC(ISPECL [`m1:num`; `c1:num->complex`; `a1:num`; `m2:num`]
          DIRICHLET_CHARACTER_MUL);
        MP_TAC(ISPECL [`m2:num`; `c2:num->complex`; `a1:num`; `a2 * m1`]
          DIRICHLET_CHARACTER_PERIODIC_GEN) THEN
        MP_TAC(ISPECL [`m2:num`; `c2:num->complex`; `a2:num`; `m1:num`]
          DIRICHLET_CHARACTER_MUL)] THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[COMPLEX_MUL_SYM];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&2 * pi * &(a1 * m2 + a2 * m1) * &n / &(m1 * m2) =
      &2 * pi * &a1 * &n / &m1 + &2 * pi * &a2 * &n / &m2`
    SUBST1_TAC THENL
     [UNDISCH_TAC `~(m1 = 0)` THEN UNDISCH_TAC `~(m2 = 0)` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL;
                  GSYM REAL_OF_NUM_ADD] THEN
      CONV_TAC REAL_FIELD;
      REWRITE_TAC[CLASSNO_GAUSS_CEXP_ADD] THEN CONV_TAC COMPLEX_RING];
    ALL_TAC] THEN
  SIMP_TAC[VSUM_COMPLEX_LMUL; VSUM_COMPLEX_RMUL; FINITE_NUMSEG] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC COMPLEX_RING);;

(* ------------------------------------------------------------------------- *)
(* The Gauss sum property, part 2: real characters at n coprime to m, prime  *)
(* moduli, and the induction over squarefree odd moduli for a family of      *)
(* characters multiplicative in the modulus.                                 *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_GAUSS_CEXP_MOD = prove
 (`!m x. ~(m = 0)
         ==> cexp(ii * Cx(&2 * pi * &(x MOD m) * &1 / &m)) =
             cexp(ii * Cx(&2 * pi * &x * &1 / &m))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:num` o MATCH_MP DIVISION) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
    [CONJUNCT1 th]) THEN
  SUBGOAL_THEN
   `&2 * pi * &(x DIV m * m + x MOD m) * &1 / &m =
    &2 * pi * (&(x MOD m) * &1 / &m + &(x DIV m))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    UNDISCH_TAC `~(m = 0)` THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
    CONV_TAC REAL_FIELD;
    SIMP_TAC[CLASSNO_GAUSS_CEXP_INTEGER; INTEGER_CLOSED]]);;

let CLASSNO_GAUSS_CHAR_SQ = prove
 (`!m c n. dirichlet_character m c /\ (!k. cnj(c k) = c k) /\ coprime(n,m)
           ==> c n * c n = Cx(&1)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
   [GSYM(ASSUME `!k. cnj(c k) = (c:num->complex) k`)] THEN
  REWRITE_TAC[COMPLEX_MUL_CNJ] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_NORM th]) THEN
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC COMPLEX_RING);;

let CLASSNO_GAUSS_PROPERTY_COPRIME = prove
 (`!m c n. dirichlet_character m c /\ (!k. cnj(c k) = c k) /\ coprime(n,m) /\
           ~(m = 0)
           ==> vsum(0..m-1) (\a. c a * cexp(ii * Cx(&2 * pi * &a * &n / &m))) =
               c n * vsum(0..m-1)
                       (\a. c a * cexp(ii * Cx(&2 * pi * &a * &1 / &m)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\a. (c:num->complex) a * cexp(ii * Cx(&2 * pi * &a * &1 / &m))`;
    `\a. (a * n) MOD m`; `0..m-1`] VSUM_INJECTION) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_0] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(m = 0) ==> (x <= m - 1 <=> x < m)`;
                 MOD_LT_EQ] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[GSYM CONG] THEN STRIP_TAC THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `m:num` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x * n == y * n) (mod m)` THEN
    UNDISCH_TAC `coprime(n:num,m)` THEN CONV_TAC NUMBER_RULE;
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[o_DEF] THEN
  ASM_SIMP_TAC[CLASSNO_GAUSS_CEXP_MOD] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIRICHLET_CHARACTER_PERIODIC) THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[MATCH_MP CLASSNO_GAUSS_PERIODIC_MOD th]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_MUL th]) THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`m:num`; `c:num->complex`; `n:num`]
    CLASSNO_GAUSS_CHAR_SQ) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; REAL_MUL_RID; REAL_MUL_ASSOC] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC; REAL_MUL_RID] THEN
  CONV_TAC COMPLEX_RING);;

let CLASSNO_GAUSS_PROPERTY_PRIME = prove
 (`!p c. prime p /\ dirichlet_character p c /\ ~(c = chi_0 p) /\
         (!k. cnj(c k) = c k)
         ==> !n. vsum(0..p-1)
                   (\a. c a * cexp(ii * Cx(&2 * pi * &a * &n / &p))) =
                 c n * vsum(0..p-1)
                         (\a. c a * cexp(ii * Cx(&2 * pi * &a * &1 / &p)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 0) /\ ~(p = 1)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_0; PRIME_1]; ALL_TAC] THEN
  ASM_CASES_TAC `coprime(n,p)` THENL
   [ASM_SIMP_TAC[CLASSNO_GAUSS_PROPERTY_COPRIME]; ALL_TAC] THEN
  SUBGOAL_THEN `(c:num->complex) n = Cx(&0)` SUBST1_TAC THENL
   [FIRST_ASSUM(fun th ->
      REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_EQ_0 th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_MUL_LZERO] THEN
  SUBGOAL_THEN `p divides n` MP_TAC THENL
   [ASM_MESON_TAC[PRIME_COPRIME_EQ; COPRIME_SYM]; ALL_TAC] THEN
  REWRITE_TAC[divides] THEN DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
  SUBGOAL_THEN `!a. cexp(ii * Cx(&2 * pi * &a * &(p * k) / &p)) = Cx(&1)`
   (fun th -> REWRITE_TAC[th; COMPLEX_MUL_RID; ETA_AX])
  THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `&2 * pi * &a * &(p * k) / &p = &2 * pi * &(a * k)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN UNDISCH_TAC `~(p = 0)` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN CONV_TAC REAL_FIELD;
      REWRITE_TAC[CLASSNO_GAUSS_CEXP_EQ_1; INTEGER_CLOSED]];
    ALL_TAC] THEN
  SIMP_TAC[VSUM_CLAUSES_LEFT; LE_0; ADD_CLAUSES] THEN
  MP_TAC(ISPECL [`p:num`; `c:num->complex`] CLASSNO_GAUSS_CHAR_SUM_0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[COMPLEX_ADD_RID] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_EQ_0 th]) THEN
  ASM_REWRITE_TAC[COPRIME_0]);;

let CLASSNO_GAUSS_PROPERTY_SQUAREFREE = prove
 (`!chi:num->num->complex.
        (!m. ODD m ==> dirichlet_character m (chi m)) /\
        (!m n. ODD m ==> cnj(chi m n) = chi m n) /\
        (!p. prime p /\ ODD p ==> ~(chi p = chi_0 p)) /\
        (!m1 m2 n. ODD m1 /\ ODD m2 ==> chi (m1 * m2) n = chi m1 n * chi m2 n)
        ==> !m. ODD m /\ squarefree m
                ==> ?gs. !n. vsum(0..m-1)
                               (\a. chi m a *
                                    cexp(ii * Cx(&2 * pi * &a * &n / &m))) =
                             chi m n * gs`,
  GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `m = 1` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN EXISTS_TAC `Cx(&1)` THEN
    SUBGOAL_THEN `!n. (chi:num->num->complex) 1 n = Cx(&1)`
     (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC
       `!m. ODD m ==> dirichlet_character m ((chi:num->num->complex) m)` THEN
      DISCH_THEN(MP_TAC o SPEC `1`) THEN
      REWRITE_TAC[ARITH; DIRICHLET_CHARACTER_1];
      ALL_TAC] THEN
    REWRITE_TAC[SUB_REFL; VSUM_SING_NUMSEG; REAL_MUL_LZERO; REAL_MUL_RZERO;
                COMPLEX_MUL_RZERO; CEXP_0; COMPLEX_MUL_LID] THEN
    REWRITE_TAC[REAL_ARITH `&2 * pi * &0 * x = &0`; COMPLEX_MUL_RZERO;
                CEXP_0];
    ALL_TAC] THEN
  MP_TAC(SPEC `m:num` PRIME_FACTOR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC o
    REWRITE_RULE[divides]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ODD_MULT; SQUAREFREE_MUL]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `1 * k < p * k ==> k < p * k`) THEN
    REWRITE_TAC[LT_MULT_RCANCEL] THEN
    ASM_SIMP_TAC[SQUAREFREE_IMP_NZ; ARITH_RULE `2 <= p ==> 1 < p`;
                 PRIME_GE_2];
    DISCH_THEN(X_CHOOSE_TAC `g2:complex`)] THEN
  SUBGOAL_THEN
   `?g1. !n. vsum(0..p-1) (\a. (chi:num->num->complex) p a *
                                cexp(ii * Cx(&2 * pi * &a * &n / &p))) =
             chi p n * g1`
  (X_CHOOSE_TAC `g1:complex`) THENL
   [EXISTS_TAC `vsum(0..p-1) (\a. (chi:num->num->complex) p a *
                                  cexp(ii * Cx(&2 * pi * &a * &1 / &p)))` THEN
    MATCH_MP_TAC CLASSNO_GAUSS_PROPERTY_PRIME THEN ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  EXISTS_TAC `(chi:num->num->complex) p k * chi k p * g1 * g2` THEN
  MATCH_MP_TAC CLASSNO_GAUSS_PROPERTY_MUL THEN
  ASM_SIMP_TAC[PRIME_IMP_NZ; SQUAREFREE_IMP_NZ; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* The class number formulas in absolute value for any family chi of real    *)
(* characters with the three structural properties (the last section         *)
(* instantiates chi with qchar, using Library/jacobi.ml).                    *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_GAUSS_PROPERTY_NONPRINCIPAL = prove
 (`!m c gs.
        dirichlet_character m c /\ 2 <= m /\
        (!n. vsum(0..m-1) (\a. c a * cexp(ii * Cx(&2 * pi * &a * &n / &m))) =
             c n * gs)
        ==> ~(c = chi_0 m)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `0`)) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; real_div; COMPLEX_MUL_RZERO;
              CEXP_0; COMPLEX_MUL_RID] THEN
  REWRITE_TAC[chi_0; COPRIME_0] THEN
  ASM_SIMP_TAC[ARITH_RULE `2 <= m ==> ~(m = 1)`; COMPLEX_MUL_LZERO] THEN
  REWRITE_TAC[COND_RAND; COND_RATOR] THEN
  ONCE_REWRITE_TAC[MESON[CX_INJ]
   `(if p then Cx(&1) else Cx(&0)) = Cx(if p then &1 else &0)`] THEN
  REWRITE_TAC[VSUM_CX; CX_INJ] THEN
  MATCH_MP_TAC(REAL_ARITH `&1 <= (x:real) ==> ~(x = &0)`) THEN
  MP_TAC(ISPECL [`\a. if coprime(a,m) then &1 else &0`; `0..m-1`; `1`]
    SUM_DELETE) THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; COPRIME_1] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= (y:real) ==> y = x - &1 ==> &1 <= x`) THEN
  MATCH_MP_TAC SUM_POS_LE THEN SIMP_TAC[FINITE_DELETE; FINITE_NUMSEG] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC);;

let CLASSNO_GAUSS_PROPERTY_REAL = prove
 (`!chi:num->num->real.
        (!m. ODD m ==> dirichlet_character m (\n. Cx(chi m n))) /\
        (!p. prime p /\ ODD p ==> ~((\n. Cx(chi p n)) = chi_0 p)) /\
        (!m1 m2 n. ODD m1 /\ ODD m2 ==> chi (m1 * m2) n = chi m1 n * chi m2 n)
        ==> !m. ODD m /\ squarefree m
                ==> ?gs. !n. vsum(0..m-1)
                               (\a. Cx(chi m a) *
                                    cexp(ii * Cx(&2 * pi * &a * &n / &m))) =
                             Cx(chi m n) * gs`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `\m n. Cx((chi:num->num->real) m n)`
    CLASSNO_GAUSS_PROPERTY_SQUAREFREE) THEN
  REWRITE_TAC[CNJ_CX; GSYM CX_MUL; CX_INJ] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;

let CLASSNO_GAUSS_L1_ODD_GEN = prove
 (`!chi:num->num->real.
        (!m. ODD m ==> dirichlet_character m (\n. Cx(chi m n))) /\
        (!p. prime p /\ ODD p ==> ~((\n. Cx(chi p n)) = chi_0 p)) /\
        (!m1 m2 n. ODD m1 /\ ODD m2 ==> chi (m1 * m2) n = chi m1 n * chi m2 n)
        ==> !q. squarefree q /\ ODD q /\ chi q (q - 1) = -- &1
                ==> norm(Lfunction (\n. Cx(chi q n))) =
                    pi * abs(sum(1..(q - 1) DIV 2) (\a. chi q a)) /
                    ((&2 - chi q 2) * sqrt(&q))`,
  GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `q:num` o
    MATCH_MP CLASSNO_GAUSS_PROPERTY_REAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `gs:complex`) THEN
  REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC LFUNCTION_GAUSS_ODD_NORM THEN
  EXISTS_TAC `gs:complex` THEN ASM_SIMP_TAC[]);;

let CLASSNO_GAUSS_L1_EVEN_GEN = prove
 (`!chi:num->num->real.
        (!m. ODD m ==> dirichlet_character m (\n. Cx(chi m n))) /\
        (!p. prime p /\ ODD p ==> ~((\n. Cx(chi p n)) = chi_0 p)) /\
        (!m1 m2 n. ODD m1 /\ ODD m2 ==> chi (m1 * m2) n = chi m1 n * chi m2 n)
        ==> !q. squarefree q /\ ODD q /\ 1 < q /\ chi q (q - 1) = &1
                ==> norm(Lfunction (\n. Cx(chi q n))) =
                    abs(sum(1..q - 1) (\a. chi q a * log(sin(pi * &a / &q)))) /
                    sqrt(&q)`,
  GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `q:num` o
    MATCH_MP CLASSNO_GAUSS_PROPERTY_REAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `gs:complex`) THEN
  MATCH_MP_TAC LFUNCTION_GAUSS_EVEN_NORM THEN
  EXISTS_TAC `gs:complex` THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC CLASSNO_GAUSS_PROPERTY_NONPRINCIPAL THEN
  EXISTS_TAC `gs:complex` THEN ASM_SIMP_TAC[] THEN
  UNDISCH_TAC `1 < q` THEN ARITH_TAC);;

let CLASSNO_GAUSS_ODD_MOD4 = prove
 (`!q. q MOD 4 = 1 \/ q MOD 4 = 3 ==> ODD q`,
  GEN_TAC THEN MP_TAC(SPECL [`q:num`; `4`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
    [CONJUNCT1 th]) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH]);;

(* ------------------------------------------------------------------------- *)
(* The main results: the real characters qchar q = jacobi(., q)              *)
(* (Library/jacobi.ml) are a family as in CLASSNO_GAUSS_L1_ODD_GEN,          *)
(* CLASSNO_GAUSS_L1_EVEN_GEN: Dirichlet characters (QCHAR_DIRICHLET),        *)
(* nonprincipal for odd primes (a quadratic nonresidue), multiplicative in   *)
(* the modulus, with qchar q (q - 1) = (-1)^((q - 1)/2).                     *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_GAUSS_QCHAR_NONPRINCIPAL = prove
 (`!p. prime p /\ ODD p ==> ~((\n. Cx(qchar p n)) = chi_0 p)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `3 <= p` MP_TAC THENL
   [MP_TAC(SPEC `p:num` PRIME_GE_2) THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `p = 2` THENL
     [UNDISCH_TAC `ODD p` THEN ASM_REWRITE_TAC[ARITH]; ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM QUADRATIC_NONRESIDUE_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o C AP_THM `a:num`) THEN
  REWRITE_TAC[chi_0] THEN ONCE_REWRITE_TAC[COPRIME_SYM] THEN
  ASM_REWRITE_TAC[qchar; CX_INJ] THEN
  MP_TAC(SPECL [`a:num`; `p:num`] JACOBI_PRIME) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~((p:num) divides a)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[PRIME_COPRIME_EQ]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[int_neg_th; int_of_num_th] THEN
  REAL_ARITH_TAC);;

(* The Gauss sum property of qchar m for odd squarefree m, and qchar m is    *)
(* nonprincipal for odd squarefree m > 1 (the Gauss sum vanishes at n = 0    *)
(* for a principal character).                                               *)

let QCHAR_GAUSS_PROPERTY = prove
 (`!m. ODD m /\ squarefree m
       ==> ?gs. !n. vsum(0..m-1)
                      (\a. Cx(qchar m a) *
                           cexp(ii * Cx(&2 * pi * &a * &n / &m))) =
                    Cx(qchar m n) * gs`,
  MATCH_MP_TAC CLASSNO_GAUSS_PROPERTY_REAL THEN
  SIMP_TAC[QCHAR_DIRICHLET; CLASSNO_GAUSS_QCHAR_NONPRINCIPAL;
           CLASSNO_SERIES_QCHAR_RMUL]);;

let QCHAR_NONPRINCIPAL = prove
 (`!m. squarefree m /\ ODD m /\ 1 < m ==> ~((\n. Cx(qchar m n)) = chi_0 m)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `m:num` QCHAR_GAUSS_PROPERTY) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `gs:complex`) THEN
  MATCH_MP_TAC CLASSNO_GAUSS_PROPERTY_NONPRINCIPAL THEN
  EXISTS_TAC `gs:complex` THEN ASM_SIMP_TAC[QCHAR_DIRICHLET] THEN
  ASM_ARITH_TAC);;

let CLASSNO_GAUSS_QCHAR_MINUS1 = prove
 (`!q. ODD q ==> qchar q (q - 1) = if q MOD 4 = 1 then &1 else -- &1`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[qchar; JACOBI_MINUS1_CASES] THEN
  REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV THEN
  COND_CASES_TAC THEN REWRITE_TAC[int_neg_th; int_of_num_th]);;

let CLASSNO_L1_ODD = prove
 (`!q. squarefree q /\ q MOD 4 = 3
      ==> norm(Lfunction (\n. Cx(qchar q n))) =
          pi * abs(sum(1..(q - 1) DIV 2) (\a. qchar q a)) /
          ((&2 - qchar q 2) * sqrt(&q))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `qchar` CLASSNO_GAUSS_L1_ODD_GEN) THEN
  ANTS_TAC THENL
   [SIMP_TAC[QCHAR_DIRICHLET; CLASSNO_GAUSS_QCHAR_NONPRINCIPAL;
             CLASSNO_SERIES_QCHAR_RMUL];
    DISCH_THEN MATCH_MP_TAC] THEN
  SUBGOAL_THEN `ODD q` ASSUME_TAC THENL
   [MATCH_MP_TAC CLASSNO_GAUSS_ODD_MOD4 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[CLASSNO_GAUSS_QCHAR_MINUS1] THEN CONV_TAC NUM_REDUCE_CONV);;

let CLASSNO_L1_EVEN = prove
 (`!q. squarefree q /\ q MOD 4 = 1 /\ 1 < q
      ==> norm(Lfunction (\n. Cx(qchar q n))) =
          abs(sum(1..q - 1) (\a. qchar q a * log(sin(pi * &a / &q)))) /
          sqrt(&q)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `qchar` CLASSNO_GAUSS_L1_EVEN_GEN) THEN
  ANTS_TAC THENL
   [SIMP_TAC[QCHAR_DIRICHLET; CLASSNO_GAUSS_QCHAR_NONPRINCIPAL;
             CLASSNO_SERIES_QCHAR_RMUL];
    DISCH_THEN MATCH_MP_TAC] THEN
  SUBGOAL_THEN `ODD q` ASSUME_TAC THENL
   [MATCH_MP_TAC CLASSNO_GAUSS_ODD_MOD4 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[CLASSNO_GAUSS_QCHAR_MINUS1]);;
