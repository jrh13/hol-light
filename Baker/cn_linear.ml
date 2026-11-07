(* ========================================================================= *)
(* The three linear forms in logarithms of the class number two problem.     *)
(*                                                                           *)
(* Purpose: for D = -d, d = p q with primes p = 1, q = 3 mod 4, d = 3 mod 8, *)
(* coprime to 21 and form_classno(-d) = 2, there are nonzero integers b1, b2 *)
(* with |b1| <= 2 sqrt(21 d) (log(21 d) + 3), |b2| <= sqrt(21 q) (log(21 q)  *)
(* + 3) and |b1 log eps + b2 log xi - (128/7) pi sqrt d| <= 504 g(eta), eps  *)
(* = (5 + sqrt 21)/2, xi = cyclo_unit(21 p), eta = exp(-pi sqrt(d)/21), g =  *)
(* qform_kernel (CN_LINEAR_MAIN; Baker, Transcendental Number Theory, Ch. 5, *)
(* sec. 5); and, for any k = k1 k2 (two distinct primes, k = 1 mod 4)        *)
(* coprime to d, the forms in the two logarithms log(cyclo_unit k) and i pi  *)
(* with the coefficient a rational multiple of sqrt d: for the two classes   *)
(* of discriminant -d with small q (CN_LINEAR_SMALL) and for the             *)
(* discriminant -4d, d prime = 1 mod 4 or d = 2 p (CN_LINEAR_EVEN).          *)
(*                                                                           *)
(* Method: the product limits (CN_GENUS_PRODUCT_LIMIT,                       *)
(* CN_TOTAL_PRODUCT_LIMIT, CN_TOTAL_PRODUCT_LIMIT_EVEN) write the products   *)
(* of the L-values L(1,chi) as zeta_k(2) times an Euler factor plus slice    *)
(* sums S of forms (a, b, c), |S| <= (4 pi / sqrt|D|) g(eta_a), eta_a =      *)
(* exp(-pi sqrt|D| / (a k)) (CLASSNO_SLICE_BOUND, QFORM_SLICE_BOUND). Only   *)
(* the absolute values of the L-values are known:                            *)
(* |L(1,chi_21)| = (2 log eps) / sqrt 21 (CLASSNO_L1_REAL); pi T / ((2 -     *)
(* chi_m(2)) sqrt m) for m = 3 mod 4 (CLASSNO_L1_ODD; T is an integer, T >=  *)
(* 1 since L(1,chi) is not 0); |log(cyclo_unit m)| / sqrt m for m = 1 mod 4  *)
(* (CLASSNO_L1_EVEN); pi |t| / (2 sqrt(k d)) for chi_k kchar4 d              *)
(* (CN_L1_KCHAR4). The signs go into the integer coefficients. In the genus  *)
(* identity L(chi_21) L(chi_21d) + L(chi_21p) L(chi_21q) = 2 (zeta_21(2) +   *)
(* S) the L-values of chi_21, chi_21d are real, so both products are real.   *)
(* Multiplication by 63 sqrt(d) / pi (resp. u q k sqrt(d) / pi with u = 2 -  *)
(* chi_kd(2), and 4 k sqrt(d) / pi) and zeta_k(2) = (k1^2 - 1) (k2^2 - 1) /  *)
(* k^2 pi^2 / 6 (CLASSNO_LINEAR_ZETA_PRIME_MUL, CN_ZETA_2) give the main     *)
(* terms; |L(1,chi)| <= log m + 3 (CN_L1_BOUND) gives the coefficient        *)
(* bounds. The characters chi_k kchar4 d are nonprincipal Dirichlet          *)
(* characters modulo 4 k d (CNP_EVEN_FACTS).                                 *)
(*                                                                           *)
(* Main results: CN_LINEAR_MAIN, CN_LINEAR_SMALL, CN_LINEAR_EVEN;            *)
(* CN_LINEAR_L1_ODD, CN_LINEAR_L1_EVEN, CN_LINEAR_ZETA_MUL, CN_LINEAR_SLICE; *)
(* helper names CN_LINEAR_*.                                                 *)
(*                                                                           *)
(* Uses: Baker/cn_defs.ml (cyclo_unit, kchar4), Baker/qform_limit.ml         *)
(* (QFORM_SLICE_BOUND), Baker/cn_products.ml (CN_GENUS_PRODUCT_LIMIT,        *)
(* CN_TOTAL_PRODUCT_LIMIT, CN_TOTAL_PRODUCT_LIMIT_EVEN, CNP_EVEN_FACTS,      *)
(* CNP_MOD4_EVEN), Baker/cn_cyclo.ml (CN_L1_BOUND), Baker/cn_gauss_even.ml   *)
(* (CN_L1_KCHAR4), Baker/cn_zeta.ml (CN_ZETA_2);                             *)
(* Baker/classno_chardefs.ml (qchar, zeta_coprime, qform_slice,              *)
(* qform_kernel), Baker/classno_series.ml (QCHAR_DIRICHLET,                  *)
(* CLASSNO_SERIES_LFUNCTION_REAL, CLASSNO_SERIES_C0),                        *)
(* Baker/classno_product.ml (CLASSNO_SLICE_BOUND), Baker/classno_limit.ml    *)
(* (CLASSNO_LIMIT_PRIMES), Baker/classno_gauss.ml (QCHAR_NONPRINCIPAL,       *)
(* CLASSNO_L1_ODD, CLASSNO_L1_EVEN, CLASSNO_GAUSS_ODD_NONPRINCIPAL,          *)
(* CLASSNO_GAUSS_QCHAR_MINUS1, CLASSNO_GAUSS_ODD_MOD4),                      *)
(* Baker/classno_cyclo.ml (CLASSNO_L1_REAL, CLASSNO_CYCLO_SQUAREFREE,        *)
(* CLASSNO_CYCLO_LOG_POS), Baker/classno_linear.ml                           *)
(* (CLASSNO_LINEAR_ZETA_PRIME_MUL, CLASSNO_LINEAR_ZETA_21_33,                *)
(* CLASSNO_LINEAR_QCHAR_2, CLASSNO_LINEAR_MOD_8_4); 100/dirichlet.ml         *)
(* (dirichlet_character, chi_0, LFUNCTION_NONZERO_NONPRINCIPAL),             *)
(* Library/prime.ml (DISTINCT_PRIME_COPRIME), Library/jacobi.ml              *)
(* (JACOBI_CASES, JACOBI_EQ_0),                                              *)
(* Library/floor.ml (REAL_ABS_INTEGER_LEMMA).                                *)
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
needs "Baker/cn_cyclo.ml";;
needs "Baker/cn_zeta.ml";;
needs "Baker/cn_products.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* 1. The class number formulas in the form used here: odd characters of     *)
(*    modulus m = 3 mod 4 (an integer T >= 1, u = 2 - chi(2) = 1 or 3, the   *)
(*    bound log m + 3, the L-value is real) and even characters of modulus   *)
(*    m = 1 mod 4 (the cyclotomic unit).                                     *)
(* ------------------------------------------------------------------------- *)

let CN_LINEAR_QCHAR_2_CASES = prove
 (`!m. ODD m ==> qchar m 2 = &1 \/ qchar m 2 = -- &1`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[qchar] THEN
  MP_TAC(SPECL [`2`; `m:num`] JACOBI_EQ_0) THEN
  ASM_REWRITE_TAC[COPRIME_2] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`2`; `m:num`] JACOBI_CASES) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[int_neg_th; int_of_num_th]);;

let CN_LINEAR_L1_ODD = prove
 (`!m. squarefree m /\ m MOD 4 = 3
       ==> ?t u. integer t /\ &1 <= t /\ (u = &1 \/ u = &3) /\
                 qchar m 2 = &2 - u /\
                 Lfunction (\n. Cx(qchar m n)) =
                 Cx(Re(Lfunction (\n. Cx(qchar m n)))) /\
                 norm(Lfunction (\n. Cx(qchar m n))) =
                 pi * t / (u * sqrt(&m)) /\
                 pi * t / (u * sqrt(&m)) <= log(&m) + &3`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ODD m` ASSUME_TAC THENL
   [MATCH_MP_TAC CLASSNO_GAUSS_ODD_MOD4 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `dirichlet_character m (\n. Cx(qchar m n))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[QCHAR_DIRICHLET]; ALL_TAC] THEN
  SUBGOAL_THEN `~((\n. Cx(qchar m n)) = chi_0 m)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLASSNO_GAUSS_ODD_NONPRINCIPAL THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[CLASSNO_GAUSS_QCHAR_MINUS1] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[CX_NEG];
    ALL_TAC] THEN
  MP_TAC(SPEC `m:num` CLASSNO_L1_ODD) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  EXISTS_TAC `abs(sum(1..(m - 1) DIV 2) (\a. qchar m a))` THEN
  EXISTS_TAC `&2 - qchar m 2` THEN
  SUBGOAL_THEN `integer(sum(1..(m - 1) DIV 2) (\a. qchar m a))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGER_SUM THEN REWRITE_TAC[qchar; INTEGER_REAL_OF_INT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[INTEGER_ABS; REAL_ARITH `x:real = &2 - (&2 - x)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`m:num`; `\n. Cx(qchar m n)`]
      LFUNCTION_NONZERO_NONPRINCIPAL) THEN
    ASM_REWRITE_TAC[GSYM COMPLEX_NORM_ZERO; REAL_ABS_0; REAL_MUL_RZERO;
                    real_div; REAL_MUL_LZERO];
    MP_TAC(SPEC `m:num` CN_LINEAR_QCHAR_2_CASES) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC CLASSNO_SERIES_LFUNCTION_REAL THEN EXISTS_TAC `m:num` THEN
    ASM_REWRITE_TAC[REAL_CX];
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC CN_L1_BOUND THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `ODD m` THEN
    REWRITE_TAC[ODD_EXISTS] THEN ARITH_TAC]);;

let CN_LINEAR_L1_EVEN = prove
 (`!m. squarefree m /\ m MOD 4 = 1 /\ 1 < m
       ==> norm(Lfunction (\n. Cx(qchar m n))) =
           abs(log(cyclo_unit m)) / sqrt(&m)`,
  SIMP_TAC[cyclo_unit; LOG_EXP; REAL_ABS_NEG; CLASSNO_L1_EVEN]);;

(* ------------------------------------------------------------------------- *)
(* 2. zeta_k(2) for k = k1 k2, the slice bound with a numeral discriminant.  *)
(* ------------------------------------------------------------------------- *)

let CN_LINEAR_ZETA_MUL = prove
 (`!k k1 k2. k = k1 * k2 /\ prime k1 /\ prime k2 /\ ~(k1 = k2)
             ==> zeta_coprime k =
                 &((k1 EXP 2 - 1) * (k2 EXP 2 - 1)) / &k pow 2 *
                 pi pow 2 / &6`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k1:num`; `k2:num`] CLASSNO_LINEAR_ZETA_PRIME_MUL) THEN
  MP_TAC(SPECL [`k2:num`; `1`] CLASSNO_LINEAR_ZETA_PRIME_MUL) THEN
  ASM_SIMP_TAC[DISTINCT_PRIME_COPRIME; COPRIME_1; MULT_CLAUSES; CN_ZETA_2] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `~(k1 = 0) /\ ~(k2 = 0)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `1 <= k1 EXP 2 /\ 1 <= k2 EXP 2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_SUB;
               GSYM REAL_OF_NUM_POW] THEN
  SUBGOAL_THEN `~(&k1 = &0) /\ ~(&k2 = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_EQ]; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

let CN_LINEAR_SLICE = prove
 (`!k k1 k2 a b c D S.
     k = k1 * k2 /\ prime k1 /\ prime k2 /\ ~(k1 = k2) /\ ODD k /\
     0 < a /\ 0 < D /\ &4 * &a * c - b pow 2 = &D /\
     coprime(k,a) /\ coprime(k,D) /\
     (qform_slice k (&a) b c (&1) real_sums S) (from 1)
     ==> abs S <= &4 * pi / sqrt(&D) *
                  qform_kernel(exp(--(pi * sqrt(&D) / (&a * &k))))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  MP_TAC(SPECL [`k1 * k2`; `k1:num`; `k2:num`; `&a:int`; `b:int`; `c:int`;
                `S:real`] QFORM_SLICE_BOUND) THEN
  ASM_REWRITE_TAC[NUM_OF_INT_OF_NUM; int_of_num_th; INT_OF_NUM_LT]);;

(* ------------------------------------------------------------------------- *)
(* 3. The arithmetic cores: signs, coefficient bounds, main terms, errors.   *)
(* ------------------------------------------------------------------------- *)

(* Only absolute values of the L-values are known: the sign of a real number *)
(* with given absolute value.                                                *)

let CN_LINEAR_SIGN = prove
 (`!x y. abs x = abs y ==> ?e. (e = &1 \/ e = -- &1) /\ x = e * y`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x:real = y` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_MUL_LID];
    EXISTS_TAC `-- &1` THEN REWRITE_TAC[] THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC]);;

(* The coefficient bounds: from n = pp t / w <= B (a class number formula    *)
(* and CN_L1_BOUND) and c <= pp, c t <= w B.                                 *)

let CN_LINEAR_COEFF_BOUND = prove
 (`!pp t w c n B. &0 < w /\ &0 <= t /\ c <= pp /\ n = pp * t / w /\ n <= B
                  ==> c * t <= w * B`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `pp * t:real` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `pp * t = n * w:real` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < w` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC(REAL_ARITH `n * w <= B * w ==> n * w <= w * B:real`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]]);;

(* The arithmetic core of CN_LINEAR_MAIN. Here pp = pi, s = sqrt d, s21,     *)
(* s21d, s21p, s21q the square roots of 21, 21 d, 21 p, 21 q, l1 = log eps,  *)
(* lx = log xi, n1, n2, n3, n4 the norms of the L-values of chi_21, chi_21d, *)
(* chi_21p, chi_21q, t1, t2 the character sums, u1, u2 the factors 2 -       *)
(* chi(2), x, y the two (real) products of the genus identity, S the slice   *)
(* sum, g = qform_kernel(eta) and B1, B2 the bounds log m + 3.               *)

let CN_LINEAR_MAIN_ARITH = prove
 (`!pp s s21 s21d s21p s21q l1 lx t1 t2 u1 u2 n1 n2 n3 n4 S g x y B1 B2.
     &3 <= pp /\ &0 < s /\ &0 < s21 /\ &0 < s21d /\ &0 < s21p /\ &0 < s21q /\
     s21 * s21d = &21 * s /\ s21p * s21q = &21 * s /\ &0 < l1 /\
     integer t1 /\ &1 <= t1 /\ integer t2 /\ &1 <= t2 /\
     u1 = &1 /\ (u2 = &1 \/ u2 = &3) /\
     abs S <= &4 * pp / s * g /\
     x + y = &2 * (&384 / &441 * pp pow 2 / &6 + S) /\
     n1 = &2 * l1 / s21 /\ n2 = pp * t1 / (u1 * s21d) /\
     n3 = abs lx / s21p /\ n4 = pp * t2 / (u2 * s21q) /\
     abs x = n1 * n2 /\ abs y = n3 * n4 /\ n2 <= B1 /\ n4 <= B2
     ==> ?b1 b2. integer b1 /\ integer b2 /\ ~(b1 = &0) /\ ~(b2 = &0) /\
                 abs b1 <= &2 * s21d * B1 /\ abs b2 <= s21q * B2 /\
                 abs(b1 * l1 + b2 * lx - &128 / &7 * pp * s) <= &504 * g`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < pp /\ &0 < u2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&3 <= pp`; `u2 = &1 \/ u2 = &3`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(&63 * s / pp * x) = abs(&6 * t1 * l1)` MP_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_NUM] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`;
                 REAL_ARITH `&1 <= x ==> abs x = x`] THEN
    MAP_EVERY UNDISCH_TAC
     [`s21 * s21d = &21 * s`; `&0 < s`; `&0 < pp`; `&0 < s21`; `&0 < s21d`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN ASSUME_TAC) o
    MATCH_MP CN_LINEAR_SIGN) THEN
  SUBGOAL_THEN `abs(&63 * s / pp * y) = abs(&3 * t2 / u2 * lx)` MP_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_NUM] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`;
                 REAL_ARITH `&1 <= x ==> abs x = x`] THEN
    MAP_EVERY UNDISCH_TAC
     [`s21p * s21q = &21 * s`; `&0 < s`; `&0 < pp`; `&0 < s21p`; `&0 < s21q`;
      `&0 < u2`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN ASSUME_TAC) o
    MATCH_MP CN_LINEAR_SIGN) THEN
  EXISTS_TAC `e1 * &6 * t1` THEN EXISTS_TAC `e2 * &3 * t2 / u2` THEN
  SUBGOAL_THEN `integer e1 /\ integer e2 /\ abs e1 = &1 /\ abs e2 = &1`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`e1 = &1 \/ e1 = -- &1`; `e2 = &1 \/ e2 = -- &1`] THEN
    REPEAT(DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC)) THEN
    REWRITE_TAC[INTEGER_NEG; INTEGER_CLOSED; REAL_ABS_NEG; REAL_ABS_NUM];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t2 / u2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN
    MAP_EVERY UNDISCH_TAC [`&1 <= t2`; `&0 < u2`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 * t2 / u2 <= pp * t2 / u2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `integer(&3 * t2 / u2)` ASSUME_TAC THENL
   [UNDISCH_TAC `u2 = &1 \/ u2 = &3` THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    SIMP_TAC[REAL_DIV_1; REAL_DIV_LMUL; REAL_ARITH `~(&3 = &0)`] THEN
    ASM_SIMP_TAC[INTEGER_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 * t1 <= (pp:real) * t1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN
    MAP_EVERY UNDISCH_TAC [`&1 <= t1`; `&3 <= pp`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(pp:real) * t1 <= s21d * B1` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `!n. a = n * s /\ n * s <= b * s ==> (a:real) <= s * b`) THEN
    EXISTS_TAC `n2:real` THEN CONJ_TAC THENL
     [UNDISCH_TAC `n2 = pp * t1 / (u1 * s21d)` THEN
      UNDISCH_TAC `u1 = &1` THEN UNDISCH_TAC `&0 < s21d` THEN
      CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(pp:real) * t2 / u2 <= s21q * B2` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `!n. a = n * s /\ n * s <= b * s ==> (a:real) <= s * b`) THEN
    EXISTS_TAC `n4:real` THEN CONJ_TAC THENL
     [UNDISCH_TAC `n4 = pp * t2 / (u2 * s21q)` THEN
      UNDISCH_TAC `&0 < u2` THEN UNDISCH_TAC `&0 < s21q` THEN
      CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(e1 * &6 * t1) * l1 + (e2 * &3 * t2 / u2) * lx - &128 / &7 * pp * s =
    &126 * s / pp * S`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `!c x y. a * l1 = c * x /\ b * lx = c * y /\ c * (x + y) - m = r
              ==> a * l1 + b * lx - m = (r:real)`) THEN
    MAP_EVERY EXISTS_TAC [`&63 * s / pp`; `x:real`; `y:real`] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `&63 * s / pp * x = e1 * &6 * t1 * l1` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `&63 * s / pp * y = e2 * &3 * t2 / u2 * lx` THEN
      REAL_ARITH_TAC;
      UNDISCH_TAC `x + y = &2 * (&384 / &441 * pp pow 2 / &6 + S)` THEN
      DISCH_THEN SUBST1_TAC THEN UNDISCH_TAC `&0 < pp` THEN
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `s / pp * abs S <= &4 * g` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `s / pp * (&4 * pp / s * g)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      UNDISCH_TAC `&0 < s` THEN UNDISCH_TAC `&0 < pp` THEN
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGER_CLOSED; REAL_ENTIRE; REAL_ABS_MUL; REAL_ABS_DIV;
               REAL_ABS_NUM; REAL_ARITH `&0 < x ==> abs x = x`;
               REAL_ARITH `&1 <= x ==> abs x = x`] THEN
  REPEAT CONJ_TAC THEN
  MAP_EVERY UNDISCH_TAC
   [`abs e1 = &1`; `abs e2 = &1`; `&1 <= t1`; `&0 < t2 / u2`;
    `&3 * t1 <= (pp:real) * t1`; `(pp:real) * t1 <= s21d * B1`;
    `&3 * t2 / u2 <= pp * t2 / u2`; `(pp:real) * t2 / u2 <= s21q * B2`;
    `s / pp * abs S <= &4 * g`] THEN
  REAL_ARITH_TAC);;

(* The arithmetic core of CN_LINEAR_SMALL and CN_LINEAR_EVEN: pp = pi, s =   *)
(* sqrt d, sk = sqrt k, skd = sqrt(k d), lx = log(cyclo_unit k), A = L(1,    *)
(* chi_k) L(1, chi) = zeta_k(2) (1 + chi_k(qq)/qq) + S1 + S2 with M = (k1^2  *)
(* - 1) (k2^2 - 1), kk = k, the norm pp t / (w skd) of L(1, chi) (t >= 1 an  *)
(* integer, 0 < w <= pp) and the slice bounds (c0 pi / sqrt d) g; then b =   *)
(* +-qq t and the multiplier w qq kk s / pp.                                 *)

let CN_LINEAR_LOG_ARITH = prove
 (`!pp s sk skd lx t w qq kk M chi S1 S2 g1 g2 c0 n1 n2 A B.
     &0 < pp /\ &0 < s /\ &0 < sk /\ &0 < skd /\ sk * skd = kk * s /\
     &1 <= qq /\ integer qq /\ &1 <= kk /\ &0 < w /\ w <= pp /\
     integer t /\ &1 <= t /\
     abs S1 <= c0 * pp / s * g1 /\ abs S2 <= c0 * pp / s * g2 /\
     A = M / kk pow 2 * pp pow 2 / &6 * (&1 + chi / qq) + S1 + S2 /\
     n1 = abs lx / sk /\ n2 = pp * t / (w * skd) /\ abs A = n1 * n2 /\
     n2 <= B
     ==> ?b. integer b /\ ~(b = &0) /\ abs b <= qq * skd * B /\
             abs(b * lx - w * (qq + chi) * M / (&6 * kk) * pp * s) <=
             c0 * w * qq * kk * (g1 + g2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `abs(w * qq * kk * s / pp * A) = abs(qq * t * lx)` MP_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`;
                 REAL_ARITH `&1 <= x ==> abs x = x`] THEN
    MAP_EVERY UNDISCH_TAC
     [`(sk:real) * skd = kk * s`; `&0 < s`; `&0 < pp`; `&0 < sk`; `&0 < skd`;
      `&0 < w`; `&1 <= kk`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN ASSUME_TAC) o
    MATCH_MP CN_LINEAR_SIGN) THEN
  EXISTS_TAC `e * qq * t:real` THEN
  SUBGOAL_THEN `integer e /\ abs e = &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `e = &1 \/ e = -- &1` THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[INTEGER_NEG; INTEGER_CLOSED; REAL_ABS_NEG; REAL_ABS_NUM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t:real) <= skd * B` ASSUME_TAC THENL
   [MP_TAC(SPECL [`pp:real`; `t:real`; `w * skd:real`; `w:real`; `n2:real`;
                  `B:real`] CN_LINEAR_COEFF_BOUND) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_MUL] THEN UNDISCH_TAC `&1 <= t` THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_SIMP_TAC[REAL_LE_LMUL_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(e * qq * t) * lx - w * (qq + chi) * M / (&6 * kk) * pp * s =
    w * qq * kk * s / pp * (S1 + S2)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `!c. b = c * A /\ c * A - m = r ==> b - m = (r:real)`) THEN
    EXISTS_TAC `w * qq * kk * s / pp` THEN CONJ_TAC THENL
     [UNDISCH_TAC `w * qq * kk * s / pp * A = e * qq * t * lx` THEN
      REAL_ARITH_TAC;
      UNDISCH_TAC
       `A = M / kk pow 2 * pp pow 2 / &6 * (&1 + chi / qq) + S1 + S2` THEN
      DISCH_THEN SUBST1_TAC THEN
      MAP_EVERY UNDISCH_TAC [`&0 < pp`; `&1 <= qq`; `&1 <= kk`] THEN
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `s / pp * abs(S1 + S2) <= c0 * (g1 + g2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `s / pp * (c0 * pp / s * g1 + c0 * pp / s * g2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(S1:real) + abs S2` THEN
        REWRITE_TAC[REAL_ABS_TRIANGLE] THEN
        MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      UNDISCH_TAC `&0 < s` THEN UNDISCH_TAC `&0 < pp` THEN
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= w * qq * kk` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    MAP_EVERY UNDISCH_TAC [`&0 < w`; `&1 <= qq`; `&1 <= kk`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[INTEGER_CLOSED];
    REWRITE_TAC[REAL_ENTIRE] THEN
    MAP_EVERY UNDISCH_TAC [`abs e = &1`; `&1 <= qq`; `&1 <= t`] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&1 <= x ==> abs x = x`; REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&1 <= qq` THEN REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`;
                 REAL_ARITH `&1 <= x ==> abs x = x`] THEN
    MP_TAC(SPECL [`w * qq * kk:real`; `s / pp * abs(S1 + S2)`;
                  `c0 * (g1 + g2):real`] REAL_LE_LMUL) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 4. The linear forms.                                                      *)
(* ------------------------------------------------------------------------- *)

(* The main case, k = 21: the genus identity, chi_21d(2) = 1 for             *)
(* d = 3 mod 8, zeta_21(2) = (384/441) pi^2/6, and 63 sqrt(d)/pi times the   *)
(* identity: b1 = +-6 T(21d), b2 = +-3 T(21q)/(2 - chi_21q(2)).              *)

let CN_LINEAR_MAIN = prove
 (`!p q. prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3 /\
         (p * q) MOD 8 = 3 /\ coprime(21,p * q) /\
         form_classno (--(&(p * q))) = 2
         ==> ?b1 b2. integer b1 /\ integer b2 /\ ~(b1 = &0) /\ ~(b2 = &0) /\
                     abs b1 <= &2 * sqrt(&(21 * p * q)) *
                               (log(&(21 * p * q)) + &3) /\
                     abs b2 <= sqrt(&(21 * q)) * (log(&(21 * q)) + &3) /\
                     abs(b1 * log((&5 + sqrt(&21)) / &2) +
                         b2 * log(cyclo_unit (21 * p)) -
                         &128 / &7 * pi * sqrt(&(p * q))) <=
                     &504 * qform_kernel(exp(--(pi * sqrt(&(p * q)) / &21)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `(p * q) MOD 4 = 3` ASSUME_TAC THENL
   [MATCH_MP_TAC CLASSNO_LINEAR_MOD_8_4 THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `coprime(21,p) /\ coprime(21,q)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `coprime(21,p * q)` THEN REWRITE_TAC[COPRIME_RMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `coprime(p,q)` ASSUME_TAC THENL
   [MATCH_MP_TAC DISTINCT_PRIME_COPRIME THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN UNDISCH_TAC `p MOD 4 = 1` THEN ASM_REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `squarefree(21 * p * q) /\ squarefree(21 * q) /\ squarefree(21 * p)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQUAREFREE_MUL; PRIME_IMP_SQUAREFREE;
                 CLASSNO_CYCLO_SQUAREFREE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(21 * p * q) MOD 4 = 3 /\ (21 * q) MOD 4 = 3 /\ (21 * p) MOD 4 = 1`
  STRIP_ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(p = 0) /\ ~(q = 0)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  MP_TAC(SPECL [`21`; `3`; `7`; `p:num`; `q:num`] CN_GENUS_PRODUCT_LIMIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CLASSNO_LIMIT_PRIMES] THEN CONV_TAC NUM_REDUCE_CONV;
    DISCH_THEN(X_CHOOSE_THEN `S:real` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `abs S <= &4 * pi / sqrt(&(p * q)) *
                qform_kernel(exp(--(pi * sqrt(&(p * q)) /
                  &21)))` ASSUME_TAC THENL
   [REWRITE_TAC[qform_kernel] THEN MATCH_MP_TAC CLASSNO_SLICE_BOUND THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `21 * p * q` CN_LINEAR_L1_ODD) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` (X_CHOOSE_THEN `u1:real`
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  MP_TAC(SPEC `21 * q` CN_LINEAR_L1_ODD) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:real` (X_CHOOSE_THEN `u2:real`
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  SUBGOAL_THEN `u1 = &1` ASSUME_TAC THENL
   [MP_TAC(SPEC `p * q` CLASSNO_LINEAR_QCHAR_2) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    UNDISCH_TAC `qchar (21 * p * q) 2 = &2 - u1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Lfunction (\n. Cx(qchar 21 n)) =
                Cx(Re(Lfunction (\n. Cx(qchar 21 n))))` ASSUME_TAC THENL
   [MATCH_MP_TAC CLASSNO_SERIES_LFUNCTION_REAL THEN EXISTS_TAC `21` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC QCHAR_DIRICHLET THEN REWRITE_TAC[ARITH];
      MATCH_MP_TAC QCHAR_NONPRINCIPAL THEN
      REWRITE_TAC[CLASSNO_CYCLO_SQUAREFREE; ARITH];
      REWRITE_TAC[REAL_CX]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Lfunction (\n. Cx(qchar 21 n)) *
    Lfunction (\n. Cx(qchar (21 * p * q) n)) =
    Cx(Re(Lfunction (\n. Cx(qchar 21 n))) *
       Re(Lfunction (\n. Cx(qchar (21 * p * q) n))))`
  ASSUME_TAC THENL
   [REWRITE_TAC[CX_MUL] THEN BINOP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Lfunction (\n. Cx(qchar (21 * p) n)) *
    Lfunction (\n. Cx(qchar (21 * q) n)) =
    Cx(&2 * (zeta_coprime 21 + S) -
       Re(Lfunction (\n. Cx(qchar 21 n))) *
       Re(Lfunction (\n. Cx(qchar (21 * p * q) n))))`
  ASSUME_TAC THENL
   [REWRITE_TAC[CX_SUB] THEN
    MATCH_MP_TAC(COMPLEX_RING
     `!x:complex. x = a /\ x + y = b ==> y = b - a`) THEN
    EXISTS_TAC
     `Lfunction (\n. Cx(qchar 21 n)) *
      Lfunction (\n. Cx(qchar (21 * p * q) n))` THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 <= pi` ASSUME_TAC THENL
   [MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < sqrt(&(p * q)) /\ &0 < sqrt(&21) /\ &0 < sqrt(&(21 * p * q)) /\
    &0 < sqrt(&(21 * p)) /\ &0 < sqrt(&(21 * q))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ; MULT_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt(&21) * sqrt(&(21 * p * q)) = &21 * sqrt(&(p * q)) /\
    sqrt(&(21 * p)) * sqrt(&(21 * q)) = &21 * sqrt(&(p * q))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; SQRT_MUL] THEN
    MP_TAC(SPEC `&21:real` SQRT_POW_2) THEN REWRITE_TAC[REAL_POS] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Re(Lfunction (\n. Cx(qchar 21 n))) *
    Re(Lfunction (\n. Cx(qchar (21 * p * q) n))) +
    (&2 * (zeta_coprime 21 + S) -
     Re(Lfunction (\n. Cx(qchar 21 n))) *
     Re(Lfunction (\n. Cx(qchar (21 * p * q) n)))) =
    &2 * (&384 / &441 * pi pow 2 / &6 + S)`
  ASSUME_TAC THENL
   [REWRITE_TAC[CLASSNO_LINEAR_ZETA_21_33; CN_ZETA_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(Lfunction (\n. Cx(qchar (21 * p) n))) =
    abs(log(cyclo_unit (21 * p))) / sqrt(&(21 * p))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CN_LINEAR_L1_EVEN THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(p = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(Re(Lfunction (\n. Cx(qchar 21 n))) *
        Re(Lfunction (\n. Cx(qchar (21 * p * q) n)))) =
    norm(Lfunction (\n. Cx(qchar 21 n))) *
    norm(Lfunction (\n. Cx(qchar (21 * p * q) n))) /\
    abs(&2 * (zeta_coprime 21 + S) -
        Re(Lfunction (\n. Cx(qchar 21 n))) *
        Re(Lfunction (\n. Cx(qchar (21 * p * q) n)))) =
    norm(Lfunction (\n. Cx(qchar (21 * p) n))) *
    norm(Lfunction (\n. Cx(qchar (21 * q) n)))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM COMPLEX_NORM_MUL; GSYM COMPLEX_NORM_CX] THEN
    CONJ_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(Lfunction (\n. Cx(qchar (21 * p * q) n))) <=
    log(&(21 * p * q)) + &3 /\
    norm(Lfunction (\n. Cx(qchar (21 * q) n))) <= log(&(21 * q)) + &3`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ASSUME_TAC(CONJUNCT1 CLASSNO_L1_REAL) THEN
  ASSUME_TAC(CONJUNCT1 CLASSNO_CYCLO_LOG_POS) THEN
  MP_TAC(SPECL
   [`pi`; `sqrt(&(p * q))`; `sqrt(&21)`; `sqrt(&(21 * p * q))`;
    `sqrt(&(21 * p))`; `sqrt(&(21 * q))`; `log((&5 + sqrt(&21)) / &2)`;
    `log(cyclo_unit (21 * p))`; `t1:real`; `t2:real`; `u1:real`; `u2:real`;
    `norm(Lfunction (\n. Cx(qchar 21 n)))`;
    `norm(Lfunction (\n. Cx(qchar (21 * p * q) n)))`;
    `norm(Lfunction (\n. Cx(qchar (21 * p) n)))`;
    `norm(Lfunction (\n. Cx(qchar (21 * q) n)))`;
    `S:real`; `qform_kernel(exp(--(pi * sqrt(&(p * q)) / &21)))`;
    `Re(Lfunction (\n. Cx(qchar 21 n))) *
     Re(Lfunction (\n. Cx(qchar (21 * p * q) n)))`;
    `&2 * (zeta_coprime 21 + S) -
     Re(Lfunction (\n. Cx(qchar 21 n))) *
     Re(Lfunction (\n. Cx(qchar (21 * p * q) n)))`;
    `log(&(21 * p * q)) + &3`; `log(&(21 * q)) + &3`]
   CN_LINEAR_MAIN_ARITH) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN ACCEPT_TAC]);;

(* Small q: one modulus k, the two classes f = (1, 1, (d + 1)/4) and         *)
(* f2 = (q, q, (p + q)/4), u = 2 - chi_kd(2), u q k sqrt(d)/pi times the     *)
(* total identity: b = +-q T(kd).                                            *)

let CN_LINEAR_SMALL = prove
 (`!k k1 k2 p q.
     k = k1 * k2 /\ prime k1 /\ prime k2 /\ ~(k1 = k2) /\ k MOD 4 = 1 /\
     prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3 /\
     coprime(k,p * q) /\ form_classno (--(&(p * q))) = 2
     ==> ?b u. integer b /\ ~(b = &0) /\ (u = &1 \/ u = &3) /\
               abs b <= &q * sqrt(&(k * p * q)) * (log(&(k * p * q)) + &3) /\
               abs(b * log(cyclo_unit k) -
                   u * (&q + qchar k q) *
                   &((k1 EXP 2 - 1) * (k2 EXP 2 - 1)) / (&6 * &k) *
                   pi * sqrt(&(p * q))) <=
               &4 * u * &q * &k *
               (qform_kernel(exp(--(pi * sqrt(&(p * q)) / &k))) +
                qform_kernel(exp(--(pi * sqrt(&(p * q)) / (&q * &k)))))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (is_var o lhs o concl)) THEN
  SUBGOAL_THEN `ODD k` ASSUME_TAC THENL
   [MATCH_MP_TAC CLASSNO_GAUSS_ODD_MOD4 THEN DISJ1_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `coprime(k,p) /\ coprime(k,q)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `coprime(k,p * q)` THEN REWRITE_TAC[COPRIME_RMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `coprime(p,q)` ASSUME_TAC THENL
   [MATCH_MP_TAC DISTINCT_PRIME_COPRIME THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_TAC THEN UNDISCH_TAC `p MOD 4 = 1` THEN
    UNDISCH_TAC `q MOD 4 = 3` THEN FIRST_X_ASSUM SUBST1_TAC THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 < k /\ squarefree k` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `k1 * k2 = k` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[SQUAREFREE_MUL; PRIME_IMP_SQUAREFREE;
                 DISTINCT_PRIME_COPRIME] THEN
    MP_TAC(SPEC `k1:num` PRIME_GE_2) THEN MP_TAC(SPEC `k2:num` PRIME_GE_2) THEN
    ASM_REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP LE_MULT2) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `squarefree(k * p * q)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQUAREFREE_MUL; PRIME_IMP_SQUAREFREE]; ALL_TAC] THEN
  SUBGOAL_THEN `(p * q) MOD 4 = 3` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN
    UNDISCH_TAC `p MOD 4 = 1` THEN UNDISCH_TAC `q MOD 4 = 3` THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `(k * p * q) MOD 4 = 3` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN
    UNDISCH_TAC `(p * q) MOD 4 = 3` THEN UNDISCH_TAC `k MOD 4 = 1` THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(p = 0) /\ ~(q = 0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC PRIME_IMP_NZ THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `4 * ((p * q + 1) DIV 4) = p * q + 1 /\
                4 * ((p + q) DIV 4) = p + q` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CLASSNO_SERIES_C0 THEN FIRST_ASSUM ACCEPT_TAC;
      ONCE_REWRITE_TAC[MULT_SYM] THEN
      REWRITE_TAC[GSYM DIVIDES_DIV_MULT; DIVIDES_MOD] THEN
      ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
      UNDISCH_TAC `p MOD 4 = 1` THEN UNDISCH_TAC `q MOD 4 = 3` THEN
      REPEAT(DISCH_THEN SUBST1_TAC) THEN CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `k1:num`; `k2:num`; `p:num`; `q:num`]
    CN_TOTAL_PRODUCT_LIMIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `S1:real` (X_CHOOSE_THEN `S2:real`
      STRIP_ASSUME_TAC))] THEN
  SUBGOAL_THEN
   `abs S1 <= &4 * pi / sqrt(&(p * q)) *
              qform_kernel(exp(--(pi * sqrt(&(p * q)) / &k)))`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`k:num`; `k1:num`; `k2:num`; `1`; `&1:int`;
                  `&((p * q + 1) DIV 4):int`; `p * q`; `S1:real`]
      CN_LINEAR_SLICE) THEN
    REWRITE_TAC[REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[COPRIME_1] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[LT_NZ; MULT_EQ_0]; ALL_TAC] THEN
    REWRITE_TAC[INT_POW_ONE; INT_MUL_LID; INT_OF_NUM_MUL] THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs S2 <= &4 * pi / sqrt(&(p * q)) *
              qform_kernel(exp(--(pi * sqrt(&(p * q)) / (&q * &k))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CN_LINEAR_SLICE THEN
    MAP_EVERY EXISTS_TAC
     [`k1:num`; `k2:num`; `&q:int`; `&((p + q) DIV 4):int`] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[LT_NZ]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[LT_NZ; MULT_EQ_0]; ALL_TAC] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN
    SUBGOAL_THEN `&4 * &((p + q) DIV 4) = &p + &q:int` MP_TAC THENL
     [ASM_REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_ADD]; ALL_TAC] THEN
    CONV_TAC INT_RING;
    ALL_TAC] THEN
  MP_TAC(SPEC `k * p * q` CN_LINEAR_L1_ODD) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `u:real`
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `norm(Lfunction (\n. Cx(qchar k n))) = abs(log(cyclo_unit k)) / sqrt(&k)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CN_LINEAR_L1_EVEN THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 <= pi` ASSUME_TAC THENL
   [MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < sqrt(&(p * q)) /\ &0 < sqrt(&k) /\ &0 < sqrt(&(k * p * q)) /\
    &1 <= &q /\ integer(&q) /\ &1 <= &k`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INTEGER_CLOSED; REAL_OF_NUM_LE] THEN
    REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC SQRT_POS_LT) THEN
    REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ; MULT_EQ_0] THEN
    MAP_EVERY UNDISCH_TAC [`~(p = 0)`; `~(q = 0)`; `1 < k`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&k) * sqrt(&(k * p * q)) = &k * sqrt(&(p * q))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; SQRT_MUL] THEN
    MP_TAC(SPEC `&k:real` SQRT_POW_2) THEN REWRITE_TAC[REAL_POS] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `zeta_coprime k * (&1 + qchar k q / &q) + S1 + S2 =
    &((k1 EXP 2 - 1) * (k2 EXP 2 - 1)) / &k pow 2 * pi pow 2 / &6 *
    (&1 + qchar k q / &q) + S1 + S2`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`k:num`; `k1:num`; `k2:num`] CN_LINEAR_ZETA_MUL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(zeta_coprime k * (&1 + qchar k q / &q) + S1 + S2) =
    norm(Lfunction (\n. Cx(qchar k n))) *
    norm(Lfunction (\n. Cx(qchar (k * p * q) n)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM COMPLEX_NORM_MUL; GSYM COMPLEX_NORM_CX] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(Lfunction (\n. Cx(qchar (k * p * q) n))) <= log(&(k * p * q)) + &3`
  ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL
   [`pi`; `sqrt(&(p * q))`; `sqrt(&k)`; `sqrt(&(k * p * q))`;
    `log(cyclo_unit k)`; `t:real`; `u:real`; `&q:real`; `&k:real`;
    `&((k1 EXP 2 - 1) * (k2 EXP 2 - 1)):real`; `qchar k q`;
    `S1:real`; `S2:real`;
    `qform_kernel(exp(--(pi * sqrt(&(p * q)) / &k)))`;
    `qform_kernel(exp(--(pi * sqrt(&(p * q)) / (&q * &k))))`; `&4`;
    `norm(Lfunction (\n. Cx(qchar k n)))`;
    `norm(Lfunction (\n. Cx(qchar (k * p * q) n)))`;
    `zeta_coprime k * (&1 + qchar k q / &q) + S1 + S2`;
    `log(&(k * p * q)) + &3`] CN_LINEAR_LOG_ARITH) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MAP_EVERY UNDISCH_TAC [`&3 <= pi`; `u = &1 \/ u = &3`] THEN
    REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `b:real` THEN EXISTS_TAC `u:real` THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

(* The discriminant -4d: the forms (1, 0, d) and (2, b2, c2), the character  *)
(* chi_k kchar4 d modulo 4 k d, 4 k sqrt(d)/pi times the total identity:     *)
(* b = +-2 t, t from CN_L1_KCHAR4.                                           *)

let CN_LINEAR_EVEN = prove
 (`!k k1 k2 d.
     k = k1 * k2 /\ prime k1 /\ prime k2 /\ ~(k1 = k2) /\ k MOD 4 = 1 /\
     (prime d /\ d MOD 4 = 1 \/ (?p. prime p /\ ODD p /\ d = 2 * p)) /\
     coprime(k,d) /\ form_classno (--(&4 * &d)) = 2
     ==> ?b. integer b /\ ~(b = &0) /\
             abs b <= &2 * sqrt(&(k * d)) * (log(&(4 * k * d)) + &3) /\
             abs(b * log(cyclo_unit k) -
                 (&2 + qchar k 2) * &((k1 EXP 2 - 1) * (k2 EXP 2 - 1)) /
                 (&3 * &k) * pi * sqrt(&d)) <=
             &8 * &k * (qform_kernel(exp(--(&2 * pi * sqrt(&d) / &k))) +
                        qform_kernel(exp(--(pi * sqrt(&d) / &k))))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (is_var o lhs o concl)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CNP_MOD4_EVEN) THEN
  SUBGOAL_THEN `squarefree d` ASSUME_TAC THENL
   [UNDISCH_TAC `prime d /\ d MOD 4 = 1 \/ (?p. prime p /\ ODD p /\ d = 2 * p)`
    THEN STRIP_TAC THEN
    ASM_SIMP_TAC[PRIME_IMP_SQUAREFREE; SQUAREFREE_MUL; PRIME_2; COPRIME_2];
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `k1:num`; `k2:num`; `d:num`] CNP_EVEN_FACTS) THEN
  ASM_REWRITE_TAC[ARITH_RULE `k * 4 * d = 4 * k * d`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 < k /\ squarefree k` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `k1 * k2 = k` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[SQUAREFREE_MUL; PRIME_IMP_SQUAREFREE;
                 DISTINCT_PRIME_COPRIME] THEN
    MP_TAC(SPEC `k1:num` PRIME_GE_2) THEN MP_TAC(SPEC `k2:num` PRIME_GE_2) THEN
    ASM_REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP LE_MULT2) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `squarefree(k * d) /\ 1 < k * d /\ 1 <= 4 * k * d`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SQUAREFREE_MUL; ARITH_RULE `1 <= n <=> ~(n = 0)`;
                    ARITH_RULE `1 < n <=> ~(n = 0) /\ ~(n = 1)`;
                    MULT_EQ_0; MULT_EQ_1] THEN
    MAP_EVERY UNDISCH_TAC [`1 < k`; `~(d = 0)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `k1:num`; `k2:num`; `d:num`]
    CN_TOTAL_PRODUCT_LIMIT_EVEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `b2:int` (X_CHOOSE_THEN `c2:int`
      (X_CHOOSE_THEN `S1:real` (X_CHOOSE_THEN `S2:real`
        STRIP_ASSUME_TAC))))] THEN
  SUBGOAL_THEN `&0 < sqrt(&d) /\ sqrt(&(4 * d)) = &2 * sqrt(&d) /\ ~(&k = &0)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      UNDISCH_TAC `~(d = 0)` THEN ARITH_TAC;
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL; SQRT_MUL] THEN AP_THM_TAC THEN
      AP_TERM_TAC THEN MATCH_MP_TAC SQRT_UNIQUE THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_EQ] THEN UNDISCH_TAC `1 < k` THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs S1 <= &2 * pi / sqrt(&d) *
              qform_kernel(exp(--(&2 * pi * sqrt(&d) / &k)))`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`k:num`; `k1:num`; `k2:num`; `1`; `&0:int`; `&d:int`;
                  `4 * d`; `S1:real`] CN_LINEAR_SLICE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[COPRIME_1] THEN
      CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `~(d = 0)` THEN ARITH_TAC;
        REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN CONV_TAC INT_RING];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `pi * (&2 * sqrt(&d)) / (&1 * &k) = &2 * pi * sqrt(&d) / &k`
    SUBST1_TAC THENL
     [UNDISCH_TAC `~(&k = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `b = c ==> a <= b ==> a <= (c:real)`) THEN
    UNDISCH_TAC `&0 < sqrt(&d)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs S2 <= &2 * pi / sqrt(&d) * qform_kernel(exp(--(pi * sqrt(&d) / &k)))`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`k:num`; `k1:num`; `k2:num`; `2`; `b2:int`; `c2:int`;
                  `4 * d`; `S2:real`] CN_LINEAR_SLICE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `~(d = 0)` THEN ARITH_TAC;
        REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN
        UNDISCH_TAC `&8 * (c2:int) - b2 pow 2 = &4 * &d` THEN INT_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `pi * (&2 * sqrt(&d)) / (&2 * &k) = pi * sqrt(&d) / &k`
    SUBST1_TAC THENL
     [UNDISCH_TAC `~(&k = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `b = c ==> a <= b ==> a <= (c:real)`) THEN
    UNDISCH_TAC `&0 < sqrt(&d)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `d:num`] CN_L1_KCHAR4) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN
   `norm(Lfunction (\n. Cx(qchar k n * kchar4 d n))) <=
    log(&(4 * k * d)) + &3 /\ ~(t = &0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CN_L1_BOUND THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN
      MP_TAC(ISPECL [`4 * k * d`; `\n. Cx(qchar k n * kchar4 d n)`]
        LFUNCTION_NONZERO_NONPRINCIPAL) THEN
      ASM_REWRITE_TAC[GSYM COMPLEX_NORM_ZERO; REAL_ABS_0; REAL_MUL_RZERO;
                      real_div; REAL_MUL_LZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(Lfunction (\n. Cx(qchar k n))) = abs(log(cyclo_unit k)) / sqrt(&k)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CN_LINEAR_L1_EVEN THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&3 <= pi /\ &0 < sqrt(&k) /\ &0 < sqrt(&(k * d)) /\ &1 <= &k /\
    sqrt(&k) * sqrt(&(k * d)) = &k * sqrt(&d)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      UNDISCH_TAC `1 < k` THEN ARITH_TAC;
      MATCH_MP_TAC SQRT_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      UNDISCH_TAC `1 < k * d` THEN ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_LE] THEN UNDISCH_TAC `1 < k` THEN ARITH_TAC;
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL; SQRT_MUL] THEN
      MP_TAC(SPEC `&k:real` SQRT_POW_2) THEN REWRITE_TAC[REAL_POS] THEN
      CONV_TAC REAL_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `zeta_coprime k * (&1 + qchar k 2 / &2) + S1 + S2 =
    &((k1 EXP 2 - 1) * (k2 EXP 2 - 1)) / &k pow 2 * pi pow 2 / &6 *
    (&1 + qchar k 2 / &2) + S1 + S2`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`k:num`; `k1:num`; `k2:num`] CN_LINEAR_ZETA_MUL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(zeta_coprime k * (&1 + qchar k 2 / &2) + S1 + S2) =
    norm(Lfunction (\n. Cx(qchar k n))) *
    norm(Lfunction (\n. Cx(qchar k n * kchar4 d n)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM COMPLEX_NORM_MUL; GSYM COMPLEX_NORM_CX] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL
   [`pi`; `sqrt(&d)`; `sqrt(&k)`; `sqrt(&(k * d))`;
    `log(cyclo_unit k)`; `abs t`; `&2`; `&2`; `&k:real`;
    `&((k1 EXP 2 - 1) * (k2 EXP 2 - 1)):real`; `qchar k 2`;
    `S1:real`; `S2:real`;
    `qform_kernel(exp(--(&2 * pi * sqrt(&d) / &k)))`;
    `qform_kernel(exp(--(pi * sqrt(&d) / &k)))`; `&2`;
    `norm(Lfunction (\n. Cx(qchar k n)))`;
    `norm(Lfunction (\n. Cx(qchar k n * kchar4 d n)))`;
    `zeta_coprime k * (&1 + qchar k 2 / &2) + S1 + S2`;
    `log(&(4 * k * d)) + &3`] CN_LINEAR_LOG_ARITH) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    ASM_SIMP_TAC[INTEGER_CLOSED; REAL_ABS_INTEGER_LEMMA] THEN
    UNDISCH_TAC `&3 <= pi` THEN REAL_ARITH_TAC;
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    MATCH_MP_TAC(TAUT
     `(p ==> q) ==> a /\ b /\ c /\ p ==> a /\ b /\ c /\ q`) THEN
    MATCH_MP_TAC(REAL_ARITH
     `x = y /\ e = e' ==> abs(z - x) <= e ==> abs(z - y) <= e'`) THEN
    CONJ_TAC THENL [UNDISCH_TAC `~(&k = &0)` THEN CONV_TAC REAL_FIELD;
                    REAL_ARITH_TAC]]);;
