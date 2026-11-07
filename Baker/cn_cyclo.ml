(* ========================================================================= *)
(* The cyclotomic unit of a real quadratic field of composite discriminant,  *)
(* and an explicit bound for L(1, chi).                                      *)
(*                                                                           *)
(* Purpose: for squarefree composite q = 1 mod 4 the cyclotomic unit         *)
(* xi = cyclo_unit q = prod_a sin(pi a / q)^(-chi(a)), chi = qchar q, lies   *)
(* in Q(sqrt q) and is a root of X^2 - t X + 1 with t an integer             *)
(* (CN_CYCLO_UNIT_QUADRATIC); with CLASSNO_L1_EVEN, abs L(1, chi) is then    *)
(* abs(log xi) / sqrt q, the logarithm of an algebraic number of degree 2    *)
(* (the large unit of the linear forms of the class number two problem).     *)
(* Second, abs L(1, c) <= log m + 3 for every non-principal Dirichlet        *)
(* character c modulo m (CN_L1_BOUND), which bounds the integer coefficients *)
(* and the heights in those linear forms.                                    *)
(*                                                                           *)
(* Method: zeta^a = exp(2 pi i a / q); S+ and S- are the a in 1..q-1 with    *)
(* chi(a) = 1 and chi(a) = -1, U and V the products of 1 - zeta^a over S+    *)
(* and S-. Since chi is even (q = 1 mod 4), S+ and S- are invariant under    *)
(* a -> q - a, so the arguments of the factors cancel and U, V are the       *)
(* positive reals prod 2 sin(pi a / q) (CN_CYCLO_HALF_PRODUCT); the sum of   *)
(* chi vanishes, so S+ and S- have the same size and xi = V / U              *)
(* (CN_CYCLO_UNIT_RATIO). The Galois group of Q(zeta_q) inside C, zeta_q =   *)
(* exp(2 pi i / q), consists of ring homomorphisms with zeta_q -> zeta_q^c,  *)
(* c coprime to q, and its fixed elements are rational (CN_CYCLO_GALOIS:     *)
(* ANT/cyclotomic_galois.ml with FIXED_FIELD_GALOIS_GROUP). Such an element  *)
(* maps U, V to U, V if chi(c) = 1 and to V, U if chi(c) = -1 (the           *)
(* permutation a -> c a of the units modulo q, CN_CYCLO_HALF_ACTION) and the *)
(* Gauss sum g (real, g^2 = q: CN_CYCLO_GAUSS_REAL) to chi(c) g, so U + V    *)
(* and (U - V) g are rational and U = A + B g, V = A - B g with A, B         *)
(* rational (CN_CYCLO_HALVES_PAIR). When two distinct primes divide q, the   *)
(* product of 1 - zeta^a over all a coprime to q is Phi_q(1) = 1             *)
(* (CN_CYCLO_UNITS_PRODUCT: CYCLOTOMIC_POLY_SPLITS and                       *)
(* CYCLOTOMIC_POLY_EVAL_1 of ANT/cyclotomic_poly.ml over complex_ring, where *)
(* zeta_q has order q), so U V = 1, xi = V / U = V^2 = (A - B g)^2, and      *)
(* t = U^2 + V^2 is a rational algebraic integer, hence an integer           *)
(* (ALGEBRAIC_INTEGER_RATIONAL). For the bound of L(1, c): the sums of c     *)
(* over intervals have norm at most m - 1 (periodicity), so Abel summation   *)
(* (SERIES_DIRICHLET_COMPLEX_VERY_EXPLICIT) bounds the tail beyond m by      *)
(* 2 (m - 1) / (m + 1) < 2 (CNC_L1_TAIL), and the first m terms by the       *)
(* harmonic sum, at most 1 + log m (CNC_HARMONIC_LE_LOG).                    *)
(*                                                                           *)
(* Main results: CN_CYCLO_UNIT_QUADRATIC, CN_L1_BOUND;                       *)
(* CN_CYCLO_UNITS_PRODUCT, CN_CYCLO_GALOIS, CN_CYCLO_HALF_ACTION,            *)
(* CN_CYCLO_HALVES_PAIR, CN_CYCLO_GAUSS_REAL, CN_CYCLO_HALF_PRODUCT,         *)
(* CN_CYCLO_UNIT_RATIO, CNC_HARMONIC_LE_LOG, CNC_DIRICHLET_INTERVAL_SUM,     *)
(* CNC_L1_TAIL; helper names CN_CYCLO_*, CNC_*.                              *)
(*                                                                           *)
(* Uses: Baker/cn_defs.ml (cyclo_unit), Baker/classno_chardefs.ml (qchar,    *)
(* QCHAR_1), Baker/classno_gauss.ml (QCHAR_GAUSS_PROPERTY,                   *)
(* QCHAR_NONPRINCIPAL, CLASSNO_GAUSS_PROPERTY_NONPRINCIPAL,                  *)
(* CLASSNO_GAUSS_NORM_SQ, CLASSNO_GAUSS_ROOT_EQ_1,                           *)
(* CLASSNO_GAUSS_ONE_SUB_CEXP, CLASSNO_GAUSS_ANGLE_BOUNDS,                   *)
(* CLASSNO_GAUSS_VSUM_ANTI, CLASSNO_GAUSS_CHAR_SUM_0),                       *)
(* Baker/classno_series.ml (QCHAR_DIRICHLET, CLASSNO_SERIES_QCHAR_LMUL),     *)
(* Baker/classno_cyclo.ml (CLASSNO_CYCLO_CEXP_POW), Baker/algint.ml          *)
(* (algebraic_integer, ALGEBRAIC_INTEGER_RATIONAL,                           *)
(* ALGEBRAIC_INTEGER_ROOT_OF_UNITY), ANT/complex_embeddings.ml               *)
(* (COMPLEX_PRIME_SUBFIELD), Baker/ant_bridge_complex.ml                     *)
(* (NUMBER_FIELD_COMPLEX_SUBFIELD_GENERATED, BRIDGE_NF_HOM_CLAUSES,          *)
(* BRIDGE_NF_HOM_POLY, BRIDGE_NF_PRIME_SUBFIELD, BRIDGE_NF_SUBRING_POLY,     *)
(* BRIDGE_NF_SUBFIELD_CLOSED, BRIDGE_NF_HOM_CPRODUCT);                       *)
(* ANT/cyclotomic_poly.ml (CYCLOTOMIC_POLY_SPLITS, CYCLOTOMIC_POLY_EVAL_1),  *)
(* ANT/cyclotomic_galois.ml (CYCLOTOMIC_FIELD_GALOIS_EXTENSION,              *)
(* CYCLOTOMIC_FIELD_GALOIS_GROUP_ROOT), Library/galois.ml                    *)
(* (FIXED_FIELD_GALOIS_GROUP, GALOIS_GROUP_RING_HOMOMORPHISM),               *)
(* Library/fieldtheory.ml (SUBFIELD_GENERATED_IDEMPOT_GEN,                   *)
(* RING_ORDER_SUBFIELD_GENERATED), Library/ringtheory.ml (RING_ORDER_UNIQUE, *)
(* RING_POW_EQ_GEN, RING_HOMOMORPHISM_PRODUCT,                               *)
(* RING_PRODUCT_SUBRING_GENERATED), Multivariate/complex_ring.ml             *)
(* (COMPLEX_RING_PRODUCT); 100/dirichlet.ml (Lfunction, LFUNCTION,           *)
(* DIRICHLET_CHARACTER_SUM_MOD), Multivariate/canal.ml                       *)
(* (SERIES_DIRICHLET_COMPLEX_VERY_EXPLICIT), Library/pocklington.ml          *)
(* (ITERATE_OVER_COPRIME), Library/jacobi.ml (JACOBI_CONG).                  *)
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
needs "Baker/ant_bridge_complex.ml";;
needs "Baker/classno_cyclo.ml";;
needs "Baker/cn_defs.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* 1. Roots of unity zeta^a = exp(2 pi i a / q), the powers of the element   *)
(*    zeta_q = exp(2 pi i / q) of order q of complex_ring. The product of    *)
(*    1 - zeta^a over the units modulo q is Phi_q(1), which is 1 when two    *)
(*    distinct primes divide q (ANT/cyclotomic_poly.ml).                     *)
(* ------------------------------------------------------------------------- *)

let CN_CYCLO_ROOT_POW_MUL = prove
 (`!q a b. cexp(ii * Cx(&2 * pi * &a / &q)) pow b =
           cexp(ii * Cx(&2 * pi * &(a * b) / &q))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLASSNO_CYCLO_CEXP_POW] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; real_div] THEN REAL_ARITH_TAC);;

let CN_CYCLO_ZETA_POW = prove
 (`!q a. cexp(ii * Cx(&2 * pi * &1 / &q)) pow a =
         cexp(ii * Cx(&2 * pi * &a / &q))`,
  REWRITE_TAC[CN_CYCLO_ROOT_POW_MUL; MULT_CLAUSES]);;

let CN_CYCLO_RING_ORDER = prove
 (`!q. ~(q = 0)
       ==> ring_order complex_ring (cexp(ii * Cx(&2 * pi * &1 / &q))) = q`,
  SIMP_TAC[RING_ORDER_UNIQUE; COMPLEX_RING_CLAUSES; IN_UNIV; COMPLEX_RING_POW;
           CN_CYCLO_ZETA_POW; CLASSNO_GAUSS_ROOT_EQ_1]);;

let CN_CYCLO_ROOT_CONG = prove
 (`!m x y. (x == y) (mod m)
           ==> cexp(ii * Cx(&2 * pi * &x / &m)) =
               cexp(ii * Cx(&2 * pi * &y / &m))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `m = 0` THEN
  ASM_SIMP_TAC[CONG_MOD_0] THEN
  MP_TAC(ISPECL [`complex_ring`; `cexp(ii * Cx(&2 * pi * &1 / &m))`;
                 `x:num`; `y:num`] RING_POW_EQ_GEN) THEN
  ASM_SIMP_TAC[COMPLEX_RING_CLAUSES; IN_UNIV; COMPLEX_RING_POW;
               CN_CYCLO_ZETA_POW; CN_CYCLO_RING_ORDER]);;

let CN_CYCLO_UNITS_PRODUCT = prove
 (`!q. squarefree q /\ 1 < q /\ ~prime q
       ==> cproduct {a | a IN 1..q - 1 /\ coprime(a,q)}
             (\a. Cx(&1) - cexp(ii * Cx(&2 * pi * &a / &q))) =
           Cx(&1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?p r. prime p /\ prime r /\ ~(p = r) /\ p divides q /\ r divides q`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `q:num` PRIME_FACTOR) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC o
      GEN_REWRITE_RULE I [divides]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SQUAREFREE_MUL]) THEN
    MP_TAC(SPEC `m:num` PRIME_FACTOR) THEN ANTS_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~prime(p * 1)` THEN ASM_REWRITE_TAC[MULT_CLAUSES];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:num` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`p:num`; `r:num`] THEN
    ASM_SIMP_TAC[DIVIDES_RMUL; DIVIDES_LMUL; DIVIDES_REFL] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    ASM_MESON_TAC[PRIME_COPRIME_EQ; COPRIME_SYM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`complex_ring`; `q:num`; `p:num`; `r:num`]
    CYCLOTOMIC_POLY_EVAL_1) THEN
  MP_TAC(ISPECL [`complex_ring`; `cexp(ii * Cx(&2 * pi * &1 / &q))`;
                 `q:num`] CYCLOTOMIC_POLY_SPLITS) THEN
  ASM_SIMP_TAC[INTEGRAL_DOMAIN_COMPLEX_RING; COMPLEX_RING_CLAUSES; IN_UNIV;
               CN_CYCLO_RING_ORDER; ARITH_RULE `1 < q ==> ~(q = 0)`] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `FINITE {j | j < q /\ coprime(j,q)}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{j:num | j < q}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[POLY_EVAL_RING_PRODUCT; POLY_X_MINUS_A_IN_CARRIER;
               COMPLEX_RING_CLAUSES; IN_UNIV] THEN
  ASM_SIMP_TAC[POLY_EVAL_SUB; RING_POLYNOMIAL_VAR; RING_POLYNOMIAL_CONST;
               POLY_EVAL_VAR; POLY_EVAL_CONST; COMPLEX_RING_PRODUCT;
               COMPLEX_RING_SUB; COMPLEX_RING_POW; COMPLEX_RING_CLAUSES;
               IN_UNIV; CN_CYCLO_ZETA_POW] THEN
  MATCH_MP_TAC(MESON[]
   `(s:num->bool) = t ==> (cproduct s f = c ==> cproduct t f = c)`) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN X_GEN_TAC `a:num` THEN
  ASM_CASES_TAC `a = 0` THEN ASM_REWRITE_TAC[COPRIME_0] THENL
   [ASM_ARITH_TAC;
    MATCH_MP_TAC(TAUT `(p <=> q) ==> (p /\ r <=> q /\ r)`) THEN
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 2. The character chi = qchar q for squarefree q = 1 mod 4: values,        *)
(*    evenness, the Gauss sum (real, square q), and the splitting of sums    *)
(*    over the units into the halves chi = 1 and chi = -1.                   *)
(* ------------------------------------------------------------------------- *)

let CN_CYCLO_QCHAR_CASES = prove
 (`!q a. qchar q a = &1 \/ qchar q a = -- &1 \/ qchar q a = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[qchar] THEN
  MP_TAC(SPECL [`a:num`; `q:num`] JACOBI_CASES) THEN
  REWRITE_TAC[int_eq; int_neg_th; int_of_num_th] THEN REAL_ARITH_TAC);;

let CN_CYCLO_QCHAR_EQ_0 = prove
 (`!q a. qchar q a = &0 <=> ~coprime(a,q)`,
  REWRITE_TAC[qchar; GSYM JACOBI_EQ_0; int_eq; int_of_num_th]);;

let CN_CYCLO_QCHAR_RATIONAL = prove
 (`!q n. rational(qchar q n)`,
  SIMP_TAC[qchar; RATIONAL_INTEGER; INTEGER_REAL_OF_INT]);;

let CN_CYCLO_QCHAR_REFLECT = prove
 (`!q a. q MOD 4 = 1 /\ 1 <= a /\ a <= q ==> qchar q (q - a) = qchar q a`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ODD q` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CLASSNO_GAUSS_ODD_MOD4]; ALL_TAC] THEN
  MP_TAC(ISPECL [`q:num`; `\n. Cx(qchar q n)`; `a:num`]
    CLASSNO_GAUSS_CHAR_REFLECT) THEN
  ASM_SIMP_TAC[QCHAR_DIRICHLET; CLASSNO_GAUSS_QCHAR_MINUS1] THEN
  REWRITE_TAC[COMPLEX_MUL_LID; CX_INJ]);;

let CN_CYCLO_CNJ_ROOT = prove
 (`!q a. 1 <= q
         ==> cnj(cexp(ii * Cx(&2 * pi * &a * &1 / &q))) =
             cexp(ii * Cx(&2 * pi * &a * &(q - 1) / &q))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[CNJ_CEXP; CNJ_MUL; CNJ_II; CNJ_CX] THEN
  SUBGOAL_THEN
   `&2 * pi * &a * &(q - 1) / &q = &2 * pi * (--(&a * &1 / &q) + &a)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
    UNDISCH_TAC `1 <= q` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN CONV_TAC REAL_FIELD;
    SIMP_TAC[CLASSNO_GAUSS_CEXP_INTEGER; INTEGER_CLOSED] THEN
    AP_TERM_TAC THEN REWRITE_TAC[CX_NEG; CX_MUL] THEN
    CONV_TAC COMPLEX_RING]);;

let CN_CYCLO_GAUSS_REAL = prove
 (`!q. squarefree q /\ q MOD 4 = 1 /\ 1 < q
       ==> ?g. g pow 2 = &q /\
               !n. vsum(0..q - 1)
                     (\a. Cx(qchar q a) *
                          cexp(ii * Cx(&2 * pi * &n * &a / &q))) =
                   Cx(qchar q n) * Cx g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ODD q` ASSUME_TAC THENL
   [MATCH_MP_TAC CLASSNO_GAUSS_ODD_MOD4 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPEC `q:num` QCHAR_GAUSS_PROPERTY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `gs:complex`) THEN
  SUBGOAL_THEN `cnj gs = gs` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `1`) THEN
    FIRST_ASSUM(MP_TAC o SPEC `q - 1`) THEN
    SIMP_TAC[CLASSNO_GAUSS_QCHAR_MINUS1; QCHAR_1; COMPLEX_MUL_LID;
             ASSUME `ODD q`; ASSUME `q MOD 4 = 1`] THEN
    DISCH_THEN(fun th2 -> DISCH_THEN(fun th1 ->
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM th1] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM th2])) THEN
    SIMP_TAC[CNJ_VSUM; FINITE_NUMSEG; CNJ_MUL; CNJ_CX] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC CN_CYCLO_CNJ_ROOT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `gs * cnj gs = Cx(&q)` MP_TAC THENL
   [MATCH_MP_TAC CLASSNO_GAUSS_NORM_SQ THEN
    EXISTS_TAC `\n. Cx(qchar q n)` THEN
    ASM_SIMP_TAC[QCHAR_DIRICHLET; CNJ_CX] THEN
    MATCH_MP_TAC CLASSNO_GAUSS_PROPERTY_NONPRINCIPAL THEN
    EXISTS_TAC `gs:complex` THEN ASM_SIMP_TAC[QCHAR_DIRICHLET] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Cx(Re gs) = gs` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL; REAL_CNJ]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN EXISTS_TAC `Re gs` THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM CX_INJ; CX_POW] THEN ASM_REWRITE_TAC[COMPLEX_POW_2];
    ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THEN
  FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC RAND_CONV [GSYM(SPEC `n:num` th)]) THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REPEAT AP_TERM_TAC THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let CN_CYCLO_SPLIT_VSUM = prove
 (`!q (f:num->complex).
        vsum(1..q - 1) (\a. Cx(qchar q a) * f a) =
        vsum {a | a IN 1..q - 1 /\ qchar q a = &1} f -
        vsum {a | a IN 1..q - 1 /\ qchar q a = -- &1} f`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[VSUM_RESTRICT_SET] THEN
  SIMP_TAC[GSYM VSUM_SUB; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC
   (SPECL [`q:num`; `a:num`] CN_CYCLO_QCHAR_CASES) THEN
  CONV_TAC(DEPTH_CONV REAL_RAT_EQ_CONV) THEN REWRITE_TAC[COMPLEX_VEC_0] THEN
  CONV_TAC COMPLEX_RING);;

let CN_CYCLO_SPLIT_UNITS = prove
 (`!q. {a | a IN 1..q - 1 /\ coprime(a,q)} =
       {a | a IN 1..q - 1 /\ qchar q a = &1} UNION
       {a | a IN 1..q - 1 /\ qchar q a = -- &1} /\
       DISJOINT {a | a IN 1..q - 1 /\ qchar q a = &1}
                {a | a IN 1..q - 1 /\ qchar q a = -- &1}`,
  GEN_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `a:num` THEN
    REWRITE_TAC[MESON[CN_CYCLO_QCHAR_EQ_0]
     `coprime(a,q) <=> ~(qchar q a = &0)`] THEN
    MP_TAC(SPECL [`q:num`; `a:num`] CN_CYCLO_QCHAR_CASES) THEN
    ASM_CASES_TAC `a IN 1..q - 1` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `a:num` THEN ASM_CASES_TAC `a IN 1..q - 1` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 3. The half products U, V: positive reals, the same number of factors,    *)
(*    xi U = V; algebraic integers.                                          *)
(* ------------------------------------------------------------------------- *)

let CN_CYCLO_ONE_SUB_ROOT = prove
 (`!q a. 0 < a /\ a < q
         ==> Cx(&1) - cexp(ii * Cx(&2 * pi * &a / &q)) =
             cexp(Cx(log(&2 * sin(pi * &a / &q))) +
                  ii * Cx(pi * &a / &q - pi / &2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `&2 * pi * &a / &q` CLASSNO_GAUSS_ONE_SUB_CEXP) THEN
  ANTS_TAC THENL
   [MP_TAC(SPECL [`q:num`; `a:num`] CLASSNO_GAUSS_ANGLE_BOUNDS) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; REAL_ARITH_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN BINOP_TAC THEN REPEAT AP_TERM_TAC THEN
  REAL_ARITH_TAC);;

let CN_CYCLO_HALF_PRODUCT = prove
 (`!q e. q MOD 4 = 1 /\ 1 < q
         ==> cproduct {a | a IN 1..q - 1 /\ qchar q a = e}
               (\a. Cx(&1) - cexp(ii * Cx(&2 * pi * &a / &q))) =
             Cx(exp(sum {a | a IN 1..q - 1 /\ qchar q a = e}
                        (\a. log(&2 * sin(pi * &a / &q)))))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `s = {a | a IN 1..q - 1 /\ qchar q a = e}` THEN
  SUBGOAL_THEN `FINITE(s:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG]; ALL_TAC] THEN
  SUBGOAL_THEN
   `cproduct s (\a. Cx(&1) - cexp(ii * Cx(&2 * pi * &a / &q))) =
    cproduct s (\a. cexp(Cx(log(&2 * sin(pi * &a / &q))) +
                         ii * Cx(pi * &a / &q - pi / &2)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CPRODUCT_EQ THEN EXPAND_TAC "s" THEN
    REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CN_CYCLO_ONE_SUB_ROOT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM CEXP_VSUM; VSUM_ADD; CX_EXP] THEN AP_TERM_TAC THEN
  REWRITE_TAC[VSUM_CX] THEN
  SUBGOAL_THEN `vsum s (\a. ii * Cx(pi * &a / &q - pi / &2)) = Cx(&0)`
   (fun th -> REWRITE_TAC[th; COMPLEX_ADD_RID]) THEN
  EXPAND_TAC "s" THEN REWRITE_TAC[VSUM_RESTRICT_SET] THEN
  MATCH_MP_TAC CLASSNO_GAUSS_VSUM_ANTI THEN X_GEN_TAC `a:num` THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC[CN_CYCLO_QCHAR_REFLECT; ARITH_RULE `a <= q - 1 ==> a <= q`] THEN
  COND_CASES_TAC THEN REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_NEG_0] THEN
  ASM_SIMP_TAC[CLASSNO_GAUSS_PI_REFLECT; ARITH_RULE `1 < q ==> ~(q = 0)`;
               ARITH_RULE `a <= q - 1 ==> a <= q`] THEN
  REWRITE_TAC[REAL_ARITH `(pi - x) - pi / &2 = --(x - pi / &2)`;
              CX_NEG; COMPLEX_MUL_RNEG]);;

let CN_CYCLO_CARD_HALVES = prove
 (`!q. squarefree q /\ q MOD 4 = 1 /\ 1 < q
       ==> CARD {a | a IN 1..q - 1 /\ qchar q a = -- &1} =
           CARD {a | a IN 1..q - 1 /\ qchar q a = &1}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `vsum(1..q - 1) (\n. Cx(qchar q n)) = Cx(&0)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLASSNO_GAUSS_CHAR_SUM_0 THEN
    ASM_SIMP_TAC[QCHAR_DIRICHLET; CLASSNO_GAUSS_ODD_MOD4; QCHAR_NONPRINCIPAL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`q:num`; `\a:num. Cx(&1)`] CN_CYCLO_SPLIT_VSUM) THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_RID] THEN
  SIMP_TAC[VSUM_CONST; FINITE_RESTRICT; FINITE_NUMSEG; COMPLEX_CMUL;
           COMPLEX_MUL_RID] THEN
  REWRITE_TAC[GSYM CX_SUB; CX_INJ; REAL_OF_NUM_EQ;
              REAL_ARITH `&0 = x - y <=> y = x`]);;

let CN_CYCLO_UNIT_RATIO = prove
 (`!q. squarefree q /\ q MOD 4 = 1 /\ 1 < q
       ==> Cx(cyclo_unit q) *
           cproduct {a | a IN 1..q - 1 /\ qchar q a = &1}
             (\a. Cx(&1) - cexp(ii * Cx(&2 * pi * &a / &q))) =
           cproduct {a | a IN 1..q - 1 /\ qchar q a = -- &1}
             (\a. Cx(&1) - cexp(ii * Cx(&2 * pi * &a / &q)))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CN_CYCLO_HALF_PRODUCT; cyclo_unit] THEN
  REWRITE_TAC[GSYM CX_MUL; CX_INJ; GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `!e. sum {a | a IN 1..q - 1 /\ qchar q a = e}
            (\a. log(&2 * sin(pi * &a / &q))) =
        &(CARD {a | a IN 1..q - 1 /\ qchar q a = e}) * log(&2) +
        sum {a | a IN 1..q - 1 /\ qchar q a = e}
            (\a. log(sin(pi * &a / &q)))`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN
    SIMP_TAC[GSYM SUM_CONST; FINITE_RESTRICT; FINITE_NUMSEG; GSYM SUM_ADD] THEN
    MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC LOG_MUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC CLASSNO_GAUSS_SIN_POS THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[CN_CYCLO_CARD_HALVES] THEN
  MATCH_MP_TAC(REAL_ARITH `x = a - b ==> --x + c + a = c + b`) THEN
  MP_TAC(ISPECL [`q:num`; `\a. Cx(log(sin(pi * &a / &q)))`]
    CN_CYCLO_SPLIT_VSUM) THEN
  REWRITE_TAC[GSYM CX_MUL; VSUM_CX; GSYM CX_SUB; CX_INJ] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

let CN_CYCLO_ROOT_ALGINT = prove
 (`!q a. 1 <= q ==> algebraic_integer(cexp(ii * Cx(&2 * pi * &a / &q)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ALGEBRAIC_INTEGER_ROOT_OF_UNITY THEN
  EXISTS_TAC `q:num` THEN
  ASM_REWRITE_TAC[CN_CYCLO_ROOT_POW_MUL; CLASSNO_GAUSS_ROOT_EQ_1] THEN
  SIMP_TAC[DIVIDES_LMUL; DIVIDES_REFL]);;

let CN_CYCLO_HALF_ALGINT = prove
 (`!q s. 1 <= q /\ FINITE s
         ==> algebraic_integer
               (cproduct s (\a. Cx(&1) - cexp(ii * Cx(&2 * pi * &a / &q))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ALGEBRAIC_INTEGER_CPRODUCT THEN
  ASM_SIMP_TAC[ALGEBRAIC_INTEGER_SUB; ALGEBRAIC_INTEGER_CLOSED;
               CN_CYCLO_ROOT_ALGINT]);;

(* ------------------------------------------------------------------------- *)
(* 4. The Galois group of Q(zeta_q) inside C, zeta_q = exp(2 pi i / q)       *)
(*    (ANT/cyclotomic_galois.ml): its elements are ring homomorphisms with   *)
(*    zeta_q -> zeta_q^c for some c coprime to q, and the elements of        *)
(*    Q(zeta_q) fixed by all of them are rational. Such an element maps U, V *)
(*    to U, V if chi(c) = 1 and to V, U if chi(c) = -1 (the permutation      *)
(*    a -> c a of the units modulo q), and the Gauss sum g to chi(c) g; so   *)
(*    U + V and (U - V) g are rational: U = x + y g, V = x - y g.            *)
(* ------------------------------------------------------------------------- *)

let CN_CYCLO_GALOIS = prove
 (`!q. ~(q = 0)
       ==> ?G. (!f. f IN G
                    ==> ring_homomorphism
                          (subfield_generated complex_ring
                             {cexp(ii * Cx(&2 * pi * &1 / &q))},
                           complex_ring) f /\
                        ?c. coprime(c,q) /\
                            f(cexp(ii * Cx(&2 * pi * &1 / &q))) =
                            cexp(ii * Cx(&2 * pi * &c / &q))) /\
               (!x. x IN ring_carrier(subfield_generated complex_ring
                                        {cexp(ii * Cx(&2 * pi * &1 / &q))}) /\
                    (!f. f IN G ==> f x = x)
                    ==> ?r. rational r /\ x = Cx r)`,
  GEN_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `z = cexp(ii * Cx(&2 * pi * &1 / &q))` THEN
  ABBREV_TAC `k = subfield_generated complex_ring {z}` THEN
  SUBGOAL_THEN
   `number_field(k:complex ring) /\ (z:complex) IN ring_carrier k /\
    ring_order k z = q /\ subfield_generated k {z} = k`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC NUMBER_FIELD_COMPLEX_SUBFIELD_GENERATED THEN
      REWRITE_TAC[FINITE_SING; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
      MATCH_MP_TAC ALGEBRAIC_INTEGER_IMP_ALGEBRAIC_NUMBER THEN
      EXPAND_TAC "z" THEN MATCH_MP_TAC CN_CYCLO_ROOT_ALGINT THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[BRIDGE_NF_GEN_IN];
      SIMP_TAC[RING_ORDER_SUBFIELD_GENERATED; BRIDGE_NF_GEN_IN] THEN
      EXPAND_TAC "z" THEN ASM_SIMP_TAC[CN_CYCLO_RING_ORDER];
      MATCH_MP_TAC SUBFIELD_GENERATED_IDEMPOT_GEN THEN
      REWRITE_TAC[SING_SUBSET; BRIDGE_NF_GEN_IN]];
    ALL_TAC] THEN
  EXISTS_TAC
   `group_carrier(galois_group(subfield_generated k {ring_0 k},
                               k:complex ring) I)` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `f:complex->complex` THEN DISCH_TAC THEN CONJ_TAC THENL
     [SUBST1_TAC(SYM(CONJUNCT1(ISPEC `f:complex->complex` I_O_ID))) THEN
      MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN
      EXISTS_TAC `k:complex ring` THEN
      ASM_MESON_TAC[GALOIS_GROUP_RING_HOMOMORPHISM;
                    RING_HOMOMORPHISM_SUBFIELD_INCLUSION];
      MP_TAC(ISPECL [`k:complex ring`; `z:complex`; `q:num`;
                     `f:complex->complex`]
        CYCLOTOMIC_FIELD_GALOIS_GROUP_ROOT) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
      SUBST1_TAC(SYM(ASSUME `subfield_generated complex_ring {z} = k`)) THEN
      REWRITE_TAC[RING_POW_SUBFIELD_GENERATED; COMPLEX_RING_POW] THEN
      EXPAND_TAC "z" THEN SIMP_TAC[CN_CYCLO_ZETA_POW]];
    X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k:complex ring`; `z:complex`; `q:num`]
      CYCLOTOMIC_FIELD_GALOIS_EXTENSION) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP FIXED_FIELD_GALOIS_GROUP) THEN
    REWRITE_TAC[EXTENSION; IN_FIXED_FIELD; IMAGE_I] THEN
    DISCH_THEN(MP_TAC o SPEC `x:complex`) THEN ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(ASSUME `subfield_generated complex_ring {z} = k`)) THEN
    REWRITE_TAC[BRIDGE_NF_PRIME_SUBFIELD; COMPLEX_PRIME_SUBFIELD] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]]);;

let CN_CYCLO_ROOT_IN = prove
 (`!q a. Cx(&1) - cexp(ii * Cx(&2 * pi * &a / &q)) IN
         ring_carrier(subfield_generated complex_ring
                        {cexp(ii * Cx(&2 * pi * &1 / &q))})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM COMPLEX_RING_SUB] THEN
  MATCH_MP_TAC IN_SUBRING_SUB THEN
  SIMP_TAC[SUBRING_SUBFIELD_GENERATED; BRIDGE_NF_SUBFIELD_RATIONAL;
           RATIONAL_NUM] THEN
  MP_TAC(SPECL [`q:num`; `a:num`] CN_CYCLO_ZETA_POW) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SIMP_TAC[BRIDGE_NF_SUBFIELD_CLOSED; BRIDGE_NF_GEN_IN]);;

let CN_CYCLO_HALF_ACTION = prove
 (`!q f c e.
        1 < q /\ coprime(c,q) /\ ~(e = &0) /\
        ring_homomorphism
         (subfield_generated complex_ring {cexp(ii * Cx(&2 * pi * &1 / &q))},
          complex_ring) f /\
        f(cexp(ii * Cx(&2 * pi * &1 / &q))) =
        cexp(ii * Cx(&2 * pi * &c / &q))
        ==> f(cproduct {a | a IN 1..q - 1 /\ qchar q a = e}
                (\a. Cx(&1) - cexp(ii * Cx(&2 * pi * &a / &q)))) =
            cproduct {a | a IN 1..q - 1 /\ qchar q a = qchar q c * e}
              (\a. Cx(&1) - cexp(ii * Cx(&2 * pi * &a / &q)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{cexp(ii * Cx(&2 * pi * &1 / &q))}`; `f:complex->complex`;
                 `{a | a IN 1..q - 1 /\ qchar q a = e}`;
                 `\a. Cx(&1) - cexp(ii * Cx(&2 * pi * &a / &q))`]
    BRIDGE_NF_HOM_CPRODUCT) THEN
  ASM_SIMP_TAC[CN_CYCLO_ROOT_IN; FINITE_RESTRICT; FINITE_NUMSEG] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!a. f(Cx(&1) - cexp(ii * Cx(&2 * pi * &a / &q))) =
        Cx(&1) - cexp(ii * Cx(&2 * pi * &(c * a) / &q))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`subfield_generated complex_ring
                      {cexp(ii * Cx(&2 * pi * &1 / &q))}`;
                   `complex_ring`; `f:complex->complex`]
      RING_HOMOMORPHISM_SUB) THEN
    ASM_REWRITE_TAC[RING_SUB_SUBFIELD_GENERATED; COMPLEX_RING_SUB] THEN
    MP_TAC(SPECL [`q:num`; `a:num`] CN_CYCLO_ZETA_POW) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`Cx(&1)`; `cexp(ii * Cx(&2 * pi * &1 / &q)) pow a`]) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BRIDGE_NF_HOM_CLAUSES) THEN
    ASM_SIMP_TAC[BRIDGE_NF_SUBFIELD_RATIONAL; RATIONAL_NUM; BRIDGE_NF_GEN_IN;
                 BRIDGE_NF_SUBFIELD_CLOSED; CN_CYCLO_ROOT_POW_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. ~(u = &0)
        ==> {a | a IN 1..q - 1 /\ qchar q a = u} =
            {a | a IN {d | coprime(d,q) /\ d < q} /\ qchar q a = u}`
  (fun th -> ASM_SIMP_TAC[th; REAL_ENTIRE; CN_CYCLO_QCHAR_EQ_0]) THENL
   [X_GEN_TAC `u:real` THEN DISCH_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
    X_GEN_TAC `a:num` THEN ASM_CASES_TAC `qchar q a = u` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `coprime(a,q) /\ ~(a = 0)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[CN_CYCLO_QCHAR_EQ_0; COPRIME_0; LT_REFL];
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[cproduct] THEN
  SIMP_TAC[ITERATE_RESTRICT_SET; MONOIDAL_COMPLEX_MUL;
           NEUTRAL_COMPLEX_MUL] THEN
  MP_TAC(BETA_RULE(ISPECL [`( * ):complex->complex->complex`;
                 `\x. if qchar q x = qchar q c * e
                      then Cx(&1) - cexp(ii * Cx(&2 * pi * &x / &q))
                      else Cx(&1)`; `q:num`; `c:num`]
    ITERATE_OVER_COPRIME)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MONOIDAL_COMPLEX_MUL] THEN
    MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `qchar q x = qchar q y` SUBST1_TAC THENL
     [REWRITE_TAC[qchar] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC JACOBI_CONG THEN ASM_REWRITE_TAC[];
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC CN_CYCLO_ROOT_CONG THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; CLASSNO_SERIES_QCHAR_LMUL] THEN
  ASM_SIMP_TAC[REAL_EQ_MUL_LCANCEL; CN_CYCLO_QCHAR_EQ_0]);;

let CN_CYCLO_HALVES_PAIR = prove
 (`!q g. 1 < q /\ g pow 2 = &q /\
         (!n. vsum(0..q - 1)
                (\a. Cx(qchar q a) * cexp(ii * Cx(&2 * pi * &n * &a / &q))) =
              Cx(qchar q n) * Cx g)
         ==> ?x y. rational x /\ rational y /\
                   cproduct {a | a IN 1..q - 1 /\ qchar q a = &1}
                     (\a. Cx(&1) - cexp(ii * Cx(&2 * pi * &a / &q))) =
                   Cx x + Cx y * Cx g /\
                   cproduct {a | a IN 1..q - 1 /\ qchar q a = -- &1}
                     (\a. Cx(&1) - cexp(ii * Cx(&2 * pi * &a / &q))) =
                   Cx x - Cx y * Cx g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!n a. cexp(ii * Cx(&2 * pi * &n * &a / &q)) =
          cexp(ii * Cx(&2 * pi * &n / &q)) pow a`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[CN_CYCLO_ROOT_POW_MUL] THEN REPEAT GEN_TAC THEN
    REPEAT AP_TERM_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_MUL; real_div] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[QCHAR_1; COMPLEX_MUL_LID] o
    SPEC `1`) THEN
  MP_TAC(SPEC `q:num` CN_CYCLO_GALOIS) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:(complex->complex)->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY ABBREV_TAC
   [`U = cproduct {a | a IN 1..q - 1 /\ qchar q a = &1}
           (\a. Cx(&1) - cexp(ii * Cx(&2 * pi * &a / &q)))`;
    `V = cproduct {a | a IN 1..q - 1 /\ qchar q a = -- &1}
           (\a. Cx(&1) - cexp(ii * Cx(&2 * pi * &a / &q)))`] THEN
  SUBGOAL_THEN
   `!x. x IN {U, V, U - V, Cx g}
        ==> x IN ring_carrier(subfield_generated complex_ring
                                {cexp(ii * Cx(&2 * pi * &1 / &q))})`
  MP_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `(!x y. x IN s /\ y IN s ==> f x y IN s) /\
      (u:complex) IN s /\ v IN s /\ w IN s
      ==> !x. x IN {u,v,f u v,w} ==> x IN s`) THEN
    REWRITE_TAC[GSYM COMPLEX_RING_SUB] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_SUBRING_SUB THEN
      ASM_REWRITE_TAC[SUBRING_SUBFIELD_GENERATED];
      EXPAND_TAC "U";
      EXPAND_TAC "V";
      FIRST_ASSUM(SUBST1_TAC o SYM o check ((=) `Cx g` o rand o concl)) THEN
      MATCH_MP_TAC BRIDGE_NF_SUBRING_POLY THEN
      REWRITE_TAC[SUBRING_SUBFIELD_GENERATED; BRIDGE_NF_GEN_IN; qchar;
                  INTEGER_REAL_OF_INT]] THEN
    SIMP_TAC[GSYM COMPLEX_RING_PRODUCT; FINITE_RESTRICT; FINITE_NUMSEG] THEN
    MATCH_MP_TAC IN_SUBRING_PRODUCT THEN
    REWRITE_TAC[SUBRING_SUBFIELD_GENERATED; CN_CYCLO_ROOT_IN];
    REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC] THEN
  SUBGOAL_THEN
   `!f. f IN G
        ==> f(U + V) = U + V /\ f((U - V) * Cx g) = (U - V) * Cx g:complex`
  ASSUME_TAC THENL
   [X_GEN_TAC `f:complex->complex` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(f:complex->complex) IN G`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `c:num` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`q:num`; `f:complex->complex`; `c:num`; `&1`]
      CN_CYCLO_HALF_ACTION) THEN
    MP_TAC(ISPECL [`q:num`; `f:complex->complex`; `c:num`; `-- &1`]
      CN_CYCLO_HALF_ACTION) THEN
    MP_TAC(ISPECL [`{cexp(ii * Cx(&2 * pi * &1 / &q))}`; `f:complex->complex`;
                   `cexp(ii * Cx(&2 * pi * &1 / &q))`; `qchar q`; `q - 1`]
      BRIDGE_NF_HOM_POLY) THEN
    MP_TAC(ISPECL [`subfield_generated complex_ring
                      {cexp(ii * Cx(&2 * pi * &1 / &q))}`;
                   `complex_ring`; `f:complex->complex`]
      RING_HOMOMORPHISM_SUB) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BRIDGE_NF_HOM_CLAUSES) THEN
    ASM_SIMP_TAC[RING_SUB_SUBFIELD_GENERATED; COMPLEX_RING_SUB; QCHAR_1;
                 COMPLEX_MUL_LID; BRIDGE_NF_GEN_IN; CN_CYCLO_QCHAR_RATIONAL;
                 REAL_ARITH `~(&1 = &0) /\ ~(-- &1 = &0)`] THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `qchar q c = &1 \/ qchar q c = -- &1`
     (DISJ_CASES_THEN SUBST1_TAC) THENL
     [MP_TAC(SPECL [`q:num`; `c:num`] CN_CYCLO_QCHAR_CASES) THEN
      ASM_REWRITE_TAC[CN_CYCLO_QCHAR_EQ_0];
      ALL_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_MUL_LID; REAL_MUL_RID; REAL_MUL_LNEG; REAL_NEG_NEG;
                    CX_NEG] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(?r. rational r /\ U + V = Cx r) /\
    (?r. rational r /\ (U - V) * Cx g = Cx r)`
  MP_TAC THENL [ASM_SIMP_TAC[BRIDGE_NF_SUBFIELD_CLOSED]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`r1 / &2`; `r2 / (&2 * &q)`] THEN
  ASM_SIMP_TAC[RATIONAL_CLOSED] THEN
  SUBGOAL_THEN `Cx g pow 2 = Cx(&q) /\ ~(Cx(&q) = Cx(&0))` MP_TAC THENL
   [ASM_REWRITE_TAC[GSYM CX_POW; CX_INJ; REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC;
    MAP_EVERY UNDISCH_TAC
     [`U + V = Cx r1`; `(U - V) * Cx g = Cx r2`] THEN
    REWRITE_TAC[CX_DIV; CX_MUL] THEN CONV_TAC COMPLEX_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* 5. The cyclotomic unit lemma.                                             *)
(* ------------------------------------------------------------------------- *)

let CN_CYCLO_UNIT_QUADRATIC = prove
 (`!q. squarefree q /\ q MOD 4 = 1 /\ 1 < q /\ ~prime q
       ==> ?t u v. integer t /\ rational u /\ rational v /\
                   cyclo_unit q = u + v * sqrt(&q) /\
                   cyclo_unit q pow 2 - t * cyclo_unit q + &1 = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `q:num` CN_CYCLO_GAUSS_REAL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`q:num`; `g:real`] CN_CYCLO_HALVES_PAIR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real` (X_CHOOSE_THEN `y:real`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPEC `q:num` CN_CYCLO_UNIT_RATIO) THEN
  MP_TAC(SPEC `q:num` CN_CYCLO_UNITS_PRODUCT) THEN
  ASM_REWRITE_TAC[CN_CYCLO_SPLIT_UNITS] THEN
  SIMP_TAC[CPRODUCT_UNION; FINITE_RESTRICT; FINITE_NUMSEG;
           CN_CYCLO_SPLIT_UNITS] THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `algebraic_integer(Cx x + Cx y * Cx g) /\
                algebraic_integer(Cx x - Cx y * Cx g)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th] THEN
      MATCH_MP_TAC CN_CYCLO_HALF_ALGINT THEN
      SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG] THEN ASM_ARITH_TAC);
    ALL_TAC] THEN
  SUBGOAL_THEN `(x + y * g) * (x - y * g) = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `(Cx x + Cx y * Cx g) * (Cx x - Cx y * Cx g) = Cx(&1)` THEN
    REWRITE_TAC[GSYM CX_MUL; GSYM CX_ADD; GSYM CX_SUB; CX_INJ];
    ALL_TAC] THEN
  SUBGOAL_THEN `cyclo_unit q = (x - y * g) pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM CX_INJ; CX_POW; CX_SUB; CX_MUL] THEN
    UNDISCH_TAC
     `Cx(cyclo_unit q) * (Cx x + Cx y * Cx g) = Cx x - Cx y * Cx g` THEN
    UNDISCH_TAC `(Cx x + Cx y * Cx g) * (Cx x - Cx y * Cx g) = Cx(&1)` THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  EXISTS_TAC `&2 * (x pow 2 + &q * y pow 2)` THEN
  SUBGOAL_THEN `integer(&2 * (x pow 2 + &q * y pow 2))` ASSUME_TAC THENL
   [MATCH_MP_TAC ALGEBRAIC_INTEGER_RATIONAL THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC RATIONAL_ADD ORELSE MATCH_MP_TAC RATIONAL_MUL ORELSE
             MATCH_MP_TAC RATIONAL_POW ORELSE CONJ_TAC) THEN
      ASM_REWRITE_TAC[RATIONAL_NUM];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `Cx(&2 * (x pow 2 + &q * y pow 2)) =
      (Cx x + Cx y * Cx g) pow 2 + (Cx x - Cx y * Cx g) pow 2`
    SUBST1_TAC THENL
     [UNDISCH_TAC `g pow 2 = &q` THEN
      REWRITE_TAC[GSYM CX_INJ; CX_POW; CX_MUL; CX_ADD] THEN
      CONV_TAC COMPLEX_RING;
      ASM_SIMP_TAC[ALGEBRAIC_INTEGER_ADD; ALGEBRAIC_INTEGER_POW]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((x - y * g) pow 2) pow 2 -
    (&2 * (x pow 2 + &q * y pow 2)) * (x - y * g) pow 2 + &1 = &0`
  ASSUME_TAC THENL
   [UNDISCH_TAC `g pow 2 = &q` THEN
    UNDISCH_TAC `(x + y * g) * (x - y * g) = &1` THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&q) pow 2 = &q` ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POW_2; REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `g = sqrt(&q) \/ g = --sqrt(&q)`
   (DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [MP_TAC(SPEC `g:real` POW_2_SQRT_ABS) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    MAP_EVERY EXISTS_TAC [`x pow 2 + &q * y pow 2`; `--(&2 * x * y)`];
    MAP_EVERY EXISTS_TAC [`x pow 2 + &q * y pow 2`; `&2 * x * y`]] THEN
  (REPEAT CONJ_TAC THENL
    [FIRST_ASSUM ACCEPT_TAC;
     REPEAT(MATCH_MP_TAC RATIONAL_ADD ORELSE MATCH_MP_TAC RATIONAL_MUL ORELSE
            MATCH_MP_TAC RATIONAL_POW ORELSE CONJ_TAC) THEN
     ASM_REWRITE_TAC[RATIONAL_NUM];
     REPEAT(MATCH_MP_TAC RATIONAL_NEG ORELSE MATCH_MP_TAC RATIONAL_MUL ORELSE
            CONJ_TAC) THEN
     ASM_REWRITE_TAC[RATIONAL_NUM];
     UNDISCH_TAC `sqrt(&q) pow 2 = &q` THEN CONV_TAC REAL_RING;
     FIRST_ASSUM ACCEPT_TAC]));;

(* ------------------------------------------------------------------------- *)
(* 6. The bound abs L(1, c) <= log m + 3 for non-principal characters.       *)
(* ------------------------------------------------------------------------- *)

let CNC_HARMONIC_LE_LOG = prove
 (`!n. 1 <= n ==> sum(1..n) (\k. inv(&k)) <= &1 + log(&n)`,
  INDUCT_TAC THEN REWRITE_TAC[ARITH] THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[ARITH; SUM_SING_NUMSEG; LOG_1] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SIMP_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `l0 - l1 <= --x ==> s <= &1 + l0 ==> s + x <= &1 + l1`) THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM LOG_DIV; REAL_ARITH `&0 < x ==> &0 < x + &1`] THEN
  SUBGOAL_THEN `&n / (&n + &1) = &1 + --inv(&n + &1)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < &n` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC LOG_LE_STRONG THEN
  REWRITE_TAC[REAL_ARITH `&0 < &1 + --x <=> x < &1`] THEN
  MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REAL_ARITH_TAC);;

let CNC_VSUM_DIFF_NUMSEG = prove
 (`!f:num->real^N x y.
        x <= y ==> vsum(1..y) f - vsum(1..x) f = vsum(x + 1..y) f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:num->real^N`; `1`; `x:num`; `y - x:num`]
    VSUM_ADD_SPLIT) THEN
  ASM_SIMP_TAC[ARITH_RULE `x <= y ==> x + y - x = y`;
               ARITH_RULE `1 <= x + 1`] THEN
  CONV_TAC VECTOR_ARITH);;

let CNC_DIRICHLET_NORM_VSUM_LE = prove
 (`!m c x y. dirichlet_character m c
             ==> norm(vsum(x + 1..y) c) <= &(y - x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`x + 1..y`; `c:num->complex`; `&1`] VSUM_NORM_BOUND) THEN
  REWRITE_TAC[FINITE_NUMSEG; CARD_NUMSEG; REAL_MUL_RID] THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun th ->
      REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_NORM th]) THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `(y + 1) - (x + 1) = y - x`]]);;

let CNC_DIRICHLET_INTERVAL_SUM = prove
 (`!m c a b. dirichlet_character m c /\ ~(c = chi_0 m) /\ 1 <= a
             ==> norm(vsum(a..b) c) <= &m - &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `c:num->complex`]
    DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &m` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `b < a` THENL
   [ASM_SIMP_TAC[VSUM_TRIV_NUMSEG; NORM_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:num->complex`; `a - 1`; `b:num`] CNC_VSUM_DIFF_NUMSEG) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= a ==> a - 1 + 1 = a`] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ONCE_REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_SUM_MOD
   (CONJ (ASSUME `dirichlet_character m (c:num->complex)`)
         (ASSUME `~(c = chi_0 m)`))] THEN
  SUBGOAL_THEN `b MOD m < m /\ (a - 1) MOD m < m` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MOD_LT_EQ]; ALL_TAC] THEN
  MAP_EVERY ABBREV_TAC [`X = b MOD m`; `Y = (a - 1) MOD m`] THEN
  SUBGOAL_THEN `!z. z < m ==> &z <= &m - &1` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_SUB_LADD; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `Y <= X` THENL
   [ASM_SIMP_TAC[CNC_VSUM_DIFF_NUMSEG] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(X - Y):real` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CNC_DIRICHLET_NORM_VSUM_LE THEN EXISTS_TAC `m:num` THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ONCE_REWRITE_TAC[NORM_SUB] THEN
    ASM_SIMP_TAC[CNC_VSUM_DIFF_NUMSEG; ARITH_RULE `~(Y <= X) ==> X <= Y`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(Y - X):real` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CNC_DIRICHLET_NORM_VSUM_LE THEN EXISTS_TAC `m:num` THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

let CNC_L1_TAIL = prove
 (`!m c. dirichlet_character m c /\ ~(c = chi_0 m)
         ==> norm(Lfunction c - vsum(1..m) (\n. c n / Cx(&n))) <=
             &2 * (&m - &1) / (&m + &1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `c:num->complex`]
    DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:num->complex`; `\n. inv(Cx(&n))`; `&m - &1`; `m + 1`]
    SERIES_DIRICHLET_COMPLEX_VERY_EXPLICIT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_SUB_LT; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      ARITH_TAC;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC CNC_DIRICHLET_INTERVAL_SUM THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      REWRITE_TAC[GSYM CX_INV; REAL_CX; RE_CX; REAL_LE_INV_EQ; REAL_POS];
      REWRITE_TAC[GSYM CX_INV; RE_CX] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `m + 1`) THEN REWRITE_TAC[LE_REFL] THEN
  REWRITE_TAC[GSYM CX_INV; COMPLEX_NORM_CX; REAL_ABS_INV; REAL_ABS_NUM] THEN
  REWRITE_TAC[GSYM complex_div; GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[REAL_ARITH `&2 * b * inv(x) = &2 * b / x`] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
  EXISTS_TAC `\n. vsum(m + 1..n) (\n. c(n) / Cx(&n))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`m:num`; `c:num->complex`] LFUNCTION) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`sequentially`; `vsum (1..m) (\n. c n / Cx (&n))`]
      LIM_CONST) THEN
    REWRITE_TAC[GSYM IMP_CONJ_ALT; sums; FROM_INTER_NUMSEG] THEN
    DISCH_THEN(MP_TAC o MATCH_MP LIM_SUB) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM) THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC LIM_EVENTUALLY THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `m + 1` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `m + 1 <= n ==> m <= n`)) THEN
    SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM] THEN
    SIMP_TAC[VSUM_ADD_SPLIT; ARITH_RULE `1 <= m + 1`] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[complex_div; CX_INV]]);;

let CN_L1_BOUND = prove
 (`!m c. 1 <= m /\ dirichlet_character m c /\ ~(c = chi_0 m)
         ==> norm(Lfunction c) <= log(&m) + &3`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `c:num->complex`] CNC_L1_TAIL) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `m:num` CNC_HARMONIC_LE_LOG) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `norm(vsum(1..m) (\n. c n / Cx(&n))) <= sum(1..m) (\k. inv(&k))`
  MP_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
    REWRITE_TAC[real_div] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
    FIRST_ASSUM(fun th ->
      REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_NORM th]) THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * (&m - &1) / (&m + &1) <= &2` MP_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= &1 ==> &2 * x <= &2`) THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &m + &1`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_ACCEPT_TAC(NORM_ARITH
   `!l s:complex b h g.
        b <= &2 ==> norm s <= h ==> h <= &1 + g ==>
        norm(l - s) <= b ==> norm l <= g + &3`));;
