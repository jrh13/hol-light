(* ========================================================================= *)
(* Feldman Delta-functions, basis polynomials and common multiples.          *)
(*                                                                           *)
(* Purpose: the Delta-functions Delta(z;k) = (z+1)...(z+k)/k!                *)
(* (feldman_delta) and the basis polynomials                                 *)
(* B(z) = Delta(z;a) Delta(z;h)^(b+1), a < h (feldman_basis h a b), used in  *)
(* the auxiliary function instead of the shifts Delta(z + a;h)^(b+1) of      *)
(* Baker (Transcendental Number Theory, Ch. 3): integrality of their         *)
(* normalized derivatives at an integer x after multiplying by N^m, where N  *)
(* is a common multiple of x+1, ..., x+h, and of their values at a rational  *)
(* r/q after multiplying by a power of q; size bounds; the explicit          *)
(* polynomial form, of exact degree a + h(b+1). Common multiples of          *)
(* 1, ..., n of size exp(18 n) (from the Chebyshev bound PSI_BOUND of        *)
(* Examples/mangoldt.ml) and of x+1, ..., x+k of size (exp(19) (x+k)/k)^k,   *)
(* by the Nair divisibility, as in Lemma 1 of Baker. Also higher derivatives *)
(* of products with a linear factor.                                         *)
(*                                                                           *)
(* Main results: feldman_delta, feldman_basis (definitions);                 *)
(*   FELDMAN_DELTA_NUM (binomial values at integers),                        *)
(*   FELDMAN_BASIS_DERIV_INTEGER, FELDMAN_BASIS_RATIONAL,                    *)
(*   FELDMAN_BASIS_POLYFUN, FELDMAN_BASIS_DERIV_BOUND_UNIFORM,               *)
(*   FELDMAN_BASIS_CPRODUCT, HOLOMORPHIC_ON_FELDMAN_BASIS;                   *)
(*   NUMSEG_COMMON_MULTIPLE, SHIFTED_COMMON_MULTIPLE_BOUND;                  *)
(*   CPRODUCT_LINEAR_DERIVATIVE_INTEGER_GEN (normalized derivatives of       *)
(*   products of linear factors at any point) and its case                   *)
(*   CPRODUCT_LINEAR_DERIVATIVE_INTEGER at integers;                         *)
(*   HIGHER_COMPLEX_DERIVATIVE_MUL_SUB_FACTOR, its case                      *)
(*   HIGHER_COMPLEX_DERIVATIVE_MUL_LINEAR_FACTOR on C,                       *)
(*   HIGHER_COMPLEX_DERIVATIVE_LMUL; NPRODUCT_SHIFT_BINOM, BINOM_LE_EXP.     *)
(*                                                                           *)
(* Uses: Baker/prelim.ml (complex integers), Baker/algebraic.ml              *)
(*   (CPRODUCT_LINEAR_POLYFUN); PSI_BOUND of Examples/mangoldt.ml;           *)
(*   factorial_lower_bound and binom_rowsum_partial of                       *)
(*   100/transcendence.ml.                                                   *)
(* ========================================================================= *)

needs "Baker/algebraic.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Elementary arithmetic: shifted factorials, a Legendre-type bound and the  *)
(* divisibility of q^h (r + q)(r + 2q)...(r + hq) by h!.                     *)
(* ------------------------------------------------------------------------- *)

let FACT_MUL_NPRODUCT_SHIFT = prove
 (`!s h. FACT s * nproduct(1..h) (\j. s + j) = FACT(s + h)`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[NPRODUCT_CLAUSES_NUMSEG; ADD_CLAUSES; MULT_CLAUSES;
                  ARITH_RULE `1 <= SUC h`; FACT; ARITH] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CONV_TAC NUM_RING);;

let NPRODUCT_SHIFT_BINOM = prove
 (`!s h. nproduct(1..h) (\j. s + j) = FACT h * binom(s + h,h)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(MESON[FACT_NZ; EQ_MULT_LCANCEL]
   `FACT s * x = FACT s * y ==> x = y`) THEN
  REWRITE_TAC[FACT_MUL_NPRODUCT_SHIFT; MULT_ASSOC; BINOM_FACT]);;

let BINOM_LE_EXP = prove
 (`!n k. binom(n,k) <= 2 EXP n`,
  REPEAT GEN_TAC THEN MP_TAC(SPECL [`n:num`; `k:num`] binom_rowsum_partial) THEN
  MATCH_MP_TAC(ARITH_RULE `a <= b ==> b <= c ==> a <= c`) THEN
  MP_TAC(ISPECL [`{k:num}`; `0..k`; `\i. binom(n,i)`] NSUM_SUBSET_SIMPLE) THEN
  REWRITE_TAC[FINITE_NUMSEG; SING_SUBSET; IN_NUMSEG; LE_0; LE_REFL;
              NSUM_SING]);;

let NSUM_DIV_EXP_2_LE = prove
 (`!m n. nsum(1..m) (\j. n DIV 2 EXP j) + n DIV 2 EXP m <= n`,
  INDUCT_TAC THEN
  REWRITE_TAC[NSUM_CLAUSES_NUMSEG; EXP; DIV_1; ADD_CLAUSES; LE_REFL; ARITH] THEN
  REWRITE_TAC[ARITH_RULE `1 <= SUC m`] THEN GEN_TAC THEN
  SUBGOAL_THEN `n DIV (2 * 2 EXP m) = (n DIV 2 EXP m) DIV 2` SUBST1_TAC THENL
   [REWRITE_TAC[DIV_DIV] THEN AP_TERM_TAC THEN REWRITE_TAC[MULT_SYM];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  MP_TAC(SPECL [`n DIV 2 EXP m`; `2`] DIVISION) THEN ARITH_TAC);;

let INDEX_FACT_LE = prove
 (`!p n. prime p ==> index p (FACT n) <= n`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[INDEX_FACT_ALT] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
  TRANS_TAC LE_TRANS `nsum(1..n) (\j. n DIV 2 EXP j)` THEN CONJ_TAC THENL
   [TRANS_TAC LE_TRANS `nsum {j | 1 <= j /\ p EXP j <= n} (\j. n DIV 2 EXP j)`
    THEN CONJ_TAC THENL
     [MATCH_MP_TAC NSUM_LE THEN REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `1..n` THEN
        REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN
        X_GEN_TAC `j:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        TRANS_TAC LE_TRANS `p EXP j` THEN ASM_REWRITE_TAC[] THEN
        TRANS_TAC LE_TRANS `2 EXP j` THEN
        ASM_SIMP_TAC[LT_IMP_LE; LT_POW2_REFL; EXP_MONO_LE_IMP];
        X_GEN_TAC `j:num` THEN STRIP_TAC THEN MATCH_MP_TAC DIV_MONO2 THEN
        ASM_SIMP_TAC[EXP_EQ_0; ARITH_EQ; EXP_MONO_LE_IMP]];
      MATCH_MP_TAC NSUM_SUBSET_SIMPLE THEN
      REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      TRANS_TAC LE_TRANS `p EXP j` THEN ASM_REWRITE_TAC[] THEN
      TRANS_TAC LE_TRANS `2 EXP j` THEN
      ASM_SIMP_TAC[LT_IMP_LE; LT_POW2_REFL; EXP_MONO_LE_IMP]];
    MP_TAC(SPECL [`n:num`; `n:num`] NSUM_DIV_EXP_2_LE) THEN ARITH_TAC]);;

let FACT_DIVIDES_NPRODUCT_AP = prove
 (`!q r h. FACT h divides q EXP h * nproduct(1..h) (\j. r + q * j)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `q = 0` THENL
   [ASM_REWRITE_TAC[EXP_ZERO] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[FACT; MULT_CLAUSES; DIVIDES_1; DIVIDES_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(q EXP h * nproduct(1..h) (\j. r + q * j) = 0)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MULT_EQ_0; EXP_EQ_0; NPRODUCT_EQ_0_NUMSEG; ADD_EQ_0] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[DIVIDES_INDEX] THEN ASM_REWRITE_TAC[FACT_NZ] THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`q EXP h * nproduct(1..h) (\j. r + q * j)`; `p:num`;
                `index p (FACT h)`] PRIMEPOW_DIVIDES_INDEX) THEN
  ASM_SIMP_TAC[PRIME_IMP_NZ; ARITH_RULE `2 <= p ==> ~(p = 1)`; PRIME_GE_2] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_CASES_TAC `p divides q` THENL
   [MATCH_MP_TAC DIVIDES_RMUL THEN MATCH_MP_TAC DIVIDES_TRANS THEN
    EXISTS_TAC `p EXP h` THEN
    ASM_SIMP_TAC[DIVIDES_EXP; DIVIDES_EXP_LE_IMP; INDEX_FACT_LE];
    MATCH_MP_TAC DIVIDES_LMUL] THEN
  SUBGOAL_THEN `coprime(q,p EXP index p (FACT h))` MP_TAC THENL
   [MATCH_MP_TAC COPRIME_EXP THEN ONCE_REWRITE_TAC[COPRIME_SYM] THEN
    ASM_SIMP_TAC[PRIME_COPRIME_EQ];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `r:num` o MATCH_MP CONG_SOLVE) THEN
  DISCH_THEN(X_CHOOSE_TAC `s:num`) THEN
  MP_TAC(ISPECL [`p EXP index p (FACT h)`; `\j. r + q * j`;
                 `\j. q * (s + j)`; `1..h`] CONG_NPRODUCT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    UNDISCH_TAC `(q * s == r) (mod (p EXP index p (FACT h)))` THEN
    REWRITE_TAC[] THEN MATCH_ACCEPT_TAC(NUMBER_RULE
     `!n q s r j:num. (q * s == r) (mod n)
                      ==> (r + q * j == q * (s + j)) (mod n)`);
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP CONG_DIVIDES th])] THEN
  SIMP_TAC[NPRODUCT_MUL; FINITE_NUMSEG; NPRODUCT_CONST_NUMSEG_1] THEN
  MATCH_MP_TAC DIVIDES_LMUL THEN REWRITE_TAC[NPRODUCT_SHIFT_BINOM] THEN
  MATCH_MP_TAC DIVIDES_RMUL THEN REWRITE_TAC[EXP_INDEX_DIVIDES]);;

(* ------------------------------------------------------------------------- *)
(* Higher derivatives of products with a linear factor and of multiples.     *)
(* ------------------------------------------------------------------------- *)

let HIGHER_COMPLEX_DERIVATIVE_ID_ADD_CONST = prove
 (`!c i z. higher_complex_derivative i (\w. w + c) z =
           if i = 0 then z + c else if i = 1 then Cx(&1) else Cx(&0)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\w:complex. w`; `\w:complex. c:complex`; `(:complex)`;
                 `i:num`; `z:complex`] HIGHER_COMPLEX_DERIVATIVE_ADD) THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV; HOLOMORPHIC_ON_ID; HOLOMORPHIC_ON_CONST] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[HIGHER_COMPLEX_DERIVATIVE_ID;
              HIGHER_COMPLEX_DERIVATIVE_CONST] THEN
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[COMPLEX_ADD_RID]);;

let HIGHER_COMPLEX_DERIVATIVE_ID_SUB_CONST = prove
 (`!a i z. higher_complex_derivative i (\w. w - a) z =
           if i = 0 then z - a else if i = 1 then Cx(&1) else Cx(&0)`,
  REWRITE_TAC[complex_sub; HIGHER_COMPLEX_DERIVATIVE_ID_ADD_CONST]);;

let HIGHER_COMPLEX_DERIVATIVE_MUL_SUB_FACTOR = prove
 (`!g s a n z.
        open s /\ g holomorphic_on s /\ z IN s
        ==> higher_complex_derivative (SUC n) (\w. (w - a) * g w) z =
            (z - a) * higher_complex_derivative (SUC n) g z +
            Cx(&(SUC n)) * higher_complex_derivative n g z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\w:complex. w - a`; `g:complex->complex`; `s:complex->bool`;
                 `SUC n`; `z:complex`] HIGHER_COMPLEX_DERIVATIVE_MUL) THEN
  ASM_SIMP_TAC[HOLOMORPHIC_ON_SUB; HOLOMORPHIC_ON_ID; HOLOMORPHIC_ON_CONST] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[HIGHER_COMPLEX_DERIVATIVE_ID_SUB_CONST] THEN
  SIMP_TAC[VSUM_CLAUSES_LEFT; LE_0] THEN
  SUBGOAL_THEN `0 + 1 <= SUC n`
   (fun th -> SIMP_TAC[MATCH_MP VSUM_CLAUSES_LEFT th])
  THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH; BINOM_REFL; binom; COMPLEX_MUL_LID; SUB_0; BINOM_1] THEN
  REWRITE_TAC[ARITH_RULE `SUC n - 1 = n`] THEN
  MATCH_MP_TAC(COMPLEX_RING `s = Cx(&0) ==> p + q + s = p + q`) THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN MATCH_MP_TAC VSUM_EQ_0 THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `2 <= i ==> ~(i = 0) /\ ~(i = 1)`] THEN
  REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO; COMPLEX_VEC_0]);;

let HIGHER_COMPLEX_DERIVATIVE_MUL_LINEAR_FACTOR = prove
 (`!g c m z.
        g holomorphic_on (:complex)
        ==> higher_complex_derivative m (\w. (w + c) * g w) z =
            (z + c) * higher_complex_derivative m g z +
            Cx(&m) * higher_complex_derivative (m - 1) g z`,
  REPEAT STRIP_TAC THEN STRUCT_CASES_TAC(SPEC `m:num` num_CASES) THENL
   [REWRITE_TAC[higher_complex_derivative; COMPLEX_MUL_LZERO;
                COMPLEX_ADD_RID];
    MP_TAC(ISPECL [`g:complex->complex`; `(:complex)`; `--c:complex`;
                   `n:num`; `z:complex`]
      HIGHER_COMPLEX_DERIVATIVE_MUL_SUB_FACTOR) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; COMPLEX_SUB_RNEG; SUC_SUB1]]);;

let HIGHER_COMPLEX_DERIVATIVE_LMUL = prove
 (`!f c s n z.
        open s /\ f holomorphic_on s /\ z IN s
        ==> higher_complex_derivative n (\w. c * f w) z =
            c * higher_complex_derivative n f z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\w:complex. c:complex`; `f:complex->complex`;
                 `s:complex->bool`; `n:num`; `z:complex`]
         HIGHER_COMPLEX_DERIVATIVE_MUL) THEN
  ASM_REWRITE_TAC[HOLOMORPHIC_ON_CONST] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[HIGHER_COMPLEX_DERIVATIVE_CONST] THEN
  SIMP_TAC[VSUM_CLAUSES_LEFT; LE_0] THEN
  REWRITE_TAC[binom; SUB_0; COMPLEX_MUL_LID] THEN
  MATCH_MP_TAC(COMPLEX_RING `s = Cx(&0) ==> p + s = p`) THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN MATCH_MP_TAC VSUM_EQ_0 THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `0 + 1 <= i ==> ~(i = 0)`] THEN
  REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO; COMPLEX_VEC_0]);;

(* ------------------------------------------------------------------------- *)
(* Integrality of normalized derivatives of products of linear factors       *)
(* z + c u at a point x, after multiplying by M^m where every M / (x + c u)  *)
(* is a complex integer, and dividing by the value of the product; the case  *)
(* of an integer x and a common multiple N of all x + c u.                   *)
(* ------------------------------------------------------------------------- *)

let CPRODUCT_LINEAR_DERIVATIVE_INTEGER_LEMMA = prove
 (`!nm fm nn np f1 mm y q d0 d1 p.
        ~(y = Cx(&0)) /\ ~(p = Cx(&0)) /\ ~(f1 = Cx(&0)) /\ ~(mm = Cx(&0)) /\
        nn = y * q /\ nm = nn * np /\ fm = mm * f1
        ==> nm * (y * d0 + mm * d1) / (fm * y * p) =
            nm * d0 / (fm * p) + q * (np * d1 / (f1 * p))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(y = Cx(&0))` THEN UNDISCH_TAC `~(p = Cx(&0))` THEN
  UNDISCH_TAC `~(f1 = Cx(&0))` THEN UNDISCH_TAC `~(mm = Cx(&0))` THEN
  CONV_TAC COMPLEX_FIELD);;

let CPRODUCT_LINEAR_DERIVATIVE_INTEGER_GEN = prove
 (`!U (c:A->num) x M.
        FINITE U /\
        (!u. u IN U ==> ~(x + Cx(&(c u)) = Cx(&0)) /\
                        complex_integer(M / (x + Cx(&(c u)))))
        ==> !m. complex_integer
                 (M pow m *
                  higher_complex_derivative m
                    (\z. cproduct U (\u. z + Cx(&(c u)))) x /
                  (Cx(&(FACT m)) * cproduct U (\u. x + Cx(&(c u)))))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN SPEC_TAC(`U:A->bool`,`U:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[NOT_IN_EMPTY; CPRODUCT_CLAUSES;
                HIGHER_COMPLEX_DERIVATIVE_CONST] THEN
    X_GEN_TAC `m:num` THEN ASM_CASES_TAC `m = 0` THEN
    ASM_REWRITE_TAC[complex_pow; FACT; COMPLEX_MUL_LID; COMPLEX_DIV_1;
                    COMPLEX_INTEGER_CX_NUM; complex_div; COMPLEX_MUL_LZERO;
                    COMPLEX_MUL_RZERO; COMPLEX_INV_1];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `U:A->bool`] THEN STRIP_TAC THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[CPRODUCT_CLAUSES] THEN X_GEN_TAC `m:num` THEN
  SUBGOAL_THEN
   `(\z. cproduct U (\u. z + Cx(&((c:A->num) u)))) holomorphic_on (:complex)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_CPRODUCT THEN
    ASM_SIMP_TAC[HOLOMORPHIC_ON_ADD; HOLOMORPHIC_ON_ID; HOLOMORPHIC_ON_CONST];
    ALL_TAC] THEN
  ASM_SIMP_TAC[HIGHER_COMPLEX_DERIVATIVE_MUL_LINEAR_FACTOR] THEN
  SUBGOAL_THEN `~(cproduct U (\u. x + Cx(&((c:A->num) u))) = Cx(&0))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[CPRODUCT_EQ_0] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM((fun th -> MP_TAC(SPEC `m - 1` th) THEN
                         MP_TAC(SPEC `m:num` th)) o
              check (is_forall o concl)) THEN
  ABBREV_TAC
   `D0 = higher_complex_derivative m
          (\z. cproduct U (\u. z + Cx(&((c:A->num) u)))) x` THEN
  ABBREV_TAC
   `D1 = higher_complex_derivative (m - 1)
          (\z. cproduct U (\u. z + Cx(&((c:A->num) u)))) x` THEN
  ABBREV_TAC `P = cproduct U (\u. x + Cx(&((c:A->num) u)))` THEN
  ABBREV_TAC `y = x + Cx(&((c:A->num) a))` THEN
  REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `m = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    UNDISCH_TAC
     `complex_integer((M:complex) pow 0 * D0 / (Cx(&(FACT 0)) * P))` THEN
    MATCH_MP_TAC(MESON[]
     `x = y ==> complex_integer x ==> complex_integer y`) THEN
    REWRITE_TAC[complex_pow; FACT; COMPLEX_MUL_LZERO; COMPLEX_ADD_RID] THEN
    UNDISCH_TAC `~(y = Cx(&0))` THEN
    UNDISCH_TAC `~(P = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(M:complex) pow m`; `Cx(&(FACT m))`; `M:complex`;
    `(M:complex) pow (m - 1)`; `Cx(&(FACT(m - 1)))`; `Cx(&m)`; `y:complex`;
    `(M:complex) / y`; `D0:complex`; `D1:complex`; `P:complex`]
   CPRODUCT_LINEAR_DERIVATIVE_INTEGER_LEMMA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ; FACT_NZ] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `~(y = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD;
      ASM_SIMP_TAC[GSYM(CONJUNCT2 complex_pow);
                   ARITH_RULE `~(m = 0) ==> SUC(m - 1) = m`];
      REWRITE_TAC[GSYM CX_MUL; REAL_OF_NUM_MUL] THEN
      MP_TAC(SPEC `m - 1` (CONJUNCT2 FACT)) THEN
      ASM_SIMP_TAC[ARITH_RULE `~(m = 0) ==> SUC(m - 1) = m`]];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC COMPLEX_INTEGER_ADD THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC COMPLEX_INTEGER_MUL THEN ASM_REWRITE_TAC[]);;

let CPRODUCT_LINEAR_DERIVATIVE_INTEGER = prove
 (`!U (c:A->num) x N.
        FINITE U /\ (!u. u IN U ==> ~(x + c u = 0) /\ (x + c u) divides N)
        ==> !m. complex_integer
                 (Cx(&N) pow m *
                  higher_complex_derivative m
                    (\z. cproduct U (\u. z + Cx(&(c u)))) (Cx(&x)) /
                  (Cx(&(FACT m)) * cproduct U (\u. Cx(&x) + Cx(&(c u)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CPRODUCT_LINEAR_DERIVATIVE_INTEGER_GEN THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `u:A`) THEN ASM_REWRITE_TAC[divides] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `q:num` SUBST1_TAC)) THEN
  SUBGOAL_THEN `~(Cx(&x) + Cx(&((c:A->num) u)) = Cx(&0))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM CX_ADD; CX_INJ; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `Cx(&((x + (c:A->num) u) * q)) / (Cx(&x) + Cx(&(c u))) = Cx(&q)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD; CX_MUL; CX_ADD] THEN
    UNDISCH_TAC `~(Cx(&x) + Cx(&((c:A->num) u)) = Cx(&0))` THEN
    CONV_TAC COMPLEX_FIELD;
    REWRITE_TAC[COMPLEX_INTEGER_CX_NUM]]);;

(* ------------------------------------------------------------------------- *)
(* The Feldman Delta-functions, integrality at integers and rationals, and   *)
(* size bounds.                                                              *)
(* ------------------------------------------------------------------------- *)

let feldman_delta = new_definition
 `feldman_delta k z = cproduct(1..k) (\j. z + Cx(&j)) / Cx(&(FACT k))`;;

let HOLOMORPHIC_ON_FELDMAN_DELTA = prove
 (`!k s. feldman_delta k holomorphic_on s`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `feldman_delta k =
    \z. cproduct(1..k) (\j. z + Cx(&j)) * inv(Cx(&(FACT k)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; feldman_delta; complex_div]; ALL_TAC] THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN REWRITE_TAC[HOLOMORPHIC_ON_CONST] THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_CPRODUCT THEN
  SIMP_TAC[FINITE_NUMSEG; HOLOMORPHIC_ON_ADD; HOLOMORPHIC_ON_ID;
           HOLOMORPHIC_ON_CONST]);;

let HOLOMORPHIC_ON_FELDMAN_DELTA_POW = prove
 (`!k l s. (\w. feldman_delta k w pow l) holomorphic_on s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HOLOMORPHIC_ON_POW THEN
  REWRITE_TAC[ETA_AX; HOLOMORPHIC_ON_FELDMAN_DELTA]);;

let FELDMAN_DELTA_NUM = prove
 (`!k x. feldman_delta k (Cx(&x)) = Cx(&(binom(x + k,k)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[feldman_delta; GSYM CX_ADD; REAL_OF_NUM_ADD] THEN
  SIMP_TAC[GSYM CX_PRODUCT; FINITE_NUMSEG; GSYM REAL_OF_NUM_NPRODUCT] THEN
  REWRITE_TAC[NPRODUCT_SHIFT_BINOM; GSYM REAL_OF_NUM_MUL; CX_MUL] THEN
  MATCH_MP_TAC(COMPLEX_FIELD `~(a = Cx(&0)) ==> (a * b) / a = b`) THEN
  REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ; FACT_NZ]);;

let FELDMAN_DELTA_POW_CPRODUCT = prove
 (`!k l w. feldman_delta k w pow l =
           cproduct ((1..l) CROSS (1..k)) (\u. w + Cx(&(SND u))) /
           Cx(&(FACT k)) pow l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[feldman_delta; COMPLEX_POW_DIV] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`cproduct(1..k) (\j. w + Cx(&j))`; `1`; `l:num`]
         CPRODUCT_CONST_NUMSEG) THEN
  REWRITE_TAC[ADD_SUB] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[cproduct; CROSS] THEN
  SIMP_TAC[MATCH_MP ITERATE_ITERATE_PRODUCT MONOIDAL_COMPLEX_MUL;
           FINITE_NUMSEG] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM]);;

let FELDMAN_DELTA_BOUND = prove
 (`!k z n. norm z <= &n ==> norm(feldman_delta k z) <= &2 pow (n + k)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[feldman_delta; COMPLEX_NORM_DIV; COMPLEX_NORM_CX;
              REAL_ABS_NUM] THEN
  SIMP_TAC[NORM_CPRODUCT; FINITE_NUMSEG] THEN
  TRANS_TAC REAL_LE_TRANS `product(1..k) (\j. &n + &j) / &(FACT k)` THEN
  CONJ_TAC THENL
   [SIMP_TAC[REAL_LE_DIV2_EQ; REAL_OF_NUM_LT; FACT_LT] THEN
    MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(z:complex) <= n /\ norm(w:complex) = j
      ==> norm(z + w) <= n + j`) THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_NPRODUCT; FINITE_NUMSEG] THEN
  REWRITE_TAC[NPRODUCT_SHIFT_BINOM; GSYM REAL_OF_NUM_MUL] THEN
  SIMP_TAC[REAL_FIELD `~(a = &0) ==> (a * b) / a = b`; REAL_OF_NUM_EQ;
           FACT_NZ] THEN
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; BINOM_LE_EXP]);;

let FELDMAN_DELTA_RATIONAL = prove
 (`!h q r. ~(q = 0)
           ==> complex_integer
                (Cx(&q) pow (2 * h) * feldman_delta h (Cx(&r) / Cx(&q)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`q:num`; `r:num`; `h:num`] FACT_DIVIDES_NPRODUCT_AP) THEN
  REWRITE_TAC[divides] THEN DISCH_THEN(X_CHOOSE_TAC `d:num`) THEN
  SUBGOAL_THEN
   `Cx(&q) pow (2 * h) * feldman_delta h (Cx(&r) / Cx(&q)) = Cx(&d)`
   (fun th -> REWRITE_TAC[th; COMPLEX_INTEGER_CX_NUM]) THEN
  SUBGOAL_THEN
   `Cx(&q) pow h * cproduct(1..h) (\j. Cx(&r) / Cx(&q) + Cx(&j)) =
    Cx(&(nproduct(1..h) (\j. r + q * j)))`
  ASSUME_TAC THENL
   [SIMP_TAC[REAL_OF_NUM_NPRODUCT; FINITE_NUMSEG; CX_PRODUCT] THEN
    SUBGOAL_THEN `Cx(&q) pow h = cproduct(1..h) (\j. Cx(&q))` SUBST1_TAC
    THENL [REWRITE_TAC[CPRODUCT_CONST_NUMSEG; ADD_SUB]; ALL_TAC] THEN
    SIMP_TAC[GSYM CPRODUCT_MUL; FINITE_NUMSEG] THEN
    MATCH_MP_TAC CPRODUCT_EQ THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL; CX_ADD; CX_MUL] THEN
    UNDISCH_TAC `~(q = 0)` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM CX_INJ] THEN
    CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[feldman_delta; MULT_2; COMPLEX_POW_ADD] THEN
  MATCH_MP_TAC(COMPLEX_FIELD
   `!x p c f d n. ~(f = Cx(&0)) /\ p * c = n /\ x * n = f * d
                  ==> (x * p) * c / f = d`) THEN
  EXISTS_TAC `Cx(&(nproduct(1..h) (\j. r + q * j)))` THEN
  ASM_REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ; FACT_NZ] THEN
  ASM_REWRITE_TAC[GSYM CX_MUL; GSYM CX_POW; REAL_OF_NUM_MUL; REAL_OF_NUM_POW]);;

(* ------------------------------------------------------------------------- *)
(* The basis polynomials Delta(z;a) Delta(z;h)^(b+1), 0 <= a < h, used in    *)
(* the auxiliary function instead of Baker shifts Delta(z + a;h)^(b+1): all  *)
(* linear factors are z + 1, ..., z + h, and the degrees a + h(b+1) are      *)
(* pairwise distinct, which makes them trivially linearly independent.       *)
(* ------------------------------------------------------------------------- *)

let CPRODUCT_LINEAR_NORMALIZED_DERIV_INTEGER = prove
 (`!U (c:A->num) x N K.
        FINITE U /\ ~(K = 0) /\
        (!u. u IN U ==> ~(x + c u = 0) /\ (x + c u) divides N) /\
        complex_integer(cproduct U (\u. Cx(&x) + Cx(&(c u))) / Cx(&K))
        ==> !m. complex_integer
                 (Cx(&N) pow m *
                  higher_complex_derivative m
                    (\w. cproduct U (\u. w + Cx(&(c u))) / Cx(&K)) (Cx(&x)) /
                  Cx(&(FACT m)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:A->bool`; `c:A->num`; `x:num`; `N:num`]
         CPRODUCT_LINEAR_DERIVATIVE_INTEGER) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `m:num`) THEN
  MP_TAC(ISPECL
   [`\z. cproduct U (\u. z + Cx(&((c:A->num) u)))`; `inv(Cx(&K))`;
    `(:complex)`; `m:num`; `Cx(&x)`] HIGHER_COMPLEX_DERIVATIVE_LMUL) THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN ANTS_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_CPRODUCT THEN
    ASM_SIMP_TAC[HOLOMORPHIC_ON_ADD; HOLOMORPHIC_ON_ID; HOLOMORPHIC_ON_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\w. cproduct U (\u. w + Cx(&((c:A->num) u))) / Cx(&K)) =
    (\w. inv(Cx(&K)) * cproduct U (\u. w + Cx(&(c u))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; complex_div; COMPLEX_MUL_SYM]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC
   `D = higher_complex_derivative m
         (\z. cproduct U (\u. z + Cx(&((c:A->num) u)))) (Cx(&x))` THEN
  ABBREV_TAC `P = cproduct U (\u. Cx(&x) + Cx(&((c:A->num) u)))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~(P = Cx(&0))` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN
    ASM_SIMP_TAC[CPRODUCT_EQ_0; GSYM CX_ADD; CX_INJ; REAL_OF_NUM_ADD;
                 REAL_OF_NUM_EQ] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[]
   `!y. complex_integer y /\ x = y ==> complex_integer x`) THEN
  EXISTS_TAC `(Cx(&N) pow m * D / (Cx(&(FACT m)) * P)) * (P / Cx(&K))` THEN
  ASM_SIMP_TAC[COMPLEX_INTEGER_MUL] THEN
  UNDISCH_TAC `~(P = Cx(&0))` THEN
  MP_TAC(SPEC `m:num` FACT_NZ) THEN UNDISCH_TAC `~(K = 0)` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM CX_INJ] THEN
  CONV_TAC COMPLEX_FIELD);;

let feldman_basis = new_definition
 `feldman_basis h a b z = feldman_delta a z * feldman_delta h z pow (b + 1)`;;

let FELDMAN_BASIS_CPRODUCT = prove
 (`!h a b w.
        feldman_basis h a b w =
        cproduct (({0} CROSS (1..a)) UNION ((1..b+1) CROSS (1..h)))
                 (\u. w + Cx(&(SND u))) /
        Cx(&(FACT a * FACT h EXP (b + 1)))`,
  REPEAT GEN_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CPRODUCT_UNION o
    lhand o rand o snd) THEN
  SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG; FINITE_SING] THEN ANTS_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; FORALL_PAIR_THM;
                IN_CROSS; IN_SING; IN_NUMSEG] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `{0} CROSS (1..a) = IMAGE (\j. (0,j)) (1..a)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_CROSS; IN_SING; IN_IMAGE;
                PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[CPRODUCT_IMAGE; PAIR_EQ; o_DEF] THEN
  REWRITE_TAC[feldman_basis; FELDMAN_DELTA_POW_CPRODUCT] THEN
  REWRITE_TAC[feldman_delta; GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW;
              CX_MUL; CX_POW] THEN
  MP_TAC(SPEC `a:num` FACT_NZ) THEN MP_TAC(SPEC `h:num` FACT_NZ) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM CX_INJ] THEN
  SPEC_TAC(`Cx(&(FACT h))`,`fh:complex`) THEN
  SPEC_TAC(`Cx(&(FACT a))`,`fa:complex`) THEN REPEAT GEN_TAC THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `~(fh pow (b + 1) = Cx(&0))` MP_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_POW_EQ_0]; ALL_TAC] THEN
  UNDISCH_TAC `~(fa = Cx(&0))` THEN
  SPEC_TAC(`cproduct (1..a) (\j. w + Cx(&j))`,`p1:complex`) THEN
  SPEC_TAC(`cproduct ((1..b + 1) CROSS (1..h)) (\u. w + Cx(&(SND u)))`,
           `p2:complex`) THEN
  CONV_TAC COMPLEX_FIELD);;

let HOLOMORPHIC_ON_FELDMAN_BASIS = prove
 (`!h a b s. feldman_basis h a b holomorphic_on s`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `feldman_basis h a b =
    \z. feldman_delta a z * feldman_delta h z pow (b + 1)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; feldman_basis]; ALL_TAC] THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN
  REWRITE_TAC[ETA_AX; HOLOMORPHIC_ON_FELDMAN_DELTA;
              HOLOMORPHIC_ON_FELDMAN_DELTA_POW]);;

let FELDMAN_BASIS_NUM = prove
 (`!h a b x. feldman_basis h a b (Cx(&x)) =
             Cx(&(binom(x + a,a) * binom(x + h,h) EXP (b + 1)))`,
  REWRITE_TAC[feldman_basis; FELDMAN_DELTA_NUM; GSYM REAL_OF_NUM_MUL;
              GSYM REAL_OF_NUM_POW; CX_MUL; CX_POW]);;

let FELDMAN_BASIS_DERIV_INTEGER = prove
 (`!h a b x N.
        a <= h /\ (!i. 1 <= i /\ i <= h ==> (x + i) divides N)
        ==> !m. complex_integer
                 (Cx(&N) pow m *
                  higher_complex_derivative m (feldman_basis h a b) (Cx(&x)) /
                  Cx(&(FACT m)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `feldman_basis h a b =
    \w. cproduct (({0} CROSS (1..a)) UNION ((1..b+1) CROSS (1..h)))
                 (\u. w + Cx(&(SND u))) /
        Cx(&(FACT a * FACT h EXP (b + 1)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; FELDMAN_BASIS_CPRODUCT]; ALL_TAC] THEN
  MATCH_MP_TAC CPRODUCT_LINEAR_NORMALIZED_DERIV_INTEGER THEN
  REWRITE_TAC[GSYM FELDMAN_BASIS_CPRODUCT; FELDMAN_BASIS_NUM;
              COMPLEX_INTEGER_CX_NUM; MULT_EQ_0; EXP_EQ_0; FACT_NZ] THEN
  SIMP_TAC[FINITE_UNION; FINITE_CROSS; FINITE_NUMSEG; FINITE_SING] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_UNION; IN_CROSS; IN_SING; IN_NUMSEG] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (CONJ_TAC THENL [ASM_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC] THEN
   ASM_ARITH_TAC));;

let FELDMAN_BASIS_BOUND = prove
 (`!h a b z n.
        norm z <= &n
        ==> norm(feldman_basis h a b z) <=
            &2 pow ((n + a) + (b + 1) * (n + h))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[feldman_basis; COMPLEX_NORM_MUL; COMPLEX_NORM_POW] THEN
  SUBGOAL_THEN
   `&2 pow ((n + a) + (b + 1) * (n + h)) =
    &2 pow (n + a) * (&2 pow (n + h)) pow (b + 1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_POW; GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_SIMP_TAC[NORM_POS_LE; REAL_POW_LE; FELDMAN_DELTA_BOUND] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN
  ASM_SIMP_TAC[NORM_POS_LE; FELDMAN_DELTA_BOUND]);;

let FELDMAN_BASIS_DERIV_BOUND = prove
 (`!h a b m z n.
        norm z + &1 <= &n
        ==> norm(higher_complex_derivative m (feldman_basis h a b) z /
                 Cx(&(FACT m))) <= &2 pow ((n + a) + (b + 1) * (n + h))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; FACT_LT] THEN
  MP_TAC(ISPECL [`feldman_basis h a b`; `z:complex`; `&1`;
                 `&2 pow ((n + a) + (b + 1) * (n + h))`; `m:num`]
         CAUCHY_INEQUALITY) THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_DIV_1; REAL_LT_01] THEN
  SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON; HOLOMORPHIC_ON_FELDMAN_BASIS] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
    MATCH_MP_TAC FELDMAN_BASIS_BOUND THEN
    UNDISCH_TAC `norm(z - w:complex) = &1` THEN
    UNDISCH_TAC `norm(z:complex) + &1 <= &n` THEN NORM_ARITH_TAC;
    REWRITE_TAC[REAL_MUL_AC]]);;

let FELDMAN_BASIS_RATIONAL = prove
 (`!h a b q r.
        ~(q = 0)
        ==> complex_integer
             (Cx(&q) pow (2 * a + 2 * h * (b + 1)) *
              feldman_basis h a b (Cx(&r) / Cx(&q)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[feldman_basis] THEN
  SUBGOAL_THEN
   `Cx(&q) pow (2 * a + 2 * h * (b + 1)) =
    Cx(&q) pow (2 * a) * (Cx(&q) pow (2 * h)) pow (b + 1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[COMPLEX_POW_POW; GSYM COMPLEX_POW_ADD] THEN AP_TERM_TAC THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING
   `(qa * qh) * (da * dh:complex) = (qa * da) * (qh * dh)`] THEN
  MATCH_MP_TAC COMPLEX_INTEGER_MUL THEN
  ASM_SIMP_TAC[FELDMAN_DELTA_RATIONAL] THEN
  REWRITE_TAC[GSYM COMPLEX_POW_MUL] THEN MATCH_MP_TAC COMPLEX_INTEGER_POW THEN
  ASM_SIMP_TAC[FELDMAN_DELTA_RATIONAL]);;

let FELDMAN_BASIS_POLYFUN = prove
 (`!h a b. ?e. ~(e(a + h * (b + 1)) = Cx(&0)) /\
               !z. feldman_basis h a b z =
                   vsum(0..a + h * (b + 1)) (\i. e i * z pow i)`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `U = ({0} CROSS (1..a)) UNION ((1..b+1) CROSS (1..h))` THEN
  SUBGOAL_THEN `FINITE(U:num#num->bool) /\ CARD U = a + h * (b + 1)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN
    SIMP_TAC[FINITE_UNION; FINITE_CROSS; FINITE_NUMSEG; FINITE_SING] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) CARD_UNION o lhand o snd) THEN
    SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG; FINITE_SING] THEN ANTS_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; FORALL_PAIR_THM;
                  IN_CROSS; IN_SING; IN_NUMSEG] THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    SIMP_TAC[CARD_CROSS; FINITE_NUMSEG; FINITE_SING; CARD_SING;
             CARD_NUMSEG_1] THEN
    REWRITE_TAC[ARITH_RULE `(b + 1) - 1 + 1 = b + 1`] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:num#num->bool`; `\u:num#num. --Cx(&(SND u))`]
         CPRODUCT_LINEAR_POLYFUN) THEN
  ASM_REWRITE_TAC[COMPLEX_SUB_RNEG] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\i:num. c i / Cx(&(FACT a * FACT h EXP (b + 1)))` THEN
  ASM_REWRITE_TAC[FELDMAN_BASIS_CPRODUCT] THEN CONJ_TAC THENL
   [REWRITE_TAC[complex_div; COMPLEX_MUL_LID; COMPLEX_INV_EQ_0; CX_INJ;
                REAL_OF_NUM_EQ; MULT_EQ_0; EXP_EQ_0; FACT_NZ];
    GEN_TAC THEN REWRITE_TAC[complex_div] THEN
    SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; FINITE_NUMSEG] THEN
    MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[COMPLEX_MUL_AC]]);;

let FELDMAN_BASIS_DERIV_BOUND_UNIFORM = prove
 (`!h L a b j z N.
        a < h /\ b <= L /\ norm z + &1 <= &N
        ==> norm(higher_complex_derivative j (feldman_basis h a b) z /
                 Cx(&(FACT j))) <= &2 pow ((L + 2) * (N + h))`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS `&2 pow ((N + a) + (b + 1) * (N + h))` THEN
  ASM_SIMP_TAC[FELDMAN_BASIS_DERIV_BOUND] THEN
  MATCH_MP_TAC REAL_POW_MONO THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE
   `a < h /\ (b + 1) * (N + h) <= (L + 1) * (N + h)
    ==> (N + a) + (b + 1) * (N + h) <= (L + 2) * (N + h)`) THEN
  ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Common multiples of consecutive integers. A common multiple of 1,...,n of *)
(* size exp(18 n) from the Chebyshev bound for psi; Nair divisibility of     *)
(* it by j * binom(n,j); and from these a common multiple of x+1,...,x+k of  *)
(* size (exp(19) (x + k) / k)^k, as in Baker Lemma 1 (Chapter 3).            *)
(* ------------------------------------------------------------------------- *)

let NUMSEG_COMMON_MULTIPLE_PSI = prove
 (`!n. ?M. ~(M = 0) /\ (!i. 1 <= i /\ i <= n ==> i divides M) /\
           log(&M) <= sum(1..n) (\d. mangoldt d)`,
  INDUCT_TAC THENL
   [EXISTS_TAC `1` THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH; LOG_1; REAL_LE_REFL] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `M:num` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  ASM_CASES_TAC `?p k. 1 <= k /\ prime p /\ SUC n = p EXP k` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `p:num`
     (X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `M * p` THEN
    ASM_SIMP_TAC[MANGOLDT_PRIMEPOW; MULT_EQ_0; PRIME_IMP_NZ] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ASM_CASES_TAC `i = SUC n` THENL
       [ALL_TAC;
        MATCH_MP_TAC DIVIDES_RMUL THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_ARITH_TAC] THEN
      SUBGOAL_THEN `p EXP k = p EXP (k - 1) * p` SUBST_ALL_TAC THENL
       [ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN
        AP_TERM_TAC THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIVIDES_MUL2 THEN
      REWRITE_TAC[DIVIDES_REFL] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
      ASM_REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; EXP_EQ_0] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(ARITH_RULE `x * 1 < x * p /\ x * p = SUC n ==> x <= n`) THEN
      ASM_REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0] THEN ASM_ARITH_TAC;
      ASM_SIMP_TAC[GSYM REAL_OF_NUM_MUL; LOG_MUL; REAL_OF_NUM_LT; LT_NZ;
                   PRIME_IMP_NZ] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `M:num` THEN
  SUBGOAL_THEN `mangoldt(SUC n) = &0` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[mangoldt]; ASM_REWRITE_TAC[REAL_ADD_RID]] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_CASES_TAC `i = SUC n` THENL
   [ALL_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_CASES_TAC `SUC n = 1` THEN ASM_REWRITE_TAC[DIVIDES_1] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC o
                MATCH_MP PRIME_FACTOR) THEN
  MP_TAC(SPECL [`SUC n`; `p:num`] INDEX_DECOMPOSITION_PRIME) THEN
  ASM_REWRITE_TAC[NOT_SUC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `e = index p (SUC n)` THEN
  SUBGOAL_THEN `1 <= e` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN
    REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; INDEX_EQ_0] THEN
    ASM_MESON_TAC[NOT_SUC; PRIME_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(b = 1)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~(?p k. 1 <= k /\ prime p /\ SUC n = p EXP k)` THEN
    REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`p:num`; `e:num`] THEN
    UNDISCH_TAC `p EXP e * b = SUC n` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(b = 0) /\ 2 <= p EXP e` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `p EXP e * b = SUC n` THEN
      ASM_REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC;
      MATCH_MP_TAC(ARITH_RULE `~(x = 0) /\ ~(x = 1) ==> 2 <= x`) THEN
      ASM_SIMP_TAC[EXP_EQ_0; EXP_EQ_1; PRIME_IMP_NZ] THEN
      ASM_MESON_TAC[PRIME_1; ARITH_RULE `1 <= e ==> ~(e = 0)`]];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check
   (fun th -> try rand(concl th) = `SUC n` with Failure _ -> false)) THEN
  MATCH_MP_TAC DIVIDES_MUL THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC;
    ONCE_REWRITE_TAC[COPRIME_SYM] THEN MATCH_MP_TAC COPRIME_EXP THEN
    ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_REWRITE_TAC[]] THEN
  (UNDISCH_TAC `p EXP e * b = SUC n` THEN
   UNDISCH_TAC `~(b = 0)` THEN UNDISCH_TAC `~(b = 1)` THEN
   UNDISCH_TAC `2 <= p EXP e` THEN
   SPEC_TAC(`p EXP e`,`a:num`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
   REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
   SUBGOAL_THEN `a * 1 < a * b /\ 1 * b < a * b` MP_TAC THENL
    [ASM_REWRITE_TAC[LT_MULT_LCANCEL; LT_MULT_RCANCEL] THEN ASM_ARITH_TAC;
     ASM_ARITH_TAC]));;

let NUMSEG_COMMON_MULTIPLE = prove
 (`!n. ?M. ~(M = 0) /\ (!i. 1 <= i /\ i <= n ==> i divides M) /\
           &M <= exp(&18 * &n)`,
  GEN_TAC THEN MP_TAC(SPEC `n:num` NUMSEG_COMMON_MULTIPLE_PSI) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M:num` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&M = exp(log(&M))` SUBST1_TAC THENL
   [ASM_SIMP_TAC[EXP_LOG; REAL_OF_NUM_LT; LT_NZ]; ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE] THEN
  MP_TAC(SPEC `n:num` PSI_BOUND) THEN ASM_REAL_ARITH_TAC);;

let SUM_NUMSEG_SUC_LEFT = prove
 (`!g m. sum(0..SUC m) g = g 0 + sum(0..m) (\i. g(i + 1))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MATCH_MP SUM_CLAUSES_LEFT (SPEC `SUC m` LE_0)] THEN
  REWRITE_TAC[ADD1; SUM_OFFSET]);;

let SUM_BINOM_DIFFERENCE = prove
 (`!f m. sum(0..SUC m) (\i. (-- &1) pow i * &(binom(SUC m,i)) * f i) =
         sum(0..m) (\i. (-- &1) pow i * &(binom(m,i)) * f i) -
         sum(0..m) (\i. (-- &1) pow i * &(binom(m,i)) * f(i + 1))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `sum(0..m) (\i. (-- &1) pow i * &(binom(m,i)) * f i) =
    sum(0..SUC m) (\i. (-- &1) pow i * &(binom(m,i)) * f i)`
  SUBST1_TAC THENL
   [SIMP_TAC[SUM_CLAUSES_NUMSEG; LE_0; BINOM_LT; ARITH_RULE `m < SUC m`] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_NUMSEG_SUC_LEFT; binom] THEN
  MATCH_MP_TAC(REAL_ARITH `x:real = y - z ==> a + x = (a + y) - z`) THEN
  REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM ADD1; binom; GSYM REAL_OF_NUM_ADD; real_pow] THEN
  CONV_TAC REAL_RING);;

let NAIR_IDENTITY = prove
 (`!m J. sum(0..m) (\i. (-- &1) pow i * &(binom(m,i)) * inv(&(J + i + 1))) =
         &(FACT J) * &(FACT m) / &(FACT(J + m + 1))`,
  INDUCT_TAC THENL
   [REWRITE_TAC[SUM_SING_NUMSEG; binom; real_pow; ADD_CLAUSES; GSYM ADD1] THEN
    REWRITE_TAC[FACT; GSYM REAL_OF_NUM_MUL] THEN GEN_TAC THEN
    MP_TAC(SPEC `J:num` FACT_NZ) THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
    MP_TAC(SPEC `J:num` NOT_SUC) THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  GEN_TAC THEN
  REWRITE_TAC[SUM_BINOM_DIFFERENCE] THEN
  REWRITE_TAC[ARITH_RULE `J + (i + 1) + 1 = (J + 1) + i + 1`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `J + SUC m + 1 = SUC(J + m + 1)`;
              ARITH_RULE `(J + 1) + m + 1 = SUC(J + m + 1)`;
              ARITH_RULE `J + 1 = SUC J`] THEN
  REWRITE_TAC[FACT; GSYM REAL_OF_NUM_MUL] THEN
  MP_TAC(SPEC `J + m + 1` FACT_NZ) THEN MP_TAC(SPEC `J + m + 1` NOT_SUC) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_SUC;
              GSYM REAL_OF_NUM_ADD] THEN
  CONV_TAC REAL_FIELD);;

let NAIR_DIVIDES = prove
 (`!L n j. (!i. 1 <= i /\ i <= n ==> i divides L) /\ 1 <= j /\ j <= n
           ==> (j * binom(n,j)) divides L`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`L:num`; `j * binom(n,j)`] INTEGER_DIV) THEN
  ASM_SIMP_TAC[MULT_EQ_0; BINOM_EQ_0; ARITH_RULE `j <= n ==> ~(n < j)`;
               ARITH_RULE `1 <= j ==> ~(j = 0)`] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `?J m. j = J + 1 /\ n = J + m + 1` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`j - 1`; `n - j`] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&L / &(j * binom(n,j)) =
    sum(0..m) (\i. (-- &1) pow i * &(binom(m,i)) * (&L / &(J + i + 1)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `a * b * c * d:real = c * a * b * d`] THEN
    REWRITE_TAC[SUM_LMUL; NAIR_IDENTITY] THEN AP_TERM_TAC THEN
    MP_TAC(SPECL [`m:num`; `J + 1`] BINOM_FACT) THEN
    MP_TAC(SPEC `J + m + 1` FACT_NZ) THEN
    ASM_REWRITE_TAC[ARITH_RULE `m + J + 1 = J + m + 1`;
                    ARITH_RULE `J + 1 = SUC J`] THEN
    REWRITE_TAC[FACT; GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL] THEN
    MP_TAC(SPEC `J:num` FACT_NZ) THEN MP_TAC(SPEC `m:num` FACT_NZ) THEN
    MP_TAC(SPEC `J:num` NOT_SUC) THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC INTEGER_SUM THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  REPEAT(MATCH_MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 INTEGER_CLOSED))))
         ORELSE CONJ_TAC) THEN
  SIMP_TAC[INTEGER_CLOSED; INTEGER_POW] THEN
  REWRITE_TAC[INTEGER_DIV; ADD_EQ_0; ARITH_EQ] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let BINOM_SHIFT_PRODUCT = prove
 (`!x J m. (J + 1) * binom(J + m + 1,J + 1) * binom(x + J + m + 1,J + m + 1) =
           (x + J + 1) * binom(x + J,J) * binom(x + J + m + 1,m)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `FACT(J + 1) = (J + 1) * FACT J /\
                FACT(x + J + 1) = (x + J + 1) * FACT(x + J)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM ADD1; ADD_CLAUSES; FACT]; ALL_TAC] THEN
  MATCH_MP_TAC(MESON[EQ_MULT_LCANCEL]
   `!a b c:num. ~(c = 0) /\ c * a = c * b ==> a = b`) THEN
  EXISTS_TAC `FACT x * FACT J * FACT m` THEN
  REWRITE_TAC[MULT_EQ_0; FACT_NZ] THEN
  MP_TAC(SPECL [`m:num`; `J + 1`] BINOM_FACT) THEN
  SUBST1_TAC(ARITH_RULE `m + J + 1 = J + m + 1`) THEN
  MP_TAC(SPECL [`x:num`; `J + m + 1`] BINOM_FACT) THEN
  MP_TAC(SPECL [`x:num`; `J:num`] BINOM_FACT) THEN
  MP_TAC(SPECL [`x + J + 1`; `m:num`] BINOM_FACT) THEN
  SUBST1_TAC(ARITH_RULE `(x + J + 1) + m = x + J + m + 1`) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_RING);;

let SHIFTED_COMMON_MULTIPLE = prove
 (`!x k L. (!i. 1 <= i /\ i <= k ==> i divides L)
           ==> !j. 1 <= j /\ j <= k ==> (x + j) divides L * binom(x + k,k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`L:num`; `k:num`; `j:num`] NAIR_DIVIDES) THEN
  ASM_REWRITE_TAC[divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num` SUBST1_TAC) THEN
  SUBGOAL_THEN `?J m. j = J + 1 /\ k = J + m + 1` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`j - 1`; `k - j`] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`x:num`; `J:num`; `m:num`] BINOM_SHIFT_PRODUCT) THEN
  DISCH_TAC THEN
  EXISTS_TAC `c * binom(x + J,J) * binom(x + J + m + 1,m)` THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  CONV_TAC NUM_RING);;

let FACT_LOWER_BOUND_EXP = prove
 (`!k. &k pow k <= exp(&k) * &(FACT k)`,
  GEN_TAC THEN MP_TAC(SPEC `k:num` factorial_lower_bound) THEN
  REWRITE_TAC[REAL_POW_DIV; GSYM REAL_EXP_N; REAL_MUL_RID] THEN
  SIMP_TAC[REAL_LE_LDIV_EQ; REAL_EXP_POS_LT] THEN REWRITE_TAC[REAL_MUL_AC]);;

let BINOM_UPPER_BOUND_EXP = prove
 (`!x k. 1 <= k ==> &(binom(x + k,k)) <= (exp(&1) * (&x + &k) / &k) pow k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &k` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &(FACT k)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; FACT_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&(binom(x + k,k)) = product(1..k) (\j. &x + &j) / &(FACT k)`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_ADD] THEN
    SIMP_TAC[GSYM REAL_OF_NUM_NPRODUCT; FINITE_NUMSEG] THEN
    REWRITE_TAC[NPRODUCT_SHIFT_BINOM; GSYM REAL_OF_NUM_MUL] THEN
    UNDISCH_TAC `&0 < &(FACT k)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  TRANS_TAC REAL_LE_TRANS `(&x + &k) pow k` THEN CONJ_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `product(1..k) (\j. &x + &k)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      REWRITE_TAC[PRODUCT_CONST_NUMSEG_1; REAL_LE_REFL]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL; REAL_POW_DIV] THEN
  MP_TAC(SPECL [`k:num`; `&1`] REAL_EXP_N) THEN
  REWRITE_TAC[REAL_MUL_RID] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(SPEC `k:num` FACT_LOWER_BOUND_EXP) THEN
  SUBGOAL_THEN `&0 < &k pow k /\ &0 <= (&x + &k) pow k` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; REAL_POW_LE; REAL_POS;
                 REAL_ARITH `&0 <= x ==> &0 <= x + &k`];
    ALL_TAC] THEN
  SPEC_TAC(`&k pow k`,`p:real`) THEN
  SPEC_TAC(`(&x + &k) pow k`,`q:real`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(exp(&k) * q / p) * &(FACT k) = (q * (exp(&k) * &(FACT k))) / p`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < p` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REWRITE_TAC[]);;

let SHIFTED_COMMON_MULTIPLE_BOUND = prove
 (`!x k. 1 <= k
         ==> ?N. ~(N = 0) /\ (!j. 1 <= j /\ j <= k ==> (x + j) divides N) /\
                 &N <= (exp(&19) * (&x + &k) / &k) pow k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `k:num` NUMSEG_COMMON_MULTIPLE) THEN
  DISCH_THEN(X_CHOOSE_THEN `L:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `L * binom(x + k,k)` THEN
  ASM_SIMP_TAC[SHIFTED_COMMON_MULTIPLE; MULT_EQ_0; BINOM_EQ_0;
               ARITH_RULE `~(x + k < k)`] THEN
  SUBGOAL_THEN
   `(exp(&19) * (&x + &k) / &k) pow k =
    exp(&18 * &k) * (exp(&1) * (&x + &k) / &k) pow k`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `exp(&19) = exp(&18) * exp(&1)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `exp(&18 * &k) = exp(&18) pow k` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_N] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_MUL; REAL_MUL_ASSOC]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_SIMP_TAC[REAL_POS; BINOM_UPPER_BOUND_EXP]);;
