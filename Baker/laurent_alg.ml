(* ========================================================================= *)
(* Two logarithms, the Laurent bound for algebraic numbers: real numbers     *)
(* a_i = be_i / ga_i of a number field K = Q(r 1) of degree n                *)
(* (nf_data n c r).                                                          *)
(*                                                                           *)
(* Purpose: M. Laurent, Linear forms in two logarithms and interpolation     *)
(* determinants II, Acta Arith. 133 (2008), Lemma 1 with D = n for a_i =     *)
(* be_i / ga_i given by algebraic integers be_i, ga_i of K (the determinant  *)
(* times window factors ga^V be^-U is an algebraic integer omega of K; its   *)
(* norm is a non-zero integer, and every conjugate of omega is bounded by    *)
(* the permutation expansion after the triangular row change with centre     *)
(* X / 2), Theorem 1 at mu = 1 and D = n, and the Theorem-2 and Corollary-2  *)
(* forms (Corollary 2: real and positive a_i, log a_i), including the        *)
(* collision cases (Liouville inequality in K) and the step from Lambda      *)
(* prime to Lambda. The pair heights nf_proj_height bound the absolute       *)
(* heights of Laurent from above, for algebraic-integer coordinates.         *)
(*                                                                           *)
(* Main results: LAURENT_ARITH_NF (Lemma 1), LAURENT_CORE_NF (Theorem 1),    *)
(* LAURENT_NF_REAL_PARAM (Theorem-2 form), LAURENT_NF_REAL (Corollary-2      *)
(* form: log |Lambda| >= -32 n^4 max(10/n, 1, log(b1/(n A2) + b2/(n A1)) +   *)
(* 0.38)^2 A1 A2); helper names LAURENT_ALG_*. LAURENT_NF_REAL_PARAM has the *)
(* hypothesis n log 2 / 2 <= h of Laurent condition (3): without it the      *)
(* statement fails for multiplicatively dependent data in Q(2^(1/n)) of      *)
(* astronomically large degree n; LAURENT_ALG_REAL_PARAM_DEG20 is the        *)
(* statement without it for n <= 20.                                         *)
(*                                                                           *)
(* Uses: Baker/laurent_nf.ml (NF_LIOUVILLE, NF_PROJ_HEIGHT_GE,               *)
(* NF_HEIGHT_ELEM_NONZERO, NF_HEIGHT_ELEM_ORDER), Baker/laurent_nf_defs.ml   *)
(* (nf_elem, nf_alg_int, nf_proj_height), Baker/laurent_corner.ml            *)
(* (LAURENT_BOUND_CORNER_5_10, LAURENT_CORNER_LOG_5), Baker/laurent_param.ml *)
(* (LAURENT_PARAMETERS, LAURENT_PARAMETERS_LARGE), Baker/laurent_core.ml     *)
(* (LAURENT_EXP_MATRIX, LAURENT_GLEMMA_BOTH, LAURENT_CORE_FINAL,             *)
(* TL_LAURENT_CORE_WINDOW, _CENTRED_SUM, _SUM_PRED_MOD, _SUM_LOG_FACT_MOD,   *)
(* _LOG_UPPER), Baker/laurent_interp.ml (TWOLOG_LAURENT_ANALYTIC),           *)
(* Baker/laurent_binom.ml (BINOM_CDET_ROW_CHANGE, BINOM_ZERO_MINOR_REAL),    *)
(* Baker/laurent_defs.ml (laurent_bound, laurent_main),                      *)
(* Baker/nf_order.ml (NF_ORDER_REDUCE, closure of the order),                *)
(* Baker/nf_defs.ml (nf_data, nf_order, NF_DATA_1_IN), Baker/algint.ml       *)
(* (closure of algebraic_integer), Baker/twolog.ml (CARD_IMAGE_INJ_GRID,     *)
(* LOG_POW_MUL, LOG_LE_SUB_1), Baker/twolog_det.ml (COMPLEX_RING_DET,        *)
(* CDET_CX), Library/ring_det.ml (RING_DET_ROW_0, RING_DET_EQ),              *)
(* Baker/lemmas.ml (CPRODUCT_POW_NSUM).                                      *)
(* ========================================================================= *)

needs "Baker/laurent_core.ml";;
needs "Baker/laurent_param.ml";;
needs "Baker/laurent_corner.ml";;
needs "Baker/laurent_nf.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Closure of nf_elem and nf_alg_int under the ring operations (common       *)
(* denominators, NF_ORDER_REDUCE).                                           *)
(* ------------------------------------------------------------------------- *)

let LAURENT_ALG_ELEM_ORDER = prove
 (`!n c r a.
     nf_data n c r
     ==> (nf_elem n r a <=>
          ?d. integer d /\ ~(d = &0) /\ nf_order n r (\k. Cx d * a k))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [MATCH_ACCEPT_TAC NF_HEIGHT_ELEM_ORDER; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`;
                `\k. Cx d * (a:num->complex) k`] NF_ORDER_REDUCE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num->real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[nf_elem] THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `p:num->real`] THEN ASM_REWRITE_TAC[]);;

let LAURENT_ALG_ELEM_CONST = prove
 (`!n c r m. nf_data n c r /\ integer m ==> nf_elem n r (\k. Cx m)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LAURENT_ALG_ELEM_ORDER th]) THEN
  EXISTS_TAC `&1` THEN
  REWRITE_TAC[INTEGER_CLOSED; REAL_OF_NUM_EQ; ARITH_EQ; COMPLEX_MUL_LID] THEN
  MATCH_MP_TAC NF_ORDER_CX THEN ASM_REWRITE_TAC[]);;

let LAURENT_ALG_ELEM_ADD = prove
 (`!n c r a b.
     nf_data n c r /\ nf_elem n r a /\ nf_elem n r b
     ==> nf_elem n r (\k. a k + b k)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LAURENT_ALG_ELEM_ORDER th]) THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `d * e:real` THEN ASM_SIMP_TAC[INTEGER_MUL; REAL_ENTIRE] THEN
  MATCH_MP_TAC NF_ORDER_EQ THEN
  EXISTS_TAC `\k. Cx e * (Cx d * (a:num->complex) k) +
                  Cx d * (Cx e * (b:num->complex) k)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NF_ORDER_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC NF_ORDER_MUL THEN ASM_SIMP_TAC[NF_ORDER_CX];
    REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING]);;

let LAURENT_ALG_ELEM_MUL = prove
 (`!n c r a b.
     nf_data n c r /\ nf_elem n r a /\ nf_elem n r b
     ==> nf_elem n r (\k. a k * b k)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LAURENT_ALG_ELEM_ORDER th]) THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `d * e:real` THEN ASM_SIMP_TAC[INTEGER_MUL; REAL_ENTIRE] THEN
  MATCH_MP_TAC NF_ORDER_EQ THEN
  EXISTS_TAC
   `\k. (Cx d * (a:num->complex) k) * (Cx e * (b:num->complex) k)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NF_ORDER_MUL THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING]);;

let LAURENT_ALG_ELEM_NEG = prove
 (`!n c r a. nf_data n c r /\ nf_elem n r a ==> nf_elem n r (\k. --(a k))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LAURENT_ALG_ELEM_ORDER th]) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC NF_ORDER_EQ THEN
  EXISTS_TAC `\k. --(Cx d * (a:num->complex) k)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NF_ORDER_NEG THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN CONV_TAC COMPLEX_RING]);;

let LAURENT_ALG_INT_CONST = prove
 (`!n c r m. nf_data n c r /\ integer m ==> nf_alg_int n r (\k. Cx m)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nf_alg_int] THEN
  ASM_MESON_TAC[LAURENT_ALG_ELEM_CONST; ALGEBRAIC_INTEGER_INTEGER]);;

let LAURENT_ALG_INT_ADD = prove
 (`!n c r a b.
     nf_data n c r /\ nf_alg_int n r a /\ nf_alg_int n r b
     ==> nf_alg_int n r (\k. a k + b k)`,
  REWRITE_TAC[nf_alg_int] THEN
  MESON_TAC[LAURENT_ALG_ELEM_ADD; ALGEBRAIC_INTEGER_ADD]);;

let LAURENT_ALG_INT_MUL = prove
 (`!n c r a b.
     nf_data n c r /\ nf_alg_int n r a /\ nf_alg_int n r b
     ==> nf_alg_int n r (\k. a k * b k)`,
  REWRITE_TAC[nf_alg_int] THEN
  MESON_TAC[LAURENT_ALG_ELEM_MUL; ALGEBRAIC_INTEGER_MUL]);;

let LAURENT_ALG_INT_SUB = prove
 (`!n c r a b.
     nf_data n c r /\ nf_alg_int n r a /\ nf_alg_int n r b
     ==> nf_alg_int n r (\k. a k - b k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `nf_alg_int n r (\k. --((b:num->complex) k))` ASSUME_TAC THENL
   [UNDISCH_TAC `nf_alg_int n r (b:num->complex)` THEN
    REWRITE_TAC[nf_alg_int] THEN
    ASM_MESON_TAC[LAURENT_ALG_ELEM_NEG; ALGEBRAIC_INTEGER_NEG];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`;
                 `a:num->complex`; `\k. --((b:num->complex) k)`]
    LAURENT_ALG_INT_ADD) THEN
  ASM_REWRITE_TAC[complex_sub]);;

let LAURENT_ALG_INT_POW = prove
 (`!n c r a m.
     nf_data n c r /\ nf_alg_int n r a ==> nf_alg_int n r (\k. a k pow m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SPEC_TAC(`m:num`,`m:num`) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[complex_pow] THEN MATCH_MP_TAC LAURENT_ALG_INT_CONST THEN
    EXISTS_TAC `c:num->real` THEN ASM_REWRITE_TAC[INTEGER_CLOSED];
    REWRITE_TAC[complex_pow] THEN
    MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`;
                   `a:num->complex`; `\k. (a:num->complex) k pow m`]
      LAURENT_ALG_INT_MUL) THEN
    ASM_REWRITE_TAC[]]);;

let LAURENT_ALG_INT_VSUM = prove
 (`!n c r (f:A->num->complex) s.
     nf_data n c r /\ FINITE s /\ (!x. x IN s ==> nf_alg_int n r (f x))
     ==> nf_alg_int n r (\k. vsum s (\x. f x k))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[IMP_CONJ] THEN SPEC_TAC(`s:A->bool`,`s:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; COMPLEX_VEC_0] THEN CONJ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC LAURENT_ALG_INT_CONST THEN
    EXISTS_TAC `c:num->real` THEN ASM_REWRITE_TAC[INTEGER_CLOSED];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `t:A->bool`] THEN STRIP_TAC THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`;
                 `(f:A->num->complex) x`;
                 `\k. vsum t (\y. (f:A->num->complex) y k)`]
    LAURENT_ALG_INT_ADD) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The window identity: the determinant of a matrix with entries             *)
(* A i j (b1/g1)^(l i rr j) (b2/g2)^(l i ss j), times g1^V1 b1^-U1           *)
(* g2^V2 b2^-U2, is a sum of monomials b^(E-U) g^(V-E) when every            *)
(* permutation exponent E lies in the window [U, V]; and its norm bound.     *)
(* ------------------------------------------------------------------------- *)

let LAURENT_ALG_POW_WINDOW = prove
 (`!(b:complex) g U E V.
     ~(b = Cx(&0)) /\ ~(g = Cx(&0)) /\ U <= E /\ E <= V
     ==> g pow V / b pow U * (b / g) pow E = b pow (E - U) * g pow (V - E)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `e:num` SUBST1_TAC o
    GEN_REWRITE_RULE I [LE_EXISTS]) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:num` SUBST1_TAC o
    GEN_REWRITE_RULE I [LE_EXISTS]) THEN
  REWRITE_TAC[ADD_SUB2; ARITH_RULE `((U + d) + e) - (U + d) = e`] THEN
  REWRITE_TAC[COMPLEX_POW_ADD; COMPLEX_POW_DIV] THEN
  SUBGOAL_THEN `~(b pow U = Cx(&0)) /\ ~(g pow U = Cx(&0)) /\
                ~(g pow d = Cx(&0))` MP_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_POW_EQ_0]; ALL_TAC] THEN
  CONV_TAC COMPLEX_FIELD);;

let LAURENT_ALG_POW_MAX_LE = prove
 (`!x y U E V.
     &0 <= x /\ &0 <= y /\ U <= E /\ E <= V
     ==> x pow (E - U) * y pow (V - E) <= max x y pow (V - U)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `V - U = (E - U) + (V - E)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[REAL_POW_ADD]] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_SIMP_TAC[REAL_POW_LE] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN
  ASM_REAL_ARITH_TAC);;

let LAURENT_ALG_RING_SHUFFLE = prove
 (`!q1 q2 s c y1 y2 m1 m2 m3 m4:complex.
     q1 * y1 = m1 * m2 /\ q2 * y2 = m3 * m4
     ==> q1 * q2 * s * c * y1 * y2 = s * c * m1 * m2 * m3 * m4`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `q1 * q2 * s * c * y1 * y2 = s * c * (q1 * y1) * (q2 * y2:complex)`
  SUBST1_TAC THENL [CONV_TAC COMPLEX_RING; ASM_REWRITE_TAC[]] THEN
  CONV_TAC COMPLEX_RING);;

let LAURENT_ALG_CDET_WINDOW = prove
 (`!N (A:num->num->complex) (l:num->num) (rr:num->num) (ss:num->num)
    b1 g1 b2 g2 U1 V1 U2 V2.
     ~(b1 = Cx(&0)) /\ ~(g1 = Cx(&0)) /\ ~(b2 = Cx(&0)) /\ ~(g2 = Cx(&0)) /\
     (!p. p permutes 1..N
          ==> U1 <= nsum(1..N) (\i. l i * rr(p i)) /\
              nsum(1..N) (\i. l i * rr(p i)) <= V1 /\
              U2 <= nsum(1..N) (\i. l i * ss(p i)) /\
              nsum(1..N) (\i. l i * ss(p i)) <= V2)
     ==> g1 pow V1 / b1 pow U1 * g2 pow V2 / b2 pow U2 *
         ring_det complex_ring (1..N)
           (\i j. A i j * (b1 / g1) pow (l i * rr j) *
                  (b2 / g2) pow (l i * ss j)) =
         vsum {p | p permutes 1..N}
           (\p. Cx(sign p) * cproduct(1..N) (\i. A i (p i)) *
                b1 pow (nsum(1..N) (\i. l i * rr(p i)) - U1) *
                g1 pow (V1 - nsum(1..N) (\i. l i * rr(p i))) *
                b2 pow (nsum(1..N) (\i. l i * ss(p i)) - U2) *
                g2 pow (V2 - nsum(1..N) (\i. l i * ss(p i))))`,
  REPEAT STRIP_TAC THEN SIMP_TAC[COMPLEX_RING_DET; FINITE_NUMSEG] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_PERMUTATIONS; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `p:num->num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  SIMP_TAC[CPRODUCT_MUL; FINITE_NUMSEG; CPRODUCT_POW_NSUM] THEN
  MATCH_MP_TAC LAURENT_ALG_RING_SHUFFLE THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p:num->num`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN CONJ_TAC THEN MATCH_MP_TAC LAURENT_ALG_POW_WINDOW THEN
  ASM_REWRITE_TAC[]);;

let LAURENT_ALG_CDET_WINDOW_BOUND = prove
 (`!N (A:num->num->complex) (l:num->num) (rr:num->num) (ss:num->num)
    b1 g1 b2 g2 U1 V1 U2 V2 B.
     ~(b1 = Cx(&0)) /\ ~(g1 = Cx(&0)) /\ ~(b2 = Cx(&0)) /\ ~(g2 = Cx(&0)) /\
     (!p. p permutes 1..N
          ==> U1 <= nsum(1..N) (\i. l i * rr(p i)) /\
              nsum(1..N) (\i. l i * rr(p i)) <= V1 /\
              U2 <= nsum(1..N) (\i. l i * ss(p i)) /\
              nsum(1..N) (\i. l i * ss(p i)) <= V2) /\
     (!p. p permutes 1..N ==> product(1..N) (\i. norm(A i (p i))) <= B)
     ==> norm(g1 pow V1 / b1 pow U1 * g2 pow V2 / b2 pow U2 *
              ring_det complex_ring (1..N)
                (\i j. A i j * (b1 / g1) pow (l i * rr j) *
                       (b2 / g2) pow (l i * ss j))) <=
         &(FACT N) * B * max (norm b1) (norm g1) pow (V1 - U1) *
         max (norm b2) (norm g2) pow (V2 - U2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))) THEN
  MP_TAC(SPECL [`N:num`; `A:num->num->complex`; `l:num->num`;
                `rr:num->num`; `ss:num->num`; `b1:complex`; `g1:complex`;
                `b2:complex`; `g2:complex`; `U1:num`; `V1:num`; `U2:num`;
                `V2:num`] LAURENT_ALG_CDET_WINDOW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `sum {p | p permutes 1..N}
        (\p:num->num. B * max (norm(b1:complex)) (norm(g1:complex))
                            pow (V1 - U1) *
                      max (norm(b2:complex)) (norm(g2:complex))
                            pow (V2 - U2))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    SIMP_TAC[SUM_CONST; FINITE_PERMUTATIONS; FINITE_NUMSEG;
             CARD_PERMUTATIONS; CARD_NUMSEG_1; REAL_LE_REFL]] THEN
  MATCH_MP_TAC VSUM_NORM_LE THEN
  SIMP_TAC[FINITE_PERMUTATIONS; FINITE_NUMSEG; IN_ELIM_THM] THEN
  X_GEN_TAC `p:num->num` THEN DISCH_TAC THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_SIGN_PERMUTATION;
              REAL_MUL_LID; COMPLEX_NORM_POW] THEN
  SIMP_TAC[NORM_CPRODUCT; FINITE_NUMSEG] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p:num->num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p:num->num`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `(a:real) * b * c * d * e = a * (b * c) * (d * e)`] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[PRODUCT_POS_LE_NUMSEG; NORM_POS_LE] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    SIMP_TAC[REAL_POW_LE; NORM_POS_LE];
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; NORM_POS_LE] THEN
    CONJ_TAC THEN MATCH_MP_TAC LAURENT_ALG_POW_MAX_LE THEN
    ASM_REWRITE_TAC[NORM_POS_LE]]);;

(* ------------------------------------------------------------------------- *)
(* Helpers for the arithmetic lower bound: monomials of algebraic integers   *)
(* of K, a zero row, X = (R-1) b2 + (S-1) b1 >= 1 for K >= 2, logarithms of  *)
(* the diagonal product, of the heights, of the prefactor and of the bounds  *)
(* at the other conjugates, and the final real inequality.                   *)
(* ------------------------------------------------------------------------- *)

let LAURENT_ALG_INT_MONOMIAL = prove
 (`!n c r m m' (a1:num->complex) a2 a3 a4 e1 e2 e3 e4.
     nf_data n c r /\ integer m /\ integer m' /\
     nf_alg_int n r a1 /\ nf_alg_int n r a2 /\
     nf_alg_int n r a3 /\ nf_alg_int n r a4
     ==> nf_alg_int n r (\k. Cx m * Cx m' * a1 k pow e1 * a2 k pow e2 *
                             a3 k pow e3 * a4 k pow e4)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!a b. nf_alg_int n r a /\ nf_alg_int n r b
                      ==> nf_alg_int n r (\k. a k * b k)`
  ASSUME_TAC THENL [ASM_MESON_TAC[LAURENT_ALG_INT_MUL]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> REPEAT(MATCH_MP_TAC th THEN CONJ_TAC)) THEN
  ASM_MESON_TAC[LAURENT_ALG_INT_POW; LAURENT_ALG_INT_CONST]);;

let LAURENT_ALG_RDET_ZERO_ROW = prove
 (`!n (f:num->num->real) i.
     i IN 1..n /\ (!j. j IN 1..n ==> f i j = &0)
     ==> ring_det real_ring (1..n) f = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`real_ring`; `1..n`; `f:num->num->real`; `i:num`]
    RING_DET_ROW_0) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; REAL_RING_CLAUSES] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_DET_EQ THEN
  ASM_MESON_TAC[]);;

let LAURENT_ALG_X_POS = prove
 (`!K L b1 b2 R S (rr:num->num) (ss:num->num) (x1:real) (x2:real).
     2 <= K /\ 1 <= L /\ (!j. j IN 1..K * L ==> rr j < R /\ ss j < S) /\
     ~(ring_det real_ring (1..K * L)
         (\i j. &(binom(rr j * b2 + ss j * b1,(i - 1) MOD K)) *
                x1 pow (((i - 1) DIV K) * rr j) *
                x2 pow (((i - 1) DIV K) * ss j)) = &0)
     ==> 1 <= (R - 1) * b2 + (S - 1) * b1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
  MATCH_MP_TAC(TAUT `(q ==> p) ==> ~p ==> ~q`) THEN DISCH_TAC THEN
  MATCH_MP_TAC LAURENT_ALG_RDET_ZERO_ROW THEN
  EXISTS_TAC `2` THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN
    SUBGOAL_THEN `2 * 1 <= K * L` MP_TAC THENL
     [MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[]; ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `(2 - 1) MOD K = 1` SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 - 1 = 1`] THEN MATCH_MP_TAC MOD_LT THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(rr:num->num) j * b2 + (ss:num->num) j * b1 = 0`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(rr:num->num) j * b2 + (ss:num->num) j * b1 <=
                  (R - 1) * b2 + (S - 1) * b1`
    MP_TAC THENL
     [MATCH_MP_TAC LE_ADD2 THEN CONJ_TAC THEN MATCH_MP_TAC LE_MULT2 THEN
      ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SIMP_TAC[BINOM_LT; ARITH_RULE `0 < 1`; REAL_MUL_LZERO]);;

let LAURENT_ALG_LOG_PP = prove
 (`!K L X.
     1 <= K /\ (K = 1 \/ &0 < X)
     ==> log(product(1..K * L)
               (\i. X pow ((i - 1) MOD K) / &(FACT((i - 1) MOD K)))) =
         &(K * L) / &2 * ((&K - &1) * log X -
                          &2 / &K * sum(1..K - 1) (\k. log(&(FACT k))))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  STRIP_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[MOD_1; real_pow; FACT; REAL_DIV_1; PRODUCT_ONE; LOG_1] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. &0 < X pow ((i - 1) MOD K) / &(FACT((i - 1) MOD K))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; FACT_LT];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_PRODUCT; FINITE_NUMSEG] THEN
  ASM_SIMP_TAC[LOG_DIV; REAL_POW_LT; REAL_OF_NUM_LT; FACT_LT; LOG_POW] THEN
  REWRITE_TAC[SUM_SUB_NUMSEG; SUM_RMUL] THEN
  ASM_SIMP_TAC[TL_LAURENT_CORE_SUM_PRED_MOD;
               TL_LAURENT_CORE_SUM_LOG_FACT_MOD] THEN
  SUBGOAL_THEN `~(&K = &0)` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN CONV_TAC REAL_FIELD);;

let LAURENT_ALG_HEIGHT_SPLIT = prove
 (`!n (be:num->complex) (ga:num->complex) x.
     1 <= n /\ ~(ga 1 = Cx(&0)) /\ be 1 = Cx x * ga 1 /\ &1 <= x
     ==> &n * nf_proj_height n be ga =
         log x + log(norm(ga 1)) +
         sum(2..n) (\k. log(max (norm(be k)) (norm(ga k))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nf_proj_height] THEN
  SUBGOAL_THEN `~(&n:real = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_DIV_LMUL] THEN
  ASM_SIMP_TAC[SUM_CLAUSES_LEFT; ARITH] THEN
  REWRITE_TAC[REAL_ADD_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
  SUBGOAL_THEN `abs x = x` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm((ga:num->complex) 1)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_NORM_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `max (x * norm((ga:num->complex) 1)) (norm(ga 1)) =
                x * norm(ga 1)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ARITH `max a b = a <=> b <= a`] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC LOG_MUL THEN ASM_REAL_ARITH_TAC);;

let LAURENT_ALG_LOG_PREF = prove
 (`!x1 g1 x2 g2 D U1 V1 U2 V2.
     &0 < x1 /\ &0 < g1 /\ &0 < x2 /\ &0 < g2 /\ &0 < D
     ==> log(g1 pow V1 / (x1 * g1) pow U1 * g2 pow V2 / (x2 * g2) pow U2 * D) =
         (&V1 * log g1 - &U1 * (log x1 + log g1)) +
         (&V2 * log g2 - &U2 * (log x2 + log g2)) + log D`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < x1 * g1 /\ &0 < x2 * g2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < g1 pow V1 / (x1 * g1) pow U1 /\
                &0 < g2 pow V2 / (x2 * g2) pow U2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_MUL; REAL_LT_MUL] THEN
  ASM_SIMP_TAC[LOG_DIV; REAL_POW_LT; LOG_POW; LOG_MUL] THEN REAL_ARITH_TAC);;

let LAURENT_ALG_LOG_BK = prove
 (`!n FF P (M1:num->real) (M2:num->real) e1 e2.
     1 <= n /\ &0 < FF /\ &0 < P /\ (!k. k IN 2..n ==> &0 < M1 k /\ &0 < M2 k)
     ==> log(product(2..n) (\k. FF * P * M1 k pow e1 * M2 k pow e2)) =
         (&n - &1) * (log FF + log P) + &e1 * sum(2..n) (\k. log(M1 k)) +
         &e2 * sum(2..n) (\k. log(M2 k))`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) LOG_PRODUCT o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POW_LT];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `sum(2..n) (\k. log(FF * P * (M1:num->real) k pow e1 *
                       (M2:num->real) k pow e2)) =
    sum(2..n) (\k. (log FF + log P) + &e1 * log(M1 k) + &e2 * log(M2 k))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
    ASM_REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `&0 < (M1:num->real) k pow e1 /\ &0 < (M2:num->real) k pow e2 /\
      &0 < M1 k pow e1 * M2 k pow e2 /\ &0 < P * M1 k pow e1 * M2 k pow e2`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_POW_LT];
      ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_MUL] THEN ASM_SIMP_TAC[LOG_POW] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL; SUM_CONST_NUMSEG] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= n ==> (n + 1) - 2 = n - 1`;
               GSYM REAL_OF_NUM_SUB] THEN
  REAL_ARITH_TAC);;

let LAURENT_ALG_ARITH_REAL = prove
 (`!M1 G1 U1 V1 l1 g1 S1 H1 M2 G2 U2 V2 l2 g2 S2 H2 m FF P D:real.
     &0 <= l1 /\ &0 <= g1 + S1 /\ H1 = l1 + g1 + S1 /\
     &0 <= l2 /\ &0 <= g2 + S2 /\ H2 = l2 + g2 + S2 /\
     M1 - G1 <= U1 /\ V1 <= M1 + G1 /\ M2 - G2 <= U2 /\ V2 <= M2 + G2 /\
     &0 <= (V1 * g1 - U1 * (l1 + g1)) + (V2 * g2 - U2 * (l2 + g2)) + D +
           (m * (FF + P) + (V1 - U1) * S1 + (V2 - U2) * S2)
     ==> (M1 + G1) * l1 - &2 * G1 * H1 + (M2 + G2) * l2 - &2 * G2 * H2 -
         m * (FF + P) <= D`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `&0 <= (U1 - (M1 - G1)) * l1 /\
    &0 <= ((U1 - (M1 - G1)) + ((M1 + G1) - V1)) * (g1 + S1) /\
    &0 <= (U2 - (M2 - G2)) * l2 /\
    &0 <= ((U2 - (M2 - G2)) + ((M2 + G2) - V2)) * (g2 + S2)`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC
   `&0 <= (V1 * g1 - U1 * (l1 + g1)) + (V2 * g2 - U2 * (l2 + g2)) + D +
          (m * (FF + P) + (V1 - U1) * S1 + (V2 - U2) * S2)` THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The arithmetic lower bound (Laurent Lemma 1 with D = n).                  *)
(* ------------------------------------------------------------------------- *)

let LAURENT_ALG_CENTRE_BOUND = prove
 (`!x X. x <= X ==> abs(&x - &X / &2) <= &X / &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= &x /\ &x <= &X` MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE]; REAL_ARITH_TAC]);;

let LAURENT_ALG_NORM_REARRANGE = prove
 (`!q1 q2 c (d:complex) B.
     norm(q1 * q2 * d) <= B ==> norm(q1 * q2 * c * d) <= norm c * B`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `q1 * q2 * c * d = c * (q1 * q2 * d:complex)` SUBST1_TAC THENL
   [CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN
  ASM_MESON_TAC[COMPLEX_NORM_MUL]);;

let LAURENT_ARITH_NF = prove
 (`!n c r be1 ga1 be2 ga2 x1 x2 b1 b2 K L N R S (rr:num->num) (ss:num->num)
    G1 G2.
     nf_data n c r /\
     nf_alg_int n r be1 /\ nf_alg_int n r ga1 /\
     nf_alg_int n r be2 /\ nf_alg_int n r ga2 /\
     ~(ga1 1 = Cx(&0)) /\ ~(ga2 1 = Cx(&0)) /\
     be1 1 = Cx x1 * ga1 1 /\ be2 1 = Cx x2 * ga2 1 /\ &1 <= x1 /\ &1 <= x2 /\
     1 <= K /\ 1 <= L /\ N = K * L /\
     (!j. j IN 1..N ==> rr j < R /\ ss j < S) /\
     (!p. p permutes 1..N
          ==> abs(sum(1..N) (\i. (&((i - 1) DIV K) - (&L - &1) / &2) *
                                 &(rr(p i)))) <= G1) /\
     (!p. p permutes 1..N
          ==> abs(sum(1..N) (\i. (&((i - 1) DIV K) - (&L - &1) / &2) *
                                 &(ss(p i)))) <= G2) /\
     ~(ring_det real_ring (1..N)
         (\i j. &(binom(rr j * b2 + ss j * b1,(i - 1) MOD K)) *
                x1 pow (((i - 1) DIV K) * rr j) *
                x2 pow (((i - 1) DIV K) * ss j)) = &0)
     ==> ((&L - &1) / &2 * &(nsum(1..N) rr) + G1) * log x1 -
         &2 * G1 * (&n * nf_proj_height n be1 ga1) +
         ((&L - &1) / &2 * &(nsum(1..N) ss) + G2) * log x2 -
         &2 * G2 * (&n * nf_proj_height n be2 ga2) -
         (&n - &1) *
         (log(&(FACT N)) +
          &N / &2 * ((&K - &1) * log(&((R - 1) * b2 + (S - 1) * b1) / &2) -
                     &2 / &K * sum(1..K - 1) (\k. log(&(FACT k)))))
         <= log(abs(ring_det real_ring (1..N)
                      (\i j. &(binom(rr j * b2 + ss j * b1,(i - 1) MOD K)) *
                             x1 pow (((i - 1) DIV K) * rr j) *
                             x2 pow (((i - 1) DIV K) * ss j))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_THEN `N = K * L` SUBST_ALL_TAC THEN
  UNDISCH_THEN
   `!j. j IN 1..K * L ==> (rr:num->num) j < R /\ (ss:num->num) j < S`
    (LABEL_TAC "rs") THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NF_DATA) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_1_IN) THEN
  SUBGOAL_THEN `~((be1:num->complex) 1 = Cx(&0)) /\
                ~((be2:num->complex) 1 = Cx(&0))` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `nf_elem n r (be1:num->complex) /\ nf_elem n r (ga1:num->complex) /\
    nf_elem n r (be2:num->complex) /\ nf_elem n r (ga2:num->complex)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [nf_alg_int]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. k IN 1..n ==> ~((be1:num->complex) k = Cx(&0)) /\
                      ~((ga1:num->complex) k = Cx(&0)) /\
                      ~((be2:num->complex) k = Cx(&0)) /\
                      ~((ga2:num->complex) k = Cx(&0))`
  (LABEL_TAC "nz") THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC NF_HEIGHT_ELEM_NONZERO THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `c:num->real`; `r:num->complex`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  (* exponent windows of the permutation terms *)
  MP_TAC(ISPECL
   [`\p:num->num. p permutes 1..K * L`;
    `\p. nsum(1..K * L) (\i. ((i - 1) DIV K) * (rr:num->num)(p i))`;
    `(&L - &1) / &2 * &(nsum(1..K * L) (rr:num->num))`; `G1:real`]
   TL_LAURENT_CORE_WINDOW) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [MESON_TAC[PERMUTES_I]; ALL_TAC] THEN
    X_GEN_TAC `p:num->num` THEN DISCH_TAC THEN
    SIMP_TAC[TL_LAURENT_CORE_CENTRED_SUM;
             ASSUME `(p:num->num) permutes 1..K * L`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U1:num` (X_CHOOSE_THEN `V1:num`
    (CONJUNCTS_THEN2 (LABEL_TAC "w1") STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL
   [`\p:num->num. p permutes 1..K * L`;
    `\p. nsum(1..K * L) (\i. ((i - 1) DIV K) * (ss:num->num)(p i))`;
    `(&L - &1) / &2 * &(nsum(1..K * L) (ss:num->num))`; `G2:real`]
   TL_LAURENT_CORE_WINDOW) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [MESON_TAC[PERMUTES_I]; ALL_TAC] THEN
    X_GEN_TAC `p:num->num` THEN DISCH_TAC THEN
    SIMP_TAC[TL_LAURENT_CORE_CENTRED_SUM;
             ASSUME `(p:num->num) permutes 1..K * L`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U2:num` (X_CHOOSE_THEN `V2:num`
    (CONJUNCTS_THEN2 (LABEL_TAC "w2") STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `!p. p permutes 1..K * L
        ==> U1 <= nsum(1..K * L) (\i. ((i - 1) DIV K) * (rr:num->num)(p i)) /\
            nsum(1..K * L) (\i. ((i - 1) DIV K) * rr(p i)) <= V1 /\
            U2 <= nsum(1..K * L) (\i. ((i - 1) DIV K) * (ss:num->num)(p i)) /\
            nsum(1..K * L) (\i. ((i - 1) DIV K) * ss(p i)) <= V2`
  (LABEL_TAC "win") THENL
   [X_GEN_TAC `p:num->num` THEN DISCH_TAC THEN
    USE_THEN "w1" (fun th -> MP_TAC(MP (SPEC `p:num->num` th)
      (ASSUME `(p:num->num) permutes 1..K * L`))) THEN
    USE_THEN "w2" (fun th -> MP_TAC(MP (SPEC `p:num->num` th)
      (ASSUME `(p:num->num) permutes 1..K * L`))) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `U1 <= V1 /\ U2 <= V2` STRIP_ASSUME_TAC THENL
   [USE_THEN "win" (MP_TAC o SPEC `I:num->num`) THEN
    REWRITE_TAC[PERMUTES_I] THEN ARITH_TAC;
    ALL_TAC] THEN
  (* the algebraic integer omega of K: the determinant times the window *)
  (* factors, written as a polynomial in be1, ga1, be2, ga2              *)
  ABBREV_TAC
   `om = \k. vsum {p | p permutes 1..K * L}
               (\p. Cx(sign p) *
                    cproduct(1..K * L)
                      (\i. Cx(&(binom((rr:num->num)(p i) * b2 +
                                      (ss:num->num)(p i) * b1,
                                      (i - 1) MOD K)))) *
                    (be1:num->complex) k pow
                      (nsum(1..K * L) (\i. ((i - 1) DIV K) * rr(p i)) - U1) *
                    (ga1:num->complex) k pow
                      (V1 - nsum(1..K * L) (\i. ((i - 1) DIV K) * rr(p i))) *
                    (be2:num->complex) k pow
                      (nsum(1..K * L) (\i. ((i - 1) DIV K) * ss(p i)) - U2) *
                    (ga2:num->complex) k pow
                      (V2 -
                       nsum(1..K * L) (\i. ((i - 1) DIV K) * ss(p i))))` THEN
  SUBGOAL_THEN
   `!k. k IN 1..n
        ==> (om:num->complex) k =
            ga1 k pow V1 / be1 k pow U1 * ga2 k pow V2 / be2 k pow U2 *
            ring_det complex_ring (1..K * L)
              (\i j. Cx(&(binom((rr:num->num) j * b2 + (ss:num->num) j * b1,
                                (i - 1) MOD K))) *
                     ((be1:num->complex) k / (ga1:num->complex) k)
                       pow (((i - 1) DIV K) * rr j) *
                     ((be2:num->complex) k / (ga2:num->complex) k)
                       pow (((i - 1) DIV K) * ss j))`
  (LABEL_TAC "omk") THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "nz" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `k:num` th)
      (ASSUME `k IN 1..n`))) THEN
    EXPAND_TAC "om" THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL
     [`K * L`;
      `\i j. Cx(&(binom((rr:num->num) j * b2 + (ss:num->num) j * b1,
                        (i - 1) MOD K)))`;
      `\i. (i - 1) DIV K`; `rr:num->num`; `ss:num->num`;
      `(be1:num->complex) k`; `(ga1:num->complex) k`;
      `(be2:num->complex) k`; `(ga2:num->complex) k`;
      `U1:num`; `V1:num`; `U2:num`; `V2:num`] LAURENT_ALG_CDET_WINDOW) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "win" ACCEPT_TAC;
    ALL_TAC] THEN
  (* the bound at every conjugate: row change with centre X / 2 *)
  SUBGOAL_THEN
   `!k. k IN 1..n
        ==> norm((om:num->complex) k) <=
            &(FACT(K * L)) *
            product(1..K * L)
              (\i. (&((R - 1) * b2 + (S - 1) * b1) / &2) pow ((i - 1) MOD K) /
                   &(FACT((i - 1) MOD K))) *
            max (norm((be1:num->complex) k)) (norm((ga1:num->complex) k))
              pow (V1 - U1) *
            max (norm((be2:num->complex) k)) (norm((ga2:num->complex) k))
              pow (V2 - U2)`
  (LABEL_TAC "bnd") THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "nz" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `k:num` th)
      (ASSUME `k IN 1..n`))) THEN
    USE_THEN "omk" (fun th -> REWRITE_TAC[MP (SPEC `k:num` th)
      (ASSUME `k IN 1..n`)]) THEN
    MP_TAC(ISPECL [`K:num`; `L:num`; `1`;
                   `Cx(&((R - 1) * b2 + (S - 1) * b1) / &2)`;
                   `\j. (rr:num->num) j * b2 + (ss:num->num) j * b1`;
                   `\l j. ((be1:num->complex) k / (ga1:num->complex) k)
                             pow (l * (rr:num->num) j) *
                          ((be2:num->complex) k / (ga2:num->complex) k)
                             pow (l * (ss:num->num) j)`]
      BINOM_CDET_ROW_CHANGE) THEN
    REWRITE_TAC[LE_REFL; REAL_DIV_1; REAL_POW_ONE] THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `norm(cproduct(1..K * L) (\i. Cx(&1 / &(FACT((i - 1) MOD K))))) *
      (&(FACT(K * L)) *
       product(1..K * L)
         (\i. (&((R - 1) * b2 + (S - 1) * b1) / &2) pow ((i - 1) MOD K)) *
       max (norm((be1:num->complex) k)) (norm((ga1:num->complex) k))
         pow (V1 - U1) *
       max (norm((be2:num->complex) k)) (norm((ga2:num->complex) k))
         pow (V2 - U2))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LAURENT_ALG_NORM_REARRANGE THEN
      MATCH_MP_TAC LAURENT_ALG_CDET_WINDOW_BOUND THEN REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
        USE_THEN "win" ACCEPT_TAC;
        ALL_TAC] THEN
      X_GEN_TAC `p:num->num` THEN DISCH_TAC THEN
      MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REWRITE_TAC[COMPLEX_NORM_POW; GSYM CX_SUB; COMPLEX_NORM_CX] THEN
      SIMP_TAC[REAL_POW_LE; REAL_ABS_POS] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC LAURENT_ALG_CENTRE_BOUND THEN
      SUBGOAL_THEN `(p:num->num) i IN 1..K * L` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`p:num->num`; `1..K * L`; `i:num`]
          PERMUTES_IN_IMAGE) THEN
        ASM_REWRITE_TAC[IN_NUMSEG];
        ALL_TAC] THEN
      USE_THEN "rs" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `(p:num->num) i` th)
        (ASSUME `(p:num->num) i IN 1..K * L`))) THEN
      MATCH_MP_TAC LE_ADD2 THEN CONJ_TAC THEN MATCH_MP_TAC LE_MULT2 THEN
      REWRITE_TAC[LE_REFL] THENL
       [UNDISCH_TAC `(rr:num->num)((p:num->num) i) < R`;
        UNDISCH_TAC `(ss:num->num)((p:num->num) i) < S`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[NORM_CPRODUCT; FINITE_NUMSEG; COMPLEX_NORM_CX] THEN
    SUBGOAL_THEN
     `product(1..K * L) (\i. abs(&1 / &(FACT((i - 1) MOD K)))) =
      product(1..K * L) (\i. &1 / &(FACT((i - 1) MOD K)))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC REAL_LE_DIV THEN
      REWRITE_TAC[REAL_POS];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `product(1..K * L)
        (\i. (&((R - 1) * b2 + (S - 1) * b1) / &2) pow ((i - 1) MOD K) /
             &(FACT((i - 1) MOD K))) =
      product(1..K * L)
        (\i. (&((R - 1) * b2 + (S - 1) * b1) / &2) pow ((i - 1) MOD K)) *
      product(1..K * L) (\i. &1 / &(FACT((i - 1) MOD K)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM PRODUCT_MUL_NUMSEG] THEN
      MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[real_div; REAL_MUL_LID];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the value at the real conjugate k = 1 *)
  SUBGOAL_THEN
   `(om:num->complex) 1 =
    ga1 1 pow V1 / be1 1 pow U1 * ga2 1 pow V2 / be2 1 pow U2 *
    Cx(ring_det real_ring (1..K * L)
         (\i j. &(binom((rr:num->num) j * b2 + (ss:num->num) j * b1,
                        (i - 1) MOD K)) *
                x1 pow (((i - 1) DIV K) * rr j) *
                x2 pow (((i - 1) DIV K) * ss j)))`
  (LABEL_TAC "om1") THENL
   [USE_THEN "omk" (fun th -> REWRITE_TAC[MP (SPEC `1` th)
      (ASSUME `1 IN 1..n`)]) THEN
    SUBGOAL_THEN `(be1:num->complex) 1 / ga1 1 = Cx x1 /\
                  (be2:num->complex) 1 / ga2 1 = Cx x2`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THEN
      MATCH_MP_TAC(COMPLEX_FIELD
       `~(g = Cx(&0)) /\ b = x * g ==> b / g = x`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM CX_POW; GSYM CX_MUL; CDET_CX];
    ALL_TAC] THEN
  (* omega is an algebraic integer of K *)
  SUBGOAL_THEN `nf_alg_int n r (om:num->complex)` ASSUME_TAC THENL
   [EXPAND_TAC "om" THEN MATCH_MP_TAC LAURENT_ALG_INT_VSUM THEN
    EXISTS_TAC `c:num->real` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [SIMP_TAC[FINITE_PERMUTATIONS; FINITE_NUMSEG]; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `p:num->num` THEN DISCH_TAC THEN
    SIMP_TAC[GSYM CX_PRODUCT; FINITE_NUMSEG] THEN
    MATCH_MP_TAC LAURENT_ALG_INT_MONOMIAL THEN EXISTS_TAC `c:num->real` THEN
    REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THEN REWRITE_TAC[INTEGER_SIGN] THEN
    MATCH_MP_TAC INTEGER_PRODUCT THEN REWRITE_TAC[INTEGER_CLOSED];
    ALL_TAC] THEN
  (* Liouville: the norm of omega is a non-zero integer *)
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`; `om:num->complex`;
    `\k. &(FACT(K * L)) *
         product(1..K * L)
           (\i. (&((R - 1) * b2 + (S - 1) * b1) / &2) pow ((i - 1) MOD K) /
                &(FACT((i - 1) MOD K))) *
         max (norm((be1:num->complex) k)) (norm((ga1:num->complex) k))
           pow (V1 - U1) *
         max (norm((be2:num->complex) k)) (norm((ga2:num->complex) k))
           pow (V2 - U2)`]
    NF_LIOUVILLE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      USE_THEN "om1" SUBST1_TAC THEN
      REWRITE_TAC[COMPLEX_ENTIRE; complex_div; COMPLEX_INV_EQ_0;
                  COMPLEX_POW_EQ_0; CX_INJ; DE_MORGAN_THM] THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN USE_THEN "bnd" MATCH_MP_TAC THEN
      UNDISCH_TAC `k IN 2..n` THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC];
    ALL_TAC] THEN
  (* logarithms *)
  SUBGOAL_THEN `norm((be1:num->complex) 1) = x1 * norm((ga1:num->complex) 1) /\
                norm((be2:num->complex) 1) = x2 * norm((ga2:num->complex) 1)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_ABS_REFL] THENL
     [UNDISCH_TAC `&1 <= x1`; UNDISCH_TAC `&1 <= x2`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `K = 1 \/ &0 < &((R - 1) * b2 + (S - 1) * b1) / &2`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `K = 1` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
    MP_TAC(ISPECL [`K:num`; `L:num`; `b1:num`; `b2:num`; `R:num`; `S:num`;
                   `rr:num->num`; `ss:num->num`; `x1:real`; `x2:real`]
      LAURENT_ALG_X_POS) THEN
    ANTS_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`1 <= K`; `~(K = 1)`] THEN ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      USE_THEN "rs" ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. &0 < (&((R - 1) * b2 + (S - 1) * b1) / &2) pow ((i - 1) MOD K) /
             &(FACT((i - 1) MOD K))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN
    REWRITE_TAC[REAL_OF_NUM_LT; FACT_LT] THEN
    ASM_CASES_TAC `K = 1` THENL
     [ASM_REWRITE_TAC[MOD_1; real_pow; REAL_LT_01];
      MATCH_MP_TAC REAL_POW_LT THEN
      UNDISCH_TAC `K = 1 \/ &0 < &((R - 1) * b2 + (S - 1) * b1) / &2` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < product(1..K * L)
          (\i. (&((R - 1) * b2 + (S - 1) * b1) / &2) pow ((i - 1) MOD K) /
               &(FACT((i - 1) MOD K)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LT_NUMSEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. k IN 2..n
        ==> &0 < max (norm((be1:num->complex) k))
                     (norm((ga1:num->complex) k)) /\
            &0 < max (norm((be2:num->complex) k)) (norm((ga2:num->complex) k))`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `k IN 1..n` ASSUME_TAC THENL
     [UNDISCH_TAC `k IN 2..n` THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "nz" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `k:num` th)
      (ASSUME `k IN 1..n`))) THEN
    CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 < b ==> &0 < max a b`) THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_NZ];
    ALL_TAC] THEN
  ABBREV_TAC
   `Dt = ring_det real_ring (1..K * L)
          (\i j. &(binom((rr:num->num) j * b2 + (ss:num->num) j * b1,
                         (i - 1) MOD K)) *
                 x1 pow (((i - 1) DIV K) * rr j) *
                 x2 pow (((i - 1) DIV K) * ss j))` THEN
  SUBGOAL_THEN `&0 < abs Dt` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_ABS_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < x1 /\ &0 < x2 /\ &0 < norm((ga1:num->complex) 1) /\
                &0 < norm((ga2:num->complex) 1)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_NORM_NZ] THEN
    MAP_EVERY UNDISCH_TAC [`&1 <= x1`; `&1 <= x2`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "om1" SUBST1_TAC THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_DIV; COMPLEX_NORM_POW;
              COMPLEX_NORM_CX] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LOG_MONO_LE_IMP o
    CONJ (REAL_ARITH `&0 < &1`)) THEN
  REWRITE_TAC[LOG_1] THEN
  SUBGOAL_THEN
   `&0 < norm((ga1:num->complex) 1) pow V1 / (x1 * norm(ga1 1)) pow U1 /\
    &0 < norm((ga2:num->complex) 1) pow V2 / (x2 * norm(ga2 1)) pow U2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_POW_LT THEN TRY(MATCH_MP_TAC REAL_LT_MUL) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) LOG_MUL o rand o lhand o snd) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC PRODUCT_POS_LT_NUMSEG THEN X_GEN_TAC `k:num` THEN
      STRIP_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `k IN 2..n` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[IN_NUMSEG]; ALL_TAC] THEN
      FIRST_X_ASSUM(fun th -> STRIP_ASSUME_TAC(MP (SPEC `k:num` th)
        (ASSUME `k IN 2..n`))) THEN
      REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; FACT_LT]];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`x1:real`; `norm((ga1:num->complex) 1)`; `x2:real`;
                 `norm((ga2:num->complex) 1)`; `abs Dt`;
                 `U1:num`; `V1:num`; `U2:num`; `V2:num`]
    LAURENT_ALG_LOG_PREF) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
   [`n:num`; `&(FACT(K * L))`;
    `product(1..K * L)
       (\i. (&((R - 1) * b2 + (S - 1) * b1) / &2) pow ((i - 1) MOD K) /
            &(FACT((i - 1) MOD K)))`;
    `\k. max (norm((be1:num->complex) k)) (norm((ga1:num->complex) k))`;
    `\k. max (norm((be2:num->complex) k)) (norm((ga2:num->complex) k))`;
    `V1 - U1`; `V2 - U2`] LAURENT_ALG_LOG_BK)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REWRITE_TAC[REAL_OF_NUM_LT; FACT_LT];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`K:num`; `L:num`; `&((R - 1) * b2 + (S - 1) * b1) / &2`]
    LAURENT_ALG_LOG_PP) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_SUB; ASSUME `U1 <= V1`; ASSUME `U2 <= V2`] THEN
  DISCH_THEN(LABEL_TAC "liou") THEN
  MP_TAC(ISPECL [`n:num`; `be1:num->complex`; `ga1:num->complex`; `x1:real`]
    LAURENT_ALG_HEIGHT_SPLIT) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `be2:num->complex`; `ga2:num->complex`; `x2:real`]
    LAURENT_ALG_HEIGHT_SPLIT) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`; `be1:num->complex`;
                 `ga1:num->complex`; `x1:real`] NF_PROJ_HEIGHT_GE) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`; `be2:num->complex`;
                 `ga2:num->complex`; `x2:real`] NF_PROJ_HEIGHT_GE) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  MATCH_MP_TAC LAURENT_ALG_ARITH_REAL THEN
  MAP_EVERY EXISTS_TAC
   [`&U1:real`; `&V1:real`; `log(norm((ga1:num->complex) 1))`;
    `sum(2..n) (\k. log(max (norm((be1:num->complex) k))
                            (norm((ga1:num->complex) k))))`;
    `&U2:real`; `&V2:real`; `log(norm((ga2:num->complex) 1))`;
    `sum(2..n) (\k. log(max (norm((be2:num->complex) k))
                            (norm((ga2:num->complex) k))))`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN FIRST_ASSUM ACCEPT_TAC;
    MAP_EVERY UNDISCH_TAC
     [`log x1 <= &n * nf_proj_height n be1 ga1`;
      `&n * nf_proj_height n be1 ga1 =
       log x1 + log(norm((ga1:num->complex) 1)) +
       sum(2..n) (\k. log(max (norm((be1:num->complex) k))
                              (norm((ga1:num->complex) k))))`] THEN
    REAL_ARITH_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC LOG_POS THEN FIRST_ASSUM ACCEPT_TAC;
    MAP_EVERY UNDISCH_TAC
     [`log x2 <= &n * nf_proj_height n be2 ga2`;
      `&n * nf_proj_height n be2 ga2 =
       log x2 + log(norm((ga2:num->complex) 1)) +
       sum(2..n) (\k. log(max (norm((be2:num->complex) k))
                              (norm((ga2:num->complex) k))))`] THEN
    REAL_ARITH_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    REMOVE_THEN "liou" MP_TAC THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The core (Laurent Theorem 1 at mu = 1, D = n): g-lemma, analytic upper    *)
(* bound, arithmetic lower bound and laurent_main are incompatible unless    *)
(* rho^-N < Lambda prime.                                                    *)
(* ------------------------------------------------------------------------- *)

let LAURENT_CORE_NF = prove
 (`!n c r be1 ga1 be2 ga2 x1 x2 b1 b2 K L R S N (rr:num->num) (ss:num->num)
    rho a1 a2.
     nf_data n c r /\
     nf_alg_int n r be1 /\ nf_alg_int n r ga1 /\
     nf_alg_int n r be2 /\ nf_alg_int n r ga2 /\
     ~(ga1 1 = Cx(&0)) /\ ~(ga2 1 = Cx(&0)) /\
     be1 1 = Cx x1 * ga1 1 /\ be2 1 = Cx x2 * ga2 1 /\ &1 <= x1 /\ &1 <= x2 /\
     1 <= b1 /\ 1 <= b2 /\ 1 <= K /\ 1 <= L /\ 2 <= R /\ 1 <= S /\
     N = K * L /\ (!j. j IN 1..N ==> rr j < R /\ ss j < S) /\
     ~(ring_det real_ring (1..N)
         (\i j. &(binom(rr j * b2 + ss j * b1,(i - 1) MOD K)) *
                x1 pow (((i - 1) DIV K) * rr j) *
                x2 pow (((i - 1) DIV K) * ss j)) = &0) /\
     &b1 * log x1 <= &b2 * log x2 /\ &1 < rho /\
     (rho - &1) * log x1 + &2 * &n * nf_proj_height n be1 ga1 <= a1 /\
     (rho - &1) * log x2 + &2 * &n * nf_proj_height n be2 ga2 <= a2 /\
     laurent_main n rho b1 b2 a1 a2 K L R S
     ==> inv(rho pow N) <
         &(L * S) * abs(&b2 * log x2 - &b1 * log x1) / (&2 * &b2) *
         exp(&(L * S) * abs(&b2 * log x2 - &b1 * log x1) / (&2 * &b2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_THEN `N = K * L` SUBST_ALL_TAC THEN
  UNDISCH_TAC `laurent_main n rho b1 b2 a1 a2 K L R S` THEN
  REWRITE_TAC[laurent_main] THEN DISCH_TAC THEN
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
  SUBGOAL_THEN `&0 < x1 /\ &0 < x2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&1 <= x1`; `&1 <= x2`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log x1 /\ &0 <= log x2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LOG_POS THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`x1:real`; `x2:real`; `b1:num`; `b2:num`; `K:num`; `L:num`;
                `R:num`; `S:num`; `K * L`; `rr:num->num`; `ss:num->num`]
    LAURENT_GLEMMA_BOTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `g = &1 / &4 - &(K * L) / (&12 * &R * &S)` THEN
  ABBREV_TAC `G1 = &L * &R * &(K * L) / &2 * g` THEN
  ABBREV_TAC `G2 = &L * &S * &(K * L) / &2 * g` THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`;
                `be1:num->complex`; `ga1:num->complex`; `be2:num->complex`;
                `ga2:num->complex`; `x1:real`; `x2:real`; `b1:num`; `b2:num`;
                `K:num`; `L:num`; `K * L`; `R:num`; `S:num`;
                `rr:num->num`; `ss:num->num`; `G1:real`; `G2:real`]
    LAURENT_ARITH_NF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`b1:num`; `b2:num`; `K:num`; `L:num`; `R:num`; `S:num`;
                `K * L`; `rr:num->num`; `ss:num->num`; `log x1`;
                `log x2`; `rho:real`; `G1:real`; `G2:real`]
    TWOLOG_LAURENT_ANALYTIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`x1:real`; `x2:real`; `b1:num`; `b2:num`; `K:num`;
                `rr:num->num`; `ss:num->num`] LAURENT_EXP_MATRIX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  DISCH_TAC THEN
  ABBREV_TAC
   `Dt = ring_det real_ring (1..K * L)
          (\i j. &(binom(rr j * b2 + ss j * b1,(i - 1) MOD K)) *
                 x1 pow (((i - 1) DIV K) * rr j) *
                 x2 pow (((i - 1) DIV K) * ss j))` THEN
  SUBGOAL_THEN `&0 < abs Dt` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_ABS_NZ]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LOG_MONO_LE_IMP o
    CONJ (ASSUME `&0 < abs Dt`)) THEN
  SIMP_TAC[TL_LAURENT_CORE_LOG_UPPER; ASSUME `1 <= K`; ASSUME `&0 < rho`;
           ASSUME `&0 < &((R - 1) * b2 + (S - 1) * b1) / &2`] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`&n:real`; `&(K * L)`; `&K`; `&L`; `&R`; `&S`; `g:real`;
                `rho:real`; `log(&2)`; `log(&(FACT(K * L)))`; `log rho`;
                `log(&((R - 1) * b2 + (S - 1) * b1) / &2)`;
                `sum(1..K - 1) (\k. log(&(FACT k)))`;
                `&(nsum(1..K * L) rr)`; `&(nsum(1..K * L) ss)`;
                `log x1`; `log x2`; `&n * nf_proj_height n be1 ga1`;
                `&n * nf_proj_height n be2 ga2`;
                `a1:real`; `a2:real`; `log(abs Dt)`; `G1:real`; `G2:real`]
    LAURENT_CORE_FINAL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE FIRST_ASSUM(ACCEPT_TAC o SYM) ORELSE
     REWRITE_TAC[REAL_OF_NUM_MUL]);
    REWRITE_TAC[TAUT `~p ==> F <=> p`] THEN FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Real lemmas for the final step, Liouville inequality in K for the linear  *)
(* form v log x2 - u log x1, and Lambda prime to Lambda.                     *)
(* ------------------------------------------------------------------------- *)

let LAURENT_ALG_LOG_GE = prove
 (`!z. &0 < z ==> &1 - inv z <= log z`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `inv z` LOG_LE_SUB_1) THEN
  ASM_SIMP_TAC[REAL_LT_INV_EQ; LOG_INV] THEN REAL_ARITH_TAC);;

let LAURENT_ALG_SUB_LE_LOG = prove
 (`!A B. &1 <= A /\ &1 <= B ==> abs(A - B) <= A * B * abs(log A - log B)`,
  SUBGOAL_THEN
   `!A B. &1 <= B /\ B <= A ==> A - B <= A * (log A - log B)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&0 < A /\ &0 < B` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `B / A` LOG_LE_SUB_1) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; LOG_DIV] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `A * (log B - log A) <= A * (B / A - &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `A * (B / A - &1) = B - A` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < A` THEN CONV_TAC REAL_FIELD; REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= log A /\ &0 <= log B` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISJ_CASES_TAC(REAL_ARITH `B <= A \/ A <= B:real`) THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`A:real`; `B:real`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `log B <= log A` ASSUME_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `A * (log A - log B) <= A * B * (log A - log B)` MP_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `abs(log A - log B) = log A - log B /\ abs(A - B) = A - B`
    (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`A - B <= A * (log A - log B)`] THEN
    REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`B:real`; `A:real`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `log A <= log B` ASSUME_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `B * (log B - log A) <= A * B * (log B - log A)` MP_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `abs(log A - log B) = log B - log A /\ abs(A - B) = B - A`
    (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`B - A <= B * (log B - log A)`] THEN
    REAL_ARITH_TAC]);;

let LAURENT_ALG_INT_POW2 = prove
 (`!n c r (a:num->complex) (b:num->complex) i j.
     nf_data n c r /\ nf_alg_int n r a /\ nf_alg_int n r b
     ==> nf_alg_int n r (\k. a k pow i * b k pow j)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`;
                 `\k. (a:num->complex) k pow i`; `\k. (b:num->complex) k pow j`]
    LAURENT_ALG_INT_MUL) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC LAURENT_ALG_INT_POW THEN
  EXISTS_TAC `c:num->real` THEN ASM_REWRITE_TAC[]);;

let LAURENT_ALG_OMEGA_THETA = prove
 (`!H. &0 < H ==> &2 <= sqrt(laurent_omega H * laurent_theta H)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[laurent_omega; laurent_theta] THEN
  ABBREV_TAC `s = sqrt(&1 + inv(&4 * H pow 2))` THEN
  SUBGOAL_THEN `&1 <= s` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN MATCH_MP_TAC REAL_LE_RSQRT THEN
    REWRITE_TAC[REAL_ARITH `&1 pow 2 <= &1 + x <=> &0 <= x`] THEN
    REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= inv(&2 * H)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RSQRT THEN
  SUBGOAL_THEN `&2 pow 2 = &4 * &1` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC);;

let LAURENT_ALG_LAMBDA_PRIME = prove
 (`!(rho:real) N (m:real) (b:real) (t:real) (Tb:real) (Y:real).
     &1 < rho /\ &1 <= m /\ &1 <= b /\ &0 < t /\ &20 <= Tb /\ &0 < Y /\
     &N * log rho <= Tb /\ m <= &186 / &100 * Y /\
     inv(rho pow N) < m * t / (&2 * b) * exp(m * t / (&2 * b))
     ==> --(Tb + log Y) <= log t`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `inv(rho pow N) < m * t / (&2 * b) * exp(m * t / (&2 * b))` THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN DISCH_TAC THEN
  ABBREV_TAC `y = m * t / (&2 * b)` THEN
  SUBGOAL_THEN `&0 < y` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `log t = log(&2 * b) + log y - log m` SUBST1_TAC THENL
   [SUBGOAL_THEN `t = (&2 * b) * y / m` SUBST1_TAC THENL
     [EXPAND_TAC "y" THEN
      SUBGOAL_THEN `~(m = &0) /\ ~(b = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &2 * b /\ &0 < m /\ &0 < y / m` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_MUL; LOG_DIV] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `--(&N * log rho) < log y + y` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inv(rho pow N)`; `y * exp y`] LOG_MONO_LT_IMP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN MATCH_MP_TAC REAL_POW_LT THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < rho pow N` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_INV; LOG_POW; LOG_MUL; REAL_EXP_POS_LT; LOG_EXP;
                 REAL_ARITH `&1 < rho ==> &0 < rho`];
    ALL_TAC] THEN
  SUBGOAL_THEN `log m <= log(&186 / &100) + log Y` ASSUME_TAC THENL
   [SUBGOAL_THEN `log(&186 / &100) + log Y = log(&186 / &100 * Y)`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC LOG_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&2) <= log(&2 * b)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `log(&186 / &100) = log(&2) + log(&93 / &100)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&186 / &100 = &2 * &93 / &100` SUBST1_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC LOG_MUL THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&93 / &100) <= --(&7 / &100)` ASSUME_TAC THENL
   [MP_TAC(SPEC `&93 / &100` LOG_LE_SUB_1) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `y <= &7 / &100` THENL
   [MAP_EVERY UNDISCH_TAC
     [`--(&N * log rho) < log y + y`; `&N * log rho <= Tb`;
      `log m <= log(&186 / &100) + log Y`; `log(&2) <= log(&2 * b)`;
      `log(&186 / &100) = log(&2) + log(&93 / &100)`;
      `log(&93 / &100) <= --(&7 / &100)`; `y <= &7 / &100`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&7 / &100) <= log y` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `&7 / &100` LAURENT_ALG_LOG_GE) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MAP_EVERY UNDISCH_TAC
   [`log(&7 / &100) <= log y`; `&20 <= Tb`;
    `log m <= log(&186 / &100) + log Y`; `log(&2) <= log(&2 * b)`;
    `log(&186 / &100) = log(&2) + log(&93 / &100)`;
    `log(&93 / &100) <= --(&7 / &100)`] THEN
  REAL_ARITH_TAC);;

let LAURENT_ALG_LOG4 = prove
 (`!a g1 g2 P u v.
     &0 < a /\ &0 < g1 /\ &0 < g2 /\ &0 < P
     ==> log((a * g1 pow u * g2 pow v) * P) =
         log a + &u * log g1 + &v * log g2 + log P`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < g1 pow u /\ &0 < g2 pow v /\ &0 < g1 pow u * g2 pow v /\
                &0 < a * g1 pow u * g2 pow v` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT] THEN
    REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POW_LT];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_MUL] THEN ASM_SIMP_TAC[LOG_POW] THEN REAL_ARITH_TAC);;

let LAURENT_ALG_LIOUVILLE_LOG = prove
 (`!n c r be1 ga1 be2 ga2 x1 x2 u v.
     nf_data n c r /\
     nf_alg_int n r be1 /\ nf_alg_int n r ga1 /\
     nf_alg_int n r be2 /\ nf_alg_int n r ga2 /\
     ~(ga1 1 = Cx(&0)) /\ ~(ga2 1 = Cx(&0)) /\
     be1 1 = Cx x1 * ga1 1 /\ be2 1 = Cx x2 * ga2 1 /\ &1 <= x1 /\ &1 <= x2 /\
     ~(&v * log x2 = &u * log x1)
     ==> --((&n - &1) * log(&2) + &u * (&n * nf_proj_height n be1 ga1) +
            &v * (&n * nf_proj_height n be2 ga2))
         <= log(abs(&v * log x2 - &u * log x1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NF_DATA) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_1_IN) THEN
  SUBGOAL_THEN
   `nf_elem n r (be1:num->complex) /\ nf_elem n r (ga1:num->complex) /\
    nf_elem n r (be2:num->complex) /\ nf_elem n r (ga2:num->complex)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [nf_alg_int]);
    ALL_TAC] THEN
  SUBGOAL_THEN `~((be1:num->complex) 1 = Cx(&0)) /\
                ~((be2:num->complex) 1 = Cx(&0))` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ] THEN
    MAP_EVERY UNDISCH_TAC [`&1 <= x1`; `&1 <= x2`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. k IN 1..n ==> ~((be1:num->complex) k = Cx(&0)) /\
                      ~((ga1:num->complex) k = Cx(&0)) /\
                      ~((be2:num->complex) k = Cx(&0)) /\
                      ~((ga2:num->complex) k = Cx(&0))`
  (LABEL_TAC "nz") THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC NF_HEIGHT_ELEM_NONZERO THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `c:num->real`; `r:num->complex`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < x1 /\ &0 < x2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&1 <= x1`; `&1 <= x2`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(x2 pow v - x1 pow u = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_SUB_0] THEN DISCH_THEN(MP_TAC o AP_TERM `log`) THEN
    ASM_SIMP_TAC[LOG_POW];
    ALL_TAC] THEN
  ABBREV_TAC
   `w = \k. (be2:num->complex) k pow v * (ga1:num->complex) k pow u -
            (be1:num->complex) k pow u * (ga2:num->complex) k pow v` THEN
  SUBGOAL_THEN `nf_alg_int n r (w:num->complex)` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN MATCH_MP_TAC LAURENT_ALG_INT_SUB THEN
    EXISTS_TAC `c:num->real` THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC LAURENT_ALG_INT_POW2 THEN EXISTS_TAC `c:num->real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(w:num->complex) 1 =
    Cx(x2 pow v - x1 pow u) * ((ga1:num->complex) 1 pow u * ga2 1 pow v)`
  ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN ASM_REWRITE_TAC[COMPLEX_POW_MUL; CX_SUB; CX_POW] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`; `w:num->complex`;
    `\k. &2 * &1 *
         max (norm((be1:num->complex) k)) (norm((ga1:num->complex) k)) pow u *
         max (norm((be2:num->complex) k)) (norm((ga2:num->complex) k)) pow v`]
    NF_LIOUVILLE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      ASM_REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ; COMPLEX_POW_EQ_0; DE_MORGAN_THM];
      ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `k IN 1..n` ASSUME_TAC THENL
     [UNDISCH_TAC `k IN 2..n` THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "w" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(x:complex) <= a /\ norm(y:complex) <= a
      ==> norm(x - y) <= &2 * &1 * a`) THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    SIMP_TAC[REAL_POW_LE; NORM_POS_LE] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LOG_MONO_LE_IMP o
    CONJ (REAL_ARITH `&0 < &1`)) THEN
  REWRITE_TAC[LOG_1] THEN
  SUBGOAL_THEN
   `norm((w:num->complex) 1) =
    abs(x2 pow v - x1 pow u) * norm((ga1:num->complex) 1) pow u *
    norm((ga2:num->complex) 1) pow v`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; COMPLEX_NORM_POW];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. k IN 2..n
        ==> &0 < max (norm((be1:num->complex) k))
                     (norm((ga1:num->complex) k)) /\
            &0 < max (norm((be2:num->complex) k)) (norm((ga2:num->complex) k))`
  (LABEL_TAC "mpos") THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `k IN 1..n` ASSUME_TAC THENL
     [UNDISCH_TAC `k IN 2..n` THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "nz" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `k:num` th)
      (ASSUME `k IN 1..n`))) THEN
    CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 < b ==> &0 < max a b`) THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < product(2..n)
          (\k. &2 * &1 *
               max (norm((be1:num->complex) k)) (norm((ga1:num->complex) k))
                 pow u *
               max (norm((be2:num->complex) k)) (norm((ga2:num->complex) k))
                 pow v)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LT_NUMSEG THEN X_GEN_TAC `k:num` THEN
    STRIP_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `k IN 2..n` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_NUMSEG]; ALL_TAC] THEN
    USE_THEN "mpos" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `k:num` th)
      (ASSUME `k IN 2..n`))) THEN
    REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POW_LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < abs(x2 pow v - x1 pow u) /\
                &0 < norm((ga1:num->complex) 1) /\
                &0 < norm((ga2:num->complex) 1)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_ABS_NZ; COMPLEX_NORM_NZ]; ALL_TAC] THEN
  MP_TAC(ISPECL [`abs(x2 pow v - x1 pow u)`; `norm((ga1:num->complex) 1)`;
                 `norm((ga2:num->complex) 1)`;
                 `product(2..n)
                    (\k. &2 * &1 *
                         max (norm((be1:num->complex) k))
                             (norm((ga1:num->complex) k)) pow u *
                         max (norm((be2:num->complex) k))
                             (norm((ga2:num->complex) k)) pow v)`;
                 `u:num`; `v:num`] LAURENT_ALG_LOG4) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
   [`n:num`; `&2`; `&1`;
    `\k. max (norm((be1:num->complex) k)) (norm((ga1:num->complex) k))`;
    `\k. max (norm((be2:num->complex) k)) (norm((ga2:num->complex) k))`;
    `u:num`; `v:num`] LAURENT_ALG_LOG_BK)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[LOG_1; REAL_ADD_RID] THEN
  MP_TAC(SPECL [`x2 pow v`; `x1 pow u`] LAURENT_ALG_SUB_LE_LOG) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE_1 THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_POW] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < abs(&v * log x2 - &u * log x1)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_ABS_NZ; REAL_SUB_0] THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `log(abs(x2 pow v - x1 pow u)) <=
    &v * log x2 + &u * log x1 + log(abs(&v * log x2 - &u * log x1))`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`abs(x2 pow v - x1 pow u)`;
                  `x2 pow v * x1 pow u * abs(&v * log x2 - &u * log x1)`]
      LOG_MONO_LE_IMP) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < x2 pow v /\ &0 < x1 pow u /\
                  &0 < x1 pow u * abs(&v * log x2 - &u * log x1)`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_MUL]; ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_MUL; LOG_POW];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `be1:num->complex`; `ga1:num->complex`; `x1:real`]
    LAURENT_ALG_HEIGHT_SPLIT) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
                  DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `be2:num->complex`; `ga2:num->complex`; `x2:real`]
    LAURENT_ALG_HEIGHT_SPLIT) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
                  DISCH_THEN SUBST1_TAC] THEN
  UNDISCH_TAC
   `log(abs(x2 pow v - x1 pow u)) <=
    &v * log x2 + &u * log x1 + log(abs(&v * log x2 - &u * log x1))` THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Collisions of the two grid maps (r,s) -> x1^r x2^s and (r,s) ->           *)
(* r b2 + s b1: small coefficients u, v and the Liouville lower bounds.      *)
(* ------------------------------------------------------------------------- *)

let LAURENT_ALG_COLL_UV = prove
 (`!l1 l2 R S r s r' s'.
     &0 < l1 /\ &0 < l2 /\ r < R /\ r' < R /\ s < S /\ s' < S /\
     ~(r = r' /\ s = s') /\ &r * l1 + &s * l2 = &r' * l1 + &s' * l2
     ==> ?u v. 1 <= u /\ u < R /\ 1 <= v /\ v < S /\ &u * l1 = &v * l2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(r:num = r')` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(r':num = r' /\ (s:num) = s')` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `&r' * l1 + &s * l2 = &r' * l1 + &s' * l2` THEN
    REWRITE_TAC[REAL_EQ_ADD_LCANCEL; REAL_EQ_MUL_RCANCEL;
                GSYM REAL_OF_NUM_EQ] THEN
    UNDISCH_TAC `&0 < l2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ARITH_RULE `~(r:num = r') ==> r < r' \/ r' < r`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `s' < (s:num)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
      SUBGOAL_THEN `&0 < (&r' - &r) * l1` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_LT];
        ALL_TAC] THEN
      SUBGOAL_THEN `(&r' - &r) * l1 = (&s - &s') * l2` SUBST1_TAC THENL
       [UNDISCH_TAC `&r * l1 + &s * l2 = &r' * l1 + &s' * l2` THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[REAL_MUL_POS_LT] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`r' - r:num`; `s - s':num`] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_ARITH_TAC) THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; LT_IMP_LE] THEN
    UNDISCH_TAC `&r * l1 + &s * l2 = &r' * l1 + &s' * l2` THEN
    REAL_ARITH_TAC;
    SUBGOAL_THEN `s < (s':num)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
      SUBGOAL_THEN `&0 < (&r - &r') * l1` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_LT];
        ALL_TAC] THEN
      SUBGOAL_THEN `(&r - &r') * l1 = (&s' - &s) * l2` SUBST1_TAC THENL
       [UNDISCH_TAC `&r * l1 + &s * l2 = &r' * l1 + &s' * l2` THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[REAL_MUL_POS_LT] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`r - r':num`; `s' - s:num`] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_ARITH_TAC) THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; LT_IMP_LE] THEN
    UNDISCH_TAC `&r * l1 + &s * l2 = &r' * l1 + &s' * l2` THEN
    REAL_ARITH_TAC]);;

let LAURENT_ALG_MCOLL = prove
 (`!n c r be1 ga1 be2 ga2 x1 x2 b1 b2 u v.
     nf_data n c r /\
     nf_alg_int n r be1 /\ nf_alg_int n r ga1 /\
     nf_alg_int n r be2 /\ nf_alg_int n r ga2 /\
     ~(ga1 1 = Cx(&0)) /\ ~(ga2 1 = Cx(&0)) /\
     be1 1 = Cx x1 * ga1 1 /\ be2 1 = Cx x2 * ga2 1 /\ &1 < x1 /\ &1 < x2 /\
     1 <= v /\ &u * log x1 = &v * log x2 /\ ~(&b2 * log x2 = &b1 * log x1)
     ==> --((&n - &1) * log(&2) + &n * nf_proj_height n be1 ga1 + log(&v))
         <= log(abs(&b2 * log x2 - &b1 * log x1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < log x1` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`;
                `be1:num->complex`; `ga1:num->complex`; `be2:num->complex`;
                `ga2:num->complex`; `x1:real`; `x2:real`; `1`; `0`]
    LAURENT_ALG_LIOUVILLE_LOG) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [UNDISCH_TAC `&1 < x1` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `&1 < x2` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < log x1` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_ADD_RID; REAL_SUB_LZERO;
              REAL_ABS_NEG] THEN
  SUBGOAL_THEN `abs(log x1) = log x1` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < log x1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `&v * (&b2 * log x2 - &b1 * log x1) = (&b2 * &u - &b1 * &v) * log x1`
  ASSUME_TAC THENL
   [UNDISCH_TAC `&u * log x1 = &v * log x2` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &v` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN UNDISCH_TAC `1 <= v` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= abs(&b2 * &u - &b1 * &v)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_MUL] THEN
      MATCH_MP_TAC INTEGER_SUB THEN REWRITE_TAC[INTEGER_CLOSED];
      DISCH_TAC THEN
      UNDISCH_TAC
       `&v * (&b2 * log x2 - &b1 * log x1) =
        (&b2 * &u - &b1 * &v) * log x1` THEN
      ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ENTIRE] THEN
      UNDISCH_TAC `~(&b2 * log x2 = &b1 * log x1)` THEN
      UNDISCH_TAC `&0 < &v` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `log x1 <= &v * abs(&b2 * log x2 - &b1 * log x1)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&v * abs(&b2 * log x2 - &b1 * log x1) =
                  abs(&v * (&b2 * log x2 - &b1 * log x1))` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM]; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `&v * (&b2 * log x2 - &b1 * log x1) =
                        (&b2 * &u - &b1 * &v) * log x1`] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs(log x1) = log x1` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < log x1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < log x1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < abs(&b2 * log x2 - &b1 * log x1)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_ABS_NZ; REAL_SUB_0] THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`log x1`; `&v * abs(&b2 * log x2 - &b1 * log x1)`]
    LOG_MONO_LE_IMP) THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[LOG_MUL] THEN
  UNDISCH_TAC
   `--((&n - &1) * log(&2) + &n * nf_proj_height n be1 ga1) <= log(log x1)` THEN
  REAL_ARITH_TAC);;

let LAURENT_ALG_ACOLL = prove
 (`!n c r be1 ga1 be2 ga2 x1 x2 b1 b2 u v.
     nf_data n c r /\
     nf_alg_int n r be1 /\ nf_alg_int n r ga1 /\
     nf_alg_int n r be2 /\ nf_alg_int n r ga2 /\
     ~(ga1 1 = Cx(&0)) /\ ~(ga2 1 = Cx(&0)) /\
     be1 1 = Cx x1 * ga1 1 /\ be2 1 = Cx x2 * ga2 1 /\ &1 < x1 /\ &1 < x2 /\
     1 <= b2 /\ 1 <= v /\ u * b2 = v * b1 /\ ~(&b2 * log x2 = &b1 * log x1)
     ==> --((&n - &1) * log(&2) + &u * (&n * nf_proj_height n be1 ga1) +
            &v * (&n * nf_proj_height n be2 ga2) + log(&v))
         <= log(abs(&b2 * log x2 - &b1 * log x1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `&v * (&b2 * log x2 - &b1 * log x1) = &b2 * (&v * log x2 - &u * log x1)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `u * b2 = v * b1` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &v /\ &1 <= &b2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
    MAP_EVERY UNDISCH_TAC [`1 <= v`; `1 <= b2`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(&v * log x2 = &u * log x1)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC
     `&v * (&b2 * log x2 - &b1 * log x1) =
      &b2 * (&v * log x2 - &u * log x1)` THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_ENTIRE] THEN
    UNDISCH_TAC `~(&b2 * log x2 = &b1 * log x1)` THEN
    UNDISCH_TAC `&0 < &v` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`;
                `be1:num->complex`; `ga1:num->complex`; `be2:num->complex`;
                `ga2:num->complex`; `x1:real`; `x2:real`; `u:num`; `v:num`]
    LAURENT_ALG_LIOUVILLE_LOG) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [UNDISCH_TAC `&1 < x1` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `&1 < x2` THEN REAL_ARITH_TAC];
    DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < abs(&v * log x2 - &u * log x1) /\
                &0 < abs(&b2 * log x2 - &b1 * log x1)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_ABS_NZ; REAL_SUB_0] THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(&v * log x2 - &u * log x1) <=
                &v * abs(&b2 * log x2 - &b1 * log x1)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&v * abs(&b2 * log x2 - &b1 * log x1) =
                  abs(&v * (&b2 * log x2 - &b1 * log x1))` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM]; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `&v * (&b2 * log x2 - &b1 * log x1) =
                        &b2 * (&v * log x2 - &u * log x1)`] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  MP_TAC(SPECL [`abs(&v * log x2 - &u * log x1)`;
                `&v * abs(&b2 * log x2 - &b1 * log x1)`] LOG_MONO_LE_IMP) THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[LOG_MUL] THEN
  UNDISCH_TAC
   `--((&n - &1) * log(&2) + &u * (&n * nf_proj_height n be1 ga1) +
       &v * (&n * nf_proj_height n be2 ga2))
    <= log(abs(&v * log x2 - &u * log x1))` THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The general assembly for given parameters (exports of the numeric layer), *)
(* with b1 log x1 <= b2 log x2: collision cases and the main case.           *)
(* ------------------------------------------------------------------------- *)

let LAURENT_ALG_GEN = prove
 (`!n c r be1 ga1 be2 ga2 x1 x2 b1 b2 rho h a1 a2 K L R1 S1 R2 S2.
     nf_data n c r /\
     nf_alg_int n r be1 /\ nf_alg_int n r ga1 /\
     nf_alg_int n r be2 /\ nf_alg_int n r ga2 /\
     ~(ga1 1 = Cx(&0)) /\ ~(ga2 1 = Cx(&0)) /\
     be1 1 = Cx x1 * ga1 1 /\ be2 1 = Cx x2 * ga2 1 /\ &1 < x1 /\ &1 < x2 /\
     1 <= b1 /\ 1 <= b2 /\ &1 < rho /\ &10 <= h /\
     &1 <= a1 /\
     (rho - &1) * log x1 + &2 * &n * nf_proj_height n be1 ga1 <= a1 /\
     &1 <= a2 /\
     (rho - &1) * log x2 + &2 * &n * nf_proj_height n be2 ga2 <= a2 /\
     &n * log(&2) / &2 <= h /\
     &b1 * log x1 <= &b2 * log x2 /\ ~(&b2 * log x2 = &b1 * log x1) /\
     2 <= K /\ 2 <= L /\ 1 <= R1 /\ 1 <= S1 /\ 1 <= R2 /\ 1 <= S2 /\
     2 <= (R1 + R2) - 1 /\ 2 <= (S1 + S2) - 1 /\
     L <= R1 * S1 /\ (K - 1) * L < R2 * S2 /\
     laurent_main n rho b1 b2 a1 a2 K L ((R1 + R2) - 1) ((S1 + S2) - 1) /\
     &(K * L) * log rho <=
       laurent_C rho h a1 a2 * (h + log rho) pow 2 * a1 * a2 +
       sqrt(laurent_omega (h / log rho + &1) *
            laurent_theta (h / log rho + &1)) * (h + log rho) /\
     &(L * ((S1 + S2) - 1)) <=
       &186 / &100 * laurent_Cp rho h a1 a2 * (h + log rho) pow 2 * a1 * a2 /\
     &((R1 + R2) - 1) * a1 + &((S1 + S2) - 1) * a2 <=
       laurent_C rho h a1 a2 * (h + log rho) pow 2 * a1 * a2 / &2
     ==> --(laurent_bound rho h a1 a2) <=
         log(abs(&b2 * log x2 - &b1 * log x1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[laurent_bound] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN
   `&((R1 + R2) - 1) * a1 + &((S1 + S2) - 1) * a2 <=
    (laurent_C rho h a1 a2 * (h + log rho) pow 2 * a1 * a2) / &2`
  ASSUME_TAC THENL
   [UNDISCH_TAC
     `&((R1 + R2) - 1) * a1 + &((S1 + S2) - 1) * a2 <=
      laurent_C rho h a1 a2 * (h + log rho) pow 2 * a1 * a2 / &2` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log rho` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 * (h + log rho) <=
    sqrt(laurent_omega (h / log rho + &1) *
         laurent_theta (h / log rho + &1)) * (h + log rho)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC LAURENT_ALG_OMEGA_THETA THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `CX = laurent_C rho h a1 a2 * (h + log rho) pow 2 * a1 * a2` THEN
  ABBREV_TAC
   `SQ = sqrt(laurent_omega (h / log rho + &1) *
              laurent_theta (h / log rho + &1)) * (h + log rho)` THEN
  ABBREV_TAC `Y = laurent_Cp rho h a1 a2 * (h + log rho) pow 2 * a1 * a2` THEN
  SUBGOAL_THEN `&4 <= &(L * ((S1 + S2) - 1))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN `2 * 2 <= L * ((S1 + S2) - 1)` MP_TAC THENL
     [MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[]; ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= Y` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`&4 <= &(L * ((S1 + S2) - 1))`;
      `&(L * ((S1 + S2) - 1)) <= &186 / &100 * Y`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log Y` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN UNDISCH_TAC `&2 <= Y` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a1 <= &((R1 + R2) - 1) * a1 /\ a2 <= &((S1 + S2) - 1) * a2 /\
                &((S1 + S2) - 1) <= &((S1 + S2) - 1) * a2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `2 <= (R1 + R2) - 1` THEN ARITH_TAC;
        UNDISCH_TAC `&1 <= a1` THEN REAL_ARITH_TAC];
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `2 <= (S1 + S2) - 1` THEN ARITH_TAC;
        UNDISCH_TAC `&1 <= a2` THEN REAL_ARITH_TAC];
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log x1 /\ &0 < log x2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LOG_POS_LT THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`; `be1:num->complex`;
                 `ga1:num->complex`; `x1:real`] NF_PROJ_HEIGHT_GE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    UNDISCH_TAC `&1 < x1` THEN REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`; `be2:num->complex`;
                 `ga2:num->complex`; `x2:real`] NF_PROJ_HEIGHT_GE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    UNDISCH_TAC `&1 < x2` THEN REAL_ARITH_TAC;
    DISCH_TAC] THEN
  ABBREV_TAC `H1 = &n * nf_proj_height n be1 ga1` THEN
  ABBREV_TAC `H2 = &n * nf_proj_height n be2 ga2` THEN
  SUBGOAL_THEN `&2 * H1 <= a1 /\ &2 * H2 <= a2` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= (rho - &1) * log x1 /\ &0 <= (rho - &1) * log x2`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`(rho - &1) * log x1 + &2 * H1 <= a1`;
      `(rho - &1) * log x2 + &2 * H2 <= a2`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&n - &1) * log(&2) <= SQ` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= log(&2)` MP_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`&2 * (h + log rho) <= SQ`; `&n * log(&2) / &2 <= h`;
      `&0 < log rho`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&20 <= SQ /\ &0 <= CX` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`&2 * (h + log rho) <= SQ`; `&10 <= h`; `&0 < log rho`;
      `&((R1 + R2) - 1) * a1 + &((S1 + S2) - 1) * a2 <= CX / &2`;
      `a1 <= &((R1 + R2) - 1) * a1`; `a2 <= &((S1 + S2) - 1) * a2`;
      `&1 <= a1`; `&1 <= a2`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* case 1: a multiplicative collision in the grid R1 x S1 *)
  ASM_CASES_TAC
   `?m1 m2 m1' m2'. m1 < R1 /\ m2 < S1 /\ m1' < R1 /\ m2' < S1 /\
                    (x1:real) pow m1 * (x2:real) pow m2 =
                    x1 pow m1' * x2 pow m2' /\
                    ~(m1 = m1' /\ m2 = m2')` THENL
   [POP_ASSUM(X_CHOOSE_THEN `m1:num` (X_CHOOSE_THEN `m2:num`
      (X_CHOOSE_THEN `m1':num` (X_CHOOSE_THEN `m2':num`
        STRIP_ASSUME_TAC)))) THEN
    MP_TAC(SPECL [`log x1`; `log x2`; `R1:num`; `S1:num`; `m1:num`; `m2:num`;
                  `m1':num`; `m2':num`] LAURENT_ALG_COLL_UV) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      SUBGOAL_THEN `log((x1:real) pow m1 * (x2:real) pow m2) =
                    log(x1 pow m1' * x2 pow m2')` MP_TAC THENL
       [AP_TERM_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < x1 /\ &0 < x2` STRIP_ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`&1 < x1`; `&1 < x2`] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SIMP_TAC[LOG_POW_MUL; ASSUME `&0 < x1`; ASSUME `&0 < x2`];
      DISCH_THEN(X_CHOOSE_THEN `u:num` (X_CHOOSE_THEN `v:num`
        STRIP_ASSUME_TAC))] THEN
    MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`;
                  `be1:num->complex`; `ga1:num->complex`; `be2:num->complex`;
                  `ga2:num->complex`; `x1:real`; `x2:real`; `b1:num`; `b2:num`;
                  `u:num`; `v:num`] LAURENT_ALG_MCOLL) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `&n * nf_proj_height n be1 ga1 = H1`] THEN
    MATCH_MP_TAC(REAL_ARITH `c <= t ==> --c <= l ==> --t <= l`) THEN
    SUBGOAL_THEN `log(&v) <= &v - &1` ASSUME_TAC THENL
     [MATCH_MP_TAC LOG_LE_SUB_1 THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      UNDISCH_TAC `1 <= v` THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&v + &1 <= &((S1 + S2) - 1)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
      MAP_EVERY UNDISCH_TAC [`v < S1`; `1 <= S2`] THEN ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`(&n - &1) * log(&2) <= SQ`; `&2 * H1 <= a1`; `log(&v) <= &v - &1`;
      `&v + &1 <= &((S1 + S2) - 1)`;
      `&((S1 + S2) - 1) <= &((S1 + S2) - 1) * a2`;
      `a1 <= &((R1 + R2) - 1) * a1`;
      `&((R1 + R2) - 1) * a1 + &((S1 + S2) - 1) * a2 <= CX / &2`;
      `&0 <= log Y`; `&0 <= CX`; `&1 <= a1`] THEN
    REAL_ARITH_TAC;
    POP_ASSUM(LABEL_TAC "nm")] THEN
  (* case 2: an additive collision in the grid R2 x S2 *)
  ASM_CASES_TAC
   `?m1 m2 m1' m2'. m1 < R2 /\ m2 < S2 /\ m1' < R2 /\ m2' < S2 /\
                    m1 * b2 + m2 * b1 = m1' * b2 + m2' * b1 /\
                    ~(m1 = m1' /\ m2 = m2')` THENL
   [POP_ASSUM(X_CHOOSE_THEN `m1:num` (X_CHOOSE_THEN `m2:num`
      (X_CHOOSE_THEN `m1':num` (X_CHOOSE_THEN `m2':num`
        STRIP_ASSUME_TAC)))) THEN
    MP_TAC(SPECL [`&b2:real`; `&b1:real`; `R2:num`; `S2:num`; `m1:num`;
                  `m2:num`; `m1':num`; `m2':num`] LAURENT_ALG_COLL_UV) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
       [REWRITE_TAC[REAL_OF_NUM_LT] THEN UNDISCH_TAC `1 <= b2` THEN ARITH_TAC;
        REWRITE_TAC[REAL_OF_NUM_LT] THEN UNDISCH_TAC `1 <= b1` THEN ARITH_TAC;
        REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
        FIRST_ASSUM ACCEPT_TAC];
      DISCH_THEN(X_CHOOSE_THEN `u:num` (X_CHOOSE_THEN `v:num`
        STRIP_ASSUME_TAC))] THEN
    MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`;
                  `be1:num->complex`; `ga1:num->complex`; `be2:num->complex`;
                  `ga2:num->complex`; `x1:real`; `x2:real`; `b1:num`; `b2:num`;
                  `u:num`; `v:num`] LAURENT_ALG_ACOLL) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[ASSUME `&n * nf_proj_height n be1 ga1 = H1`;
                ASSUME `&n * nf_proj_height n be2 ga2 = H2`] THEN
    MATCH_MP_TAC(REAL_ARITH `c <= t ==> --c <= l ==> --t <= l`) THEN
    SUBGOAL_THEN `log(&v) <= &v - &1` ASSUME_TAC THENL
     [MATCH_MP_TAC LOG_LE_SUB_1 THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      UNDISCH_TAC `1 <= v` THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&v + &1 <= &((S1 + S2) - 1) /\ &u <= &((R1 + R2) - 1) /\
                  &v <= &((S1 + S2) - 1)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
      MAP_EVERY UNDISCH_TAC [`v < S2`; `u < R2`; `1 <= S1`; `1 <= R1`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= H1 /\ &0 <= H2` STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`log x1 <= H1`; `log x2 <= H2`;
                             `&0 < log x1`; `&0 < log x2`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&u * H1 <= &((R1 + R2) - 1) * H1 /\ &v * H2 <= &((S1 + S2) - 1) * H2 /\
      &((R1 + R2) - 1) * (&2 * H1) <= &((R1 + R2) - 1) * a1 /\
      &((S1 + S2) - 1) * (&2 * H2) <= &((S1 + S2) - 1) * a2`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`(&n - &1) * log(&2) <= SQ`; `log(&v) <= &v - &1`;
      `&v + &1 <= &((S1 + S2) - 1)`;
      `&((S1 + S2) - 1) <= &((S1 + S2) - 1) * a2`;
      `&u * H1 <= &((R1 + R2) - 1) * H1`; `&v * H2 <= &((S1 + S2) - 1) * H2`;
      `&((R1 + R2) - 1) * (&2 * H1) <= &((R1 + R2) - 1) * a1`;
      `&((S1 + S2) - 1) * (&2 * H2) <= &((S1 + S2) - 1) * a2`;
      `&((R1 + R2) - 1) * a1 + &((S1 + S2) - 1) * a2 <= CX / &2`;
      `&0 <= log Y`; `&0 <= CX`; `&1 <= a1`;
      `a1 <= &((R1 + R2) - 1) * a1`] THEN
    REAL_ARITH_TAC;
    POP_ASSUM(LABEL_TAC "na")] THEN
  (* case 3: both grid maps are injective: the main argument *)
  SUBGOAL_THEN
   `CARD {(x1:real) pow m1 * (x2:real) pow m2 | m1,m2 | m1 < R1 /\ m2 < S1} =
    R1 * S1`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\m1 m2. (x1:real) pow m1 * (x2:real) pow m2`;
                   `R1:num`; `S1:num`] CARD_IMAGE_INJ_GRID) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY X_GEN_TAC [`m1:num`; `m2:num`; `m1':num`; `m2':num`] THEN
    STRIP_TAC THEN
    USE_THEN "nm" (MP_TAC o SPECL [`m1:num`; `m2:num`; `m1':num`; `m2':num`] o
      REWRITE_RULE[NOT_EXISTS_THM]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD {m1 * b2 + m2 * b1 | m1,m2 | m1 < R2 /\ m2 < S2} = R2 * S2`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\m1 m2. m1 * b2 + m2 * b1`; `R2:num`; `S2:num`]
      CARD_IMAGE_INJ_GRID) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY X_GEN_TAC [`m1:num`; `m2:num`; `m1':num`; `m2':num`] THEN
    STRIP_TAC THEN
    USE_THEN "na" (MP_TAC o SPECL [`m1:num`; `m2:num`; `m1':num`; `m2':num`] o
      REWRITE_RULE[NOT_EXISTS_THM]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`x1:real`; `x2:real`; `b1:num`; `b2:num`; `K:num`; `L:num`;
                `R1:num`; `S1:num`; `R2:num`; `S2:num`]
    BINOM_ZERO_MINOR_REAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`&1 < x1`; `&1 < x2`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rr:num->num` (X_CHOOSE_THEN `ss:num->num`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`;
                `be1:num->complex`; `ga1:num->complex`; `be2:num->complex`;
                `ga2:num->complex`; `x1:real`; `x2:real`; `b1:num`; `b2:num`;
                `K:num`; `L:num`; `(R1 + R2) - 1`; `(S1 + S2) - 1`; `K * L`;
                `rr:num->num`; `ss:num->num`; `rho:real`; `a1:real`;
                `a2:real`] LAURENT_CORE_NF) THEN
  REWRITE_TAC[ASSUME `&n * nf_proj_height n be1 ga1 = H1`;
              ASSUME `&n * nf_proj_height n be2 ga2 = H2`] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(MAP_EVERY UNDISCH_TAC [`&1 < x1`; `&1 < x2`] THEN REAL_ARITH_TAC) THEN
    MAP_EVERY UNDISCH_TAC [`2 <= K`; `2 <= L`; `2 <= (S1 + S2) - 1`] THEN
    ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(SPECL [`rho:real`; `K * L`; `&(L * ((S1 + S2) - 1))`; `&b2:real`;
                `abs(&b2 * log x2 - &b1 * log x1)`; `CX + SQ:real`; `Y:real`]
    LAURENT_ALG_LAMBDA_PRIME) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [UNDISCH_TAC `&4 <= &(L * ((S1 + S2) - 1))` THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_LE] THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[GSYM REAL_ABS_NZ; REAL_SUB_0] THEN FIRST_ASSUM ACCEPT_TAC;
      MAP_EVERY UNDISCH_TAC [`&20 <= SQ`; `&0 <= CX`] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `&2 <= Y` THEN REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The final theorems: Theorem-2 form (domains A and B, both orders of       *)
(* b1 log x1 and b2 log x2 by symmetry) and Corollary 2.                     *)
(* ------------------------------------------------------------------------- *)

let LAURENT_ALG_BOUND_SYM = prove
 (`!rho h a1 a2. laurent_bound rho h a1 a2 = laurent_bound rho h a2 a1`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `laurent_C rho h a1 a2 = laurent_C rho h a2 a1` ASSUME_TAC THENL
   [REWRITE_TAC[laurent_C] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[REAL_MUL_AC; REAL_ADD_AC];
    ALL_TAC] THEN
  REWRITE_TAC[laurent_bound; laurent_Cp] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let LAURENT_NF_REAL_PARAM = prove
 (`!n c r be1 ga1 be2 ga2 x1 x2 b1 b2 rho h a1 a2.
     nf_data n c r /\
     nf_alg_int n r be1 /\ nf_alg_int n r ga1 /\
     nf_alg_int n r be2 /\ nf_alg_int n r ga2 /\
     ~(ga1 1 = Cx(&0)) /\ ~(ga2 1 = Cx(&0)) /\
     be1 1 = Cx x1 * ga1 1 /\ be2 1 = Cx x2 * ga2 1 /\ &1 < x1 /\ &1 < x2 /\
     1 <= b1 /\ 1 <= b2 /\ &4 <= rho /\ rho <= &8 /\ &10 <= h /\
     &1 <= a1 /\
     (rho - &1) * log x1 + &2 * &n * nf_proj_height n be1 ga1 <= a1 /\
     &1 <= a2 /\
     (rho - &1) * log x2 + &2 * &n * nf_proj_height n be2 ga2 <= a2 /\
     log rho pow 2 <= a1 * a2 /\
     &n * (log(&b1 / a2 + &b2 / a1) + log(log rho) + &5 / &2) <= h /\
     &n * log(&2) / &2 <= h /\
     ~(&b2 * log x2 = &b1 * log x1)
     ==> --(laurent_bound rho h a1 a2) <=
         log(abs(&b2 * log x2 - &b1 * log x1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NF_DATA) THEN
  SUBGOAL_THEN `&1 < rho` ASSUME_TAC THENL
   [UNDISCH_TAC `&4 <= rho` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISJ_CASES_TAC(REAL_ARITH
   `&b1 * log x1 <= &b2 * log x2 \/ &b2 * log x2 <= &b1 * log x1`) THENL
   [MP_TAC(SPECL [`n:num`; `rho:real`; `h:real`; `a1:real`; `a2:real`;
                  `b1:num`; `b2:num`] LAURENT_PARAMETERS) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`K:num`; `L:num`; `R1:num`; `S1:num`; `R2:num`;
                         `S2:num`] THEN
    STRIP_TAC THEN MATCH_MP_TAC LAURENT_ALG_GEN THEN
    MAP_EVERY EXISTS_TAC
     [`n:num`; `c:num->real`; `r:num->complex`; `be1:num->complex`;
      `ga1:num->complex`; `be2:num->complex`; `ga2:num->complex`;
      `K:num`; `L:num`; `R1:num`; `S1:num`; `R2:num`; `S2:num`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[LAURENT_ALG_BOUND_SYM] THEN
  ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
  MP_TAC(SPECL [`n:num`; `rho:real`; `h:real`; `a2:real`; `a1:real`;
                `b2:num`; `b1:num`] LAURENT_PARAMETERS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
      ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
      UNDISCH_TAC
       `&n * (log(&b1 / a2 + &b2 / a1) + log(log rho) + &5 / &2) <= h` THEN
      REWRITE_TAC[REAL_ADD_AC]];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`K:num`; `L:num`; `R1:num`; `S1:num`; `R2:num`;
                       `S2:num`] THEN
  STRIP_TAC THEN MATCH_MP_TAC LAURENT_ALG_GEN THEN
  MAP_EVERY EXISTS_TAC
   [`n:num`; `c:num->real`; `r:num->complex`; `be2:num->complex`;
    `ga2:num->complex`; `be1:num->complex`; `ga1:num->complex`;
    `K:num`; `L:num`; `R1:num`; `S1:num`; `R2:num`; `S2:num`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  UNDISCH_TAC `~(&b2 * log x2 = &b1 * log x1)` THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The Theorem-2 statement without the hypothesis n log 2 / 2 <= h holds     *)
(* for fields of degree n <= 20 (then n log 2 / 2 <= 10 <= h), e.g. Q        *)
(* (n = 1) and the class number one field Q(sqrt 21, sqrt 33) (n = 4).       *)
(* ------------------------------------------------------------------------- *)

let LAURENT_ALG_REAL_PARAM_DEG20 = prove
 (`!n c r be1 ga1 be2 ga2 x1 x2 b1 b2 rho h a1 a2.
     nf_data n c r /\
     nf_alg_int n r be1 /\ nf_alg_int n r ga1 /\
     nf_alg_int n r be2 /\ nf_alg_int n r ga2 /\
     ~(ga1 1 = Cx(&0)) /\ ~(ga2 1 = Cx(&0)) /\
     be1 1 = Cx x1 * ga1 1 /\ be2 1 = Cx x2 * ga2 1 /\ &1 < x1 /\ &1 < x2 /\
     1 <= b1 /\ 1 <= b2 /\ &4 <= rho /\ rho <= &8 /\ &10 <= h /\
     &1 <= a1 /\
     (rho - &1) * log x1 + &2 * &n * nf_proj_height n be1 ga1 <= a1 /\
     &1 <= a2 /\
     (rho - &1) * log x2 + &2 * &n * nf_proj_height n be2 ga2 <= a2 /\
     log rho pow 2 <= a1 * a2 /\
     &n * (log(&b1 / a2 + &b2 / a1) + log(log rho) + &5 / &2) <= h /\
     ~(&b2 * log x2 = &b1 * log x1) /\ n <= 20
     ==> --(laurent_bound rho h a1 a2) <=
         log(abs(&b2 * log x2 - &b1 * log x1))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LAURENT_NF_REAL_PARAM THEN
  MAP_EVERY EXISTS_TAC
   [`n:num`; `c:num->real`; `r:num->complex`; `be1:num->complex`;
    `ga1:num->complex`; `be2:num->complex`; `ga2:num->complex`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  SUBGOAL_THEN `&n * log(&2) <= &20 * &1` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_POS] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      MATCH_MP_TAC LOG_POS THEN REAL_ARITH_TAC;
      MP_TAC(SPEC `&2` LOG_LE_SUB_1) THEN REAL_ARITH_TAC];
    UNDISCH_TAC `&10 <= h` THEN REAL_ARITH_TAC]);;

let LAURENT_ALG_REAL_LARGE = prove
 (`!n c r be1 ga1 be2 ga2 x1 x2 b1 b2 rho h a1 a2.
     nf_data n c r /\
     nf_alg_int n r be1 /\ nf_alg_int n r ga1 /\
     nf_alg_int n r be2 /\ nf_alg_int n r ga2 /\
     ~(ga1 1 = Cx(&0)) /\ ~(ga2 1 = Cx(&0)) /\
     be1 1 = Cx x1 * ga1 1 /\ be2 1 = Cx x2 * ga2 1 /\ &1 < x1 /\ &1 < x2 /\
     1 <= b1 /\ 1 <= b2 /\ &4 <= rho /\ rho <= &8 /\ &10 <= h /\
     rho + &1 <= a1 /\
     (rho - &1) * log x1 + &2 * &n * nf_proj_height n be1 ga1 <= a1 /\
     rho + &1 <= a2 /\
     (rho - &1) * log x2 + &2 * &n * nf_proj_height n be2 ga2 <= a2 /\
     &n * (log(&b1 / a2 + &b2 / a1) + log(log rho) + &3 / &2) <= h /\
     &n * log(&2) / &2 <= h /\
     ~(&b2 * log x2 = &b1 * log x1)
     ==> --(laurent_bound rho h a1 a2) <=
         log(abs(&b2 * log x2 - &b1 * log x1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NF_DATA) THEN
  SUBGOAL_THEN `&1 < rho /\ &1 <= a1 /\ &1 <= a2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&4 <= rho`; `rho + &1 <= a1`; `rho + &1 <= a2`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISJ_CASES_TAC(REAL_ARITH
   `&b1 * log x1 <= &b2 * log x2 \/ &b2 * log x2 <= &b1 * log x1`) THENL
   [MP_TAC(SPECL [`n:num`; `rho:real`; `h:real`; `a1:real`; `a2:real`;
                  `b1:num`; `b2:num`] LAURENT_PARAMETERS_LARGE) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`K:num`; `L:num`; `R1:num`; `S1:num`; `R2:num`;
                         `S2:num`] THEN
    STRIP_TAC THEN MATCH_MP_TAC LAURENT_ALG_GEN THEN
    MAP_EVERY EXISTS_TAC
     [`n:num`; `c:num->real`; `r:num->complex`; `be1:num->complex`;
      `ga1:num->complex`; `be2:num->complex`; `ga2:num->complex`;
      `K:num`; `L:num`; `R1:num`; `S1:num`; `R2:num`; `S2:num`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[LAURENT_ALG_BOUND_SYM] THEN
  ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
  MP_TAC(SPECL [`n:num`; `rho:real`; `h:real`; `a2:real`; `a1:real`;
                `b2:num`; `b1:num`] LAURENT_PARAMETERS_LARGE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    UNDISCH_TAC
     `&n * (log(&b1 / a2 + &b2 / a1) + log(log rho) + &3 / &2) <= h` THEN
    REWRITE_TAC[REAL_ADD_AC];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`K:num`; `L:num`; `R1:num`; `S1:num`; `R2:num`;
                       `S2:num`] THEN
  STRIP_TAC THEN MATCH_MP_TAC LAURENT_ALG_GEN THEN
  MAP_EVERY EXISTS_TAC
   [`n:num`; `c:num->real`; `r:num->complex`; `be2:num->complex`;
    `ga2:num->complex`; `be1:num->complex`; `ga1:num->complex`;
    `K:num`; `L:num`; `R1:num`; `S1:num`; `R2:num`; `S2:num`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  UNDISCH_TAC `~(&b2 * log x2 = &b1 * log x1)` THEN REAL_ARITH_TAC);;

let LAURENT_ALG_LOG_C0 = prove
 (`log(log(&5)) + &3 / &2 - log(&6) <= &38 / &100`,
  MP_TAC LAURENT_CORNER_LOG_5 THEN STRIP_TAC THEN
  SUBGOAL_THEN `log(log(&5)) <= &161 / &100 - &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&161 / &100)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_LE_SUB_1 THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&6) = log(&5) + log(&6 / &5)` SUBST1_TAC THENL
   [SUBGOAL_THEN `&6 = &5 * &6 / &5` (fun th -> GEN_REWRITE_TAC
      (LAND_CONV o RAND_CONV) [th])
    THENL [REAL_ARITH_TAC; MATCH_MP_TAC LOG_MUL THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `&6 / &5` LAURENT_ALG_LOG_GE) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MAP_EVERY UNDISCH_TAC [`log(log(&5)) <= &161 / &100 - &1`;
                         `&1609 / &1000 <= log(&5)`] THEN
  REAL_ARITH_TAC);;

let LAURENT_NF_REAL = prove
 (`!n c r be1 ga1 be2 ga2 x1 x2 b1 b2 A1 A2.
     nf_data n c r /\
     nf_alg_int n r be1 /\ nf_alg_int n r ga1 /\
     nf_alg_int n r be2 /\ nf_alg_int n r ga2 /\
     ~(ga1 1 = Cx(&0)) /\ ~(ga2 1 = Cx(&0)) /\
     be1 1 = Cx x1 * ga1 1 /\ be2 1 = Cx x2 * ga2 1 /\ &1 < x1 /\ &1 < x2 /\
     1 <= b1 /\ 1 <= b2 /\
     nf_proj_height n be1 ga1 <= A1 /\ log x1 <= &n * A1 /\ &1 <= &n * A1 /\
     nf_proj_height n be2 ga2 <= A2 /\ log x2 <= &n * A2 /\ &1 <= &n * A2 /\
     ~(&b2 * log x2 = &b1 * log x1)
     ==> exp(--(&32 * &n pow 4 *
                max (max (&10 / &n) (&1))
                  (log(&b1 / (&n * A2) + &b2 / (&n * A1)) + &38 / &100) pow 2 *
                A1 * A2))
         <= abs(&b2 * log x2 - &b1 * log x1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NF_DATA) THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN UNDISCH_TAC `1 <= n` THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `M = max (max (&10 / &n) (&1))
            (log(&b1 / (&n * A2) + &b2 / (&n * A1)) + &38 / &100)` THEN
  SUBGOAL_THEN
   `&10 / &n <= M /\ &1 <= M /\
    log(&b1 / (&n * A2) + &b2 / (&n * A1)) + &38 / &100 <= M`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&10 <= &n * M` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&n * &10 / &n` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_LE_REFL];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &n * A1 /\ &0 < &n * A2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&1 <= &n * A1`; `&1 <= &n * A2`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &b1 / (&n * A2) + &b2 / (&n * A1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
    MAP_EVERY UNDISCH_TAC [`1 <= b1`; `1 <= b2`] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`;
                `be1:num->complex`; `ga1:num->complex`; `be2:num->complex`;
                `ga2:num->complex`; `x1:real`; `x2:real`; `b1:num`; `b2:num`;
                `&5`; `&n * M`; `&6 * &n * A1`; `&6 * &n * A2`]
    LAURENT_ALG_REAL_LARGE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      UNDISCH_TAC `&1 <= &n * A1` THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `&n * nf_proj_height n be1 ga1 <= &n * A1` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ALL_TAC] THEN
      UNDISCH_TAC `log x1 <= &n * A1` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `&1 <= &n * A2` THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `&n * nf_proj_height n be2 ga2 <= &n * A2` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ALL_TAC] THEN
      UNDISCH_TAC `log x2 <= &n * A2` THEN REAL_ARITH_TAC;
      SUBGOAL_THEN
       `&b1 / (&6 * &n * A2) + &b2 / (&6 * &n * A1) =
        (&b1 / (&n * A2) + &b2 / (&n * A1)) / &6`
      SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`&0 < &n * A1`; `&0 < &n * A2`] THEN
        CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      ASM_SIMP_TAC[LOG_DIV; REAL_ARITH `&0 < &6`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MP_TAC LAURENT_ALG_LOG_C0 THEN
      UNDISCH_TAC
       `log(&b1 / (&n * A2) + &b2 / (&n * A1)) + &38 / &100 <= M` THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MP_TAC(SPEC `&2` LOG_LE_SUB_1) THEN
      UNDISCH_TAC `&1 <= M` THEN REAL_ARITH_TAC];
    DISCH_TAC] THEN
  MP_TAC(SPECL [`&n * M`; `&6 * &n * A1`; `&6 * &n * A2`]
    LAURENT_BOUND_CORNER_5_10) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`&1 <= &n * A1`; `&1 <= &n * A2`] THEN
    REAL_ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < abs(&b2 * log x2 - &b1 * log x1)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_ABS_NZ; REAL_SUB_0] THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(log(abs(&b2 * log x2 - &b1 * log x1)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    SUBGOAL_THEN
     `&32 * &n pow 4 * M pow 2 * A1 * A2 =
      &32 / &36 * (&n * M) pow 2 * (&6 * &n * A1) * (&6 * &n * A2)`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`--(laurent_bound (&5) (&n * M) (&6 * &n * A1) (&6 * &n * A2)) <=
       log(abs(&b2 * log x2 - &b1 * log x1))`;
      `laurent_bound (&5) (&n * M) (&6 * &n * A1) (&6 * &n * A2) <=
       &32 / &36 * (&n * M) pow 2 * (&6 * &n * A1) * (&6 * &n * A2)`] THEN
    REAL_ARITH_TAC;
    ASM_SIMP_TAC[EXP_LOG; REAL_LE_REFL]]);;
