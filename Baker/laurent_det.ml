(* ========================================================================= *)
(* Two logarithms, the Laurent bound: determinant tools.                     *)
(*                                                                           *)
(* Purpose: the complex and real forms of the triangular row change in       *)
(* blocks of rows indexed by (i - 1) MOD K, (i - 1) DIV K (the binomial rows *)
(* of the interpolation determinant are triangular combinations of power     *)
(* rows, as in M. Laurent, Linear forms in two logarithms and interpolation  *)
(* determinants, Acta Arith. 66 (1994), section 4; the general ring form     *)
(* RING_DET_TRIANGULAR_ROWS is in Library/ring_det.ml), integrality of a     *)
(* real determinant from integrality of every product along a permutation,   *)
(* and sums over the rows of one residue (i - 1) MOD K.                      *)
(*                                                                           *)
(* Main results: CDET_TRIANGULAR_ROWS, RDET_TRIANGULAR_ROWS,                 *)
(* RDET_INTEGER_PERMUTATIONS, SUM_NUMSEG_PRED_MOD.                           *)
(*                                                                           *)
(* Uses: Library/ring_det.ml (RING_DET_TRIANGULAR_ROWS), Baker/twolog_det.ml *)
(* (REAL_RING_DET), Library/ringtheory.ml (REAL_RING_SUM,                    *)
(* REAL_RING_PRODUCT),                                                       *)
(* INTEGER_SIGN of Multivariate/determinants.ml.                             *)
(* ========================================================================= *)

needs "Baker/twolog_det.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The complex and real instances: row i = l K + k + 1 is the polynomial     *)
(* sum_(t <= k) c k t z^t in z = z j of degree k with leading coefficient    *)
(* c k k, times y l j.                                                       *)
(* ------------------------------------------------------------------------- *)

let CDET_TRIANGULAR_ROWS = prove
 (`!K L (c:num->num->complex) (z:num->complex) (y:num->num->complex).
     ring_det complex_ring (1..K * L)
          (\i j. vsum(0..(i - 1) MOD K) (\t. c ((i - 1) MOD K) t * z j pow t) *
                 y ((i - 1) DIV K) j) =
     cproduct(1..K * L) (\i. c ((i - 1) MOD K) ((i - 1) MOD K)) *
     ring_det complex_ring (1..K * L)
       (\i j. z j pow ((i - 1) MOD K) * y ((i - 1) DIV K) j)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`complex_ring`; `K:num`; `L:num`; `c:num->num->complex`;
                 `\t l j. (z:num->complex) j pow t * (y:num->num->complex) l j`]
    RING_DET_TRIANGULAR_ROWS) THEN
  REWRITE_TAC[COMPLEX_RING_CLAUSES; IN_UNIV] THEN
  SIMP_TAC[COMPLEX_RING_PRODUCT; COMPLEX_RING_SUM;
           FINITE_NUMSEG] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN ABS_TAC THEN ABS_TAC THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; FINITE_NUMSEG; COMPLEX_MUL_ASSOC]);;

let RDET_TRIANGULAR_ROWS = prove
 (`!K L (c:num->num->real) (z:num->real) (y:num->num->real).
     ring_det real_ring (1..K * L)
          (\i j. sum(0..(i - 1) MOD K) (\t. c ((i - 1) MOD K) t * z j pow t) *
                 y ((i - 1) DIV K) j) =
     product(1..K * L) (\i. c ((i - 1) MOD K) ((i - 1) MOD K)) *
     ring_det real_ring (1..K * L)
       (\i j. z j pow ((i - 1) MOD K) * y ((i - 1) DIV K) j)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`real_ring`; `K:num`; `L:num`; `c:num->num->real`;
                 `\t l j. (z:num->real) j pow t * (y:num->num->real) l j`]
    RING_DET_TRIANGULAR_ROWS) THEN
  REWRITE_TAC[REAL_RING_CLAUSES; IN_UNIV; REAL_RING_SUM; REAL_RING_PRODUCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN ABS_TAC THEN ABS_TAC THEN
  REWRITE_TAC[GSYM SUM_RMUL; REAL_MUL_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Integrality of a real determinant from integrality of every product along *)
(* a permutation.                                                            *)
(* ------------------------------------------------------------------------- *)

let RDET_INTEGER_PERMUTATIONS = prove
 (`!n (f:num->num->real) c.
     (!p. p permutes 1..n ==> integer(c * product(1..n) (\i. f i (p i))))
     ==> integer(c * ring_det real_ring (1..n) f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_RING_DET; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC INTEGER_SUM THEN X_GEN_TAC `p:num->num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `c * s * x:real = s * c * x`] THEN
  MATCH_MP_TAC INTEGER_MUL THEN REWRITE_TAC[INTEGER_SIGN] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Sums over the rows of one residue (i - 1) MOD K: L copies of the sum over *)
(* 0..K - 1 (the diagonal of the triangular row change, e.g. the factorials  *)
(* of the binomial rows).                                                    *)
(* ------------------------------------------------------------------------- *)

let SUM_NUMSEG_PRED_MOD = prove
 (`!K L (f:num->real).
        1 <= K
        ==> sum(1..K * L) (\i. f((i - 1) MOD K)) = &L * sum(0..K - 1) f`,
  REPEAT STRIP_TAC THEN SPEC_TAC(`L:num`,`L:num`) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; SUM_CLAUSES_NUMSEG; ARITH_EQ; REAL_MUL_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `K * SUC L = K * L + K` SUBST1_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[SUM_ADD_SPLIT; ARITH_RULE `1 <= n + 1`] THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  SUBGOAL_THEN
   `sum(K * L + 1..K * L + K) (\i. (f:num->real)((i - 1) MOD K)) =
    sum(0..K - 1) f`
  SUBST1_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `K * L + 1..K * L + K = (0 + K * L + 1)..((K - 1) + K * L + 1)`
  SUBST1_TAC THENL
   [BINOP_TAC THEN ASM_ARITH_TAC; REWRITE_TAC[SUM_OFFSET]] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `(i + K * L + 1) - 1 = K * L + i`; MOD_MULT_ADD] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;
