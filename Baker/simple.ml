(* ========================================================================= *)
(* A lower bound for the nonzero roots of an integer polynomial.             *)
(*                                                                           *)
(* Purpose: if z <> 0 is a root of the polynomial with integer coefficients  *)
(* a 0, ..., a d, all of absolute value <= B, and a d <> 0, then             *)
(* 1 / (2 B) <= |z|. Proof: let k be the least index with a k <> 0 (so       *)
(* k < d). Dividing by z^k gives                                             *)
(*     a k = - sum(i = k + 1..d) a i z^(i - k),                              *)
(* and if |z| < 1 / (2 B) <= 1 / 2 the geometric bound SUM_GP_LE_HALF makes  *)
(* the right side smaller than 2 B |z| < 1 in absolute value, whereas        *)
(* |a k| >= 1 for the nonzero integer a k. (The proof does not divide by     *)
(* z^k: it compares |a k| |z|^k with 2 B |z| |z|^k.) For B >= 2 this gives   *)
(* the bound 1 / B^2.                                                        *)
(*                                                                           *)
(* Main results: ALGEBRAIC_ROOT_LOWER_BOUND, ALGEBRAIC_ROOT_LOWER_BOUND_POW  *)
(*   (the bound 1 / B^2 for B >= 2), SUM_GP_LE_HALF.                         *)
(*                                                                           *)
(* Uses: Multivariate/complex_algebra.ml (COMPLEX_NORM_MUL,                  *)
(* COMPLEX_NORM_POW) and Multivariate/misc.ml (SUM_GP_MULTIPLIED).           *)
(* ========================================================================= *)

needs "Multivariate/complex_algebra.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Geometric sums with ratio in [0,1/2] are at most twice their first term.  *)
(* ------------------------------------------------------------------------- *)

let SUM_GP_LE_HALF = prove
 (`!x m n. &0 <= x /\ x <= inv(&2)
           ==> sum(m..n) (\i. x pow i) <= &2 * x pow m`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n < m` THENL
   [ASM_SIMP_TAC[SUM_TRIV_NUMSEG] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_POS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`x:real`; `m:num`; `n:num`] SUM_GP_MULTIPLIED) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sum(m..n) (\i. (x:real) pow i)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_SIMP_TAC[REAL_POW_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 - &2 * x) * sum(m..n) (\i. (x:real) pow i)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`x:real`; `SUC n`] REAL_POW_LE) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Nonzero roots of an integer polynomial with coefficients bounded by B.    *)
(* ------------------------------------------------------------------------- *)

let ALGEBRAIC_ROOT_LOWER_BOUND = prove
 (`!(a:num->real) d B (z:complex).
        (!i. integer(a i) /\ abs(a i) <= B) /\ ~(a d = &0) /\
        vsum(0..d) (\i. Cx(a i) * z pow i) = Cx(&0) /\ ~(z = Cx(&0))
        ==> inv(&2 * B) <= norm z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= (B:real)` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `abs((a:num->real) d)` THEN
    ASM_SIMP_TAC[REAL_ABS_INTEGER_LEMMA];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?k. ~((a:num->real) k = &0) /\ !j. j < k ==> a j = &0`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `\n. ~((a:num->real) n = &0)` num_WOP) THEN
    REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `k <= d` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `vsum(k..d) (\i. Cx((a:num->real) i) * (z:complex) pow i) = Cx(&0)`
  ASSUME_TAC THENL
   [UNDISCH_TAC
     `vsum(0..d) (\i. Cx((a:num->real) i) * (z:complex) pow i) = Cx(&0)` THEN
    MATCH_MP_TAC(MESON[] `(x:complex) = y ==> x = c ==> y = c`) THEN
    MATCH_MP_TAC VSUM_SUPERSET THEN
    REWRITE_TAC[SUBSET; IN_NUMSEG; COMPLEX_VEC_0] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(a:num->real) j = &0` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[COMPLEX_MUL_LZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN `k < d` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LT_LE] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC
     `vsum(d..d) (\i. Cx((a:num->real) i) * (z:complex) pow i) = Cx(&0)` THEN
    ASM_REWRITE_TAC[VSUM_SING_NUMSEG; COMPLEX_ENTIRE; COMPLEX_POW_EQ_0;
                    CX_INJ];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(z:complex) <= inv(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN
    TRANS_TAC REAL_LTE_TRANS `inv(&2 * (B:real))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(z:complex) pow k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[COMPLEX_NORM_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Cx((a:num->real) k) * (z:complex) pow k =
    --vsum(k + 1..d) (\i. Cx(a i) * z pow i)`
  MP_TAC THENL
   [MP_TAC(ISPECL [`\i. Cx((a:num->real) i) * (z:complex) pow i`;
                   `k:num`; `d:num`] VSUM_CLAUSES_LEFT) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `norm:complex->real`) THEN
  REWRITE_TAC[NORM_NEG; COMPLEX_NORM_MUL; COMPLEX_NORM_CX;
              COMPLEX_NORM_POW] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `abs((a:num->real) k) * norm(z:complex) pow k <=
    (&2 * B * norm z) * norm z pow k`
  MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    TRANS_TAC REAL_LE_TRANS
     `sum(k + 1..d) (\i. B * norm(z:complex) pow i)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; COMPLEX_NORM_POW] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_POW_LE; NORM_POS_LE];
      ALL_TAC] THEN
    REWRITE_TAC[SUM_LMUL] THEN
    SUBGOAL_THEN
     `(&2 * B * norm z) * norm(z:complex) pow k =
      B * &2 * norm z pow (k + 1)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM ADD1; real_pow] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SUM_GP_LE_HALF THEN ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RMUL_EQ] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&2 * B * norm(z:complex) < &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `(&2 * (B:real)) * inv(&2 * B) = &1` MP_TAC THENL
     [MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`&2 * (B:real)`; `norm(z:complex)`; `inv(&2 * (B:real))`]
      REAL_LT_LMUL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `(a:num->real) k` REAL_ABS_INTEGER_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* For B >= 2 we have 2 B <= B^2, giving the bound 1 / B^2.                  *)
(* ------------------------------------------------------------------------- *)

let ALGEBRAIC_ROOT_LOWER_BOUND_POW = prove
 (`!(a:num->real) d B (z:complex).
        &2 <= B /\ (!i. integer(a i) /\ abs(a i) <= B) /\ ~(a d = &0) /\
        vsum(0..d) (\i. Cx(a i) * z pow i) = Cx(&0) /\ ~(z = Cx(&0))
        ==> inv(B pow 2) <= norm z`,
  REPEAT STRIP_TAC THEN TRANS_TAC REAL_LE_TRANS `inv(&2 * (B:real))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[REAL_POW_2] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC ALGEBRAIC_ROOT_LOWER_BOUND THEN
    MAP_EVERY EXISTS_TAC [`a:num->real`; `d:num`] THEN ASM_REWRITE_TAC[]]);;
