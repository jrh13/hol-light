(* ========================================================================= *)
(* The type "real^2" regarded as the complex numbers.                        *)
(*                                                                           *)
(* The algebra (the type, Re, Im, Cx, ii, the field operations, norms,       *)
(* conjugation, square roots, sums, products, roots of polynomials) is in    *)
(* Multivariate/complex_algebra.ml; this file adds the results that need     *)
(* topology.                                                                 *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(*              (c) Copyright, Valentina Bruno 2010                          *)
(* ========================================================================= *)

needs "Multivariate/convex.ml";;
needs "Multivariate/complex_algebra.ml";;

prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Conjugation and multiplication as orthogonal transformations.             *)
(* ------------------------------------------------------------------------- *)

let ORTHOGONAL_TRANSFORMATION_CNJ = prove
 (`orthogonal_transformation cnj`,
  REWRITE_TAC[orthogonal_transformation; LINEAR_CNJ; DOT_CNJ]);;

let ORTHOGONAL_TRANSFORMATION_COMPLEX_MUL = prove
 (`!c. orthogonal_transformation(\z. c * z) <=> norm c = &1`,
  REWRITE_TAC[ORTHOGONAL_TRANSFORMATION; LINEAR_COMPLEX_MUL] THEN
  GEN_TAC THEN REWRITE_TAC[COMPLEX_NORM_MUL] THEN
  REWRITE_TAC[REAL_RING `c * v:real = v <=> c = &1 \/ v = &0`] THEN
  ASM_CASES_TAC `norm(c:complex) = &1` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `Cx(&1)`) THEN REWRITE_TAC[COMPLEX_NORM_CX] THEN
  REAL_ARITH_TAC);;

let COMPLEX_ORTHOGONAL_ROTATION = prove
 (`!f:complex->complex.
        orthogonal_transformation f /\ det(matrix f) = &1 <=>
        ?c. norm c = &1 /\ f = \z. c * z`,
  GEN_TAC THEN TRANS_TAC EQ_TRANS
   `(!z. norm(f z) = norm z) /\ (?c. f = \z:complex. c * z)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[COMPLEX_LINEAR] THEN
    ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> (q /\ p) /\ r`] THEN
    REWRITE_TAC[GSYM ORTHOGONAL_TRANSFORMATION] THEN
    REWRITE_TAC[ORTHOGONAL_TRANSFORMATION_MATRIX] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN AP_TERM_TAC THEN
    REWRITE_TAC[ORTHOGONAL_MATRIX_2; DET_2] THEN CONV_TAC REAL_RING;
    REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    X_GEN_TAC `c:complex` THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `f:complex->complex = \z. c * z` THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_MUL] THEN
    REWRITE_TAC[REAL_RING `c * v:real = v <=> c = &1 \/ v = &0`] THEN
    ASM_CASES_TAC `norm(c:complex) = &1` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `Cx(&1)`) THEN REWRITE_TAC[COMPLEX_NORM_CX] THEN
    REAL_ARITH_TAC]);;

let COMPLEX_ORTHOGONAL_ROTOINVERSION = prove
 (`!f:complex->complex.
        orthogonal_transformation f /\ det(matrix f) = -- &1 <=>
        ?c. norm c = &1 /\ f = \z. c * cnj z`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `!c. (f = \z. c * cnj z) = (f o cnj = \z. c * z)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN MESON_TAC[CNJ_CNJ; CNJ_MUL];
    REWRITE_TAC[GSYM COMPLEX_ORTHOGONAL_ROTATION]] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN `(f:complex->complex) = (f o cnj) o cnj` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; CNJ_CNJ];
      POP_ASSUM MP_TAC THEN
      SPEC_TAC(`(f:complex->complex) o cnj`,`f:complex->complex`) THEN
      REPEAT STRIP_TAC]] THEN
  ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_COMPOSE; MATRIX_COMPOSE; DET_MUL;
    ORTHOGONAL_TRANSFORMATION_CNJ; ORTHOGONAL_TRANSFORMATION_LINEAR] THEN
  SIMP_TAC[DET_2; MATRIX_COMPONENT; DIMINDEX_2; ARITH] THEN
  REWRITE_TAC[COMPLEX_BASIS; CNJ_II; CNJ_CX] THEN
  REWRITE_TAC[GSYM IM_DEF; GSYM RE_DEF; IM; RE; CX_DEF; ii; complex_neg] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let COMPLEX_ORTHOGONAL_TRANSFORMATION = prove
 (`!f:complex->complex.
        orthogonal_transformation f <=>
        ?c. norm c = &1 /\ ((f = \z. c * z) \/ (f = \z. c * cnj z))`,
  GEN_TAC THEN
  REWRITE_TAC[LEFT_OR_DISTRIB; EXISTS_OR_THM] THEN
  REWRITE_TAC[GSYM COMPLEX_ORTHOGONAL_ROTATION;
              GSYM COMPLEX_ORTHOGONAL_ROTOINVERSION] THEN
  MESON_TAC[DET_ORTHOGONAL_MATRIX; ORTHOGONAL_TRANSFORMATION_MATRIX]);;

(* ------------------------------------------------------------------------- *)
(* Segments, convexity and the interior of the real numbers in C.            *)
(* ------------------------------------------------------------------------- *)

let REAL_SEGMENT = prove
 (`!a b x. x IN segment[a,b] /\ real a /\ real b ==> real x`,
  SIMP_TAC[segment; IN_ELIM_THM; real; COMPLEX_EQ; LEFT_AND_EXISTS_THM;
           LEFT_IMP_EXISTS_THM; IM_ADD; IM_CMUL] THEN
  REAL_ARITH_TAC);;

let IN_SEGMENT_CX = prove
 (`!a b x. Cx(x) IN segment[Cx(a),Cx(b)] <=>
                a <= x /\ x <= b \/ b <= x /\ x <= a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[segment; IN_ELIM_THM] THEN
  REWRITE_TAC[COMPLEX_CMUL; GSYM CX_ADD; CX_INJ; GSYM CX_MUL] THEN
  ASM_CASES_TAC `a:real = b` THENL
   [ASM_REWRITE_TAC[REAL_ARITH `(&1 - u) * b + u * b = b`] THEN
    ASM_CASES_TAC `x:real = b` THEN ASM_REWRITE_TAC[REAL_LE_ANTISYM] THEN
    EXISTS_TAC `&0` THEN REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real`
     (CONJUNCTS_THEN2 STRIP_ASSUME_TAC SUBST1_TAC)) THEN
    REWRITE_TAC[REAL_ARITH `a <= (&1 - u) * a + u * b <=> &0 <= u * (b - a)`;
      REAL_ARITH `b <= (&1 - u) * a + u * b <=> &0 <= (&1 - u) * (a - b)`;
      REAL_ARITH `(&1 - u) * a + u * b <= a <=> &0 <= u * (a - b)`;
      REAL_ARITH `(&1 - u) * a + u * b <= b <=> &0 <= (&1 - u) * (b - a)`] THEN
    DISJ_CASES_TAC(REAL_ARITH `a <= b \/ b <= a`) THENL
     [DISJ1_TAC; DISJ2_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `&0 < b - a` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC;
      EXISTS_TAC `(x - a:real) / (b - a)`];
    SUBGOAL_THEN `&0 < a - b` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC;
      EXISTS_TAC `(a - x:real) / (a - b)`]] THEN
  (CONJ_TAC THENL
    [ALL_TAC; UNDISCH_TAC `~(a:real = b)` THEN CONV_TAC REAL_FIELD]) THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ] THEN
  ASM_REAL_ARITH_TAC);;

let IN_SEGMENT_CX_GEN = prove
 (`!a b x.
        x IN segment[Cx a,Cx b] <=>
        Im(x) = &0 /\ (a <= Re x /\ Re x <= b \/ b <= Re x /\ Re x <= a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM real] THEN
  ASM_CASES_TAC `real x` THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o REWRITE_RULE[REAL]) THEN
    REWRITE_TAC[IN_SEGMENT_CX; REAL_CX; RE_CX] THEN REAL_ARITH_TAC;
    ASM_MESON_TAC[REAL_SEGMENT; REAL_CX]]);;

let RE_POS_SEGMENT = prove
 (`!a b x. x IN segment[a,b] /\ &0 < Re a /\ &0 < Re b ==> &0 < Re x`,
  SIMP_TAC[segment; IN_ELIM_THM; real; COMPLEX_EQ; LEFT_AND_EXISTS_THM;
           LEFT_IMP_EXISTS_THM; RE_ADD; RE_CMUL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH
    `&0 <= x /\ &0 <= y /\ ~(x = &0 /\ y = &0) ==> &0 < x + y`) THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_SUB_LE; REAL_LT_IMP_LE; REAL_ENTIRE] THEN
  ASM_REAL_ARITH_TAC);;

let CONVEX_REAL = prove
 (`convex real`,
  REWRITE_TAC[convex; IN; COMPLEX_CMUL] THEN
  SIMP_TAC[REAL_ADD; REAL_MUL; REAL_CX]);;

let INTERIOR_REAL = prove
 (`interior real = {}`,
  MATCH_MP_TAC EMPTY_INTERIOR_LOWDIM THEN
  REWRITE_TAC[DIM_REAL; DIMINDEX_2; ARITH]);;

(* ------------------------------------------------------------------------- *)
(* Nonconstant polynomials are unbounded at infinity.                        *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_POLYFUN_EXTREMAL = prove
 (`!c n. (!k. k IN 1..n ==> c(k) = Cx(&0)) \/
         !B. eventually (\z. norm(vsum(0..n) (\i. c(i) * z pow i)) >= B)
                        at_infinity`,
  GEN_TAC THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[NUMSEG_CLAUSES; ARITH; NOT_IN_EMPTY] THEN
  MP_TAC(ARITH_RULE `0 <= n`) THEN SIMP_TAC[GSYM NUMSEG_RREC] THEN
  DISCH_THEN(K ALL_TAC) THEN ASM_CASES_TAC `c(n:num) = Cx(&0)` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM NUMSEG_RREC; LE_1] THEN
    SIMP_TAC[IN_INSERT; VSUM_CLAUSES; FINITE_NUMSEG; IN_NUMSEG] THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_ADD_LID; COND_ID] THEN
    ASM_MESON_TAC[];
    DISJ2_TAC THEN MP_TAC(ISPECL
      [`c:num->complex`; `n - 1`; `norm(c(n:num):complex) / &2`]
      COMPLEX_POLYFUN_EXTREMAL_LEMMA) THEN ASM_SIMP_TAC[SUB_ADD; LE_1] THEN
    ASM_SIMP_TAC[COMPLEX_NORM_NZ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    SIMP_TAC[IN_INSERT; VSUM_CLAUSES; FINITE_NUMSEG; IN_NUMSEG] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> ~(n <= n - 1)`] THEN
    DISCH_THEN(X_CHOOSE_TAC `M:real`) THEN X_GEN_TAC `B:real` THEN
    REWRITE_TAC[EVENTUALLY_AT_INFINITY] THEN EXISTS_TAC
     `max M (max (&1) ((abs B + &1) / (norm(c(n:num):complex) / &2)))` THEN
    X_GEN_TAC `z:complex` THEN REWRITE_TAC[real_ge; REAL_MAX_LE] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(NORM_ARITH
     `abs b + &1 <= norm(y) - a ==> norm(x) <= a ==> b <= norm(y + x)`) THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW] THEN
    REWRITE_TAC[REAL_ARITH `c * x - c / &2 * x = x * c / &2`] THEN
    ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; COMPLEX_NORM_NZ; REAL_LT_DIV;
                 REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(z:complex) pow 1` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_POW_1]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_SIMP_TAC[LE_1]]);;
