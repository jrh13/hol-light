(* ========================================================================= *)
(* The law of cosines, of sines, and sum of angles of a triangle.            *)
(* ========================================================================= *)

needs "Multivariate/transcendentals.ml";;

prioritize_vector();;

(* ------------------------------------------------------------------------- *)
(* Angle between vectors (always 0 <= angle <= pi).                          *)
(* ------------------------------------------------------------------------- *)

let vangle = new_definition
 `vangle x y = if x = vec 0 \/ y = vec 0 then pi / &2
               else acs((x dot y) / (norm x * norm y))`;;

(* ------------------------------------------------------------------------- *)
(* Traditional geometric notion of angle (but always 0 <= theta <= pi).      *)
(* ------------------------------------------------------------------------- *)

let angle = new_definition
 `angle(a,b,c) = vangle (a - b) (c - b)`;;

(* ------------------------------------------------------------------------- *)
(* Lemmas (more than we need for this result).                               *)
(* ------------------------------------------------------------------------- *)

let VANGLE = prove
 (`!x y:real^N. x dot y = norm(x) * norm(y) * cos(vangle x y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[vangle] THEN
  ASM_CASES_TAC `x:real^N = vec 0` THEN
  ASM_REWRITE_TAC[DOT_LZERO; NORM_0; REAL_MUL_LZERO] THEN
  ASM_CASES_TAC `y:real^N = vec 0` THEN
  ASM_REWRITE_TAC[DOT_RZERO; NORM_0; REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC `a * b * c:real = c * a * b`] THEN
  ASM_SIMP_TAC[GSYM REAL_EQ_LDIV_EQ; REAL_LT_MUL; NORM_POS_LT] THEN
  MATCH_MP_TAC(GSYM COS_ACS) THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; NORM_POS_LT; REAL_LT_MUL] THEN
  MP_TAC(SPECL [`x:real^N`; `y:real^N`] NORM_CAUCHY_SCHWARZ_ABS) THEN
  REAL_ARITH_TAC);;

let VANGLE_RANGE = prove
 (`!x y:real^N. &0 <= vangle x y /\ vangle x y <= pi`,
  REPEAT GEN_TAC THEN REWRITE_TAC[vangle] THEN COND_CASES_TAC THENL
   [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN MATCH_MP_TAC ACS_BOUNDS THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_LT_MUL; NORM_POS_LT] THEN
  MATCH_MP_TAC(REAL_ARITH `abs(x) <= a ==> -- &1 * a <= x /\ x <= &1 * a`) THEN
  REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS]);;

let ORTHOGONAL_VANGLE = prove
 (`!x y:real^N. orthogonal x y <=> vangle x y = pi / &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[orthogonal; vangle] THEN
  ASM_CASES_TAC `x:real^N = vec 0` THEN ASM_REWRITE_TAC[DOT_LZERO] THEN
  ASM_CASES_TAC `y:real^N = vec 0` THEN ASM_REWRITE_TAC[DOT_RZERO] THEN
  EQ_TAC THENL
   [SIMP_TAC[real_div; REAL_MUL_LZERO] THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM real_div; GSYM COS_PI2] THEN
    MATCH_MP_TAC ACS_COS THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
    MP_TAC(SPECL [`x:real^N`; `y:real^N`] NORM_CAUCHY_SCHWARZ_ABS) THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_MUL_LID] THEN
    REWRITE_TAC[GSYM REAL_BOUNDS_LE] THEN
    ONCE_REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN
    ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; GSYM REAL_LE_LDIV_EQ;
                 REAL_LT_MUL; NORM_POS_LT] THEN
    STRIP_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `cos`) THEN
    ASM_SIMP_TAC[COS_ACS; COS_PI2] THEN
    REWRITE_TAC[real_div; REAL_ENTIRE; REAL_INV_EQ_0] THEN
    ASM_REWRITE_TAC[NORM_EQ_0]]);;

let VANGLE_EQ_PI = prove
 (`!x y:real^N. vangle x y = pi ==> norm(x) % y + norm(y) % x = vec 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:real^N`; `y:real^N`] VANGLE) THEN
  ASM_REWRITE_TAC[COS_PI] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^N`; `--y:real^N`] NORM_CAUCHY_SCHWARZ_EQ) THEN
  REWRITE_TAC[NORM_NEG; DOT_RNEG; VECTOR_MUL_RNEG] THEN
  ASM_REWRITE_TAC[REAL_MUL_RNEG; REAL_NEG_NEG; REAL_MUL_RID] THEN
  VECTOR_ARITH_TAC);;

let ANGLE_EQ_PI = prove
 (`!A B C:real^N. angle(A,B,C) = pi ==> dist(A,C) = dist(A,B) + dist(B,C)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[angle] THEN
  DISCH_THEN(MP_TAC o MATCH_MP VANGLE_EQ_PI) THEN
  REWRITE_TAC[VECTOR_ARITH `a + x % (b - c) = vec 0 <=> a = x % (c - b)`] THEN
  GEN_REWRITE_TAC (funpow 3 LAND_CONV) [NORM_SUB] THEN
  REWRITE_TAC[GSYM NORM_TRIANGLE_EQ] THEN
  REWRITE_TAC[VECTOR_ARITH `(B - A) + (C - B):real^N = C - A`] THEN
  REWRITE_TAC[dist; NORM_SUB]);;

let SIN_ANGLE_POS = prove
 (`!A B C. &0 <= sin(angle(A,B,C))`,
  SIMP_TAC[SIN_POS_PI_LE; angle; VANGLE_RANGE]);;

let ANGLE = prove
 (`!A B C. (A - C) dot (B - C) = dist(A,C) * dist(B,C) * cos(angle(A,C,B))`,
  REWRITE_TAC[angle; dist; GSYM VANGLE]);;

let ANGLE_REFL = prove
 (`!A B. angle(A,A,B) = pi / &2 /\
         angle(B,A,A) = pi / &2`,
  REWRITE_TAC[angle; vangle; VECTOR_SUB_REFL]);;

let ANGLE_REFL_MID = prove
 (`!A B. ~(A = B) ==> angle(A,B,A) = &0`,
  SIMP_TAC[angle; vangle; VECTOR_SUB_EQ; GSYM NORM_POW_2; GSYM REAL_POW_2;
           REAL_DIV_REFL; ACS_1; REAL_POW_EQ_0; ARITH; NORM_EQ_0]);;

let ANGLE_SYM = prove
 (`!A B C. angle(A,B,C) = angle(C,B,A)`,
  REWRITE_TAC[angle; vangle; VECTOR_SUB_EQ; DISJ_SYM; REAL_MUL_SYM; DOT_SYM]);;

let ANGLE_RANGE = prove
 (`!A B C. &0 <= angle(A,B,C) /\ angle(A,B,C) <= pi`,
  REWRITE_TAC[angle; VANGLE_RANGE]);;

(* ------------------------------------------------------------------------- *)
(* The law of cosines.                                                       *)
(* ------------------------------------------------------------------------- *)

let LAW_OF_COSINES = prove
 (`!A B C:real^N.
     dist(B,C) pow 2 = dist(A,B) pow 2 + dist(A,C) pow 2 -
                         &2 * dist(A,B) * dist(A,C) * cos(angle(B,A,C))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[angle; ONCE_REWRITE_RULE[NORM_SUB] dist; GSYM VANGLE;
              NORM_POW_2] THEN
  VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The law of sines.                                                         *)
(* ------------------------------------------------------------------------- *)

let LAW_OF_SINES = prove
 (`!A B C:real^N.
      sin(angle(A,B,C)) * dist(B,C) = sin(angle(B,A,C)) * dist(A,C)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_POW_EQ THEN EXISTS_TAC `2` THEN
  SIMP_TAC[SIN_ANGLE_POS; DIST_POS_LE; REAL_LE_MUL; ARITH] THEN
  REWRITE_TAC[REAL_POW_MUL; MATCH_MP
   (REAL_ARITH `x + y = &1 ==> x = &1 - y`) (SPEC_ALL SIN_CIRCLE)] THEN
  ASM_CASES_TAC `A:real^N = B` THEN ASM_REWRITE_TAC[ANGLE_REFL; COS_PI2] THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM VECTOR_SUB_EQ]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM NORM_EQ_0]) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_RING
   `~(a = &0) ==> a pow 2 * x = a pow 2 * y ==> x = y`)) THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[GSYM dist] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [DIST_SYM] THEN
  REWRITE_TAC[REAL_RING
   `a * (&1 - x) * b = c * (&1 - y) * d <=>
    a * b - a * b * x = c * d - c * d * y`] THEN
  REWRITE_TAC[GSYM REAL_POW_MUL; GSYM ANGLE] THEN
  REWRITE_TAC[REAL_POW_MUL; dist; NORM_POW_2] THEN
  REWRITE_TAC[DOT_LSUB; DOT_RSUB; DOT_SYM] THEN CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* Hence the sum of the angles of a triangle.                                *)
(* ------------------------------------------------------------------------- *)

let TRIANGLE_ANGLE_SUM_LEMMA = prove
 (`!A B C:real^N. ~(A = B) /\ ~(A = C) /\ ~(B = C)
                  ==> cos(angle(B,A,C) + angle(A,B,C) + angle(B,C,A)) = -- &1`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  REWRITE_TAC[GSYM NORM_EQ_0] THEN
  MP_TAC(ISPECL [`A:real^N`; `B:real^N`; `C:real^N`] LAW_OF_COSINES) THEN
  MP_TAC(ISPECL [`B:real^N`; `A:real^N`; `C:real^N`] LAW_OF_COSINES) THEN
  MP_TAC(ISPECL [`C:real^N`; `B:real^N`; `A:real^N`] LAW_OF_COSINES) THEN
  MP_TAC(ISPECL [`A:real^N`; `B:real^N`; `C:real^N`] LAW_OF_SINES) THEN
  MP_TAC(ISPECL [`B:real^N`; `A:real^N`; `C:real^N`] LAW_OF_SINES) THEN
  MP_TAC(ISPECL [`B:real^N`; `C:real^N`; `A:real^N`] LAW_OF_SINES) THEN
  REWRITE_TAC[COS_ADD; SIN_ADD; dist; NORM_SUB] THEN
  MAP_EVERY (fun t -> MP_TAC(SPEC t SIN_CIRCLE))
   [`angle(B:real^N,A,C)`; `angle(A:real^N,B,C)`; `angle(B:real^N,C,A)`] THEN
  REWRITE_TAC[COS_ADD; SIN_ADD; ANGLE_SYM] THEN CONV_TAC REAL_RING);;

let COS_MINUS1_LEMMA = prove
 (`!x. cos(x) = -- &1 /\ &0 <= x /\ x < &3 * pi ==> x = pi`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?n. integer n /\ x = n * pi`
   (X_CHOOSE_THEN `nn:real` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  REWRITE_TAC[GSYM SIN_EQ_0] THENL
   [MP_TAC(SPEC `x:real` SIN_CIRCLE) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `?n. nn = &n` (X_CHOOSE_THEN `n:num` SUBST_ALL_TAC) THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_MUL_POS_LE]) THEN
    SIMP_TAC[PI_POS; REAL_ARITH `&0 < p ==> ~(p < &0) /\ ~(p = &0)`] THEN
    ASM_MESON_TAC[INTEGER_POS; REAL_LT_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_RING `n = &1 ==> n * p = p`) THEN
  REWRITE_TAC[REAL_OF_NUM_EQ] THEN
  MATCH_MP_TAC(ARITH_RULE `n < 3 /\ ~(n = 0) /\ ~(n = 2) ==> n = 1`) THEN
  RULE_ASSUM_TAC(SIMP_RULE[REAL_LT_RMUL_EQ; PI_POS; REAL_OF_NUM_LT]) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  REPEAT(POP_ASSUM MP_TAC) THEN SIMP_TAC[COS_0; REAL_MUL_LZERO; COS_NPI] THEN
  REAL_ARITH_TAC);;

let TRIANGLE_ANGLE_SUM = prove
 (`!A B C:real^N. ~(A = B) /\ ~(A = C) /\ ~(B = C)
                  ==> angle(B,A,C) + angle(A,B,C) + angle(B,C,A) = pi`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COS_MINUS1_LEMMA THEN
  ASM_SIMP_TAC[TRIANGLE_ANGLE_SUM_LEMMA; REAL_LE_ADD; ANGLE_RANGE] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= x /\ x <= p /\ &0 <= y /\ y <= p /\ &0 <= z /\ z <= p /\
    ~(x = p /\ y = p /\ z = p)
    ==> x + y + z < &3 * p`) THEN
  ASM_SIMP_TAC[ANGLE_RANGE] THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP ANGLE_EQ_PI)) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
   [GSYM VECTOR_SUB_EQ])) THEN
  REWRITE_TAC[GSYM NORM_EQ_0; dist; NORM_SUB] THEN REAL_ARITH_TAC);;
