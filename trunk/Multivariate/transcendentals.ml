(* ========================================================================= *)
(* Complex transcendentals and their real counterparts.                      *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(* ========================================================================= *)

needs "Multivariate/determinants.ml";;
needs "Multivariate/canal.ml";;

prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* The complex exponential function.                                         *)
(* ------------------------------------------------------------------------- *)

let cexp = new_definition
 `cexp z = infsum (from 0) (\n. z pow n / Cx(&(FACT n)))`;;

let CEXP_0 = prove
 (`cexp(Cx(&0)) = Cx(&1)`,
  REWRITE_TAC[cexp] THEN MATCH_MP_TAC INFSUM_UNIQUE THEN
  MP_TAC(ISPECL [`\i. Cx(&0) pow i / Cx(&(FACT i))`; `{0}`; `from 0`]
         SERIES_FINITE_SUPPORT) THEN
  SIMP_TAC[FROM_0; INTER_UNIV; FINITE_INSERT; FINITE_RULES] THEN ANTS_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[IN_SING; NOT_SUC] THEN
    REWRITE_TAC[complex_div; complex_pow; COMPLEX_MUL_LZERO; COMPLEX_VEC_0];
    REWRITE_TAC[VSUM_SING; FACT; COMPLEX_DIV_1; complex_pow]]);;

let CEXP_CONVERGES_UNIFORMLY_CAUCHY = prove
 (`!R e. &0 < e /\ &0 < R
         ==> ?N. !m n z. m >= N /\ norm(z) <= R
                         ==> norm(vsum(m..n) (\i. z pow i / Cx(&(FACT i))))
                                     < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`&1 / &2`; `\i. Cx(R) pow i / Cx(&(FACT i))`;
                 `from 0`] SERIES_RATIO) THEN
  REWRITE_TAC[SERIES_CAUCHY; LEFT_FORALL_IMP_THM] THEN
  MP_TAC(SPEC `&2 * norm(Cx(R))` REAL_ARCH_SIMPLE) THEN
  REWRITE_TAC[COMPLEX_NORM_CX; COMPLEX_NORM_DIV; COMPLEX_NORM_POW] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC(TAUT `(a ==> b) /\ (c ==> d) ==> a ==> (b ==> c) ==> d`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[GE] THEN DISCH_TAC THEN
    SIMP_TAC[FACT; real_pow; GSYM REAL_OF_NUM_MUL; real_div; REAL_INV_MUL] THEN
    REWRITE_TAC[REAL_ARITH
     `(z * zn) * (is * ik) <= (&1 * inv(&2)) * zn * ik <=>
      &0 <= (&1 - (&2 * z) * is) * zn * ik`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_POW_LE; REAL_SUB_LE;
             REAL_LE_INV_EQ; REAL_ABS_POS] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LT_0] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_SUC] THEN
    REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    REWRITE_TAC[FROM_0; INTER_UNIV] THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MP_TAC th) THEN
    ASM_SIMP_TAC[GSYM CX_DIV; GSYM CX_POW; VSUM_CX_NUMSEG; COMPLEX_NORM_CX] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> y < e ==> x < e`) THEN
    SUBGOAL_THEN `abs (sum (m..n) (\i. R pow i / &(FACT i))) =
                  sum (m..n) (\i. R pow i / &(FACT i))`
    SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE;REAL_LT_DIV; REAL_OF_NUM_LT;
                   FACT_LT; REAL_POW_LT];
      ALL_TAC] THEN
    MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN
    REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_POW; COMPLEX_NORM_CX] THEN
    SIMP_TAC[REAL_ABS_NUM; REAL_LE_DIV2_EQ; REAL_OF_NUM_LT; FACT_LT] THEN
    ASM_SIMP_TAC[REAL_POW_LE2; NORM_POS_LE]]);;

let CEXP_CONVERGES = prove
 (`!z. ((\n. z pow n / Cx(&(FACT n))) sums cexp(z)) (from 0)`,
  GEN_TAC THEN REWRITE_TAC[cexp; SUMS_INFSUM; summable; SERIES_CAUCHY] THEN
  REWRITE_TAC[FROM_0; INTER_UNIV] THEN
  MP_TAC(SPEC `norm(z:complex) + &1` CEXP_CONVERGES_UNIFORMLY_CAUCHY) THEN
  SIMP_TAC[REAL_ARITH `&0 <= x ==> &0 < x + &1`; NORM_POS_LE] THEN
  MESON_TAC[REAL_ARITH `x <= x + &1`]);;

let CEXP_CONVERGES_UNIQUE = prove
 (`!w z. ((\n. z pow n / Cx(&(FACT n))) sums w) (from 0) <=> w = cexp(z)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[CEXP_CONVERGES] THEN
  DISCH_THEN(MP_TAC o C CONJ (SPEC `z:complex` CEXP_CONVERGES)) THEN
  REWRITE_TAC[SERIES_UNIQUE]);;

let CEXP_CONVERGES_UNIFORMLY = prove
 (`!R e. &0 < R /\ &0 < e
         ==> ?N. !n z. n >= N /\ norm(z) < R
                       ==> norm(vsum(0..n) (\i. z pow i / Cx(&(FACT i))) -
                                cexp(z)) <= e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`R:real`; `e / &2`] CEXP_CONVERGES_UNIFORMLY_CAUCHY) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `z:complex`] THEN STRIP_TAC THEN
  MP_TAC(SPEC `z:complex` CEXP_CONVERGES) THEN
  REWRITE_TAC[sums; LIM_SEQUENTIALLY; FROM_0; INTER_UNIV; dist] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:num` (MP_TAC o SPEC `n + M + 1`)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n + 1`; `n + M + 1`; `z:complex`]) THEN
  ASM_SIMP_TAC[ARITH_RULE `(n >= N ==> n + 1 >= N) /\ M <= n + M + 1`] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; VSUM_ADD_SPLIT; LE_0] THEN
  CONV_TAC(ONCE_DEPTH_CONV(ALPHA_CONV `i:num`)) THEN NORM_ARITH_TAC);;

let HAS_COMPLEX_DERIVATIVE_CEXP = prove
 (`!z. (cexp has_complex_derivative cexp(z)) (at z)`,
  REPEAT GEN_TAC THEN MP_TAC(ISPECL
   [`ball(Cx(&0),norm(z:complex) + &1)`;
    `\n z. z pow n / Cx(&(FACT n))`;
    `\n z. if n = 0 then Cx(&0) else z pow (n-1) / Cx(&(FACT(n-1)))`;
    `cexp:complex->complex`;
    `(from 0)`]
   HAS_COMPLEX_DERIVATIVE_SERIES) THEN
  REWRITE_TAC[CONVEX_BALL; OPEN_BALL; IN_BALL; dist] THEN
  SIMP_TAC[HAS_COMPLEX_DERIVATIVE_WITHIN_OPEN; OPEN_BALL; IN_BALL;
           dist; COMPLEX_SUB_LZERO; COMPLEX_SUB_RZERO; NORM_NEG] THEN
  ANTS_TAC THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN REPEAT STRIP_TAC THEN COMPLEX_DIFF_TAC THEN
    SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[ARITH; complex_div; COMPLEX_MUL_LZERO] THEN
    MP_TAC(SPECL [`&n + &1`; `&0`] CX_INJ) THEN
    REWRITE_TAC[NOT_SUC; SUC_SUB1; GSYM REAL_OF_NUM_SUC; FACT;
         CX_ADD; CX_MUL; GSYM REAL_OF_NUM_MUL; COMPLEX_INV_MUL] THEN
    REWRITE_TAC[REAL_ARITH `~(&n + &1 = &0)`] THEN
    ABBREV_TAC `a = inv(Cx(&(FACT n)))` THEN CONV_TAC COMPLEX_FIELD;
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`norm(z:complex) + &1`; `e:real`]
       CEXP_CONVERGES_UNIFORMLY) THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_ARITH `&0 <= x ==> &0 < x + &1`] THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N + 1` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `w:complex`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n - 1`; `w:complex`]) THEN
    ASM_SIMP_TAC[ARITH_RULE `n >= m + 1 ==> n - 1 >= m`] THEN
    REWRITE_TAC[FROM_0; INTER_UNIV] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `0..n = 0 INSERT (IMAGE SUC (0..n-1))` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INSERT; IN_IMAGE; IN_NUMSEG] THEN
      INDUCT_TAC THEN REWRITE_TAC[LE_0; NOT_SUC; SUC_INJ; UNWIND_THM1] THEN
      UNDISCH_TAC `n >= N + 1` THEN ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[VSUM_CLAUSES; FINITE_IMAGE; FINITE_NUMSEG] THEN
    REWRITE_TAC[IN_IMAGE; NOT_SUC; COMPLEX_ADD_LID] THEN
    SIMP_TAC[VSUM_IMAGE; FINITE_NUMSEG; SUC_INJ] THEN
    MATCH_MP_TAC VSUM_EQ THEN SIMP_TAC[IN_NUMSEG; NOT_SUC; o_THM; SUC_SUB1];
    MAP_EVERY EXISTS_TAC [`Cx(&0)`; `cexp(Cx(&0))`] THEN
    REWRITE_TAC[CEXP_CONVERGES; COMPLEX_NORM_0] THEN
    SIMP_TAC[REAL_ARITH `&0 <= z ==> &0 < z + &1`; NORM_POS_LE];
    DISCH_THEN(X_CHOOSE_THEN `g:complex->complex` MP_TAC) THEN
    REWRITE_TAC[CEXP_CONVERGES_UNIQUE] THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`g:complex->complex`; `&1`] THEN
    REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
     [ALL_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN
      ANTS_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[]]] THEN
    POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_FORALL THEN
    X_GEN_TAC `w:complex` THEN MATCH_MP_TAC MONO_IMP THEN SIMP_TAC[] THEN
    NORM_ARITH_TAC]);;

let COMPLEX_DIFFERENTIABLE_AT_CEXP = prove
 (`!z. cexp complex_differentiable at z`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CEXP]);;

let COMPLEX_DIFFERENTIABLE_WITHIN_CEXP = prove
 (`!s z. cexp complex_differentiable (at z within s)`,
  MESON_TAC[COMPLEX_DIFFERENTIABLE_AT_WITHIN;
            COMPLEX_DIFFERENTIABLE_AT_CEXP]);;

let CONTINUOUS_AT_CEXP = prove
 (`!z. cexp continuous at z`,
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CEXP;
            HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT]);;

let CONTINUOUS_WITHIN_CEXP = prove
 (`!s z. cexp continuous (at z within s)`,
  MESON_TAC[CONTINUOUS_AT_WITHIN; CONTINUOUS_AT_CEXP]);;

let CONTINUOUS_ON_CEXP = prove
 (`!s. cexp continuous_on s`,
  MESON_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON; CONTINUOUS_AT_CEXP]);;

let HOLOMORPHIC_ON_CEXP = prove
 (`!s. cexp holomorphic_on s`,
  REWRITE_TAC [holomorphic_on] THEN
  MESON_TAC [HAS_COMPLEX_DERIVATIVE_AT_WITHIN; HAS_COMPLEX_DERIVATIVE_CEXP]);;

(* ------------------------------------------------------------------------- *)
(* Add it to the database.                                                   *)
(* ------------------------------------------------------------------------- *)

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN_UNIV
             HAS_COMPLEX_DERIVATIVE_CEXP)));;

(* ------------------------------------------------------------------------- *)
(* Hence the main results.                                                   *)
(* ------------------------------------------------------------------------- *)

let CEXP_ADD_MUL = prove
 (`!w z. cexp(w + z) * cexp(--z) = cexp(w)`,
  GEN_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE `(!x. P x) <=> (!x. x IN UNIV ==> P x)`] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_ZERO_UNIQUE THEN
  EXISTS_TAC `Cx(&0)` THEN REWRITE_TAC[OPEN_UNIV; CONVEX_UNIV; IN_UNIV] THEN
  REWRITE_TAC[COMPLEX_ADD_RID; COMPLEX_NEG_0; CEXP_0; COMPLEX_MUL_RID] THEN
  GEN_TAC THEN COMPLEX_DIFF_TAC THEN CONV_TAC COMPLEX_RING);;

let CEXP_NEG_RMUL = prove
 (`!z. cexp(z) * cexp(--z) = Cx(&1)`,
  MP_TAC(SPEC `Cx(&0)` CEXP_ADD_MUL) THEN MATCH_MP_TAC MONO_FORALL THEN
  SIMP_TAC[COMPLEX_ADD_LID; CEXP_0]);;

let CEXP_NEG_LMUL = prove
 (`!z. cexp(--z) * cexp(z) = Cx(&1)`,
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN REWRITE_TAC[CEXP_NEG_RMUL]);;

let CEXP_NEG = prove
 (`!z. cexp(--z) = inv(cexp z)`,
  MP_TAC CEXP_NEG_LMUL THEN MATCH_MP_TAC MONO_FORALL THEN
  CONV_TAC COMPLEX_FIELD);;

let CEXP_ADD = prove
 (`!w z. cexp(w + z) = cexp(w) * cexp(z)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`w:complex`; `z:complex`] CEXP_ADD_MUL) THEN
  MP_TAC(SPEC `z:complex` CEXP_NEG_LMUL) THEN CONV_TAC COMPLEX_FIELD);;

let CEXP_SUB = prove
 (`!w z. cexp(w - z) = cexp(w) / cexp(z)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[complex_sub; complex_div; CEXP_ADD; CEXP_NEG]);;

let CEXP_NZ = prove
 (`!z. ~(cexp(z) = Cx(&0))`,
  MP_TAC CEXP_NEG_LMUL THEN MATCH_MP_TAC MONO_FORALL THEN
  CONV_TAC COMPLEX_FIELD);;

let CEXP_N = prove
 (`!n x. cexp(Cx(&n) * x) = cexp(x) pow n`,
  INDUCT_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_SUC; CX_ADD] THEN
  REWRITE_TAC[COMPLEX_MUL_LZERO; complex_pow; CEXP_0] THEN
  ASM_REWRITE_TAC[COMPLEX_ADD_RDISTRIB; CEXP_ADD; COMPLEX_MUL_LID] THEN
  REWRITE_TAC[COMPLEX_MUL_AC]);;

let CEXP_VSUM = prove
 (`!f s. FINITE s ==> cexp(vsum s f) = cproduct s (\x. cexp(f x))`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; CPRODUCT_CLAUSES; CEXP_ADD; COMPLEX_VEC_0; CEXP_0]);;

let LIM_CEXP_MINUS_1 = prove
 (`((\z. (cexp(z) - Cx(&1)) / z) --> Cx(&1)) (at (Cx(&0)))`,
  MP_TAC(COMPLEX_DIFF_CONV
      `((\z. cexp(z) - Cx(&1)) has_complex_derivative f') (at(Cx(&0)))`) THEN
  REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_AT; CEXP_0; COMPLEX_SUB_REFL] THEN
  REWRITE_TAC[COMPLEX_MUL_LID; COMPLEX_SUB_RZERO]);;

(* ------------------------------------------------------------------------- *)
(* Crude bounds on complex exponential function, usable to get tighter ones. *)
(* ------------------------------------------------------------------------- *)

let CEXP_BOUND_BLEMMA = prove
 (`!B. (!z. norm(z) <= &1 / &2 ==> norm(cexp z) <= B)
       ==> !z. norm(z) <= &1 / &2 ==> norm(cexp z) <= &1 + B / &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`cexp`; `cexp`; `cball(Cx(&0),&1 / &2)`; `B:real`]
                COMPLEX_DIFFERENTIABLE_BOUND) THEN
  ASM_SIMP_TAC[CONVEX_CBALL; IN_CBALL; dist; COMPLEX_SUB_LZERO; NORM_NEG;
    HAS_COMPLEX_DERIVATIVE_AT_WITHIN; HAS_COMPLEX_DERIVATIVE_CEXP] THEN
  DISCH_THEN(MP_TAC o SPECL [`z:complex`; `Cx(&0)`]) THEN
  REWRITE_TAC[COMPLEX_NORM_0; CEXP_0; COMPLEX_SUB_RZERO] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(y) = &1 /\ d <= e ==> norm(x - y) <= d ==> norm(x) <= &1 + e`) THEN
  REWRITE_TAC[COMPLEX_NORM_CX; real_div; REAL_ABS_NUM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN FIRST_X_ASSUM(MP_TAC o SPEC `Cx(&0)`) THEN
  REWRITE_TAC[COMPLEX_NORM_CX] THEN POP_ASSUM MP_TAC THEN
  NORM_ARITH_TAC);;

let CEXP_BOUND_HALF = prove
 (`!z. norm(z) <= &1 / &2 ==> norm(cexp z) <= &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE cexp (cball(Cx(&0),&1 / &2))`; `Cx(&0)`]
    DISTANCE_ATTAINS_SUP) THEN
  SIMP_TAC[COMPACT_CONTINUOUS_IMAGE; COMPACT_CBALL; CONTINUOUS_ON_CEXP;
           IMAGE_EQ_EMPTY; CBALL_EQ_EMPTY; FORALL_IN_IMAGE; EXISTS_IN_IMAGE;
           IN_CBALL; dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `w:complex` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPEC `w:complex` o MATCH_MP CEXP_BOUND_BLEMMA) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let CEXP_BOUND_LEMMA = prove
 (`!z. norm(z) <= &1 / &2 ==> norm(cexp z) <= &1 + &2 * norm(z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`cexp`; `cexp`; `cball(Cx(&0),&1 / &2)`; `&2`]
                COMPLEX_DIFFERENTIABLE_BOUND) THEN
  ASM_SIMP_TAC[CONVEX_CBALL; IN_CBALL; dist; COMPLEX_SUB_LZERO; NORM_NEG;
               HAS_COMPLEX_DERIVATIVE_AT_WITHIN; HAS_COMPLEX_DERIVATIVE_CEXP;
               CEXP_BOUND_HALF] THEN
  DISCH_THEN(MP_TAC o SPECL [`z:complex`; `Cx(&0)`]) THEN
  REWRITE_TAC[COMPLEX_NORM_0; CEXP_0; COMPLEX_SUB_RZERO] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(y) = &1 ==> norm(x - y) <= d ==> norm(x) <= &1 + d`) THEN
  REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM]);;

(* ------------------------------------------------------------------------- *)
(* Complex trig functions.                                                   *)
(* ------------------------------------------------------------------------- *)

let ccos = new_definition
  `ccos z = (cexp(ii * z) + cexp(--ii * z)) / Cx(&2)`;;

let csin = new_definition
  `csin z = (cexp(ii * z) - cexp(--ii * z)) / (Cx(&2) * ii)`;;

let CSIN_0 = prove
 (`csin(Cx(&0)) = Cx(&0)`,
  REWRITE_TAC[csin; COMPLEX_MUL_RZERO; COMPLEX_SUB_REFL] THEN
  CONV_TAC COMPLEX_FIELD);;

let CCOS_0 = prove
 (`ccos(Cx(&0)) = Cx(&1)`,
  REWRITE_TAC[ccos; COMPLEX_MUL_RZERO; CEXP_0] THEN
  CONV_TAC COMPLEX_FIELD);;

let CSIN_CIRCLE = prove
 (`!z. csin(z) pow 2 + ccos(z) pow 2 = Cx(&1)`,
  GEN_TAC THEN REWRITE_TAC[csin; ccos] THEN
  MP_TAC(SPEC `ii * z` CEXP_NEG_LMUL) THEN
  REWRITE_TAC[COMPLEX_MUL_LNEG] THEN
  CONV_TAC COMPLEX_FIELD);;

let CSIN_ADD = prove
 (`!w z. csin(w + z) = csin(w) * ccos(z) + ccos(w) * csin(z)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[csin; ccos; COMPLEX_ADD_LDISTRIB; CEXP_ADD] THEN
  CONV_TAC COMPLEX_FIELD);;

let CCOS_ADD = prove
 (`!w z. ccos(w + z) = ccos(w) * ccos(z) - csin(w) * csin(z)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[csin; ccos; COMPLEX_ADD_LDISTRIB; CEXP_ADD] THEN
  CONV_TAC COMPLEX_FIELD);;

let CSIN_NEG = prove
 (`!z. csin(--z) = --(csin(z))`,
  REWRITE_TAC[csin; COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG; COMPLEX_NEG_NEG] THEN
  CONV_TAC COMPLEX_FIELD);;

let CCOS_NEG = prove
 (`!z. ccos(--z) = ccos(z)`,
  REWRITE_TAC[ccos; COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG; COMPLEX_NEG_NEG] THEN
  CONV_TAC COMPLEX_FIELD);;

let CSIN_DOUBLE = prove
 (`!z. csin(Cx(&2) * z) = Cx(&2) * csin(z) * ccos(z)`,
  REWRITE_TAC[COMPLEX_RING `Cx(&2) * x = x + x`; CSIN_ADD] THEN
  CONV_TAC COMPLEX_RING);;

let CCOS_DOUBLE = prove
 (`!z. ccos(Cx(&2) * z) = (ccos(z) pow 2) - (csin(z) pow 2)`,
  REWRITE_TAC[COMPLEX_RING `Cx(&2) * x = x + x`; CCOS_ADD] THEN
  CONV_TAC COMPLEX_RING);;

let CSIN_SUB = prove
 (`!w z. csin(w - z) = csin(w) * ccos(z) - ccos(w) * csin(z)`,
  REWRITE_TAC[complex_sub; COMPLEX_MUL_RNEG; CSIN_ADD; CSIN_NEG; CCOS_NEG]);;

let CCOS_SUB = prove
 (`!w z. ccos(w - z) = ccos(w) * ccos(z) + csin(w) * csin(z)`,
  REWRITE_TAC[complex_sub; CCOS_ADD; CSIN_NEG; CCOS_NEG;
              COMPLEX_MUL_RNEG; COMPLEX_NEG_NEG]);;

let COMPLEX_MUL_CSIN_CSIN = prove
 (`!w z. csin(w) * csin(z) = (ccos(w - z) - ccos(w + z)) / Cx(&2)`,
  REWRITE_TAC[CCOS_ADD; CCOS_SUB] THEN CONV_TAC COMPLEX_RING);;

let COMPLEX_MUL_CSIN_CCOS = prove
 (`!w z. csin(w) * ccos(z) = (csin(w + z) + csin(w - z)) / Cx(&2)`,
  REWRITE_TAC[CSIN_ADD; CSIN_SUB] THEN CONV_TAC COMPLEX_RING);;

let COMPLEX_MUL_CCOS_CSIN = prove
 (`!w z. ccos(w) * csin(z) = (csin(w + z) - csin(w - z)) / Cx(&2)`,
  REWRITE_TAC[CSIN_ADD; CSIN_SUB] THEN CONV_TAC COMPLEX_RING);;

let COMPLEX_MUL_CCOS_CCOS = prove
 (`!w z. ccos(w) * ccos(z) = (ccos(w - z) + ccos(w + z)) / Cx(&2)`,
  REWRITE_TAC[CCOS_ADD; CCOS_SUB] THEN CONV_TAC COMPLEX_RING);;

let COMPLEX_ADD_CSIN = prove
 (`!w z. csin(w) + csin(z) =
         Cx(&2) * csin((w + z) / Cx(&2)) * ccos((w - z) / Cx(&2))`,
  SIMP_TAC[COMPLEX_MUL_CSIN_CCOS; COMPLEX_RING `Cx(&2) * x / Cx(&2) = x`] THEN
  REPEAT GEN_TAC THEN BINOP_TAC THEN AP_TERM_TAC THEN CONV_TAC COMPLEX_RING);;

let COMPLEX_SUB_CSIN = prove
 (`!w z. csin(w) - csin(z) =
         Cx(&2) * csin((w - z) / Cx(&2)) * ccos((w + z) / Cx(&2))`,
  SIMP_TAC[COMPLEX_MUL_CSIN_CCOS; COMPLEX_RING `Cx(&2) * x / Cx(&2) = x`] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[complex_sub; GSYM CSIN_NEG] THEN
  BINOP_TAC THEN AP_TERM_TAC THEN CONV_TAC COMPLEX_RING);;

let COMPLEX_ADD_CCOS = prove
 (`!w z. ccos(w) + ccos(z) =
         Cx(&2) * ccos((w + z) / Cx(&2)) * ccos((w - z) / Cx(&2))`,
  SIMP_TAC[COMPLEX_MUL_CCOS_CCOS; COMPLEX_RING `Cx(&2) * x / Cx(&2) = x`] THEN
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [COMPLEX_ADD_SYM] THEN
  BINOP_TAC THEN AP_TERM_TAC THEN CONV_TAC COMPLEX_RING);;

let COMPLEX_SUB_CCOS = prove
 (`!w z. ccos(w) - ccos(z) =
         Cx(&2) * csin((w + z) / Cx(&2)) * csin((z - w) / Cx(&2))`,
  SIMP_TAC[COMPLEX_MUL_CSIN_CSIN; COMPLEX_RING `Cx(&2) * x / Cx(&2) = x`] THEN
  REPEAT GEN_TAC THEN BINOP_TAC THEN AP_TERM_TAC THEN CONV_TAC COMPLEX_RING);;

let CCOS_DOUBLE_CCOS = prove
 (`!z. ccos(Cx(&2) * z) = Cx(&2) * ccos z pow 2 - Cx(&1)`,
  GEN_TAC THEN REWRITE_TAC[COMPLEX_RING `Cx(&2) * x = x + x`; CCOS_ADD] THEN
  MP_TAC(SPEC `z:complex` CSIN_CIRCLE) THEN CONV_TAC COMPLEX_RING);;

let CCOS_DOUBLE_CSIN = prove
 (`!z. ccos(Cx(&2) * z) = Cx(&1) - Cx(&2) * csin z pow 2`,
  GEN_TAC THEN REWRITE_TAC[COMPLEX_RING `Cx(&2) * x = x + x`; CCOS_ADD] THEN
  MP_TAC(SPEC `z:complex` CSIN_CIRCLE) THEN CONV_TAC COMPLEX_RING);;

(* ------------------------------------------------------------------------- *)
(* Euler and de Moivre formulas.                                             *)
(* ------------------------------------------------------------------------- *)

let CEXP_EULER = prove
 (`!z. cexp(ii * z) = ccos(z) + ii * csin(z)`,
  REWRITE_TAC[ccos; csin] THEN CONV_TAC COMPLEX_FIELD);;

let DEMOIVRE = prove
 (`!z n. (ccos z + ii * csin z) pow n =
         ccos(Cx(&n) * z) + ii * csin(Cx(&n) * z)`,
  REWRITE_TAC[GSYM CEXP_EULER; GSYM CEXP_N] THEN
  REWRITE_TAC[COMPLEX_MUL_AC]);;

(* ------------------------------------------------------------------------- *)
(* Real exponential function. Same names as old Library/transc.ml.           *)
(* ------------------------------------------------------------------------- *)

let exp = new_definition `exp(x) = Re(cexp(Cx x))`;;

let CNJ_CEXP = prove
 (`!z. cnj(cexp z) = cexp(cnj z)`,
  GEN_TAC THEN MATCH_MP_TAC SERIES_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`\n. cnj(z pow n / Cx(&(FACT n)))`; `from 0`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUMS_CNJ; CEXP_CONVERGES];
    REWRITE_TAC[CNJ_DIV; CNJ_CX; CNJ_POW; CEXP_CONVERGES]]);;

let REAL_EXP = prove
 (`!z. real z ==> real(cexp z)`,
  SIMP_TAC[REAL_CNJ; CNJ_CEXP]);;

let CX_EXP = prove
 (`!x. Cx(exp x) = cexp(Cx x)`,
  REWRITE_TAC[exp] THEN MESON_TAC[REAL; REAL_CX; REAL_EXP]);;

let REAL_EXP_ADD = prove
 (`!x y. exp(x + y) = exp(x) * exp(y)`,
  REWRITE_TAC[GSYM CX_INJ; CX_MUL; CX_EXP; CX_ADD; CEXP_ADD]);;

let REAL_EXP_0 = prove
 (`exp(&0) = &1`,
  REWRITE_TAC[GSYM CX_INJ; CX_EXP; CEXP_0]);;

let REAL_EXP_ADD_MUL = prove
 (`!x y. exp(x + y) * exp(--x) = exp(y)`,
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[GSYM CX_INJ; CX_MUL; CX_EXP; CX_ADD; CX_NEG; CEXP_ADD_MUL]);;

let REAL_EXP_NEG_MUL = prove
 (`!x. exp(x) * exp(--x) = &1`,
  REWRITE_TAC[GSYM CX_INJ; CX_MUL; CX_EXP; CX_NEG; CEXP_NEG_RMUL]);;

let REAL_EXP_NEG_MUL2 = prove
 (`!x. exp(--x) * exp(x) = &1`,
  REWRITE_TAC[GSYM CX_INJ; CX_MUL; CX_EXP; CX_NEG; CEXP_NEG_LMUL]);;

let REAL_EXP_NEG = prove
 (`!x. exp(--x) = inv(exp(x))`,
  REWRITE_TAC[GSYM CX_INJ; CX_INV; CX_EXP; CX_NEG; CEXP_NEG]);;

let REAL_EXP_N = prove
 (`!n x. exp(&n * x) = exp(x) pow n`,
  REWRITE_TAC[GSYM CX_INJ; CX_EXP; CX_POW; CX_MUL; CEXP_N]);;

let REAL_EXP_SUB = prove
 (`!x y. exp(x - y) = exp(x) / exp(y)`,
  REWRITE_TAC[GSYM CX_INJ; CX_SUB; CX_DIV; CX_EXP; CEXP_SUB]);;

let REAL_EXP_NZ = prove
 (`!x. ~(exp(x) = &0)`,
  REWRITE_TAC[GSYM CX_INJ; CX_EXP; CEXP_NZ]);;

let REAL_EXP_POS_LE = prove
 (`!x. &0 <= exp(x)`,
  GEN_TAC THEN SUBST1_TAC(REAL_ARITH `x = x / &2 + x / &2`) THEN
  REWRITE_TAC[REAL_EXP_ADD; REAL_LE_SQUARE]);;

let REAL_EXP_POS_LT = prove
 (`!x. &0 < exp(x)`,
  REWRITE_TAC[REAL_LT_LE; REAL_EXP_NZ; REAL_EXP_POS_LE]);;

let REAL_EXP_LE_X = prove
 (`!x. &1 + x <= exp(x)`,
  GEN_TAC THEN ASM_CASES_TAC `&1 + x < &0` THENL
   [MP_TAC(SPEC `x:real` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[exp; RE_DEF] THEN
  MATCH_MP_TAC(MATCH_MP
   (ONCE_REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> b ==> a /\ c ==> d`]
        LIM_COMPONENT_LBOUND)
   (REWRITE_RULE[sums] (SPEC `Cx x` CEXP_CONVERGES))) THEN
  SIMP_TAC[DIMINDEX_2; ARITH; TRIVIAL_LIMIT_SEQUENTIALLY;
           VSUM_COMPONENT; EVENTUALLY_SEQUENTIALLY; FROM_0; INTER_UNIV] THEN
  REWRITE_TAC[GSYM CX_DIV; GSYM RE_DEF; RE_CX; GSYM CX_POW] THEN
  EXISTS_TAC `1` THEN SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ADD_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[real_pow; REAL_POW_1; REAL_DIV_1; REAL_LE_ADDR; REAL_ADD_ASSOC] THEN
  SUBGOAL_THEN
   `!n. &0 <= sum(2*1..2*n+1) (\k. x pow k / &(FACT k))`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[SUM_PAIR] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM ADD1; real_pow; FACT; GSYM REAL_OF_NUM_MUL] THEN
    ASM_SIMP_TAC[REAL_OF_NUM_EQ; FACT_NZ; NOT_SUC; REAL_FIELD
     `~(k = &0) /\ ~(f = &0)
      ==> p / f + (x * p) / (k * f) = p / f * (&1 + x / k)`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[REAL_ARITH `&0 <= a + b <=> --a <= b`] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; LT_0; REAL_OF_NUM_LT] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN ASM_REAL_ARITH_TAC];
    RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MP_TAC(SPEC `n - 1` EVEN_OR_ODD) THEN
    ASM_SIMP_TAC[EVEN_EXISTS; ODD_EXISTS;
                 ARITH_RULE `1 <= n ==> (n - 1 = d <=> n = SUC d)`] THEN
    STRIP_TAC THENL [ASM_MESON_TAC[ADD1]; ALL_TAC] THEN
    ASM_REWRITE_TAC[ARITH_RULE `SUC(2 * n) = 2 * n + 1`] THEN
    ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG] THEN
    COND_CASES_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN
    ASM_REWRITE_TAC[ARITH_RULE `SUC(2 * m + 1) = 2 * (m + 1)`]] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
  ASM_SIMP_TAC[GSYM REAL_POW_POW; REAL_POW_LE; REAL_LE_POW_2]);;

let REAL_EXP_LT_1 = prove
 (`!x. &0 < x ==> &1 < exp(x)`,
  MP_TAC REAL_EXP_LE_X THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC);;

let REAL_EXP_MONO_IMP = prove
 (`!x y. x < y ==> exp(x) < exp(y)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_SUB_LT] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_EXP_LT_1) THEN
  SIMP_TAC[REAL_EXP_SUB; REAL_LT_RDIV_EQ; REAL_EXP_POS_LT; REAL_MUL_LID]);;

let REAL_EXP_MONO_LT = prove
 (`!x y. exp(x) < exp(y) <=> x < y`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH
   `(x < y ==> f < g) /\ (x = y ==> f = g) /\ (y < x ==> g < f)
    ==> (f < g <=> x < y)`) THEN
  SIMP_TAC[REAL_EXP_MONO_IMP]);;

let REAL_EXP_MONO_LE = prove
 (`!x y. exp(x) <= exp(y) <=> x <= y`,
  REWRITE_TAC[GSYM REAL_NOT_LT; REAL_EXP_MONO_LT]);;

let REAL_EXP_INJ = prove
 (`!x y. (exp(x) = exp(y)) <=> (x = y)`,
  REWRITE_TAC[GSYM REAL_LE_ANTISYM; REAL_EXP_MONO_LE]);;

let REAL_EXP_EQ_1 = prove
 (`!x. exp(x) = &1 <=> x = &0`,
  ONCE_REWRITE_TAC[GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_INJ]);;

let REAL_ABS_EXP = prove
 (`!x. abs(exp x) = exp x`,
  REWRITE_TAC[real_abs; REAL_EXP_POS_LE]);;

let REAL_EXP_SUM = prove
 (`!f s. FINITE s ==> exp(sum s f) = product s (\x. exp(f x))`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; PRODUCT_CLAUSES; REAL_EXP_ADD; REAL_EXP_0]);;

let REAL_EXP_BOUND_LEMMA = prove
 (`!x. &0 <= x /\ x <= inv(&2) ==> exp(x) <= &1 + &2 * x`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `Cx x` CEXP_BOUND_LEMMA) THEN
  REWRITE_TAC[GSYM CX_EXP; COMPLEX_NORM_CX; RE_CX] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Real trig functions, their reality,  derivatives of complex versions.     *)
(* ------------------------------------------------------------------------- *)

let sin = new_definition `sin(x) = Re(csin(Cx x))`;;

let cos = new_definition `cos(x) = Re(ccos(Cx x))`;;

let CNJ_CSIN = prove
 (`!z. cnj(csin z) = csin(cnj z)`,
  REWRITE_TAC[csin; CNJ_DIV; CNJ_SUB; CNJ_MUL; CNJ_CX; CNJ_CEXP;
              CNJ_NEG; CNJ_II; COMPLEX_NEG_NEG] THEN
  CONV_TAC COMPLEX_FIELD);;

let CNJ_CCOS = prove
 (`!z. cnj(ccos z) = ccos(cnj z)`,
  REWRITE_TAC[ccos; CNJ_DIV; CNJ_ADD; CNJ_MUL; CNJ_CX; CNJ_CEXP;
              CNJ_NEG; CNJ_II; COMPLEX_NEG_NEG; COMPLEX_ADD_AC]);;

let REAL_SIN = prove
 (`!z. real z ==> real(csin z)`,
  SIMP_TAC[REAL_CNJ; CNJ_CSIN]);;

let REAL_COS = prove
 (`!z. real z ==> real(ccos z)`,
  SIMP_TAC[REAL_CNJ; CNJ_CCOS]);;

let CX_SIN = prove
 (`!x. Cx(sin x) = csin(Cx x)`,
  REWRITE_TAC[sin] THEN MESON_TAC[REAL; REAL_CX; REAL_SIN]);;

let CX_COS = prove
 (`!x. Cx(cos x) = ccos(Cx x)`,
  REWRITE_TAC[cos] THEN MESON_TAC[REAL; REAL_CX; REAL_COS]);;

let HAS_COMPLEX_DERIVATIVE_CSIN = prove
 (`!z. (csin has_complex_derivative ccos z) (at z)`,
  GEN_TAC THEN GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[csin; ccos] THEN COMPLEX_DIFF_TAC THEN
  CONV_TAC COMPLEX_FIELD);;

let COMPLEX_DIFFERENTIABLE_AT_CSIN = prove
 (`!z. csin complex_differentiable at z`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CSIN]);;

let COMPLEX_DIFFERENTIABLE_WITHIN_CSIN = prove
 (`!s z. csin complex_differentiable (at z within s)`,
  MESON_TAC[COMPLEX_DIFFERENTIABLE_AT_WITHIN;
            COMPLEX_DIFFERENTIABLE_AT_CSIN]);;

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN_UNIV
             HAS_COMPLEX_DERIVATIVE_CSIN)));;

let HAS_COMPLEX_DERIVATIVE_CCOS = prove
 (`!z. (ccos has_complex_derivative --csin z) (at z)`,
  GEN_TAC THEN GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[csin; ccos] THEN COMPLEX_DIFF_TAC THEN
  CONV_TAC COMPLEX_FIELD);;

let COMPLEX_DIFFERENTIABLE_AT_CCOS = prove
 (`!z. ccos complex_differentiable at z`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CCOS]);;

let COMPLEX_DIFFERENTIABLE_WITHIN_CCOS = prove
 (`!s z. ccos complex_differentiable (at z within s)`,
  MESON_TAC[COMPLEX_DIFFERENTIABLE_AT_WITHIN;
            COMPLEX_DIFFERENTIABLE_AT_CCOS]);;

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN_UNIV
             HAS_COMPLEX_DERIVATIVE_CCOS)));;

let CONTINUOUS_AT_CSIN = prove
 (`!z. csin continuous at z`,
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CSIN;
            HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT]);;

let CONTINUOUS_WITHIN_CSIN = prove
 (`!s z. csin continuous (at z within s)`,
  MESON_TAC[CONTINUOUS_AT_WITHIN; CONTINUOUS_AT_CSIN]);;

let CONTINUOUS_ON_CSIN = prove
 (`!s. csin continuous_on s`,
  MESON_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON; CONTINUOUS_AT_CSIN]);;

let HOLOMORPHIC_ON_CSIN = prove
 (`!s. csin holomorphic_on s`,
  REWRITE_TAC [holomorphic_on] THEN
  MESON_TAC [HAS_COMPLEX_DERIVATIVE_AT_WITHIN; HAS_COMPLEX_DERIVATIVE_CSIN]);;

let CONTINUOUS_AT_CCOS = prove
 (`!z. ccos continuous at z`,
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CCOS;
            HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT]);;

let CONTINUOUS_WITHIN_CCOS = prove
 (`!s z. ccos continuous (at z within s)`,
  MESON_TAC[CONTINUOUS_AT_WITHIN; CONTINUOUS_AT_CCOS]);;

let CONTINUOUS_ON_CCOS = prove
 (`!s. ccos continuous_on s`,
  MESON_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON; CONTINUOUS_AT_CCOS]);;

let HOLOMORPHIC_ON_CCOS = prove
 (`!s. ccos holomorphic_on s`,
  REWRITE_TAC [holomorphic_on] THEN
  MESON_TAC [HAS_COMPLEX_DERIVATIVE_AT_WITHIN; HAS_COMPLEX_DERIVATIVE_CCOS]);;

(* ------------------------------------------------------------------------- *)
(* Slew of theorems for compatibility with old transc.ml file.               *)
(* ------------------------------------------------------------------------- *)

let SIN_0 = prove
 (`sin(&0) = &0`,
  REWRITE_TAC[GSYM CX_INJ; CX_SIN; CSIN_0]);;

let COS_0 = prove
 (`cos(&0) = &1`,
  REWRITE_TAC[GSYM CX_INJ; CX_COS; CCOS_0]);;

let SIN_CIRCLE = prove
 (`!x. (sin(x) pow 2) + (cos(x) pow 2) = &1`,
  REWRITE_TAC[GSYM CX_INJ; CX_COS; CX_SIN; CX_ADD; CX_POW; CSIN_CIRCLE]);;

let SIN_ADD = prove
 (`!x y. sin(x + y) = sin(x) * cos(y) + cos(x) * sin(y)`,
  REWRITE_TAC[GSYM CX_INJ; CX_COS; CX_SIN; CX_ADD; CX_MUL; CSIN_ADD]);;

let COS_ADD = prove
 (`!x y. cos(x + y) = cos(x) * cos(y) - sin(x) * sin(y)`,
  REWRITE_TAC[GSYM CX_INJ; CX_COS; CX_SIN; CX_ADD; CX_SUB; CX_MUL; CCOS_ADD]);;

let SIN_NEG = prove
 (`!x. sin(--x) = --(sin(x))`,
  REWRITE_TAC[GSYM CX_INJ; CX_SIN; CX_NEG; CSIN_NEG]);;

let COS_NEG = prove
 (`!x. cos(--x) = cos(x)`,
  REWRITE_TAC[GSYM CX_INJ; CX_COS; CX_NEG; CCOS_NEG]);;

let SIN_DOUBLE = prove
 (`!x. sin(&2 * x) = &2 * sin(x) * cos(x)`,
  REWRITE_TAC[GSYM CX_INJ; CX_SIN; CX_COS; CX_MUL; CSIN_DOUBLE]);;

let COS_DOUBLE = prove
 (`!x. cos(&2 * x) = (cos(x) pow 2) - (sin(x) pow 2)`,
  SIMP_TAC[GSYM CX_INJ; CX_SIN; CX_COS; CX_SUB; CX_MUL; CX_POW; CCOS_DOUBLE]);;

let COS_DOUBLE_COS = prove
 (`!x. cos(&2 * x) = &2 * cos(x) pow 2 - &1`,
  MP_TAC SIN_CIRCLE THEN MATCH_MP_TAC MONO_FORALL THEN
  REWRITE_TAC[COS_DOUBLE] THEN REAL_ARITH_TAC);;

let (SIN_BOUND,COS_BOUND) = (CONJ_PAIR o prove)
 (`(!x. abs(sin x) <= &1) /\ (!x. abs(cos x) <= &1)`,
  CONJ_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_ABS_NUM] THEN
  ONCE_REWRITE_TAC[REAL_LE_SQUARE_ABS] THEN
  MP_TAC(SPEC `x:real` SIN_CIRCLE) THEN
  MAP_EVERY (MP_TAC o C SPEC REAL_LE_SQUARE) [`sin x`; `cos x`] THEN
  REAL_ARITH_TAC);;

let SIN_BOUNDS = prove
 (`!x. --(&1) <= sin(x) /\ sin(x) <= &1`,
  MP_TAC SIN_BOUND THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC);;

let COS_BOUNDS = prove
 (`!x. --(&1) <= cos(x) /\ cos(x) <= &1`,
  MP_TAC COS_BOUND THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC);;

let COS_ABS = prove
 (`!x. cos(abs x) = cos(x)`,
  REWRITE_TAC[real_abs] THEN MESON_TAC[COS_NEG]);;

let SIN_SUB = prove
 (`!w z. sin(w - z) = sin(w) * cos(z) - cos(w) * sin(z)`,
  REWRITE_TAC[GSYM CX_INJ; CX_SIN; CX_COS; CX_SUB; CX_MUL; CSIN_SUB]);;

let COS_SUB = prove
 (`!w z. cos(w - z) = cos(w) * cos(z) + sin(w) * sin(z)`,
  REWRITE_TAC[GSYM CX_INJ; CX_SIN; CX_COS; CX_SUB; CX_ADD; CX_MUL; CCOS_SUB]);;

let REAL_MUL_SIN_SIN = prove
 (`!x y. sin(x) * sin(y) = (cos(x - y) - cos(x + y)) / &2`,
  REWRITE_TAC[GSYM CX_INJ; CX_COS; CX_SIN; CX_ADD; CX_SUB; CX_MUL; CX_DIV] THEN
  REWRITE_TAC[COMPLEX_MUL_CSIN_CSIN]);;

let REAL_MUL_SIN_COS = prove
 (`!x y. sin(x) * cos(y) = (sin(x + y) + sin(x - y)) / &2`,
  REWRITE_TAC[GSYM CX_INJ; CX_COS; CX_SIN; CX_ADD; CX_SUB; CX_MUL; CX_DIV] THEN
  REWRITE_TAC[COMPLEX_MUL_CSIN_CCOS]);;

let REAL_MUL_COS_SIN = prove
 (`!x y. cos(x) * sin(y) = (sin(x + y) - sin(x - y)) / &2`,
  REWRITE_TAC[GSYM CX_INJ; CX_COS; CX_SIN; CX_ADD; CX_SUB; CX_MUL; CX_DIV] THEN
  REWRITE_TAC[COMPLEX_MUL_CCOS_CSIN]);;

let REAL_MUL_COS_COS = prove
 (`!x y. cos(x) * cos(y) = (cos(x - y) + cos(x + y)) / &2`,
  REWRITE_TAC[GSYM CX_INJ; CX_COS; CX_SIN; CX_ADD; CX_SUB; CX_MUL; CX_DIV] THEN
  REWRITE_TAC[COMPLEX_MUL_CCOS_CCOS]);;

let REAL_ADD_SIN = prove
 (`!x y. sin(x) + sin(y) = &2 * sin((x + y) / &2) * cos((x - y) / &2)`,
  REWRITE_TAC[GSYM CX_INJ; CX_COS; CX_SIN; CX_ADD; CX_SUB; CX_MUL; CX_DIV] THEN
  REWRITE_TAC[COMPLEX_ADD_CSIN]);;

let REAL_SUB_SIN = prove
 (`!x y. sin(x) - sin(y) = &2 * sin((x - y) / &2) * cos((x + y) / &2)`,
  REWRITE_TAC[GSYM CX_INJ; CX_COS; CX_SIN; CX_ADD; CX_SUB; CX_MUL; CX_DIV] THEN
  REWRITE_TAC[COMPLEX_SUB_CSIN]);;

let REAL_ADD_COS = prove
 (`!x y. cos(x) + cos(y) = &2 * cos((x + y) / &2) * cos((x - y) / &2)`,
  REWRITE_TAC[GSYM CX_INJ; CX_COS; CX_SIN; CX_ADD; CX_SUB; CX_MUL; CX_DIV] THEN
  REWRITE_TAC[COMPLEX_ADD_CCOS]);;

let REAL_SUB_COS = prove
 (`!x y. cos(x) - cos(y) = &2 * sin((x + y) / &2) * sin((y - x) / &2)`,
  REWRITE_TAC[GSYM CX_INJ; CX_COS; CX_SIN; CX_ADD; CX_SUB; CX_MUL; CX_DIV] THEN
  REWRITE_TAC[COMPLEX_SUB_CCOS]);;

let COS_DOUBLE_SIN = prove
 (`!x. cos(&2 * x) = &1 - &2 * sin x pow 2`,
  GEN_TAC THEN REWRITE_TAC[REAL_RING `&2 * x = x + x`; COS_ADD] THEN
  MP_TAC(SPEC `x:real` SIN_CIRCLE) THEN CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* Get a nice real/imaginary separation in Euler's formula.                  *)
(* ------------------------------------------------------------------------- *)

let EULER = prove
 (`!z. cexp(z) = Cx(exp(Re z)) * (Cx(cos(Im z)) + ii * Cx(sin(Im z)))`,
  GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [COMPLEX_EXPAND] THEN
  REWRITE_TAC[CEXP_ADD; CEXP_EULER; GSYM CX_SIN; GSYM CX_COS; GSYM CX_EXP]);;

let RE_CEXP = prove
 (`!z. Re(cexp z) = exp(Re z) * cos(Im z)`,
  REWRITE_TAC[EULER; RE_ADD; RE_MUL_CX; RE_MUL_II; IM_CX; RE_CX] THEN
  REAL_ARITH_TAC);;

let IM_CEXP = prove
 (`!z. Im(cexp z) = exp(Re z) * sin(Im z)`,
  REWRITE_TAC[EULER; IM_ADD; IM_MUL_CX; IM_MUL_II; IM_CX; RE_CX] THEN
  REAL_ARITH_TAC);;

let RE_CSIN = prove
 (`!z. Re(csin z) = (exp(Im z) + exp(--(Im z))) / &2 * sin(Re z)`,
  GEN_TAC THEN REWRITE_TAC[csin] THEN
  SIMP_TAC[COMPLEX_FIELD `x / (Cx(&2) * ii) = ii * --(x / Cx(&2))`] THEN
  REWRITE_TAC[IM_MUL_II; IM_DIV_CX; RE_NEG; IM_SUB; IM_CEXP;
              RE_MUL_II; COMPLEX_MUL_LNEG; IM_NEG] THEN
  REWRITE_TAC[REAL_NEG_NEG; SIN_NEG] THEN CONV_TAC REAL_RING);;

let IM_CSIN = prove
 (`!z. Im(csin z) = (exp(Im z) - exp(--(Im z))) / &2 * cos(Re z)`,
  GEN_TAC THEN REWRITE_TAC[csin] THEN
  SIMP_TAC[COMPLEX_FIELD `x / (Cx(&2) * ii) = ii * --(x / Cx(&2))`] THEN
  REWRITE_TAC[IM_MUL_II; RE_DIV_CX; RE_NEG; RE_SUB; RE_CEXP;
              RE_MUL_II; COMPLEX_MUL_LNEG; IM_NEG] THEN
  REWRITE_TAC[REAL_NEG_NEG; COS_NEG] THEN CONV_TAC REAL_RING);;

let RE_CCOS = prove
 (`!z. Re(ccos z) = (exp(Im z) + exp(--(Im z))) / &2 * cos(Re z)`,
  GEN_TAC THEN REWRITE_TAC[ccos] THEN
  REWRITE_TAC[RE_DIV_CX; RE_ADD; RE_CEXP; COMPLEX_MUL_LNEG;
              RE_MUL_II; IM_MUL_II; RE_NEG; IM_NEG; COS_NEG] THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN CONV_TAC REAL_RING);;

let IM_CCOS = prove
 (`!z. Im(ccos z) = (exp(--(Im z)) - exp(Im z)) / &2 * sin(Re z)`,
  GEN_TAC THEN REWRITE_TAC[ccos] THEN
  REWRITE_TAC[IM_DIV_CX; IM_ADD; IM_CEXP; COMPLEX_MUL_LNEG;
              RE_MUL_II; IM_MUL_II; RE_NEG; IM_NEG; SIN_NEG] THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* Some special intermediate value theorems over the reals.                  *)
(* ------------------------------------------------------------------------- *)

let IVT_INCREASING_RE = prove
 (`!f a b y.
        a <= b /\
        (!x. a <= x /\ x <= b ==> f continuous at (Cx x)) /\
        Re(f(Cx a)) <= y /\ y <= Re(f(Cx b))
        ==> ?x. a <= x /\ x <= b /\ Re(f(Cx x)) = y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(f:complex->complex) o Cx o drop`;
                 `lift a`; `lift b`; `y:real`; `1`]
        IVT_INCREASING_COMPONENT_1) THEN
  REWRITE_TAC[EXISTS_DROP; GSYM drop; LIFT_DROP; o_THM; GSYM RE_DEF] THEN
  ASM_REWRITE_TAC[IN_INTERVAL_1; GSYM CONJ_ASSOC; LIFT_DROP] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[DIMINDEX_2; ARITH] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
  ASM_SIMP_TAC[o_THM] THEN REWRITE_TAC[continuous_at; o_THM] THEN
  REWRITE_TAC[dist; GSYM CX_SUB; GSYM DROP_SUB; COMPLEX_NORM_CX] THEN
  REWRITE_TAC[GSYM ABS_DROP] THEN MESON_TAC[]);;

let IVT_DECREASING_RE = prove
 (`!f a b y.
        a <= b /\
        (!x. a <= x /\ x <= b ==> f continuous at (Cx x)) /\
        Re(f(Cx b)) <= y /\ y <= Re(f(Cx a))
        ==> ?x. a <= x /\ x <= b /\ Re(f(Cx x)) = y`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_EQ_NEG2] THEN
  REWRITE_TAC[GSYM RE_NEG] THEN MATCH_MP_TAC IVT_INCREASING_RE THEN
  ASM_SIMP_TAC[CONTINUOUS_NEG; RE_NEG; REAL_LE_NEG2]);;

let IVT_INCREASING_IM = prove
 (`!f a b y.
        a <= b /\
        (!x. a <= x /\ x <= b ==> f continuous at (Cx x)) /\
        Im(f(Cx a)) <= y /\ y <= Im(f(Cx b))
        ==> ?x. a <= x /\ x <= b /\ Im(f(Cx x)) = y`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_EQ_NEG2] THEN
  REWRITE_TAC[SYM(CONJUNCT2(SPEC_ALL RE_MUL_II))] THEN
  MATCH_MP_TAC IVT_DECREASING_RE THEN
  ASM_SIMP_TAC[CONTINUOUS_COMPLEX_MUL; ETA_AX; CONTINUOUS_CONST] THEN
  ASM_REWRITE_TAC[RE_MUL_II; REAL_LE_NEG2]);;

let IVT_DECREASING_IM = prove
 (`!f a b y.
        a <= b /\
        (!x. a <= x /\ x <= b ==> f continuous at (Cx x)) /\
        Im(f(Cx b)) <= y /\ y <= Im(f(Cx a))
        ==> ?x. a <= x /\ x <= b /\ Im(f(Cx x)) = y`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_EQ_NEG2] THEN
  REWRITE_TAC[GSYM IM_NEG] THEN MATCH_MP_TAC IVT_INCREASING_IM THEN
  ASM_SIMP_TAC[CONTINUOUS_NEG; IM_NEG; REAL_LE_NEG2]);;

(* ------------------------------------------------------------------------- *)
(* Some minimal properties of real logs help to define complex logs.         *)
(* ------------------------------------------------------------------------- *)

let log_def = new_definition
 `log y = @x. exp(x) = y`;;

let EXP_LOG = prove
 (`!x. &0 < x ==> exp(log x) = x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[log_def] THEN CONV_TAC SELECT_CONV THEN
  SUBGOAL_THEN `?y. --inv(x) <= y /\ y <= x /\ Re(cexp(Cx y)) = x`
  MP_TAC THENL [ALL_TAC; MESON_TAC[CX_EXP; RE_CX]] THEN
  MATCH_MP_TAC IVT_INCREASING_RE THEN
  SIMP_TAC[GSYM CX_EXP; RE_CX; CONTINUOUS_AT_CEXP] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < x /\ &0 < y ==> --y <= x`) THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ];
    ONCE_REWRITE_TAC[GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[REAL_EXP_NEG; REAL_INV_INV; REAL_LT_INV_EQ];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&1 + x <= y ==> x <= y`) THEN
  ASM_SIMP_TAC[REAL_EXP_LE_X; REAL_LE_INV_EQ; REAL_LT_IMP_LE]);;

let LOG_EXP = prove
 (`!x. log(exp x) = x`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_EXP_INJ] THEN
  SIMP_TAC[EXP_LOG; REAL_EXP_POS_LT]);;

let REAL_EXP_LOG = prove
 (`!x. (exp(log x) = x) <=> &0 < x`,
  MESON_TAC[EXP_LOG; REAL_EXP_POS_LT]);;

let LOG_MUL = prove
 (`!x y. &0 < x /\ &0 < y ==> (log(x * y) = log(x) + log(y))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_EXP_INJ] THEN
  ASM_SIMP_TAC[REAL_EXP_ADD; REAL_LT_MUL; EXP_LOG]);;

let LOG_INJ = prove
 (`!x y. &0 < x /\ &0 < y ==> (log(x) = log(y) <=> x = y)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_INJ] THEN
  ASM_SIMP_TAC[EXP_LOG]);;

let LOG_1 = prove
 (`log(&1) = &0`,
  ONCE_REWRITE_TAC[GSYM REAL_EXP_INJ] THEN
  REWRITE_TAC[REAL_EXP_0; REAL_EXP_LOG; REAL_LT_01]);;

let LOG_INV = prove
 (`!x. &0 < x ==> (log(inv x) = --(log x))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_EXP_INJ] THEN
  ASM_SIMP_TAC[REAL_EXP_NEG; EXP_LOG; REAL_LT_INV_EQ]);;

let LOG_DIV = prove
 (`!x y. &0 < x /\ &0 < y ==> log(x / y) = log(x) - log(y)`,
  SIMP_TAC[real_div; real_sub; LOG_MUL; LOG_INV; REAL_LT_INV_EQ]);;

let LOG_MONO_LT = prove
 (`!x y. &0 < x /\ &0 < y ==> (log(x) < log(y) <=> x < y)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_MONO_LT] THEN
  ASM_SIMP_TAC[EXP_LOG]);;

let LOG_MONO_LT_IMP = prove
 (`!x y. &0 < x /\ x < y ==> log(x) < log(y)`,
  MESON_TAC[LOG_MONO_LT; REAL_LT_TRANS]);;

let LOG_MONO_LT_REV = prove
 (`!x y. &0 < x /\ &0 < y /\ log x < log y ==> x < y`,
  MESON_TAC[LOG_MONO_LT]);;

let LOG_MONO_LE = prove
 (`!x y. &0 < x /\ &0 < y ==> (log(x) <= log(y) <=> x <= y)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_MONO_LE] THEN
  ASM_SIMP_TAC[EXP_LOG]);;

let LOG_MONO_LE_IMP = prove
 (`!x y. &0 < x /\ x <= y ==> log(x) <= log(y)`,
  MESON_TAC[LOG_MONO_LE; REAL_LT_IMP_LE; REAL_LTE_TRANS]);;

let LOG_MONO_LE_REV = prove
 (`!x y. &0 < x /\ &0 < y /\ log x <= log y ==> x <= y`,
  MESON_TAC[LOG_MONO_LE]);;

let LOG_POW = prove
 (`!n x. &0 < x ==> (log(x pow n) = &n * log(x))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_EXP_INJ] THEN
  ASM_SIMP_TAC[REAL_EXP_N; EXP_LOG; REAL_POW_LT]);;

let LOG_LE_STRONG = prove
 (`!x. &0 < &1 + x ==> log(&1 + x) <= x`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN
  ASM_SIMP_TAC[EXP_LOG; REAL_EXP_LE_X]);;

let LOG_LE = prove
 (`!x. &0 <= x ==> log(&1 + x) <= x`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN
  ASM_SIMP_TAC[EXP_LOG; REAL_ARITH `&0 <= x ==> &0 < &1 + x`; REAL_EXP_LE_X]);;

let LOG_LT_X = prove
 (`!x. &0 < x ==> log(x) < x`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LT] THEN
  ASM_SIMP_TAC[EXP_LOG] THEN MP_TAC(SPEC `x:real` REAL_EXP_LE_X) THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

let LOG_POS = prove
 (`!x. &1 <= x ==> &0 <= log(x)`,
  REWRITE_TAC[GSYM LOG_1] THEN
  SIMP_TAC[LOG_MONO_LE; ARITH_RULE `&1 <= x ==> &0 < x`; REAL_LT_01]);;

let LOG_POS_LT = prove
 (`!x. &1 < x ==> &0 < log(x)`,
  REWRITE_TAC[GSYM LOG_1] THEN
  SIMP_TAC[LOG_MONO_LT; ARITH_RULE `&1 < x ==> &0 < x`; REAL_LT_01]);;

let LOG_PRODUCT = prove
 (`!f:A->real s.
        FINITE s /\ (!x. x IN s ==> &0 < f x)
        ==> log(product s f) = sum s (\x. log(f x))`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; SUM_CLAUSES; LOG_1; FORALL_IN_INSERT; LOG_MUL;
           PRODUCT_POS_LT]);;

(* ------------------------------------------------------------------------- *)
(* Deduce periodicity just from derivative and zero values.                  *)
(* ------------------------------------------------------------------------- *)

let SIN_NEARZERO = prove
 (`?x. &0 < x /\ !y. &0 < y /\ y <= x ==> &0 < sin(y)`,
  MP_TAC(SPEC `&1 / &2` (CONJUNCT2
   (REWRITE_RULE[has_complex_derivative; HAS_DERIVATIVE_AT_ALT]
    (ISPEC `Cx(&0)` HAS_COMPLEX_DERIVATIVE_CSIN)))) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[CSIN_0; COMPLEX_SUB_RZERO; CCOS_0; COMPLEX_MUL_LZERO;
              COMPLEX_MUL_LID] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  X_GEN_TAC `y:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `Cx y`) THEN
  ASM_REWRITE_TAC[GSYM CX_SIN; COMPLEX_NORM_CX; GSYM CX_SUB] THEN
  ASM_REAL_ARITH_TAC);;

let SIN_NONTRIVIAL = prove
 (`?x. &0 < x /\ ~(sin x = &0)`,
  MESON_TAC[REAL_LE_REFL; REAL_LT_REFL; SIN_NEARZERO]);;

let COS_NONTRIVIAL = prove
 (`?x. &0 < x /\ ~(cos x = &1)`,
  MP_TAC SIN_NONTRIVIAL THEN MATCH_MP_TAC MONO_EXISTS THEN
  MP_TAC SIN_CIRCLE THEN MATCH_MP_TAC MONO_FORALL THEN
  CONV_TAC REAL_FIELD);;

let COS_DOUBLE_BOUND = prove
 (`!x. &0 <= cos x ==> &2 * (&1 - cos x) <= &1 - cos(&2 * x)`,
  REWRITE_TAC[COS_DOUBLE_COS] THEN REWRITE_TAC[REAL_ARITH
   `&2 * (&1 - a) <= &1 - (&2 * b - &1) <=> b <= &1 * a`] THEN
  SIMP_TAC[REAL_POW_2; REAL_LE_RMUL; COS_BOUNDS]);;

let COS_GOESNEGATIVE_LEMMA = prove
 (`!x. cos(x) < &1 ==> ?n. cos(&2 pow n * x) < &0`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> p) ==> p`) THEN
  REWRITE_TAC[NOT_EXISTS_THM; REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!n.  &2  pow n * (&1 - cos x) <= &1 - cos(&2 pow n * x)`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[real_pow; REAL_MUL_LID; REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * (&1 - cos(&2 pow n * x))` THEN
    ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC; REAL_LE_LMUL; REAL_POS; COS_DOUBLE_BOUND];
    MP_TAC(ISPEC `&1 / (&1 - cos(x))` REAL_ARCH_POW2) THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_SUB_LT] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `n:num`)) THEN REAL_ARITH_TAC]);;

let COS_GOESNEGATIVE = prove
 (`?x. &0 < x /\ cos(x) < &0`,
  X_CHOOSE_TAC `x:real` COS_NONTRIVIAL THEN
  MP_TAC(SPEC `x:real` COS_GOESNEGATIVE_LEMMA) THEN ANTS_TAC THENL
   [MP_TAC(SPEC `x:real` COS_BOUNDS) THEN
    ASM_REAL_ARITH_TAC;
    ASM_MESON_TAC[REAL_LT_MUL; REAL_POW_LT; REAL_ARITH `&0 < &2`]]);;

let COS_HASZERO = prove
 (`?x. &0 < x /\ cos(x) = &0`,
  X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC COS_GOESNEGATIVE THEN
  SUBGOAL_THEN `?x. &0 <= x /\ x <= z /\ Re(ccos(Cx x)) = &0` MP_TAC THENL
   [MATCH_MP_TAC IVT_DECREASING_RE THEN
    ASM_SIMP_TAC[GSYM CX_COS; RE_CX; REAL_LT_IMP_LE; COS_0; REAL_POS] THEN
    MESON_TAC[HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT;
              HAS_COMPLEX_DERIVATIVE_CCOS];
    MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[GSYM CX_COS; RE_CX] THEN
    MESON_TAC[COS_0; REAL_LE_LT; REAL_ARITH `~(&1 = &0)`]]);;

let SIN_HASZERO = prove
 (`?x. &0 < x /\ sin(x) = &0`,
  X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC COS_HASZERO THEN
  EXISTS_TAC `&2 * x` THEN ASM_SIMP_TAC[SIN_DOUBLE] THEN
  ASM_REAL_ARITH_TAC);;

let SIN_HASZERO_MINIMAL = prove
 (`?p. &0 < p /\ sin p = &0 /\ !x. &0 < x /\ x < p ==> ~(sin x = &0)`,
  X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC SIN_NEARZERO THEN
  MP_TAC(ISPECL
    [`{z | z IN IMAGE Cx {x | x >= e} /\ csin z IN {Cx(&0)}}`; `Cx(&0)`]
    DISTANCE_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[IN_ELIM_THM; GSYM CONJ_ASSOC; IMP_CONJ] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SING; real_ge; GSYM CX_COS; CX_INJ] THEN
    REWRITE_TAC[dist; GSYM CX_SUB; GSYM CX_SIN; CX_INJ; COMPLEX_NORM_CX] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    REWRITE_TAC[REAL_ARITH `abs(&0 - x) = abs x`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC;
      X_GEN_TAC `x:real` THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `x:real`))] THEN
    ASM_REAL_ARITH_TAC] THEN
  X_CHOOSE_TAC `a:real` SIN_HASZERO THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `Cx a` THEN
    ASM_REWRITE_TAC[IN_SING; IN_IMAGE; IN_ELIM_THM; GSYM CX_SIN] THEN
    ASM_MESON_TAC[REAL_ARITH `x >= w \/ x <= w`; REAL_LT_REFL]] THEN
  MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
  REWRITE_TAC[CONTINUOUS_ON_CSIN; CLOSED_SING] THEN
  SUBGOAL_THEN
   `IMAGE Cx {x | x >= e} = {z | Im(z) = &0} INTER {z | Re(z) >= e}`
   (fun th -> SIMP_TAC[th; CLOSED_INTER; CLOSED_HALFSPACE_IM_EQ;
                           CLOSED_HALFSPACE_RE_GE]) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
  REWRITE_TAC[FORALL_COMPLEX; COMPLEX_EQ; RE; IM; RE_CX; IM_CX] THEN
  MESON_TAC[]);;

let pi = new_definition
 `pi = @p. &0 < p /\ sin(p) = &0 /\ !x. &0 < x /\ x < p ==> ~(sin(x) = &0)`;;

let PI_WORKS = prove
 (`&0 < pi /\ sin(pi) = &0 /\ !x. &0 < x /\ x < pi ==> ~(sin x = &0)`,
  REWRITE_TAC[pi] THEN CONV_TAC SELECT_CONV THEN
  REWRITE_TAC[SIN_HASZERO_MINIMAL]);;

(* ------------------------------------------------------------------------- *)
(* Now more relatively easy consequences.                                    *)
(* ------------------------------------------------------------------------- *)

let PI_POS = prove
 (`&0 < pi`,
  REWRITE_TAC[PI_WORKS]);;

let PI_POS_LE = prove
 (`&0 <= pi`,
  REWRITE_TAC[REAL_LE_LT; PI_POS]);;

let PI_NZ = prove
 (`~(pi = &0)`,
  SIMP_TAC[PI_POS; REAL_LT_IMP_NZ]);;

let REAL_ABS_PI = prove
 (`abs pi = pi`,
  REWRITE_TAC[real_abs; PI_POS_LE]);;

let SIN_PI = prove
 (`sin(pi) = &0`,
  REWRITE_TAC[PI_WORKS]);;

let SIN_POS_PI = prove
 (`!x. &0 < x /\ x < pi ==> &0 < sin(x)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC SIN_NEARZERO THEN
  MP_TAC(ISPECL [`csin`; `e:real`; `x:real`; `&0`] IVT_DECREASING_RE) THEN
  ASM_SIMP_TAC[NOT_IMP; CONTINUOUS_AT_CSIN; GSYM CX_SIN; RE_CX; SIN_0] THEN
  ASM_MESON_TAC[REAL_LE_TOTAL; REAL_LET_ANTISYM; PI_WORKS; REAL_LET_TRANS;
                REAL_LTE_TRANS]);;

let COS_PI2 = prove
 (`cos(pi / &2) = &0`,
  MP_TAC(SYM(SPEC `pi / &2` SIN_DOUBLE)) THEN
  REWRITE_TAC[REAL_HALF; SIN_PI; REAL_ENTIRE; REAL_OF_NUM_EQ; ARITH] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < y ==> y = &0 \/ z = &0 ==> z = &0`) THEN
  MATCH_MP_TAC SIN_POS_PI THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let COS_PI = prove
 (`cos(pi) = -- &1`,
  ONCE_REWRITE_TAC[REAL_ARITH `pi = &2 * pi / &2`] THEN
  REWRITE_TAC[COS_DOUBLE_COS; COS_PI2] THEN REAL_ARITH_TAC);;

let SIN_PI2 = prove
 (`sin(pi / &2) = &1`,
  MP_TAC(SPEC `pi / &2` SIN_CIRCLE) THEN
  REWRITE_TAC[COS_PI2; REAL_POW_2; REAL_ADD_RID; REAL_MUL_LZERO] THEN
  REWRITE_TAC[REAL_RING `x * x = &1 <=> x = &1 \/ x = -- &1`] THEN
  MP_TAC(SPEC `pi / &2` SIN_POS_PI) THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let SIN_COS = prove
 (`!x. sin(x) = cos(pi / &2 - x)`,
  REWRITE_TAC[COS_SUB; COS_PI2; SIN_PI2] THEN REAL_ARITH_TAC);;

let COS_SIN = prove
 (`!x. cos(x) = sin(pi / &2 - x)`,
  REWRITE_TAC[SIN_SUB; COS_PI2; SIN_PI2] THEN REAL_ARITH_TAC);;

let SIN_PERIODIC_PI = prove
 (`!x. sin(x + pi) = --(sin(x))`,
  REWRITE_TAC[SIN_ADD; SIN_PI; COS_PI] THEN REAL_ARITH_TAC);;

let COS_PERIODIC_PI = prove
 (`!x. cos(x + pi) = --(cos(x))`,
  REWRITE_TAC[COS_ADD; SIN_PI; COS_PI] THEN REAL_ARITH_TAC);;

let SIN_PERIODIC = prove
 (`!x. sin(x + &2 * pi) = sin(x)`,
  REWRITE_TAC[REAL_MUL_2; REAL_ADD_ASSOC; SIN_PERIODIC_PI; REAL_NEG_NEG]);;

let COS_PERIODIC = prove
 (`!x. cos(x + &2 * pi) = cos(x)`,
  REWRITE_TAC[REAL_MUL_2; REAL_ADD_ASSOC; COS_PERIODIC_PI; REAL_NEG_NEG]);;

let SIN_NPI = prove
 (`!n. sin(&n * pi) = &0`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_MUL_LID; REAL_ADD_RDISTRIB;
                  REAL_NEG_0; SIN_PERIODIC_PI; REAL_MUL_LZERO; SIN_0]);;

let COS_NPI = prove
 (`!n. cos(&n * pi) = --(&1) pow n`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[real_pow; REAL_MUL_LZERO; COS_0; COS_PERIODIC_PI;
    REAL_MUL_LID; REAL_MUL_LNEG; GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB]);;

let COS_POS_PI2 = prove
 (`!x. &0 < x /\ x < pi / &2 ==> &0 < cos(x)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ccos`; `&0`; `x:real`; `&0`] IVT_DECREASING_RE) THEN
  ASM_SIMP_TAC[CONTINUOUS_AT_CCOS; REAL_LT_IMP_LE; GSYM CX_COS; RE_CX] THEN
  REWRITE_TAC[COS_0; REAL_POS] THEN DISCH_THEN(X_CHOOSE_TAC `y:real`) THEN
  MP_TAC(SPEC `y:real` SIN_DOUBLE) THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
  MATCH_MP_TAC(last(CONJUNCTS PI_WORKS)) THEN REPEAT(POP_ASSUM MP_TAC) THEN
  ASM_CASES_TAC `y = &0` THEN ASM_REWRITE_TAC[COS_0] THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

let SIN_POS_PI2 = prove
 (`!x. &0 < x /\ x < pi / &2 ==> &0 < sin(x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SIN_POS_PI THEN
  ASM_REAL_ARITH_TAC);;

let COS_POS_PI = prove
 (`!x. --(pi / &2) < x /\ x < pi / &2 ==> &0 < cos(x)`,
  GEN_TAC THEN MP_TAC(SPEC `abs x` COS_POS_PI2) THEN REWRITE_TAC[COS_ABS] THEN
  ASM_CASES_TAC `x = &0` THEN ASM_REWRITE_TAC[COS_0] THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

let COS_POS_PI_LE = prove
 (`!x. --(pi / &2) <= x /\ x <= pi / &2 ==> &0 <= cos(x)`,
  REWRITE_TAC[REAL_LE_LT] THEN MESON_TAC[COS_PI2; COS_NEG; COS_POS_PI]);;

let SIN_POS_PI_LE = prove
 (`!x. &0 <= x /\ x <= pi ==> &0 <= sin(x)`,
  REWRITE_TAC[REAL_LE_LT] THEN MESON_TAC[SIN_0; SIN_PI; SIN_POS_PI]);;

let SIN_PIMUL_EQ_0 = prove
 (`!n. sin(n * pi) = &0 <=> integer(n)`,
  SUBGOAL_THEN `!n. integer n ==> sin(n * pi) = &0 /\ ~(cos(n * pi) = &0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[INTEGER_CASES] THEN GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN
    ASM_SIMP_TAC[REAL_MUL_LNEG; COS_NPI; SIN_NPI;
                 SIN_NEG; COS_NEG; REAL_POW_EQ_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[] THEN
  SUBST1_TAC(last(CONJUNCTS(SPEC `n:real` FLOOR_FRAC))) THEN
  ASM_SIMP_TAC[REAL_ADD_RDISTRIB; FLOOR; SIN_ADD; REAL_MUL_LZERO] THEN
  ASM_SIMP_TAC[REAL_ADD_LID; REAL_ENTIRE; FLOOR] THEN
  DISCH_TAC THEN MP_TAC(SPEC `frac n * pi` SIN_POS_PI) THEN
  ASM_SIMP_TAC[REAL_LT_REFL; GSYM REAL_LT_RDIV_EQ; GSYM REAL_LT_LDIV_EQ;
               PI_POS; REAL_DIV_REFL; REAL_LT_IMP_NZ] THEN
  MP_TAC(SPEC `n:real` FLOOR_FRAC) THEN ASM_CASES_TAC `frac n = &0` THEN
  ASM_REWRITE_TAC[FLOOR; REAL_ADD_RID] THEN
  ASM_REAL_ARITH_TAC);;

let SIN_EQ_0 = prove
 (`!x. sin(x) = &0 <=> ?n. integer n /\ x = n * pi`,
  GEN_TAC THEN MP_TAC(SPEC `x / pi` SIN_PIMUL_EQ_0) THEN
  SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; GSYM REAL_EQ_LDIV_EQ; PI_POS] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[UNWIND_THM1]);;

let COS_EQ_0 = prove
 (`!x. cos(x) = &0 <=> ?n. integer n /\ x = (n + &1 / &2) * pi`,
  GEN_TAC THEN REWRITE_TAC[COS_SIN; SIN_EQ_0] THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `--n:real` THEN ASM_REWRITE_TAC[INTEGER_NEG] THEN
  ASM_REAL_ARITH_TAC);;

let SIN_ZERO_PI = prove
 (`!x. sin(x) = &0 <=> (?n. x = &n * pi) \/ (?n. x = --(&n * pi))`,
  REWRITE_TAC[SIN_EQ_0; INTEGER_CASES] THEN MESON_TAC[REAL_MUL_LNEG]);;

let COS_ZERO_PI = prove
 (`!x. cos(x) = &0 <=>
       (?n. x = (&n + &1 / &2) * pi) \/ (?n. x = --((&n + &1 / &2) * pi))`,
  GEN_TAC THEN REWRITE_TAC[COS_EQ_0; INTEGER_CASES; RIGHT_OR_DISTRIB] THEN
  REWRITE_TAC[EXISTS_OR_THM; LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN SIMP_TAC[UNWIND_THM2] THEN EQ_TAC THEN
  DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `n:num` SUBST1_TAC)) THENL
   [DISJ1_TAC THEN EXISTS_TAC `n:num`;
    ASM_CASES_TAC `n = 0` THENL
     [DISJ1_TAC THEN EXISTS_TAC `0`;
      DISJ2_TAC THEN EXISTS_TAC `n - 1`];
    DISJ1_TAC THEN EXISTS_TAC `n:num`;
    DISJ2_TAC THEN EXISTS_TAC `n + 1`] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM REAL_OF_NUM_ADD;
               ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
  REAL_ARITH_TAC);;

let SIN_ZERO = prove
 (`!x. (sin(x) = &0) <=> (?n. EVEN n /\ x = &n * (pi / &2)) \/
                         (?n. EVEN n /\ x = --(&n * (pi / &2)))`,
  REWRITE_TAC[SIN_ZERO_PI; EVEN_EXISTS; LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[UNWIND_THM2] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_MUL; REAL_ARITH `(&2 * x) * y / &2 = x * y`]);;

let COS_ZERO = prove
 (`!x. cos(x) = &0 <=> (?n. ~EVEN n /\ (x = &n * (pi / &2))) \/
                       (?n. ~EVEN n /\ (x = --(&n * (pi / &2))))`,
  REWRITE_TAC[COS_ZERO_PI; NOT_EVEN; ODD_EXISTS; LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[UNWIND_THM2] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_SUC;
           REAL_ARITH `(&2 * x + &1) * y / &2 = (x + &1 / &2) * y`]);;

let COS_ONE_2PI = prove
 (`!x. (cos(x) = &1) <=> (?n. x = &n * &2 * pi) \/ (?n. x = --(&n * &2 * pi))`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `sin(x)` o MATCH_MP (REAL_RING
     `c = &1 ==> !s. s pow 2 + c pow 2 = &1 ==> s = &0`)) THEN
    REWRITE_TAC[SIN_ZERO_PI; SIN_CIRCLE] THEN
    DISCH_THEN(DISJ_CASES_THEN(X_CHOOSE_THEN `n:num` SUBST_ALL_TAC)) THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[COS_NEG; COS_NPI; REAL_POW_NEG] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_POW_ONE] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[EVEN_EXISTS]) THEN
    REWRITE_TAC[OR_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    SIMP_TAC[GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC;
    FIRST_X_ASSUM (DISJ_CASES_THEN CHOOSE_TAC) THEN
    ASM_REWRITE_TAC[COS_NEG; REAL_MUL_ASSOC; REAL_OF_NUM_MUL; COS_NPI;
                    REAL_POW_NEG; EVEN_MULT; ARITH; REAL_POW_ONE]]);;

let SIN_COS_SQRT = prove
 (`!x. &0 <= sin(x) ==> (sin(x) = sqrt(&1 - (cos(x) pow 2)))`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_UNIQUE THEN
  ASM_REWRITE_TAC[SIN_CIRCLE; REAL_EQ_SUB_LADD]);;

let SIN_EQ_0_PI = prove
 (`!x. --pi < x /\ x < pi /\ sin(x) = &0 ==> x = &0`,
  GEN_TAC THEN REWRITE_TAC[SIN_EQ_0; CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC
   (X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[REAL_ARITH
   `--p < n * p /\ n * p < p <=> -- &1 * p < n * p /\ n * p < &1 * p`] THEN
  SIMP_TAC[REAL_ENTIRE; REAL_LT_IMP_NZ; REAL_LT_RMUL_EQ; PI_POS] THEN
  MP_TAC(SPEC `n:real` REAL_ABS_INTEGER_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let COS_TREBLE_COS = prove
 (`!x. cos(&3 * x) = &4 * cos(x) pow 3 - &3 * cos x`,
  GEN_TAC THEN REWRITE_TAC[COS_ADD; REAL_ARITH `&3 * x = &2 * x + x`] THEN
  REWRITE_TAC[SIN_DOUBLE; COS_DOUBLE_COS] THEN
  MP_TAC(SPEC `x:real` SIN_CIRCLE) THEN CONV_TAC REAL_RING);;

let COS_PI6 = prove
 (`cos(pi / &6) = sqrt(&3) / &2`,
  MP_TAC(ISPEC `pi / &6` COS_TREBLE_COS) THEN
  REWRITE_TAC[REAL_ARITH `&3 * x / &6 = x / &2`; COS_PI2] THEN
  REWRITE_TAC[REAL_RING `&0 = &4 * c pow 3 - &3 * c <=>
                         c = &0 \/ (&2 * c) pow 2 = &3`] THEN
  SUBGOAL_THEN `&0 < cos(pi / &6)` ASSUME_TAC THENL
   [MATCH_MP_TAC COS_POS_PI THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
    DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
     [ASM_MESON_TAC[REAL_LT_REFL]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `sqrt`) THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_LE_MUL; REAL_LT_IMP_LE; REAL_POS] THEN
    REAL_ARITH_TAC]);;

let SIN_PI6 = prove
 (`sin(pi / &6) = &1 / &2`,
  MP_TAC(SPEC `pi / &6` SIN_CIRCLE) THEN REWRITE_TAC[COS_PI6] THEN
  SIMP_TAC[REAL_POW_DIV; SQRT_POW_2; REAL_POS] THEN MATCH_MP_TAC(REAL_FIELD
   `~(s + &1 / &2 = &0) ==> s pow 2 + &3 / &2 pow 2 = &1 ==> s = &1 / &2`) THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x + &1 / &2 = &0)`) THEN
  MATCH_MP_TAC SIN_POS_PI THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let SIN_POS_PI_REV = prove
 (`!x. &0 <= x /\ x <= &2 * pi /\ &0 < sin x ==> &0 < x /\ x < pi`,
  GEN_TAC THEN ASM_CASES_TAC `x = &0` THEN
  ASM_REWRITE_TAC[SIN_0; REAL_LT_REFL] THEN
  ASM_CASES_TAC `x = pi` THEN
  ASM_REWRITE_TAC[SIN_PI; REAL_LT_REFL] THEN
  ASM_CASES_TAC `x = &2 * pi` THEN
  ASM_REWRITE_TAC[SIN_NPI; REAL_LT_REFL] THEN
  REPEAT STRIP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < sin(&2 * pi - x)` MP_TAC THENL
   [MATCH_MP_TAC SIN_POS_PI THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SIN_SUB; SIN_NPI; COS_NPI] THEN ASM_REAL_ARITH_TAC]);;

let SIN_PI3 = prove
 (`sin(pi / &3) = sqrt(&3) / &2`,
  REWRITE_TAC[SIN_DOUBLE; COS_PI6; SIN_PI6;
              REAL_ARITH `x / &3 = &2 * x / &6`] THEN
  REAL_ARITH_TAC);;

let COS_PI3 = prove
 (`cos(pi / &3) = &1 / &2`,
  REWRITE_TAC[COS_DOUBLE_COS; COS_PI6; REAL_ARITH `x / &3 = &2 * x / &6`] THEN
  SIMP_TAC[REAL_POW_DIV; SQRT_POW_2; REAL_POS; REAL_ARITH
   `&2 * s / &2 pow 2 - &1 = &1 / &2 <=> s = &3`]);;

(* ------------------------------------------------------------------------- *)
(* Prove totality of trigs.                                                  *)
(* ------------------------------------------------------------------------- *)

let SIN_TOTAL_POS = prove
 (`!y. &0 <= y /\ y <= &1
       ==> ?x. &0 <= x /\ x <= pi / &2 /\ sin(x) = y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`csin`; `&0`; `pi / &2`; `y:real`] IVT_INCREASING_RE) THEN
  ASM_REWRITE_TAC[GSYM CX_SIN; RE_CX; SIN_0; SIN_PI2] THEN
  SIMP_TAC[CONTINUOUS_AT_CSIN; PI_POS; REAL_ARITH `&0 < x ==> &0 <= x / &2`]);;

let SINCOS_TOTAL_PI2 = prove
 (`!x y. &0 <= x /\ &0 <= y /\ x pow 2 + y pow 2 = &1
         ==> ?t. &0 <= t /\ t <= pi / &2 /\ x = cos t /\ y = sin t`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `y:real` SIN_TOTAL_POS) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x pow 2 + y pow 2 = &1
      ==> (&1 < y ==> &1 pow 2 < y pow 2) /\ &0 <= x * x
          ==> y <= &1`)) THEN
    SIMP_TAC[REAL_LE_SQUARE; REAL_POW_LT2; REAL_POS; ARITH];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `x = cos t \/ x = --(cos t)` MP_TAC THENL
     [MP_TAC(SPEC `t:real` SIN_CIRCLE);
      MP_TAC(SPEC `t:real` COS_POS_PI_LE)] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD]);;

let SINCOS_TOTAL_PI = prove
 (`!x y. &0 <= y /\ x pow 2 + y pow 2 = &1
         ==> ?t. &0 <= t /\ t <= pi /\ x = cos t /\ y = sin t`,
  REPEAT STRIP_TAC THEN DISJ_CASES_TAC(REAL_ARITH `&0 <= x \/ &0 <= --x`) THENL
   [MP_TAC(SPECL [`x:real`; `y:real`] SINCOS_TOTAL_PI2);
    MP_TAC(SPECL [`--x:real`; `y:real`] SINCOS_TOTAL_PI2)] THEN
  ASM_REWRITE_TAC[REAL_POW_NEG; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `t:real`; EXISTS_TAC `pi - t`] THEN
  ASM_REWRITE_TAC[SIN_SUB; COS_SUB; SIN_PI; COS_PI] THEN
  ASM_REAL_ARITH_TAC);;

let SINCOS_TOTAL_2PI = prove
 (`!x y. x pow 2 + y pow 2 = &1
         ==> ?t. &0 <= t /\ t < &2 * pi /\ x = cos t /\ y = sin t`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x = &1 /\ y = &0` THENL
   [EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[SIN_0; COS_0] THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISJ_CASES_TAC(REAL_ARITH `&0 <= y \/ &0 <= --y`) THENL
   [MP_TAC(SPECL [`x:real`; `y:real`] SINCOS_TOTAL_PI);
    MP_TAC(SPECL [`x:real`; `--y:real`] SINCOS_TOTAL_PI)] THEN
  ASM_REWRITE_TAC[REAL_POW_NEG; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `t:real`; EXISTS_TAC `&2 * pi - t`] THEN
  ASM_REWRITE_TAC[SIN_SUB; COS_SUB; SIN_NPI; COS_NPI] THENL
   [MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN ASM_CASES_TAC `t = &0` THEN
  ASM_REWRITE_TAC[SIN_0; COS_0] THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

let CIRCLE_SINCOS = prove
 (`!x y. x pow 2 + y pow 2 = &1 ==> ?t. x = cos(t) /\ y = sin(t)`,
  MESON_TAC[SINCOS_TOTAL_2PI]);;

(* ------------------------------------------------------------------------- *)
(* Polar representation.                                                     *)
(* ------------------------------------------------------------------------- *)

let CX_PI_NZ = prove
 (`~(Cx pi = Cx(&0))`,
  SIMP_TAC[CX_INJ; REAL_LT_IMP_NZ; PI_POS]);;

let COMPLEX_UNIMODULAR_POLAR = prove
 (`!z. (norm z = &1) ==> ?x. z = complex(cos(x),sin(x))`,
  GEN_TAC THEN
  DISCH_THEN(MP_TAC o C AP_THM `2` o AP_TERM `(pow):real->num->real`) THEN
  REWRITE_TAC[complex_norm] THEN
  SIMP_TAC[REAL_POW_2; REWRITE_RULE[REAL_POW_2] SQRT_POW_2;
           REAL_LE_SQUARE; REAL_LE_ADD] THEN
  REWRITE_TAC[GSYM REAL_POW_2; REAL_MUL_LID] THEN
  DISCH_THEN(X_CHOOSE_TAC `t:real` o MATCH_MP CIRCLE_SINCOS) THEN
  EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[COMPLEX_EQ; RE; IM]);;

let SIN_INTEGER_2PI = prove
 (`!n. integer n ==> sin((&2 * pi) * n) = &0`,
  REWRITE_TAC[SIN_EQ_0; REAL_ARITH `(&2 * pi) * n = (&2 * n) * pi`] THEN
  MESON_TAC[INTEGER_CLOSED]);;

let SIN_INTEGER_PI = prove
 (`!n. integer n ==> sin (n * pi) = &0`,
  REWRITE_TAC[INTEGER_CASES] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_MUL_LNEG; SIN_NPI; SIN_NEG; REAL_NEG_0]);;

let COS_INTEGER_2PI = prove
 (`!n. integer n ==> cos((&2 * pi) * n) = &1`,
  REWRITE_TAC[INTEGER_CASES; REAL_ARITH `(&2 * pi) * n = (&2 * n) * pi`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RNEG; REAL_OF_NUM_MUL] THEN
  SIMP_TAC[COS_NEG; COS_NPI; REAL_POW_NEG; REAL_MUL_LNEG;
           ARITH; EVEN_MULT; REAL_POW_ONE]);;

let SINCOS_PRINCIPAL_VALUE = prove
 (`!x. ?y. (--pi < y /\ y <= pi) /\ (sin(y) = sin(x) /\ cos(y) = cos(x))`,
  GEN_TAC THEN EXISTS_TAC `pi - (&2 * pi) * frac((pi - x) / (&2 * pi))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[REAL_ARITH `--p < p - x <=> x < (&2 * p) * &1`;
             REAL_ARITH `p - x <= p <=> (&2 * p) * &0 <= x`;
             REAL_LT_LMUL_EQ; REAL_LE_LMUL_EQ; REAL_LT_MUL;
             PI_POS; REAL_OF_NUM_LT; ARITH; FLOOR_FRAC];
   REWRITE_TAC[FRAC_FLOOR; REAL_SUB_LDISTRIB] THEN
   SIMP_TAC[REAL_DIV_LMUL; REAL_ENTIRE; REAL_OF_NUM_EQ; ARITH; REAL_LT_IMP_NZ;
    PI_POS; REAL_ARITH `a - (a - b - c):real = b + c`; SIN_ADD; COS_ADD] THEN
   SIMP_TAC[FLOOR_FRAC; SIN_INTEGER_2PI; COS_INTEGER_2PI] THEN
   CONV_TAC REAL_RING]);;

let CEXP_COMPLEX = prove
 (`!r t. cexp(complex(r,t)) = Cx(exp r) * complex(cos t,sin t)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [COMPLEX_EXPAND] THEN
  REWRITE_TAC[RE; IM; CEXP_ADD; CEXP_EULER; CX_EXP] THEN
  REWRITE_TAC[COMPLEX_TRAD; CX_SIN; CX_COS]);;

let NORM_COSSIN = prove
 (`!t. norm(complex(cos t,sin t)) = &1`,
  REWRITE_TAC[complex_norm; RE; IM] THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[SIN_CIRCLE; SQRT_1]);;

let NORM_CEXP = prove
 (`!z. norm(cexp z) = exp(Re z)`,
  REWRITE_TAC[FORALL_COMPLEX; CEXP_COMPLEX; COMPLEX_NORM_MUL] THEN
  REWRITE_TAC[NORM_COSSIN; RE; COMPLEX_NORM_CX] THEN
  MP_TAC REAL_EXP_POS_LT THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC);;

let NORM_CEXP_II = prove
 (`!t. norm (cexp (ii * Cx t)) = &1`,
  REWRITE_TAC [NORM_CEXP; RE_MUL_II; IM_CX; REAL_NEG_0; REAL_EXP_0]);;

let NORM_CEXP_IMAGINARY = prove
 (`!z. norm(cexp z) = &1 ==> Re(z) = &0`,
  REWRITE_TAC[NORM_CEXP; REAL_EXP_EQ_1]);;

let CEXP_EQ_1 = prove
 (`!z. cexp z = Cx(&1) <=> Re(z) = &0 /\ ?n. integer n /\ Im(z) = &2 * n * pi`,
  REWRITE_TAC[FORALL_COMPLEX; CEXP_COMPLEX; RE; IM] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN EQ_TAC THENL
   [DISCH_TAC THEN FIRST_ASSUM(MP_TAC o AP_TERM `norm:complex->real`) THEN
    SIMP_TAC[COMPLEX_NORM_MUL; CX_EXP; NORM_CEXP; RE_CX; COMPLEX_NORM_CX] THEN
    REWRITE_TAC[NORM_COSSIN; REAL_ABS_NUM; REAL_ABS_EXP; REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_EXP_EQ_1] THEN DISCH_THEN SUBST_ALL_TAC THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[REAL_EXP_0; COMPLEX_MUL_LID] THEN
    REWRITE_TAC[COMPLEX_EQ; RE; IM; RE_CX; IM_CX] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SIN_EQ_0]) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:real`
     (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
    EXISTS_TAC `m / &2` THEN CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    ONCE_REWRITE_TAC[GSYM INTEGER_ABS] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE LAND_CONV [GSYM COS_ABS]) THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_NUM] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [integer]) THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST_ALL_TAC) THEN
    SIMP_TAC[real_abs; PI_POS; REAL_LT_IMP_LE; COS_NPI] THEN
    REWRITE_TAC[REAL_POW_NEG; REAL_POW_ONE] THEN
    COND_CASES_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[EVEN_EXISTS]) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; REAL_ARITH `(&2 * x) / &2 = x`] THEN
    REWRITE_TAC[INTEGER_CLOSED];
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (X_CHOOSE_TAC `n:real`)) THEN
    ASM_SIMP_TAC[REAL_EXP_0; COMPLEX_MUL_LID] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `&2 * x * y = (&2 * y) * x`] THEN
    ASM_SIMP_TAC[SIN_INTEGER_2PI; COS_INTEGER_2PI] THEN
    SIMPLE_COMPLEX_ARITH_TAC]);;

let CEXP_EQ = prove
 (`!w z. cexp w = cexp z <=> ?n. integer n /\ w = z + Cx(&2 * n * pi) * ii`,
  SIMP_TAC[CEXP_NZ; COMPLEX_FIELD
   `~(z = Cx(&0)) ==> (w = z <=> w / z = Cx(&1))`] THEN
  REWRITE_TAC[GSYM CEXP_SUB; CEXP_EQ_1; RE_SUB; IM_SUB; REAL_SUB_0] THEN
  SIMP_TAC[COMPLEX_EQ; RE_ADD; IM_ADD; RE_MUL_II; IM_MUL_II; RE_CX; IM_CX] THEN
  REWRITE_TAC[REAL_NEG_0; REAL_ADD_RID; REAL_EQ_SUB_RADD] THEN
  MESON_TAC[REAL_ADD_SYM]);;

let COMPLEX_EQ_CEXP = prove
 (`!w z. abs(Im w - Im z) < &2 * pi /\ cexp w = cexp z ==> w = z`,
  SIMP_TAC[CEXP_NZ; GSYM CEXP_SUB; CEXP_EQ_1; COMPLEX_FIELD
   `~(a = Cx(&0)) /\ ~(b = Cx(&0)) ==> (a = b <=> a / b = Cx(&1))`] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `abs(Im w - Im z) < &2 * pi` THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[GSYM IM_SUB; REAL_ABS_MUL; REAL_ABS_PI; REAL_ABS_NUM] THEN
  SIMP_TAC[REAL_MUL_ASSOC; REAL_LT_RMUL_EQ; PI_POS] THEN
  MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> ~(&2 * x < &2)`) THEN
  MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~(w:complex = z)` THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM COMPLEX_SUB_0] THEN
  ASM_REWRITE_TAC[COMPLEX_EQ; RE_CX; IM_CX; REAL_MUL_LZERO; REAL_MUL_RZERO]);;

let CEXP_INTEGER_2PI = prove
 (`!n. integer n ==> cexp(Cx(&2 * n * pi) * ii) = Cx(&1)`,
  REWRITE_TAC[CEXP_EQ_1; IM_MUL_II; RE_MUL_II; RE_CX; IM_CX] THEN
  REWRITE_TAC[REAL_NEG_0] THEN MESON_TAC[]);;

let SIN_COS_EQ = prove
 (`!x y. sin y = sin x /\ cos y = cos x <=>
         ?n. integer n /\ y = x + &2 * n * pi`,
  REPEAT GEN_TAC THEN MP_TAC(ISPECL [`ii * Cx y`; `ii * Cx x`] CEXP_EQ) THEN
  REWRITE_TAC[CEXP_EULER; GSYM CX_SIN; GSYM CX_COS] THEN
  REWRITE_TAC[COMPLEX_RING `ii * y = ii * x + z * ii <=> y = x + z`] THEN
  REWRITE_TAC[GSYM CX_ADD; CX_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[COMPLEX_EQ; RE_ADD; IM_ADD; RE_MUL_II; IM_MUL_II; RE_CX; IM_CX;
              REAL_NEG_0; REAL_ADD_LID; REAL_ADD_RID] THEN
  MESON_TAC[]);;

let SIN_COS_INJ = prove
 (`!x y. sin x = sin y /\ cos x = cos y /\ abs(x - y) < &2 * pi ==> x = y`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM CX_INJ] THEN
  MATCH_MP_TAC(COMPLEX_RING `ii * x = ii * y ==> x = y`) THEN
  MATCH_MP_TAC COMPLEX_EQ_CEXP THEN
  ASM_REWRITE_TAC[CEXP_EULER; GSYM CX_SIN; GSYM CX_COS] THEN
  ASM_REWRITE_TAC[IM_MUL_II; RE_CX]);;

let CEXP_II_NE_1 = prove
 (`!x. &0 < x /\ x < &2 * pi ==> ~(cexp(ii * Cx x) = Cx(&1))`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[CEXP_EQ_1] THEN
  REWRITE_TAC[RE_MUL_II; IM_CX; IM_MUL_II; IM_CX; REAL_NEG_0; RE_CX] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real`
   (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  UNDISCH_TAC `&0 < &2 * n * pi` THEN ASM_CASES_TAC `n = &0` THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LT_REFL] THEN
  MP_TAC(ISPEC `n:real` REAL_ABS_INTEGER_LEMMA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
   `&2 * n * pi < &2 * pi ==> &0 < (&1 - n) * &2 * pi`)) THEN
  ASM_SIMP_TAC[REAL_LT_MUL_EQ; PI_POS; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
  ASM_REAL_ARITH_TAC);;

let CSIN_EQ_0 = prove
 (`!z. csin z = Cx(&0) <=> ?n. integer n /\ z = Cx(n * pi)`,
  GEN_TAC THEN REWRITE_TAC[csin; COMPLEX_MUL_LNEG; CEXP_NEG] THEN
  SIMP_TAC[CEXP_NZ; COMPLEX_FIELD `~(z = Cx(&0))
        ==> ((z - inv z) / (Cx(&2) * ii) = Cx(&0) <=> z pow 2 = Cx(&1))`] THEN
  REWRITE_TAC[GSYM CEXP_N; CEXP_EQ_1] THEN
  REWRITE_TAC[RE_MUL_CX; IM_MUL_CX; RE_MUL_II; IM_MUL_II] THEN
  REWRITE_TAC[COMPLEX_EQ; IM_CX; RE_CX; RIGHT_AND_EXISTS_THM] THEN
  EQ_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[] THEN REAL_ARITH_TAC);;

let CCOS_EQ_0 = prove
 (`!z. ccos z = Cx(&0) <=> ?n. integer n /\ z = Cx((n + &1 / &2) * pi)`,
  GEN_TAC THEN MP_TAC(SPEC `z - Cx(pi / &2)` CSIN_EQ_0) THEN
  REWRITE_TAC[CSIN_SUB; GSYM CX_SIN; GSYM CX_COS; SIN_PI2; COS_PI2] THEN
  SIMP_TAC[COMPLEX_RING `s * Cx(&0) - c * Cx(&1) = Cx(&0) <=> c = Cx(&0)`] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB; COMPLEX_EQ_SUB_RADD; CX_ADD] THEN
  REWRITE_TAC[REAL_ARITH `&1 / &2 * x = x / &2`]);;

let CCOS_EQ_1 = prove
 (`!z. ccos z = Cx(&1) <=> ?n. integer n /\ z = Cx(&2 * n * pi)`,
  GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV)
   [COMPLEX_RING `z = Cx(&2) * z / Cx(&2)`] THEN
  REWRITE_TAC[CCOS_DOUBLE_CSIN; COMPLEX_RING
   `a - Cx(&2) * s pow 2 = a <=> s = Cx(&0)`] THEN
  REWRITE_TAC[CSIN_EQ_0; CX_MUL] THEN
  EQ_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[] THEN
  CONV_TAC COMPLEX_RING);;

let CSIN_EQ_1 = prove
 (`!z. csin z = Cx(&1) <=> ?n. integer n /\ z = Cx((&2 * n + &1 / &2) * pi)`,
  GEN_TAC THEN MP_TAC(SPEC `z - Cx(pi / &2)` CCOS_EQ_1) THEN
  REWRITE_TAC[CCOS_SUB; GSYM CX_SIN; GSYM CX_COS; SIN_PI2; COS_PI2] THEN
  SIMP_TAC[COMPLEX_RING `s * Cx(&0) + c * Cx(&1) = Cx(&1) <=> c = Cx(&1)`] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB; COMPLEX_EQ_SUB_RADD; CX_ADD] THEN
  REWRITE_TAC[REAL_MUL_ASSOC; REAL_ARITH `&1 / &2 * x = x / &2`]);;

let CSIN_EQ_MINUS1 = prove
 (`!z. csin z = --Cx(&1) <=>
       ?n. integer n /\ z = Cx((&2 * n + &3 / &2) * pi)`,
  GEN_TAC THEN REWRITE_TAC[COMPLEX_RING `z:complex = --w <=> --z = w`] THEN
  REWRITE_TAC[GSYM CSIN_NEG; CSIN_EQ_1] THEN
  REWRITE_TAC[COMPLEX_RING `--z:complex = w <=> z = --w`] THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[GSYM CX_NEG; CX_INJ] THEN
  EXISTS_TAC `--(n + &1)` THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC);;

let CCOS_EQ_MINUS1 = prove
 (`!z. ccos z = --Cx(&1) <=>
       ?n. integer n /\ z = Cx((&2 * n + &1) * pi)`,
  GEN_TAC THEN MP_TAC(SPEC `z - Cx(pi / &2)` CSIN_EQ_1) THEN
  REWRITE_TAC[CSIN_SUB; GSYM CX_SIN; GSYM CX_COS; SIN_PI2; COS_PI2] THEN
  SIMP_TAC[COMPLEX_RING
    `s * Cx(&0) - c * Cx(&1) = Cx(&1) <=> c = --Cx(&1)`] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB; COMPLEX_EQ_SUB_RADD; GSYM CX_ADD] THEN
  DISCH_TAC THEN EQ_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN
  SIMP_TAC[CX_INJ] THEN REAL_ARITH_TAC);;

let COS_EQ_1 = prove
 (`!x. cos x = &1 <=> ?n. integer n /\ x = &2 * n * pi`,
  REWRITE_TAC[GSYM CX_INJ; CX_COS; CCOS_EQ_1]);;

let SIN_EQ_1 = prove
 (`!x. sin x = &1 <=> ?n. integer n /\ x = (&2 * n + &1 / &2) * pi`,
  REWRITE_TAC[GSYM CX_INJ; CX_SIN; CSIN_EQ_1]);;

let SIN_EQ_MINUS1 = prove
 (`!x. sin x = --(&1) <=> ?n. integer n /\ x = (&2 * n + &3 / &2) * pi`,
  REWRITE_TAC[GSYM CX_INJ; CX_NEG; CX_SIN; CSIN_EQ_MINUS1]);;

let COS_EQ_MINUS1 = prove
 (`!x. cos x = --(&1) <=>
       ?n. integer n /\ x = (&2 * n + &1) * pi`,
  REWRITE_TAC[GSYM CX_INJ; CX_NEG; CX_COS; CCOS_EQ_MINUS1]);;

let DIST_CEXP_II_1 = prove
 (`!z. norm(cexp(ii * Cx t) - Cx(&1)) = &2 * abs(sin(t / &2))`,
  GEN_TAC THEN REWRITE_TAC[NORM_EQ_SQUARE] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; REWRITE_TAC[GSYM NORM_POW_2]] THEN
  REWRITE_TAC[CEXP_EULER; COMPLEX_SQNORM; GSYM CX_COS; GSYM CX_SIN] THEN
  REWRITE_TAC[IM_ADD; RE_ADD; IM_SUB; RE_SUB; IM_MUL_II; RE_MUL_II] THEN
  REWRITE_TAC[RE_CX; IM_CX; REAL_POW2_ABS; REAL_POW_MUL] THEN
  MP_TAC(ISPEC `t / &2` COS_DOUBLE_SIN) THEN
  REWRITE_TAC[REAL_ARITH `&2 * t / &2 = t`] THEN
  MP_TAC(SPEC `t:real` SIN_CIRCLE) THEN CONV_TAC REAL_RING);;

let CX_SINH = prove
 (`Cx((exp x - inv(exp x)) / &2) = --ii * csin(ii * Cx x)`,
  REWRITE_TAC[csin; COMPLEX_RING `--ii * ii * z = z /\ ii * ii * z = --z`] THEN
  REWRITE_TAC[CEXP_NEG; GSYM CX_EXP; GSYM CX_INV; CX_SUB; CX_DIV] THEN
  CONV_TAC COMPLEX_FIELD);;

let CX_COSH = prove
 (`Cx((exp x + inv(exp x)) / &2) = ccos(ii * Cx x)`,
  REWRITE_TAC[ccos; COMPLEX_RING `--ii * ii * z = z /\ ii * ii * z = --z`] THEN
  REWRITE_TAC[CEXP_NEG; GSYM CX_EXP; GSYM CX_INV; CX_ADD; CX_DIV] THEN
  CONV_TAC COMPLEX_FIELD);;

let NORM_CCOS_POW_2 = prove
 (`!z. norm(ccos z) pow 2 =
       cos(Re z) pow 2 + (exp(Im z) - inv(exp(Im z))) pow 2 / &4`,
  REWRITE_TAC[FORALL_COMPLEX; RE; IM] THEN
  REWRITE_TAC[COMPLEX_TRAD; CCOS_ADD; COMPLEX_SQNORM] THEN
  SIMP_TAC[RE_SUB; IM_SUB; GSYM CX_COS; GSYM CX_SIN; IM_MUL_CX; RE_MUL_CX] THEN
  REWRITE_TAC[ccos; csin; CEXP_NEG; COMPLEX_FIELD
   `--ii * ii * z = z /\ ii * ii * z = --z /\
    z / (Cx(&2) * ii) = --(ii * z / Cx(&2))`] THEN
  REWRITE_TAC[RE_ADD; RE_SUB; IM_ADD; IM_SUB; RE_MUL_II; IM_MUL_II;
              RE_DIV_CX; IM_DIV_CX; RE_NEG; IM_NEG] THEN
  REWRITE_TAC[GSYM CX_EXP; GSYM CX_INV; IM_CX; RE_CX] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN
  MP_TAC(SPEC `x:real` SIN_CIRCLE) THEN MP_TAC(SPEC `y:real` REAL_EXP_NZ) THEN
  CONV_TAC REAL_FIELD);;

let NORM_CSIN_POW_2 = prove
 (`!z. norm(csin z) pow 2 =
       (exp(&2 * Im z) + inv(exp(&2 * Im z)) - &2 * cos(&2 * Re z)) / &4`,
  REWRITE_TAC[FORALL_COMPLEX; RE; IM] THEN
  REWRITE_TAC[COMPLEX_TRAD; CSIN_ADD; COMPLEX_SQNORM] THEN
  SIMP_TAC[RE_ADD; IM_ADD; GSYM CX_SIN; GSYM CX_SIN; IM_MUL_CX; RE_MUL_CX;
           GSYM CX_COS] THEN
  REWRITE_TAC[ccos; csin; CEXP_NEG; COMPLEX_FIELD
   `--ii * ii * z = z /\ ii * ii * z = --z /\
    z / (Cx(&2) * ii) = --(ii * z / Cx(&2))`] THEN
  REWRITE_TAC[RE_ADD; RE_SUB; IM_ADD; IM_SUB; RE_MUL_II; IM_MUL_II;
              RE_DIV_CX; IM_DIV_CX; RE_NEG; IM_NEG] THEN
  REWRITE_TAC[GSYM CX_EXP; GSYM CX_INV; IM_CX; RE_CX] THEN
  REWRITE_TAC[REAL_EXP_N; COS_DOUBLE] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN
  MP_TAC(SPEC `x:real` SIN_CIRCLE) THEN MP_TAC(SPEC `y:real` REAL_EXP_NZ) THEN
  CONV_TAC REAL_FIELD);;

let CSIN_EQ = prove
 (`!w z. csin w = csin z <=>
         ?n. integer n /\
             (w = z + Cx(&2 * n * pi) \/ w = --z + Cx((&2 * n + &1) * pi))`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM COMPLEX_SUB_0] THEN
  REWRITE_TAC[COMPLEX_SUB_CSIN; COMPLEX_ENTIRE; CSIN_EQ_0; CCOS_EQ_0] THEN
  REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ; ARITH_EQ; OR_EXISTS_THM] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:real` THEN
  ASM_CASES_TAC `integer(n)` THEN
  ASM_REWRITE_TAC[COMPLEX_FIELD `a / Cx(&2) = b <=> a = Cx(&2) * b`] THEN
  REWRITE_TAC[GSYM CX_MUL; REAL_ARITH
    `&2 * (n + &1 / &2) * pi = (&2 * n + &1) * pi`] THEN
  CONV_TAC COMPLEX_RING);;

let CCOS_EQ = prove
 (`!w z. ccos(w) = ccos(z) <=>
         ?n. integer n /\
             (w = z + Cx(&2 * n * pi) \/ w = --z + Cx(&2 * n * pi))`,
  REPEAT GEN_TAC THEN CONV_TAC(LAND_CONV SYM_CONV) THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM COMPLEX_SUB_0] THEN
  REWRITE_TAC[COMPLEX_SUB_CCOS; COMPLEX_ENTIRE; CSIN_EQ_0] THEN
  REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ; ARITH_EQ; OR_EXISTS_THM] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:real` THEN
  ASM_CASES_TAC `integer(n)` THEN ASM_REWRITE_TAC[CX_MUL] THEN
  CONV_TAC COMPLEX_RING);;

let SIN_EQ = prove
 (`!x y. sin x = sin y <=>
         ?n. integer n /\
             (x = y + &2 * n * pi \/ x = --y + (&2 * n + &1) * pi)`,
  REWRITE_TAC[GSYM CX_INJ; CX_SIN; CSIN_EQ] THEN
  REWRITE_TAC[GSYM CX_ADD; GSYM CX_NEG; CX_INJ]);;

let COS_EQ = prove
 (`!x y. cos x = cos y <=>
         ?n. integer n /\
             (x = y + &2 * n * pi \/ x = --y + &2 * n * pi)`,
  REWRITE_TAC[GSYM CX_INJ; CX_COS; CCOS_EQ] THEN
  REWRITE_TAC[GSYM CX_ADD; GSYM CX_NEG; CX_INJ]);;

let NORM_CCOS_LE = prove
 (`!z. norm(ccos z) <= exp(norm z)`,
  GEN_TAC THEN REWRITE_TAC[ccos] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  REWRITE_TAC[REAL_ARITH `x / &2 <= y <=> x <= &2 * y`] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(a) + norm(b) <= d ==> norm(a + b) <= d`) THEN
  REWRITE_TAC[NORM_CEXP; COMPLEX_MUL_LNEG; RE_NEG; REAL_EXP_NEG] THEN
  REWRITE_TAC[COMPLEX_NORM_CX; RE_MUL_II; REAL_ABS_NUM] THEN
  MATCH_MP_TAC(REAL_ARITH
   `exp(&0) = &1 /\ (exp(&0) <= w \/ exp(&0) <= z) /\ (w <= u /\ z <= u)
    ==> w + z <= &2 * u`) THEN
  REWRITE_TAC[GSYM REAL_EXP_NEG; REAL_EXP_MONO_LE] THEN
  REWRITE_TAC[REAL_EXP_0] THEN
  MP_TAC(SPEC `z:complex` COMPLEX_NORM_GE_RE_IM) THEN
  REAL_ARITH_TAC);;

let NORM_CCOS_PLUS1_LE = prove
 (`!z. norm(Cx(&1) + ccos z) <= &2 * exp(norm z)`,
  GEN_TAC THEN REWRITE_TAC[ccos] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM; COMPLEX_RING
   `Cx(&1) + (z + z') / Cx(&2) = (Cx(&2) + z + z') / Cx(&2)`] THEN
  REWRITE_TAC[REAL_ARITH `x / &2 <= &2 * y <=> x <= &4 * y`] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(a) + norm(b) + norm(c) <= d ==> norm(a + b + c) <= d`) THEN
  REWRITE_TAC[NORM_CEXP; COMPLEX_MUL_LNEG; RE_NEG; REAL_EXP_NEG] THEN
  REWRITE_TAC[COMPLEX_NORM_CX; RE_MUL_II; REAL_ABS_NUM] THEN
  MATCH_MP_TAC(REAL_ARITH
   `exp(&0) = &1 /\ (exp(&0) <= w \/ exp(&0) <= z) /\ (w <= u /\ z <= u)
    ==> &2 + w + z <= &4 * u`) THEN
  REWRITE_TAC[GSYM REAL_EXP_NEG; REAL_EXP_MONO_LE] THEN
  REWRITE_TAC[REAL_EXP_0] THEN
  MP_TAC(SPEC `z:complex` COMPLEX_NORM_GE_RE_IM) THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Taylor series for complex exponential.                                    *)
(* ------------------------------------------------------------------------- *)

let TAYLOR_CEXP = prove
 (`!n z. norm(cexp z - vsum(0..n) (\k. z pow k / Cx(&(FACT k))))
         <= exp(abs(Re z)) * (norm z) pow (n + 1) / &(FACT n)`,
  REPEAT GEN_TAC THEN MP_TAC(ISPECL
   [`\k:num. cexp`; `n:num`; `segment[Cx(&0),z]`; `exp(abs(Re z))`]
        COMPLEX_TAYLOR) THEN
  REWRITE_TAC[CONVEX_SEGMENT; NORM_CEXP; REAL_EXP_MONO_LE] THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_SEGMENT] THEN REPEAT STRIP_TAC THENL
     [GEN_REWRITE_TAC(RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
      COMPLEX_DIFF_TAC THEN REWRITE_TAC[COMPLEX_MUL_LID];
      ASM_REWRITE_TAC[GSYM COMPLEX_VEC_0; VECTOR_MUL_RZERO] THEN
      REWRITE_TAC[VECTOR_ADD_LID; COMPLEX_CMUL; COMPLEX_NORM_MUL] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC(REAL_ARITH `abs x <= a ==> x <= a`) THEN
      REWRITE_TAC[RE_MUL_CX; REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REAL_ARITH_TAC];
    DISCH_THEN(MP_TAC o SPECL [`Cx(&0)`; `z:complex`]) THEN
    SIMP_TAC[ENDS_IN_SEGMENT; COMPLEX_SUB_RZERO; CEXP_0; COMPLEX_MUL_LID]]);;

(* ------------------------------------------------------------------------- *)
(* Approximation to e.                                                       *)
(* ------------------------------------------------------------------------- *)

let E_APPROX_32 = prove
 (`abs(exp(&1) - &5837465777 / &2147483648) <= inv(&2 pow 32)`,
  MP_TAC(ISPECL [`14`; `Cx(&1)`] TAYLOR_CEXP) THEN
  SIMP_TAC[RE_CX; REAL_ABS_NUM; GSYM CX_EXP; GSYM CX_DIV; GSYM CX_SUB;
           COMPLEX_POW_ONE; COMPLEX_NORM_CX] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_VSUM_CONV) THEN
  REWRITE_TAC[GSYM CX_ADD; GSYM CX_SUB; COMPLEX_NORM_CX] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Taylor series for complex sine and cosine.                                *)
(* ------------------------------------------------------------------------- *)

let TAYLOR_CSIN_RAW = prove
 (`!n z. norm(csin z -
              vsum(0..n) (\k. if ODD k
                              then --ii * (ii * z) pow k / Cx(&(FACT k))
                              else Cx(&0)))
         <= exp(abs(Im z)) * (norm z) pow (n + 1) / &(FACT n)`,
  MP_TAC TAYLOR_CEXP THEN MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
  DISCH_TAC THEN X_GEN_TAC `z:complex` THEN REWRITE_TAC[csin] THEN
  REWRITE_TAC[COMPLEX_FIELD
    `a / (Cx(&2) * ii) - b = (a - Cx(&2) * ii * b) / (Cx(&2) * ii)`] THEN
  FIRST_ASSUM(fun th ->
    MP_TAC(SPEC `ii * z` th) THEN MP_TAC(SPEC `--ii * z` th)) THEN
  REWRITE_TAC[COMPLEX_MUL_LNEG; RE_NEG; REAL_ABS_NEG; RE_MUL_II] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_MUL; COMPLEX_NORM_CX; NORM_NEG;
              COMPLEX_NORM_II; REAL_ABS_NUM; REAL_MUL_RID; REAL_MUL_LID;
              REAL_ARITH `x / &2 <= y <=> x <= &2 * y`] THEN
  MATCH_MP_TAC(NORM_ARITH
   `sp - sn = s2
    ==> norm(en - sn) <= d
        ==> norm(ep - sp) <= d ==> norm(ep - en - s2) <= &2 * d`) THEN
  SIMP_TAC[GSYM VSUM_SUB; GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[COMPLEX_POW_NEG; GSYM NOT_EVEN] THEN ASM_CASES_TAC `EVEN k` THEN
  ASM_REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_MUL_RZERO] THEN
  REWRITE_TAC[COMPLEX_RING `Cx(&2) * ii * --(ii * z) = Cx(&2) * z`] THEN
  SIMPLE_COMPLEX_ARITH_TAC);;

let TAYLOR_CSIN = prove
 (`!n z. norm(csin z -
              vsum(0..n) (\k. --Cx(&1) pow k *
                              z pow (2 * k + 1) / Cx(&(FACT(2 * k + 1)))))
         <= exp(abs(Im z)) * norm(z) pow (2 * n + 3) / &(FACT(2 * n + 2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`SUC(2 * n + 1)`; `z:complex`] TAYLOR_CSIN_RAW) THEN
  SIMP_TAC[VSUM_CLAUSES_NUMSEG; VSUM_PAIR_0; ODD_ADD; ODD_MULT; ARITH_ODD;
           LE_0; ODD; COMPLEX_ADD_LID; COMPLEX_ADD_RID] THEN
  SIMP_TAC[ARITH_RULE `SUC(2 * n + 1) = 2 * n + 2`; GSYM ADD_ASSOC; ARITH] THEN
  MATCH_MP_TAC(NORM_ARITH
   `s = t ==> norm(x - s) <= e ==> norm(x - t) <= e`) THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[COMPLEX_POW_MUL; complex_div; COMPLEX_MUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[COMPLEX_POW_ADD; GSYM COMPLEX_POW_POW] THEN
  REWRITE_TAC[COMPLEX_POW_II_2] THEN CONV_TAC COMPLEX_RING);;

let CSIN_CONVERGES = prove
 (`!z. ((\n. --Cx(&1) pow n * z pow (2 * n + 1) / Cx(&(FACT(2 * n + 1))))
        sums csin(z)) (from 0)`,
  GEN_TAC THEN REWRITE_TAC[sums; FROM_0; INTER_UNIV] THEN
  ONCE_REWRITE_TAC[LIM_NULL] THEN MATCH_MP_TAC LIM_NULL_COMPARISON THEN
  EXISTS_TAC
   `\n. exp(abs(Im z)) * norm z pow (2 * n + 3) / &(FACT(2 * n + 2))` THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  ONCE_REWRITE_TAC[NORM_SUB] THEN REWRITE_TAC[TAYLOR_CSIN] THEN
  REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC LIM_NULL_CMUL THEN
  REWRITE_TAC[ARITH_RULE `2 * n + 3 = SUC(2 * n + 2)`; real_div] THEN
  REWRITE_TAC[LIFT_CMUL; real_pow] THEN
  REWRITE_TAC[GSYM VECTOR_MUL_ASSOC] THEN
  MATCH_MP_TAC LIM_NULL_CMUL THEN
  MP_TAC(MATCH_MP SERIES_TERMS_TOZERO (SPEC `z:complex` CEXP_CONVERGES)) THEN
  GEN_REWRITE_TAC LAND_CONV [LIM_NULL_NORM] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_POW; COMPLEX_NORM_CX] THEN
  REWRITE_TAC[REAL_ABS_NUM; GSYM LIFT_CMUL; GSYM real_div] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let TAYLOR_CCOS_RAW = prove
 (`!n z. norm(ccos z -
              vsum(0..n) (\k. if EVEN k
                              then (ii * z) pow k / Cx(&(FACT k))
                              else Cx(&0)))
         <= exp(abs(Im z)) * (norm z) pow (n + 1) / &(FACT n)`,
  MP_TAC TAYLOR_CEXP THEN MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
  DISCH_TAC THEN X_GEN_TAC `z:complex` THEN REWRITE_TAC[ccos] THEN
  REWRITE_TAC[COMPLEX_FIELD
    `a / Cx(&2) - b = (a - Cx(&2) * b) / Cx(&2)`] THEN
  FIRST_ASSUM(fun th ->
    MP_TAC(SPEC `ii * z` th) THEN MP_TAC(SPEC `--ii * z` th)) THEN
  REWRITE_TAC[COMPLEX_MUL_LNEG; RE_NEG; REAL_ABS_NEG; RE_MUL_II] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_MUL; COMPLEX_NORM_CX; NORM_NEG;
              COMPLEX_NORM_II; REAL_ABS_NUM; REAL_MUL_RID; REAL_MUL_LID;
              REAL_ARITH `x / &2 <= y <=> x <= &2 * y`] THEN
  MATCH_MP_TAC(NORM_ARITH
   `sp + sn = s2
    ==> norm(en - sn) <= d
        ==> norm(ep - sp) <= d ==> norm((ep + en) - s2) <= &2 * d`) THEN
  SIMP_TAC[GSYM VSUM_ADD; GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[COMPLEX_POW_NEG; GSYM NOT_EVEN] THEN ASM_CASES_TAC `EVEN k` THEN
  ASM_REWRITE_TAC[COMPLEX_ADD_RINV; COMPLEX_MUL_RZERO] THEN
  SIMPLE_COMPLEX_ARITH_TAC);;

let TAYLOR_CCOS = prove
 (`!n z. norm(ccos z -
              vsum(0..n) (\k. --Cx(&1) pow k *
                              z pow (2 * k) / Cx(&(FACT(2 * k)))))
         <= exp(abs(Im z)) * norm(z) pow (2 * n + 2) / &(FACT(2 * n + 1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2 * n + 1`; `z:complex`] TAYLOR_CCOS_RAW) THEN
  SIMP_TAC[VSUM_PAIR_0; EVEN_ADD; EVEN_MULT; ARITH_EVEN;
           LE_0; EVEN; COMPLEX_ADD_LID; COMPLEX_ADD_RID] THEN
  SIMP_TAC[ARITH_RULE `(2 * n + 1) + 1 = 2 * n + 2`] THEN
  MATCH_MP_TAC(NORM_ARITH
   `s = t ==> norm(x - s) <= e ==> norm(x - t) <= e`) THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[COMPLEX_POW_MUL; complex_div; COMPLEX_MUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM COMPLEX_POW_POW; COMPLEX_POW_II_2]);;

let CCOS_CONVERGES = prove
 (`!z. ((\n. --Cx(&1) pow n * z pow (2 * n) / Cx(&(FACT(2 * n))))
        sums ccos(z)) (from 0)`,
  GEN_TAC THEN REWRITE_TAC[sums; FROM_0; INTER_UNIV] THEN
  ONCE_REWRITE_TAC[LIM_NULL] THEN MATCH_MP_TAC LIM_NULL_COMPARISON THEN
  EXISTS_TAC
   `\n. exp(abs(Im z)) * norm z pow (2 * n + 2) / &(FACT(2 * n + 1))` THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  ONCE_REWRITE_TAC[NORM_SUB] THEN REWRITE_TAC[TAYLOR_CCOS] THEN
  REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC LIM_NULL_CMUL THEN
  REWRITE_TAC[ARITH_RULE `2 * n + 2 = SUC(2 * n + 1)`; real_div] THEN
  REWRITE_TAC[LIFT_CMUL; real_pow] THEN
  REWRITE_TAC[GSYM VECTOR_MUL_ASSOC] THEN
  MATCH_MP_TAC LIM_NULL_CMUL THEN
  MP_TAC(MATCH_MP SERIES_TERMS_TOZERO (SPEC `z:complex` CEXP_CONVERGES)) THEN
  GEN_REWRITE_TAC LAND_CONV [LIM_NULL_NORM] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_POW; COMPLEX_NORM_CX] THEN
  REWRITE_TAC[REAL_ABS_NUM; GSYM LIFT_CMUL; GSYM real_div] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The argument of a complex number, where 0 <= arg(z) < 2 pi                *)
(* ------------------------------------------------------------------------- *)

let Arg_DEF = new_definition
 `Arg z = if z = Cx(&0) then &0
          else @t. &0 <= t /\ t < &2 * pi /\
                   z = Cx(norm(z)) * cexp(ii * Cx t)`;;

let ARG_0 = prove
 (`Arg(Cx(&0)) = &0`,
  REWRITE_TAC[Arg_DEF]);;

let ARG = prove
 (`!z. &0 <= Arg(z) /\ Arg(z) < &2 * pi /\
       z = Cx(norm z) * cexp(ii * Cx(Arg z))`,
  GEN_TAC THEN REWRITE_TAC[Arg_DEF] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[COMPLEX_NORM_0; COMPLEX_MUL_LZERO] THEN
  SIMP_TAC[REAL_LE_REFL; REAL_LT_MUL; PI_POS; REAL_ARITH `&0 < &2`] THEN
  CONV_TAC SELECT_CONV THEN
  MP_TAC(SPECL [`Re(z) / norm z`; `Im(z) / norm z`]
        SINCOS_TOTAL_2PI) THEN
  ASM_SIMP_TAC[COMPLEX_SQNORM; COMPLEX_NORM_ZERO; REAL_FIELD
    `~(z = &0) /\ x pow 2 + y pow 2 = z pow 2
      ==> (x / z) pow 2 + (y / z) pow 2 = &1`] THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  ASM_SIMP_TAC[COMPLEX_NORM_ZERO; REAL_FIELD
   `~(z = &0) ==> (x / z = y <=> x = z * y)`] THEN
  REWRITE_TAC[COMPLEX_EQ; RE_MUL_CX; IM_MUL_CX; CEXP_EULER; RE_ADD; IM_ADD;
        RE_MUL_II; IM_MUL_II; GSYM CX_SIN; GSYM CX_COS; RE_CX; IM_CX] THEN
  REAL_ARITH_TAC);;

let COMPLEX_NORM_EQ_1_CEXP = prove
 (`!z. norm z = &1 <=> (?t. z = cexp(ii * Cx t))`,
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC [NORM_CEXP; RE_MUL_II; IM_CX; REAL_NEG_0; REAL_EXP_0] THEN
  MP_TAC (SPEC `z:complex` ARG) THEN ASM_REWRITE_TAC [COMPLEX_MUL_LID] THEN
  MESON_TAC[]);;

let ARG_UNIQUE = prove
 (`!a r z. &0 < r /\ Cx r * cexp(ii * Cx a) = z /\ &0 <= a /\ a < &2 * pi
           ==> Arg z = a`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM CX_INJ] THEN
  MATCH_MP_TAC(COMPLEX_RING `ii * x = ii * y ==> x = y`) THEN
  MATCH_MP_TAC COMPLEX_EQ_CEXP THEN CONJ_TAC THENL
   [REWRITE_TAC[IM_MUL_II; RE_CX] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x < p /\ &0 <= y /\ y < p
                             ==> abs(x - y) < p`) THEN
    ASM_SIMP_TAC[ARG];
    MATCH_MP_TAC(COMPLEX_RING
     `!a b. Cx a = Cx b /\ ~(Cx b = Cx(&0)) /\
            Cx a * w = Cx b * z ==> w = z`) THEN
    MAP_EVERY EXISTS_TAC [`norm(z:complex)`; `r:real`] THEN
    ASM_REWRITE_TAC[GSYM ARG] THEN ASM_SIMP_TAC[CX_INJ; REAL_LT_IMP_NZ] THEN
    EXPAND_TAC "z" THEN
    REWRITE_TAC[NORM_CEXP_II; COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    ASM_REAL_ARITH_TAC]);;

let ARG_MUL_CX = prove
 (`!r z. &0 < r ==> Arg(Cx r * z) = Arg(z)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `z = Cx(&0)` THEN ASM_REWRITE_TAC[COMPLEX_MUL_RZERO] THEN
  MATCH_MP_TAC ARG_UNIQUE THEN EXISTS_TAC `r * norm(z:complex)` THEN
  ASM_REWRITE_TAC[CX_MUL; GSYM COMPLEX_MUL_ASSOC; GSYM ARG] THEN
  ASM_SIMP_TAC[REAL_LT_MUL; COMPLEX_NORM_NZ]);;

let ARG_DIV_CX = prove
 (`!r z. &0 < r ==> Arg(z / Cx r) = Arg(z)`,
  REWRITE_TAC[ONCE_REWRITE_RULE[COMPLEX_MUL_SYM] complex_div] THEN
  SIMP_TAC[GSYM CX_INV; ARG_MUL_CX; REAL_LT_INV_EQ]);;

let ARG_LT_NZ = prove
 (`!z. &0 < Arg z <=> ~(Arg z = &0)`,
  MP_TAC ARG THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC);;

let ARG_LE_PI = prove
 (`!z. Arg z <= pi <=> &0 <= Im z`,
  GEN_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THENL
   [ASM_REWRITE_TAC[Arg_DEF; IM_CX; REAL_LE_REFL; PI_POS_LE]; ALL_TAC] THEN
  GEN_REWRITE_TAC (funpow 3 RAND_CONV) [ARG] THEN
  ASM_SIMP_TAC[IM_MUL_CX; CEXP_EULER; REAL_LE_MUL_EQ; COMPLEX_NORM_NZ] THEN
  REWRITE_TAC[IM_ADD; GSYM CX_SIN; GSYM CX_COS; IM_CX; IM_MUL_II; RE_CX] THEN
  REWRITE_TAC[REAL_ADD_LID] THEN EQ_TAC THEN SIMP_TAC[ARG; SIN_POS_PI_LE] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < sin(&2 * pi - Arg z)` MP_TAC THENL
   [MATCH_MP_TAC SIN_POS_PI THEN MP_TAC(SPEC `z:complex` ARG) THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SIN_SUB; SIN_NPI; COS_NPI] THEN REAL_ARITH_TAC]);;

let ARG_LT_PI = prove
 (`!z. &0 < Arg z /\ Arg z < pi <=> &0 < Im z`,
  GEN_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THENL
   [ASM_REWRITE_TAC[Arg_DEF; IM_CX; REAL_LT_REFL; PI_POS_LE]; ALL_TAC] THEN
  GEN_REWRITE_TAC (funpow 3 RAND_CONV) [ARG] THEN
  ASM_SIMP_TAC[IM_MUL_CX; CEXP_EULER; REAL_LT_MUL_EQ; COMPLEX_NORM_NZ] THEN
  REWRITE_TAC[IM_ADD; GSYM CX_SIN; GSYM CX_COS; IM_CX; IM_MUL_II; RE_CX] THEN
  REWRITE_TAC[REAL_ADD_LID] THEN EQ_TAC THEN SIMP_TAC[SIN_POS_PI] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  ASM_CASES_TAC `Arg z = &0` THEN
  ASM_REWRITE_TAC[SIN_0; REAL_LT_REFL] THEN
  ASM_SIMP_TAC[ARG; REAL_ARITH `~(x = &0) ==> (&0 < x <=> &0 <= x)`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= sin(&2 * pi - Arg z)` MP_TAC THENL
   [MATCH_MP_TAC SIN_POS_PI_LE THEN MP_TAC(SPEC `z:complex` ARG) THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SIN_SUB; SIN_NPI; COS_NPI] THEN REAL_ARITH_TAC]);;

let ARG_EQ_0 = prove
 (`!z. Arg z = &0 <=> real z /\ &0 <= Re z`,
  GEN_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THENL
   [ASM_REWRITE_TAC[REAL_CX; RE_CX; Arg_DEF; REAL_LE_REFL]; ALL_TAC] THEN
  CONV_TAC(RAND_CONV(SUBS_CONV[last(CONJUNCTS(SPEC `z:complex` ARG))])) THEN
  ASM_SIMP_TAC[RE_MUL_CX; REAL_MUL_CX; REAL_LE_MUL_EQ; COMPLEX_NORM_NZ] THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_ZERO; CEXP_EULER] THEN
  REWRITE_TAC[real; RE_ADD; IM_ADD; RE_MUL_II; IM_MUL_II;
              GSYM CX_SIN; GSYM CX_COS; RE_CX; IM_CX] THEN
  REWRITE_TAC[REAL_ADD_RID; REAL_ADD_LID; REAL_NEG_0] THEN
  EQ_TAC THEN SIMP_TAC[SIN_0; COS_0; REAL_POS] THEN
  ASM_CASES_TAC `Arg z = pi` THENL
   [ASM_REWRITE_TAC[COS_PI] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `z:complex` ARG) THEN REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP
   (REAL_ARITH `&0 <= x /\ x < &2 * pi
                ==> --pi < x /\ x < pi \/ --pi < x - pi /\ x - pi < pi`)) THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SIN_EQ_0_PI] THEN
  UNDISCH_TAC `~(Arg z = pi)` THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  DISCH_TAC THEN REWRITE_TAC[REAL_ARITH `x = pi <=> x - pi = &0`] THEN
  MATCH_MP_TAC SIN_EQ_0_PI THEN ASM_REWRITE_TAC[SIN_SUB; SIN_PI] THEN
  REAL_ARITH_TAC);;

let ARG_NUM = prove
 (`!n. Arg(Cx(&n)) = &0`,
  REWRITE_TAC[ARG_EQ_0; REAL_CX; RE_CX; REAL_POS]);;

let ARG_EQ_PI = prove
 (`!z. Arg z = pi <=> real z /\ Re z < &0`,
  SIMP_TAC[ARG; PI_POS; REAL_ARITH
    `&0 < pi /\ &0 <= z
     ==> (z = pi <=> z <= pi /\ ~(z = &0) /\ ~(&0 < z /\ z < pi))`] THEN
  REWRITE_TAC[ARG_EQ_0; ARG; ARG_LT_PI; ARG_LE_PI; real] THEN
  REAL_ARITH_TAC);;

let ARG_EQ_0_PI = prove
 (`!z. Arg z = &0 \/ Arg z = pi <=> real z`,
  REWRITE_TAC[ARG_EQ_0; ARG_EQ_PI; real] THEN REAL_ARITH_TAC);;

let ARG_INV = prove
 (`!z. ~(real z /\ &0 <= Re z) ==> Arg(inv z) = &2 * pi - Arg z`,
  GEN_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THEN
  ASM_REWRITE_TAC[REAL_CX; RE_CX; REAL_LE_REFL] THEN
  REWRITE_TAC[real] THEN STRIP_TAC THEN MATCH_MP_TAC ARG_UNIQUE THEN
  EXISTS_TAC `inv(norm(z:complex))` THEN
  ASM_SIMP_TAC[COMPLEX_NORM_NZ; REAL_LT_INV_EQ] THEN
  REWRITE_TAC[CX_SUB; CX_MUL; COMPLEX_SUB_LDISTRIB; CEXP_SUB] THEN
  SUBST1_TAC(SPEC `Cx(&2) * Cx pi` CEXP_EULER) THEN
  REWRITE_TAC[GSYM CX_MUL; GSYM CX_SIN; GSYM CX_COS] THEN
  REWRITE_TAC[SIN_NPI; COS_NPI; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[complex_div; COMPLEX_MUL_LID; CX_INV; GSYM COMPLEX_INV_MUL] THEN
  REWRITE_TAC[GSYM ARG] THEN
  MP_TAC(SPEC `z:complex` ARG_EQ_0) THEN ASM_REWRITE_TAC[real] THEN
  MP_TAC(SPEC `z:complex` ARG) THEN REAL_ARITH_TAC);;

let ARG_EQ = prove
 (`!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
         ==> (Arg w = Arg z <=> ?x. &0 < x /\ w = Cx(x) * z)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC; STRIP_TAC THEN ASM_SIMP_TAC[ARG_MUL_CX]] THEN
  DISCH_TAC THEN
  MAP_EVERY (MP_TAC o CONJUNCT2 o CONJUNCT2 o C SPEC ARG)
   [`z:complex`; `w:complex`] THEN
  ASM_REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(fun th -> CONV_TAC(SUBS_CONV(CONJUNCTS th))) THEN
  EXISTS_TAC `norm(w:complex) / norm(z:complex)` THEN
  ASM_SIMP_TAC[REAL_LT_DIV; COMPLEX_NORM_NZ; CX_DIV] THEN
  REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[COMPLEX_DIV_RMUL; COMPLEX_NORM_ZERO; CX_INJ]);;

let ARG_INV_EQ_0 = prove
 (`!z. Arg(inv z) = &0 <=> Arg z = &0`,
  GEN_TAC THEN REWRITE_TAC[ARG_EQ_0; REAL_INV_EQ] THEN
  MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)`) THEN
  REWRITE_TAC[real] THEN DISCH_TAC THEN ASM_REWRITE_TAC[complex_inv; RE] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_ADD_RID] THEN
  ASM_CASES_TAC `Re z = &0` THEN ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO] THEN
  ASM_SIMP_TAC[REAL_FIELD `~(x = &0) ==> x * inv(x pow 2) = inv x`] THEN
  REWRITE_TAC[REAL_LE_INV_EQ]);;

let ARG_LE_DIV_SUM = prove
 (`!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0)) /\ Arg(w) <= Arg(z)
         ==> Arg(z) = Arg(w) + Arg(z / w)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a:real = b + c <=> c = a - b`] THEN
  MATCH_MP_TAC ARG_UNIQUE THEN EXISTS_TAC `norm(z / w)`THEN
  ASM_SIMP_TAC[ARG; REAL_ARITH
   `&0 <= a /\ a < &2 * pi /\ &0 <= b /\ b <= a ==> a - b < &2 * pi`] THEN
  ASM_REWRITE_TAC[REAL_SUB_LE] THEN
  ASM_SIMP_TAC[COMPLEX_NORM_DIV; CX_DIV] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; COMPLEX_NORM_NZ] THEN
  REWRITE_TAC[COMPLEX_SUB_LDISTRIB; CEXP_SUB; CX_SUB] THEN
  REWRITE_TAC[complex_div] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING
   `(a * b) * (c * d):complex = (a * c) * (b * d)`] THEN
  REWRITE_TAC[GSYM COMPLEX_INV_MUL] THEN ASM_SIMP_TAC[GSYM ARG]);;

let ARG_LE_DIV_SUM_EQ = prove
 (`!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
         ==> (Arg(w) <= Arg(z) <=> Arg(z) = Arg(w) + Arg(z / w))`,
  MESON_TAC[ARG_LE_DIV_SUM; REAL_LE_ADDR; ARG]);;

let REAL_SUB_ARG = prove
 (`!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
         ==> Arg w - Arg z = if Arg(z) <= Arg(w) then Arg(w / z)
                             else Arg(w / z) - &2 * pi`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [MP_TAC(ISPECL [`z:complex`; `w:complex`] ARG_LE_DIV_SUM) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL [`w:complex`; `z:complex`] ARG_LE_DIV_SUM) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[REAL_ARITH `a - (a + b):real = --b`] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM COMPLEX_INV_DIV] THEN
    MATCH_MP_TAC(REAL_ARITH `x = &2 * pi - y ==> --x = y - &2 * pi`) THEN
    MATCH_MP_TAC ARG_INV THEN REWRITE_TAC[GSYM ARG_EQ_0] THEN
    ONCE_REWRITE_TAC[GSYM COMPLEX_INV_DIV] THEN
    REWRITE_TAC[ARG_INV_EQ_0] THEN
    MP_TAC(ISPECL [`w:complex`; `z:complex`] ARG_LE_DIV_SUM) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let REAL_ADD_ARG = prove
 (`!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
         ==> Arg(w) + Arg(z) =
             if Arg w + Arg z < &2 * pi
             then Arg(w * z)
             else Arg(w * z) + &2 * pi`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`w * z:complex`; `z:complex`] REAL_SUB_ARG) THEN
  MP_TAC(SPECL [`z:complex`; `w * z:complex`] ARG_LE_DIV_SUM_EQ) THEN
  ASM_SIMP_TAC[COMPLEX_ENTIRE; COMPLEX_FIELD
   `~(z = Cx(&0)) ==> (w * z) / z = w`] THEN
  ASM_CASES_TAC `Arg (w * z) = Arg z + Arg w` THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[ARG; REAL_ADD_SYM];
    SIMP_TAC[REAL_ARITH `wz - z = w - &2 * pi <=> w + z = wz + &2 * pi`] THEN
    REWRITE_TAC[REAL_ARITH `w + p < p <=> ~(&0 <= w)`; ARG]]);;

let ARG_MUL = prove
 (`!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
         ==> Arg(w * z) = if Arg w + Arg z < &2 * pi
                          then Arg w + Arg z
                          else (Arg w + Arg z) - &2 * pi`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_ADD_ARG) THEN
  REAL_ARITH_TAC);;

let ARG_CNJ = prove
 (`!z. Arg(cnj z) = if real z /\ &0 <= Re z then Arg z else &2 * pi - Arg z`,
  GEN_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THEN
  ASM_REWRITE_TAC[CNJ_CX; ARG_0; REAL_CX; RE_CX; REAL_LE_REFL] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_IMP_CNJ] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `Arg(inv z)` THEN CONJ_TAC THENL
   [REWRITE_TAC[COMPLEX_INV_CNJ] THEN
    ASM_SIMP_TAC[GSYM CX_POW; ARG_DIV_CX; REAL_POW_LT; COMPLEX_NORM_NZ];
    ASM_SIMP_TAC[ARG_INV]]);;

let ARG_REAL = prove
 (`!z. real z ==> Arg z = if &0 <= Re z then &0 else pi`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[ARG_EQ_PI; ARG_EQ_0] THEN ASM_REAL_ARITH_TAC);;

let ARG_CEXP = prove
 (`!z. &0 <= Im z /\ Im z < &2 * pi ==> Arg(cexp(z)) = Im z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ARG_UNIQUE THEN
  EXISTS_TAC `exp(Re z)` THEN
  ASM_REWRITE_TAC[CX_EXP; GSYM CEXP_ADD; REAL_EXP_POS_LT] THEN
  REWRITE_TAC[GSYM COMPLEX_EXPAND]);;

(* ------------------------------------------------------------------------- *)
(* Properties of 2-D rotations, and their interpretation using cexp.         *)
(* ------------------------------------------------------------------------- *)

let rotate2d = new_definition
 `(rotate2d:real->real^2->real^2) t x =
        vector[x$1 * cos(t) - x$2 * sin(t);
               x$1 * sin(t) + x$2 * cos(t)]`;;

let LINEAR_ROTATE2D = prove
 (`!t. linear(rotate2d t)`,
  SIMP_TAC[linear; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2;
           VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; rotate2d] THEN
  REAL_ARITH_TAC);;

let ROTATE2D_ADD_VECTORS = prove
 (`!t w z. rotate2d t (w + z) = rotate2d t w + rotate2d t z`,
  SIMP_TAC[LINEAR_ADD; LINEAR_ROTATE2D]);;

let ROTATE2D_SUB = prove
 (`!t w z. rotate2d t (w - z) = rotate2d t w - rotate2d t z`,
  SIMP_TAC[LINEAR_SUB; LINEAR_ROTATE2D]);;

let NORM_ROTATE2D = prove
 (`!t z. norm(rotate2d t z) = norm z`,
  REWRITE_TAC[NORM_EQ; rotate2d; DIMINDEX_2; DOT_2; VECTOR_2] THEN
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `t:real` SIN_CIRCLE) THEN
  CONV_TAC REAL_RING);;

let ROTATE2D_0 = prove
 (`!t. rotate2d t (Cx(&0)) = Cx(&0)`,
  REWRITE_TAC[GSYM COMPLEX_NORM_ZERO; NORM_ROTATE2D; COMPLEX_NORM_0]);;

let ROTATE2D_EQ_0 = prove
 (`!t z. rotate2d t z = Cx(&0) <=> z = Cx(&0)`,
  REWRITE_TAC[GSYM COMPLEX_NORM_ZERO; NORM_ROTATE2D]);;

let ROTATE2D_ZERO = prove
 (`!z. rotate2d (&0) z = z`,
  REWRITE_TAC[rotate2d; SIN_0; COS_0] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
  REAL_ARITH_TAC);;

let ORTHOGONAL_TRANSFORMATION_ROTATE2D = prove
 (`!t. orthogonal_transformation(rotate2d t)`,
  REWRITE_TAC[ORTHOGONAL_TRANSFORMATION; LINEAR_ROTATE2D; NORM_ROTATE2D]);;

let ROTATE2D_POLAR = prove
 (`!r t s. rotate2d t (vector[r * cos(s); r * sin(s)]) =
                        vector[r * cos(t + s); r * sin(t + s)]`,
  SIMP_TAC[rotate2d; DIMINDEX_2; VECTOR_2; CART_EQ; FORALL_2] THEN
  REWRITE_TAC[SIN_ADD; COS_ADD] THEN REAL_ARITH_TAC);;

let MATRIX_ROTATE2D = prove
 (`!t. matrix(rotate2d t) = vector[vector[cos t;--(sin t)];
                                   vector[sin t; cos t]]`,
  SIMP_TAC[MATRIX_EQ; MATRIX_WORKS; LINEAR_ROTATE2D] THEN
  SIMP_TAC[matrix_vector_mul; rotate2d; CART_EQ; DIMINDEX_2; FORALL_2;
           LAMBDA_BETA; VECTOR_2; ARITH; SUM_2] THEN
  REAL_ARITH_TAC);;

let DET_MATRIX_ROTATE2D = prove
 (`!t. det(matrix(rotate2d t)) = &1`,
  GEN_TAC THEN REWRITE_TAC[MATRIX_ROTATE2D; DET_2; VECTOR_2] THEN
  MP_TAC(SPEC `t:real` SIN_CIRCLE) THEN REAL_ARITH_TAC);;

let ROTATION_ROTATE2D = prove
 (`!f. orthogonal_transformation f /\ det(matrix f) = &1
       ==> ?t. &0 <= t /\ t < &2 * pi /\ f = rotate2d t`,
  REWRITE_TAC[ORTHOGONAL_TRANSFORMATION_MATRIX] THEN
  REWRITE_TAC[matrix_mul; orthogonal_matrix; transp] THEN
  SIMP_TAC[DIMINDEX_2; SUM_2; FORALL_2; LAMBDA_BETA; ARITH;
           CART_EQ; mat; DET_2] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(matrix f)$1$1 pow 2 + (matrix f)$2$1 pow 2 = &1 /\
                (matrix f)$1$2 = --((matrix f)$2$1) /\
                (matrix f:real^2^2)$2$2 = (matrix f)$1$1`
  STRIP_ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o SYM)) THEN CONV_TAC REAL_RING;
    FIRST_X_ASSUM(MP_TAC o MATCH_MP SINCOS_TOTAL_2PI) THEN
    MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LINEAR_EQ_MATRIX THEN
    ASM_REWRITE_TAC[LINEAR_ROTATE2D; MATRIX_ROTATE2D] THEN
    ASM_SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2]]);;

let ROTATE2D_ADD = prove
 (`!s t x. rotate2d (s + t) x = rotate2d s (rotate2d t x)`,
  SIMP_TAC[CART_EQ; rotate2d; LAMBDA_BETA; DIMINDEX_2; ARITH;
           FORALL_2; VECTOR_2] THEN
  REWRITE_TAC[SIN_ADD; COS_ADD] THEN REAL_ARITH_TAC);;

let ROTATE2D_COMPLEX = prove
 (`!t z. rotate2d t z = cexp(ii * Cx t) * z`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [complex_mul] THEN
  REWRITE_TAC[CEXP_EULER; rotate2d; GSYM CX_SIN; GSYM CX_COS;
              RE_ADD; IM_ADD; RE_MUL_II; IM_MUL_II; IM_CX; RE_CX] THEN
  REWRITE_TAC[CART_EQ; FORALL_2; VECTOR_2; DIMINDEX_2] THEN
  REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; RE; IM] THEN
  REAL_ARITH_TAC);;

let ROTATE2D_PI2 = prove
 (`!z. rotate2d (pi / &2) z = ii * z`,
  REWRITE_TAC[ROTATE2D_COMPLEX; CEXP_EULER; SIN_PI2; COS_PI2; GSYM CX_SIN;
              GSYM CX_COS] THEN
  CONV_TAC COMPLEX_RING);;

let ROTATE2D_PI = prove
 (`!z. rotate2d pi z = --z`,
  REWRITE_TAC[ROTATE2D_COMPLEX; CEXP_EULER; SIN_PI; COS_PI; GSYM CX_SIN;
              GSYM CX_COS] THEN
  CONV_TAC COMPLEX_RING);;

let ROTATE2D_NPI = prove
 (`!n z. rotate2d (&n * pi) z = --Cx(&1) pow n * z`,
  REWRITE_TAC[ROTATE2D_COMPLEX; CEXP_EULER; SIN_NPI; COS_NPI; GSYM CX_SIN;
              GSYM CX_COS; CX_NEG; CX_POW] THEN
  CONV_TAC COMPLEX_RING);;

let ROTATE2D_2PI = prove
 (`!z. rotate2d (&2 * pi) z = z`,
  REWRITE_TAC[ROTATE2D_NPI] THEN CONV_TAC COMPLEX_RING);;

let ARG_ROTATE2D = prove
 (`!t z. ~(z = Cx(&0)) /\ &0 <= t + Arg z /\ t + Arg z < &2 * pi
         ==> Arg(rotate2d t z) = t + Arg z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ARG_UNIQUE THEN
  EXISTS_TAC `norm(z:complex)` THEN
  ASM_SIMP_TAC[ARG; ROTATE2D_COMPLEX; REAL_LE_ADD; COMPLEX_NORM_NZ] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [ARG] THEN
  REWRITE_TAC[CX_ADD; COMPLEX_ADD_LDISTRIB; CEXP_ADD] THEN
  REWRITE_TAC[COMPLEX_MUL_AC]);;

let ARG_ROTATE2D_UNIQUE = prove
 (`!t a z. ~(z = Cx(&0)) /\ Arg(rotate2d t z) = a
           ==> ?n. integer n /\ t = &2 * n * pi + (a - Arg z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(last(CONJUNCTS(ISPEC `rotate2d t z` ARG))) THEN
  ASM_REWRITE_TAC[NORM_ROTATE2D] THEN
  REWRITE_TAC[ROTATE2D_COMPLEX] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [ARG] THEN
  ASM_REWRITE_TAC[COMPLEX_RING `a * z * b = z * c <=> z = Cx(&0) \/ a * b = c`;
                  CX_INJ; COMPLEX_NORM_ZERO; GSYM CEXP_ADD; CEXP_EQ] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_AND THEN
  REWRITE_TAC[GSYM CX_ADD; GSYM CX_SUB; CX_INJ; COMPLEX_RING
   `ii * t + ii * z = ii * a + n * ii <=> t = n + (a - z)`]);;

let ARG_ROTATE2D_UNIQUE_2PI = prove
 (`!s t z. ~(z = Cx(&0)) /\
           &0 <= s /\ s < &2 * pi /\ &0 <= t /\ t < &2 * pi /\
           Arg(rotate2d s z) = Arg(rotate2d t z)
           ==> s = t`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `a = Arg(rotate2d t z)` THEN
  MP_TAC(ISPECL [`s:real`; `a:real`; `z:complex`] ARG_ROTATE2D_UNIQUE) THEN
  MP_TAC(ISPECL [`t:real`; `a:real`; `z:complex`] ARG_ROTATE2D_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC SIN_COS_INJ THEN
  REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[SIN_COS_EQ; REAL_RING
     `x + az:real = (y + az) + z <=> x - y = z`] THEN
    REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; GSYM REAL_SUB_RDISTRIB] THEN
    ASM_MESON_TAC[INTEGER_CLOSED];
    ASM_REAL_ARITH_TAC]);;

let COMPLEX_DIV_ROTATION = prove
 (`!f w z. orthogonal_transformation f /\ det(matrix f) = &1
           ==> f w / f z = w / z`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP ROTATION_ROTATE2D) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[ROTATE2D_COMPLEX] THEN
  SIMP_TAC[complex_div; COMPLEX_INV_MUL; CEXP_NZ; COMPLEX_FIELD
   `~(a = Cx(&0)) ==> (a * w) * (inv a * z) = w * z`]);;

let th = prove
 (`!f w z. linear f /\ (!x. norm(f x) = norm x) /\
           (2 <= dimindex(:2) ==> det(matrix f) = &1)
           ==> f w / f z = w / z`,
  REWRITE_TAC[CONJ_ASSOC; GSYM ORTHOGONAL_TRANSFORMATION;
              DIMINDEX_2; LE_REFL; COMPLEX_DIV_ROTATION]) in
add_linear_invariants [th];;

let th = prove
 (`!f t z. linear f /\ (!x. norm(f x) = norm x) /\
           (2 <= dimindex(:2) ==> det(matrix f) = &1)
           ==> rotate2d t (f z) = f(rotate2d t z)`,
  REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `f:complex->complex` ROTATION_ROTATE2D) THEN
  ASM_REWRITE_TAC[ORTHOGONAL_TRANSFORMATION] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[GSYM ROTATE2D_ADD] THEN REWRITE_TAC[REAL_ADD_SYM]) in
add_linear_invariants [th];;

let ROTATION_ROTATE2D_EXISTS_GEN = prove
 (`!x y. ?t. &0 <= t /\ t < &2 * pi /\ norm(y) % rotate2d t x = norm(x) % y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`norm(y:real^2) % x:real^2`; `norm(x:real^2) % y:real^2`]
               ROTATION_EXISTS) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; NORM_MUL; ARITH; REAL_ABS_NORM;
                  EQT_INTRO(SPEC_ALL REAL_MUL_SYM); CONJ_ASSOC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^2` (CONJUNCTS_THEN ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ROTATION_ROTATE2D) THEN
  MATCH_MP_TAC MONO_EXISTS THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LINEAR_CMUL; LINEAR_ROTATE2D]);;

let ROTATION_ROTATE2D_EXISTS = prove
 (`!x y. norm x = norm y ==> ?t. &0 <= t /\ t < &2 * pi /\ rotate2d t x = y`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `norm(y:complex) = &0` THENL
   [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN EXISTS_TAC `&0` THEN
    SIMP_TAC[REAL_LT_MUL; PI_POS; REAL_OF_NUM_LT; ARITH; REAL_LE_REFL] THEN
    ASM_MESON_TAC[COMPLEX_NORM_ZERO; ROTATE2D_0];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`x:complex`; `y:complex`] ROTATION_ROTATE2D_EXISTS_GEN) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LCANCEL]]);;

let ROTATION_ROTATE2D_EXISTS_ORTHOGONAL = prove
 (`!e1 e2. norm(e1) = &1 /\ norm(e2) = &1 /\ orthogonal e1 e2
           ==> e1 = rotate2d (pi / &2) e2 \/ e2 = rotate2d (pi / &2) e1`,
  REWRITE_TAC[NORM_EQ_1; orthogonal] THEN
  SIMP_TAC[DOT_2; CART_EQ; FORALL_2; DIMINDEX_2; rotate2d; VECTOR_2] THEN
  REWRITE_TAC[COS_PI2; SIN_PI2; REAL_MUL_RZERO; REAL_ADD_RID;
              REAL_SUB_LZERO; REAL_SUB_RZERO; REAL_MUL_RID] THEN
  CONV_TAC REAL_RING);;

let ROTATION_ROTATE2D_EXISTS_ORTHOGONAL_ORIENTED = prove
 (`!e1 e2. norm(e1) = &1 /\ norm(e2) = &1 /\ orthogonal e1 e2 /\
           &0 < e1$1 * e2$2 - e1$2 * e2$1
           ==> e2 = rotate2d (pi / &2) e1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN DISCH_TAC THEN
  FIRST_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o MATCH_MP
    ROTATION_ROTATE2D_EXISTS_ORTHOGONAL) THEN
  REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_NOT_LE]) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_THEN(K ALL_TAC) THEN
  SIMP_TAC[DOT_2; CART_EQ; FORALL_2; DIMINDEX_2; rotate2d; VECTOR_2] THEN
  REWRITE_TAC[COS_PI2; SIN_PI2; REAL_MUL_RZERO; REAL_ADD_RID;
              REAL_SUB_LZERO; REAL_SUB_RZERO; REAL_MUL_RID] THEN
  REWRITE_TAC[REAL_ARITH `--x * x - y * y <= &0 <=> &0 <= x * x + y * y`] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_SQUARE]);;

let ROTATE2D_EQ = prove
 (`!t x y. rotate2d t x = rotate2d t y <=> x = y`,
  MESON_TAC[ORTHOGONAL_TRANSFORMATION_INJECTIVE;
            ORTHOGONAL_TRANSFORMATION_ROTATE2D]);;

let ROTATE2D_SUB_ARG = prove
 (`!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
         ==> rotate2d(Arg w - Arg z) = rotate2d(Arg(w / z))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_SUB_ARG] THEN
  COND_CASES_TAC THEN REWRITE_TAC[real_sub; ROTATE2D_ADD; FUN_EQ_THM] THEN
  GEN_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[ROTATE2D_COMPLEX] THEN
  REWRITE_TAC[EULER; RE_MUL_II; IM_MUL_II; RE_CX; IM_CX; COS_NEG; SIN_NEG] THEN
  REWRITE_TAC[SIN_NPI; COS_NPI; REAL_EXP_NEG; REAL_EXP_0; CX_NEG] THEN
  REWRITE_TAC[COMPLEX_NEG_0; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[COMPLEX_MUL_LID]);;

let ROTATION_MATRIX_ROTATE2D = prove
 (`!t. rotation_matrix(matrix(rotate2d t))`,
  SIMP_TAC[ROTATION_MATRIX_2; MATRIX_ROTATE2D; VECTOR_2] THEN
  MESON_TAC[SIN_CIRCLE; REAL_ADD_SYM]);;

let ROTATION_MATRIX_ROTATE2D_EQ = prove
 (`!A:real^2^2. rotation_matrix A <=> ?t. A = matrix(rotate2d t)`,
  GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM; ROTATION_MATRIX_ROTATE2D] THEN
  REWRITE_TAC[ROTATION_MATRIX_2; MATRIX_ROTATE2D] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP SINCOS_TOTAL_2PI) THEN
  MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Homotopy of linear maps of various kinds where the homotopy stays inside  *)
(* that class of linear maps.                                                *)
(* ------------------------------------------------------------------------- *)

let NULLHOMOTOPIC_ORTHOGONAL_TRANSFORMATION = prove
 (`!f:real^N->real^N.
       orthogonal_transformation f /\ det(matrix f) = &1
       ==> homotopic_with orthogonal_transformation ((:real^N),(:real^N)) f I`,
  let lemma0 = prove
   (`!a x:real^N.
          2 <= dimindex(:N) /\ a IN span {basis 1,basis 2}
          ==> reflect_along (vector[a$1; a$2]:real^2) (lambda i. x$i) =
              (lambda i. reflect_along a x$i)`,
    REPEAT STRIP_TAC THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA; reflect_along; VECTOR_SUB_COMPONENT;
             VECTOR_MUL_COMPONENT; DIMINDEX_2; FORALL_2; VECTOR_2; ARITH] THEN
    CONJ_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN BINOP_TAC THEN REWRITE_TAC[dot] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_EQ_SUPERSET THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; FORALL_2; DIMINDEX_2; LAMBDA_BETA;
                 ARITH; VECTOR_2; SUBSET_NUMSEG] THEN
    REWRITE_TAC[ARITH_RULE
     `(1 <= i /\ i <= n) /\ ~(1 <= i /\ i <= 2) <=>
      1 <= i /\ 3 <= i /\ i <= n`] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [SPAN_2]) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT] THEN
    REPEAT STRIP_TAC THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO]) THEN
    ASM_ARITH_TAC) in
  let lemma1 = prove
   (`!a b:real^2 r.
          ~(a = vec 0) /\ ~(b = vec 0)
          ==> homotopic_with orthogonal_transformation ((:real^2),(:real^2))
                             (reflect_along a o reflect_along b) I`,
    REPEAT STRIP_TAC THEN
    MP_TAC(SPEC `reflect_along (a:real^2) o reflect_along b`
          ROTATION_ROTATE2D) THEN
    ANTS_TAC THENL
     [REPEAT(FIRST_X_ASSUM(MP_TAC o
        MATCH_MP ROTOINVERSION_MATRIX_REFLECT_ALONG)) THEN
      REWRITE_TAC[rotoinversion_matrix] THEN
      SIMP_TAC[ORTHOGONAL_MATRIX_MATRIX;
               ORTHOGONAL_TRANSFORMATION_REFLECT_ALONG;
               ORTHOGONAL_TRANSFORMATION_COMPOSE; MATRIX_COMPOSE;
               LINEAR_REFLECT_ALONG; DET_MUL] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
      ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN
      ASM_REWRITE_TAC[homotopic_with] THEN
      EXISTS_TAC `\z. rotate2d (drop(fstcart z) * t) (sndcart z)` THEN
      SIMP_TAC[ORTHOGONAL_TRANSFORMATION_ROTATE2D; SNDCART_PASTECART;
               ETA_AX; FSTCART_PASTECART; DROP_VEC; I_THM; NORM_ROTATE2D;
               REAL_MUL_LZERO; REAL_MUL_LID; SUBSET; FORALL_IN_IMAGE; IN_UNIV;
               FORALL_IN_PCROSS; IN_SPHERE_0; ROTATE2D_ZERO] THEN
      REWRITE_TAC[ROTATE2D_COMPLEX] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      REWRITE_TAC[CONTINUOUS_ON_CEXP; CX_MUL] THEN
      ONCE_REWRITE_TAC[COMPLEX_RING `ii * x * t = (ii * t) * x`] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
      MATCH_MP_TAC CONTINUOUS_ON_CX_DROP THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART]]) in
  let lemma2 = prove
   (`!a b:real^N r.
          2 <= dimindex(:N) /\
          ~(a = vec 0) /\ ~(b = vec 0) /\
          {a,b} SUBSET span {basis 1,basis 2}
          ==> homotopic_with orthogonal_transformation ((:real^N),(:real^N))
                             (reflect_along a o reflect_along b) I`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
      `homotopic_with orthogonal_transformation
        ((:real^N),(:real^N))
        ((\z. (lambda i. if i <= 2 then (fstcart z)$i
                         else (sndcart z)$i):real^N) o
         (\z. pastecart
               (((reflect_along (vector [(a:real^N)$1; a$2]) o
                 reflect_along (vector [(b:real^N)$1; b$2]))
                  :real^2->real^2)(fstcart z))
               (sndcart z)) o
         (\z:real^N. pastecart ((lambda i. z$i) :real^2) z))
        ((\z. (lambda i. if i <= 2 then (fstcart z)$i
                         else (sndcart z)$i):real^N) o
         I o
         (\z:real^N. pastecart ((lambda i. z$i) :real^2) z))`
    MP_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
      EXISTS_TAC `(:real^2) PCROSS (:real^N)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
        ONCE_REWRITE_TAC[LINEAR_COMPONENTWISE] THEN
        SIMP_TAC[LAMBDA_BETA] THEN X_GEN_TAC `i:num` THEN
        STRIP_TAC THEN ASM_CASES_TAC `i <= 2` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[linear; FSTCART_ADD; FSTCART_CMUL;
                            SNDCART_ADD; SNDCART_CMUL] THEN
        REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
        REWRITE_TAC[LIFT_ADD; LIFT_CMUL]] THEN
      MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
      EXISTS_TAC `(:real^2) PCROSS (:real^N)` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; PASTECART_IN_PCROSS] THEN
      CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
        MATCH_MP_TAC LINEAR_PASTECART THEN REWRITE_TAC[LINEAR_ID] THEN
        SIMP_TAC[linear; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
                 VECTOR_MUL_COMPONENT]] THEN
      SUBGOAL_THEN
       `I = \z:real^(2,N)finite_sum. pastecart (fstcart z) (sndcart z)`
      SUBST1_TAC THENL
       [REWRITE_TAC[PASTECART_FST_SND; I_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC HOMOTOPIC_WITH_PCROSS THEN
      EXISTS_TAC `orthogonal_transformation:(real^2->real^2)->bool` THEN
      EXISTS_TAC `\f:real^N->real^N. f = I` THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[GSYM I_DEF; ETA_AX] THEN MATCH_MP_TAC lemma1 THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INSERT_SUBSET]) THEN
        REWRITE_TAC[SING_SUBSET; SPAN_2; IN_ELIM_THM; IN_UNIV] THEN
        DISCH_THEN(REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC) THEN
        POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
        REWRITE_TAC[CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                    DIMINDEX_2; FORALL_2; VECTOR_2] THEN
        SIMP_TAC[BASIS_COMPONENT; ARITH; DIMINDEX_2; VEC_COMPONENT;
                 DIMINDEX_GE_1; LE_REFL] THEN
        MATCH_MP_TAC(TAUT
         `(r ==> q) /\ (s ==> p) ==> a /\ ~p /\ ~q ==> ~s /\ ~r`) THEN
        SIMP_TAC[REAL_MUL_RZERO; REAL_MUL_LZERO; REAL_MUL_RID;
                 REAL_ADD_LID; REAL_ADD_RID];
        REWRITE_TAC[HOMOTOPIC_WITH_REFL; SUBSET_UNIV; I_DEF] THEN
        REWRITE_TAC[CONTINUOUS_ON_ID];
        SIMP_TAC[o_DEF; FSTCART_PASTECART; SNDCART_PASTECART;
                 LAMBDA_BETA; DIMINDEX_2; ARITH; I_THM] THEN
        REWRITE_TAC[ORTHOGONAL_TRANSFORMATION; NORM_EQ] THEN
        X_GEN_TAC `f:real^2->real^2` THEN GEN_TAC THEN STRIP_TAC THEN
        CONJ_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [linear]) THEN
          SIMP_TAC[linear; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
                   VECTOR_MUL_COMPONENT; DIMINDEX_2; ARITH] THEN
          MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN
          DISCH_THEN(ASSUME_TAC o GSYM) THEN GEN_TAC THEN
          GEN_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
          COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
          AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
          SIMP_TAC[CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
                   VECTOR_MUL_COMPONENT];
          X_GEN_TAC `v:real^N` THEN REWRITE_TAC[dot; GSYM REAL_POW_2] THEN
          SUBGOAL_THEN `dimindex(:N) = 2 + (dimindex(:N) - 2)` SUBST1_TAC THENL
           [ASM_ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[SUM_ADD_SPLIT; ARITH_RULE `1 <= n + 1`] THEN
          BINOP_TAC THENL
           [RULE_ASSUM_TAC(REWRITE_RULE[dot; DIMINDEX_2; GSYM REAL_POW_2]) THEN
            FIRST_X_ASSUM(MP_TAC o SPEC `(lambda i. (v:real^N)$i):real^2`) THEN
            MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN
            MATCH_MP_TAC SUM_EQ_NUMSEG THEN
            FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
             `2 <= n ==> !i. i <= 2 ==> i <= n`)) THEN
            SIMP_TAC[LAMBDA_BETA; DIMINDEX_2];
            ASM_SIMP_TAC[ARITH_RULE `2 <= n ==> 2 + n - 2 = n`] THEN
            MATCH_MP_TAC SUM_EQ_NUMSEG THEN
            SIMP_TAC[ARITH_RULE `2 + 1 <= i ==> 1 <= i`;
                     LAMBDA_BETA; DIMINDEX_2] THEN
            REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
            ASM_ARITH_TAC]]];
      MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_EQ) THEN
      REWRITE_TAC[IN_UNIV; GSYM FUN_EQ_THM] THEN
      SIMP_TAC[o_DEF; FSTCART_PASTECART; SNDCART_PASTECART;
               LAMBDA_BETA; DIMINDEX_2; ARITH; I_THM] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[INSERT_SUBSET; EMPTY_SUBSET]) THEN
      ASM_SIMP_TAC[lemma0] THEN
      SIMP_TAC[CART_EQ; LAMBDA_BETA; DIMINDEX_2; ARITH; COND_ID] THEN
      MAP_EVERY X_GEN_TAC [`x:real^N`; `i:num`] THEN STRIP_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(a:real^N)$i = &0 /\ (b:real^N)$i = &0` ASSUME_TAC THENL
       [FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC) THEN
        REWRITE_TAC[SPAN_2; IN_ELIM_THM; IN_UNIV] THEN REPEAT STRIP_TAC THEN
        ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                     BASIS_COMPONENT] THEN
        REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
        (REAL_ARITH_TAC ORELSE ASM_ARITH_TAC);
        ASM_REWRITE_TAC[reflect_along; VECTOR_SUB_COMPONENT; REAL_MUL_RZERO;
                        VECTOR_MUL_COMPONENT; REAL_SUB_RZERO]]]) in
  let lemma3 = prove
   (`!a b:real^N r.
          ~(a = vec 0) /\ ~(b = vec 0)
          ==> homotopic_with orthogonal_transformation ((:real^N),(:real^N))
                             (reflect_along a o reflect_along b) I`,
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `dimindex(:N) = 1` THENL
     [ASM_SIMP_TAC[o_DEF; I_DEF; REFLECT_ALONG_1D; VECTOR_NEG_NEG] THEN
      REWRITE_TAC[HOMOTOPIC_WITH_REFL; SUBSET_UNIV; CONTINUOUS_ON_ID] THEN
      REWRITE_TAC[ORTHOGONAL_TRANSFORMATION_ID];
      FIRST_X_ASSUM(MP_TAC o MATCH_MP(ARITH_RULE
       `~(n = 1) ==> 1 <= n ==> 2 <= n`)) THEN
      REWRITE_TAC[DIMINDEX_GE_1] THEN DISCH_TAC] THEN
    MP_TAC(ISPECL [`span{a:real^N,b}`; `span{basis 1:real^N,basis 2}`]
          ORTHOGONAL_TRANSFORMATION_INTO_SUBSPACE) THEN
    REWRITE_TAC[SUBSPACE_SPAN; DIM_SPAN] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[DIM_INSERT; SPAN_SING; SPAN_EMPTY;
                      IN_SING; DIM_EMPTY] THEN
      MATCH_MP_TAC(ARITH_RULE `m <= 2 /\ n = 2 ==> m <= n`) THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[BASIS_NONZERO; ARITH] THEN
      REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(CHOOSE_THEN (MP_TAC o AP_TERM `(\x:real^N. x$1)`)) THEN
      ASM_SIMP_TAC[BASIS_COMPONENT; VECTOR_MUL_COMPONENT;
                   ARITH; DIMINDEX_GE_1] THEN
      REAL_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `f:real^N->real^N` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPEC `f:real^N->real^N` ORTHOGONAL_TRANSFORMATION_INVERSE_o) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC)] THEN
    SUBGOAL_THEN
     `homotopic_with orthogonal_transformation ((:real^N),(:real^N))
       (g o (f o (reflect_along a o reflect_along b) o (g:real^N->real^N)) o f)
       (g o (f o I o (g:real^N->real^N)) o f)`
    MP_TAC THENL
     [ALL_TAC;
      ASM_REWRITE_TAC[o_ASSOC] THEN ASM_REWRITE_TAC[GSYM o_ASSOC; I_O_ID]] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
    EXISTS_TAC `(:real^N)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
    ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR; LINEAR_CONTINUOUS_ON] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
    EXISTS_TAC `(:real^N)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
    ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR; LINEAR_CONTINUOUS_ON] THEN
    ASM_REWRITE_TAC[I_O_ID] THEN
    MP_TAC(ISPEC `f:real^N->real^N` REFLECT_ALONG_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[GSYM ORTHOGONAL_TRANSFORMATION] THEN
    DISCH_THEN(ASSUME_TAC o GSYM) THEN
    SUBGOAL_THEN
     `!h:real^N->real^N.
          orthogonal_transformation (g o h o (f:real^N->real^N)) <=>
          orthogonal_transformation h`
     (fun th -> REWRITE_TAC[th; ETA_AX])
    THENL
     [GEN_TAC THEN EQ_TAC THEN
      ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_COMPOSE] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `h:real^N->real^N = f o (g o h o f) o (g:real^N->real^N)`
      SUBST1_TAC THENL
       [ALL_TAC; ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_COMPOSE]] THEN
      ASM_REWRITE_TAC[o_ASSOC] THEN ASM_REWRITE_TAC[GSYM o_ASSOC; I_O_ID];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(f:real^N->real^N) o (reflect_along a o reflect_along b) o g =
      reflect_along (f a) o reflect_along (f b)`
    SUBST1_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[FUN_EQ_THM; o_THM; I_THM]) THEN
      ASM_REWRITE_TAC[o_DEF];
      MATCH_MP_TAC lemma2 THEN RULE_ASSUM_TAC
       (REWRITE_RULE[GSYM NORM_EQ_0; ORTHOGONAL_TRANSFORMATION]) THEN
      ASM_REWRITE_TAC[GSYM NORM_EQ_0] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
         SUBSET_TRANS)) THEN
      ASM_SIMP_TAC[GSYM SPAN_LINEAR_IMAGE; IMAGE_CLAUSES] THEN
      REWRITE_TAC[SPAN_INC]]) in
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MP_TAC(ISPECL [`f:real^N->real^N`; `dimindex(:N)`]
        ORTHOGONAL_TRANSFORMATION_GENERATED_BY_REFLECTIONS) THEN
  ASM_REWRITE_TAC[ARITH_RULE `n:num <= a + n`] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:(real^N)list` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `ALL (\v:real^N. ~(v = vec 0)) l` THEN
  UNDISCH_TAC `orthogonal_transformation(f:real^N->real^N)` THEN
  MATCH_MP_TAC(TAUT `r /\ (p /\ q ==> s) ==> r ==> p ==> q ==> s`) THEN
  ASM_REWRITE_TAC[IMP_IMP] THEN
  SPEC_TAC(`l:(real^N)list`,`l:(real^N)list`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN GEN_TAC THEN
  WF_INDUCT_TAC `LENGTH(l:(real^N)list)` THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC(`l:(real^N)list`,`l:(real^N)list`) THEN
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[ALL; ITLIST; HOMOTOPIC_WITH_REFL] THEN
  REWRITE_TAC[REWRITE_RULE[GSYM I_DEF] CONTINUOUS_ON_ID;
              ORTHOGONAL_TRANSFORMATION_I; SUBSET_UNIV] THEN
  X_GEN_TAC `a:real^N` THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[ALL; ITLIST; I_O_ID; DET_MATRIX_REFLECT_ALONG] THEN
  REWRITE_TAC[ORTHOGONAL_TRANSFORMATION_REFLECT_ALONG] THEN
  CONJ_TAC THENL [MESON_TAC[REAL_ARITH `~(-- &1 = &1)`]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`b:real^N`; `l:(real^N)list`] THEN
  REPLICATE_TAC 2 (DISCH_THEN(K ALL_TAC)) THEN
  DISCH_THEN(MP_TAC o SPEC `l:(real^N)list`) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `n < SUC(SUC n)`] THEN
  SIMP_TAC[LINEAR_COMPOSE; LINEAR_REFLECT_ALONG; MATRIX_COMPOSE;
     ORTHOGONAL_TRANSFORMATION_REFLECT_ALONG;
     ORTHOGONAL_TRANSFORMATION_COMPOSE; ORTHOGONAL_TRANSFORMATION_LINEAR] THEN
  DISCH_THEN(fun th ->
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN MP_TAC th) THEN
  ASM_SIMP_TAC[DET_MUL; DET_MATRIX_REFLECT_ALONG; REAL_ARITH
   `-- &1 * -- &1 * x = x`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HOMOTOPIC_WITH_TRANS) THEN
  GEN_REWRITE_TAC RAND_CONV [MESON[I_O_ID] `f = I o f`] THEN
  REWRITE_TAC[o_ASSOC] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
  EXISTS_TAC `(:real^N)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
  ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; ORTHOGONAL_TRANSFORMATION_LINEAR] THEN
  ABBREV_TAC `g = ITLIST (\v:real^N h. reflect_along v o h) l I` THEN
  SUBGOAL_THEN
   `(\f:real^N->real^N.
        orthogonal_transformation (f o g)) = orthogonal_transformation`
  SUBST1_TAC THENL [ALL_TAC; MATCH_MP_TAC lemma3 THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `f:real^N->real^N` THEN
  EQ_TAC THEN ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_COMPOSE] THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC `g:real^N->real^N` ORTHOGONAL_TRANSFORMATION_INVERSE_o) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `h:real^N->real^N` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `f = ((f:real^N->real^N) o (g:real^N->real^N)) o h`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[GSYM o_ASSOC; I_O_ID];
    ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_COMPOSE]]);;

let HOMOTOPIC_SPECIAL_ORTHOGONAL_TRANSFORMATIONS,
    HOMOTOPIC_ORTHOGONAL_TRANSFORMATIONS = (CONJ_PAIR o prove)
 (`(!f g. homotopic_with
            (\h. orthogonal_transformation h /\ det(matrix h) = det(matrix f))
            ((:real^N),(:real^N)) f g <=>
          homotopic_with
            orthogonal_transformation ((:real^N),(:real^N)) f g) /\
   !f g. homotopic_with orthogonal_transformation ((:real^N),(:real^N)) f g <=>
         orthogonal_transformation f /\ orthogonal_transformation g /\
         det(matrix f) = det(matrix g)`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC(TAUT
   `(u ==> s) /\ (s ==> t) /\ (t ==> u)
    ==> (u <=> t) /\ (t <=> s)`) THEN
  REPEAT CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_PROPERTY) THEN MESON_TAC[];
    STRIP_TAC THEN
    MP_TAC(ISPEC `g:real^N->real^N` ORTHOGONAL_TRANSFORMATION_INVERSE_o) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `(f:real^N->real^N) = g o (h:real^N->real^N) o f /\ g = g o I`
     (fun th -> ONCE_REWRITE_TAC[th])
    THENL [ASM_REWRITE_TAC[o_ASSOC; I_O_ID]; ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
    EXISTS_TAC `(:real^N)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
    ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR; LINEAR_CONTINUOUS_ON] THEN
    SUBGOAL_THEN
      `!k:real^N->real^N.
          orthogonal_transformation (g o k) <=> orthogonal_transformation k`
      (fun th -> REWRITE_TAC[th; ETA_AX])
    THENL
     [GEN_TAC THEN EQ_TAC THEN
      ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_COMPOSE] THEN DISCH_THEN
       (MP_TAC o SPEC `h:real^N->real^N` o MATCH_MP (ONCE_REWRITE_RULE
         [IMP_CONJ_ALT] ORTHOGONAL_TRANSFORMATION_COMPOSE)) THEN
      ASM_SIMP_TAC[o_ASSOC; I_O_ID];
      MATCH_MP_TAC NULLHOMOTOPIC_ORTHOGONAL_TRANSFORMATION THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o AP_TERM
       `\f:real^N->real^N. det(matrix f)`)) THEN
      ASM_SIMP_TAC[MATRIX_COMPOSE; ORTHOGONAL_TRANSFORMATION_LINEAR;
                   ORTHOGONAL_TRANSFORMATION_COMPOSE; DET_MUL;
                   MATRIX_I; DET_I]];
    REWRITE_TAC[homotopic_with] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `k:real^(1,N)finite_sum->real^N` THEN
    STRIP_TAC THEN ASM_SIMP_TAC[] THEN MP_TAC(ISPECL
     [`\t. lift(
       det(matrix((k:real^(1,N)finite_sum->real^N) o pastecart t)))`;
      `interval[vec 0:real^1,vec 1]`]
     CONTINUOUS_DISCRETE_RANGE_CONSTANT) THEN
    REWRITE_TAC[CONNECTED_INTERVAL] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_LIFT_DET THEN
        SIMP_TAC[matrix; LAMBDA_BETA; o_DEF] THEN
        MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
        MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
        ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_CONST;
                 CONTINUOUS_ON_ID] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; IN_UNIV];
        X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN EXISTS_TAC `&1` THEN
        REWRITE_TAC[REAL_LT_01] THEN X_GEN_TAC `u:real^1` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT; LIFT_EQ] THEN
        SUBGOAL_THEN
         `orthogonal_transformation
           ((k:real^(1,N)finite_sum->real^N) o pastecart t) /\
          orthogonal_transformation (k o pastecart u)`
        MP_TAC THENL [ASM_SIMP_TAC[o_DEF]; ALL_TAC] THEN
        DISCH_THEN(CONJUNCTS_THEN
          (STRIP_ASSUME_TAC o MATCH_MP DET_ORTHOGONAL_MATRIX o
                    MATCH_MP ORTHOGONAL_MATRIX_MATRIX)) THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV];
      REWRITE_TAC[o_DEF; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `a:real^1` THEN DISCH_TAC THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM FUN_EQ_THM])) THEN
      REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
      ASM_SIMP_TAC[ENDS_IN_UNIT_INTERVAL; GSYM LIFT_EQ]]]);;

let HOMOTOPIC_ORTHOGONAL_TRANSFORMATIONS_SPHERE = prove
 (`!f g r.
        &0 < r
        ==> (homotopic_with orthogonal_transformation
                            (sphere(vec 0,r),sphere(vec 0,r)) f g <=>
             homotopic_with orthogonal_transformation
                            ((:real^N),(:real^N)) f g)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC;
    DISCH_TAC THEN MATCH_MP_TAC HOMOTOPIC_WITH_RESTRICT THEN
    REPEAT(EXISTS_TAC `(:real^N)`) THEN ASM_REWRITE_TAC[SUBSET_UNIV] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE; DIST_0] THEN
    MESON_TAC[ORTHOGONAL_TRANSFORMATION]] THEN
  REWRITE_TAC[homotopic_with] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `h:real^(1,N)finite_sum->real^N` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[SUBSET_UNIV] THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC
   `\z. norm(sndcart z) / r %
        (h:real^(1,N)finite_sum->real^N)
        (pastecart (fstcart z) (r / norm(sndcart z) % sndcart z))` THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; FORALL_IN_PCROSS; IN_UNIV;
              FSTCART_PASTECART; SNDCART_PASTECART] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:real^1`; `x:real^N`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:real^1`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR) THEN
    DISCH_THEN(MP_TAC o MATCH_MP LINEAR_CMUL) THEN
    SIMP_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `&0`) THEN
    REWRITE_TAC[VECTOR_MUL_LZERO] THEN STRIP_TAC THEN
    ASM_CASES_TAC `x:real^N = vec 0` THEN
    ASM_REWRITE_TAC[NORM_0; VECTOR_MUL_LZERO; real_div; REAL_MUL_LZERO] THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; NORM_EQ_0; VECTOR_MUL_LID; REAL_FIELD
     `~(x = &0) /\ &0 < r ==> (x * inv r) * r * inv x = &1`];
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  MAP_EVERY X_GEN_TAC [`a:real^1`; `x:real^N`] THEN DISCH_TAC THEN
  ASM_CASES_TAC `x:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[CONTINUOUS_WITHIN; SNDCART_PASTECART] THEN
    REWRITE_TAC[NORM_0; real_div; REAL_MUL_LZERO; VECTOR_MUL_LZERO] THEN
    MATCH_MP_TAC LIM_NULL_COMPARISON THEN
    EXISTS_TAC `(norm o sndcart):real^(1,N)finite_sum->real` THEN
    CONJ_TAC THENL
     [SIMP_TAC[EVENTUALLY_WITHIN; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
      EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01; IN_UNIV] THEN
      REWRITE_TAC[o_DEF; FSTCART_PASTECART; SNDCART_PASTECART] THEN
      MAP_EVERY X_GEN_TAC [`b:real^1`; `y:real^N`] THEN STRIP_TAC THEN
      ASM_CASES_TAC `y:real^N = vec 0` THEN
      ASM_SIMP_TAC[NORM_0; VECTOR_MUL_LZERO; REAL_MUL_LZERO; REAL_LE_REFL] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `b:real^1`) THEN
      ASM_REWRITE_TAC[ORTHOGONAL_TRANSFORMATION] THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      DISCH_THEN(MP_TAC o MATCH_MP LINEAR_CMUL) THEN
      ASM_SIMP_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_MUL; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[NORM_EQ_0; REAL_LE_REFL; REAL_FIELD
       `&0 < r /\ ~(y = &0) ==> (y * inv(abs r)) * (abs r * inv y) * y = y`];
      MATCH_MP_TAC(MESON[CONTINUOUS_WITHIN; CONTINUOUS_AT_WITHIN]
       `f continuous at a /\ f a = l ==> (f --> l) (at a within s)`) THEN
      REWRITE_TAC[o_DEF; SNDCART_PASTECART; NORM_0; LIFT_NUM] THEN
      SIMP_TAC[CONTINUOUS_LIFT_NORM_COMPOSE; LINEAR_CONTINUOUS_AT;
               LINEAR_SNDCART]];
    MATCH_MP_TAC CONTINUOUS_MUL THEN REWRITE_TAC[o_DEF; real_div] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `norm(x:real^N) * inv r = inv r * norm x`] THEN
    SIMP_TAC[LIFT_CMUL; CONTINUOUS_CMUL; CONTINUOUS_LIFT_NORM_COMPOSE;
             LINEAR_CONTINUOUS_WITHIN; LINEAR_SNDCART] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_WITHIN_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_PASTECART THEN
      SIMP_TAC[LINEAR_CONTINUOUS_WITHIN; LINEAR_FSTCART] THEN
      MATCH_MP_TAC CONTINUOUS_MUL THEN
      SIMP_TAC[LINEAR_CONTINUOUS_WITHIN; LINEAR_SNDCART] THEN
      REWRITE_TAC[o_DEF; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_CMUL THEN
      MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_AT_WITHIN_INV) THEN
      SIMP_TAC[CONTINUOUS_LIFT_NORM_COMPOSE; LINEAR_CONTINUOUS_WITHIN;
               LINEAR_SNDCART; o_DEF] THEN
      ASM_REWRITE_TAC[NORM_EQ_0; SNDCART_PASTECART];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
        [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]) THEN
      REWRITE_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART] THEN
      DISCH_THEN(MP_TAC o SPECL [`a:real^1`; `r / norm(x) % x:real^N`]) THEN
      ASM_SIMP_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM;
                   REAL_MUL_LINV; NORM_EQ_0; real_div; REAL_ABS_INV;
                   REAL_ABS_MUL; REAL_ARITH `&0 < r ==> abs r = r`;
                REAL_FIELD `&0 < r /\ ~(x = &0) ==> (r * inv x) * x = r`] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_TRANSFORM_WITHIN_SET_IMP) THEN
      REWRITE_TAC[EVENTUALLY_AT] THEN
      REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
      REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; FORALL_IN_PCROSS; IN_UNIV] THEN
      EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_IN_PCROSS] THEN
      MAP_EVERY X_GEN_TAC [`b:real^1`; `y:real^N`] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM;
                   REAL_ABS_MUL; REAL_ARITH `&0 < r ==> abs r = r`;
                   REAL_RING `(r * x) * y = r <=> r = &0 \/ x * y = &1`;
                   REAL_LT_IMP_NZ; REAL_FIELD `inv x * x = &1 <=> ~(x = &0)`;
                   NORM_EQ_0] THEN
      DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[NORM_0; REAL_INV_0; REAL_MUL_RZERO; VECTOR_MUL_LZERO] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (MESON[DIST_LE_PASTECART; REAL_LET_TRANS]
        `dist(pastecart a b,pastecart c d) < r ==> dist(b,d) < r`)) THEN
      ASM_SIMP_TAC[DIST_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM; REAL_ABS_MUL;
                   REAL_ARITH `&0 < r ==> abs r = r`] THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_DIV_RMUL; NORM_EQ_0; REAL_LT_REFL]]]);;

let HOMOTOPIC_LINEAR_MAPS = prove
 (`!f g. homotopic_with linear ((:real^M),(:real^N)) f g <=>
         linear f /\ linear g`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[HOMOTOPIC_WITH_IMP_PROPERTY] THEN
  STRIP_TAC THEN REWRITE_TAC[homotopic_with] THEN
  EXISTS_TAC `\z. (&1 - drop(fstcart z)) % (f:real^M->real^N) (sndcart z) +
                  drop(fstcart z) % (g:real^M->real^N) (sndcart z)` THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; DROP_VEC; SUBSET_UNIV;
              VECTOR_MUL_LID; VECTOR_MUL_LZERO; REAL_SUB_RZERO; REAL_SUB_REFL;
              VECTOR_ADD_LID; VECTOR_ADD_RID] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    SIMP_TAC[o_DEF; LIFT_SUB; LIFT_DROP; CONTINUOUS_ON_SUB; LINEAR_FSTCART;
      ETA_AX; LINEAR_SNDCART; CONTINUOUS_ON_CONST; LINEAR_CONTINUOUS_ON] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC LINEAR_COMPOSE_ADD THEN
    CONJ_TAC THEN MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN ASM_REWRITE_TAC[]]);;

let HOMOTOPIC_LINEAR_POSITIVE_SEMIDEFINITE_MAPS = prove
 (`!f g. homotopic_with (\f. linear f /\ positive_semidefinite(matrix f))
                        ((:real^N),(:real^N)) f g <=>
           linear f /\ linear g /\
           positive_semidefinite(matrix f) /\
           positive_semidefinite(matrix g)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_PROPERTY) THEN SIMP_TAC[];
    REWRITE_TAC[homotopic_with]] THEN
  EXISTS_TAC `\z. (&1 - drop(fstcart z)) % (f:real^N->real^N) (sndcart z) +
                  drop(fstcart z) % (g:real^N->real^N) (sndcart z)` THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; DROP_VEC; SUBSET_UNIV;
              VECTOR_MUL_LID; VECTOR_MUL_LZERO; REAL_SUB_RZERO; REAL_SUB_REFL;
              VECTOR_ADD_LID; VECTOR_ADD_RID] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    SIMP_TAC[o_DEF; LIFT_SUB; LIFT_DROP; CONTINUOUS_ON_SUB; LINEAR_FSTCART;
      ETA_AX; LINEAR_SNDCART; CONTINUOUS_ON_CONST; LINEAR_CONTINUOUS_ON] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART];
    REWRITE_TAC[IN_INTERVAL_1; GSYM FORALL_DROP; DROP_VEC] THEN
    ASM_SIMP_TAC[LINEAR_COMPOSE_ADD; MATRIX_ADD; LINEAR_COMPOSE_CMUL;
                 MATRIX_CMUL] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC POSITIVE_SEMIDEFINITE_ADD THEN
    CONJ_TAC THEN MATCH_MP_TAC POSITIVE_SEMIDEFINITE_CMUL THEN
    ASM_REWRITE_TAC[REAL_SUB_LE]]);;

let HOMOTOPIC_LINEAR_POSITIVE_DEFINITE_MAPS = prove
 (`!f g. homotopic_with (\f. linear f /\ positive_definite(matrix f))
                        ((:real^N),(:real^N)) f g <=>
           linear f /\ linear g /\
           positive_definite(matrix f) /\
           positive_definite(matrix g)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_PROPERTY) THEN SIMP_TAC[];
    REWRITE_TAC[homotopic_with]] THEN
  EXISTS_TAC `\z. (&1 - drop(fstcart z)) % (f:real^N->real^N) (sndcart z) +
                  drop(fstcart z) % (g:real^N->real^N) (sndcart z)` THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; DROP_VEC; SUBSET_UNIV;
              VECTOR_MUL_LID; VECTOR_MUL_LZERO; REAL_SUB_RZERO; REAL_SUB_REFL;
              VECTOR_ADD_LID; VECTOR_ADD_RID] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    SIMP_TAC[o_DEF; LIFT_SUB; LIFT_DROP; CONTINUOUS_ON_SUB; LINEAR_FSTCART;
      ETA_AX; LINEAR_SNDCART; CONTINUOUS_ON_CONST; LINEAR_CONTINUOUS_ON] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART];
    REWRITE_TAC[IN_INTERVAL_1; GSYM FORALL_DROP; DROP_VEC] THEN
    ASM_SIMP_TAC[LINEAR_COMPOSE_ADD; MATRIX_ADD; LINEAR_COMPOSE_CMUL;
                 MATRIX_CMUL] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_CASES_TAC `t = &0` THEN
    ASM_REWRITE_TAC[REAL_SUB_RZERO; MATRIX_CMUL_LZERO; MATRIX_ADD_RID;
                    MATRIX_CMUL_LID] THEN
    ASM_CASES_TAC `t = &1` THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; MATRIX_CMUL_LZERO; MATRIX_ADD_LID;
                    MATRIX_CMUL_LID] THEN
    MATCH_MP_TAC POSITIVE_DEFINITE_ADD THEN
    CONJ_TAC THEN MATCH_MP_TAC POSITIVE_DEFINITE_CMUL THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let HOMOTOPIC_RESTRICTED_LINEAR_MAPS = prove
 (`!f g b. homotopic_with (\f. linear f /\ real_sgn(det(matrix f)) = b)
                          ((:real^N),(:real^N)) f g <=>
           linear f /\ linear g /\
           real_sgn(det(matrix f)) = b /\
           real_sgn(det(matrix g)) = b`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_PROPERTY) THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `b = &0` THENL
   [ASM_REWRITE_TAC[REAL_SGN_EQ] THEN STRIP_TAC THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN
    EXISTS_TAC `(\x. vec 0):real^N->real^N` THEN
    GEN_REWRITE_TAC LAND_CONV [HOMOTOPIC_WITH_SYM] THEN
    REWRITE_TAC[homotopic_with] THEN CONJ_TAC THENL
     [EXISTS_TAC `\z. drop(fstcart z) % (f:real^N->real^N) (sndcart z)`;
      EXISTS_TAC `\z. drop(fstcart z) % (g:real^N->real^N) (sndcart z)`] THEN
    REWRITE_TAC[SUBSET_UNIV; FSTCART_PASTECART; SNDCART_PASTECART;
                DROP_VEC; VECTOR_MUL_LZERO; VECTOR_MUL_LID] THEN
    ASM_SIMP_TAC[LINEAR_COMPOSE_CMUL; MATRIX_CMUL] THEN
    ASM_REWRITE_TAC[DET_CMUL; REAL_MUL_RZERO] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    SIMP_TAC[o_DEF; LIFT_DROP; LINEAR_FSTCART; ETA_AX; LINEAR_SNDCART;
             LINEAR_CONTINUOUS_ON] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(?fu fp. linear fu /\ linear fp /\
             orthogonal_transformation fu /\
             positive_definite(matrix fp) /\
             (f:real^N->real^N) = fu o fp) /\
    (?gu gp. linear gu /\ linear gp /\
             orthogonal_transformation gu /\
             positive_definite(matrix gp) /\
             (g:real^N->real^N) = gu o gp)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPEC `matrix(f:real^N->real^N)`
        RIGHT_POLAR_DECOMPOSITION_INVERTIBLE);
      MP_TAC(ISPEC `matrix(g:real^N->real^N)`
        RIGHT_POLAR_DECOMPOSITION_INVERTIBLE)] THEN
    REWRITE_TAC[INVERTIBLE_DET_NZ] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [GSYM REAL_SGN_EQ] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC(MESON[]
     `(!M. P M ==> Q(\x:real^N. M ** x))
      ==> (?M. P M) ==> (?f. Q f)`) THEN GEN_TAC) THEN
    SIMP_TAC[GSYM ORTHOGONAL_MATRIX_TRANSFORMATION;
             MATRIX_VECTOR_MUL_LINEAR; MATRIX_OF_MATRIX_VECTOR_MUL] THEN
    STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_DEF] THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[MATRIX_WORKS];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE THEN
  EXISTS_TAC `\h. linear h /\ positive_definite(matrix h:real^N^N)` THEN
  EXISTS_TAC `\h. orthogonal_transformation h /\
                det(matrix h:real^N^N) = det (matrix fu:real^N^N)` THEN
  EXISTS_TAC `(:real^N)` THEN SIMP_TAC[SUBSET_UNIV] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_THEN `real_sgn(det(matrix f:real^N^N)) = b`
     (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[LINEAR_COMPOSE; MATRIX_COMPOSE; DET_MUL; REAL_SGN_MUL;
                 ORTHOGONAL_TRANSFORMATION_IMP_LINEAR] THEN
    REPEAT STRIP_TAC THEN
    AP_TERM_TAC THEN ASM_SIMP_TAC[real_sgn; DET_POSITIVE_DEFINITE];
    ASM_REWRITE_TAC[HOMOTOPIC_LINEAR_POSITIVE_DEFINITE_MAPS];
    REWRITE_TAC[HOMOTOPIC_SPECIAL_ORTHOGONAL_TRANSFORMATIONS] THEN
    ASM_REWRITE_TAC[HOMOTOPIC_ORTHOGONAL_TRANSFORMATIONS] THEN
    ONCE_REWRITE_TAC[REAL_EQ_SGN_ABS] THEN CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC(REAL_ARITH
       `(a = &1 \/ a = -- &1) /\ (b = &1 \/ b = -- &1) ==> abs a = abs b`) THEN
      CONJ_TAC THEN MATCH_MP_TAC DET_ORTHOGONAL_MATRIX THEN
      ASM_SIMP_TAC[ORTHOGONAL_MATRIX_MATRIX]] THEN
    UNDISCH_TAC `real_sgn(det(matrix f:real^N^N)) = b` THEN
    UNDISCH_THEN `real_sgn(det(matrix g:real^N^N)) = b`
     (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[MATRIX_COMPOSE; ORTHOGONAL_TRANSFORMATION_IMP_LINEAR] THEN
    ASM_REWRITE_TAC[DET_MUL; REAL_SGN_MUL] THEN MATCH_MP_TAC(REAL_RING
     `x = &1 /\ y = &1 ==> a * x = b * y ==> a = b`) THEN
    ASM_SIMP_TAC[REAL_SGN_EQ; DET_POSITIVE_DEFINITE; real_gt]]);;

(* ------------------------------------------------------------------------- *)
(* "If and only if" variants of unrestricted homotopy characterization       *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_ORTHOGONAL_TRANSFORMATIONS_EQ = prove
 (`!f g:real^N->real^N.
        orthogonal_transformation f /\ orthogonal_transformation g
        ==> (homotopic_with
                (\x. T) (sphere (vec 0,&1),sphere (vec 0,&1)) f g <=>
             det(matrix f) = det(matrix g))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_ORTHOGONAL_TRANSFORMATIONS_IMP THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC HOMOTOPIC_WITH_MONO THEN
    EXISTS_TAC `orthogonal_transformation:(real^N->real^N)->bool` THEN
    SIMP_TAC[HOMOTOPIC_ORTHOGONAL_TRANSFORMATIONS_SPHERE; REAL_LT_01] THEN
    ASM_REWRITE_TAC[HOMOTOPIC_ORTHOGONAL_TRANSFORMATIONS]]);;

let HOMOTOPIC_ANTIPODAL_IDENTITY_MAP = prove
 (`homotopic_with (\x. T) (sphere(vec 0,&1),sphere(vec 0,&1))
                  (\x:real^N. --x) (\x. x) <=>
   EVEN(dimindex(:N))`,
  SIMP_TAC[HOMOTOPIC_ORTHOGONAL_TRANSFORMATIONS_EQ;
           ORTHOGONAL_TRANSFORMATION_NEG;
           ORTHOGONAL_TRANSFORMATION_ID] THEN
  SIMP_TAC[MATRIX_NEG; LINEAR_ID; DET_NEG; MATRIX_ID; DET_I] THEN
  REWRITE_TAC[REAL_POW_NEG; REAL_POW_ONE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Complex tangent function.                                                 *)
(* ------------------------------------------------------------------------- *)

let ctan = new_definition
 `ctan z = csin z / ccos z`;;

let CTAN_0 = prove
 (`ctan(Cx(&0)) = Cx(&0)`,
  REWRITE_TAC[ctan; CSIN_0; CCOS_0; COMPLEX_DIV_1]);;

let CTAN_NEG = prove
 (`!z. ctan(--z) = --(ctan z)`,
  REWRITE_TAC[ctan; CSIN_NEG; CCOS_NEG; complex_div; COMPLEX_MUL_LNEG]);;

let CTAN_ADD = prove
 (`!w z. ~(ccos(w) = Cx(&0)) /\
         ~(ccos(z) = Cx(&0)) /\
         ~(ccos(w + z) = Cx(&0))
         ==> ctan(w + z) = (ctan w + ctan z) / (Cx(&1) - ctan(w) * ctan(z))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ctan; CSIN_ADD; CCOS_ADD] THEN
  CONV_TAC COMPLEX_FIELD);;

let CTAN_DOUBLE = prove
 (`!z. ~(ccos(z) = Cx(&0)) /\ ~(ccos(Cx(&2) * z) = Cx(&0))
       ==> ctan(Cx(&2) * z) =
           (Cx(&2) * ctan z) / (Cx(&1) - ctan(z) pow 2)`,
  SIMP_TAC[COMPLEX_MUL_2; CTAN_ADD; COMPLEX_POW_2]);;

let CTAN_SUB = prove
 (`!w z. ~(ccos(w) = Cx(&0)) /\
         ~(ccos(z) = Cx(&0)) /\
         ~(ccos(w - z) = Cx(&0))
         ==> ctan(w - z) = (ctan w - ctan z) / (Cx(&1) + ctan(w) * ctan(z))`,
  SIMP_TAC[complex_sub; CTAN_ADD; CCOS_NEG; CTAN_NEG] THEN
  REWRITE_TAC[COMPLEX_MUL_RNEG; COMPLEX_NEG_NEG]);;

let COMPLEX_ADD_CTAN = prove
 (`!w z. ~(ccos(w) = Cx(&0)) /\
         ~(ccos(z) = Cx(&0))
         ==> ctan(w) + ctan(z) = csin(w + z) / (ccos(w) * ccos(z))`,
  REWRITE_TAC[ctan; CSIN_ADD] THEN CONV_TAC COMPLEX_FIELD);;

let COMPLEX_SUB_CTAN = prove
 (`!w z. ~(ccos(w) = Cx(&0)) /\
         ~(ccos(z) = Cx(&0))
         ==> ctan(w) - ctan(z) = csin(w - z) / (ccos(w) * ccos(z))`,
  REWRITE_TAC[ctan; CSIN_SUB] THEN CONV_TAC COMPLEX_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Analytic properties of tangent function.                                  *)
(* ------------------------------------------------------------------------- *)

let HAS_COMPLEX_DERIVATIVE_CTAN = prove
 (`!z. ~(ccos z = Cx(&0))
       ==> (ctan has_complex_derivative (inv(ccos(z) pow 2))) (at z)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[ctan] THEN COMPLEX_DIFF_TAC THEN
  MP_TAC(SPEC `z:complex` CSIN_CIRCLE) THEN
  POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_FIELD);;

let COMPLEX_DIFFERENTIABLE_AT_CTAN = prove
 (`!z. ~(ccos z = Cx(&0)) ==> ctan complex_differentiable at z`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CTAN]);;

let COMPLEX_DIFFERENTIABLE_WITHIN_CTAN = prove
 (`!s z. ~(ccos z = Cx(&0))
         ==> ctan complex_differentiable (at z within s)`,
  MESON_TAC[COMPLEX_DIFFERENTIABLE_AT_WITHIN;
            COMPLEX_DIFFERENTIABLE_AT_CTAN]);;

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
             HAS_COMPLEX_DERIVATIVE_CTAN)));;

let CONTINUOUS_AT_CTAN = prove
 (`!z. ~(ccos z = Cx(&0)) ==> ctan continuous at z`,
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CTAN;
            HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT]);;

let CONTINUOUS_WITHIN_CTAN = prove
 (`!s z. ~(ccos z = Cx(&0)) ==> ctan continuous (at z within s)`,
  MESON_TAC[CONTINUOUS_AT_WITHIN; CONTINUOUS_AT_CTAN]);;

let CONTINUOUS_ON_CTAN = prove
 (`!s. (!z. z IN s ==> ~(ccos z = Cx(&0))) ==> ctan continuous_on s`,
  MESON_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON; CONTINUOUS_AT_CTAN]);;

let HOLOMORPHIC_ON_CTAN = prove
 (`!s. (!z. z IN s ==> ~(ccos z = Cx(&0))) ==> ctan holomorphic_on s`,
  REWRITE_TAC [holomorphic_on] THEN
  MESON_TAC [HAS_COMPLEX_DERIVATIVE_AT_WITHIN; HAS_COMPLEX_DERIVATIVE_CTAN]);;

(* ------------------------------------------------------------------------- *)
(* Real tangent function.                                                    *)
(* ------------------------------------------------------------------------- *)

let tan_def = new_definition
 `tan(x) = Re(ctan(Cx x))`;;

let CNJ_CTAN = prove
 (`!z. cnj(ctan z) = ctan(cnj z)`,
  REWRITE_TAC[ctan; CNJ_DIV; CNJ_CSIN; CNJ_CCOS]);;

let REAL_TAN = prove
 (`!z. real z ==> real(ctan z)`,
  SIMP_TAC[REAL_CNJ; CNJ_CTAN]);;

let CX_TAN = prove
 (`!x. Cx(tan x) = ctan(Cx x)`,
  REWRITE_TAC[tan_def] THEN MESON_TAC[REAL; REAL_CX; REAL_TAN]);;

let tan = prove
 (`!x. tan x = sin x / cos x`,
  REWRITE_TAC[GSYM CX_INJ; CX_DIV; CX_TAN; CX_SIN; CX_COS; ctan]);;

let TAN_0 = prove
 (`tan(&0) = &0`,
  REWRITE_TAC[GSYM CX_INJ; CX_TAN; CTAN_0]);;

let TAN_PI = prove
 (`tan(pi) = &0`,
  REWRITE_TAC[tan; SIN_PI; real_div; REAL_MUL_LZERO]);;

let TAN_NPI = prove
 (`!n. tan(&n * pi) = &0`,
  REWRITE_TAC[tan; SIN_NPI; real_div; REAL_MUL_LZERO]);;

let TAN_NEG = prove
 (`!x. tan(--x) = --(tan x)`,
  REWRITE_TAC[GSYM CX_INJ; CX_TAN; CX_NEG; CTAN_NEG]);;

let TAN_PERIODIC_PI = prove
 (`!x. tan(x + pi) = tan(x)`,
  REWRITE_TAC[tan; SIN_PERIODIC_PI; COS_PERIODIC_PI; real_div] THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_INV_NEG; REAL_MUL_RNEG; REAL_NEG_NEG]);;

let TAN_PERIODIC_NPI = prove
 (`!x n. tan(x + &n * pi) = tan(x)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
  ASM_REWRITE_TAC[REAL_ADD_ASSOC; TAN_PERIODIC_PI]);;

let TAN_ADD = prove
 (`!x y. ~(cos(x) = &0) /\ ~(cos(y) = &0) /\ ~(cos(x + y) = &0)
         ==> tan(x + y) = (tan(x) + tan(y)) / (&1 - tan(x) * tan(y))`,
  REWRITE_TAC[GSYM CX_INJ; CX_TAN; CX_SIN; CX_COS; CTAN_ADD;
              CX_DIV; CX_ADD; CX_SUB; CX_MUL]);;

let TAN_SUB = prove
 (`!x y. ~(cos(x) = &0) /\ ~(cos(y) = &0) /\ ~(cos(x - y) = &0)
         ==> tan(x - y) = (tan(x) - tan(y)) / (&1 + tan(x) * tan(y))`,
  REWRITE_TAC[GSYM CX_INJ; CX_TAN; CX_SIN; CX_COS; CX_ADD; CTAN_SUB;
              CX_DIV; CX_ADD; CX_SUB; CX_MUL]);;

let TAN_DOUBLE = prove
 (`!x. ~(cos(x) = &0) /\ ~(cos(&2 * x) = &0)
       ==> tan(&2 * x) = (&2 * tan(x)) / (&1 - (tan(x) pow 2))`,
  SIMP_TAC[REAL_MUL_2; TAN_ADD; REAL_POW_2]);;

let REAL_ADD_TAN = prove
 (`!x y. ~(cos(x) = &0) /\ ~(cos(y) = &0)
         ==> tan(x) + tan(y) = sin(x + y) / (cos(x) * cos(y))`,
  REWRITE_TAC[GSYM CX_INJ; CX_TAN; CX_SIN; CX_COS; CX_MUL; CX_ADD; CX_DIV] THEN
  REWRITE_TAC[COMPLEX_ADD_CTAN]);;

let REAL_SUB_TAN = prove
 (`!x y. ~(cos(x) = &0) /\ ~(cos(y) = &0)
         ==> tan(x) - tan(y) = sin(x - y) / (cos(x) * cos(y))`,
  REWRITE_TAC[GSYM CX_INJ; CX_TAN; CX_SIN; CX_COS; CX_MUL; CX_SUB; CX_DIV] THEN
  REWRITE_TAC[COMPLEX_SUB_CTAN]);;

let TAN_PI4 = prove
 (`tan(pi / &4) = &1`,
  REWRITE_TAC[tan; SIN_COS; REAL_ARITH `p / &2 - p / &4 = p / &4`] THEN
  MATCH_MP_TAC REAL_DIV_REFL THEN REWRITE_TAC[COS_EQ_0; PI_NZ; REAL_FIELD
   `p / &4 = (n + &1 / &2) * p <=> p = &0 \/ n = -- &1 / &4`] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[UNWIND_THM2] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
   REAL_ABS_INTEGER_LEMMA)) THEN
  REAL_ARITH_TAC);;

let TAN_POS_PI2 = prove
 (`!x. &0 < x /\ x < pi / &2 ==> &0 < tan x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tan] THEN
  MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
   [MATCH_MP_TAC SIN_POS_PI; MATCH_MP_TAC COS_POS_PI] THEN
  ASM_REAL_ARITH_TAC);;

let TAN_POS_PI2_LE = prove
 (`!x. &0 <= x /\ x < pi / &2 ==> &0 <= tan x`,
  REWRITE_TAC[REAL_LE_LT] THEN MESON_TAC[TAN_0; TAN_POS_PI2]);;

let COS_TAN = prove
 (`!x. abs(x) < pi / &2 ==> cos(x) = &1 / sqrt(&1 + tan(x) pow 2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_FIELD
   `sqrt(s) pow 2 = s /\ c pow 2 * s = &1 /\ ~(&1 + c * sqrt s = &0)
    ==> c = &1 / sqrt s`) THEN
  SUBGOAL_THEN `&0 < &1 + tan x pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `tan x` REAL_LE_SQUARE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN CONJ_TAC THENL
   [REWRITE_TAC[tan] THEN
    MATCH_MP_TAC(REAL_FIELD
     `s pow 2 + c pow 2 = &1 /\ &0 < c
      ==> c pow 2 * (&1 + (s / c) pow 2) = &1`) THEN
    ASM_SIMP_TAC[SIN_CIRCLE; COS_POS_PI; REAL_BOUNDS_LT];
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(&1 + x = &0)`) THEN
    ASM_SIMP_TAC[SIN_CIRCLE; COS_POS_PI; REAL_BOUNDS_LT; SQRT_POS_LT;
                 REAL_LT_MUL]]);;

let SIN_TAN = prove
 (`!x. abs(x) < pi / &2 ==> sin(x) = tan(x) / sqrt(&1 + tan(x) pow 2)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a / b = a * &1 / b`] THEN
  ASM_SIMP_TAC[GSYM COS_TAN] THEN
  ASM_SIMP_TAC[tan; REAL_DIV_RMUL; REAL_LT_IMP_NZ; COS_POS_PI;
               REAL_BOUNDS_LT]);;

(* ------------------------------------------------------------------------- *)
(* Monotonicity theorems for the basic trig functions.                       *)
(* ------------------------------------------------------------------------- *)

let SIN_MONO_LT = prove
 (`!x y. --(pi / &2) <= x /\ x < y /\ y <= pi / &2 ==> sin(x) < sin(y)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  REWRITE_TAC[REAL_SUB_SIN; REAL_ARITH `&0 < &2 * x <=> &0 < x`] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC SIN_POS_PI; MATCH_MP_TAC COS_POS_PI] THEN
  ASM_REAL_ARITH_TAC);;

let SIN_MONO_LE = prove
 (`!x y. --(pi / &2) <= x /\ x <= y /\ y <= pi / &2 ==> sin(x) <= sin(y)`,
  MESON_TAC[SIN_MONO_LT; REAL_LE_LT]);;

let SIN_MONO_LT_EQ = prove
 (`!x y. --(pi / &2) <= x /\ x <= pi / &2 /\ --(pi / &2) <= y /\ y <= pi / &2
         ==> (sin(x) < sin(y) <=> x < y)`,
  MESON_TAC[REAL_NOT_LE; SIN_MONO_LT; SIN_MONO_LE]);;

let SIN_MONO_LE_EQ = prove
 (`!x y. --(pi / &2) <= x /\ x <= pi / &2 /\ --(pi / &2) <= y /\ y <= pi / &2
         ==> (sin(x) <= sin(y) <=> x <= y)`,
  MESON_TAC[REAL_NOT_LE; SIN_MONO_LT; SIN_MONO_LE]);;

let SIN_INJ_PI = prove
 (`!x y. --(pi / &2) <= x /\ x <= pi / &2 /\
         --(pi / &2) <= y /\ y <= pi / &2 /\
         sin(x) = sin(y)
         ==> x = y`,
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN MESON_TAC[SIN_MONO_LE_EQ]);;

let COS_MONO_LT = prove
 (`!x y. &0 <= x /\ x < y /\ y <= pi ==> cos(y) < cos(x)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  REWRITE_TAC[REAL_SUB_COS; REAL_ARITH `&0 < &2 * x <=> &0 < x`] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN MATCH_MP_TAC SIN_POS_PI THEN
  ASM_REAL_ARITH_TAC);;

let COS_MONO_LE = prove
 (`!x y. &0 <= x /\ x <= y /\ y <= pi ==> cos(y) <= cos(x)`,
  MESON_TAC[COS_MONO_LT; REAL_LE_LT]);;

let COS_MONO_LT_EQ = prove
 (`!x y. &0 <= x /\ x <= pi /\ &0 <= y /\ y <= pi
         ==> (cos(x) < cos(y) <=> y < x)`,
  MESON_TAC[REAL_NOT_LE; COS_MONO_LT; COS_MONO_LE]);;

let COS_MONO_LE_EQ = prove
 (`!x y. &0 <= x /\ x <= pi /\ &0 <= y /\ y <= pi
         ==> (cos(x) <= cos(y) <=> y <= x)`,
  MESON_TAC[REAL_NOT_LE; COS_MONO_LT; COS_MONO_LE]);;

let COS_INJ_PI = prove
 (`!x y. &0 <= x /\ x <= pi /\ &0 <= y /\ y <= pi /\ cos(x) = cos(y)
         ==> x = y`,
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN MESON_TAC[COS_MONO_LE_EQ]);;

let REAL_ABS_COS_MONO_LE_EQ = prove
 (`!x y. abs(x) <= pi / &2 /\ abs(y) <= pi / &2
         ==> (abs(cos x) <= abs(cos y) <=> abs y <= abs x)`,
  MAP_EVERY (fun t ->
    MATCH_MP_TAC(MESON[REAL_LE_NEGTOTAL]
     `(!x. P(--x) <=> P x) /\ (!x. &0 <= x ==> P x) ==> !x. P x`) THEN
    REWRITE_TAC[REAL_ABS_NEG; COS_NEG] THEN X_GEN_TAC t THEN DISCH_TAC)
   [`x:real`; `y:real`] THEN
  SIMP_TAC[REWRITE_RULE[REAL_BOUNDS_LE] COS_POS_PI_LE;
           REAL_ARITH `&0 <= cos x ==> abs(cos x) = cos x`] THEN
  REWRITE_TAC[REAL_BOUNDS_LE] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[real_abs] THEN MATCH_MP_TAC COS_MONO_LE_EQ THEN
  ASM_REAL_ARITH_TAC);;

let TAN_MONO_LT = prove
 (`!x y. --(pi / &2) < x /\ x < y /\ y < pi / &2 ==> tan(x) < tan(y)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [GSYM REAL_SUB_LT] THEN
  SUBGOAL_THEN `&0 < cos(x) /\ &0 < cos(y)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC COS_POS_PI;
    ASM_SIMP_TAC[REAL_LT_IMP_NZ; REAL_SUB_TAN] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_LT_MUL] THEN
    MATCH_MP_TAC SIN_POS_PI] THEN
  ASM_REAL_ARITH_TAC);;

let TAN_MONO_LE = prove
 (`!x y. --(pi / &2) < x /\ x <= y /\ y < pi / &2 ==> tan(x) <= tan(y)`,
  REWRITE_TAC[REAL_LE_LT] THEN MESON_TAC[TAN_MONO_LT]);;

let TAN_MONO_LT_EQ = prove
 (`!x y. --(pi / &2) < x /\ x < pi / &2 /\ --(pi / &2) < y /\ y < pi / &2
         ==> (tan(x) < tan(y) <=> x < y)`,
  MESON_TAC[REAL_NOT_LE; TAN_MONO_LT; TAN_MONO_LE]);;

let TAN_MONO_LE_EQ = prove
 (`!x y. --(pi / &2) < x /\ x < pi / &2 /\ --(pi / &2) < y /\ y < pi / &2
         ==> (tan(x) <= tan(y) <=> x <= y)`,
  MESON_TAC[REAL_NOT_LE; TAN_MONO_LT; TAN_MONO_LE]);;

let TAN_BOUND_PI2 = prove
 (`!x. abs(x) < pi / &4 ==> abs(tan x) < &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM TAN_PI4] THEN
  REWRITE_TAC[GSYM TAN_NEG; REAL_ARITH `abs(x) < a <=> --a < x /\ x < a`] THEN
  CONJ_TAC THEN MATCH_MP_TAC TAN_MONO_LT THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

let TAN_COT = prove
 (`!x. tan(pi / &2 - x) = inv(tan x)`,
  REWRITE_TAC[tan; SIN_SUB; COS_SUB; SIN_PI2; COS_PI2; REAL_INV_DIV] THEN
  GEN_TAC THEN BINOP_TAC THEN REAL_ARITH_TAC);;

let REAL_ABS_SIN_BOUND_LT = prove
 (`!x. ~(x = &0) ==> abs(sin x) < abs x`,
  MATCH_MP_TAC(MESON[SIN_NEG; REAL_ABS_NEG; REAL_LT_NEGTOTAL]
   `(!x. &0 < x ==> abs(sin x) < abs x)
    ==> !x. ~(x = &0) ==> abs(sin x) < abs x`) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `a < x ==> a < abs x`) THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs s <= &1 /\ (x <= &1 ==> abs(s) < x) ==> abs s < x`) THEN
  REWRITE_TAC[SIN_BOUND] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`1`; `Cx x`] TAYLOR_CSIN) THEN
  REWRITE_TAC[num_CONV `1`; VSUM_CLAUSES_NUMSEG; IM_CX] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_ABS_NUM; REAL_EXP_0; COMPLEX_POW_1; complex_pow;
              COMPLEX_DIV_1] THEN
  REWRITE_TAC[GSYM CX_SIN; GSYM CX_MUL; GSYM CX_NEG; GSYM CX_POW; GSYM CX_DIV;
              GSYM CX_SUB; GSYM CX_ADD; REAL_MUL_LID; COMPLEX_NORM_CX] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a < x /\ e < a ==> abs(s - (x + -- &1 * a)) <= e ==> abs s < x`) THEN
  ASM_SIMP_TAC[real_abs; REAL_LT_IMP_LE] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < y /\ x <= y pow 1 ==> x / &6 < y`);
    MATCH_MP_TAC(REAL_ARITH `&0 < x /\ x <= y ==> x / &24 < y / &6`)] THEN
  ASM_SIMP_TAC[REAL_POW_LT] THEN MATCH_MP_TAC REAL_POW_MONO_INV THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC);;

let REAL_ABS_SIN_BOUND_LE = prove
 (`!x. abs(sin x) <= abs x`,
  GEN_TAC THEN ASM_CASES_TAC `x = &0` THEN
  ASM_SIMP_TAC[REAL_ABS_SIN_BOUND_LT; REAL_LT_IMP_LE; SIN_0; REAL_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Approximation to pi.                                                      *)
(* ------------------------------------------------------------------------- *)

let SIN_PI6_STRADDLE = prove
 (`!a b. &0 <= a /\ a <= b /\ b <= &4 /\
         sin(a / &6) <= &1 / &2 /\ &1 / &2 <= sin(b / &6)
         ==> a <= pi /\ pi <= b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`pi / &6`; `b / &6`] SIN_MONO_LE_EQ) THEN
  MP_TAC(SPECL [`a / &6`; `pi / &6`] SIN_MONO_LE_EQ) THEN
  ASM_REWRITE_TAC[SIN_PI6] THEN
  SUBGOAL_THEN `!x. &0 < x /\ x < &7 / &5 ==> &0 < sin x`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`0`; `Cx(x)`] TAYLOR_CSIN) THEN
    REWRITE_TAC[VSUM_SING_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[COMPLEX_DIV_1; COMPLEX_POW_1; complex_pow] THEN
    REWRITE_TAC[COMPLEX_MUL_LID; GSYM CX_SIN; GSYM CX_SUB] THEN
    REWRITE_TAC[IM_CX; COMPLEX_NORM_CX; REAL_ABS_NUM; REAL_EXP_0] THEN
    MATCH_MP_TAC(REAL_ARITH
     `e + d < a ==> abs(s - a) <= d ==> e < s`) THEN
    ASM_SIMP_TAC[real_abs; real_pow; REAL_MUL_LID; REAL_LT_IMP_LE] THEN
    SIMP_TAC[REAL_ARITH `&0 + x pow 3 / &2 < x <=> x * x pow 2 < x * &2`] THEN
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ] THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `(&7 / &5) pow 2` THEN
    ASM_SIMP_TAC[REAL_POW_LT2; ARITH_EQ; REAL_LT_IMP_LE] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    DISCH_THEN(MP_TAC o SPEC `pi`) THEN
    SIMP_TAC[SIN_PI; REAL_LT_REFL; PI_POS; REAL_NOT_LT] THEN
    ASM_REAL_ARITH_TAC]);;

let PI_APPROX_32 = prove
 (`abs(pi - &13493037705 / &4294967296) <= inv(&2 pow 32)`,
  REWRITE_TAC[REAL_ARITH `abs(x - a) <= e <=> a - e <= x /\ x <= a + e`] THEN
  MATCH_MP_TAC SIN_PI6_STRADDLE THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`5`; `Cx(&1686629713 / &3221225472)`] TAYLOR_CSIN);
    MP_TAC(SPECL [`5`; `Cx(&6746518853 / &12884901888)`] TAYLOR_CSIN)] THEN
  SIMP_TAC[COMPLEX_NORM_CX; GSYM CX_POW; GSYM CX_DIV; GSYM CX_MUL;
           GSYM CX_NEG; VSUM_CX; FINITE_NUMSEG; GSYM CX_SIN; GSYM CX_SUB] THEN
  REWRITE_TAC[IM_CX; REAL_ABS_NUM; REAL_EXP_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; GSYM REAL_POW_POW] THEN
  REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_MUL; real_div] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  CONV_TAC(ONCE_DEPTH_CONV HORNER_SUM_CONV) THEN REAL_ARITH_TAC);;

let PI2_BOUNDS = prove
 (`&0 < pi / &2 /\ pi / &2 < &2`,
  MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Complex logarithms (the conventional principal value).                    *)
(* ------------------------------------------------------------------------- *)

let clog = new_definition
 `clog z = @w. cexp(w) = z /\ --pi < Im(w) /\ Im(w) <= pi`;;

let EXISTS_COMPLEX' = prove
 (`!P. (?z. P (Re z) (Im z)) <=> ?x y. P x y`,
  MESON_TAC[RE; IM; COMPLEX]);;

let CLOG_WORKS = prove
 (`!z. ~(z = Cx(&0))
       ==> cexp(clog z) = z /\ --pi < Im(clog z) /\ Im(clog z) <= pi`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[clog] THEN CONV_TAC SELECT_CONV THEN
  MP_TAC(SPEC `z / Cx(norm z)` COMPLEX_UNIMODULAR_POLAR) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX] THEN
    ASM_SIMP_TAC[REAL_ABS_NORM; REAL_DIV_REFL; COMPLEX_NORM_ZERO];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `x:real` SINCOS_PRINCIPAL_VALUE) THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `complex(log(norm(z:complex)),y)` THEN
  ASM_REWRITE_TAC[RE; IM; CEXP_COMPLEX] THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM)) THEN
  ASM_SIMP_TAC[EXP_LOG; COMPLEX_NORM_NZ; COMPLEX_DIV_LMUL;
               COMPLEX_NORM_ZERO; CX_INJ]);;

let CEXP_CLOG = prove
 (`!z. ~(z = Cx(&0)) ==> cexp(clog z) = z`,
  SIMP_TAC[CLOG_WORKS]);;

let CLOG_CEXP = prove
 (`!z. --pi < Im(z) /\ Im(z) <= pi ==> clog(cexp z) = z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[clog] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `w:complex` THEN
  EQ_TAC THEN ASM_SIMP_TAC[] THEN REWRITE_TAC[CEXP_EQ] THEN
  REWRITE_TAC[IMP_CONJ] THEN DISCH_THEN(X_CHOOSE_THEN `n:real`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  REWRITE_TAC[IM_ADD; IM_MUL_II; RE_CX] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `n = &0` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
  REWRITE_TAC[REAL_MUL_RZERO; COMPLEX_ADD_RID; COMPLEX_MUL_LZERO] THEN
  SUBGOAL_THEN `abs(n * pi) < &1 * pi` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_MUL; REAL_LT_RMUL_EQ; PI_POS; REAL_ABS_PI] THEN
  ASM_MESON_TAC[REAL_ABS_INTEGER_LEMMA; REAL_NOT_LT]);;

let CLOG_EQ = prove
 (`!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0)) ==> (clog w = clog z <=> w = z)`,
  MESON_TAC[CEXP_CLOG]);;

let CLOG_UNIQUE = prove
 (`!w z. --pi < Im(z) /\ Im(z) <= pi /\ cexp(z) = w ==> clog w = z`,
  MESON_TAC[CLOG_CEXP]);;

let RE_CLOG = prove
 (`!z. ~(z = Cx(&0)) ==> Re(clog z) = log(norm z)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM
   (MP_TAC o AP_TERM `norm:complex->real` o MATCH_MP CEXP_CLOG) THEN
  REWRITE_TAC[NORM_CEXP] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[LOG_EXP]);;

let EXISTS_COMPLEX_ROOT = prove
 (`!a n. ~(n = 0) ==> ?z. z pow n = a`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `a = Cx(&0)` THENL
   [EXISTS_TAC `Cx(&0)` THEN ASM_REWRITE_TAC[COMPLEX_POW_ZERO];
    EXISTS_TAC `cexp(clog(a) / Cx(&n))` THEN REWRITE_TAC[GSYM CEXP_N] THEN
    ASM_SIMP_TAC[COMPLEX_DIV_LMUL; CX_INJ; REAL_OF_NUM_EQ; CEXP_CLOG]]);;

(* ------------------------------------------------------------------------- *)
(* Derivative of clog away from the branch cut.                              *)
(* ------------------------------------------------------------------------- *)

let HAS_COMPLEX_DERIVATIVE_CLOG = prove
 (`!z. (Im(z) = &0 ==> &0 < Re(z))
       ==> (clog has_complex_derivative inv(z)) (at z)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_INVERSE_STRONG_X THEN
  EXISTS_TAC `cexp` THEN
  EXISTS_TAC `{w | --pi < Im(w) /\ Im(w) < pi}` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_CASES_TAC `z = Cx(&0)` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN
     ASM_REWRITE_TAC[RE_CX; IM_CX; REAL_LT_REFL];
     ALL_TAC] THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_CEXP; CEXP_CLOG; CLOG_CEXP; REAL_LT_IMP_LE] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SET_RULE `{x | p x /\ q x} = {x | p x} INTER {x | q x}`] THEN
    MATCH_MP_TAC OPEN_INTER THEN
    REWRITE_TAC[REAL_ARITH `--x < w <=> w > --x`] THEN
    REWRITE_TAC[OPEN_HALFSPACE_IM_LT; OPEN_HALFSPACE_IM_GT];
    ASM_SIMP_TAC[CLOG_WORKS];
    ASM_SIMP_TAC[CLOG_WORKS; REAL_LT_LE] THEN
    DISCH_THEN(fun th ->
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o MATCH_MP CEXP_CLOG) THEN
      POP_ASSUM MP_TAC THEN ASSUME_TAC th) THEN
    ASM_REWRITE_TAC[EULER; COS_PI; SIN_PI; COMPLEX_MUL_RZERO] THEN
    REWRITE_TAC[COMPLEX_ADD_RID; CX_NEG; COMPLEX_MUL_RNEG] THEN
    REWRITE_TAC[COMPLEX_MUL_RID; IM_NEG; IM_CX; RE_NEG; RE_CX] THEN
    MP_TAC(SPEC `Re(clog z)` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC;
    ASM_MESON_TAC[HAS_COMPLEX_DERIVATIVE_CEXP; CEXP_CLOG]]);;

let COMPLEX_DIFFERENTIABLE_AT_CLOG = prove
 (`!z. (Im(z) = &0 ==> &0 < Re(z)) ==> clog complex_differentiable at z`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CLOG]);;

let COMPLEX_DIFFERENTIABLE_WITHIN_CLOG = prove
 (`!s z. (Im(z) = &0 ==> &0 < Re(z))
         ==> clog complex_differentiable (at z within s)`,
  MESON_TAC[COMPLEX_DIFFERENTIABLE_AT_WITHIN;
            COMPLEX_DIFFERENTIABLE_AT_CLOG]);;

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
             HAS_COMPLEX_DERIVATIVE_CLOG)));;

let CONTINUOUS_AT_CLOG = prove
 (`!z. (Im(z) = &0 ==> &0 < Re(z)) ==> clog continuous at z`,
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CLOG;
            HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT]);;

let CONTINUOUS_WITHIN_CLOG = prove
 (`!s z. (Im(z) = &0 ==> &0 < Re(z)) ==> clog continuous (at z within s)`,
  MESON_TAC[CONTINUOUS_AT_WITHIN; CONTINUOUS_AT_CLOG]);;

let CONTINUOUS_ON_CLOG = prove
 (`!s. (!z. z IN s /\ Im(z) = &0 ==> &0 < Re(z)) ==> clog continuous_on s`,
  MESON_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON; CONTINUOUS_AT_CLOG]);;

let HOLOMORPHIC_ON_CLOG = prove
 (`!s. (!z. z IN s /\ Im(z) = &0 ==> &0 < Re(z)) ==> clog holomorphic_on s`,
  REWRITE_TAC [holomorphic_on] THEN
  MESON_TAC [HAS_COMPLEX_DERIVATIVE_AT_WITHIN; HAS_COMPLEX_DERIVATIVE_CLOG]);;

(* ------------------------------------------------------------------------- *)
(* Relation to real log.                                                     *)
(* ------------------------------------------------------------------------- *)

let CX_LOG = prove
 (`!z. &0 < z ==> Cx(log z) = clog(Cx z)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(fun th ->
   GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
     [SYM(MATCH_MP EXP_LOG th)]) THEN
  REWRITE_TAC[CX_EXP] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC CLOG_CEXP THEN REWRITE_TAC[IM_CX] THEN
  MP_TAC PI_POS THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Quadrant-type results for clog.                                           *)
(* ------------------------------------------------------------------------- *)

let RE_CLOG_POS_LT = prove
 (`!z. ~(z = Cx(&0)) ==> (abs(Im(clog z)) < pi / &2 <=> &0 < Re(z))`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CLOG_WORKS) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [SYM th])
    MP_TAC) THEN
  SIMP_TAC[RE_CEXP; REAL_LT_MUL_EQ; REAL_EXP_POS_LT] THEN
  SPEC_TAC(`clog z`,`z:complex`) THEN GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `--p < x /\ x <= p
    ==> --(p / &2) < x /\ x < p / &2 \/
        --(p / &2) <= p + x /\ p + x <= p / &2 \/
        --(p / &2) <= x - p /\ x - p <= p / &2`)) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  (FIRST_ASSUM(MP_TAC o MATCH_MP COS_POS_PI) ORELSE
   FIRST_ASSUM(MP_TAC o MATCH_MP COS_POS_PI_LE)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[COS_ADD; COS_SUB; COS_PI; SIN_PI] THEN
  REAL_ARITH_TAC);;

let RE_CLOG_POS_LE = prove
 (`!z. ~(z = Cx(&0)) ==> (abs(Im(clog z)) <= pi / &2 <=> &0 <= Re(z))`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CLOG_WORKS) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [SYM th])
    MP_TAC) THEN
  SIMP_TAC[RE_CEXP; REAL_LE_MUL_EQ; REAL_EXP_POS_LT] THEN
  SPEC_TAC(`clog z`,`z:complex`) THEN GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `--p < x /\ x <= p
    ==> --(p / &2) <= x /\ x <= p / &2 \/
        --(p / &2) < p + x /\ p + x < p / &2 \/
        --(p / &2) < x - p /\ x - p < p / &2`)) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  (FIRST_ASSUM(MP_TAC o MATCH_MP COS_POS_PI) ORELSE
   FIRST_ASSUM(MP_TAC o MATCH_MP COS_POS_PI_LE)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[COS_ADD; COS_SUB; COS_PI; SIN_PI] THEN
  REAL_ARITH_TAC);;

let IM_CLOG_POS_LT = prove
 (`!z. ~(z = Cx(&0)) ==> (&0 < Im(clog z) /\ Im(clog z) < pi <=> &0 < Im(z))`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CLOG_WORKS) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [SYM th])
    MP_TAC) THEN
  SIMP_TAC[IM_CEXP; REAL_LT_MUL_EQ; REAL_EXP_POS_LT] THEN
  SPEC_TAC(`clog z`,`z:complex`) THEN GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `--p < x /\ x <= p
    ==> &0 < x /\ x < p \/
        &0 <= x + p /\ x + p <= p \/
        &0 <= x - p /\ x - p <= p`)) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  (FIRST_ASSUM(MP_TAC o MATCH_MP SIN_POS_PI) ORELSE
   FIRST_ASSUM(MP_TAC o MATCH_MP SIN_POS_PI_LE)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[SIN_ADD; SIN_SUB; COS_PI; SIN_PI] THEN
  REAL_ARITH_TAC);;

let IM_CLOG_POS_LE = prove
 (`!z. ~(z = Cx(&0)) ==> (&0 <= Im(clog z) <=> &0 <= Im(z))`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CLOG_WORKS) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [SYM th])
    MP_TAC) THEN
  SIMP_TAC[IM_CEXP; REAL_LE_MUL_EQ; REAL_EXP_POS_LT] THEN
  SPEC_TAC(`clog z`,`z:complex`) THEN GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `--p < x /\ x <= p
    ==> &0 <= x /\ x <= p \/
        &0 < x + p /\ x + p < p \/
        &0 < p - x /\ p - x < p`)) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  (FIRST_ASSUM(MP_TAC o MATCH_MP SIN_POS_PI) ORELSE
   FIRST_ASSUM(MP_TAC o MATCH_MP SIN_POS_PI_LE)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[SIN_ADD; SIN_SUB; COS_PI; SIN_PI] THEN
  REAL_ARITH_TAC);;

let RE_CLOG_POS_LT_IMP = prove
 (`!z. &0 < Re(z) ==> abs(Im(clog z)) < pi / &2`,
  GEN_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THEN
  ASM_SIMP_TAC[RE_CLOG_POS_LT; RE_CX; REAL_LT_REFL]);;

let IM_CLOG_POS_LT_IMP = prove
 (`!z. &0 < Im(z) ==> &0 < Im(clog z) /\ Im(clog z) < pi`,
  GEN_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THEN
  ASM_SIMP_TAC[IM_CLOG_POS_LT; IM_CX; REAL_LT_REFL]);;

let IM_CLOG_EQ_0 = prove
 (`!z. ~(z = Cx(&0)) ==> (Im(clog z) = &0 <=> &0 < Re(z) /\ Im(z) = &0)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
   [REAL_ARITH `z = &0 <=> &0 <= z /\ ~(&0 < z)`] THEN
  ASM_SIMP_TAC[GSYM RE_CLOG_POS_LT; GSYM IM_CLOG_POS_LE;
               GSYM IM_CLOG_POS_LT] THEN
  MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let IM_CLOG_EQ_PI = prove
 (`!z. ~(z = Cx(&0)) ==> (Im(clog z) = pi <=> Re(z) < &0 /\ Im(z) = &0)`,
  SIMP_TAC[PI_POS; RE_CLOG_POS_LE; IM_CLOG_POS_LE; IM_CLOG_POS_LT; CLOG_WORKS;
           REAL_ARITH `&0 < pi ==> (x = pi <=> (&0 <= x /\ x <= pi) /\
                            ~(abs x <= pi / &2) /\ ~(&0 < x /\ x < pi))`] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Various properties.                                                       *)
(* ------------------------------------------------------------------------- *)

let CNJ_CLOG = prove
 (`!z. (Im z = &0 ==> &0 < Re z) ==> cnj(clog z) = clog(cnj z)`,
  GEN_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THEN
  ASM_REWRITE_TAC[RE_CX; IM_CX; REAL_LT_REFL] THEN
  DISCH_TAC THEN MATCH_MP_TAC COMPLEX_EQ_CEXP THEN
  REWRITE_TAC[GSYM CNJ_CEXP] THEN
  ASM_SIMP_TAC[CEXP_CLOG; CNJ_EQ_CX; IM_CNJ] THEN
  MATCH_MP_TAC(REAL_ARITH
   `(--p < x /\ x <= p) /\ (--p < y /\ y <= p) /\
    ~(x = p /\ y = p)
    ==> abs(--x - y) < &2 * p`) THEN
  ASM_SIMP_TAC[IM_CLOG_EQ_PI; CNJ_EQ_CX; CLOG_WORKS] THEN
  ASM_REAL_ARITH_TAC);;

let CLOG_INV = prove
 (`!z. (Im(z) = &0 ==> &0 < Re z) ==> clog(inv z) = --(clog z)`,
  GEN_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THEN
  ASM_REWRITE_TAC[RE_CX; IM_CX; REAL_LT_REFL] THEN
  STRIP_TAC THEN MATCH_MP_TAC COMPLEX_EQ_CEXP THEN
  ASM_SIMP_TAC[CEXP_CLOG; CEXP_NEG; COMPLEX_INV_EQ_0] THEN
  REWRITE_TAC[IM_NEG; REAL_SUB_RNEG] THEN
  MATCH_MP_TAC(REAL_ARITH
   `--pi < x /\ x <= pi /\ --pi < y /\ y <= pi /\
    ~(x = pi /\ y = pi) ==> abs(x + y) < &2 * pi`) THEN
  ASM_SIMP_TAC[CLOG_WORKS; COMPLEX_INV_EQ_0; IM_CLOG_EQ_PI] THEN
  UNDISCH_TAC `Im z = &0 ==> &0 < Re z` THEN
  ASM_CASES_TAC `Im z = &0` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let CLOG_1 = prove
 (`clog(Cx(&1)) = Cx(&0)`,
  REWRITE_TAC[GSYM CEXP_0] THEN MATCH_MP_TAC CLOG_CEXP THEN
  REWRITE_TAC[IM_CX] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let CLOG_NEG_1 = prove
 (`clog(--Cx(&1)) = ii * Cx pi`,
  MATCH_MP_TAC COMPLEX_EQ_CEXP THEN REWRITE_TAC[GSYM CX_NEG] THEN
  SIMP_TAC[CEXP_EULER; GSYM CX_COS; GSYM CX_SIN; IM_MUL_II; IM_CX; RE_CX] THEN
  REWRITE_TAC[COS_PI; SIN_PI; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID] THEN
  SIMP_TAC[CLOG_WORKS; COMPLEX_RING `~(Cx(-- &1) = Cx(&0))`;
           REAL_ARITH `--pi < x /\ x <= pi ==> abs(x - pi) < &2 * pi`]);;

let CLOG_II = prove
 (`clog ii = ii * Cx(pi / &2)`,
  MP_TAC(SPEC `ii * Cx(pi / &2)` CLOG_CEXP) THEN
  SIMP_TAC[CEXP_EULER; GSYM CX_COS; GSYM CX_SIN; IM_MUL_II; IM_CX; RE_CX] THEN
  REWRITE_TAC[COS_PI2; SIN_PI2] THEN ANTS_TAC THENL
   [MP_TAC PI_POS THEN REAL_ARITH_TAC;
    REWRITE_TAC[COMPLEX_ADD_LID; COMPLEX_MUL_RID]]);;

let CLOG_NEG_II = prove
 (`clog(--ii) = --ii * Cx(pi / &2)`,
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [COMPLEX_FIELD `--ii = inv ii`] THEN
  SIMP_TAC[CLOG_INV; RE_II; IM_II; REAL_OF_NUM_EQ; ARITH; CLOG_II] THEN
  REWRITE_TAC[COMPLEX_MUL_LNEG]);;

(* ------------------------------------------------------------------------- *)
(* Relation between square root and exp/log, and hence its derivative.       *)
(* ------------------------------------------------------------------------- *)

let CSQRT_CEXP_CLOG = prove
 (`!z. ~(z = Cx(&0)) ==> csqrt z = cexp(clog(z) / Cx(&2))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CSQRT_UNIQUE THEN
  REWRITE_TAC[GSYM CEXP_N; RE_CEXP; IM_CEXP] THEN
  ASM_SIMP_TAC[COMPLEX_DIV_LMUL; CX_INJ; REAL_OF_NUM_EQ; ARITH; CEXP_CLOG] THEN
  SIMP_TAC[REAL_LT_MUL_EQ; REAL_EXP_POS_LT; REAL_LE_MUL_EQ] THEN
  REWRITE_TAC[REAL_ENTIRE; REAL_EXP_NZ; IM_DIV_CX] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o CONJUNCT2 o MATCH_MP CLOG_WORKS) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
   [DISJ1_TAC THEN MATCH_MP_TAC COS_POS_PI THEN
    ASM_REAL_ARITH_TAC;
    DISJ2_TAC THEN ASM_REWRITE_TAC[COS_PI2; SIN_PI2; REAL_POS]]);;

let CNJ_CSQRT = prove
 (`!z. (Im z = &0 ==> &0 <= Re(z)) ==> cnj(csqrt z) = csqrt(cnj z)`,
  GEN_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THEN
  ASM_REWRITE_TAC[CSQRT_0; CNJ_CX] THEN DISCH_TAC THEN
  SUBGOAL_THEN `Im z = &0 ==> &0 < Re(z)` ASSUME_TAC THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN
    REWRITE_TAC[COMPLEX_EQ; IM_CX; RE_CX] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[RE_CX; IM_CX; REAL_LT_REFL] THEN
    ASM_SIMP_TAC[CSQRT_CEXP_CLOG; CNJ_CEXP; CNJ_CLOG;
                 CNJ_DIV; CNJ_EQ_CX; CNJ_CX]]);;

let HAS_COMPLEX_DERIVATIVE_CSQRT = prove
 (`!z. (Im z = &0 ==> &0 < Re(z))
       ==> (csqrt has_complex_derivative inv(Cx(&2) * csqrt z)) (at z)`,
  GEN_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THEN
  ASM_REWRITE_TAC[IM_CX; RE_CX; REAL_LT_REFL] THEN DISCH_TAC THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT THEN
  MAP_EVERY EXISTS_TAC [`\z. cexp(clog(z) / Cx(&2))`; `norm(z:complex)`] THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_NZ] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CSQRT_CEXP_CLOG THEN REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN NORM_ARITH_TAC;
    COMPLEX_DIFF_TAC THEN ASM_SIMP_TAC[GSYM CSQRT_CEXP_CLOG] THEN
    UNDISCH_TAC `~(z = Cx(&0))` THEN MP_TAC(SPEC `z:complex` CSQRT) THEN
    CONV_TAC COMPLEX_FIELD]);;

let COMPLEX_DIFFERENTIABLE_AT_CSQRT = prove
 (`!z. (Im z = &0 ==> &0 < Re(z)) ==> csqrt complex_differentiable at z`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CSQRT]);;

let COMPLEX_DIFFERENTIABLE_WITHIN_CSQRT = prove
 (`!s z. (Im z = &0 ==> &0 < Re(z))
         ==> csqrt complex_differentiable (at z within s)`,
  MESON_TAC[COMPLEX_DIFFERENTIABLE_AT_WITHIN;
            COMPLEX_DIFFERENTIABLE_AT_CSQRT]);;

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
             HAS_COMPLEX_DERIVATIVE_CSQRT)));;

let CONTINUOUS_AT_CSQRT = prove
 (`!z. (Im z = &0 ==> &0 < Re(z)) ==> csqrt continuous at z`,
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CSQRT;
            HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT]);;

let CONTINUOUS_WITHIN_CSQRT = prove
 (`!s z. (Im z = &0 ==> &0 < Re(z)) ==> csqrt continuous (at z within s)`,
  MESON_TAC[CONTINUOUS_AT_WITHIN; CONTINUOUS_AT_CSQRT]);;

let CONTINUOUS_ON_CSQRT = prove
 (`!s. (!z. z IN s /\ Im z = &0 ==> &0 < Re(z)) ==> csqrt continuous_on s`,
  MESON_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON; CONTINUOUS_AT_CSQRT]);;

let HOLOMORPHIC_ON_CSQRT = prove
 (`!s. (!z. z IN s /\ Im(z) = &0 ==> &0 < Re(z)) ==> csqrt holomorphic_on s`,
  REWRITE_TAC [holomorphic_on] THEN
  MESON_TAC [HAS_COMPLEX_DERIVATIVE_AT_WITHIN; HAS_COMPLEX_DERIVATIVE_CSQRT]);;

let CONTINUOUS_WITHIN_CSQRT_POSREAL = prove
 (`!z. csqrt continuous (at z within {w | real w /\ &0 <= Re(w)})`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `Im z = &0 ==> &0 < Re(z)` THENL
   [ASM_SIMP_TAC[CONTINUOUS_WITHIN_CSQRT]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[NOT_IMP; REAL_NOT_LT] THEN
  REWRITE_TAC[REAL_ARITH `x <= &0 <=> x < &0 \/ x = &0`] THEN STRIP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_WITHIN_CLOSED_NONTRIVIAL THEN
    REWRITE_TAC[SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
    SIMP_TAC[CLOSED_REAL_SET; CLOSED_INTER; IN_INTER; IN_ELIM_THM;
             REWRITE_RULE[real_ge] CLOSED_HALFSPACE_RE_GE] THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `z = Cx(&0)` SUBST_ALL_TAC THENL
     [ASM_REWRITE_TAC[COMPLEX_EQ; RE_CX; IM_CX]; ALL_TAC] THEN
    REWRITE_TAC[continuous_within] THEN
    REWRITE_TAC[IN_ELIM_THM; IMP_CONJ; FORALL_REAL; RE_CX] THEN
    SIMP_TAC[GSYM CX_SQRT; REAL_LE_REFL] THEN
    SIMP_TAC[dist; GSYM CX_SUB; COMPLEX_NORM_CX; SQRT_0; REAL_SUB_RZERO] THEN
    X_GEN_TAC `e:real` THEN STRIP_TAC THEN EXISTS_TAC `(e:real) pow 2` THEN
    ASM_SIMP_TAC[REAL_POW_LT] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `e = sqrt(e pow 2)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE];
      ASM_SIMP_TAC[real_abs; SQRT_POS_LE]] THEN
    MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Complex powers.                                                           *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("cpow",(24,"left"));;

let cpow = new_definition
 `w cpow z = if w = Cx(&0) then Cx(&0)
             else cexp(z * clog w)`;;

let CPOW_0 = prove
 (`!z. Cx(&0) cpow z = Cx(&0)`,
  REWRITE_TAC[cpow]);;

let CPOW_N = prove
 (`!z. z cpow (Cx(&n)) = if z = Cx(&0) then Cx(&0) else z pow n`,
  GEN_TAC THEN REWRITE_TAC[cpow] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[CEXP_N; CEXP_CLOG]);;

let CPOW_1 = prove
 (`!z. Cx(&1) cpow z = Cx(&1)`,
  REWRITE_TAC[cpow; CX_INJ; REAL_OF_NUM_EQ; ARITH_EQ; CLOG_1] THEN
  REWRITE_TAC[CEXP_0; COMPLEX_MUL_RZERO]);;

let CPOW_ADD = prove
 (`!w z1 z2. w cpow (z1 + z2) = w cpow z1 * w cpow z2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cpow] THEN
  ASM_CASES_TAC `w = Cx(&0)` THEN ASM_REWRITE_TAC[COMPLEX_MUL_RZERO] THEN
  REWRITE_TAC[COMPLEX_ADD_RDISTRIB; CEXP_ADD]);;

let CPOW_SUC = prove
 (`!w z. w cpow (z + Cx(&1)) = w * w cpow z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CPOW_ADD; CPOW_N] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO] THEN
  REWRITE_TAC[COMPLEX_POW_1; COMPLEX_MUL_SYM]);;

let CPOW_NEG = prove
 (`!w z. w cpow (--z) = inv(w cpow z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cpow] THEN ASM_CASES_TAC `w = Cx(&0)` THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_INV_0] THEN
  REWRITE_TAC[COMPLEX_MUL_LNEG; CEXP_NEG]);;

let CPOW_SUB = prove
 (`!w z1 z2. w cpow (z1 - z2) = w cpow z1 / w cpow z2`,
  REWRITE_TAC[complex_sub; complex_div; CPOW_ADD; CPOW_NEG]);;

let CEXP_MUL_CPOW = prove
 (`!w z. --pi < Im w /\ Im w <= pi ==> cexp(w * z) = cexp(w) cpow z`,
  SIMP_TAC[cpow; CEXP_NZ; CLOG_CEXP] THEN
  REWRITE_TAC[COMPLEX_MUL_SYM]);;

let CPOW_EQ_0 = prove
 (`!w z. w cpow z = Cx(&0) <=> w = Cx(&0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cpow] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[CEXP_NZ]);;

let NORM_CPOW_REAL = prove
 (`!w z. real w /\ &0 < Re w ==> norm(w cpow z) = exp(Re z * log(Re w))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o GEN_REWRITE_RULE I [REAL]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RE_CX]) THEN
  ASM_SIMP_TAC[cpow; CX_INJ; REAL_LT_IMP_NZ] THEN
  ASM_SIMP_TAC[NORM_CEXP; GSYM CX_LOG; RE_MUL_CX; RE_CX]);;

let CPOW_REAL_REAL = prove
 (`!w z. real w /\ real z /\ &0 < Re w
         ==> w cpow z = Cx(exp(Re z * log(Re w)))`,
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o GEN_REWRITE_RULE I [REAL])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RE_CX]) THEN
  ASM_SIMP_TAC[cpow; CX_INJ; REAL_LT_IMP_NZ] THEN
  ASM_SIMP_TAC[NORM_CEXP; GSYM CX_LOG; RE_MUL_CX; RE_CX; CX_EXP; CX_MUL]);;

let NORM_CPOW_REAL_MONO = prove
 (`!w z1 z2. real w /\ &1 < Re w
             ==> (norm(w cpow z1) <= norm(w cpow z2) <=> Re(z1) <= Re(z2))`,
  SIMP_TAC[NORM_CPOW_REAL; REAL_ARITH `&1 < x ==> &0 < x`] THEN
  SIMP_TAC[REAL_EXP_MONO_LE; REAL_LE_RMUL_EQ; LOG_POS_LT]);;

let CPOW_MUL_REAL = prove
 (`!x y z. real x /\ real y /\ &0 <= Re x /\ &0 <= Re y
           ==> (x * y) cpow z = x cpow z * y cpow z`,
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o GEN_REWRITE_RULE I [REAL])) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[RE_CX; IM_CX] THEN
  REWRITE_TAC[REAL_ARITH `&0 <= x <=> x = &0 \/ &0 < x`] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO; CPOW_0] THEN
  ASM_SIMP_TAC[cpow; COMPLEX_ENTIRE; CX_INJ; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[GSYM CEXP_ADD; GSYM COMPLEX_ADD_LDISTRIB] THEN
  ASM_SIMP_TAC[GSYM CX_LOG; GSYM CX_ADD; GSYM CX_MUL; REAL_LT_MUL] THEN
  ASM_SIMP_TAC[LOG_MUL]);;

let HAS_COMPLEX_DERIVATIVE_CPOW = prove
 (`!s z. (Im z = &0 ==> &0 < Re z)
         ==> ((\z. z cpow s) has_complex_derivative
              (s * z cpow (s - Cx(&1)))) (at z)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THEN
  ASM_REWRITE_TAC[IM_CX; RE_CX; REAL_LT_REFL] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[cpow] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT THEN
  MAP_EVERY EXISTS_TAC [`\z. cexp (s * clog z)`; `norm(z:complex)`] THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_NZ] THEN CONJ_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[dist] THEN
    REWRITE_TAC[COMPLEX_SUB_LZERO; NORM_NEG; REAL_LT_REFL];
    COMPLEX_DIFF_TAC THEN ASM_REWRITE_TAC[CEXP_SUB; COMPLEX_SUB_RDISTRIB] THEN
    ASM_SIMP_TAC[CEXP_CLOG; COMPLEX_MUL_LID] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC COMPLEX_FIELD]);;

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (GEN `s:complex`
     (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
               (SPEC `s:complex` HAS_COMPLEX_DERIVATIVE_CPOW)))));;

let HAS_COMPLEX_DERIVATIVE_CPOW_RIGHT = prove
 (`!w z. ~(w = Cx(&0))
         ==> ((\z. w cpow z) has_complex_derivative clog(w) * w cpow z) (at z)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[cpow] THEN
  COMPLEX_DIFF_TAC THEN REWRITE_TAC[COMPLEX_MUL_LID]);;

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (GEN `s:complex`
     (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
               (SPEC `s:complex` HAS_COMPLEX_DERIVATIVE_CPOW_RIGHT)))));;

let COMPLEX_DIFFERENTIABLE_CPOW_RIGHT = prove
 (`!w z. (\z. w cpow z) complex_differentiable (at z)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `w = Cx(&0)` THENL
   [ASM_REWRITE_TAC[cpow; COMPLEX_DIFFERENTIABLE_CONST];
    REWRITE_TAC[complex_differentiable] THEN
    ASM_MESON_TAC[HAS_COMPLEX_DERIVATIVE_CPOW_RIGHT]]);;

let HOLOMORPHIC_ON_CPOW_RIGHT = prove
 (`!w f s. f holomorphic_on s
           ==> (\z. w cpow (f z)) holomorphic_on s`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
  REWRITE_TAC[holomorphic_on; GSYM complex_differentiable] THEN
  ASM_SIMP_TAC[COMPLEX_DIFFERENTIABLE_CPOW_RIGHT;
               COMPLEX_DIFFERENTIABLE_AT_WITHIN]);;

let CONTINUOUS_ON_CPOW_RIGHT = prove
 (`!w f s. f continuous_on s
           ==> (\z. w cpow (f z)) continuous_on s`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_IMP_CONTINUOUS_ON THEN
  REWRITE_TAC[holomorphic_on; GSYM complex_differentiable] THEN
  ASM_SIMP_TAC[COMPLEX_DIFFERENTIABLE_CPOW_RIGHT;
               COMPLEX_DIFFERENTIABLE_AT_WITHIN]);;

(* ------------------------------------------------------------------------- *)
(* Product rule.                                                             *)
(* ------------------------------------------------------------------------- *)

let CLOG_MUL = prove
 (`!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
           ==> clog(w * z) =
                if Im(clog w + clog z) <= --pi then
                  (clog(w) + clog(z)) + ii * Cx(&2 * pi)
                else if Im(clog w + clog z) > pi then
                  (clog(w) + clog(z)) - ii * Cx(&2 * pi)
                else clog(w) + clog(z)`,
  REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  MATCH_MP_TAC CLOG_UNIQUE THEN
  ASM_SIMP_TAC[CEXP_ADD; CEXP_SUB; CEXP_EULER; CEXP_CLOG; CONJ_ASSOC;
               GSYM CX_SIN; GSYM CX_COS; COS_NPI; SIN_NPI] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  TRY(CONJ_TAC THENL [ALL_TAC; CONV_TAC COMPLEX_FIELD]) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP CLOG_WORKS)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[IM_ADD; IM_SUB; IM_MUL_II; RE_CX] THEN
  REAL_ARITH_TAC);;

let CLOG_MUL_SIMPLE = prove
 (`!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0)) /\
         --pi < Im(clog(w)) + Im(clog(z)) /\
         Im(clog(w)) + Im(clog(z)) <= pi
         ==> clog(w * z) = clog(w) + clog(z)`,
  SIMP_TAC[CLOG_MUL; IM_ADD] THEN REAL_ARITH_TAC);;

let CLOG_MUL_CX = prove
 (`(!x z. &0 < x /\ ~(z = Cx(&0)) ==> clog(Cx x * z) = Cx(log x) + clog z) /\
   (!x z. &0 < x /\ ~(z = Cx(&0)) ==> clog(z * Cx x) = clog z + Cx(log x))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CX_LOG] THEN
  MATCH_MP_TAC CLOG_MUL_SIMPLE THEN
  ASM_SIMP_TAC[CX_INJ; REAL_LT_IMP_NZ; GSYM CX_LOG] THEN
  ASM_SIMP_TAC[IM_CX; REAL_ADD_LID; REAL_ADD_RID; CLOG_WORKS]);;

let CLOG_NEG = prove
 (`!z. ~(z = Cx(&0))
       ==> clog(--z) = if Im(z) <= &0 /\ ~(Re(z) < &0 /\ Im(z) = &0)
                       then clog(z) + ii * Cx(pi)
                       else clog(z) - ii * Cx(pi)`,
  REPEAT STRIP_TAC THEN
  SUBST1_TAC(SIMPLE_COMPLEX_ARITH `--z = --Cx(&1) * z`) THEN
  ASM_SIMP_TAC[CLOG_MUL; COMPLEX_RING `~(--Cx(&1) = Cx(&0))`] THEN
  REWRITE_TAC[CLOG_NEG_1; IM_ADD; IM_MUL_II; RE_CX] THEN
  ASM_SIMP_TAC[CLOG_WORKS; REAL_ARITH
   `--p < x /\ x <= p ==> ~(p + x <= --p)`] THEN
  REWRITE_TAC[REAL_ARITH `p + x > p <=> &0 < x`] THEN
  ASM_SIMP_TAC[GSYM IM_CLOG_EQ_PI] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `Im z <= &0 <=> ~(&0 < Im z)`] THEN
  ASM_SIMP_TAC[GSYM IM_CLOG_POS_LT] THEN
  ASM_SIMP_TAC[CLOG_WORKS; REAL_ARITH `x <= p ==> (x < p <=> ~(x = p))`] THEN
  REWRITE_TAC[TAUT `~(a /\ ~b) /\ ~b <=> ~a /\ ~b`] THEN
  ASM_CASES_TAC `Im(clog z) = pi` THEN ASM_REWRITE_TAC[PI_POS] THEN
  ASM_CASES_TAC `&0 < Im(clog z)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING);;

let CLOG_MUL_II = prove
 (`!z. ~(z = Cx(&0))
       ==> clog(ii * z) = if &0 <= Re(z) \/ Im(z) < &0
                          then clog(z) + ii * Cx(pi / &2)
                          else clog(z) - ii * Cx(&3 * pi / &2)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CLOG_MUL; II_NZ; CLOG_II] THEN
  REWRITE_TAC[IM_ADD; IM_MUL_II; RE_CX] THEN
  ASM_SIMP_TAC[CLOG_WORKS; REAL_ARITH
   `--p < x /\ x <= p ==> ~(p / &2 + x <= --p)`] THEN
  REWRITE_TAC[REAL_ARITH `p / &2 + x > p <=> p / &2 < x`] THEN
  REWRITE_TAC[REAL_ARITH `Im z < &0 <=> ~(&0 <= Im z)`] THEN
  ASM_SIMP_TAC[GSYM RE_CLOG_POS_LE; GSYM IM_CLOG_POS_LE] THEN
  MATCH_MP_TAC(MESON[]
   `(p <=> ~q) /\ x = a /\ y = b
    ==> ((if p then x else y) = (if q then b else a))`) THEN
  CONJ_TAC THENL
   [MP_TAC PI_POS THEN REAL_ARITH_TAC;
    REWRITE_TAC[CX_MUL; CX_DIV] THEN CONV_TAC COMPLEX_RING]);;

(* ------------------------------------------------------------------------- *)
(* Unwinding number gives another version of log-product formula.            *)
(* Note that in this special case the unwinding number is -1, 0 or 1.        *)
(* ------------------------------------------------------------------------- *)

let unwinding = new_definition
 `unwinding(z) = (z - clog(cexp z)) / (Cx(&2 * pi) * ii)`;;

let UNWINDING_2PI = prove
 (`Cx(&2 * pi) * ii * unwinding(z) = z - clog(cexp z)`,
  REWRITE_TAC[unwinding; COMPLEX_MUL_ASSOC] THEN
  MATCH_MP_TAC COMPLEX_DIV_LMUL THEN
  REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ; II_NZ] THEN
  MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let CLOG_MUL_UNWINDING = prove
 (`!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
           ==> clog(w * z) =
               clog(w) + clog(z) -
               Cx(&2 * pi) * ii * unwinding(clog w + clog z)`,
  REWRITE_TAC[UNWINDING_2PI;
    COMPLEX_RING `w + z - ((w + z) - c) = c:complex`] THEN
  ASM_SIMP_TAC[CEXP_ADD; CEXP_CLOG]);;

(* ------------------------------------------------------------------------- *)
(* Complex arctangent (branch cut gives standard bounds in real case).       *)
(* ------------------------------------------------------------------------- *)

let catn = new_definition
 `catn z = (ii / Cx(&2)) * clog((Cx(&1) - ii * z) / (Cx(&1) + ii * z))`;;

let CATN_0 = prove
 (`catn(Cx(&0)) = Cx(&0)`,
  REWRITE_TAC[catn; COMPLEX_MUL_RZERO; COMPLEX_SUB_RZERO; COMPLEX_ADD_RID] THEN
  REWRITE_TAC[COMPLEX_DIV_1; CLOG_1; COMPLEX_MUL_RZERO]);;

let IM_COMPLEX_DIV_LEMMA = prove
 (`!z. Im((Cx(&1) - ii * z) / (Cx(&1) + ii * z)) = &0 <=> Re z = &0`,
  REWRITE_TAC[IM_COMPLEX_DIV_EQ_0] THEN
  REWRITE_TAC[complex_mul;  IM; RE; IM_CNJ; RE_CNJ; RE_CX; IM_CX; RE_II; IM_II;
              RE_SUB; RE_ADD; IM_SUB; IM_ADD] THEN
  REAL_ARITH_TAC);;

let RE_COMPLEX_DIV_LEMMA = prove
 (`!z. &0 < Re((Cx(&1) - ii * z) / (Cx(&1) + ii * z)) <=> norm(z) < &1`,
  REWRITE_TAC[RE_COMPLEX_DIV_GT_0; NORM_LT_SQUARE; REAL_LT_01] THEN
  REWRITE_TAC[GSYM NORM_POW_2; COMPLEX_SQNORM] THEN
  REWRITE_TAC[complex_mul;  IM; RE; IM_CNJ; RE_CNJ; RE_CX; IM_CX; RE_II; IM_II;
              RE_SUB; RE_ADD; IM_SUB; IM_ADD] THEN
  REAL_ARITH_TAC);;

let CTAN_CATN = prove
 (`!z. ~(z pow 2 = --Cx(&1)) ==> ctan(catn z) = z`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[catn; ctan; csin; ccos;
              COMPLEX_RING `--i * i / Cx(&2) * z = --(i * i) / Cx(&2) * z`;
              COMPLEX_RING `i * i / Cx(&2) * z =  (i * i) / Cx(&2) * z`] THEN
  REWRITE_TAC[COMPLEX_POW_II_2; GSYM COMPLEX_POW_2] THEN
  REWRITE_TAC[COMPLEX_RING `--Cx(&1) / Cx(&2) * x = --(Cx(&1) / Cx(&2) * x)`;
              CEXP_NEG] THEN
  SUBGOAL_THEN
  `~(cexp(Cx(&1) / Cx(&2) *
          (clog((Cx(&1) - ii * z) / (Cx(&1) + ii * z)))) pow 2 = --Cx(&1))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM CEXP_N; CEXP_SUB; COMPLEX_RING
     `Cx(&2) * Cx(&1) / Cx(&2) * z = z`] THEN
    ASM_SIMP_TAC[CEXP_CLOG; COMPLEX_POW_II_2;
      COMPLEX_FIELD `~(w = Cx(&0)) /\ ~(z = Cx(&0)) ==> ~(w / z = Cx(&0))`;
      COMPLEX_FIELD `~(w = Cx(&0)) ==> (x / w = y <=> x = y * w)`;
      COMPLEX_FIELD
     `ii pow 2 = --Cx(&1) /\ ~(z pow 2 = --Cx(&1))
      ==> ~(Cx(&1) - ii * z = Cx(&0)) /\ ~(Cx(&1) + ii * z = Cx(&0))`] THEN
    POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_RING `-- --Cx (&1) / Cx (&2) = Cx(&1) / Cx(&2)`] THEN
  ASM_SIMP_TAC[CEXP_NZ; COMPLEX_FIELD
    `~(z = Cx(&0)) /\ ~(z pow 2 = --Cx(&1))
     ==> ((inv(z) - z) / (Cx(&2) * ii)) / ((inv(z) + z) / Cx(&2)) =
         inv ii * ((Cx(&1) - z pow 2) / (Cx(&1) + z pow 2))`] THEN
  ASM_SIMP_TAC[GSYM CEXP_N; CEXP_SUB;
               COMPLEX_RING `Cx(&2) * Cx(&1) / Cx(&2) * z = z`] THEN
  ASM_SIMP_TAC[CEXP_CLOG; COMPLEX_FIELD
     `~(z pow 2 = --Cx(&1))
      ==> ~((Cx(&1) - ii * z) / (Cx(&1) + ii * z) = Cx(&0))`] THEN
  UNDISCH_TAC `~(z pow 2 = --Cx(&1))` THEN CONV_TAC COMPLEX_FIELD);;

let CATN_CTAN = prove
 (`!z. abs(Re z) < pi / &2 ==> catn(ctan z) = z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[catn; ctan; csin; ccos] THEN
  ASM_SIMP_TAC[COMPLEX_FIELD
   `ii * (a / (Cx(&2) * ii)) / (b / Cx(&2)) = a / b`] THEN
  SIMP_TAC[COMPLEX_FIELD
   `ii / Cx(&2) * x = y <=> x = Cx(&2) * --(ii * y)`] THEN
  SUBGOAL_THEN `~(cexp(ii * z) pow 2 = --Cx(&1))` ASSUME_TAC THENL
   [SUBGOAL_THEN `--Cx(&1) = cexp(ii * Cx pi)` SUBST1_TAC THENL
     [REWRITE_TAC[CEXP_EULER; GSYM CX_SIN; GSYM CX_COS; SIN_PI; COS_PI] THEN
      CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM CEXP_N; CEXP_EQ] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `Im`) THEN
    REWRITE_TAC[IM_MUL_CX; IM_MUL_II; IM_ADD; RE_CX; IM_II; REAL_MUL_RID] THEN
    MATCH_MP_TAC(REAL_ARITH
     `abs(z) < p / &2 /\ (w = &0 \/ abs(w) >= &2 * p)
      ==> ~(&2 * z = p + w)`) THEN
    ASM_REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_PI; REAL_ABS_NUM] THEN
    SIMP_TAC[real_ge; REAL_MUL_ASSOC; REAL_LE_RMUL_EQ; PI_POS] THEN
    REWRITE_TAC[REAL_ENTIRE; PI_NZ] THEN
    MP_TAC(SPEC `n:real` REAL_ABS_INTEGER_LEMMA) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[CEXP_NEG; CEXP_NZ; COMPLEX_MUL_LNEG; COMPLEX_FIELD
     `~(w = Cx(&0)) /\ ~(w pow 2 = --Cx(&1))
      ==> (Cx(&1) - (w - inv w) / (w + inv w)) /
          (Cx(&1) + (w - inv w) / (w + inv w)) =
           inv(w) pow 2`] THEN
    REWRITE_TAC[GSYM CEXP_N; GSYM CEXP_NEG] THEN
    MATCH_MP_TAC CLOG_CEXP THEN REWRITE_TAC[IM_MUL_CX; IM_NEG; IM_MUL_II] THEN
    ASM_REAL_ARITH_TAC]);;

let RE_CATN_BOUNDS = prove
 (`!z. (Re z = &0 ==> abs(Im z) < &1) ==> abs(Re(catn z)) < pi / &2`,
  REWRITE_TAC[catn; complex_div; GSYM CX_INV; GSYM COMPLEX_MUL_ASSOC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[RE_MUL_II; IM_MUL_CX] THEN
  MATCH_MP_TAC(REAL_ARITH `abs x < p ==> abs(--(inv(&2) * x)) < p / &2`) THEN
  MATCH_MP_TAC(REAL_ARITH `(--p < x /\ x <= p) /\ ~(x = p) ==> abs x < p`) THEN
  SUBGOAL_THEN `~(z = ii) /\ ~(z = --ii)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    DISCH_THEN(fun th -> POP_ASSUM MP_TAC THEN SUBST1_TAC th) THEN
    REWRITE_TAC[RE_II; IM_II; RE_NEG; IM_NEG] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM complex_div] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `~((Cx(&1) - ii * z) / (Cx(&1) + ii * z) = Cx(&0))`
     (fun th -> MESON_TAC[th; CLOG_WORKS]) THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC `clog((Cx(&1) - ii * z) / (Cx(&1) + ii * z))` EULER) THEN
  ASM_REWRITE_TAC[SIN_PI; COS_PI; CX_NEG] THEN
  REWRITE_TAC[COMPLEX_RING
   `x = y * (--Cx(&1) + z * Cx(&0)) <=> x + y = Cx(&0)`] THEN
  REWRITE_TAC[CX_EXP] THEN
  ASM_SIMP_TAC[CEXP_CLOG; COMPLEX_FIELD
     `~(z = ii) /\ ~(z = --ii)
      ==> ~((Cx(&1) - ii * z) / (Cx(&1) + ii * z) = Cx(&0))`] THEN
  REWRITE_TAC[GSYM CX_EXP] THEN DISCH_THEN(MP_TAC o AP_TERM `Im`) THEN
  REWRITE_TAC[IM_ADD; IM_CX; REAL_ADD_RID; IM_COMPLEX_DIV_LEMMA] THEN
  DISCH_TAC THEN UNDISCH_TAC `Re z = &0 ==> abs (Im z) < &1` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `ii * z = --Cx(Im z)` SUBST_ALL_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_EQ; RE_NEG; IM_NEG; RE_MUL_II; IM_MUL_II;
                    RE_CX; IM_CX; REAL_NEG_0];
    ALL_TAC] THEN
  UNDISCH_TAC
   `Im(clog((Cx(&1) - --Cx(Im z)) / (Cx(&1) + --Cx(Im z)))) = pi` THEN
  REWRITE_TAC[COMPLEX_SUB_RNEG; GSYM complex_sub] THEN
  REWRITE_TAC[GSYM CX_ADD; GSYM CX_SUB; GSYM CX_DIV] THEN
  SUBGOAL_THEN `&0 < (&1 + Im z) / (&1 - Im z)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[GSYM CX_LOG; IM_CX; PI_NZ]]);;

let HAS_COMPLEX_DERIVATIVE_CATN = prove
 (`!z. (Re z = &0 ==> abs(Im z) < &1)
       ==> (catn has_complex_derivative inv(Cx(&1) + z pow 2)) (at z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(z = ii) /\ ~(z = --ii)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    DISCH_THEN(fun th -> POP_ASSUM MP_TAC THEN SUBST1_TAC th) THEN
    REWRITE_TAC[RE_II; IM_II; RE_NEG; IM_NEG] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[catn] THEN COMPLEX_DIFF_TAC THEN
  REWRITE_TAC[RE_SUB; RE_ADD; IM_SUB; IM_ADD;
              RE_CX; RE_MUL_II; IM_CX; IM_MUL_II] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[IM_COMPLEX_DIV_LEMMA; RE_COMPLEX_DIV_LEMMA] THEN
    SIMP_TAC[complex_norm] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[REAL_ADD_LID; POW_2_SQRT_ABS];
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC COMPLEX_FIELD]);;

let COMPLEX_DIFFERENTIABLE_AT_CATN = prove
 (`!z. (Re z = &0 ==> abs(Im z) < &1) ==> catn complex_differentiable at z`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CATN]);;

let COMPLEX_DIFFERENTIABLE_WITHIN_CATN = prove
 (`!s z. (Re z = &0 ==> abs(Im z) < &1)
         ==> catn complex_differentiable (at z within s)`,
  MESON_TAC[COMPLEX_DIFFERENTIABLE_AT_WITHIN;
            COMPLEX_DIFFERENTIABLE_AT_CATN]);;

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
             HAS_COMPLEX_DERIVATIVE_CATN)));;

let CONTINUOUS_AT_CATN = prove
 (`!z. (Re z = &0 ==> abs(Im z) < &1) ==> catn continuous at z`,
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CATN;
            HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT]);;

let CONTINUOUS_WITHIN_CATN = prove
 (`!s z. (Re z = &0 ==> abs(Im z) < &1) ==> catn continuous (at z within s)`,
  MESON_TAC[CONTINUOUS_AT_WITHIN; CONTINUOUS_AT_CATN]);;

let CONTINUOUS_ON_CATN = prove
 (`!s. (!z. z IN s /\ Re z = &0 ==> abs(Im z) < &1) ==> catn continuous_on s`,
  MESON_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON; CONTINUOUS_AT_CATN]);;

let HOLOMORPHIC_ON_CATN = prove
 (`!s. (!z. z IN s /\ Re z = &0 ==> abs(Im z) < &1) ==> catn holomorphic_on s`,
  REWRITE_TAC [holomorphic_on] THEN
  MESON_TAC [HAS_COMPLEX_DERIVATIVE_AT_WITHIN; HAS_COMPLEX_DERIVATIVE_CATN]);;

(* ------------------------------------------------------------------------- *)
(* Real arctangent.                                                          *)
(* ------------------------------------------------------------------------- *)

let atn = new_definition
 `atn(x) = Re(catn(Cx x))`;;

let CX_ATN = prove
 (`!x. Cx(atn x) = catn(Cx x)`,
  GEN_TAC THEN REWRITE_TAC[atn; catn; GSYM REAL; real] THEN
  REWRITE_TAC[complex_div; IM_MUL_II; GSYM CX_INV; GSYM COMPLEX_MUL_ASSOC] THEN
  REWRITE_TAC[RE_MUL_CX; REAL_ARITH `inv(&2) * x = &0 <=> x = &0`] THEN
  MATCH_MP_TAC NORM_CEXP_IMAGINARY THEN
  SUBGOAL_THEN `~(Cx(&1) - ii * Cx(x) = Cx(&0)) /\
                ~(Cx(&1) + ii * Cx(x) = Cx(&0))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `Re`) THEN
    REWRITE_TAC[RE_ADD; RE_SUB; RE_MUL_II; IM_CX; RE_CX] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_SIMP_TAC[CEXP_SUB; CEXP_CLOG; COMPLEX_FIELD
   `~(a = Cx(&0)) /\ ~(b = Cx(&0)) ==> ~(a * inv b = Cx(&0))`] THEN
  REWRITE_TAC[GSYM complex_div; COMPLEX_NORM_DIV] THEN
  MATCH_MP_TAC(REAL_FIELD `~(b = &0) /\ a = b ==> a / b = &1`) THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_ZERO] THEN
  MATCH_MP_TAC(MESON[COMPLEX_NORM_CNJ] `cnj a = b ==> norm a = norm b`) THEN
  REWRITE_TAC[CNJ_SUB; CNJ_MUL; CNJ_MUL; CNJ_II; CNJ_CX] THEN
  CONV_TAC COMPLEX_RING);;

let ATN_TAN = prove
 (`!y. tan(atn y) = y`,
  GEN_TAC THEN REWRITE_TAC[tan_def; atn] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `Re(ctan(catn(Cx y)))` THEN
  CONJ_TAC THENL [REWRITE_TAC[GSYM CX_ATN; RE_CX]; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM RE_CX] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC CTAN_CATN THEN MATCH_MP_TAC(COMPLEX_RING
   `~(z = ii) /\ ~(z = --ii) ==> ~(z pow 2 = --Cx(&1))`) THEN
  CONJ_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `Im`) THEN
  REWRITE_TAC[IM_II; IM_CX; IM_NEG] THEN REAL_ARITH_TAC);;

let ATN_BOUND = prove
 (`!y. abs(atn y) < pi / &2`,
  GEN_TAC THEN REWRITE_TAC[atn] THEN MATCH_MP_TAC RE_CATN_BOUNDS THEN
  REWRITE_TAC[IM_CX] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let ATN_BOUNDS = prove
 (`!y. --(pi / &2) < atn(y) /\ atn(y) < (pi / &2)`,
  MP_TAC ATN_BOUND THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC);;

let TAN_ATN = prove
 (`!x. --(pi / &2) < x /\ x < pi / &2 ==> atn(tan(x)) = x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tan_def; atn] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `Re(catn(ctan(Cx x)))` THEN
  CONJ_TAC THENL [REWRITE_TAC[GSYM CX_TAN; RE_CX]; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM RE_CX] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC CATN_CTAN THEN REWRITE_TAC[RE_CX] THEN
  ASM_REAL_ARITH_TAC);;

let ATN_0 = prove
 (`atn(&0) = &0`,
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM TAN_0] THEN
  MATCH_MP_TAC TAN_ATN THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let ATN_1 = prove
 (`atn(&1) = pi / &4`,
  MP_TAC(AP_TERM `atn` TAN_PI4) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC TAN_ATN THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let ATN_NEG = prove
 (`!x. atn(--x) = --(atn x)`,
  GEN_TAC THEN MP_TAC(SPEC `atn(x)` TAN_NEG) THEN REWRITE_TAC[ATN_TAN] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC TAN_ATN THEN
  MP_TAC(SPEC `x:real` ATN_BOUNDS) THEN REAL_ARITH_TAC);;

let ATN_MONO_LT = prove
 (`!x y. x < y ==> atn(x) < atn(y)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV) [GSYM ATN_TAN] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[REAL_NOT_LT] THEN
  SIMP_TAC[TAN_MONO_LE; ATN_BOUNDS]);;

let ATN_MONO_LT_EQ = prove
 (`!x y. atn(x) < atn(y) <=> x < y`,
  MESON_TAC[REAL_NOT_LE; REAL_LE_LT; ATN_MONO_LT]);;

let ATN_MONO_LE_EQ = prove
 (`!x y. atn(x) <= atn(y) <=> x <= y`,
  REWRITE_TAC[GSYM REAL_NOT_LT; ATN_MONO_LT_EQ]);;

let ATN_INJ = prove
 (`!x y. (atn x = atn y) <=> (x = y)`,
  REWRITE_TAC[GSYM REAL_LE_ANTISYM; ATN_MONO_LE_EQ]);;

let ATN_POS_LT = prove
 (`&0 < atn(x) <=> &0 < x`,
  MESON_TAC[ATN_0; ATN_MONO_LT_EQ]);;

let ATN_POS_LE = prove
 (`&0 <= atn(x) <=> &0 <= x`,
  MESON_TAC[ATN_0; ATN_MONO_LE_EQ]);;

let ATN_LT_PI4_POS = prove
 (`!x. x < &1 ==> atn(x) < pi / &4`,
  SIMP_TAC[GSYM ATN_1; ATN_MONO_LT]);;

let ATN_LT_PI4_NEG = prove
 (`!x. --(&1) < x ==> --(pi / &4) < atn(x)`,
  SIMP_TAC[GSYM ATN_1; GSYM ATN_NEG; ATN_MONO_LT]);;

let ATN_LT_PI4 = prove
 (`!x. abs(x) < &1 ==> abs(atn x) < pi / &4`,
  GEN_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `(&0 < x ==> &0 < y) /\
    (x < &0 ==> y < &0) /\
    ((x = &0) ==> (y = &0)) /\
    (x < a ==> y < b) /\
    (--a < x ==> --b < y)
    ==> abs(x) < a ==> abs(y) < b`) THEN
  SIMP_TAC[ATN_LT_PI4_POS; ATN_LT_PI4_NEG; ATN_0] THEN CONJ_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM ATN_0] THEN
  SIMP_TAC[ATN_MONO_LT]);;

let ATN_LE_PI4 = prove
 (`!x. abs(x) <= &1 ==> abs(atn x) <= pi / &4`,
  REWRITE_TAC[REAL_LE_LT] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ATN_LT_PI4] THEN DISJ2_TAC THEN
  FIRST_ASSUM(DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
    (REAL_ARITH `(abs(x) = a) ==> (x = a) \/ (x = --a)`)) THEN
  ASM_REWRITE_TAC[ATN_1; ATN_NEG] THEN
  REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NUM; REAL_ABS_NEG] THEN
  SIMP_TAC[real_abs; REAL_LT_IMP_LE; PI_POS]);;

let COS_ATN_NZ = prove
 (`!x. ~(cos(atn(x)) = &0)`,
  GEN_TAC THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
  MATCH_MP_TAC COS_POS_PI THEN REWRITE_TAC[ATN_BOUNDS]);;

let TAN_SEC = prove
 (`!x. ~(cos(x) = &0) ==> (&1 + (tan(x) pow 2) = inv(cos x) pow 2)`,
  MP_TAC SIN_CIRCLE THEN MATCH_MP_TAC MONO_FORALL THEN REWRITE_TAC[tan] THEN
  CONV_TAC REAL_FIELD);;

let COS_ATN = prove
 (`!x. cos(atn x) = &1 / sqrt(&1 + x pow 2)`,
  SIMP_TAC[COS_TAN; ATN_BOUND; ATN_TAN]);;

let SIN_ATN = prove
 (`!x. sin(atn x) = x / sqrt(&1 + x pow 2)`,
  SIMP_TAC[SIN_TAN; ATN_BOUND; ATN_TAN]);;

let ATN_ABS = prove
 (`!x. atn(abs x) = abs(atn x)`,
  GEN_TAC THEN REWRITE_TAC[real_abs; ATN_POS_LE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ATN_NEG]);;

let ATN_ADD = prove
 (`!x y. abs(atn x + atn y) < pi / &2
         ==> atn(x) + atn(y) = atn((x + y) / (&1 - x * y))`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS `atn((tan(atn x) + tan(atn y)) /
                          (&1 - tan(atn x) * tan(atn y)))` THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[ATN_TAN]] THEN
  W(MP_TAC o PART_MATCH (rand o rand) TAN_ADD o rand o rand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COS_ATN_NZ] THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
    MATCH_MP_TAC COS_POS_PI THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC TAN_ATN THEN ASM_REAL_ARITH_TAC]);;

let ATN_INV = prove
 (`!x. &0 < x ==> atn(inv x) = pi / &2 - atn x`,
  REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS `atn(inv(tan(atn x)))` THEN
  CONJ_TAC THENL [REWRITE_TAC[ATN_TAN]; REWRITE_TAC[GSYM TAN_COT]] THEN
  MATCH_MP_TAC TAN_ATN THEN REWRITE_TAC[ATN_BOUNDS; REAL_ARITH
   `--(p / &2) < p / &2 - x /\ p / &2 - x < p / &2 <=> &0 < x /\ x < p`] THEN
  ASM_REWRITE_TAC[ATN_POS_LT] THEN MP_TAC(SPEC `x:real` ATN_BOUNDS) THEN
  ASM_REAL_ARITH_TAC);;

let ATN_ADD_SMALL = prove
 (`!x y. abs(x * y) < &1
         ==> (atn(x) + atn(y) = atn((x + y) / (&1 - x * y)))`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`x = &0`; `y = &0`] THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_SUB_RZERO;
                  REAL_DIV_1; REAL_ADD_LID; REAL_ADD_RID; ATN_0] THEN
  MATCH_MP_TAC ATN_ADD THEN MATCH_MP_TAC(REAL_ARITH
   `abs(x) < p - abs(y) \/ abs(y) < p - abs(x) ==> abs(x + y) < p`) THEN
  REWRITE_TAC[GSYM ATN_ABS] THEN
  ASM_SIMP_TAC[GSYM ATN_INV; REAL_ARITH `~(x = &0) ==> &0 < abs x`;
        ATN_MONO_LT_EQ; REAL_ARITH `inv x = &1 / x`; REAL_LT_RDIV_EQ] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Machin-like formulas for pi.                                              *)
(* ------------------------------------------------------------------------- *)

let [MACHIN; MACHIN_EULER; MACHIN_GAUSS] = (CONJUNCTS o prove)
 (`(&4 * atn(&1 / &5) - atn(&1 / &239) = pi / &4) /\
   (&5 * atn(&1 / &7) + &2 * atn(&3 / &79) = pi / &4) /\
   (&12 * atn(&1 / &18) + &8 * atn(&1 / &57) - &5 * atn(&1 / &239) = pi / &4)`,
  REPEAT CONJ_TAC THEN CONV_TAC(ONCE_DEPTH_CONV(fun tm ->
    if is_binop `( * ):real->real->real` tm
    then LAND_CONV(RAND_CONV(TOP_DEPTH_CONV num_CONV)) tm
    else failwith "")) THEN
  REWRITE_TAC[real_sub; GSYM REAL_MUL_RNEG; GSYM ATN_NEG] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_ADD_LID] THEN
  CONV_TAC(DEPTH_CONV (fun tm ->
    let th1 = PART_MATCH (lhand o rand) ATN_ADD_SMALL tm in
    let th2 = MP th1 (EQT_ELIM(REAL_RAT_REDUCE_CONV(lhand(concl th1)))) in
    CONV_RULE(RAND_CONV(RAND_CONV REAL_RAT_REDUCE_CONV)) th2)) THEN
  REWRITE_TAC[ATN_1]);;

(* ------------------------------------------------------------------------- *)
(* Some bound theorems where a bit of simple calculus is handy.              *)
(* ------------------------------------------------------------------------- *)

let ATN_ABS_LE_X = prove
 (`!x. abs(atn x) <= abs x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`catn`; `\z. inv(Cx(&1) + z pow 2)`; `real`; `&1`]
      COMPLEX_MVT) THEN
  REWRITE_TAC[CONVEX_REAL; IN] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[real] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_AT_WITHIN THEN
      MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_CATN THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      GEN_TAC THEN REWRITE_TAC[REAL] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[GSYM CX_POW; GSYM CX_ADD; GSYM CX_INV; COMPLEX_NORM_CX] THEN
      REWRITE_TAC[REAL_ABS_INV] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
      MP_TAC(SPEC `Re z` REAL_LE_SQUARE) THEN REAL_ARITH_TAC];
    DISCH_THEN(MP_TAC o SPECL [`Cx(&0)`; `Cx(x)`]) THEN
    REWRITE_TAC[GSYM CX_ATN; COMPLEX_SUB_RZERO; REAL_CX; ATN_0] THEN
    REWRITE_TAC[COMPLEX_NORM_CX; REAL_MUL_LID]]);;

let ATN_LE_X = prove
 (`!x. &0 <= x ==> atn(x) <= x`,
  MP_TAC ATN_ABS_LE_X THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC);;

let TAN_ABS_GE_X = prove
 (`!x. abs(x) < pi / &2 ==> abs(x) <= abs(tan x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(atn(tan x))` THEN REWRITE_TAC[ATN_ABS_LE_X] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC TAN_ATN THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Probably not very useful, but for compatibility with old analysis theory. *)
(* ------------------------------------------------------------------------- *)

let TAN_TOTAL = prove
 (`!y. ?!x. --(pi / &2) < x /\ x < (pi / &2) /\ tan(x) = y`,
  MESON_TAC[TAN_ATN; ATN_TAN; ATN_BOUNDS]);;

let TAN_TOTAL_POS = prove
 (`!y. &0 <= y ==> ?x. &0 <= x /\ x < pi / &2 /\ tan(x) = y`,
  MESON_TAC[ATN_TAN; ATN_BOUNDS; ATN_POS_LE]);;

let TAN_TOTAL_LEMMA = prove
 (`!y. &0 < y ==> ?x. &0 < x /\ x < pi / &2 /\ y < tan(x)`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `atn(y + &1)` THEN
  REWRITE_TAC[ATN_TAN; ATN_BOUNDS; ATN_POS_LT] THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Some slightly ad hoc lemmas useful here.                                  *)
(* ------------------------------------------------------------------------- *)

let RE_POW_2 = prove
 (`Re(z pow 2) = Re(z) pow 2 - Im(z) pow 2`,
  REWRITE_TAC[COMPLEX_POW_2; complex_mul; RE] THEN REAL_ARITH_TAC);;

let IM_POW_2 = prove
 (`Im(z pow 2) = &2 * Re(z) * Im(z)`,
  REWRITE_TAC[COMPLEX_POW_2; complex_mul; IM] THEN REAL_ARITH_TAC);;

let ABS_SQUARE_LT_1 = prove
 (`!x. x pow 2 < &1 <=> abs(x) < &1`,
  ONCE_REWRITE_TAC[GSYM REAL_ABS_NUM] THEN
  REWRITE_TAC[REAL_LT_SQUARE_ABS] THEN REAL_ARITH_TAC);;

let ABS_SQUARE_LE_1 = prove
 (`!x. x pow 2 <= &1 <=> abs(x) <= &1`,
  ONCE_REWRITE_TAC[GSYM REAL_ABS_NUM] THEN
  REWRITE_TAC[REAL_LT_SQUARE_ABS; GSYM REAL_NOT_LT] THEN REAL_ARITH_TAC);;

let ABS_SQUARE_EQ_1 = prove
 (`!x. x pow 2 = &1 <=> abs(x) = &1`,
  REWRITE_TAC[REAL_RING `x pow 2 = &1 <=> x = &1 \/ x = -- &1`] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Inverse sine.                                                             *)
(* ------------------------------------------------------------------------- *)

let casn = new_definition
 `casn z = --ii * clog(ii * z + csqrt(Cx(&1) - z pow 2))`;;

let CASN_BODY_LEMMA = prove
 (`!z. ~(ii * z + csqrt(Cx(&1) - z pow 2) = Cx(&0))`,
  GEN_TAC THEN MP_TAC(SPEC `Cx(&1) - z pow 2` CSQRT) THEN
  CONV_TAC COMPLEX_FIELD);;

let CSIN_CASN = prove
 (`!z. csin(casn z) = z`,
  GEN_TAC THEN REWRITE_TAC[csin; casn; COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG] THEN
  REWRITE_TAC[COMPLEX_MUL_ASSOC; COMPLEX_NEG_NEG] THEN
  REWRITE_TAC[COMPLEX_POW_II_2; GSYM COMPLEX_POW_2] THEN
  REWRITE_TAC[COMPLEX_NEG_NEG; COMPLEX_MUL_LNEG; COMPLEX_MUL_LID] THEN
  REWRITE_TAC[CEXP_NEG] THEN
  ASM_SIMP_TAC[CASN_BODY_LEMMA; CEXP_CLOG; COMPLEX_FIELD
     `~(z = Cx(&0))
      ==> ((z - inv z) / (Cx(&2) * ii) = c <=>
           z pow 2 - Cx(&1) = Cx(&2) * ii * c * z)`] THEN
  MP_TAC(SPEC `Cx(&1) - z pow 2` CSQRT) THEN CONV_TAC COMPLEX_FIELD);;

let CASN_CSIN = prove
 (`!z. abs(Re z) < pi / &2 \/ (abs(Re z) = pi / &2 /\ Im z = &0)
       ==> casn(csin z) = z`,
  GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[csin; casn; COMPLEX_MUL_LNEG; CEXP_NEG] THEN
  SIMP_TAC[CEXP_NZ; COMPLEX_FIELD
    `~(z = Cx(&0))
     ==> Cx(&1) - ((z - inv z) / (Cx(&2) * ii)) pow 2 =
         ((z + inv z) / Cx(&2)) pow 2`] THEN
  SUBGOAL_THEN
   `csqrt(((cexp(ii * z) + inv(cexp(ii * z))) / Cx(&2)) pow 2) =
    (cexp(ii * z) + inv(cexp(ii * z))) / Cx(&2)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC POW_2_CSQRT THEN REWRITE_TAC[GSYM CEXP_NEG] THEN
    REWRITE_TAC[complex_div; GSYM CX_INV; RE_MUL_CX; IM_MUL_CX] THEN
    REWRITE_TAC[REAL_ARITH
     `&0 < r * inv(&2) \/ r * inv(&2) = &0 /\ &0 <= i * inv(&2) <=>
      &0 < r \/ r = &0 /\ &0 <= i`] THEN
    REWRITE_TAC[RE_ADD; IM_ADD; RE_CEXP; IM_CEXP] THEN
    REWRITE_TAC[RE_MUL_II; RE_NEG; IM_MUL_II; IM_NEG] THEN
    REWRITE_TAC[SIN_NEG; COS_NEG; REAL_NEG_NEG] THEN
    REWRITE_TAC[REAL_MUL_RNEG; GSYM real_sub] THEN
    REWRITE_TAC[GSYM REAL_ADD_RDISTRIB; GSYM REAL_SUB_RDISTRIB] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [DISJ1_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_SIMP_TAC[REAL_LT_ADD; REAL_EXP_POS_LT] THEN
      MATCH_MP_TAC COS_POS_PI THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
      DISJ2_TAC THEN ASM_REWRITE_TAC[SIN_PI2; COS_PI2] THEN
      REWRITE_TAC[REAL_EXP_NEG; REAL_EXP_0; REAL_INV_1; REAL_SUB_REFL] THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_LE_REFL; REAL_ENTIRE] THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o MATCH_MP (REAL_ARITH
       `abs(x) = p ==> x = p \/ x = --p`)) THEN
      REWRITE_TAC[COS_PI2; COS_NEG] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SIMP_TAC[COMPLEX_FIELD
   `ii * (a - b) / (Cx(&2) * ii) + (a + b) / Cx(&2) = a`] THEN
  SIMP_TAC[COMPLEX_FIELD `--(ii * w) = z <=> w = ii * z`] THEN
  MATCH_MP_TAC CLOG_CEXP THEN REWRITE_TAC[IM_MUL_II] THEN
  MP_TAC PI_POS THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

let CASN_UNIQUE = prove
 (`!w z. csin(z) = w /\
         (abs(Re z) < pi / &2 \/ (abs(Re z) = pi / &2 /\ Im z = &0))
         ==> casn w = z`,
  MESON_TAC[CASN_CSIN]);;

let CASN_0 = prove
 (`casn(Cx(&0)) = Cx(&0)`,
  REWRITE_TAC[casn; COMPLEX_MUL_RZERO; COMPLEX_ADD_LID; COMPLEX_POW_2;
              COMPLEX_SUB_RZERO; CSQRT_1; CLOG_1; COMPLEX_MUL_RZERO]);;

let CASN_1 = prove
 (`casn(Cx(&1)) = Cx(pi / &2)`,
  REWRITE_TAC[casn; GSYM CX_POW; GSYM CX_SUB] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[CSQRT_0; COMPLEX_MUL_RID; COMPLEX_ADD_RID] THEN
  REWRITE_TAC[CLOG_II] THEN CONV_TAC COMPLEX_RING);;

let CASN_NEG_1 = prove
 (`casn(--Cx(&1)) = --Cx(pi / &2)`,
  REWRITE_TAC[casn; GSYM CX_NEG; GSYM CX_POW; GSYM CX_SUB] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[CSQRT_0; COMPLEX_MUL_RID; COMPLEX_ADD_RID] THEN
  REWRITE_TAC[CX_NEG; COMPLEX_MUL_RID; COMPLEX_MUL_RNEG] THEN
  REWRITE_TAC[CLOG_NEG_II] THEN CONV_TAC COMPLEX_RING);;

let HAS_COMPLEX_DERIVATIVE_CASN = prove
 (`!z. (Im z = &0 ==> abs(Re z) < &1)
       ==> (casn has_complex_derivative inv(ccos(casn z))) (at z)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_INVERSE_BASIC THEN
  EXISTS_TAC `csin` THEN
  REWRITE_TAC[CSIN_CASN; HAS_COMPLEX_DERIVATIVE_CSIN; CONTINUOUS_AT_CSIN] THEN
  EXISTS_TAC `ball(z:complex,&1)` THEN
  REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL; REAL_LT_01] THEN CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP (COMPLEX_RING
     `ccos z = Cx(&0) ==> csin(z) pow 2 + ccos(z) pow 2 = Cx(&1)
                          ==> csin(z) pow 2 = Cx(&1)`)) THEN
    REWRITE_TAC[CSIN_CASN; CSIN_CIRCLE] THEN
    REWRITE_TAC[COMPLEX_RING
     `z pow 2 = Cx(&1) <=> z = Cx(&1) \/ z = --Cx(&1)`] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[RE_CX; IM_CX; RE_NEG; IM_NEG] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN REWRITE_TAC[casn] THEN
  MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN REWRITE_TAC[CONTINUOUS_CONST] THEN
  ONCE_REWRITE_TAC[GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ADD THEN
    SIMP_TAC[CONTINUOUS_COMPLEX_MUL; CONTINUOUS_CONST; CONTINUOUS_AT_ID] THEN
    ONCE_REWRITE_TAC[GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_COMPLEX_POW; CONTINUOUS_SUB;
             CONTINUOUS_CONST; CONTINUOUS_AT_ID] THEN
    MATCH_MP_TAC CONTINUOUS_AT_CSQRT THEN
    REWRITE_TAC[RE_SUB; IM_SUB; RE_CX; IM_CX; RE_POW_2; IM_POW_2] THEN
    REWRITE_TAC[REAL_RING `&0 - &2 * x * y = &0 <=> x = &0 \/ y = &0`] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC[REAL_POW_2; REAL_MUL_LZERO; REAL_SUB_RZERO;
                    REAL_ARITH `&1 - (&0 - x) = &1 + x`] THEN
    ASM_SIMP_TAC[REAL_LE_SQUARE; REAL_ARITH `&0 <= x ==> &0 < &1 + x`] THEN
    REWRITE_TAC[REAL_ARITH `&0 < &1 - x * x <=> x pow 2 < &1 pow 2`] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LT2 THEN
    ASM_SIMP_TAC[REAL_ABS_POS; REAL_ABS_NUM; ARITH];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_AT_CLOG THEN
  REWRITE_TAC[IM_ADD; IM_MUL_II; RE_ADD; RE_MUL_II] THEN
  ASM_CASES_TAC `Im z = &0` THENL
   [DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[csqrt] THEN
    ASM_REWRITE_TAC[IM_SUB; RE_SUB; IM_CX; RE_CX; IM_POW_2; RE_POW_2;
                    REAL_MUL_RZERO; REAL_SUB_REFL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_ARITH `&0 <= &1 - (z pow 2 - &0) <=> z pow 2 <= &1 pow 2`;
                GSYM REAL_LE_SQUARE_ABS] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_ABS_NUM; RE; REAL_ADD_LID] THEN
    MATCH_MP_TAC SQRT_POS_LT THEN
    REWRITE_TAC[REAL_ARITH `&0 < &1 - (z pow 2 - &0) <=> z pow 2 < &1 pow 2`;
                GSYM REAL_LT_SQUARE_ABS] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[csqrt; IM_SUB; RE_SUB; IM_CX; RE_CX; IM_POW_2; RE_POW_2] THEN
  REWRITE_TAC[REAL_RING `&0 - &2 * x * y = &0 <=> x = &0 \/ y = &0`] THEN
  ASM_CASES_TAC `Re z = &0` THEN ASM_REWRITE_TAC[RE; IM] THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_ARITH `&1 - (&0 - x) = &1 + x`] THEN
    SIMP_TAC[REAL_POW_2; REAL_LE_ADD; REAL_LE_SQUARE; REAL_POS] THEN
    REWRITE_TAC[RE; IM; REAL_ADD_LID; REAL_ARITH `&0 < --x + y <=> x < y`] THEN
    MATCH_MP_TAC REAL_LT_RSQRT THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[REAL_ARITH `&0 < --x + y <=> x < y`] THEN
  MATCH_MP_TAC REAL_LT_RSQRT THEN
  REWRITE_TAC[REAL_POW_2; REAL_ARITH
   `a < (n + &1 - (b - a)) / &2 <=> (a + b) - &1 < n`] THEN
  REWRITE_TAC[complex_norm] THEN MATCH_MP_TAC REAL_LT_RSQRT THEN
  REWRITE_TAC[RE_SUB; IM_SUB; RE_CX; IM_CX; RE_POW_2; IM_POW_2] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o
    GEN_REWRITE_RULE I [GSYM REAL_LT_SQUARE])) THEN
  REAL_ARITH_TAC);;

let COMPLEX_DIFFERENTIABLE_AT_CASN = prove
 (`!z. (Im z = &0 ==> abs(Re z) < &1) ==> casn complex_differentiable at z`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CASN]);;

let COMPLEX_DIFFERENTIABLE_WITHIN_CASN = prove
 (`!s z. (Im z = &0 ==> abs(Re z) < &1)
         ==> casn complex_differentiable (at z within s)`,
  MESON_TAC[COMPLEX_DIFFERENTIABLE_AT_WITHIN;
            COMPLEX_DIFFERENTIABLE_AT_CASN]);;

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
             HAS_COMPLEX_DERIVATIVE_CASN)));;

let CONTINUOUS_AT_CASN = prove
 (`!z. (Im z = &0 ==> abs(Re z) < &1) ==> casn continuous at z`,
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CASN;
            HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT]);;

let CONTINUOUS_WITHIN_CASN = prove
 (`!s z. (Im z = &0 ==> abs(Re z) < &1) ==> casn continuous (at z within s)`,
  MESON_TAC[CONTINUOUS_AT_WITHIN; CONTINUOUS_AT_CASN]);;

let CONTINUOUS_ON_CASN = prove
 (`!s. (!z. z IN s /\ Im z = &0 ==> abs(Re z) < &1) ==> casn continuous_on s`,
  MESON_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON; CONTINUOUS_AT_CASN]);;

let HOLOMORPHIC_ON_CASN = prove
 (`!s. (!z. z IN s /\ Im z = &0 ==> abs(Re z) < &1) ==> casn holomorphic_on s`,
  REWRITE_TAC [holomorphic_on] THEN
  MESON_TAC [HAS_COMPLEX_DERIVATIVE_AT_WITHIN; HAS_COMPLEX_DERIVATIVE_CASN]);;

(* ------------------------------------------------------------------------- *)
(* Inverse cosine.                                                           *)
(* ------------------------------------------------------------------------- *)

let cacs = new_definition
 `cacs z = --ii * clog(z + ii * csqrt(Cx(&1) - z pow 2))`;;

let CACS_BODY_LEMMA = prove
 (`!z. ~(z + ii * csqrt(Cx(&1) - z pow 2) = Cx(&0))`,
  GEN_TAC THEN MP_TAC(SPEC `Cx(&1) - z pow 2` CSQRT) THEN
  CONV_TAC COMPLEX_FIELD);;

let CCOS_CACS = prove
 (`!z. ccos(cacs z) = z`,
  GEN_TAC THEN REWRITE_TAC[ccos; cacs; COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG] THEN
  REWRITE_TAC[COMPLEX_MUL_ASSOC; COMPLEX_NEG_NEG] THEN
  REWRITE_TAC[COMPLEX_POW_II_2; GSYM COMPLEX_POW_2] THEN
  REWRITE_TAC[COMPLEX_NEG_NEG; COMPLEX_MUL_LNEG; COMPLEX_MUL_LID] THEN
  REWRITE_TAC[CEXP_NEG] THEN
  ASM_SIMP_TAC[CACS_BODY_LEMMA; CEXP_CLOG; COMPLEX_POW_II_2; COMPLEX_FIELD
     `~(z = Cx(&0))
      ==> ((z + inv z) / Cx(&2) = c <=>
           z pow 2 + Cx(&1) = Cx(&2) * c * z)`] THEN
  MP_TAC(SPEC `Cx(&1) - z pow 2` CSQRT) THEN CONV_TAC COMPLEX_FIELD);;

let CACS_CCOS = prove
 (`!z. &0 < Re z /\ Re z < pi \/
       Re(z) = &0 /\ &0 <= Im(z) \/
       Re(z) = pi /\ Im(z) <= &0
       ==> cacs(ccos z) = z`,
  GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[ccos; cacs; COMPLEX_MUL_LNEG; CEXP_NEG] THEN
  SIMP_TAC[CEXP_NZ; COMPLEX_FIELD
    `~(z = Cx(&0))
     ==> Cx(&1) - ((z + inv z) / Cx(&2)) pow 2 =
         --(((z - inv z) / Cx(&2)) pow 2)`] THEN
  SUBGOAL_THEN
   `csqrt(--(((cexp(ii * z) - inv(cexp(ii * z))) / Cx(&2)) pow 2)) =
    --ii * (cexp(ii * z) - inv(cexp(ii * z))) / Cx(&2)`
  SUBST1_TAC THENL
   [SIMP_TAC[COMPLEX_FIELD `--(x pow 2) = (--ii * x) pow 2`] THEN
    MATCH_MP_TAC POW_2_CSQRT THEN REWRITE_TAC[GSYM CEXP_NEG] THEN
    REWRITE_TAC[complex_div; GSYM CX_INV; RE_MUL_CX; IM_MUL_CX; RE_NEG; IM_NEG;
                COMPLEX_MUL_LNEG; RE_MUL_II; IM_MUL_II; RE_SUB; IM_SUB] THEN
    REWRITE_TAC[REAL_NEG_NEG; REAL_NEG_EQ_0] THEN
    REWRITE_TAC[REAL_ARITH
     `&0 < r * inv(&2) \/ r * inv(&2) = &0 /\ &0 <= --(i * inv(&2)) <=>
      &0 < r \/ r = &0 /\ &0 <= --i`] THEN
    REWRITE_TAC[RE_ADD; IM_ADD; RE_CEXP; IM_CEXP] THEN
    REWRITE_TAC[RE_MUL_II; RE_NEG; IM_MUL_II; IM_NEG] THEN
    REWRITE_TAC[SIN_NEG; COS_NEG; REAL_NEG_NEG] THEN
    REWRITE_TAC[REAL_MUL_RNEG; GSYM real_sub; REAL_SUB_RNEG; REAL_NEG_SUB] THEN
    REWRITE_TAC[GSYM REAL_ADD_RDISTRIB; GSYM REAL_SUB_RDISTRIB] THEN
    ASM_SIMP_TAC[REAL_LT_ADD; REAL_EXP_POS_LT; REAL_LT_MUL_EQ] THEN
    POP_ASSUM(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[SIN_POS_PI] THEN DISJ2_TAC THEN
    REWRITE_TAC[SIN_PI; REAL_MUL_RZERO; COS_PI; SIN_0; COS_0] THEN
    REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RNEG] THEN
    REWRITE_TAC[REAL_NEG_SUB; REAL_SUB_LE; REAL_EXP_MONO_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[COMPLEX_FIELD
   `(e + e') / Cx(&2) + ii * --ii * (e - e') / Cx(&2) = e`] THEN
  SIMP_TAC[COMPLEX_FIELD `--(ii * w) = z <=> w = ii * z`] THEN
  MATCH_MP_TAC CLOG_CEXP THEN REWRITE_TAC[IM_MUL_II] THEN
  MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC);;

let CACS_UNIQUE = prove
 (`!w z.
       ccos z = w /\
       (&0 < Re z /\ Re z < pi \/
        Re(z) = &0 /\ &0 <= Im(z) \/
        Re(z) = pi /\ Im(z) <= &0)
       ==> cacs(w) = z`,
  MESON_TAC[CACS_CCOS]);;

let CACS_0 = prove
 (`cacs(Cx(&0)) = Cx(pi / &2)`,
  MATCH_MP_TAC CACS_UNIQUE THEN
  REWRITE_TAC[RE_CX; IM_CX; GSYM CX_COS; COS_PI2] THEN
  MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let CACS_1 = prove
 (`cacs(Cx(&1)) = Cx(&0)`,
  MATCH_MP_TAC CACS_UNIQUE THEN
  REWRITE_TAC[RE_CX; IM_CX; GSYM CX_COS; COS_0; REAL_LE_REFL]);;

let CACS_NEG_1 = prove
 (`cacs(--Cx(&1)) = Cx pi`,
  MATCH_MP_TAC CACS_UNIQUE THEN
  REWRITE_TAC[RE_CX; IM_CX; GSYM CX_COS; COS_PI; CX_NEG; REAL_LE_REFL]);;

let HAS_COMPLEX_DERIVATIVE_CACS = prove
 (`!z. (Im z = &0 ==> abs(Re z) < &1)
       ==> (cacs has_complex_derivative --inv(csin(cacs z))) (at z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[COMPLEX_NEG_INV] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_INVERSE_BASIC THEN
  EXISTS_TAC `ccos` THEN
  REWRITE_TAC[CCOS_CACS; HAS_COMPLEX_DERIVATIVE_CCOS; CONTINUOUS_AT_CCOS] THEN
  EXISTS_TAC `ball(z:complex,&1)` THEN
  REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL; REAL_LT_01] THEN CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP (COMPLEX_RING
     `--(csin z) = Cx(&0) ==> csin(z) pow 2 + ccos(z) pow 2 = Cx(&1)
                              ==> ccos(z) pow 2 = Cx(&1)`)) THEN
    REWRITE_TAC[CCOS_CACS; CSIN_CIRCLE] THEN
    REWRITE_TAC[COMPLEX_RING
     `z pow 2 = Cx(&1) <=> z = Cx(&1) \/ z = --Cx(&1)`] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[RE_CX; IM_CX; RE_NEG; IM_NEG] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN REWRITE_TAC[cacs] THEN
  MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN REWRITE_TAC[CONTINUOUS_CONST] THEN
  ONCE_REWRITE_TAC[GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ADD THEN REWRITE_TAC[CONTINUOUS_AT_ID] THEN
    MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN REWRITE_TAC[CONTINUOUS_CONST] THEN
    ONCE_REWRITE_TAC[GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_COMPLEX_POW; CONTINUOUS_SUB;
             CONTINUOUS_CONST; CONTINUOUS_AT_ID] THEN
    MATCH_MP_TAC CONTINUOUS_AT_CSQRT THEN
    REWRITE_TAC[RE_SUB; IM_SUB; RE_CX; IM_CX; RE_POW_2; IM_POW_2] THEN
    REWRITE_TAC[REAL_RING `&0 - &2 * x * y = &0 <=> x = &0 \/ y = &0`] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC[REAL_POW_2; REAL_MUL_LZERO; REAL_SUB_RZERO;
                    REAL_ARITH `&1 - (&0 - x) = &1 + x`] THEN
    ASM_SIMP_TAC[REAL_LE_SQUARE; REAL_ARITH `&0 <= x ==> &0 < &1 + x`] THEN
    REWRITE_TAC[REAL_ARITH `&0 < &1 - x * x <=> x pow 2 < &1 pow 2`] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LT2 THEN
    ASM_SIMP_TAC[REAL_ABS_POS; REAL_ABS_NUM; ARITH];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_AT_CLOG THEN
  REWRITE_TAC[IM_ADD; IM_MUL_II; RE_ADD; RE_MUL_II] THEN
  ASM_CASES_TAC `Im z = &0` THENL
   [ASM_REWRITE_TAC[csqrt] THEN
    ASM_REWRITE_TAC[IM_SUB; RE_SUB; IM_CX; RE_CX; IM_POW_2; RE_POW_2;
                    REAL_MUL_RZERO; REAL_SUB_REFL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_ARITH `&0 <= &1 - (z pow 2 - &0) <=> z pow 2 <= &1 pow 2`;
                GSYM REAL_LE_SQUARE_ABS] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_ABS_NUM; RE; REAL_ADD_LID] THEN
    REWRITE_TAC[GSYM real_sub; IM; REAL_SUB_LT; REAL_SUB_RZERO] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> x = &0 ==> &0 < y`) THEN
    MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_SIMP_TAC[REAL_SUB_LT; ABS_SQUARE_LT_1];
    ALL_TAC] THEN
  REWRITE_TAC[csqrt; IM_SUB; RE_SUB; IM_CX; RE_CX; IM_POW_2; RE_POW_2] THEN
  REWRITE_TAC[REAL_RING `&0 - &2 * x * y = &0 <=> x = &0 \/ y = &0`] THEN
  ASM_CASES_TAC `Re z = &0` THEN ASM_REWRITE_TAC[RE; IM] THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_ARITH `&1 - (&0 - x) = &1 + x`] THEN
    SIMP_TAC[REAL_POW_2; REAL_LE_ADD; REAL_LE_SQUARE; REAL_POS] THEN
    REWRITE_TAC[RE; IM; REAL_ADD_LID] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `a + b = &0 ==> a = --b`)) THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x:real. x pow 2`) THEN
    SIMP_TAC[SQRT_POW_2; REAL_POW_NEG; ARITH; REAL_LE_SQUARE; REAL_LE_ADD;
             REAL_POS] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `a + b = &0 ==> a = --b`)) THEN
  DISCH_THEN(MP_TAC o AP_TERM `\x:real. x pow 2`) THEN
  SUBGOAL_THEN `&0 < (norm(Cx (&1) - z pow 2) +
                      &1 - (Re z pow 2 - Im z pow 2)) / &2`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `&0 < (x + y - z) / &2 <=> z - y < x`] THEN
    REWRITE_TAC[complex_norm] THEN MATCH_MP_TAC REAL_LT_RSQRT THEN
    REWRITE_TAC[RE_SUB; IM_SUB; RE_CX; IM_CX; RE_POW_2; IM_POW_2] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o
     GEN_REWRITE_RULE I [GSYM REAL_LT_SQUARE])) THEN
    REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_MUL) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_POW_2; REAL_POW_NEG; ARITH; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[REAL_POW_2; REAL_ARITH
   `a = (n + &1 - (b - a)) / &2 <=> (a + b) - &1 = n`] THEN
  REWRITE_TAC[complex_norm] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\x:real. x pow 2`) THEN
  SIMP_TAC[SQRT_POW_2; REWRITE_RULE[GSYM REAL_POW_2] REAL_LE_SQUARE;
           REAL_LE_ADD] THEN
  REWRITE_TAC[RE_SUB; RE_CX; RE_POW_2; IM_SUB; IM_CX; IM_POW_2] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o
   GEN_REWRITE_RULE I [GSYM REAL_LT_SQUARE])) THEN
  REAL_ARITH_TAC);;

let COMPLEX_DIFFERENTIABLE_AT_CACS = prove
 (`!z. (Im z = &0 ==> abs(Re z) < &1) ==> cacs complex_differentiable at z`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CACS]);;

let COMPLEX_DIFFERENTIABLE_WITHIN_CACS = prove
 (`!s z. (Im z = &0 ==> abs(Re z) < &1)
         ==> cacs complex_differentiable (at z within s)`,
  MESON_TAC[COMPLEX_DIFFERENTIABLE_AT_WITHIN;
            COMPLEX_DIFFERENTIABLE_AT_CACS]);;

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
             HAS_COMPLEX_DERIVATIVE_CACS)));;

let CONTINUOUS_AT_CACS = prove
 (`!z. (Im z = &0 ==> abs(Re z) < &1) ==> cacs continuous at z`,
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CACS;
            HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT]);;

let CONTINUOUS_WITHIN_CACS = prove
 (`!s z. (Im z = &0 ==> abs(Re z) < &1) ==> cacs continuous (at z within s)`,
  MESON_TAC[CONTINUOUS_AT_WITHIN; CONTINUOUS_AT_CACS]);;

let CONTINUOUS_ON_CACS = prove
 (`!s. (!z. z IN s /\ Im z = &0 ==> abs(Re z) < &1) ==> cacs continuous_on s`,
  MESON_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON; CONTINUOUS_AT_CACS]);;

let HOLOMORPHIC_ON_CACS = prove
 (`!s. (!z. z IN s /\ Im z = &0 ==> abs(Re z) < &1) ==> cacs holomorphic_on s`,
  REWRITE_TAC [holomorphic_on] THEN
  MESON_TAC [HAS_COMPLEX_DERIVATIVE_AT_WITHIN; HAS_COMPLEX_DERIVATIVE_CACS]);;

(* ------------------------------------------------------------------------- *)
(* Some crude range theorems (could be sharpened).                           *)
(* ------------------------------------------------------------------------- *)

let CASN_RANGE_LEMMA = prove
 (`!z. abs (Re z) < &1 ==> &0 < Re(ii * z + csqrt(Cx(&1) - z pow 2))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RE_ADD; RE_MUL_II] THEN
  REWRITE_TAC[REAL_ARITH `&0 < --i + r <=> i < r`] THEN
  REWRITE_TAC[csqrt; IM_SUB; RE_SUB; COMPLEX_POW_2; RE_CX; IM_CX] THEN
  REWRITE_TAC[complex_mul; RE; IM] THEN REWRITE_TAC[GSYM complex_mul] THEN
  REWRITE_TAC[REAL_ARITH `r * i + i * r = &2 * r * i`] THEN
  REWRITE_TAC[REAL_SUB_LZERO; REAL_NEG_EQ_0; REAL_ABS_NEG] THEN
  REWRITE_TAC[REAL_NEG_SUB; REAL_ENTIRE; REAL_OF_NUM_EQ; ARITH] THEN
  MAP_EVERY ASM_CASES_TAC [`Re z = &0`; `Im z = &0`] THEN
  ASM_REWRITE_TAC[REAL_SUB_LZERO; REAL_SUB_RZERO] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[RE; SQRT_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV THENL
   [REWRITE_TAC[REAL_ARITH `&1 - (&0 - z) = &1 + z`] THEN
    SIMP_TAC[REAL_LE_ADD; REAL_POS; REAL_LE_SQUARE; RE] THEN
    MATCH_MP_TAC REAL_LT_RSQRT THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `Re(z) pow 2 < &1 pow 2` MP_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LT2 THEN
      ASM_REWRITE_TAC[REAL_ABS_POS; REAL_ABS_NUM; ARITH];
      REWRITE_TAC[REAL_POW_ONE] THEN STRIP_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[RE] THEN
    TRY(MATCH_MP_TAC SQRT_POS_LT) THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_RSQRT THEN
    REWRITE_TAC[REAL_POW_2; REAL_ARITH
     `a < (n + &1 - (b - a)) / &2 <=> (a + b) - &1 < n`] THEN
    REWRITE_TAC[complex_norm] THEN MATCH_MP_TAC REAL_LT_RSQRT THEN
    REWRITE_TAC[RE_SUB; IM_SUB; RE_CX; IM_CX] THEN
    REWRITE_TAC[complex_mul; RE; IM] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o
      GEN_REWRITE_RULE I [GSYM REAL_LT_SQUARE])) THEN
    REAL_ARITH_TAC]);;

let CACS_RANGE_LEMMA = prove
 (`!z. abs(Re z) < &1 ==> &0 < Im(z + ii * csqrt(Cx(&1) - z pow 2))`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `--z:complex` CASN_RANGE_LEMMA) THEN
  ASM_SIMP_TAC[IM_NEG; RE_NEG; IM_ADD; RE_ADD; IM_MUL_II; RE_MUL_II;
               COMPLEX_POW_NEG; ARITH; REAL_ABS_NEG] THEN
  REAL_ARITH_TAC);;

let RE_CASN = prove
 (`!z. Re(casn z) = Im(clog(ii * z + csqrt(Cx(&1) - z pow 2)))`,
  REWRITE_TAC[casn; COMPLEX_MUL_LNEG; RE_NEG; RE_MUL_II; REAL_NEGNEG]);;

let RE_CACS = prove
 (`!z. Re(cacs z) = Im(clog(z + ii * csqrt(Cx(&1) - z pow 2)))`,
  REWRITE_TAC[cacs; COMPLEX_MUL_LNEG; RE_NEG; RE_MUL_II; REAL_NEGNEG]);;

let CASN_BOUNDS = prove
 (`!z. abs(Re z) < &1 ==> abs(Re(casn z)) < pi / &2`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[RE_CASN] THEN
  MATCH_MP_TAC RE_CLOG_POS_LT_IMP THEN ASM_SIMP_TAC[CASN_RANGE_LEMMA]);;

let CACS_BOUNDS = prove
 (`!z. abs(Re z) < &1 ==> &0 < Re(cacs z) /\ Re(cacs z) < pi`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[RE_CACS] THEN
  MATCH_MP_TAC IM_CLOG_POS_LT_IMP THEN ASM_SIMP_TAC[CACS_RANGE_LEMMA]);;

let RE_CACS_BOUNDS = prove
 (`!z. --pi < Re(cacs z) /\ Re(cacs z) <= pi`,
  REWRITE_TAC[RE_CACS] THEN SIMP_TAC[CLOG_WORKS; CACS_BODY_LEMMA]);;

let RE_CACS_BOUND = prove
 (`!z. abs(Re(cacs z)) <= pi`,
  MP_TAC RE_CACS_BOUNDS THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC);;

let RE_CASN_BOUNDS = prove
 (`!z. --pi < Re(casn z) /\ Re(casn z) <= pi`,
  REWRITE_TAC[RE_CASN] THEN SIMP_TAC[CLOG_WORKS; CASN_BODY_LEMMA]);;

let RE_CASN_BOUND = prove
 (`!z. abs(Re(casn z)) <= pi`,
  MP_TAC RE_CASN_BOUNDS THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Interrelations between the two functions.                                 *)
(* ------------------------------------------------------------------------- *)

let CCOS_CASN_NZ = prove
 (`!z. ~(z pow 2 = Cx(&1)) ==> ~(ccos(casn z) = Cx(&0))`,
  REWRITE_TAC[ccos; casn; CEXP_NEG; COMPLEX_RING `ii * --ii * z = z`;
              COMPLEX_RING `--ii * --ii * z = --z`] THEN
  SIMP_TAC[CEXP_CLOG; CASN_BODY_LEMMA;
           COMPLEX_FIELD `~(x = Cx(&0))
                          ==> ((x + inv(x)) / Cx(&2) = Cx(&0) <=>
                                x pow 2 = --Cx(&1))`] THEN
  SIMP_TAC[CSQRT; COMPLEX_FIELD
              `s pow 2 = Cx(&1) - z pow 2
               ==> ((ii * z + s) pow 2 = --Cx(&1) <=>
                    ii * s * z = Cx(&1) - z pow 2)`] THEN
  GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(COMPLEX_RING
   `~(x pow 2 + y pow 2 = Cx(&0)) ==> ~(ii * x = y)`) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  MP_TAC(SPEC `Cx(&1) - z pow 2` CSQRT) THEN CONV_TAC COMPLEX_RING);;

let CSIN_CACS_NZ = prove
 (`!z. ~(z pow 2 = Cx(&1)) ==> ~(csin(cacs z) = Cx(&0))`,
  REWRITE_TAC[csin; cacs; CEXP_NEG; COMPLEX_RING `ii * --ii * z = z`;
              COMPLEX_RING `--ii * --ii * z = --z`] THEN
  SIMP_TAC[CEXP_CLOG; CACS_BODY_LEMMA;
           COMPLEX_FIELD `~(x = Cx(&0))
                          ==> ((x - inv(x)) / (Cx(&2) * ii) = Cx(&0) <=>
                                x pow 2 = Cx(&1))`] THEN
  SIMP_TAC[CSQRT; COMPLEX_FIELD
              `s pow 2 = Cx(&1) - z pow 2
               ==> ((z + ii * s) pow 2 = Cx(&1) <=>
                    ii * s * z = Cx(&1) - z pow 2)`] THEN
  GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(COMPLEX_RING
   `~(x pow 2 + y pow 2 = Cx(&0)) ==> ~(ii * x = y)`) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  MP_TAC(SPEC `Cx(&1) - z pow 2` CSQRT) THEN CONV_TAC COMPLEX_RING);;

let CCOS_CSIN_CSQRT = prove
 (`!z. &0 < cos(Re z) \/ cos(Re z) = &0 /\ Im(z) * sin(Re z) <= &0
       ==> ccos(z) = csqrt(Cx(&1) - csin(z) pow 2)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CSQRT_UNIQUE THEN
  REWRITE_TAC[COMPLEX_EQ_SUB_LADD] THEN ONCE_REWRITE_TAC[COMPLEX_ADD_SYM] THEN
  REWRITE_TAC[CSIN_CIRCLE] THEN REWRITE_TAC[RE_CCOS; IM_CCOS] THEN
  ASM_SIMP_TAC[REAL_LT_MUL_EQ; REAL_HALF; REAL_LT_ADD; REAL_EXP_POS_LT] THEN
  DISJ2_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP(REAL_ARITH
   `x * y <= &0 ==> &0 <= --x * y`)) THEN
  REWRITE_TAC[REAL_MUL_POS_LE] THEN
  SIMP_TAC[REAL_ARITH `x / &2 = &0 <=> x = &0`; REAL_LT_RDIV_EQ; REAL_ADD_LID;
           REAL_SUB_LT; REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH; REAL_MUL_LZERO;
           REAL_SUB_0; REAL_EXP_MONO_LT; REAL_LT_SUB_RADD; REAL_EXP_INJ] THEN
  REAL_ARITH_TAC);;

let CSIN_CCOS_CSQRT = prove
 (`!z. &0 < sin(Re z) \/ sin(Re z) = &0 /\ &0 <= Im(z) * cos(Re z)
       ==> csin(z) = csqrt(Cx(&1) - ccos(z) pow 2)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CSQRT_UNIQUE THEN
  REWRITE_TAC[COMPLEX_EQ_SUB_LADD] THEN ONCE_REWRITE_TAC[COMPLEX_ADD_SYM] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[COMPLEX_ADD_SYM] CSIN_CIRCLE] THEN
  REWRITE_TAC[RE_CSIN; IM_CSIN] THEN
  ASM_SIMP_TAC[REAL_LT_MUL_EQ; REAL_HALF; REAL_LT_ADD; REAL_EXP_POS_LT] THEN
  DISJ2_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[REAL_MUL_POS_LE] THEN
  SIMP_TAC[REAL_ARITH `x / &2 = &0 <=> x = &0`; REAL_LT_RDIV_EQ; REAL_ADD_LID;
           REAL_SUB_LT; REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH; REAL_MUL_LZERO;

           REAL_SUB_0; REAL_EXP_MONO_LT; REAL_LT_SUB_RADD; REAL_EXP_INJ] THEN
  REAL_ARITH_TAC);;

let CASN_CACS_SQRT_POS = prove
 (`!z. (&0 < Re z \/ Re z = &0 /\ &0 <= Im z)
       ==> casn(z) = cacs(csqrt(Cx(&1) - z pow 2))`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[casn; cacs] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(COMPLEX_RING `w = z ==> ii * z + s = s + ii * w`) THEN
  MATCH_MP_TAC CSQRT_UNIQUE THEN
  ASM_REWRITE_TAC[CSQRT] THEN CONV_TAC COMPLEX_RING);;

let CACS_CASN_SQRT_POS = prove
 (`!z. (&0 < Re z \/ Re z = &0 /\ &0 <= Im z)
       ==> cacs(z) = casn(csqrt(Cx(&1) - z pow 2))`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[casn; cacs] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(COMPLEX_RING `w = z ==> z + ii * s = ii * s + w`) THEN
  MATCH_MP_TAC CSQRT_UNIQUE THEN
  ASM_REWRITE_TAC[CSQRT] THEN CONV_TAC COMPLEX_RING);;

let CSIN_CACS = prove
 (`!z. &0 < Re z \/ Re(z) = &0 /\ &0 <= Im z
       ==> csin(cacs z) = csqrt(Cx(&1) - z pow 2)`,
  GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM CSIN_CASN] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC CACS_CASN_SQRT_POS THEN
  ASM_REWRITE_TAC[]);;

let CCOS_CASN = prove
 (`!z. &0 < Re z \/ Re(z) = &0 /\ &0 <= Im z
       ==> ccos(casn z) = csqrt(Cx(&1) - z pow 2)`,
  GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM CCOS_CACS] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC CASN_CACS_SQRT_POS THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Real arcsin.                                                              *)
(* ------------------------------------------------------------------------- *)

let asn = new_definition `asn(x) = Re(casn(Cx x))`;;

let REAL_ASN = prove
 (`!z. real z /\ abs(Re z) <= &1 ==> real(casn z)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN SPEC_TAC(`Re z`,`x:real`) THEN
  REWRITE_TAC[real; casn; COMPLEX_MUL_LNEG; IM_NEG; IM_MUL_II] THEN
  GEN_TAC THEN REWRITE_TAC[RE_CX; REAL_NEG_EQ_0] THEN DISCH_TAC THEN
  MATCH_MP_TAC NORM_CEXP_IMAGINARY THEN
  SIMP_TAC[CEXP_CLOG; CASN_BODY_LEMMA; NORM_EQ_SQUARE] THEN
  REWRITE_TAC[DOT_SQUARE_NORM; COMPLEX_SQNORM] THEN
  REWRITE_TAC[RE_ADD; IM_ADD; RE_MUL_II; IM_MUL_II; RE_CX; IM_CX] THEN
  ASM_SIMP_TAC[GSYM CX_POW; GSYM CX_SUB; GSYM CX_SQRT; REAL_SUB_LE;
               ABS_SQUARE_LE_1; RE_CX; IM_CX; REAL_NEG_0; REAL_ADD_LID;
               SQRT_POW_2] THEN
  REAL_ARITH_TAC);;

let CX_ASN = prove
 (`!x. abs(x) <= &1 ==> Cx(asn x) = casn(Cx x)`,
  REWRITE_TAC[asn] THEN MESON_TAC[REAL; RE_CX; REAL_CX; REAL_ASN]);;

let SIN_ASN = prove
 (`!y. --(&1) <= y /\ y <= &1 ==> sin(asn(y)) = y`,
  REWRITE_TAC[REAL_ARITH `--(&1) <= y /\ y <= &1 <=> abs(y) <= &1`] THEN
  ONCE_REWRITE_TAC[GSYM CX_INJ] THEN SIMP_TAC[CX_ASN; CX_SIN; CSIN_CASN]);;

let ASN_SIN = prove
 (`!x. --(pi / &2) <= x /\ x <= pi / &2 ==> asn(sin(x)) = x`,
  ONCE_REWRITE_TAC[GSYM CX_INJ] THEN SIMP_TAC[CX_ASN; SIN_BOUND; CX_SIN] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CASN_CSIN THEN
  REWRITE_TAC[IM_CX; RE_CX] THEN REPEAT(POP_ASSUM MP_TAC) THEN
  REAL_ARITH_TAC);;

let ASN_BOUNDS_LT = prove
 (`!y. --(&1) < y /\ y < &1 ==> --(pi / &2) < asn(y) /\ asn(y) < pi / &2`,
  GEN_TAC THEN REWRITE_TAC[asn] THEN
  MP_TAC(SPEC `Cx y` CASN_BOUNDS) THEN
  REWRITE_TAC[RE_CX] THEN REAL_ARITH_TAC);;

let ASN_0 = prove
 (`asn(&0) = &0`,
  REWRITE_TAC[asn; CASN_0; RE_CX]);;

let ASN_1 = prove
 (`asn(&1) = pi / &2`,
  REWRITE_TAC[asn; CASN_1; RE_CX]);;

let ASN_NEG_1 = prove
 (`asn(-- &1) = --(pi / &2)`,
  REWRITE_TAC[asn; CX_NEG; CASN_NEG_1; RE_CX; RE_NEG]);;

let ASN_BOUNDS = prove
 (`!y. --(&1) <= y /\ y <= &1 ==> --(pi / &2) <= asn(y) /\ asn(y) <= pi / &2`,
  REWRITE_TAC[REAL_LE_LT] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY MP_TAC [ASN_1; ASN_NEG_1; SPEC `y:real` ASN_BOUNDS_LT] THEN
  ASM_REWRITE_TAC[] THEN REPEAT(POP_ASSUM MP_TAC) THEN
  MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let ASN_BOUNDS_PI2 = prove
 (`!x. &0 <= x /\ x <= &1 ==> &0 <= asn x /\ asn x <= pi / &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`&0`; `asn x`] SIN_MONO_LE_EQ) THEN
  ASM_SIMP_TAC[SIN_0; SIN_ASN; REAL_ARITH `&0 <= x ==> --(&1) <= x`] THEN
  MP_TAC(SPEC `x:real` ASN_BOUNDS) THEN MP_TAC PI_POS THEN
  ASM_REAL_ARITH_TAC);;

let ASN_NEG = prove
 (`!x. -- &1 <= x /\ x <= &1 ==> asn(--x) = --asn(x)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
     [GSYM(MATCH_MP SIN_ASN th)]) THEN
  REWRITE_TAC[GSYM SIN_NEG] THEN MATCH_MP_TAC ASN_SIN THEN
  REWRITE_TAC[REAL_ARITH `--a <= --x /\ --x <= a <=> --a <= x /\ x <= a`] THEN
  ASM_SIMP_TAC[ASN_BOUNDS]);;

let COS_ASN_NZ = prove
 (`!x. --(&1) < x /\ x < &1 ==> ~(cos(asn(x)) = &0)`,
  ONCE_REWRITE_TAC[GSYM CX_INJ] THEN SIMP_TAC[CX_ASN; CX_COS;
    REAL_ARITH `--(&1) < x /\ x < &1 ==> abs(x) <= &1`] THEN
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CCOS_CASN_NZ THEN
  SIMP_TAC[COMPLEX_RING `x pow 2 = Cx(&1) <=> x = Cx(&1) \/ x = --Cx(&1)`] THEN
  REWRITE_TAC[GSYM CX_NEG; CX_INJ] THEN
  ASM_REAL_ARITH_TAC);;

let ASN_MONO_LT_EQ = prove
 (`!x y. abs(x) <= &1 /\ abs(y) <= &1 ==> (asn(x) < asn(y) <=> x < y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sin(asn(x)) < sin(asn(y))` THEN CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SIN_MONO_LT_EQ THEN
    ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THEN MATCH_MP_TAC ASN_BOUNDS;
    BINOP_TAC THEN MATCH_MP_TAC SIN_ASN] THEN
  ASM_REAL_ARITH_TAC);;

let ASN_MONO_LE_EQ = prove
 (`!x y. abs(x) <= &1 /\ abs(y) <= &1 ==> (asn(x) <= asn(y) <=> x <= y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  ASM_SIMP_TAC[ASN_MONO_LT_EQ]);;

let ASN_MONO_LT = prove
 (`!x y. --(&1) <= x /\ x < y /\ y <= &1 ==> asn(x) < asn(y)`,
  MP_TAC ASN_MONO_LT_EQ THEN REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  REAL_ARITH_TAC);;

let ASN_MONO_LE = prove
 (`!x y. --(&1) <= x /\ x <= y /\ y <= &1 ==> asn(x) <= asn(y)`,
  MP_TAC ASN_MONO_LE_EQ THEN REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  REAL_ARITH_TAC);;

let COS_ASN = prove
 (`!x. --(&1) <= x /\ x <= &1 ==> cos(asn x) = sqrt(&1 - x pow 2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(GSYM SQRT_UNIQUE) THEN
  ASM_SIMP_TAC[ASN_BOUNDS; COS_POS_PI_LE; REAL_EQ_SUB_RADD] THEN
  ASM_MESON_TAC[SIN_ASN; SIN_CIRCLE; REAL_ADD_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Real arccosine.                                                           *)
(* ------------------------------------------------------------------------- *)

let acs = new_definition `acs(x) = Re(cacs(Cx x))`;;

let REAL_ACS = prove
 (`!z. real z /\ abs(Re z) <= &1 ==> real(cacs z)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN SPEC_TAC(`Re z`,`x:real`) THEN
  REWRITE_TAC[real; cacs; COMPLEX_MUL_LNEG; IM_NEG; IM_MUL_II] THEN
  GEN_TAC THEN REWRITE_TAC[RE_CX; REAL_NEG_EQ_0] THEN DISCH_TAC THEN
  MATCH_MP_TAC NORM_CEXP_IMAGINARY THEN
  SIMP_TAC[CEXP_CLOG; CACS_BODY_LEMMA; NORM_EQ_SQUARE] THEN
  REWRITE_TAC[DOT_SQUARE_NORM; COMPLEX_SQNORM] THEN
  REWRITE_TAC[RE_ADD; IM_ADD; RE_MUL_II; IM_MUL_II; RE_CX; IM_CX] THEN
  ASM_SIMP_TAC[GSYM CX_POW; GSYM CX_SUB; GSYM CX_SQRT; REAL_SUB_LE;
               ABS_SQUARE_LE_1; RE_CX; IM_CX; REAL_NEG_0; REAL_ADD_LID;
               SQRT_POW_2] THEN
  REAL_ARITH_TAC);;

let CX_ACS = prove
 (`!x. abs(x) <= &1 ==> Cx(acs x) = cacs(Cx x)`,
  REWRITE_TAC[acs] THEN MESON_TAC[REAL; RE_CX; REAL_CX; REAL_ACS]);;

let COS_ACS = prove
 (`!y. --(&1) <= y /\ y <= &1 ==> cos(acs(y)) = y`,
  REWRITE_TAC[REAL_ARITH `--(&1) <= y /\ y <= &1 <=> abs(y) <= &1`] THEN
  ONCE_REWRITE_TAC[GSYM CX_INJ] THEN SIMP_TAC[CX_ACS; CX_COS; CCOS_CACS]);;

let ACS_COS = prove
 (`!x. &0 <= x /\ x <= pi ==> acs(cos(x)) = x`,
  ONCE_REWRITE_TAC[GSYM CX_INJ] THEN SIMP_TAC[CX_ACS; COS_BOUND; CX_COS] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CACS_CCOS THEN
  REWRITE_TAC[IM_CX; RE_CX] THEN ASM_REAL_ARITH_TAC);;

let ACS_BOUNDS_LT = prove
 (`!y. --(&1) < y /\ y < &1 ==> &0 < acs(y) /\ acs(y) < pi`,
  GEN_TAC THEN REWRITE_TAC[acs] THEN
  MP_TAC(SPEC `Cx y` CACS_BOUNDS) THEN
  REWRITE_TAC[RE_CX] THEN REAL_ARITH_TAC);;

let ACS_0 = prove
 (`acs(&0) = pi / &2`,
  REWRITE_TAC[acs; CACS_0; RE_CX]);;

let ACS_1 = prove
 (`acs(&1) = &0`,
  REWRITE_TAC[acs; CACS_1; RE_CX]);;

let ACS_NEG_1 = prove
 (`acs(-- &1) = pi`,
  REWRITE_TAC[acs; CX_NEG; CACS_NEG_1; RE_CX; RE_NEG]);;

let ACS_BOUNDS = prove
 (`!y. --(&1) <= y /\ y <= &1 ==> &0 <= acs(y) /\ acs(y) <= pi`,
  REWRITE_TAC[REAL_LE_LT] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY MP_TAC [ACS_1; ACS_NEG_1; SPEC `y:real` ACS_BOUNDS_LT] THEN
  ASM_REWRITE_TAC[] THEN REPEAT(POP_ASSUM MP_TAC) THEN
  MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let ACS_NEG = prove
 (`!x. -- &1 <= x /\ x <= &1 ==> acs(--x) = pi - acs(x)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
     [GSYM(MATCH_MP COS_ACS th)]) THEN
  ONCE_REWRITE_TAC[GSYM COS_NEG] THEN REWRITE_TAC[GSYM COS_PERIODIC_PI] THEN
  REWRITE_TAC[REAL_ARITH `--x + y:real = y - x`] THEN MATCH_MP_TAC ACS_COS THEN
  SIMP_TAC[REAL_ARITH `&0 <= p - x /\ p - x <= p <=> &0 <= x /\ x <= p`] THEN
  ASM_SIMP_TAC[ACS_BOUNDS]);;

let SIN_ACS_NZ = prove
 (`!x. --(&1) < x /\ x < &1 ==> ~(sin(acs(x)) = &0)`,
  ONCE_REWRITE_TAC[GSYM CX_INJ] THEN SIMP_TAC[CX_ACS; CX_SIN;
    REAL_ARITH `--(&1) < x /\ x < &1 ==> abs(x) <= &1`] THEN
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CSIN_CACS_NZ THEN
  SIMP_TAC[COMPLEX_RING `x pow 2 = Cx(&1) <=> x = Cx(&1) \/ x = --Cx(&1)`] THEN
  REWRITE_TAC[GSYM CX_NEG; CX_INJ] THEN
  ASM_REAL_ARITH_TAC);;

let ACS_MONO_LT_EQ = prove
 (`!x y. abs(x) <= &1 /\ abs(y) <= &1 ==> (acs(x) < acs(y) <=> y < x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `cos(acs(y)) < cos(acs(x))` THEN CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC COS_MONO_LT_EQ THEN
    ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THEN MATCH_MP_TAC ACS_BOUNDS;
    BINOP_TAC THEN MATCH_MP_TAC COS_ACS] THEN
  ASM_REAL_ARITH_TAC);;

let ACS_MONO_LE_EQ = prove
 (`!x y. abs(x) <= &1 /\ abs(y) <= &1 ==> (acs(x) <= acs(y) <=> y <= x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  ASM_SIMP_TAC[ACS_MONO_LT_EQ]);;

let ACS_MONO_LT = prove
 (`!x y. --(&1) <= x /\ x < y /\ y <= &1 ==> acs(y) < acs(x)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`y:real`; `x:real`] ACS_MONO_LT_EQ) THEN
  REAL_ARITH_TAC);;

let ACS_MONO_LE = prove
 (`!x y. --(&1) <= x /\ x <= y /\ y <= &1 ==> acs(y) <= acs(x)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`y:real`; `x:real`] ACS_MONO_LE_EQ) THEN
  REAL_ARITH_TAC);;

let SIN_ACS = prove
 (`!x. --(&1) <= x /\ x <= &1 ==> sin(acs x) = sqrt(&1 - x pow 2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(GSYM SQRT_UNIQUE) THEN
  ASM_SIMP_TAC[ACS_BOUNDS; SIN_POS_PI_LE; REAL_EQ_SUB_RADD] THEN
  ASM_MESON_TAC[COS_ACS; SIN_CIRCLE]);;

let ACS_INJ = prove
 (`!x y. abs(x) <= &1 /\ abs(y) <= &1 ==> (acs x = acs y <=> x = y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
  ASM_SIMP_TAC[ACS_MONO_LE_EQ] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Some interrelationships among the real inverse trig functions.            *)
(* ------------------------------------------------------------------------- *)

let ACS_ATN = prove
 (`!x. -- &1 < x /\ x < &1 ==> acs(x) = pi / &2 - atn(x / sqrt(&1 - x pow 2))`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x:real = p - y <=> y - (p - x) = &0`] THEN
  MATCH_MP_TAC SIN_EQ_0_PI THEN
  ASM_SIMP_TAC[ATN_BOUND; ACS_BOUNDS; REAL_LT_IMP_LE; REAL_ARITH
   `abs(x) < pi / &2 /\ &0 <= y /\ y <= pi
    ==> --pi < x - (pi / &2 - y) /\ x - (pi / &2 - y) < pi`] THEN
  SUBGOAL_THEN `tan(atn(x / sqrt(&1 - x pow 2))) = tan(pi / &2 - acs x)`
  MP_TAC THENL
   [REWRITE_TAC[TAN_COT; ATN_TAN] THEN REWRITE_TAC[tan] THEN
    ASM_SIMP_TAC[SIN_ACS; COS_ACS; REAL_LT_IMP_LE; REAL_INV_DIV];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_SUB_0] THEN
  ASM_SIMP_TAC[SIN_ACS_NZ; GSYM SIN_COS; COS_ATN_NZ; REAL_SUB_TAN; REAL_FIELD
   `~(y = &0) /\ ~(z = &0) ==> (x / (y * z) = &0 <=> x = &0)`]);;

let ASN_PLUS_ACS = prove
 (`!x. -- &1 <= x /\ x <= &1 ==> asn(x) + acs(x) = pi / &2`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x + y:real = p <=> x = p - y`] THEN
  MATCH_MP_TAC SIN_INJ_PI THEN
  ASM_SIMP_TAC[SIN_PI2; COS_PI2; SIN_SUB; REAL_MUL_LZERO; REAL_SUB_RZERO] THEN
  ASM_SIMP_TAC[SIN_ASN; COS_ACS; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_ARITH `--p <= p - x <=> x <= &2 * p`;
              REAL_ARITH `p - x <= p <=> &0 <= x`] THEN
  ASM_SIMP_TAC[ASN_BOUNDS; ACS_BOUNDS; REAL_ARITH `&2 * x / &2 = x`]);;

let ASN_ACS = prove
 (`!x. -- &1 <= x /\ x <= &1 ==> asn(x) = pi / &2 - acs(x)`,
  SIMP_TAC[REAL_EQ_SUB_LADD; ASN_PLUS_ACS]);;

let ACS_ASN = prove
 (`!x. -- &1 <= x /\ x <= &1 ==> acs(x) = pi / &2 - asn(x)`,
  SIMP_TAC[ASN_ACS] THEN REAL_ARITH_TAC);;

let ASN_ATN = prove
 (`!x. -- &1 < x /\ x < &1 ==> asn(x) = atn(x / sqrt(&1 - x pow 2))`,
  SIMP_TAC[ASN_ACS; REAL_LT_IMP_LE; ACS_ATN] THEN REAL_ARITH_TAC);;

let ASN_ACS_SQRT_POS = prove
 (`!x. &0 <= x /\ x <= &1 ==> asn(x) = acs(sqrt(&1 - x pow 2))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[asn; acs] THEN
  ASM_SIMP_TAC[CX_SQRT; REAL_SUB_LE; REAL_POW_1_LE; CX_SUB; CX_POW] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC CASN_CACS_SQRT_POS THEN
  ASM_REWRITE_TAC[RE_CX; IM_CX] THEN ASM_REAL_ARITH_TAC);;

let ASN_ACS_SQRT_NEG = prove
 (`!x. -- &1 <= x /\ x <= &0 ==> asn(x) = --acs(sqrt(&1 - x pow 2))`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x = --y <=> (--x:real) = y`] THEN
  ASM_SIMP_TAC[GSYM ASN_NEG; REAL_ARITH `x <= &0 ==> x <= &1`] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(x:real) pow 2 = (--x) pow 2`] THEN
  MATCH_MP_TAC ASN_ACS_SQRT_POS THEN ASM_REAL_ARITH_TAC);;

let ACS_ASN_SQRT_POS = prove
 (`!x. &0 <= x /\ x <= &1 ==> acs(x) = asn(sqrt(&1 - x pow 2))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[asn; acs] THEN
  ASM_SIMP_TAC[CX_SQRT; REAL_SUB_LE; REAL_POW_1_LE; CX_SUB; CX_POW] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC CACS_CASN_SQRT_POS THEN
  ASM_REWRITE_TAC[RE_CX; IM_CX] THEN ASM_REAL_ARITH_TAC);;

let ACS_ASN_SQRT_NEG = prove
 (`!x. -- &1 <= x /\ x <= &0 ==> acs(x) = pi - asn(sqrt(&1 - x pow 2))`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `--x:real` ACS_ASN_SQRT_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[REAL_POW_NEG; ARITH]] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_NEG_NEG] THEN
  MATCH_MP_TAC ACS_NEG THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* More delicate continuity results for arcsin and arccos.                   *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_ON_CASN_REAL = prove
 (`casn continuous_on {w | real w /\ abs(Re w) <= &1}`,
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `IMAGE csin {z | real z /\ abs(Re z) <= pi / &2}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_INVERSE THEN
    REWRITE_TAC[CONTINUOUS_ON_CSIN] THEN CONJ_TAC THENL
     [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
       [MATCH_MP_TAC BOUNDED_SUBSET THEN
        EXISTS_TAC `cball(Cx(&0),pi / &2)` THEN
        REWRITE_TAC[BOUNDED_CBALL; SUBSET; IN_ELIM_THM; IN_CBALL] THEN
        REWRITE_TAC[dist; COMPLEX_SUB_LZERO; NORM_NEG; real] THEN
        X_GEN_TAC `z:complex` THEN
        MP_TAC(SPEC `z:complex` COMPLEX_NORM_LE_RE_IM) THEN REAL_ARITH_TAC;
        SIMP_TAC[SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`;
                  GSYM REAL_BOUNDS_LE] THEN
        SIMP_TAC[CLOSED_INTER; CLOSED_REAL_SET; CLOSED_HALFSPACE_RE_LE;
                 REWRITE_RULE[real_ge] CLOSED_HALFSPACE_RE_GE]];
      SIMP_TAC[SUBSET; IMP_CONJ; FORALL_REAL; IN_ELIM_THM; RE_CX] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC CASN_CSIN THEN
      REWRITE_TAC[RE_CX; IM_CX] THEN ASM_REAL_ARITH_TAC];
    SIMP_TAC[SUBSET; IMP_CONJ; FORALL_REAL; IN_ELIM_THM; RE_CX; IN_IMAGE] THEN
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    EXISTS_TAC `Cx(asn x)` THEN
    ASM_SIMP_TAC[RE_CX; ASN_BOUNDS; REAL_BOUNDS_LE; REAL_CX; SIN_ASN;
                 GSYM CX_SIN] THEN
    ASM_MESON_TAC[REAL_BOUNDS_LE; ASN_BOUNDS]]);;

let CONTINUOUS_WITHIN_CASN_REAL = prove
 (`!z. casn continuous (at z within {w | real w /\ abs(Re w) <= &1})`,
  GEN_TAC THEN ASM_CASES_TAC `z IN {w | real w /\ abs(Re w) <= &1}` THENL
   [ASM_SIMP_TAC[REWRITE_RULE[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]
      CONTINUOUS_ON_CASN_REAL];
    MATCH_MP_TAC CONTINUOUS_WITHIN_CLOSED_NONTRIVIAL THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_BOUNDS_LE] THEN
    ASM_SIMP_TAC[SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
    SIMP_TAC[CLOSED_INTER; CLOSED_REAL_SET; CLOSED_HALFSPACE_RE_LE;
             REWRITE_RULE[real_ge] CLOSED_HALFSPACE_RE_GE]]);;

let CONTINUOUS_ON_CACS_REAL = prove
 (`cacs continuous_on {w | real w /\ abs(Re w) <= &1}`,
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `IMAGE ccos {z | real z /\ &0 <= Re z /\ Re z <= pi}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_INVERSE THEN
    REWRITE_TAC[CONTINUOUS_ON_CCOS] THEN CONJ_TAC THENL
     [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
       [MATCH_MP_TAC BOUNDED_SUBSET THEN
        EXISTS_TAC `cball(Cx(&0),&2 * pi)` THEN
        REWRITE_TAC[BOUNDED_CBALL; SUBSET; IN_ELIM_THM; IN_CBALL] THEN
        REWRITE_TAC[dist; COMPLEX_SUB_LZERO; NORM_NEG; real] THEN
        X_GEN_TAC `z:complex` THEN
        MP_TAC(SPEC `z:complex` COMPLEX_NORM_LE_RE_IM) THEN REAL_ARITH_TAC;
        SIMP_TAC[SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
        SIMP_TAC[CLOSED_INTER; CLOSED_REAL_SET; CLOSED_HALFSPACE_RE_LE;
                 REWRITE_RULE[real_ge] CLOSED_HALFSPACE_RE_GE]];
      SIMP_TAC[SUBSET; IMP_CONJ; FORALL_REAL; IN_ELIM_THM; RE_CX] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC CACS_CCOS THEN
      REWRITE_TAC[RE_CX; IM_CX] THEN ASM_REAL_ARITH_TAC];
    SIMP_TAC[SUBSET; IMP_CONJ; FORALL_REAL; IN_ELIM_THM; RE_CX; IN_IMAGE] THEN
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    EXISTS_TAC `Cx(acs x)` THEN
    ASM_SIMP_TAC[RE_CX; ACS_BOUNDS; REAL_BOUNDS_LE; REAL_CX; COS_ACS;
                 GSYM CX_COS]]);;

let CONTINUOUS_WITHIN_CACS_REAL = prove
 (`!z. cacs continuous (at z within {w | real w /\ abs(Re w) <= &1})`,
  GEN_TAC THEN ASM_CASES_TAC `z IN {w | real w /\ abs(Re w) <= &1}` THENL
   [ASM_SIMP_TAC[REWRITE_RULE[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]
      CONTINUOUS_ON_CACS_REAL];
    MATCH_MP_TAC CONTINUOUS_WITHIN_CLOSED_NONTRIVIAL THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_BOUNDS_LE] THEN
    ASM_SIMP_TAC[SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
    SIMP_TAC[CLOSED_INTER; CLOSED_REAL_SET; CLOSED_HALFSPACE_RE_LE;
             REWRITE_RULE[real_ge] CLOSED_HALFSPACE_RE_GE]]);;

(* ------------------------------------------------------------------------- *)
(* Some limits, most involving sequences of transcendentals.                 *)
(* ------------------------------------------------------------------------- *)

let LIM_CX_OVER_CEXP = prove
 (`((\x. Cx x / cexp(Cx x)) --> Cx(&0)) at_posinfinity`,
  ONCE_REWRITE_TAC[LIM_NULL_COMPLEX_NORM] THEN
  REWRITE_TAC[LIM_AT_POSINFINITY; real_ge] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `max (&1) (&1 + &2 * log (&2 / e))` THEN
  X_GEN_TAC `x:real` THEN REWRITE_TAC[REAL_MAX_LE] THEN STRIP_TAC THEN
  REWRITE_TAC[dist; COMPLEX_SUB_RZERO; COMPLEX_NORM_CX; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[COMPLEX_NORM_DIV; NORM_CEXP; COMPLEX_NORM_CX; RE_CX] THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_EXP_POS_LT] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ] THEN GEN_REWRITE_TAC
   (RAND_CONV o RAND_CONV) [REAL_ARITH `x = x / &2 + x / &2`] THEN
  REWRITE_TAC[REAL_EXP_ADD; REAL_ARITH
   `x / e < y * y <=> x / &2 * &2 / e < y * y`] THEN
  MATCH_MP_TAC REAL_LT_MUL2 THEN REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH
     `&1 <= x /\ &1 + x / &2 <= y ==> abs x / &2 < y`) THEN
    ASM_REWRITE_TAC[REAL_EXP_LE_X];
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE];
    MATCH_MP_TAC LOG_MONO_LT_REV THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH; LOG_EXP;
                 REAL_ARITH `&1 <= x ==> &0 < x`; REAL_EXP_POS_LT] THEN
    ASM_REAL_ARITH_TAC]);;

let LIM_Z_TIMES_CLOG = prove
 (`((\z. z * clog z) --> Cx(&0)) (at (Cx(&0)))`,
  ONCE_REWRITE_TAC[SPEC `clog z` COMPLEX_EXPAND] THEN
  REWRITE_TAC[COMPLEX_ADD_LDISTRIB] THEN
  MATCH_MP_TAC LIM_NULL_COMPLEX_ADD THEN CONJ_TAC THENL
   [SIMP_TAC[RE_CLOG] THEN MP_TAC LIM_CX_OVER_CEXP THEN
    REWRITE_TAC[LIM_AT_POSINFINITY; LIM_AT; dist; COMPLEX_SUB_RZERO] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
    ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[real_ge] THEN
    REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; NORM_CEXP; RE_CX] THEN
    DISCH_THEN(X_CHOOSE_TAC `b:real`) THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    EXISTS_TAC `inv(exp b)` THEN SIMP_TAC[REAL_LT_INV_EQ; REAL_EXP_POS_LT] THEN
    X_GEN_TAC `z:complex` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `log(inv(norm(z:complex)))`) THEN
    ASM_SIMP_TAC[LOG_INV; EXP_LOG; REAL_LT_INV_EQ] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[real_div; REAL_INV_INV; REAL_ABS_NEG] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    GEN_REWRITE_TAC I [GSYM REAL_EXP_MONO_LE] THEN
    ASM_SIMP_TAC[EXP_LOG; REAL_EXP_NEG] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC LIM_NULL_COMPLEX_RMUL_BOUNDED THEN
    REWRITE_TAC[LIM_AT_ID] THEN EXISTS_TAC `pi` THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_II; COMPLEX_NORM_CX] THEN
    REWRITE_TAC[EVENTUALLY_AT; dist; COMPLEX_SUB_0; COMPLEX_NORM_NZ] THEN
    SIMP_TAC[CLOG_WORKS; REAL_MUL_LID; REAL_ABS_BOUNDS; REAL_LT_IMP_LE] THEN
    MESON_TAC[REAL_LT_01]]);;

let LIM_LOG_OVER_Z = prove
 (`((\z. clog z / z) --> Cx(&0)) at_infinity`,
  SIMP_TAC[LIM_AT_INFINITY_COMPLEX_0; o_DEF; complex_div; COMPLEX_INV_INV;
           CLOG_INV] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING
   `clog(inv z) * z = z * (clog z + clog(inv z)) - z * clog z`] THEN
  MATCH_MP_TAC LIM_NULL_COMPLEX_SUB THEN
  REWRITE_TAC[LIM_Z_TIMES_CLOG] THEN
  MATCH_MP_TAC LIM_NULL_COMPLEX_RMUL_BOUNDED THEN
  REWRITE_TAC[LIM_AT_ID] THEN EXISTS_TAC `&2 * pi` THEN
  REWRITE_TAC[EVENTUALLY_AT; dist; COMPLEX_SUB_RZERO; COMPLEX_NORM_NZ] THEN
  EXISTS_TAC `&1` THEN SIMP_TAC[REAL_LT_01] THEN
  X_GEN_TAC `z:complex` THEN STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [COMPLEX_EXPAND] THEN
  ASM_SIMP_TAC[RE_ADD; RE_CLOG; REAL_LT_INV_EQ; COMPLEX_INV_EQ_0;
               COMPLEX_NORM_INV; LOG_INV; COMPLEX_NORM_NZ] THEN
  REWRITE_TAC[REAL_ADD_RINV; COMPLEX_ADD_LID; COMPLEX_NORM_MUL] THEN
  REWRITE_TAC[COMPLEX_NORM_II; COMPLEX_NORM_CX; IM_ADD] THEN
  MATCH_MP_TAC(REAL_ARITH
   `--pi < x /\ x <= pi /\ --pi < y /\ y <= pi
    ==> &1 * abs(x + y) <= &2 * pi`) THEN
  ASM_SIMP_TAC[CLOG_WORKS; COMPLEX_INV_EQ_0]);;

let LIM_LOG_OVER_POWER = prove
 (`!s. &0 < Re s
       ==> ((\x. clog(Cx x) / (Cx x) cpow s) --> Cx(&0)) at_posinfinity`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIM_AT_POSINFINITY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN REWRITE_TAC[real_ge] THEN
  MP_TAC(REWRITE_RULE[LIM_AT_POSINFINITY] LIM_CX_OVER_CEXP) THEN
  DISCH_THEN(MP_TAC o SPEC `Re s * e`) THEN
  ASM_SIMP_TAC[REAL_LT_MUL; real_ge; dist; COMPLEX_SUB_RZERO] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; NORM_CEXP; RE_CX] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  EXISTS_TAC `max (&1) (exp((abs B + &1) / Re s))` THEN X_GEN_TAC `x:real` THEN
  REWRITE_TAC[REAL_MAX_LE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[NORM_CPOW_REAL; COMPLEX_NORM_DIV; REAL_CX; RE_CX;
               GSYM CX_LOG; COMPLEX_NORM_CX; real_abs; LOG_POS] THEN
  MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `Re s` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `Re s * log x`) THEN
  ASM_SIMP_TAC[real_abs; REAL_LE_MUL; LOG_POS; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `abs b + &1 <= x * y ==> b <= y * x`) THEN
  ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ] THEN
  ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN
  ASM_SIMP_TAC[EXP_LOG]);;

let LIM_LOG_OVER_X = prove
 (`((\x. clog(Cx x) / Cx x) --> Cx(&0)) at_posinfinity`,
  MP_TAC(SPEC `Cx(&1)` LIM_LOG_OVER_POWER) THEN
  REWRITE_TAC[CPOW_N; RE_CX; REAL_LT_01; COMPLEX_POW_1] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
  REWRITE_TAC[EVENTUALLY_AT_POSINFINITY; CX_INJ] THEN
  EXISTS_TAC `&1` THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let LIM_LOG_OVER_POWER_N = prove
 (`!s. &0 < Re s
       ==> ((\n. clog(Cx(&n)) / Cx(&n) cpow s) --> Cx(&0)) sequentially`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_POSINFINITY_SEQUENTIALLY THEN
  ASM_SIMP_TAC[LIM_LOG_OVER_POWER]);;

let LIM_LOG_OVER_N = prove
 (`((\n. clog(Cx(&n)) / Cx(&n)) --> Cx(&0)) sequentially`,
  MP_TAC(SPEC `Cx(&1)` LIM_LOG_OVER_POWER_N) THEN
  SIMP_TAC[RE_CX; REAL_LT_01] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY; CPOW_N; CX_INJ] THEN EXISTS_TAC `1` THEN
  SIMP_TAC[COMPLEX_POW_1; REAL_OF_NUM_EQ; ARITH_RULE `1 <= n <=> ~(n = 0)`]);;

let LIM_1_OVER_POWER = prove
 (`!s. &0 < Re s
       ==> ((\n. Cx(&1) / Cx(&n) cpow s) --> Cx(&0)) sequentially`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_NULL_COMPLEX_BOUND THEN
  EXISTS_TAC `\n. clog(Cx(&n)) / Cx(&n) cpow s` THEN
  ASM_SIMP_TAC[LIM_LOG_OVER_POWER_N] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  MP_TAC(ISPEC `exp(&1)` REAL_ARCH_SIMPLE) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  ASM_CASES_TAC `N = 0` THENL
   [ASM_SIMP_TAC[GSYM REAL_NOT_LT; REAL_EXP_POS_LT]; ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[complex_div; COMPLEX_NORM_MUL] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM CX_LOG; REAL_OF_NUM_LT; LT_NZ;
               COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= abs y`) THEN
  ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN
  ASM_SIMP_TAC[EXP_LOG; REAL_OF_NUM_LT; LT_NZ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN ASM_REAL_ARITH_TAC);;

let LIM_INV_Z_OFFSET = prove
 (`!z. ((\w. inv(w + z)) --> Cx(&0)) at_infinity`,
  GEN_TAC THEN REWRITE_TAC[LIM_AT_INFINITY_COMPLEX_0; o_DEF] THEN
  SIMP_TAC[COMPLEX_INV_DIV; COMPLEX_FIELD
   `~(w = Cx(&0)) ==> inv w + z = (Cx(&1) + w * z) / w`] THEN
  GEN_REWRITE_TAC LAND_CONV
   [COMPLEX_FIELD `Cx(&0) = Cx(&0) / (Cx(&1) + Cx(&0) * z)`] THEN
  MATCH_MP_TAC LIM_COMPLEX_DIV THEN
  REWRITE_TAC[COMPLEX_RING `~(Cx(&1) + Cx(&0) * z = Cx(&0))`] THEN
  CONJ_TAC THEN LIM_TAC);;

let LIM_INV_Z = prove
 (`((\z. inv(z)) --> Cx(&0)) at_infinity`,
  ONCE_REWRITE_TAC[MESON[COMPLEX_ADD_RID] `inv z = inv(z + Cx(&0))`] THEN
  REWRITE_TAC[LIM_INV_Z_OFFSET]);;

let LIM_INV_X_OFFSET = prove
 (`!z. ((\x. inv(Cx x + z)) --> Cx(&0)) at_posinfinity`,
  GEN_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[o_DEF] LIM_INFINITY_POSINFINITY_CX) THEN
  REWRITE_TAC[LIM_INV_Z_OFFSET]);;

let LIM_INV_X = prove
 (`((\x. inv(Cx x)) --> Cx(&0)) at_posinfinity`,
  MATCH_MP_TAC(REWRITE_RULE[o_DEF] LIM_INFINITY_POSINFINITY_CX) THEN
  REWRITE_TAC[REWRITE_RULE[ETA_AX] LIM_INV_Z]);;

let LIM_INV_N_OFFSET = prove
 (`!z. ((\n. inv(Cx(&n) + z)) --> Cx(&0)) sequentially`,
  GEN_TAC THEN MATCH_MP_TAC LIM_POSINFINITY_SEQUENTIALLY THEN
  REWRITE_TAC[LIM_INV_X_OFFSET]);;

let LIM_1_OVER_N = prove
 (`((\n. Cx(&1) / Cx(&n)) --> Cx(&0)) sequentially`,
  MP_TAC(SPEC `Cx(&1)` LIM_1_OVER_POWER) THEN SIMP_TAC[RE_CX; REAL_LT_01] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY; CPOW_N; CX_INJ] THEN EXISTS_TAC `1` THEN
  SIMP_TAC[COMPLEX_POW_1; REAL_OF_NUM_EQ; ARITH_RULE `1 <= n <=> ~(n = 0)`]);;

let LIM_INV_N = prove
 (`((\n. inv(Cx(&n))) --> Cx(&0)) sequentially`,
  MP_TAC LIM_1_OVER_N THEN REWRITE_TAC[complex_div; COMPLEX_MUL_LID]);;

let LIM_INV_Z_POW_OFFSET = prove
 (`!z n. 1 <= n ==> ((\w. inv(w + z) pow n) --> Cx(&0)) at_infinity`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `Cx(&0) = Cx(&0) pow n` SUBST1_TAC THENL
   [ASM_SIMP_TAC[COMPLEX_POW_ZERO; LE_1];
    MATCH_MP_TAC LIM_COMPLEX_POW THEN REWRITE_TAC[LIM_INV_Z_OFFSET]]);;

let LIM_INV_Z_POW = prove
 (`!n. 1 <= n ==> ((\z. inv(z) pow n) --> Cx(&0)) at_infinity`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `Cx(&0) = Cx(&0) pow n` SUBST1_TAC THENL
   [ASM_SIMP_TAC[COMPLEX_POW_ZERO; LE_1];
    MATCH_MP_TAC LIM_COMPLEX_POW THEN
    REWRITE_TAC[REWRITE_RULE[ETA_AX] LIM_INV_Z]]);;

let LIM_INV_X_POW_OFFSET = prove
 (`!z n. 1 <= n ==> ((\x. inv(Cx x + z) pow n) --> Cx(&0)) at_posinfinity`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[o_DEF] LIM_INFINITY_POSINFINITY_CX) THEN
  ASM_SIMP_TAC[LIM_INV_Z_POW_OFFSET]);;

let LIM_INV_X_POW = prove
 (`!n. 1 <= n ==> ((\x. inv(Cx x) pow n) --> Cx(&0)) at_posinfinity`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[o_DEF] LIM_INFINITY_POSINFINITY_CX) THEN
  ASM_SIMP_TAC[LIM_INV_Z_POW]);;

let LIM_INV_N_POW_OFFSET = prove
 (`!z m. 1 <= m ==> ((\n. inv(Cx(&n) + z) pow m) --> Cx(&0)) sequentially`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_POSINFINITY_SEQUENTIALLY THEN
  ASM_SIMP_TAC[LIM_INV_X_POW_OFFSET]);;

let LIM_INV_N_POW = prove
 (`!m. 1 <= m ==> ((\n. inv(Cx(&n)) pow m) --> Cx(&0)) sequentially`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_POSINFINITY_SEQUENTIALLY THEN
  ASM_SIMP_TAC[LIM_INV_X_POW]);;

let LIM_1_OVER_LOG = prove
 (`((\n. Cx(&1) / clog(Cx(&n))) --> Cx(&0)) sequentially`,
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN
  DISCH_TAC THEN X_CHOOSE_TAC `N:num` (SPEC `exp(inv e)` REAL_ARCH_SIMPLE) THEN
  EXISTS_TAC `N + 1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[dist; COMPLEX_SUB_RZERO; COMPLEX_MUL_LID; complex_div] THEN
  SUBGOAL_THEN `0 < n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD]) THEN
  ASM_SIMP_TAC[GSYM CX_LOG; COMPLEX_NORM_CX; COMPLEX_NORM_INV] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
  MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH `a < x ==> a < abs x`) THEN
  ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LT] THEN
  ASM_SIMP_TAC[EXP_LOG] THEN ASM_REAL_ARITH_TAC);;

let LIM_N_TIMES_POWN = prove
 (`!z. norm(z) < &1 ==> ((\n. Cx(&n) * z pow n) --> Cx(&0)) sequentially`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THEN
  ASM_SIMP_TAC[COMPLEX_POW_ZERO; LIM_CASES_FINITE_SEQUENTIALLY; LIM_CONST;
               COND_RAND; FINITE_SING; SING_GSPEC; COMPLEX_MUL_RZERO] THEN
  MP_TAC LIM_LOG_OVER_N THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; dist; COMPLEX_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `log(inv(norm(z:complex))) / &2`) THEN
  ASM_SIMP_TAC[LOG_POS_LT; REAL_INV_1_LT; COMPLEX_NORM_NZ; REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "+")) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `N2:num` STRIP_ASSUME_TAC o
              GEN_REWRITE_RULE I [REAL_ARCH_INV]) THEN
  EXISTS_TAC `MAX 1 (MAX N1 N2)` THEN
  REWRITE_TAC[ARITH_RULE `MAX a b <= c <=> a <= c /\ b <= c`] THEN
  X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ASM_SIMP_TAC[GSYM CX_LOG; REAL_OF_NUM_LT; LE_1; GSYM CX_DIV;
               COMPLEX_NORM_CX; REAL_ABS_DIV; REAL_ABS_NUM] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; ARITH; real_abs;
               LOG_POS; REAL_OF_NUM_LE] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a / b * &2 = (&2 * a) / b`] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_MONO_LT] THEN
  ASM_SIMP_TAC[REAL_EXP_N; EXP_LOG; REAL_OF_NUM_LT; LE_1;
               REAL_LT_INV_EQ; COMPLEX_NORM_NZ] THEN
  REWRITE_TAC[REAL_POW_INV] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_MUL_LID] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LT_RDIV_EQ; REAL_POW_LT; COMPLEX_NORM_NZ;
               COMPLEX_NORM_MUL; COMPLEX_NORM_NUM; COMPLEX_NORM_POW] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N2)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(&n)` THEN
  ASM_SIMP_TAC[REAL_LE_INV2; REAL_OF_NUM_LE; REAL_OF_NUM_LT; LE_1] THEN
  MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `&n` THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_OF_NUM_LT; LE_1] THEN
  ASM_REAL_ARITH_TAC);;

let LIM_N_OVER_POWN = prove
 (`!z. &1 < norm(z) ==> ((\n. Cx(&n) / z pow n) --> Cx(&0)) sequentially`,
  ASM_SIMP_TAC[complex_div; GSYM COMPLEX_POW_INV; COMPLEX_NORM_INV;
               REAL_INV_LT_1; LIM_N_TIMES_POWN]);;

let LIM_POWN = prove
 (`!z. norm(z) < &1 ==> ((\n. z pow n) --> Cx(&0)) sequentially`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_NULL_COMPARISON_COMPLEX THEN
  EXISTS_TAC `\n. Cx(&n) * z pow n` THEN ASM_SIMP_TAC[LIM_N_TIMES_POWN] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  REWRITE_TAC[REAL_ARITH `a <= n * a <=> &0 <= (n - &1) * a`] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
  ASM_REWRITE_TAC[NORM_POS_LE; REAL_SUB_LE; REAL_OF_NUM_LE]);;

let LIM_CSIN_OVER_X = prove
 (`((\z. csin z / z) --> Cx(&1)) (at (Cx(&0)))`,
  ONCE_REWRITE_TAC[LIM_NULL_COMPLEX] THEN
  MATCH_MP_TAC LIM_NULL_COMPARISON_COMPLEX THEN
  EXISTS_TAC `\z. cexp(Cx(abs(Im z))) * z pow 2 / Cx(&2)` THEN
  REWRITE_TAC[EVENTUALLY_AT] THEN CONJ_TAC THENL
   [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01; dist; COMPLEX_SUB_RZERO] THEN
    X_GEN_TAC `z:complex` THEN SIMP_TAC[COMPLEX_NORM_NZ] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `norm(z:complex)` THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_NZ; GSYM COMPLEX_NORM_MUL] THEN
    ASM_SIMP_TAC[COMPLEX_FIELD
     `~(z = Cx(&0)) ==> z * (s / z - Cx(&1)) = s - z`] THEN
    REWRITE_TAC[GSYM CX_EXP; COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    REWRITE_TAC[real_abs; REAL_EXP_POS_LE] THEN REWRITE_TAC[GSYM real_abs] THEN
    MP_TAC(ISPECL [`0`; `z:complex`] TAYLOR_CSIN) THEN
    REWRITE_TAC[VSUM_SING_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[complex_pow; COMPLEX_POW_1; COMPLEX_DIV_1] THEN
    REWRITE_TAC[COMPLEX_MUL_LID] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
    REWRITE_TAC[COMPLEX_NORM_POW] THEN REAL_ARITH_TAC;
    LIM_TAC THEN TRY(CONV_TAC COMPLEX_RING) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
    REWRITE_TAC[CONTINUOUS_AT_CEXP] THEN
    REWRITE_TAC[CONTINUOUS_AT; LIM_AT; dist; COMPLEX_SUB_RZERO;
                IM_CX; REAL_ABS_NUM; COMPLEX_NORM_CX; REAL_ABS_ABS] THEN
    MESON_TAC[REAL_LET_TRANS; COMPLEX_NORM_GE_RE_IM]]);;

(* ------------------------------------------------------------------------- *)
(* Roots of unity.                                                           *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_ROOT_POLYFUN = prove
 (`!n z a.
        1 <= n
        ==> (z pow n = a <=>
             vsum(0..n) (\i. (if i = 0 then --a else if i = n then Cx(&1)
                              else Cx(&0)) * z pow i) = Cx(&0))`,
  ASM_SIMP_TAC[VSUM_CLAUSES_RIGHT; LE_1; LE_0] THEN
  SIMP_TAC[VSUM_CLAUSES_LEFT; LE_0; ADD_CLAUSES] THEN
  ASM_SIMP_TAC[LE_1; ARITH_RULE `1 <= n /\ 1 <= i /\ i <= n - 1
                           ==> ~(i = n)`] THEN
  REWRITE_TAC[COMPLEX_MUL_LZERO; complex_pow; COMPLEX_MUL_RID] THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0; VSUM_0; VECTOR_ADD_RID] THEN
  REWRITE_TAC[COMPLEX_VEC_0] THEN CONV_TAC COMPLEX_RING);;

let COMPLEX_ROOT_UNITY = prove
 (`!n j. ~(n = 0)
         ==> cexp(Cx(&2) * Cx pi * ii * Cx(&j / &n)) pow n = Cx(&1)`,
  REWRITE_TAC[GSYM CEXP_N; CX_DIV] THEN
  ASM_SIMP_TAC[CX_INJ; complex_div; REAL_OF_NUM_EQ; COMPLEX_FIELD
    `~(n = Cx(&0)) ==> n * t * p * ii * j * inv(n) = j * (ii * t * p)`] THEN
  REWRITE_TAC[CEXP_N; GSYM CX_MUL] THEN
  REWRITE_TAC[CEXP_EULER; GSYM CX_MUL; GSYM CX_SIN; GSYM CX_COS] THEN
  REWRITE_TAC[COS_NPI; SIN_NPI; REAL_POW_NEG; COMPLEX_MUL_RZERO;
              REAL_POW_ONE; ARITH_EVEN; COMPLEX_ADD_RID; COMPLEX_POW_ONE]);;

let COMPLEX_ROOT_UNITY_EQ = prove
 (`!n j k. ~(n = 0)
           ==> (cexp(Cx(&2) * Cx pi * ii * Cx(&j / &n)) =
                cexp(Cx(&2) * Cx pi * ii * Cx(&k / &n)) <=> (j == k) (mod n))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CEXP_EQ; num_congruent; CX_MUL] THEN
  REWRITE_TAC[COMPLEX_RING
   `t * p * ii * j = t * p * ii * k + (t * n * p) * ii <=>
        (t * p * ii = Cx(&0)) \/ j - k = n`] THEN
  SIMP_TAC[COMPLEX_ENTIRE; II_NZ; CX_INJ; PI_NZ; REAL_OF_NUM_EQ; ARITH] THEN
  REWRITE_TAC[GSYM CX_SUB; CX_INJ] THEN
  ASM_SIMP_TAC[REAL_OF_NUM_EQ; REAL_FIELD
   `~(n = &0) ==> (j / n - k / n = m <=> j - k = n * m)`] THEN
  REWRITE_TAC[int_congruent] THEN
  REWRITE_TAC[int_eq; int_sub_th; int_mul_th; int_of_num_th] THEN
  MESON_TAC[int_abstr; int_rep]);;

let COMPLEX_ROOT_UNITY_EQ_1 = prove
 (`!n j. ~(n = 0)
         ==> (cexp(Cx(&2) * Cx pi * ii * Cx(&j / &n)) = Cx(&1) <=>
              n divides j)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `Cx(&1) = cexp(Cx(&2) * Cx pi * ii * Cx(&n / &n))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_DIV_REFL; REAL_OF_NUM_EQ; COMPLEX_MUL_RID] THEN
    ONCE_REWRITE_TAC[COMPLEX_RING `t * p * ii = ii * t * p`] THEN
    REWRITE_TAC[CEXP_EULER; GSYM CX_MUL; GSYM CX_SIN; GSYM CX_COS] THEN
    REWRITE_TAC[COS_NPI; SIN_NPI] THEN SIMPLE_COMPLEX_ARITH_TAC;
    ASM_SIMP_TAC[COMPLEX_ROOT_UNITY_EQ] THEN CONV_TAC NUMBER_RULE]);;

let FINITE_CARD_COMPLEX_ROOTS_UNITY = prove
 (`!n. 1 <= n
       ==> FINITE {z | z pow n = Cx(&1)} /\ CARD {z | z pow n = Cx(&1)} <= n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[COMPLEX_ROOT_POLYFUN] THEN
  MATCH_MP_TAC COMPLEX_POLYFUN_ROOTBOUND THEN
  DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
  ASM_SIMP_TAC[IN_NUMSEG; LE_1; LE_0; LE_REFL] THEN CONV_TAC COMPLEX_RING);;

let FINITE_COMPLEX_ROOTS_UNITY = prove
 (`!n. ~(n = 0) ==> FINITE {z | z pow n = Cx(&1)}`,
  SIMP_TAC[FINITE_CARD_COMPLEX_ROOTS_UNITY; LE_1]);;

let FINITE_CARD_COMPLEX_ROOTS_UNITY_EXPLICIT = prove
 (`!n. 1 <= n
       ==> FINITE {cexp(Cx(&2) * Cx pi * ii * Cx(&j / &n)) | j | j < n} /\
           CARD {cexp(Cx(&2) * Cx pi * ii * Cx(&j / &n)) | j | j < n} = n`,
  let lemma = prove (* So we don't need to load number theories yet *)
   (`!x y n:num. (x == y) (mod n) /\ x < y + n /\ y < x + n ==> x = y`,
    REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_LT] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
    REWRITE_TAC[INT_ARITH `x < y + n /\ y < x + n <=> abs(x - y:int) < n`] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[int_congruent] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `d:int`) MP_TAC) THEN
    ONCE_REWRITE_TAC[GSYM INT_SUB_0] THEN
    ASM_SIMP_TAC[INT_ABS_MUL; INT_ENTIRE; INT_ABS_NUM;
                 INT_ARITH `n * x:int < n <=> n * x < n * &1`] THEN
    DISJ_CASES_TAC(INT_ARITH `&n:int = &0 \/ &0:int < &n`) THEN
    ASM_SIMP_TAC[INT_LT_LMUL_EQ] THEN INT_ARITH_TAC) in
  REWRITE_TAC[GSYM HAS_SIZE] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_SIMP_TAC[HAS_SIZE_NUMSEG_LT; COMPLEX_ROOT_UNITY_EQ; LE_1] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma THEN EXISTS_TAC `n:num` THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let COMPLEX_ROOTS_UNITY = prove
 (`!n. 1 <= n
       ==> {z | z pow n = Cx(&1)} =
           {cexp(Cx(&2) * Cx pi * ii * Cx(&j / &n)) | j | j < n}`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_LE THEN
  ASM_SIMP_TAC[FINITE_CARD_COMPLEX_ROOTS_UNITY;
               FINITE_CARD_COMPLEX_ROOTS_UNITY_EXPLICIT] THEN
  GEN_REWRITE_TAC LAND_CONV [SIMPLE_IMAGE_GEN] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[COMPLEX_ROOT_UNITY; LE_1]);;

let CARD_COMPLEX_ROOTS_UNITY = prove
 (`!n. 1 <= n ==> CARD {z | z pow n = Cx(&1)} = n`,
  SIMP_TAC[COMPLEX_ROOTS_UNITY; FINITE_CARD_COMPLEX_ROOTS_UNITY_EXPLICIT]);;

let HAS_SIZE_COMPLEX_ROOTS_UNITY = prove
 (`!n. 1 <= n ==> {z | z pow n = Cx(&1)} HAS_SIZE n`,
  SIMP_TAC[HAS_SIZE; CARD_COMPLEX_ROOTS_UNITY; FINITE_COMPLEX_ROOTS_UNITY;
           LE_1]);;

let COMPLEX_NOT_ROOT_UNITY = prove
 (`!n. 1 <= n ==> ?u. norm u = &1 /\ ~(u pow n = Cx(&1))`,
  GEN_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `u = cexp (Cx pi * ii * Cx (&1 / &n))` THEN
  EXISTS_TAC `u : complex` THEN CONJ_TAC THEN EXPAND_TAC "u" THEN
  REWRITE_TAC [NORM_CEXP; RE_MUL_CX; RE_II; REAL_MUL_LZERO;
               REAL_MUL_RZERO; REAL_EXP_0] THEN
  EXPAND_TAC "u" THEN REWRITE_TAC[GSYM CEXP_N] THEN
  ASM_SIMP_TAC[CX_DIV; LE_1; CX_INJ; REAL_OF_NUM_EQ; COMPLEX_FIELD
       `~(n = Cx(&0)) ==> n * p * i * Cx(&1) / n = i * p`] THEN
  REWRITE_TAC[CEXP_EULER; RE_CX; IM_CX; GSYM CX_COS; GSYM CX_SIN] THEN
  REWRITE_TAC[COS_PI; SIN_PI] THEN CONV_TAC COMPLEX_RING);;

(* ------------------------------------------------------------------------- *)
(* Relation between clog and Arg, and hence continuity of Arg.               *)
(* ------------------------------------------------------------------------- *)

let ARG_CLOG = prove
 (`!z. &0 < Arg z ==> Arg z = Im(clog(--z)) + pi`,
  GEN_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THENL
   [ASM_REWRITE_TAC[Arg_DEF; REAL_LT_REFL]; ALL_TAC] THEN
  DISCH_TAC THEN MP_TAC(last(CONJUNCTS(SPEC `z:complex` ARG))) THEN
  ASM_SIMP_TAC[CX_INJ; COMPLEX_NORM_ZERO; COMPLEX_FIELD
   `~(z = Cx(&0)) ==> (w = z * a <=> a = w / z)`] THEN
  DISCH_THEN(MP_TAC o AP_TERM `( * ) (cexp(--(ii * Cx pi)))`) THEN
  REWRITE_TAC[GSYM CEXP_ADD] THEN DISCH_THEN(MP_TAC o AP_TERM `clog`) THEN
  W(MP_TAC o PART_MATCH (lhs o rand) CLOG_CEXP o lhand o lhand o snd) THEN
  REWRITE_TAC[IM_ADD; IM_MUL_II; RE_CX; IM_NEG] THEN
  ASM_SIMP_TAC[REAL_LT_ADDR; ARG; REAL_ARITH
    `z < &2 * pi ==> --pi + z <= pi`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CEXP_NEG; CEXP_EULER] THEN
  REWRITE_TAC[GSYM CX_SIN; GSYM CX_COS; SIN_PI; COS_PI] THEN
  REWRITE_TAC[CX_NEG; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID;
              SIMPLE_COMPLEX_ARITH `inv(--Cx(&1)) * z / w = --z / w`] THEN
  DISCH_THEN(MP_TAC o AP_TERM `Im`) THEN
  REWRITE_TAC[IM_ADD; IM_NEG; IM_MUL_II; RE_CX] THEN
  MATCH_MP_TAC(REAL_RING `w = z ==> --pi + x = w ==> x = z + pi`) THEN
  REWRITE_TAC[complex_div] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) CLOG_MUL_SIMPLE o rand o lhand o snd) THEN
  ASM_SIMP_TAC[CX_INJ; REAL_INV_EQ_0; COMPLEX_NORM_ZERO; COMPLEX_NEG_EQ_0;
    GSYM CX_INV; GSYM CX_LOG; REAL_LT_INV_EQ; COMPLEX_NORM_NZ; IM_CX] THEN
  ASM_SIMP_TAC[REAL_ADD_RID; CLOG_WORKS; COMPLEX_NEG_EQ_0] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IM_ADD; IM_CX; REAL_ADD_RID]);;

let CONTINUOUS_AT_ARG = prove
 (`!z. ~(real z /\ &0 <= Re z) ==> (Cx o Arg) continuous (at z)`,
  let lemma = prove
   (`(\z. Cx(Im(f z) + pi)) = (Cx o Im) o (\z. f z + ii * Cx pi)`,
    REWRITE_TAC[FUN_EQ_THM; o_DEF; IM_ADD; IM_CX; IM_MUL_II; RE_CX]) in
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONTINUOUS_AT] THEN
  MATCH_MP_TAC LIM_TRANSFORM_WITHIN_OPEN THEN
  EXISTS_TAC `\z. Cx(Im(clog(--z)) + pi)` THEN
  EXISTS_TAC `(:complex) DIFF {z | real z /\ &0 <= Re z}` THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; IN_ELIM_THM; GSYM closed] THEN
  ASM_SIMP_TAC[o_THM; ARG_CLOG; ARG_LT_NZ; ARG_EQ_0] THEN CONJ_TAC THENL
   [REWRITE_TAC[SET_RULE `{z | P z /\ Q z} = P INTER {z | Q z}`] THEN
    MATCH_MP_TAC CLOSED_INTER THEN
    REWRITE_TAC[CLOSED_REAL; GSYM real_ge; CLOSED_HALFSPACE_RE_GE];
    REWRITE_TAC[GSYM CONTINUOUS_AT; lemma] THEN
    MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
    REWRITE_TAC[CONTINUOUS_AT_CX_IM] THEN
    MATCH_MP_TAC CONTINUOUS_ADD THEN REWRITE_TAC[CONTINUOUS_CONST] THEN
    MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_AT_COMPOSE) THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM ETA_AX] THEN
    SIMP_TAC[CONTINUOUS_NEG; CONTINUOUS_AT_ID] THEN
    MATCH_MP_TAC CONTINUOUS_AT_CLOG THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC[real; IM_NEG; RE_NEG] THEN REAL_ARITH_TAC]);;

let CONTINUOUS_WITHIN_UPPERHALF_ARG = prove
 (`!z. ~(z = Cx(&0))
       ==> (Cx o Arg) continuous (at z) within {z | &0 <= Im z}`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `real z /\ &0 <= Re z` THEN
  ASM_SIMP_TAC[CONTINUOUS_AT_ARG; CONTINUOUS_AT_WITHIN] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2
   (ASSUME_TAC o GEN_REWRITE_RULE I [real]) MP_TAC) THEN
  SUBGOAL_THEN `~(Re z = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(z = Cx(&0))` THEN
    ASM_REWRITE_TAC[COMPLEX_EQ; RE_CX; IM_CX];
    GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT]] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `rotate2d (pi / &2) z` CONTINUOUS_AT_ARG) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[ROTATE2D_PI2; real; IM_MUL_II]; ALL_TAC] THEN
  REWRITE_TAC[continuous_at; continuous_within] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  REWRITE_TAC[o_THM; dist; GSYM CX_SUB; COMPLEX_NORM_CX] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `w:complex` THEN STRIP_TAC THEN
  SUBGOAL_THEN `Arg z = &0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[ARG_EQ_0; real; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_CASES_TAC `Arg w = &0` THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM] THEN
  SUBGOAL_THEN `&0 < Arg w` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ARG; REAL_LT_LE]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `rotate2d (pi / &2) w`) THEN
  ASM_REWRITE_TAC[GSYM ROTATE2D_SUB; NORM_ROTATE2D] THEN
  MP_TAC(ISPECL [`pi / &2`; `z:complex`] ARG_ROTATE2D) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[REAL_ADD_RID] THEN
  MATCH_MP_TAC(REAL_ARITH
   `w' = p + w ==> abs(w' - p) < e ==> abs(w - &0) < e`) THEN
  MATCH_MP_TAC ARG_ROTATE2D THEN CONJ_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `&0 < Arg w` THEN
    ASM_REWRITE_TAC[Arg_DEF; REAL_LT_REFL];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM ARG_LE_PI]) THEN
    MP_TAC(SPEC `w:complex` ARG) THEN REAL_ARITH_TAC]);;

let CONTINUOUS_ON_UPPERHALF_ARG = prove
 (`(Cx o Arg) continuous_on ({z | &0 <= Im z} DIFF {Cx(&0)})`,
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `z:complex` THEN REWRITE_TAC[IN_DIFF; IN_SING; IN_ELIM_THM] THEN
  STRIP_TAC THEN FIRST_ASSUM(MP_TAC o
    MATCH_MP CONTINUOUS_WITHIN_UPPERHALF_ARG) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CONTINUOUS_WITHIN_SUBSET) THEN
  SET_TAC[]);;

let CONTINUOUS_ON_COMPOSE_ARG = prove
 (`!s p:real->real^N.
        (p o drop) continuous_on interval[vec 0,lift(&2 * pi)] /\
        p(&2 * pi) = p(&0) /\ ~(Cx(&0) IN s)
        ==> (\z. p(Arg z)) continuous_on s`,
  let ulemma = prove
   (`!s. s INTER {z | &0 <= Im z} UNION s INTER {z | Im z <= &0} = s`,
    SET_TAC[REAL_LE_TOTAL]) in
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC
   `\z. if &0 <= Im z then p(Arg z)
        else p(&2 * pi - Arg(cnj z)):real^N` THEN
  REWRITE_TAC[IN_UNIV; IN_SING; IN_DIFF] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[ARG_CNJ] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_SUB_SUB2] THEN
    SUBGOAL_THEN `Arg z = &0`
     (fun th -> ASM_REWRITE_TAC[REAL_SUB_RZERO; th]) THEN
    ASM_REWRITE_TAC[ARG_EQ_0];
    GEN_REWRITE_TAC RAND_CONV [GSYM ulemma] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN REWRITE_TAC[ulemma] THEN
    SIMP_TAC[CLOSED_IN_CLOSED_INTER; CLOSED_HALFSPACE_IM_LE;
             REWRITE_RULE[real_ge] CLOSED_HALFSPACE_IM_GE] THEN
    REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV; IN_SING; IN_ELIM_THM] THEN
    SIMP_TAC[GSYM CONJ_ASSOC; REAL_LE_ANTISYM; TAUT `~(p /\ ~p)`] THEN
    REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV) [GSYM o_DEF] THEN
      SUBGOAL_THEN `(p:real->real^N) = (p o drop) o lift` SUBST1_TAC THENL
       [REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX]; ALL_TAC] THEN
      ONCE_REWRITE_TAC[GSYM o_ASSOC] THEN
      CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [REWRITE_TAC[o_DEF; GSYM CONTINUOUS_ON_CX_LIFT] THEN
        MP_TAC CONTINUOUS_ON_UPPERHALF_ARG THEN REWRITE_TAC[o_DEF] THEN
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CONTINUOUS_ON_SUBSET) THEN
        ASM SET_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
        REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; o_THM; DROP_VEC] THEN
        SIMP_TAC[ARG; REAL_LT_IMP_LE];
        REWRITE_TAC[o_DEF; LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
        REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
        GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [GSYM o_DEF] THEN
        REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        REWRITE_TAC[CONTINUOUS_ON_CNJ; o_DEF; GSYM CONTINUOUS_ON_CX_LIFT] THEN
        MP_TAC CONTINUOUS_ON_UPPERHALF_ARG THEN REWRITE_TAC[o_DEF] THEN
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CONTINUOUS_ON_SUBSET) THEN
        SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM; IN_DIFF] THEN
        SIMP_TAC[IN_SING; CNJ_EQ_0; IM_CNJ; REAL_NEG_GE0] THEN ASM SET_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
        REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; o_THM; DROP_VEC] THEN
        X_GEN_TAC `z:complex` THEN STRIP_TAC THEN
        MP_TAC(SPEC `cnj z` ARG) THEN REAL_ARITH_TAC];
      REWRITE_TAC[GSYM ARG_EQ_0_PI; GSYM real; ARG_CNJ] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_SUB_SUB2; REAL_SUB_RZERO] THEN
      ASM_REWRITE_TAC[REAL_ARITH `&2 * x - x = x`]]]);;

let OPEN_ARG_LTT = prove
 (`!s t. &0 <= s /\ t <= &2 * pi ==> open {z | s < Arg z /\ Arg z < t}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Cx o Arg`; `(:complex) DIFF {z | real z /\ &0 <= Re z}`;
                   `{z | Re(z) > s} INTER {z | Re(z) < t}`]
           CONTINUOUS_OPEN_PREIMAGE) THEN
  ASM_SIMP_TAC[OPEN_INTER; OPEN_HALFSPACE_RE_GT; OPEN_HALFSPACE_RE_LT] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
      REWRITE_TAC[IN_DIFF; IN_UNIV; IN_ELIM_THM; CONTINUOUS_AT_ARG];
      REWRITE_TAC[GSYM closed] THEN
      REWRITE_TAC[SET_RULE `{z | P z /\ Q z} = P INTER {z | Q z}`] THEN
      MATCH_MP_TAC CLOSED_INTER THEN
      REWRITE_TAC[CLOSED_REAL; GSYM real_ge; CLOSED_HALFSPACE_RE_GE]];
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[EXTENSION] THEN
    ASM_SIMP_TAC[IN_DIFF; IN_INTER; IN_UNIV; IN_ELIM_THM; o_THM; RE_CX;
                 GSYM ARG_EQ_0] THEN
    ASM_REAL_ARITH_TAC]);;

let OPEN_ARG_GT = prove
 (`!t. open {z | t < Arg z}`,
  GEN_TAC THEN DISJ_CASES_TAC(REAL_ARITH `t < &0 \/ &0 <= t`) THENL
   [SUBGOAL_THEN `{z | t < Arg z} = (:complex)`
     (fun th -> SIMP_TAC[th; OPEN_UNIV]) THEN
    REWRITE_TAC[EXTENSION; IN_UNIV; IN_ELIM_THM] THEN
    MP_TAC ARG THEN MATCH_MP_TAC MONO_FORALL THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`t:real`; `&2 * pi`] OPEN_ARG_LTT) THEN
    ASM_REWRITE_TAC[ARG; REAL_LE_REFL]]);;

let CLOSED_ARG_LE = prove
 (`!t. closed {z | Arg z <= t}`,
  REWRITE_TAC[closed; DIFF; IN_UNIV; IN_ELIM_THM] THEN
  REWRITE_TAC[REAL_NOT_LE; OPEN_ARG_GT]);;

(* ------------------------------------------------------------------------- *)
(* Relation between Arg and arctangent in upper halfplane.                   *)
(* ------------------------------------------------------------------------- *)

let ARG_ATAN_UPPERHALF = prove
 (`!z. &0 < Im z ==> Arg(z) = pi / &2 - atn(Re z / Im z)`,
  GEN_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THEN
  ASM_REWRITE_TAC[IM_CX; REAL_LT_REFL] THEN DISCH_TAC THEN
  MATCH_MP_TAC ARG_UNIQUE THEN EXISTS_TAC `norm(z:complex)` THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_NZ] THEN CONJ_TAC THENL
   [ALL_TAC; MP_TAC(ISPEC `Re z / Im z` ATN_BOUNDS) THEN REAL_ARITH_TAC] THEN
  REWRITE_TAC[CEXP_EULER; GSYM CX_SIN; GSYM CX_COS] THEN
  REWRITE_TAC[SIN_SUB; COS_SUB; SIN_PI2; COS_PI2] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; SIN_ATN; COS_ATN] THEN
  SUBGOAL_THEN `sqrt(&1 + (Re z / Im z) pow 2) = norm(z) / Im z`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SQRT_UNIQUE THEN
    ASM_SIMP_TAC[REAL_LE_DIV; NORM_POS_LE; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[REAL_POW_DIV; COMPLEX_SQNORM] THEN
    UNDISCH_TAC `&0 < Im z` THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[REAL_ADD_LID; REAL_SUB_RZERO; real_div] THEN
    REWRITE_TAC[COMPLEX_EQ; RE_MUL_CX; IM_MUL_CX; RE_MUL_II; IM_MUL_II;
                RE_ADD; IM_ADD; RE_CX; IM_CX] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM COMPLEX_NORM_NZ]) THEN
    POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* Real n'th roots. Regardless of whether n is odd or even, we totalize by   *)
(* setting root_n(-x) = -root_n(x), which makes some convenient facts hold.  *)
(* ------------------------------------------------------------------------- *)

let root = new_definition
 `root(n) x = real_sgn(x) * exp(log(abs x) / &n)`;;

let ROOT_0 = prove
 (`!n. root n (&0) = &0`,
  REWRITE_TAC[root; REAL_SGN_0; REAL_MUL_LZERO]);;

let ROOT_1 = prove
 (`!n. root n (&1) = &1`,
  REWRITE_TAC[root; REAL_ABS_NUM; LOG_1; real_div; REAL_MUL_LZERO] THEN
  REWRITE_TAC[real_sgn; REAL_EXP_0] THEN REAL_ARITH_TAC);;

let ROOT_2 = prove
 (`!x. root 2 x = sqrt x`,
  GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_UNIQUE_GEN THEN
  REWRITE_TAC[root; REAL_SGN_MUL; REAL_POW_MUL; REAL_SGN_REAL_SGN] THEN
  REWRITE_TAC[REAL_SGN_POW_2; GSYM REAL_SGN_POW] THEN
  SIMP_TAC[real_sgn; REAL_EXP_POS_LT; REAL_MUL_RID] THEN
  REWRITE_TAC[REAL_ARITH `(&0 < abs x <=> ~(x = &0)) /\ ~(abs x < &0)`] THEN
  ASM_CASES_TAC `x = &0` THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ABS_NUM; REAL_MUL_LID] THEN
  REWRITE_TAC[GSYM REAL_EXP_N; REAL_ARITH `&2 * x / &2 = x`] THEN
  ASM_SIMP_TAC[EXP_LOG; REAL_ARITH `&0 < abs x <=> ~(x = &0)`]);;

let ROOT_NEG = prove
 (`!n x. root n (--x) = --(root n x)`,
  REWRITE_TAC[root; REAL_SGN_NEG; REAL_ABS_NEG; REAL_MUL_LNEG]);;

let ROOT_WORKS = prove
 (`!n x. real_sgn(root n x) = real_sgn x /\
         (root n x) pow n = if n = 0 then &1
                            else real_sgn(x) pow n * abs x`,
  REWRITE_TAC[root; REAL_SGN_MUL; REAL_POW_MUL; GSYM REAL_EXP_N] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_INV_0;
                  REAL_EXP_0; REAL_MUL_RID; real_pow; REAL_SGN_REAL_SGN] THEN
  REWRITE_TAC[real_sgn; REAL_LT_01; REAL_MUL_RID] THEN
  ASM_SIMP_TAC[REAL_EXP_POS_LT; REAL_MUL_RID; GSYM REAL_ABS_NZ;
               GSYM real_div; REAL_DIV_LMUL; REAL_OF_NUM_EQ] THEN
  ASM_CASES_TAC `x = &0` THEN
  ASM_REWRITE_TAC[REAL_LT_REFL; REAL_POW_ZERO; REAL_MUL_LZERO] THEN
  ASM_SIMP_TAC[EXP_LOG; GSYM REAL_ABS_NZ]);;

let REAL_POW_ROOT = prove
 (`!n x. ODD n \/ ~(n = 0) /\ &0 <= x ==> (root n x) pow n = x`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[ARITH] THEN STRIP_TAC THEN ASM_REWRITE_TAC[ROOT_WORKS] THENL
   [FIRST_ASSUM(CHOOSE_THEN SUBST1_TAC o GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] real_pow] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC; REAL_SGN_ABS] THEN
    REWRITE_TAC[GSYM REAL_POW_POW] THEN
    REWRITE_TAC[REWRITE_RULE[REAL_SGN_POW] REAL_SGN_POW_2] THEN
    REWRITE_TAC[real_sgn; GSYM REAL_ABS_NZ] THEN
    ASM_CASES_TAC `x = &0` THEN
    ASM_REWRITE_TAC[REAL_LT_REFL; REAL_POW_ONE] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[real_sgn; REAL_LT_LE] THEN
    ASM_CASES_TAC `x = &0` THEN
    ASM_REWRITE_TAC[REAL_POW_ZERO; REAL_POW_ONE] THEN
    ASM_REAL_ARITH_TAC]);;

let ROOT_POS_LT = prove
 (`!n x. &0 < x ==> &0 < root n x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[root] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN
  ASM_REWRITE_TAC[REAL_EXP_POS_LT; REAL_SGN_INEQS]);;

let ROOT_POS_LE = prove
 (`!n x. &0 <= x ==> &0 <= root n x`,
  MESON_TAC[REAL_LE_LT; ROOT_POS_LT; ROOT_0; REAL_LT_REFL]);;

let ROOT_LT_0 = prove
 (`!n x. &0 < root n x <=> &0 < x`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[ROOT_POS_LT] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[REAL_ARITH `x <= &0 <=> &0 <= --x`; GSYM ROOT_NEG] THEN
  REWRITE_TAC[ROOT_POS_LE]);;

let ROOT_LE_0 = prove
 (`!n x. &0 <= root n x <=> &0 <= x`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[ROOT_POS_LE] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[REAL_ARITH `x < &0 <=> &0 < --x`; GSYM ROOT_NEG] THEN
  REWRITE_TAC[ROOT_POS_LT]);;

let ROOT_EQ_0 = prove
 (`!n x. root n x = &0 <=> x = &0`,
  REWRITE_TAC[root; REAL_ENTIRE; REAL_EXP_NZ; REAL_SGN_INEQS]);;

let REAL_ROOT_MUL = prove
 (`!n x y. root n (x * y) = root n x * root n y`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `x = &0` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO; ROOT_0] THEN
  ASM_CASES_TAC `y = &0` THEN ASM_REWRITE_TAC[REAL_MUL_RZERO; ROOT_0] THEN
  REWRITE_TAC[root; REAL_SGN_MUL; REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[LOG_MUL; GSYM REAL_ABS_NZ; real_div] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB; REAL_EXP_ADD] THEN
  REAL_ARITH_TAC);;

let REAL_ROOT_POW_GEN = prove
 (`!m n x y. root n (x pow m) = (root n x) pow m`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[REAL_ROOT_MUL; ROOT_1; real_pow]);;

let REAL_ROOT_POW = prove
 (`!n x. ODD n \/ ~(n = 0) /\ &0 <= x ==> root n (x pow n) = x`,
  SIMP_TAC[REAL_ROOT_POW_GEN; REAL_POW_ROOT]);;

let ROOT_UNIQUE = prove
 (`!n x y. y pow n = x /\ (ODD n \/ ~(n = 0) /\ &0 <= y) ==> root n x = y`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  UNDISCH_THEN `(y:real) pow n = x` (SUBST_ALL_TAC o SYM) THEN
  MATCH_MP_TAC REAL_ROOT_POW THEN ASM_REWRITE_TAC[]);;

let REAL_ROOT_INV = prove
 (`!n x. root n (inv x) = inv(root n x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[root; REAL_SGN_INV; REAL_INV_SGN] THEN
  ASM_CASES_TAC `x = &0` THEN
  ASM_REWRITE_TAC[REAL_SGN_0; REAL_MUL_LZERO; REAL_INV_0] THEN
  REWRITE_TAC[REAL_INV_MUL; REAL_INV_SGN; REAL_ABS_INV] THEN
  ASM_SIMP_TAC[GSYM REAL_EXP_NEG; LOG_INV; GSYM REAL_ABS_NZ] THEN
  REWRITE_TAC[real_div; REAL_MUL_LNEG]);;

let REAL_ROOT_DIV = prove
 (`!n x y. root n (x / y) = root n x / root n y`,
  SIMP_TAC[real_div; REAL_ROOT_MUL; REAL_ROOT_INV]);;

let ROOT_MONO_LT = prove
 (`!n x y. ~(n = 0) /\ x < y ==> root n x < root n y`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!x y. &0 <= x /\ x < y ==> root n x < root n y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LT2_REV THEN
    EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[ROOT_WORKS; ROOT_LE_0] THEN
    ASM_REWRITE_TAC[real_sgn] THEN REPEAT
     (COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_POW_ONE; REAL_POW_ZERO]) THEN
    ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `&0 <= x` THEN ASM_SIMP_TAC[] THEN
    ASM_CASES_TAC `&0 <= y` THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&0` THEN
      ASM_REWRITE_TAC[GSYM REAL_NOT_LE; ROOT_LE_0];
      FIRST_X_ASSUM(MP_TAC o SPECL [`--y:real`; `--x:real`]) THEN
      REWRITE_TAC[ROOT_NEG] THEN ASM_REAL_ARITH_TAC]]);;

let ROOT_MONO_LE = prove
 (`!n x y. x <= y ==> root n x <= root n y`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[root; real_div; REAL_INV_0; REAL_MUL_RZERO;
                    REAL_EXP_0; REAL_MUL_RID] THEN
    REWRITE_TAC[real_sgn] THEN ASM_REAL_ARITH_TAC;
    ASM_MESON_TAC[REAL_LE_LT; ROOT_0; ROOT_MONO_LT]]);;

let ROOT_MONO_LT_EQ = prove
 (`!n x y. ~(n = 0) ==> (root n x < root n y <=> x < y)`,
  MESON_TAC[ROOT_MONO_LT; REAL_NOT_LT; ROOT_MONO_LE]);;

let ROOT_MONO_LE_EQ = prove
 (`!n x y. ~(n = 0) ==> (root n x <= root n y <=> x <= y)`,
  MESON_TAC[ROOT_MONO_LT; REAL_NOT_LT; ROOT_MONO_LE]);;

let ROOT_INJ = prove
 (`!n x y. ~(n = 0) ==> (root n x = root n y <=> x = y)`,
  SIMP_TAC[GSYM REAL_LE_ANTISYM; ROOT_MONO_LE_EQ]);;

let REAL_ROOT_LE = prove
 (`!n x y. ~(n = 0) /\ &0 <= y
           ==> (root n x <= y <=> x <= y pow n)`,
  MESON_TAC[REAL_ROOT_POW; REAL_POW_LE; ROOT_MONO_LE_EQ]);;

let REAL_LE_ROOT = prove
 (`!n x y. ~(n = 0) /\ &0 <= x
           ==> (x <= root n y <=> x pow n <= y)`,
  MESON_TAC[REAL_ROOT_POW; REAL_POW_LE; ROOT_MONO_LE_EQ]);;

let LOG_ROOT = prove
 (`!n x. ~(n = 0) /\ &0 < x ==> log(root n x) = log x / &n`,
  SIMP_TAC[REAL_EQ_RDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM LOG_POW; ROOT_POS_LT; REAL_POW_ROOT; REAL_LT_IMP_LE]);;

let ROOT_EXP_LOG = prove
 (`!n x. ~(n = 0) /\ &0 < x ==> root n x = exp(log x / &n)`,
  SIMP_TAC[root; real_sgn; real_abs; REAL_LT_IMP_LE; REAL_MUL_LID]);;

let ROOT_PRODUCT = prove
 (`!n f s. FINITE s ==> root n (product s f) = product s (\i. root n (f i))`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; REAL_ROOT_MUL; ROOT_1]);;

let SQRT_PRODUCT = prove
 (`!f s. FINITE s ==> sqrt(product s f) = product s (\i. sqrt(f i))`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; SQRT_MUL; SQRT_1]);;

(* ------------------------------------------------------------------------- *)
(* Real power function. This involves a few arbitrary choices.               *)
(*                                                                           *)
(* The value of x^y is unarguable when x > 0.                                *)
(*                                                                           *)
(* We make 0^0 = 1 to agree with "pow", but otherwise 0^y = 0.               *)
(*                                                                           *)
(* There is a sensible real value for (-x)^(p/q) where q is odd and either   *)
(* p is even [(-x)^y = x^y] or odd [(-x)^y = -x^y].                          *)
(*                                                                           *)
(* In all other cases, we return (-x)^y = -x^y. This is meaningless but at   *)
(* least it covers half the cases above without another case split.          *)
(*                                                                           *)
(* As for laws of indices, we do have x^-y = 1/x^y. Of course we can't  have *)
(* x^(yz) = x^y^z or x^(y+z) = x^y x^z since then (-1)^(1/2)^2 = -1.         *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("rpow",(24,"left"));;

let rpow = new_definition
  `x rpow y = if &0 < x then exp(y * log x)
               else if x = &0 then if y = &0 then &1 else &0
               else if ?m n. ODD(m) /\ ODD(n) /\ (abs y = &m / &n)
                    then --(exp(y * log(--x)))
                    else exp(y * log(--x))`;;

let RPOW_POW = prove
 (`!x n. x rpow &n = x pow n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rpow] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_EXP_N; EXP_LOG] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_POW_ZERO; REAL_OF_NUM_EQ] THEN
  ASM_SIMP_TAC[EXP_LOG; REAL_ARITH `~(&0 < x) /\ ~(x = &0) ==> &0 < --x`] THEN
  REWRITE_TAC[REAL_POW_NEG; REAL_ABS_NUM] THEN
  SUBGOAL_THEN `(?p q. ODD(p) /\ ODD(q) /\ &n = &p / &q) <=> ODD n`
   (fun th -> SIMP_TAC[th; GSYM NOT_ODD; REAL_NEG_NEG; COND_ID]) THEN
  EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THENL
   [REPEAT GEN_TAC THEN ASM_CASES_TAC `q = 0` THEN
    ASM_REWRITE_TAC[ARITH_ODD] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_SIMP_TAC[REAL_OF_NUM_EQ; REAL_FIELD
     `~(q = &0) ==> (n = p / q <=> q * n = p)`] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_EQ] THEN
    ASM_MESON_TAC[ODD_MULT];
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`n:num`; `1`] THEN
    ASM_REWRITE_TAC[REAL_DIV_1; ARITH_ODD]]);;

let RPOW_0 = prove
 (`!x. x rpow &0 = &1`,
  REWRITE_TAC[RPOW_POW; real_pow]);;

let RPOW_NEG = prove
 (`!x y. x rpow (--y) = inv(x rpow y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rpow] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LNEG; REAL_EXP_NEG] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_NEG_EQ_0] THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_INV_0; REAL_INV_1];
    REWRITE_TAC[REAL_ABS_NEG] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_INV_NEG]]);;

let RPOW_ZERO = prove
 (`!y. &0 rpow y = if y = &0 then &1 else &0`,
  REWRITE_TAC[rpow; REAL_LT_REFL]);;

let RPOW_POS_LT = prove
 (`!x y. &0 < x ==> &0 < x rpow y`,
  SIMP_TAC[rpow; REAL_EXP_POS_LT]);;

let RPOW_POS_LE = prove
 (`!x y. &0 <= x ==> &0 <= x rpow y`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x = &0` THENL
   [ASM_REWRITE_TAC[RPOW_ZERO] THEN MESON_TAC[REAL_POS];
    ASM_SIMP_TAC[RPOW_POS_LT; REAL_LE_LT]]);;

let RPOW_LT2 = prove
 (`!x y z. &0 <= x /\ x < y /\ &0 < z ==> x rpow z < y rpow z`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x = &0` THEN
  ASM_SIMP_TAC[RPOW_ZERO; REAL_LT_IMP_NZ; RPOW_POS_LT] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[rpow] THEN
  ASM_CASES_TAC `&0 < x /\ &0 < y` THENL
   [ALL_TAC; MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_REAL_ARITH_TAC] THEN
  ASM_SIMP_TAC[REAL_EXP_MONO_LT; REAL_LT_LMUL_EQ] THEN
  MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REAL_ARITH_TAC);;

let RPOW_LE2 = prove
 (`!x y z. &0 <= x /\ x <= y /\ &0 <= z ==> x rpow z <= y rpow z`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `z = &0` THEN
  ASM_REWRITE_TAC[RPOW_POW; real_pow; REAL_LE_REFL] THEN
  ASM_CASES_TAC `x:real = y` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  ASM_MESON_TAC[RPOW_LT2; REAL_LE_LT]);;

let REAL_ABS_RPOW = prove
 (`!x y. abs(x rpow y) = abs(x) rpow y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rpow] THEN
  ASM_CASES_TAC `x = &0` THEN ASM_REWRITE_TAC[REAL_ABS_NUM; REAL_LT_REFL] THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM REAL_ABS_NZ; REAL_ABS_ZERO] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[REAL_ABS_EXP; REAL_ARITH `&0 < x ==> abs x = x`] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_EXP] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC);;

let RPOW_ONE = prove
 (`!z. &1 rpow z = &1`,
  REWRITE_TAC[rpow; REAL_LT_01; LOG_1; REAL_MUL_RZERO; REAL_EXP_0]);;

let RPOW_RPOW = prove
 (`!x y z. &0 <= x ==> x rpow y rpow z = x rpow (y * z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  ASM_CASES_TAC `x = &0` THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[RPOW_ZERO; REAL_ENTIRE] THEN
    ASM_CASES_TAC `y = &0` THEN ASM_REWRITE_TAC[RPOW_ZERO; RPOW_ONE];
    SIMP_TAC[rpow; REAL_EXP_POS_LT; LOG_EXP] THEN
    REWRITE_TAC[REAL_MUL_AC]]);;

let RPOW_LNEG = prove
 (`!x y. --x rpow y =
         if ?m n. ODD m /\ ODD n /\ abs y = &m / &n
         then --(x rpow y) else x rpow y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rpow] THEN
  ASM_CASES_TAC `x = &0` THEN
  ASM_REWRITE_TAC[REAL_NEG_0; REAL_ABS_NUM; REAL_LT_REFL] THENL
   [ASM_CASES_TAC `y = &0` THEN ASM_REWRITE_TAC[REAL_NEG_0; COND_ID] THEN
    REWRITE_TAC[REAL_ARITH `abs(&0) = m / n <=> m * inv n = &0`] THEN
    SIMP_TAC[REAL_ENTIRE; REAL_INV_EQ_0; REAL_OF_NUM_EQ] THEN MESON_TAC[ODD];
    ASM_SIMP_TAC[REAL_ARITH `~(x = &0) ==> (&0 < --x <=> ~(&0 < x))`] THEN
    ASM_REWRITE_TAC[REAL_NEG_EQ_0] THEN
    ASM_CASES_TAC `&0 < x` THEN ASM_REWRITE_TAC[REAL_NEG_NEG; COND_ID]]);;

let RPOW_EQ_0 = prove
 (`!x y. x rpow y = &0 <=> x = &0 /\ ~(y = &0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rpow] THEN
  ASM_CASES_TAC `x = &0` THEN ASM_REWRITE_TAC[REAL_LT_REFL] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_NEG_EQ_0; REAL_EXP_NZ]) THEN
  REAL_ARITH_TAC);;

let RPOW_MUL = prove
 (`!x y z. (x * y) rpow z = x rpow z * y rpow z`,
  SUBGOAL_THEN
    `!x y z. &0 <= x /\ &0 <= y ==> (x * y) rpow z = x rpow z * y rpow z`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
    ASM_CASES_TAC `z = &0` THEN
    ASM_REWRITE_TAC[RPOW_POW; real_pow; REAL_MUL_LID] THEN
    ASM_CASES_TAC `x = &0` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO; RPOW_ZERO] THEN
    ASM_CASES_TAC `y = &0` THEN ASM_REWRITE_TAC[REAL_MUL_RZERO; RPOW_ZERO] THEN
    SIMP_TAC[rpow; REAL_LT_MUL; LOG_MUL; REAL_ADD_LDISTRIB; REAL_EXP_ADD];
    REPEAT GEN_TAC THEN
    REPEAT_TCL DISJ_CASES_THEN (ANTE_RES_THEN (MP_TAC o SPEC `z:real`))
     (REAL_ARITH `&0 <= x /\ &0 <= y \/ &0 <= x /\ &0 <= --y \/
                  &0 <= --x /\ &0 <= y \/ &0 <= --x /\ &0 <= --y`) THEN
    REWRITE_TAC[RPOW_LNEG; REAL_MUL_RNEG; REAL_MUL_LNEG] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_MUL_RNEG; REAL_MUL_LNEG; REAL_EQ_NEG2]]);;

let RPOW_INV = prove
 (`!x y. inv(x) rpow y = inv(x rpow y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rpow; REAL_LT_INV_EQ] THEN
  SIMP_TAC[LOG_INV; REAL_MUL_RNEG; REAL_EXP_NEG] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_INV_EQ_0] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_INV_1; REAL_INV_0]) THEN
  ASM_SIMP_TAC[GSYM REAL_INV_NEG; LOG_INV;
               REAL_ARITH `~(&0 < x) /\ ~(x = &0) ==> &0 < --x`] THEN
  REWRITE_TAC[REAL_MUL_RNEG; REAL_EXP_NEG; REAL_INV_NEG]);;

let REAL_INV_RPOW = prove
 (`!x y. inv(x rpow y) = inv(x) rpow y`,
  REWRITE_TAC[RPOW_INV]);;

let RPOW_DIV = prove
 (`!x y z. (x / y) rpow z = x rpow z / y rpow z`,
  REWRITE_TAC[real_div; RPOW_MUL; RPOW_INV]);;

let RPOW_PRODUCT = prove
 (`!s:A->bool x y.
      FINITE s ==> (product s x) rpow y = product s (\i. x i rpow y)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES; RPOW_MUL; RPOW_ONE]);;

let RPOW_ADD = prove
 (`!x y z. &0 < x ==> x rpow (y + z) = x rpow y * x rpow z`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[rpow; REAL_ADD_RDISTRIB; REAL_EXP_ADD]);;

let RPOW_ADD_ALT = prove
 (`!x y z. &0 <= x /\ (x = &0 /\ y + z = &0 ==> y = &0 \/ z = &0)
           ==> x rpow (y + z) = x rpow y * x rpow z`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `x = &0` THEN ASM_SIMP_TAC[REAL_LE_LT; RPOW_ADD] THEN
  REWRITE_TAC[RPOW_ZERO] THEN
  ASM_CASES_TAC `y = &0` THEN
  ASM_REWRITE_TAC[REAL_MUL_LID; REAL_ADD_LID] THEN
  ASM_CASES_TAC `y + z = &0` THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let RPOW_SQRT = prove
 (`!x. &0 <= x ==> x rpow (&1 / &2) = sqrt x`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_RING
   `x pow 2 = y pow 2 /\ (x + y = &0 ==> x = &0 /\ y = &0)
    ==> x = y`) THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2] THEN
    ASM_SIMP_TAC[GSYM RPOW_POW; RPOW_RPOW] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[RPOW_POW; REAL_POW_1];
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= x /\ &0 <= y ==> x + y = &0 ==> x = &0 /\ y = &0`) THEN
    ASM_SIMP_TAC[SQRT_POS_LE; RPOW_POS_LE]]);;

let RPOW_MONO_LE = prove
 (`!a b x. &1 <= x /\ a <= b ==> x rpow a <= x rpow b`,
  SIMP_TAC[rpow; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
  SIMP_TAC[REAL_EXP_MONO_LE; LOG_POS; REAL_LE_RMUL]);;

let RPOW_MONO_LT = prove
 (`!a b x. &1 < x /\ a < b ==> x rpow a < x rpow b`,
  SIMP_TAC[rpow; REAL_ARITH `&1 < x ==> &0 < x`] THEN
  SIMP_TAC[REAL_EXP_MONO_LT; LOG_POS_LT; REAL_LT_RMUL]);;

let RPOW_MONO_LE_EQ = prove
 (`!a b x. &1 < x ==> (x rpow a <= x rpow b <=> a <= b)`,
  MESON_TAC[RPOW_MONO_LT; RPOW_MONO_LE; REAL_NOT_LT; REAL_LT_IMP_LE]);;

let RPOW_MONO_LT_EQ = prove
 (`!a b x. &1 < x ==> (x rpow a < x rpow b <=> a < b)`,
  SIMP_TAC[GSYM REAL_NOT_LE; RPOW_MONO_LE_EQ]);;

let RPOW_INJ = prove
 (`!x y z. &0 < x ==> (x rpow y = x rpow z <=> x = &1 \/ y = z)`,
  REPEAT STRIP_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (REAL_ARITH `x = &1 \/ &1 < x \/ x < &1`) THEN
  ASM_SIMP_TAC[RPOW_ONE; REAL_LT_IMP_NE] THENL
   [ALL_TAC; GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EQ_INV2]] THEN
  ASM_SIMP_TAC[REAL_INV_RPOW; GSYM REAL_LE_ANTISYM; RPOW_MONO_LE_EQ;
               REAL_INV_1_LT]);;

let RPOW_LE_1 = prove
 (`!x y. &1 <= x /\ &0 <= y ==> &1 <= x rpow y`,
  MESON_TAC[RPOW_0; RPOW_MONO_LE]);;

let RPOW_LT_1 = prove
 (`!x y. &1 < x /\ &0 < y ==> &1 < x rpow y`,
  MESON_TAC[RPOW_0; RPOW_MONO_LT]);;

let RPOW_MONO_INV = prove
 (`!a b x. &0 < x /\ x <= &1 /\ b <= a ==> x rpow a <= x rpow b`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC BINOP_CONV [GSYM REAL_INV_INV] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  ASM_SIMP_TAC[REAL_LT_INV_EQ; RPOW_POS_LT; GSYM RPOW_INV] THEN
  MATCH_MP_TAC RPOW_MONO_LE THEN
  ASM_SIMP_TAC[REAL_INV_1_LE]);;

let RPOW_1_LE = prove
 (`!a x. &0 <= x /\ x <= &1 /\ &0 <= a ==> x rpow a <= &1`,
  REPEAT STRIP_TAC THEN  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&1 rpow a` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RPOW_LE2 THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[RPOW_ONE; REAL_LE_REFL]]);;

let REAL_ROOT_RPOW = prove
 (`!n x. ~(n = 0) /\ (&0 <= x \/ ODD n) ==> root n x = x rpow (inv(&n))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x = &0` THEN
  ASM_SIMP_TAC[ROOT_0; RPOW_ZERO; REAL_INV_EQ_0; REAL_OF_NUM_EQ] THEN
  ASM_CASES_TAC `&0 <= x` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [ASM_SIMP_TAC[ROOT_EXP_LOG; rpow; REAL_LT_LE] THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC;
    ASM_REWRITE_TAC[rpow] THEN COND_CASES_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NUM] THEN
    REWRITE_TAC[REAL_ARITH `inv x = &1 / x`] THEN
    COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[ARITH]] THEN
    MATCH_MP_TAC ROOT_UNIQUE THEN
    ASM_REWRITE_TAC[REAL_POW_NEG; GSYM REAL_EXP_N; GSYM NOT_ODD] THEN
    ASM_SIMP_TAC[REAL_OF_NUM_EQ; REAL_FIELD
      `~(n = &0) ==> n * &1 / n * x = x`] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `--x:real = y <=> x = --y`] THEN
    MATCH_MP_TAC EXP_LOG THEN ASM_REAL_ARITH_TAC]);;

let LOG_RPOW = prove
 (`!x y. &0 < x ==> log(x rpow y) = y * log x`,
  SIMP_TAC[rpow; LOG_EXP]);;

let LOG_SQRT = prove
 (`!x. &0 < x ==> log(sqrt x) = log x / &2`,
  SIMP_TAC[GSYM RPOW_SQRT; LOG_RPOW; REAL_LT_IMP_LE] THEN
  REAL_ARITH_TAC);;

let RPOW_ADD_INTEGER = prove
 (`!x m n. integer m /\ integer n /\ ~(x = &0 /\ m + n = &0 /\ ~(n = &0))
            ==> x rpow (m + n) = x rpow m * x rpow n`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x = &0` THENL
   [ASM_REWRITE_TAC[RPOW_ZERO] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IMP_CONJ] THEN
  REWRITE_TAC[is_int; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `p:num` THEN DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  X_GEN_TAC `q:num` THEN DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[GSYM REAL_NEG_ADD; RPOW_NEG; RPOW_POW; REAL_OF_NUM_ADD;
              REAL_POW_ADD; REAL_INV_MUL] THEN
  REWRITE_TAC[REAL_ARITH `--x + y:real = y - x`; GSYM real_sub] THEN
  REWRITE_TAC[REAL_OF_NUM_SUB_CASES] THEN COND_CASES_TAC THEN
  REWRITE_TAC[RPOW_NEG; RPOW_POW] THEN
  ASM_SIMP_TAC[REAL_POW_SUB; ARITH_RULE `~(p:num <= q) ==> q <= p`] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; REAL_INV_INV] THEN
  REAL_ARITH_TAC);;

let NORM_CPOW = prove
 (`!w z. real w /\ &0 < Re w ==> norm(w cpow z) = norm(w) rpow (Re z)`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[NORM_CPOW_REAL; rpow; COMPLEX_NORM_NZ] THEN
  ASM_CASES_TAC `w = Cx(&0)` THEN ASM_REWRITE_TAC[RE_CX; REAL_LT_REFL] THEN
  SIMP_TAC[REAL_NORM; real_abs; REAL_LT_IMP_LE]);;

(* ------------------------------------------------------------------------- *)
(* Summability of zeta function series.                                      *)
(* ------------------------------------------------------------------------- *)

let SUMMABLE_ZETA = prove
 (`!n z. &1 < Re z ==> summable (from n) (\k. inv(Cx(&k) cpow z))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUMMABLE_FROM_ELSEWHERE THEN
  EXISTS_TAC `1` THEN MATCH_MP_TAC SERIES_ABSCONV_IMP_CONV THEN
  MATCH_MP_TAC SUMMABLE_EQ THEN EXISTS_TAC `\k. Cx(inv(&k rpow (Re z)))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[IN_FROM; NORM_CPOW_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT; LE_1;
             COMPLEX_NORM_INV; rpow];
    POP_ASSUM MP_TAC THEN SPEC_TAC(`Re z`,`x:real`)] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[summable] THEN
  MATCH_MP_TAC(MESON[] `(?x. P(Cx x)) ==> ?x. P x`) THEN
  REWRITE_TAC[SERIES_CX_LIFT] THEN
  REWRITE_TAC[sums; FROM_INTER_NUMSEG; LIM_SEQUENTIALLY; DIST_REAL] THEN
  REWRITE_TAC[GSYM drop; LIFT_DROP; VSUM_REAL; o_DEF] THEN
  MATCH_MP_TAC CONVERGENT_BOUNDED_MONOTONE THEN
  EXISTS_TAC `&2 rpow x / (&1 - (&1 / &2) rpow (x - &1))` THEN CONJ_TAC THENL
   [ALL_TAC;
    DISJ1_TAC THEN MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN DISCH_TAC THEN
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    SIMP_TAC[REAL_LE_INV_EQ; RPOW_POS_LE; REAL_POS] THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET_NUMSEG] THEN ASM_ARITH_TAC] THEN
  X_GEN_TAC `n:num` THEN
  TRANS_TAC REAL_LE_TRANS `sum(1..2 EXP n) (\k. inv(&k rpow x))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[SUM_POS_LE_NUMSEG; REAL_LE_INV_EQ; RPOW_POS_LE; REAL_POS;
             real_abs] THEN
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    SIMP_TAC[REAL_LE_INV_EQ; RPOW_POS_LE; REAL_POS] THEN
    SIMP_TAC[FINITE_NUMSEG; SUBSET_NUMSEG; LE_REFL;
             LT_POW2_REFL; LT_IMP_LE];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `sum(0..n) (\k. &2 rpow x / &2 rpow (&k * (x - &1)))` THEN
  CONJ_TAC THENL
   [SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THENL
     [REWRITE_TAC[EXP; SUM_SING_NUMSEG; REAL_MUL_LZERO; RPOW_0; REAL_INV_RPOW;
                  REAL_DIV_1] THEN
      MATCH_MP_TAC RPOW_LE2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\k. inv(&k rpow x)`; `1`; `2 EXP n`; `2 EXP n`]
        SUM_ADD_SPLIT) THEN
    ANTS_TAC THENL [ARITH_TAC; REWRITE_TAC[MULT_2; EXP]] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[] THEN
    TRANS_TAC REAL_LE_TRANS
     `sum (2 EXP n + 1..2 EXP n + 2 EXP n) (\k. inv(&2 pow n rpow x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; ARITH; RPOW_POS_LT] THEN
      MATCH_MP_TAC RPOW_LE2 THEN
      ASM_SIMP_TAC[RPOW_POW; REAL_OF_NUM_POW; REAL_OF_NUM_LE; LE_0] THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[SUM_CONST_NUMSEG; ARITH_RULE `((n + n) + 1) - (n + 1) = n`;
                  GSYM REAL_OF_NUM_POW; REAL_INV_POW; REAL_POW_2] THEN
      REWRITE_TAC[real_div; GSYM RPOW_NEG] THEN
      SIMP_TAC[GSYM RPOW_POW; RPOW_RPOW; REAL_POS; GSYM RPOW_ADD;
               REAL_OF_NUM_LT; ARITH] THEN
      MATCH_MP_TAC RPOW_MONO_LE THEN REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
      ASM_REAL_ARITH_TAC];
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    SIMP_TAC[GSYM RPOW_RPOW; REAL_POS; real_div; RPOW_POW] THEN
    REWRITE_TAC[REAL_INV_POW; SUM_LMUL] THEN REWRITE_TAC[SUM_GP] THEN
    REWRITE_TAC[CONJUNCT1 LT; CONJUNCT1 real_pow] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[RPOW_POS_LE; REAL_POS] THEN
    COND_CASES_TAC THENL
     [MATCH_MP_TAC(TAUT `F ==> p`) THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH `x = &1 ==> &1 <= x`)) THEN
      REWRITE_TAC[REAL_NOT_LE] THEN MATCH_MP_TAC REAL_INV_LT_1 THEN
      MATCH_MP_TAC RPOW_LT_1 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_MUL_LID; RPOW_INV] THEN
      REWRITE_TAC[REAL_ARITH `a / b <= inv b <=> a * inv b <= &1 * inv b`] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[REAL_ARITH `&1 - x <= &1 <=> &0 <= x`; REAL_LE_INV_EQ] THEN
      SIMP_TAC[REAL_POW_LE; REAL_LE_DIV; REAL_POS; REAL_SUB_LE;
               RPOW_POS_LE; REAL_LE_INV_EQ] THEN
      MATCH_MP_TAC REAL_INV_LE_1 THEN
      MATCH_MP_TAC RPOW_LE_1 THEN ASM_REAL_ARITH_TAC]]);;

let SUMMABLE_ZETA_INTEGER = prove
 (`!n m. 2 <= m ==> summable (from n) (\k. inv(Cx(&k) pow m))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUMMABLE_FROM_ELSEWHERE THEN EXISTS_TAC `1` THEN
  MP_TAC(SPECL [`1`; `Cx(&m)`] SUMMABLE_ZETA) THEN
  ASM_SIMP_TAC[RE_CX; REAL_OF_NUM_LT; ARITH_RULE `2 <= n ==> 1 < n`] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SUMMABLE_EQ) THEN
  SIMP_TAC[IN_FROM; CPOW_N; CX_INJ; REAL_OF_NUM_EQ; LE_1]);;

(* ------------------------------------------------------------------------- *)
(* Formulation of loop homotopy in terms of maps out of S^1                  *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_CIRCLEMAPS_IMP_HOMOTOPIC_LOOPS = prove
 (`!f:complex->real^N g s.
        homotopic_with (\h. T) (sphere(vec 0,&1),s) f g
        ==> homotopic_loops s (f o cexp o (\t. Cx(&2 * pi * drop t) * ii))
                              (g o cexp o (\t. Cx(&2 * pi * drop t) * ii))`,
  REWRITE_TAC[homotopic_loops; sphere; DIST_0] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
  EXISTS_TAC `{z:complex | norm z = &1}` THEN
  REWRITE_TAC[pathstart; pathfinish; o_THM; DROP_VEC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `&2 * pi * n = &2 * n * pi`] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[CEXP_INTEGER_2PI; INTEGER_CLOSED] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[COMPLEX_MUL_SYM] NORM_CEXP_II] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[CONTINUOUS_ON_CEXP] THEN
  REWRITE_TAC[CX_MUL] THEN
  REPEAT(MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
         REWRITE_TAC[CONTINUOUS_ON_CONST]) THEN
  SIMP_TAC[CONTINUOUS_ON_CX_DROP; CONTINUOUS_ON_ID]);;

let HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_CIRCLEMAPS = prove
 (`!p q s:real^N->bool.
        homotopic_loops s p q
        ==> homotopic_with (\h. T) (sphere(vec 0,&1),s)
                                   (p o (\z. lift(Arg z / (&2 * pi))))
                                   (q o (\z. lift(Arg z / (&2 * pi))))`,
 let ulemma = prove
   (`!s. s INTER (UNIV PCROSS {z | &0 <= Im z}) UNION
         s INTER (UNIV PCROSS {z | Im z <= &0}) = s`,
    REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_INTER; IN_UNION;
                 PASTECART_IN_PCROSS] THEN
    SET_TAC[REAL_LE_TOTAL]) in
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_loops; sphere; DIST_0] THEN
  GEN_REWRITE_TAC LAND_CONV [homotopic_with] THEN
  SIMP_TAC[pathstart; pathfinish; LEFT_IMP_EXISTS_THM; HOMOTOPIC_WITH] THEN
  X_GEN_TAC `h:real^(1,1)finite_sum->real^N` THEN STRIP_TAC THEN
  EXISTS_TAC `\w. (h:real^(1,1)finite_sum->real^N)
                  (pastecart (fstcart w)
                             (lift(Arg(sndcart w) / (&2 * pi))))` THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; o_THM] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC
     `(\z. if &0 <= Im(sndcart z)
           then h (pastecart (fstcart z) (lift(Arg(sndcart z) / (&2 * pi))))
           else h (pastecart (fstcart z)
                             (vec 1 - lift(Arg(cnj(sndcart z)) / (&2 * pi)))))
      :real^(1,2)finite_sum->real^N` THEN
    REWRITE_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`t:real^1`; `z:complex`] THEN STRIP_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[ARG_CNJ] THEN
      COND_CASES_TAC THENL [ASM_MESON_TAC[real; REAL_LE_REFL]; ALL_TAC] THEN
      SIMP_TAC[PI_POS; LIFT_SUB; LIFT_NUM; REAL_FIELD
        `&0 < pi ==> (&2 * pi - z) / (&2 * pi) = &1 - z / (&2 * pi)`] THEN
      REWRITE_TAC[VECTOR_ARITH `a - (a - b):real^N = b`];
      GEN_REWRITE_TAC RAND_CONV [GSYM ulemma] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN REWRITE_TAC[ulemma] THEN
      SIMP_TAC[CLOSED_IN_CLOSED_INTER; CLOSED_HALFSPACE_IM_LE; CLOSED_UNIV;
        CLOSED_PCROSS; REWRITE_RULE[real_ge] CLOSED_HALFSPACE_IM_GE] THEN
      REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTER; IN_DIFF;
       FSTCART_PASTECART; SNDCART_PASTECART; IN_UNIV; IN_SING; IN_ELIM_THM;
       GSYM CONJ_ASSOC; REAL_LE_ANTISYM; TAUT `~(p /\ ~p)`] THEN
      REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
       [ALL_TAC;
        REWRITE_TAC[GSYM ARG_EQ_0_PI; GSYM real; ARG_CNJ] THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        SIMP_TAC[REAL_ARITH `&2 * x - x = x`; COND_ID; GSYM LIFT_NUM; PI_POS;
         GSYM LIFT_SUB; REAL_FIELD
          `&0 < pi ==> &1 - pi / (&2 * pi) = pi / (&2 * pi)`] THEN
        COND_CASES_TAC THEN
        SIMP_TAC[REAL_SUB_RZERO; REAL_DIV_REFL; REAL_ENTIRE; REAL_OF_NUM_EQ;
                 ARITH_EQ; PI_NZ] THEN
        SIMP_TAC[real_div; REAL_MUL_LZERO; REAL_SUB_REFL; REAL_SUB_RZERO] THEN
        ASM_SIMP_TAC[LIFT_NUM]] THEN
      GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV) [GSYM o_DEF] THEN
      CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
        REWRITE_TAC[real_div; REWRITE_RULE[REAL_MUL_SYM] LIFT_CMUL] THEN
        MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
        REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
        REWRITE_TAC[o_DEF; GSYM CONTINUOUS_ON_CX_LIFT] THEN
        MP_TAC CONTINUOUS_ON_UPPERHALF_ARG THEN REWRITE_TAC[o_DEF] THEN
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CONTINUOUS_ON_SUBSET) THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; IN_INTER;
                    PASTECART_IN_PCROSS; IN_ELIM_THM; SNDCART_PASTECART] THEN
        MAP_EVERY X_GEN_TAC [`t:real^1`; `z:complex`] THEN
        SIMP_TAC[IN_DIFF; IN_ELIM_THM; IN_SING] THEN
        ASM_CASES_TAC `z = Cx(&0)` THEN ASM_REWRITE_TAC[COMPLEX_NORM_0] THEN
        REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ];
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; IN_INTER;
                    PASTECART_IN_PCROSS; IN_ELIM_THM; SNDCART_PASTECART;
                    FSTCART_PASTECART] THEN
        SIMP_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
        SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; PI_POS; REAL_MUL_LZERO;
             REAL_MUL_LID; REAL_ARITH `&0 < &2 * x <=> &0 < x`] THEN
        SIMP_TAC[ARG; REAL_LT_IMP_LE];
        MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
        REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
        REWRITE_TAC[real_div; REWRITE_RULE[REAL_MUL_SYM] LIFT_CMUL] THEN
        MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
        REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM o_DEF] THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART; CONTINUOUS_ON_COMPOSE;
                 CONTINUOUS_ON_CNJ] THEN
        REWRITE_TAC[o_DEF; GSYM CONTINUOUS_ON_CX_LIFT] THEN
        MP_TAC CONTINUOUS_ON_UPPERHALF_ARG THEN REWRITE_TAC[o_DEF] THEN
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CONTINUOUS_ON_SUBSET) THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; IN_INTER;
                    PASTECART_IN_PCROSS; IN_ELIM_THM; SNDCART_PASTECART] THEN
        MAP_EVERY X_GEN_TAC [`t:real^1`; `z:complex`] THEN
        SIMP_TAC[IN_DIFF; IN_ELIM_THM; IN_SING] THEN
        SIMP_TAC[IM_CNJ; REAL_NEG_GE0; CNJ_EQ_0] THEN
        ASM_CASES_TAC `z = Cx(&0)` THEN ASM_REWRITE_TAC[COMPLEX_NORM_0] THEN
        REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ];
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; IN_INTER;
                    PASTECART_IN_PCROSS; IN_ELIM_THM; SNDCART_PASTECART;
                    FSTCART_PASTECART] THEN
        SIMP_TAC[IN_INTERVAL_1; DROP_SUB; DROP_VEC; LIFT_DROP] THEN
        REWRITE_TAC[REAL_ARITH `&0 <= &1 - x /\ &1 - x <= &1 <=>
                                &0 <= x /\ x <= &1`] THEN
        SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; PI_POS; REAL_MUL_LZERO;
             REAL_MUL_LID; REAL_ARITH `&0 < &2 * x <=> &0 < x`] THEN
        SIMP_TAC[ARG; REAL_LT_IMP_LE]]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; IN_ELIM_THM] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `IMAGE h s SUBSET t ==> y IN s ==> h y IN t`)) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    SIMP_TAC[DROP_VEC; REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; PI_POS;
             REAL_ARITH `&0 < &2 * x <=> &0 < x`] THEN
    SIMP_TAC[REAL_MUL_LZERO; REAL_MUL_LID; ARG; REAL_LT_IMP_LE]]);;

let SIMPLY_CONNECTED_EQ_HOMOTOPIC_CIRCLEMAPS,
    SIMPLY_CONNECTED_EQ_CONTRACTIBLE_CIRCLEMAP =
 (CONJ_PAIR o prove)
 (`(!s:real^N->bool.
        simply_connected s <=>
        !f g:complex->real^N.
              f continuous_on sphere(vec 0,&1) /\
              IMAGE f (sphere(vec 0,&1)) SUBSET s /\
              g continuous_on sphere(vec 0,&1) /\
              IMAGE g (sphere(vec 0,&1)) SUBSET s
              ==> homotopic_with (\h. T) (sphere(vec 0,&1),s) f g) /\
   (!s:real^N->bool.
      simply_connected s <=>
      path_connected s /\
      !f:real^2->real^N.
              f continuous_on sphere(vec 0,&1) /\
              IMAGE f (sphere(vec 0,&1)) SUBSET s
              ==> ?a. homotopic_with (\h. T) (sphere(vec 0,&1),s) f (\x. a))`,
  REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN MATCH_MP_TAC(TAUT
   `(p ==> q) /\ (q ==> r) /\ (r ==> p) ==> (p <=> q) /\ (p <=> r)`) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[simply_connected] THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`f:complex->real^N`; `g:complex->real^N`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
     [`(f:complex->real^N) o cexp o (\t. Cx(&2 * pi * drop t) * ii)`;
      `(g:complex->real^N) o cexp o (\t. Cx(&2 * pi * drop t) * ii)`]) THEN
    ONCE_REWRITE_TAC[TAUT `p1 /\ q1 /\ r1 /\ p2 /\ q2 /\ r2 <=>
                           (p1 /\ r1 /\ q1) /\ (p2 /\ r2 /\ q2)`] THEN
    REWRITE_TAC[GSYM HOMOTOPIC_LOOPS_REFL] THEN
    ASM_SIMP_TAC[HOMOTOPIC_CIRCLEMAPS_IMP_HOMOTOPIC_LOOPS;
                 HOMOTOPIC_WITH_REFL] THEN
    DISCH_THEN(MP_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_CIRCLEMAPS) THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_EQ) THEN
    REWRITE_TAC[IN_SPHERE_0; LIFT_DROP; o_DEF] THEN X_GEN_TAC `z:complex` THEN
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN MP_TAC(SPEC `z:complex` ARG) THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_LID] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN SIMP_TAC[PI_POS;
      REAL_FIELD `&0 < pi ==> &2 * pi * x / (&2 * pi) = x`] THEN
    ASM_MESON_TAC[COMPLEX_MUL_SYM];
    DISCH_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[PATH_CONNECTED_EQ_HOMOTOPIC_POINTS] THEN
      MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`(\x. a):complex->real^N`; `(\x. b):complex->real^N`]) THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN DISCH_THEN
       (MP_TAC o MATCH_MP HOMOTOPIC_CIRCLEMAPS_IMP_HOMOTOPIC_LOOPS) THEN
      REWRITE_TAC[o_DEF; LINEPATH_REFL];
      X_GEN_TAC `f:complex->real^N` THEN STRIP_TAC THEN
      EXISTS_TAC `f(Cx(&1)):real^N` THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0]) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[COMPLEX_NORM_CX] THEN REAL_ARITH_TAC];
    STRIP_TAC THEN
    ASM_REWRITE_TAC[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_SOME] THEN
    X_GEN_TAC `p:real^1->real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
     `(p:real^1->real^N) o (\z. lift(Arg z / (&2 * pi)))`) THEN
    ANTS_TAC THENL
     [MP_TAC(ISPECL [`s:real^N->bool`; `p:real^1->real^N`]
        HOMOTOPIC_LOOPS_REFL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP
        HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_CIRCLEMAPS) THEN
      SIMP_TAC[HOMOTOPIC_WITH_REFL];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
      STRIP_TAC THEN FIRST_ASSUM
       (MP_TAC o MATCH_MP HOMOTOPIC_CIRCLEMAPS_IMP_HOMOTOPIC_LOOPS) THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0; o_DEF] THEN
      DISCH_THEN(MP_TAC o SPEC `Cx(&1)` o CONJUNCT2) THEN
      REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[LINEPATH_REFL] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HOMOTOPIC_LOOPS_TRANS) THEN
      MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IN_INTERVAL_1; FORALL_LIFT; LIFT_DROP; DROP_VEC] THEN
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_CASES_TAC `t = &1` THENL
       [ASM_REWRITE_TAC[REAL_ARITH `&2 * pi * &1 = &2 * &1 * pi`] THEN
        SIMP_TAC[CEXP_INTEGER_2PI; INTEGER_CLOSED; ARG_NUM] THEN
        REWRITE_TAC[real_div; REAL_MUL_LZERO; LIFT_NUM] THEN
        ASM_MESON_TAC[pathstart; pathfinish];
        AP_TERM_TAC THEN AP_TERM_TAC THEN SIMP_TAC[PI_POS; REAL_FIELD
         `&0 < pi ==> (t = x / (&2 * pi) <=> x = &2 * pi * t)`] THEN
        MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `Im(Cx (&2 * pi * t) * ii)` THEN
        CONJ_TAC THENL [MATCH_MP_TAC ARG_CEXP; ALL_TAC] THEN
        SIMP_TAC[IM_MUL_II; RE_CX; REAL_ARITH
          `a < &2 * pi <=> a < &2 * pi * &1`] THEN
        ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_LMUL_EQ; REAL_OF_NUM_LT; ARITH;
                     PI_POS; REAL_LT_IMP_LE; REAL_POS; REAL_LE_MUL] THEN
        ASM_REWRITE_TAC[REAL_LT_LE]]]]);;

let HOMOTOPY_EQUIVALENT_SIMPLE_CONNECTEDNESS = prove
 (`!s:real^M->bool t:real^N->bool.
        s homotopy_equivalent t
        ==> (simply_connected s <=> simply_connected t)`,
  REWRITE_TAC[SIMPLY_CONNECTED_EQ_HOMOTOPIC_CIRCLEMAPS] THEN
  REWRITE_TAC[HOMOTOPY_EQUIVALENT_HOMOTOPIC_TRIVIALITY]);;

(* ------------------------------------------------------------------------- *)
(* Homeomorphism of simple closed curves to circles.                         *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHIC_SIMPLE_PATH_IMAGE_CIRCLE = prove
 (`!g:real^1->real^N a:real^2 r.
        simple_path g /\ pathfinish g = pathstart g /\ &0 < r
        ==> (path_image g) homeomorphic sphere(a,r)`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC HOMEOMORPHIC_TRANS `sphere(vec 0:real^2,&1)` THEN
  ASM_SIMP_TAC[HOMEOMORPHIC_SPHERES; REAL_LT_01] THEN MP_TAC(ISPECL
   [`g:real^1->real^N`; `g:real^1->real^N`; `path_image(g:real^1->real^N)`]
   HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_CIRCLEMAPS) THEN
  REWRITE_TAC[HOMOTOPIC_LOOPS_REFL; HOMOTOPIC_WITH_REFL; SUBSET_REFL] THEN
  ASM_SIMP_TAC[SIMPLE_PATH_IMP_PATH] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
  EXISTS_TAC `(g:real^1->real^N) o (\z. lift(Arg z / (&2 * pi)))` THEN
  MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN
  ASM_REWRITE_TAC[COMPACT_SPHERE] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; path_image; FORALL_IN_IMAGE; IN_INTERVAL_1] THEN
    X_GEN_TAC `t:real^1` THEN REWRITE_TAC[DROP_VEC] THEN STRIP_TAC THEN
    REWRITE_TAC[IN_IMAGE; o_THM; IN_SPHERE_0] THEN
    ASM_CASES_TAC `t:real^1 = vec 1` THENL
     [EXISTS_TAC `Cx(&1)` THEN
      ASM_REWRITE_TAC[ARG_NUM; COMPLEX_NORM_CX; real_div; REAL_MUL_LZERO] THEN
      REWRITE_TAC[LIFT_NUM; REAL_ABS_NUM] THEN
      ASM_MESON_TAC[pathstart; pathfinish];
      EXISTS_TAC `cexp(ii * Cx(&2 * pi * drop t))` THEN
      REWRITE_TAC[NORM_CEXP_II] THEN AP_TERM_TAC THEN
      W(MP_TAC o PART_MATCH (lhand o rand) ARG_CEXP o
        lhand o rand o rand o snd) THEN
      REWRITE_TAC[IM_MUL_II; RE_CX] THEN ANTS_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_MUL; PI_POS_LE; REAL_POS] THEN
        SIMP_TAC[REAL_ARITH `&2 * pi * x < &2 * pi <=> pi * x < pi * &1`;
                 REAL_LT_LMUL_EQ; PI_POS] THEN
        ASM_REWRITE_TAC[REAL_LT_LE] THEN
        ASM_REWRITE_TAC[GSYM LIFT_EQ; LIFT_DROP; LIFT_NUM];
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN
        MP_TAC PI_POS THEN CONV_TAC REAL_FIELD]];
    MAP_EVERY X_GEN_TAC [`w:complex`; `z:complex`] THEN
    REWRITE_TAC[IN_SPHERE_0] THEN STRIP_TAC THEN
    MAP_EVERY (SUBST1_TAC o last o CONJUNCTS o C SPEC ARG)
     [`w:complex`; `z:complex`] THEN
    FIRST_X_ASSUM(MP_TAC o SYM o SYM) THEN
    ASM_REWRITE_TAC[o_DEF; COMPLEX_MUL_LID] THEN DISCH_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(REAL_FIELD
     `&0 < pi /\ x / (&2 * pi) = y / (&2 * pi) ==> x = y`) THEN
    REWRITE_TAC[PI_POS; GSYM LIFT_EQ] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simple_path]) THEN
    DISCH_THEN(MP_TAC  o SPECL
     [`lift(Arg w / (&2 * pi))`; `lift(Arg z / (&2 * pi))`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[GSYM LIFT_NUM; IN_INTERVAL_1; LIFT_DROP; LIFT_EQ] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; PI_POS;
                 REAL_ARITH `&0 < &2 * x <=> &0 < x`;
                 REAL_FIELD `&0 < y ==> (x / y = &1 <=> x = y)`] THEN
    SIMP_TAC[REAL_MUL_LZERO; REAL_MUL_LID; ARG; REAL_LT_IMP_LE;
             REAL_LT_IMP_NE]]);;

let HOMEOMORPHIC_SIMPLE_PATH_IMAGES = prove
 (`!g:real^1->real^M h:real^1->real^N.
        simple_path g /\ pathfinish g = pathstart g /\
        simple_path h /\ pathfinish h = pathstart h
        ==> (path_image g) homeomorphic (path_image h)`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC HOMEOMORPHIC_TRANS `sphere(vec 0:real^2,&1)` THEN
  CONJ_TAC THENL [ALL_TAC; ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM]] THEN
  MATCH_MP_TAC HOMEOMORPHIC_SIMPLE_PATH_IMAGE_CIRCLE THEN
  ASM_REWRITE_TAC[REAL_LT_01]);;

let ENR_PATH_IMAGE_SIMPLE_PATH = prove
 (`!g:real^1->real^N. simple_path g ==> ENR(path_image g)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `pathfinish g:real^N = pathstart g` THENL
   [MP_TAC(ISPECL [`g:real^1->real^N`; `vec 0:real^2`; `&1`]
        HOMEOMORPHIC_SIMPLE_PATH_IMAGE_CIRCLE) THEN
    ASM_REWRITE_TAC[REAL_LT_01] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP HOMEOMORPHIC_ENRNESS) THEN
    REWRITE_TAC[ENR_SPHERE];
    REWRITE_TAC[ENR] THEN EXISTS_TAC `(:real^N)` THEN
    REWRITE_TAC[OPEN_UNIV] THEN
    MATCH_MP_TAC ABSOLUTE_RETRACT_PATH_IMAGE_ARC THEN
    ASM_REWRITE_TAC[ARC_SIMPLE_PATH; SUBSET_UNIV]]);;

let ANR_PATH_IMAGE_SIMPLE_PATH = prove
 (`!g:real^1->real^N. simple_path g ==> ANR(path_image g)`,
  SIMP_TAC[ENR_PATH_IMAGE_SIMPLE_PATH; ENR_IMP_ANR]);;
