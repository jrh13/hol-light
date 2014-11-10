(* ========================================================================= *)
(* Proof that the complex exponential map is topologically transitive,       *)
(* following Misiurewicz's original paper "On iterates of e^z".              *)
(* Suggestion of problem and additional advice from Lasse Rempe-Gillen.      *)
(* ========================================================================= *)

needs "Multivariate/cauchy.ml";;

(* ------------------------------------------------------------------------- *)
(* Some preliminaries.                                                       *)
(* ------------------------------------------------------------------------- *)

let HAS_COMPLEX_DERIVATIVE_CEXP_COMPOSE = prove
 (`!f z. (f has_complex_derivative f') (at z)
         ==> ((\w. cexp(f w)) has_complex_derivative (f' * cexp(f z))) (at z)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM o_DEF] THEN
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
  MATCH_MP_TAC COMPLEX_DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
  COMPLEX_DIFF_TAC THEN REWRITE_TAC[COMPLEX_MUL_LID]);;

let COMPLEX_DIFFERENTIABLE_CEXP_COMPOSE = prove
 (`!f z. f complex_differentiable at z
         ==> (\w. cexp(f w)) complex_differentiable at z`,
  MESON_TAC[complex_differentiable; HAS_COMPLEX_DERIVATIVE_CEXP_COMPOSE]);;

let COMPLEX_DERIVATIVE_CEXP_COMPOSE = prove
 (`!f z. f complex_differentiable at z
         ==> complex_derivative (\w. cexp(f w)) z =
             complex_derivative f z * cexp(f z)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_CEXP_COMPOSE THEN
  ASM_REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE]);;

let COMPLEX_DIFFERENTIABLE_ITER_CEXP = prove
 (`!n z. (ITER n cexp) complex_differentiable at z`,
  GEN_REWRITE_TAC (funpow 2 BINDER_CONV o LAND_CONV) [GSYM ETA_AX] THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[ITER; COMPLEX_DIFFERENTIABLE_ID] THEN
  ASM_SIMP_TAC[COMPLEX_DIFFERENTIABLE_CEXP_COMPOSE]);;

let CONTINUOUS_ITER_CEXP = prove
 (`!n z. (ITER n cexp) continuous at z`,
  SIMP_TAC[COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT;
           COMPLEX_DIFFERENTIABLE_ITER_CEXP]);;

let HOLOMORPHIC_ON_ITER_CEXP = prove
 (`!n s. (ITER n cexp) holomorphic_on s`,
  SIMP_TAC[HOLOMORPHIC_ON_DIFFERENTIABLE; COMPLEX_DIFFERENTIABLE_AT_WITHIN;
           COMPLEX_DIFFERENTIABLE_ITER_CEXP]);;

let CONTINUOUS_ON_ITER_CEXP = prove
 (`!n s. (ITER n cexp) continuous_on s`,
  SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON; HOLOMORPHIC_ON_ITER_CEXP]);;

(* ------------------------------------------------------------------------- *)
(* Lemma 1.                                                                  *)
(* ------------------------------------------------------------------------- *)

let LEMMA_1 = prove
 (`!n z. 1 <= n
         ==> abs(Im(ITER n cexp z)) <= norm(complex_derivative(ITER n cexp) z)`,
  INDUCT_TAC THEN REWRITE_TAC[ITER; ARITH] THEN
  X_GEN_TAC `z:complex` THEN DISCH_THEN(K ALL_TAC) THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[ITER] THEN
  ASM_SIMP_TAC[COMPLEX_DERIVATIVE_CEXP_COMPOSE;
               COMPLEX_DIFFERENTIABLE_ITER_CEXP; ETA_AX] THEN
  ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[ITER_POINTLESS; I_DEF; o_DEF; COMPLEX_DERIVATIVE_ID;
                  COMPLEX_MUL_LID; COMPLEX_NORM_GE_RE_IM] THEN
  TRANS_TAC REAL_LE_TRANS
   `abs(Im(ITER n cexp z)) * norm(cexp (ITER n cexp z))` THEN
  ASM_SIMP_TAC[COMPLEX_NORM_MUL; REAL_LE_RMUL; NORM_POS_LE; LE_1] THEN
  SPEC_TAC(`ITER n cexp z`,`w:complex`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[IM_CEXP; NORM_CEXP; REAL_ABS_MUL; REAL_ABS_EXP] THEN
  SIMP_TAC[REAL_LE_LMUL_EQ; REAL_EXP_POS_LT; REAL_ABS_SIN_BOUND_LE]);;

(* ------------------------------------------------------------------------- *)
(* Lemma 2 (two parts)                                                       *)
(* ------------------------------------------------------------------------- *)

let LEMMA_2a = prove
 (`!z. abs(Im z) <= pi / &3 ==> Re(cexp z) >= Re z + (&1 - log(&2))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RE_CEXP; real_ge] THEN
  TRANS_TAC REAL_LE_TRANS `exp(Re z) / &2` THEN CONJ_TAC THENL
   [ALL_TAC;
    SIMP_TAC[real_div; REAL_LE_LMUL_EQ; REAL_EXP_POS_LT] THEN
    MP_TAC(ISPECL [`pi / &3`; `abs(Im z)`] COS_MONO_LE_EQ) THEN
    ASM_REWRITE_TAC[COS_ABS] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS) THEN
    REWRITE_TAC[COS_PI3] THEN CONV_TAC REAL_RAT_REDUCE_CONV] THEN
  ABBREV_TAC `x = Re z - log(&2)` THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
   `z - l:real = x ==> z = x + l`)) THEN
  SIMP_TAC[REAL_EXP_ADD; EXP_LOG; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[REAL_EXP_LE_X; REAL_ARITH
   `(x + l) + &1 - l <= (e * &2) / &2 <=> &1 + x <= e`]);;

let LEMMA_2b = prove
 (`!z. ~(real z) ==> ?n. abs(Im(ITER n cexp z)) > pi / &3`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[MESON[] `(?n. P n) <=> (!n. ~P n) ==> F`] THEN
  REWRITE_TAC[real_gt; REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!n. abs(Im(ITER (n + 1) cexp z)) >=
        (&2 / &5 * exp(Re(ITER n cexp z))) * abs(Im(ITER n cexp z))`
  (LABEL_TAC "*") THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[ITER; GSYM ADD1; IM_CEXP; REAL_ABS_EXP; REAL_ABS_MUL] THEN
    REWRITE_TAC[REAL_ARITH `e * x >= (y * e) * z <=> e * y * z <= e * x`] THEN
    SIMP_TAC[REAL_LE_LMUL_EQ; REAL_EXP_POS_LT] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    SPEC_TAC(`Im(ITER n cexp z)`,`x:real`) THEN
    MATCH_MP_TAC(MESON[REAL_LE_NEGTOTAL]
     `(!x. P(--x) <=> P x) /\ (!x. &0 <= x ==> P x) ==> !x. P x`) THEN
    REWRITE_TAC[SIN_NEG; REAL_ABS_NEG] THEN
    SIMP_TAC[real_abs; SIN_POS_PI_LE; REAL_ARITH
     `&0 <= x /\ x <= pi / &3 ==> x <= pi`] THEN
    REPEAT STRIP_TAC THEN MP_TAC(SPECL [`0`; `Cx x`] TAYLOR_CSIN) THEN
    REWRITE_TAC[VSUM_SING_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[IM_CX; REAL_ABS_NUM; REAL_EXP_0; GSYM CX_SIN] THEN
    REWRITE_TAC[complex_pow; COMPLEX_POW_1] THEN
    REWRITE_TAC[GSYM CX_DIV; GSYM CX_POW; GSYM CX_MUL; GSYM CX_SUB;
                GSYM CX_ADD; GSYM CX_NEG; COMPLEX_NORM_CX; REAL_MUL_LID] THEN
    MATCH_MP_TAC(REAL_ARITH
     `e <= (&1 - a) * x ==> abs(sin x - x / &1) <= e ==> a * x <= sin x`) THEN
    ASM_SIMP_TAC[real_abs; REAL_ARITH
     `x pow 3 / &2 <= a * x <=> x * x pow 2 <= x * &2 * a`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    TRANS_TAC REAL_LE_TRANS `(pi / &3) pow 2` THEN
    ASM_SIMP_TAC[REAL_POW_LE2; REAL_ARITH
     `(pi / &3) pow 2 <= a <=> pi pow 2 <= &9 * a`] THEN
    TRANS_TAC REAL_LE_TRANS `(&16 / &5) pow 2` THEN
    CONJ_TAC THENL [ALL_TAC; CONV_TAC REAL_RAT_REDUCE_CONV] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. &0 < abs(Im(ITER n cexp z))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_ABS_NZ] THEN
    INDUCT_TAC THENL [ASM_MESON_TAC[ITER; real]; ALL_TAC] THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `n:num`) THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    SIMP_TAC[ADD1; real_ge; REAL_NOT_LE; REAL_ABS_NUM] THEN DISCH_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[GSYM REAL_ABS_NZ; REAL_EXP_POS_LT] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?N. !n. N <= n
            ==> abs(Im(ITER (n + 1) cexp z)) >= &2 * abs(Im(ITER n cexp z))`
  CHOOSE_TAC THENL
   [MP_TAC(ISPEC `&1 - log(&2)` REAL_ARCH) THEN ANTS_TAC THENL
     [MP_TAC LOG2_APPROX_32 THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `log(&5) - Re z`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `n:num`) THEN MATCH_MP_TAC(REAL_ARITH
     `&5 * b <= u * v ==> x >= (&2 / &5 * u) * v ==> x >= &2 * b`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    ONCE_REWRITE_TAC[SYM(MATCH_MP EXP_LOG (REAL_ARITH `&0 < &5`))] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    TRANS_TAC REAL_LE_TRANS `Re z + &N * (&1 - log(&2))` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `Re z + &n * (&1 - log(&2))` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_LADD] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN MP_TAC LOG2_APPROX_32 THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SPEC_TAC(`n:num`,`m:num`) THEN INDUCT_TAC THENL
     [REWRITE_TAC[ITER; REAL_MUL_LZERO; REAL_ADD_RID; REAL_LE_REFL];
      REWRITE_TAC[GSYM REAL_OF_NUM_SUC]] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `z + m * l <= n ==> s >= n + l ==> z + (m + &1) * l <= s`)) THEN
    REWRITE_TAC[ITER] THEN MATCH_MP_TAC LEMMA_2a THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `!n. abs(Im(ITER n cexp z)) <= pi / &3` THEN
  MP_TAC(SPECL [`&2`; `pi / &3 / abs(Im (ITER N cexp z))`]
        REAL_ARCH_POW) THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_TAC `d:num`) THEN
  DISCH_THEN(MP_TAC o SPEC `N + d:num`) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `p < x ==> x <= a ==> a <= p ==> F`)) THEN
  SPEC_TAC(`d:num`,`m:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; real_pow; REAL_MUL_LID; REAL_LE_REFL] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `m * a <= b ==> c >= &2 * b  ==> (&2 * m) * a <= c`)) THEN
  REWRITE_TAC[ADD1] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[LE_ADD]);;

(* ------------------------------------------------------------------------- *)
(* Lemma 3.                                                                  *)
(* ------------------------------------------------------------------------- *)

let LEMMA_3 = prove
 (`!n b r s.
        &0 < r /\
        (!w z. w IN ball(b,r) /\ z IN ball(b,r) /\
               ITER n cexp w = ITER n cexp z
               ==> w = z) /\
        (!z. z IN ball(b,r)
             ==> s <= r * norm(complex_derivative (ITER n cexp) z))
        ==> ball(ITER n cexp b,s) SUBSET IMAGE (ITER n cexp) (ball(b,r))`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC(REAL_ARITH `s <= &0 \/ &0 < s`) THENL
   [ASM_MESON_TAC[BALL_EQ_EMPTY; EMPTY_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPEC `n:num` COMPLEX_DIFFERENTIABLE_ITER_CEXP) THEN
  SPEC_TAC(`ITER n cexp`,`f:complex->complex`) THEN
  REWRITE_TAC[INJECTIVE_ON_ALT] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:complex->complex`; `ball(b:complex,r)`]
        HOLOMORPHIC_ON_INVERSE) THEN
  ASM_REWRITE_TAC[INJECTIVE_ON_ALT; OPEN_BALL] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[HOLOMORPHIC_ON_DIFFERENTIABLE;
                 COMPLEX_DIFFERENTIABLE_AT_WITHIN];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `g:complex->complex` STRIP_ASSUME_TAC))] THEN
  ABBREV_TAC
   `c = closest_point ((:complex) DIFF IMAGE f (ball(b:complex,r))) (f b)` THEN
  MP_TAC(ISPECL [`(:complex) DIFF IMAGE f (ball(b:complex,r))`;
                 `(f:complex->complex) b`]
        CLOSEST_POINT_EXISTS) THEN
  ASM_REWRITE_TAC[GSYM OPEN_CLOSED; IN_DIFF; IN_UNIV] THEN ANTS_TAC THENL
   [REWRITE_TAC[SET_RULE `UNIV DIFF s = {} <=> s = UNIV`] THEN
    DISCH_THEN(MP_TAC o AP_TERM `bounded:(complex->bool)->bool`) THEN
    REWRITE_TAC[NOT_BOUNDED_UNIV] THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `IMAGE (f:complex->complex) (cball(b,r))` THEN
    SIMP_TAC[IMAGE_SUBSET; BALL_SUBSET_CBALL] THEN
    MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    REWRITE_TAC[COMPACT_CBALL] THEN
    ASM_SIMP_TAC[HOLOMORPHIC_ON_DIFFERENTIABLE;
                 HOLOMORPHIC_ON_IMP_CONTINUOUS_ON;
                 COMPLEX_DIFFERENTIABLE_AT_WITHIN];
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o BINDER_CONV)
     [GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[GSYM IN_BALL; REAL_NOT_LE; GSYM SUBSET]] THEN
  ABBREV_TAC `t = dist((f:complex->complex) b,c)` THEN STRIP_TAC THEN
  ASM_CASES_TAC `s:real <= t` THENL
   [ASM_MESON_TAC[SUBSET_BALL; SUBSET_TRANS]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[GSYM DIST_NZ] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `~(y IN IMAGE f s) ==> x IN s ==> ~(f x = y)`)) THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `c IN closure(IMAGE (f:complex->complex) (ball (b,r)) INTER
                 ball(f b,t))`
  MP_TAC THENL
   [ASM_SIMP_TAC[SET_RULE `s SUBSET t ==> t INTER s = s`] THEN
    ASM_SIMP_TAC[CLOSURE_BALL] THEN
    ASM_REWRITE_TAC[IN_CBALL; REAL_LE_REFL];
    REWRITE_TAC[CLOSURE_SEQUENTIAL]] THEN
  REWRITE_TAC[IN_IMAGE; IN_INTER; SKOLEM_THM; FORALL_AND_THM] THEN
  ONCE_REWRITE_TAC[GSYM FUN_EQ_THM] THEN
  REWRITE_TAC[ETA_AX; LEFT_AND_EXISTS_THM; GSYM CONJ_ASSOC] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[UNWIND_THM2] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:num->complex` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!n. (z:num->complex) n IN cball(b,t / s * r)`
  ASSUME_TAC THENL
   [ALL_TAC;
    MP_TAC(ISPEC `cball(b:complex,t / s * r)` compact) THEN
    REWRITE_TAC[COMPACT_CBALL] THEN
    DISCH_THEN(MP_TAC o SPEC `z:num->complex`) THEN
    ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`w:complex`; `r:num->num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [IN_IMAGE]) THEN
    REWRITE_TAC[] THEN EXISTS_TAC `w:complex` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
      EXISTS_TAC `(f:complex->complex) o z o (r:num->num)` THEN
      REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
       [REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC LIM_SUBSEQUENCE THEN
        ASM_REWRITE_TAC[o_DEF];
        MP_TAC(ISPECL [`f:complex->complex`; `sequentially`]
          LIM_CONTINUOUS_FUNCTION) THEN
        REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[GSYM o_DEF] THEN
        ASM_SIMP_TAC[COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT]];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `x IN s ==> s SUBSET t ==> x IN t`)) THEN
      REWRITE_TAC[SUBSET_BALLS; DIST_REFL; REAL_ADD_LID] THEN
      DISJ1_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      ASM_SIMP_TAC[REAL_LT_RMUL_EQ; REAL_LT_LDIV_EQ; REAL_MUL_LID]]] THEN
  UNDISCH_TAC `!n:num. (f:complex->complex) (z n) IN ball (f b,t)` THEN
  UNDISCH_TAC `!n:num. z n IN ball(b:complex,r)` THEN
  REWRITE_TAC[AND_FORALL_THM; IMP_IMP] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `nn:num` THEN
  SPEC_TAC(`(z:num->complex) nn`,`w:complex`) THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:complex->complex`; `complex_derivative g`;
                `ball((f:complex->complex) b,t)`;
                 `r / s:real`]
        COMPLEX_MVT) THEN
  REWRITE_TAC[CONVEX_BALL] THEN ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPECL
     [`(f:complex->complex) b`; `(f:complex->complex) w`]) THEN
    ASM_SIMP_TAC[CENTRE_IN_BALL; IN_CBALL] THEN
    MATCH_MP_TAC(NORM_ARITH
     `s <= t ==> norm(w - b) <= s ==> dist(b,w) <= t`) THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `t / s * r:real = r / s * t`] THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_LT_DIV] THEN
    ASM_MESON_TAC[IN_BALL; dist; DIST_SYM; REAL_LT_IMP_LE]] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOLOMORPHIC_ON_DIFFERENTIABLE]) THEN
  ASM_SIMP_TAC[HAS_COMPLEX_DERIVATIVE_WITHIN_OPEN; OPEN_BALL;
               COMPLEX_DIFFERENTIABLE_WITHIN_OPEN] THEN
  REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
  DISCH_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
   `t SUBSET IMAGE f s
    ==> (!x. x IN s ==> P(f x)) ==> !x. x IN t ==> P x`)) THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
  EXISTS_TAC `norm(complex_derivative f z)` THEN
  ASM_SIMP_TAC[GSYM COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  REWRITE_TAC[REAL_ARITH `n * r / s:real = (r * n) / s`] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; COMPLEX_NORM_NZ; REAL_MUL_LID] THEN
  ASM_MESON_TAC[COMPLEX_RING `a * b = Cx(&1) ==> ~(a = Cx(&0))`]);;

(* ------------------------------------------------------------------------- *)
(* Lemma 4.                                                                  *)
(* ------------------------------------------------------------------------- *)

let LEMMA_4 = prove
 (`!v. ~(v = {}) /\ open v /\ connected v
        ==> FINITE {n | DISJOINT (IMAGE (ITER n cexp) v)
                                 {z | abs(Im z) <= pi / &3}}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?N. !n. N < n
            ==> ~DISJOINT (IMAGE (ITER n cexp) v) {z | abs(Im z) <= pi / &3}`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> p) ==> p`) THEN DISCH_TAC;
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..N` THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    ASM_REWRITE_TAC[NOT_LE]] THEN
  SUBGOAL_THEN
   `?n z:complex. z IN v /\ integer(Im(ITER n cexp z) / pi)`
  STRIP_ASSUME_TAC THENL
   [ALL_TAC;
    EXISTS_TAC `n:num` THEN REWRITE_TAC[LT_EXISTS; LEFT_IMP_EXISTS_THM] THEN
    SUBGOAL_THEN `!d. real(ITER (n + SUC d) cexp z)` ASSUME_TAC THENL
     [INDUCT_TAC THEN ONCE_REWRITE_TAC[ADD_CLAUSES] THENL
       [REWRITE_TAC[ADD_CLAUSES; ITER; real; IM_CEXP; REAL_ENTIRE] THEN
        DISJ2_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP SIN_INTEGER_PI) THEN
        SIMP_TAC[REAL_DIV_RMUL; PI_NZ];
        ASM_SIMP_TAC[ITER; REAL_EXP]];
      MAP_EVERY X_GEN_TAC [`q:num`; `d:num`] THEN DISCH_THEN SUBST1_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `d:num`) THEN MATCH_MP_TAC(SET_RULE
       `(!x. real x ==> x IN t) /\ z IN s
        ==> real(f z) ==> ~DISJOINT (IMAGE f s) t`) THEN
      ASM_SIMP_TAC[real; IN_ELIM_THM] THEN MP_TAC PI_POS THEN
      REAL_ARITH_TAC]] THEN
  SUBGOAL_THEN
   `?n w z. w IN v /\ z IN v /\
            pi <= abs(Im(ITER n cexp w) - Im(ITER n cexp z))`
  MP_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MATCH_MP_TAC WLOG_RELATION THEN
    EXISTS_TAC `\w z. Im(ITER n cexp z) <= Im(ITER n cexp w)` THEN
    REWRITE_TAC[REAL_LE_TOTAL] THEN
    CONJ_TAC THENL [MESON_TAC[REAL_ABS_SUB]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`w:complex`; `z:complex`] THEN
    SIMP_TAC[real_abs; REAL_SUB_LE] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL
     [`IMAGE (ITER n cexp) v`; `ITER n cexp z`; `ITER n cexp w`;
      `floor(Im(ITER n cexp w) / pi) * pi`; `2`]
        CONNECTED_IVT_COMPONENT) THEN
    REWRITE_TAC[DIMINDEX_2; ARITH; GSYM IM_DEF; EXISTS_IN_IMAGE] THEN
    SIMP_TAC[PI_POS; REAL_ARITH `&0 < &2`; REAL_LT_MUL;
             GSYM REAL_LE_LDIV_EQ; GSYM REAL_LE_RDIV_EQ] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FLOOR] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
        SIMP_TAC[HOLOMORPHIC_ON_DIFFERENTIABLE;
                 COMPLEX_DIFFERENTIABLE_ITER_CEXP;
                 HOLOMORPHIC_ON_IMP_CONTINUOUS_ON;
                 COMPLEX_DIFFERENTIABLE_AT_WITHIN];
        REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
        MATCH_MP_TAC(REAL_ARITH
         `x + &1 <= y /\ y < floor y + &1 ==> x <= floor y`) THEN
        REWRITE_TAC[FLOOR] THEN
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ADD_RDISTRIB; REAL_DIV_RMUL;
                     PI_POS; REAL_LT_IMP_NZ;
                     IM_ADD; IM_MUL_II; RE_CX; REAL_LE_LADD] THEN
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:complex` THEN
      STRIP_TAC THEN
      ASM_SIMP_TAC[PI_NZ; FLOOR; REAL_FIELD
       `~(pi = &0) ==> (x * pi) / pi = x`]]] THEN
  ASM_CASES_TAC
   `!n w z. w IN v /\ z IN v /\ ITER n cexp w = ITER n cexp z ==> w = z`
  THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN INDUCT_TAC THEN SIMP_TAC[ITER] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (TAUT
     `(p ==> r) ==> (~p ==> q ==> r) ==> (q ==> r)`)) THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN
    DISCH_THEN(fun th -> EXISTS_TAC `n:num` THEN MP_TAC th) THEN
    REWRITE_TAC[NOT_FORALL_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:complex` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:complex` THEN
    REWRITE_TAC[NOT_IMP] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`w:complex`; `z:complex`]) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CEXP_EQ]) THEN
    DISCH_THEN(X_CHOOSE_THEN `i:real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[IM_ADD; REAL_ADD_SUB; IM_MUL_II; RE_CX] THEN
    ASM_CASES_TAC `i = &0` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; COMPLEX_MUL_LZERO;
                    COMPLEX_ADD_RID] THEN
    DISCH_THEN(K ALL_TAC) THEN
    SIMP_TAC[REAL_ABS_MUL; REAL_ABS_PI; REAL_ABS_NUM] THEN
    REWRITE_TAC[REAL_ARITH `pi <= &2 * x * pi <=> pi * &1 <= pi * &2 * x`] THEN
    SIMP_TAC[REAL_LE_LMUL_EQ; PI_POS] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &1 <= &2 * x`) THEN
    MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN
    ASM_REWRITE_TAC[]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INJECTIVE_ON_ALT]) THEN
  SUBGOAL_THEN
   `?r. ((!n. 0 < r n) /\
         (!n. DISJOINT (IMAGE (ITER (r n) cexp) v)
              {z | abs (Im z) <= pi / &3})) /\
        (!n. r n < r(SUC n))`
  STRIP_ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[AND_FORALL_THM] THEN
    MATCH_MP_TAC DEPENDENT_CHOICE THEN
    ASM_MESON_TAC[ARITH_RULE `m < n ==> 0 < n`];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m n. m < n ==> (r:num->num) m < r n` ASSUME_TAC THENL
   [MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN ASM_MESON_TAC[LT_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n z. z IN v
          ==> (pi / &3) pow n <= norm(complex_derivative (ITER (r n) cexp) z)`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN X_GEN_TAC `z:complex` THEN DISCH_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `abs(Im(ITER (r 0) cexp z))` THEN
      ASM_SIMP_TAC[real_pow; LE_1; LEMMA_1] THEN
      UNDISCH_TAC `(z:complex) IN v` THEN
      SPEC_TAC(`z:complex`,`z:complex`) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `DISJOINT (IMAGE f s) t ==> (!z. ~(z IN t) ==> P z)
         ==> !z. z IN s ==> P(f z)`) o SPEC `0`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ITER (r (SUC n)) cexp = ITER (r(SUC n) - r n) cexp o ITER (r n) cexp`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; ITER_ADD] THEN
      ASM_SIMP_TAC[SUB_ADD; LT_IMP_LE];
      SIMP_TAC[COMPLEX_DERIVATIVE_CHAIN;COMPLEX_DIFFERENTIABLE_ITER_CEXP]] THEN
    REWRITE_TAC[real_pow; COMPLEX_NORM_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x / &3 <=> &0 < x`; PI_POS; REAL_POW_LE;
                 REAL_LT_IMP_LE] THEN
    W(MP_TAC o PART_MATCH (rand o rand) LEMMA_1 o rand o snd) THEN
    ASM_SIMP_TAC[ARITH_RULE `m < n ==> 1 <= n - m`] THEN
    ASM_SIMP_TAC[ITER_ADD; SUB_ADD; LT_IMP_LE] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS) THEN
    UNDISCH_TAC `(z:complex) IN v` THEN
      SPEC_TAC(`z:complex`,`z:complex`) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
       `DISJOINT (IMAGE f s) t ==> !P. (!z. ~(z IN t) ==> P z)
         ==> !z. z IN s ==> P(f z)`) o SPEC `SUC n`) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `z:complex`) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `r:real` THEN
  STRIP_TAC THEN MP_TAC(ISPECL [`pi / &3`; `pi / r`] REAL_ARCH_POW) THEN
  ANTS_TAC THENL [MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] REAL_LT_LDIV_EQ] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `(r:num->num) n` THEN
  MP_TAC(ISPECL [`(r:num->num) n`; `z:complex`; `r:real`; `pi`] LEMMA_3) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; X_GEN_TAC `w:complex`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `pi < x ==> x <= y ==> pi <= y`)) THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN ASM SET_TAC[];
    ABBREV_TAC `w = ITER (r(n:num)) cexp z` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN(fun th ->
      MP_TAC(SPEC `w - pi / &2 % basis 2:complex` th) THEN
      MP_TAC(SPEC `w + pi / &2 % basis 2:complex` th)) THEN
    SIMP_TAC[IN_BALL; NORM_MUL; NORM_BASIS; DIMINDEX_2; ARITH; PI_POS;
      REAL_ARITH `&0 < pi ==> abs(pi / &2) * &1 < pi`;
      NORM_ARITH `dist(w,w + x) = norm x /\ dist(w,w - x) = norm x`] THEN
    REWRITE_TAC[IN_IMAGE; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `a:complex` THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    X_GEN_TAC `b:complex` THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    MAP_EVERY EXISTS_TAC [`a:complex`; `b:complex`] THEN
    REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    ASM_REWRITE_TAC[IM_ADD; IM_SUB; COMPLEX_CMUL; IM_MUL_CX] THEN
    SIMP_TAC[IM_DEF; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Lemma 5.                                                                  *)
(* ------------------------------------------------------------------------- *)

let LEMMA_5 = prove
 (`!v. ~(v = {}) /\ open v /\ connected v /\
       INFINITE {n | IMAGE (ITER n cexp) v SUBSET {z | Re z > &4}}
       ==> ?n. ~(IMAGE (ITER n cexp) v INTER real = {})`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM NOT_FORALL_THM] THEN
  DISCH_TAC THEN MAP_EVERY ABBREV_TAC
   [`h = {z | Re z > &4}`;
    `s = {z | abs(Im z) <= pi / &3}`;
    `w = {z | abs(Im z) <= &2 * pi /\ abs(Im(cexp z)) <= &2 * pi}`] THEN
  SUBGOAL_THEN `DISJOINT (frontier s) (w INTER h:complex->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN
    REWRITE_TAC[IM_DEF; FRONTIER_STRIP_COMPONENT_LE] THEN
    REWRITE_TAC[GSYM IM_DEF] THEN MATCH_MP_TAC(SET_RULE
     `(!x. x IN s /\ x IN u ==> ~(x IN t)) ==> DISJOINT s (t INTER u)`) THEN
    MAP_EVERY EXPAND_TAC ["h"; "w"] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `z:complex` THEN REWRITE_TAC[IM_CEXP; real_gt] THEN
    STRIP_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[REAL_NOT_LE; REAL_ABS_MUL; REAL_ABS_EXP] THEN
    SUBGOAL_THEN `abs(sin(Im z)) = sqrt(&3) / &2` SUBST1_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o MATCH_MP (REAL_ARITH
       `abs x = a ==> x = a \/ x = --a`)) THEN
      REWRITE_TAC[SIN_NEG; SIN_PI3; REAL_ABS_NEG] THEN
      SIMP_TAC[REAL_ABS_REFL; REAL_LE_DIV; SQRT_POS_LE; REAL_POS];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
      `pi < &4 /\ &2 pow 4 <= x * y ==> &2 * pi < x * y / &2`) THEN
    CONJ_TAC THENL [MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= x /\ x * &1 <= x * s ==> a <= x * s`) THEN
    CONJ_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `exp(&4 * &1)` THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_EXP_N] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
        MP_TAC E_APPROX_32 THEN REAL_ARITH_TAC;
        REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      SUBST1_TAC(SYM SQRT_1) THEN MATCH_MP_TAC SQRT_MONO_LE THEN
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. IMAGE (ITER n cexp) v INTER frontier {z | abs (Im z) <= &2 * pi} = {}`
  ASSUME_TAC THENL
   [REWRITE_TAC[IM_DEF; FRONTIER_STRIP_COMPONENT_LE] THEN
    REWRITE_TAC[GSYM IM_DEF] THEN X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC n`) THEN
    REWRITE_TAC[ITER_POINTLESS; IMAGE_o] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x. x IN t ==> real(f x))
      ==> IMAGE f s INTER real = {} ==> s INTER t = {}`) THEN
    REWRITE_TAC[IN_ELIM_THM; real; IM_CEXP] THEN GEN_TAC THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC o MATCH_MP (REAL_ARITH
     `abs x = a ==> x = a \/ x = --a`)) THEN
    REWRITE_TAC[SIN_NEG; SIN_NPI; REAL_MUL_RZERO; REAL_NEG_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. IMAGE (ITER n cexp) v INTER frontier {z | abs(Im(cexp z)) <= &2 * pi} =
        {}`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `SUC n`) THEN
    REWRITE_TAC[ITER_POINTLESS; IMAGE_o] THEN MATCH_MP_TAC(SET_RULE
     `IMAGE f u SUBSET t
      ==> IMAGE f s INTER t = {} ==> s INTER u = {}`) THEN
    REWRITE_TAC[FRONTIER_CLOSURES; REAL_NOT_LE; SET_RULE
     `UNIV DIFF {x | P x} = {x | ~P x}`] THEN
    MATCH_MP_TAC(SET_RULE
     `IMAGE f s SUBSET t /\ IMAGE f u SUBSET v
      ==> IMAGE f (s INTER u) SUBSET t INTER v`) THEN
    CONJ_TAC THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    MATCH_MP_TAC FORALL_IN_CLOSURE THEN
    REWRITE_TAC[CLOSED_CLOSURE; CONTINUOUS_ON_CEXP] THEN
    GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {n | DISJOINT (IMAGE (ITER n cexp) v) w}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{n | DISJOINT (IMAGE (ITER n cexp) v)
                              {z | abs(Im z) <= pi / &3}} UNION
                {n | DISJOINT (IMAGE (ITER (n + 1) cexp) v)
                              {z | abs(Im z) <= pi / &3}}` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[FINITE_UNION; LEMMA_4] THEN
      GEN_REWRITE_TAC
       (RAND_CONV o RAND_CONV o ABS_CONV o BINDER_CONV o RAND_CONV)
       [ARITH_RULE `n = (n + 1) - 1`] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `IMAGE (\n. n - 1)
                        {n | DISJOINT (IMAGE (ITER n cexp) v)
                                      {z | abs (Im z) <= pi / &3}}` THEN
      ASM_SIMP_TAC[LEMMA_4; FINITE_IMAGE] THEN SET_TAC[];
      EXPAND_TAC "w" THEN
      REWRITE_TAC[SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
      MATCH_MP_TAC(SET_RULE
       `((!n. f n SUBSET s \/ DISJOINT (f n) s) /\
         (!n. f n SUBSET t \/ DISJOINT (f n) t))/\
        {n | DISJOINT (f n) s} UNION {n | DISJOINT (f n) t} SUBSET u
        ==> {n | DISJOINT (f n) (s INTER t)} SUBSET u`) THEN
      CONJ_TAC THENL
       [CONJ_TAC THEN GEN_TAC THEN MATCH_MP_TAC(SET_RULE
         `~(~(s INTER (UNIV DIFF t) = {}) /\ ~(s DIFF (UNIV DIFF t) = {}))
          ==> s SUBSET t \/ DISJOINT s t`) THEN
        DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
          CONNECTED_INTER_FRONTIER)) THEN
        ASM_REWRITE_TAC[FRONTIER_COMPLEMENT] THEN
        ASM_SIMP_TAC[CONNECTED_CONTINUOUS_IMAGE; CONTINUOUS_ON_ITER_CEXP];
        MATCH_MP_TAC(SET_RULE
         `s SUBSET s' /\ t SUBSET t'
          ==> (s UNION t) SUBSET (s' UNION t')`) THEN
        CONJ_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        X_GEN_TAC `n:num` THENL
         [MATCH_MP_TAC(SET_RULE
           `(!x. x IN s ==> x IN t) ==> DISJOINT u t ==> DISJOINT u s`);
          REWRITE_TAC[GSYM ADD1; ITER_POINTLESS; IMAGE_o] THEN
          MATCH_MP_TAC(SET_RULE
           `(!z. Q z ==> P z) ==> DISJOINT t {z | P(cexp z)}
             ==> DISJOINT (IMAGE cexp t) {z | Q z}`)] THEN
        REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {n | ~(IMAGE (ITER n cexp) v SUBSET w)}`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      FINITE_SUBSET)) THEN
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC(SET_RULE
     `(~(s INTER (UNIV DIFF t) = {}) /\ ~(s DIFF (UNIV DIFF t) = {}) ==> F)
      ==> ~(s SUBSET t) ==> DISJOINT s t`) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
          CONNECTED_INTER_FRONTIER)) THEN
    ASM_SIMP_TAC[CONNECTED_CONTINUOUS_IMAGE; CONTINUOUS_ON_ITER_CEXP] THEN
    REWRITE_TAC[FRONTIER_COMPLEMENT] THEN EXPAND_TAC "w" THEN
    REWRITE_TAC[SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
    W(MP_TAC o PART_MATCH lhand FRONTIER_INTER_SUBSET o
      rand o lhand o snd) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?N. (!n. N <= n ==> ~(IMAGE (ITER n cexp) v INTER s = {})) /\
        (!n. N <= n ==> IMAGE (ITER n cexp) v SUBSET w)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`\n:num. n`;
      `{n | ~(IMAGE (ITER n cexp) v SUBSET w)} UNION
       {n | DISJOINT (IMAGE (ITER n cexp) v) s}`]
     UPPER_BOUND_FINITE_SET) THEN ASM_SIMP_TAC[FINITE_UNION] THEN
     ANTS_TAC THENL [ASM_MESON_TAC[LEMMA_4]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num`
     (fun th -> EXISTS_TAC `N + 1` THEN MP_TAC th)) THEN
    REWRITE_TAC[ARITH_RULE `N + 1 <= n <=> ~(n <= N)`; CONTRAPOS_THM] THEN
    REWRITE_TAC[DISJOINT; IN_ELIM_THM; IN_UNION] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~({n | IMAGE (ITER n cexp) v SUBSET w INTER h} SUBSET 0..N)`
  MP_TAC THENL
   [DISCH_THEN(MP_TAC o
      MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET)) THEN
    REWRITE_TAC[FINITE_NUMSEG; GSYM INFINITE] THEN
    MATCH_MP_TAC INFINITE_SUPERSET THEN
    EXISTS_TAC `{n | IMAGE (ITER n cexp) v SUBSET h} DIFF
                {n |  ~(IMAGE (ITER n cexp) v SUBSET w)}` THEN
    ASM_SIMP_TAC[INFINITE_DIFF_FINITE] THEN SET_TAC[];
    ALL_TAC] THEN
  PURE_ONCE_REWRITE_TAC[SUBSET] THEN
  REWRITE_TAC[NOT_IMP; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[SUBSET_INTER] THEN STRIP_TAC THEN
  MATCH_MP_TAC(ARITH_RULE `~(m:num <= n) ==> n <= m`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`IMAGE (ITER n cexp) v`; `s:complex->bool`]
        CONNECTED_INTER_FRONTIER) THEN
  ASM_SIMP_TAC[CONNECTED_CONTINUOUS_IMAGE; CONTINUOUS_ON_ITER_CEXP;
               NOT_IMP] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  REWRITE_TAC[SET_RULE `s DIFF t = {} <=> s SUBSET t`] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?m. ~(IMAGE (ITER (n + m) cexp) v SUBSET s)`
  MP_TAC THENL
   [SUBGOAL_THEN `?z. z IN IMAGE (ITER n cexp) v` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(SPEC `z:complex` LEMMA_2b) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `x > y <=> ~(x <= y)`] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV o LAND_CONV)
      [GSYM ETA_AX] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] (GSYM ITER_ADD)] THEN ASM SET_TAC[];
    REWRITE_TAC[NOT_EXISTS_THM]] THEN
  SUBGOAL_THEN
   `!m. IMAGE (ITER (n + m) cexp) v SUBSET (w INTER h INTER s)`
  MP_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  INDUCT_TAC THENL
   [ASM_REWRITE_TAC[ADD_CLAUSES; ITER_POINTLESS; SUBSET_INTER]; ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES; SUBSET_INTER] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[ITER_POINTLESS; IMAGE_o] THEN FIRST_X_ASSUM(MATCH_MP_TAC o
      MATCH_MP (SET_RULE
        `u SUBSET w INTER h INTER s ==> (!x. x IN h /\ x IN s ==> f x IN h)
         ==> IMAGE f u SUBSET h`)) THEN
    MAP_EVERY EXPAND_TAC ["h"; "s"] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP LEMMA_2a) THEN
    MP_TAC LOG2_APPROX_32 THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN
    MP_TAC(ISPECL [`IMAGE (ITER (SUC(n + m)) cexp) v`; `s:complex->bool`]
      CONNECTED_INTER_FRONTIER) THEN
     ASM_SIMP_TAC[CONNECTED_CONTINUOUS_IMAGE; CONTINUOUS_ON_ITER_CEXP] THEN
     REWRITE_TAC[SET_RULE `s DIFF t = {} <=> s SUBSET t`] THEN
    MATCH_MP_TAC(TAUT `~p /\ r ==> (~p /\ ~q ==> ~r) ==> q`) THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ASM SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Lemma 6.                                                                  *)
(* ------------------------------------------------------------------------- *)

let LEMMA_6 = prove
 (`!v. ~(v = {}) /\ open v /\ connected v
       ==> ?n. ~(IMAGE (ITER n cexp) v INTER real = {})`,
  let lemma = prove
   (`!v. ~(v = {}) /\ open v /\ connected v /\
         (!n. IMAGE (ITER n cexp) v INTER real = {})
         ==> FINITE {n | IMAGE (ITER n cexp) v INTER
                         cball(Cx(&0),exp(&4)) = {}}`,
    REPEAT STRIP_TAC THEN MP_TAC(SPEC `v:complex->bool` LEMMA_5) THEN
    ASM_REWRITE_TAC[INFINITE] THEN DISCH_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
     `0 INSERT (IMAGE (\n. n + 1)
                      {n | IMAGE (ITER n cexp) v SUBSET {z | Re z > &4}})` THEN
    ASM_SIMP_TAC[FINITE_INSERT; FINITE_IMAGE] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_INSERT; IN_ELIM_THM] THEN
    MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC[] THEN
    X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN DISCH_TAC THEN
    DISJ2_TAC THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `n:num` THEN
    ASM_REWRITE_TAC[ADD1; IN_ELIM_THM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ITER_POINTLESS; IMAGE_o]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `IMAGE f s INTER t = {}
      ==> (!x. ~(x IN u) ==> f x IN t)
      ==> s SUBSET u`)) THEN
    REWRITE_TAC[IN_ELIM_THM; COMPLEX_IN_CBALL_0; real_gt; REAL_NOT_LT] THEN
    REWRITE_TAC[NORM_CEXP; REAL_EXP_MONO_LE]) in
  REWRITE_TAC[GSYM NOT_FORALL_THM] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `d = cball(Cx(&0),exp(&4))` THEN
  MAP_EVERY ABBREV_TAC
   [`h = {z | Re z > &4}`; `s = {z | abs(Im z) <= pi / &3}`] THEN
  SUBGOAL_THEN
   `?g r:num->num.
        g holomorphic_on v /\
        (!m n. m < n ==> r m < r n) /\
        (!x. x IN v ==> ((\n. ITER (r n) cexp x) --> g x) sequentially) /\
        (!x e. x IN v /\ &0 < e
               ==> ?d N. &0 < d /\
                         !n y. N <= n /\ y IN cball(x,d)
                               ==> norm(ITER (r n) cexp y - g x) < e)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\n. ITER n cexp`; `{ITER n cexp | n IN (:num)}`;
                   `v:complex->bool`; `Cx(&0)`; `Cx(&1)`] MONTEL_OMITTING) THEN
    ASM_REWRITE_TAC[NOT_IMP] THEN ANTS_TAC THENL
     [REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ; ARITH_EQ] THEN
      ASM_REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV; NOT_IMP] THEN
      CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      REWRITE_TAC[HOLOMORPHIC_ON_ITER_CEXP] THEN
      X_GEN_TAC `n:num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
      MATCH_MP_TAC(SET_RULE
       `P a /\ P b ==> IMAGE f s INTER P = {}
          ==> !x. x IN s ==> ~(f x = a) /\ ~(f x = b)`) THEN
      REWRITE_TAC[REAL_CX];
      ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `r:num->num` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ASM_REWRITE_TAC[]] THEN
    DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
     [MATCH_MP_TAC(TAUT `~q ==> p /\ q ==> r`) THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
      DISCH_THEN(X_CHOOSE_TAC `w:complex`) THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
      DISCH_THEN(MP_TAC o SPEC `w:complex`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN
      DISCH_THEN(MP_TAC o SPECL [`cball(w:complex,b)`; `exp(&4)`]) THEN
      ASM_REWRITE_TAC[COMPACT_CBALL; NOT_EXISTS_THM] THEN
      X_GEN_TAC `N:num` THEN MP_TAC(SPEC `ball(w:complex,b)` lemma) THEN
      ASM_REWRITE_TAC[OPEN_BALL; CONNECTED_BALL; BALL_EQ_EMPTY] THEN
      ASM_REWRITE_TAC[REAL_NOT_LE] THEN ANTS_TAC THENL
       [MP_TAC(ISPECL [`w:complex`; `b:real`] BALL_SUBSET_CBALL) THEN
        ASM SET_TAC[];
        DISCH_THEN(MP_TAC o ISPEC `\n:num. n` o
           MATCH_MP UPPER_BOUND_FINITE_SET) THEN
        REWRITE_TAC[LEFT_IMP_EXISTS_THM; FORALL_IN_GSPEC] THEN
        X_GEN_TAC `M:num` THEN DISCH_THEN(fun th ->
         DISCH_THEN(MP_TAC o SPEC `M + N + 1`) THEN
         MP_TAC(SPEC `r(M + N + 1):num` th)) THEN
        FIRST_ASSUM(ASSUME_TAC o MATCH_MP MONOTONE_BIGGER) THEN
        ASM_SIMP_TAC[ARITH_RULE
         `M + N + 1 >= N /\
          (M + N + 1 <= r(M + N + 1) ==> ~(r(M + N + 1) <= M))`] THEN
        EXPAND_TAC "d" THEN
        REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
        REWRITE_TAC[IN_BALL; IN_CBALL; CONTRAPOS_THM] THEN
        REWRITE_TAC[dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN
        REWRITE_TAC[LEFT_AND_EXISTS_THM; NOT_EXISTS_THM] THEN
        ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
        X_GEN_TAC `y:complex` THEN
        REWRITE_TAC[TAUT `~((p /\ q) /\ r) <=> p ==> q ==> ~r`] THEN
        REWRITE_TAC[FORALL_UNWIND_THM2; REAL_NOT_LE] THEN
        SIMP_TAC[REAL_LT_IMP_LE]];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:complex->complex` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY X_GEN_TAC [`w:complex`; `e:real`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(g:complex->complex) continuous at w` MP_TAC THENL
       [ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT;
                      HOLOMORPHIC_ON_IMP_CONTINUOUS_ON];
        REWRITE_TAC[continuous_at]] THEN
      DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
      DISCH_THEN(MP_TAC o SPEC `w:complex`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `min b (d / &2)` THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`cball(w:complex,b)`; `e / &2`]) THEN
      ASM_REWRITE_TAC[COMPACT_CBALL; REAL_HALF; GE; REAL_LT_MIN; IN_CBALL] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `y:complex` THEN
      REWRITE_TAC[REAL_LE_MIN] THEN DISCH_THEN(fun th ->
        STRIP_TAC THEN MP_TAC th THEN ASM_REWRITE_TAC[]) THEN
      MATCH_MP_TAC(NORM_ARITH
       `dist(y,x) < e / &2 ==> norm(z - y) < e / &2 ==> norm(z - x) < e`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      ASM_REAL_ARITH_TAC];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `w:complex`) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `w:complex`)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN
     `?k. ITER k cexp (g(w:complex)) IN h UNION ((:complex) DIFF s)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[IN_UNION; IN_DIFF; IN_UNIV; EXISTS_OR_THM] THEN
      ASM_CASES_TAC `real(g(w:complex))` THENL
       [ALL_TAC;
        DISJ2_TAC THEN EXPAND_TAC "s" THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP LEMMA_2b) THEN
        REWRITE_TAC[real_gt; REAL_NOT_LE; IN_ELIM_THM]] THEN
      DISJ1_TAC THEN EXPAND_TAC "h" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      MP_TAC(SPEC `&5 - Re(g(w:complex))` REAL_ARCH_SIMPLE) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
      MATCH_MP_TAC(REAL_ARITH
       `x + n <= y ==> &5 - x <= n ==> y > &4`) THEN
      MATCH_MP_TAC(TAUT `!p. p /\ q ==> q`) THEN
      EXISTS_TAC `real(ITER n cexp (g(w:complex)))` THEN
      SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
      ASM_REWRITE_TAC[ITER; REAL_ADD_RID; REAL_LE_REFL] THEN
      ASM_SIMP_TAC[REAL_EXP; GSYM REAL_OF_NUM_SUC] THEN
      MATCH_MP_TAC(REAL_ARITH
       `g + n <= Re x /\ &1 + Re x <= Re(cexp x)
        ==> g + n + &1 <= Re(cexp x)`) THEN
      ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[real]) THEN
      ASM_REWRITE_TAC[RE_CEXP; COS_0; REAL_MUL_RID; REAL_EXP_LE_X];
      ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[IN_UNION]) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (MESON[OPEN_CONTAINS_BALL]
     `ITER n f x IN s
      ==> open s ==> ?e. &0 < e /\ ball(ITER n f x,e) SUBSET s`)) THEN
    (ANTS_TAC THENL
      [EXPAND_TAC "h" THEN REWRITE_TAC[RE_DEF; OPEN_HALFSPACE_COMPONENT_GT] THEN
       EXPAND_TAC "s" THEN
       REWRITE_TAC[GSYM closed; IM_DEF; CLOSED_STRIP_COMPONENT_LE];
       ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`k:num`; `(:complex)`] CONTINUOUS_ON_ITER_CEXP) THEN
    REWRITE_TAC[continuous_on; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPECL [`(g:complex->complex) w`; `e:real`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `d:real`) THEN
    ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`b:real`; `N:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
    DISCH_THEN(MP_TAC o SPEC `w:complex`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THENL
     [MP_TAC(SPEC `ball(w:complex,min b c)` LEMMA_5) THEN
      ASM_REWRITE_TAC[OPEN_BALL; CONNECTED_BALL; BALL_EQ_EMPTY] THEN
      REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ALL_TAC;
        REWRITE_TAC[NOT_EXISTS_THM] THEN
        SUBGOAL_THEN `ball(w:complex,min b c) SUBSET ball(w,c)` MP_TAC THENL
         [REWRITE_TAC[SUBSET_BALLS; DIST_REFL] THEN REAL_ARITH_TAC;
          ASM SET_TAC[]]];
      MP_TAC(SPEC `ball(w:complex,min b c)` LEMMA_4) THEN
      ASM_REWRITE_TAC[OPEN_BALL; CONNECTED_BALL; BALL_EQ_EMPTY] THEN
      REWRITE_TAC[NOT_IMP] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[GSYM INFINITE]]] THEN
    (MATCH_MP_TAC INFINITE_SUPERSET THEN
      EXISTS_TAC `IMAGE (\n. r n + (k:num)) ((:num) DIFF (0..N))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC INFINITE_IMAGE THEN
        SIMP_TAC[INFINITE_DIFF_FINITE; num_INFINITE; FINITE_NUMSEG] THEN
        REWRITE_TAC[IN_UNIV; IN_NUMSEG; IN_DIFF; LE_0; NOT_LE] THEN
        MATCH_MP_TAC WLOG_LT THEN REWRITE_TAC[EQ_ADD_RCANCEL] THEN
        ASM_MESON_TAC[LT_REFL];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_ELIM_THM; IN_DIFF] THEN
        REWRITE_TAC[FORALL_IN_IMAGE; SET_RULE
         `DISJOINT s t <=> !x. x IN s ==> x IN (UNIV DIFF t)`] THEN
        X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_NUMSEG; LE_0] THEN DISCH_TAC THEN
        X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
        REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] (GSYM ITER_ADD)] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
        REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[dist] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        CONJ_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[IN_CBALL]] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IN_BALL]) THEN ASM_REAL_ARITH_TAC])]);;

(* ------------------------------------------------------------------------- *)
(* Main theorem that the iterates of the exponential do not give a           *)
(* "normal family" in the sense of Montel's theorem.                         *)
(* ------------------------------------------------------------------------- *)

let THEOREM = prove
 (`!v. open v /\ connected v /\ ~(v = {})
       ==> ?q. (!m n. m < n ==> (q:num->num) m < q n) /\
               !r. (!m n. m < n ==> r m < r n) /\
                   ((!x. x IN v
                         ==> ((\n. inv (ITER (q(r n)) cexp x)) --> Cx (&0))
                             sequentially) /\
                    (!k c.
                         compact k /\ k SUBSET v
                         ==> (?N. !n x. n >= N /\ x IN k
                                        ==> c < norm(ITER (q(r n)) cexp x))) \/
                    (?g. g holomorphic_on v /\
                         (!x. x IN v
                              ==> ((\n. ITER (q(r n)) cexp x) --> g x)
                                  sequentially) /\
                         (!k e.
                              compact k /\ k SUBSET v /\ &0 < e
                              ==> (?N. !n x.
                                           n >= N /\ x IN k
                                           ==> norm(ITER (q(r n)) cexp x - g x)
                                                < e)))) ==> F`,
  SUBGOAL_THEN
   `!v. ~(open v /\ connected v /\ bounded v /\ ~(v = {}) /\
          (!c. ?N. !n x. n >= N /\ x IN v ==> c < norm(ITER n cexp x)))`
  ASSUME_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `v:complex->bool` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `z:complex`) THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
    DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `ball(z:complex,d / &2)`) THEN
    ASM_REWRITE_TAC[OPEN_BALL; CONNECTED_BALL; BALL_EQ_EMPTY;
                    REAL_NOT_LE; REAL_HALF; BOUNDED_BALL] THEN
    ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_EXISTS_THM; NOT_IMP] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; REAL_NOT_LT] THEN
    DISCH_THEN(X_CHOOSE_TAC `c:real`) THEN
    SUBGOAL_THEN
     `?q. (!n. ?x. x IN IMAGE (ITER (q n) cexp) (ball(z,d / &2)) /\
                   norm(x) <= c) /\
          (!n. q n < q(SUC n))`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC DEPENDENT_CHOICE THEN
      REWRITE_TAC[EXISTS_IN_IMAGE] THEN
      ASM_MESON_TAC[ARITH_RULE `n >= N + 1 ==> N < n`];
      ALL_TAC] THEN
    SUBGOAL_THEN `!m n. m < n ==> (q:num->num) m < q n` ASSUME_TAC THENL
     [MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN ASM_MESON_TAC[LT_TRANS];
      ALL_TAC] THEN
    EXISTS_TAC `q:num->num` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `p:num->num` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ABBREV_TAC `r n = (q:num->num) (p(n:num))` THEN
    SUBGOAL_THEN `!m n. m < n ==> (r:num->num) m < r n` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!n:num. ?x. x IN IMAGE (ITER (r n) cexp) (ball(z,d / &2)) /\ norm x <= c`
    MP_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[EXISTS_IN_IMAGE]] THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check is_forall o concl)) THEN
    REPEAT STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`cball(z:complex,d / &2)`; `c:real`]) THEN
      REWRITE_TAC[COMPACT_CBALL; NOT_IMP] THEN CONJ_TAC THENL
       [TRANS_TAC SUBSET_TRANS `ball(z:complex,d)` THEN
        ASM_REWRITE_TAC[SUBSET_BALLS; DIST_REFL] THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN(X_CHOOSE_THEN `n:num` (MP_TAC o SPEC `n:num`)) THEN
        REWRITE_TAC[GE; LE_REFL; GSYM REAL_NOT_LE] THEN
        ASM_MESON_TAC[REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL]];
      MP_TAC(SPEC `v:complex->bool` LEMMA_6) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      REWRITE_TAC[SET_RULE `P /\ x IN real <=> real x /\ P`] THEN
      REWRITE_TAC[EXISTS_REAL; IN_IMAGE] THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `x:real`; `w:complex`] THEN
      DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `w:complex`) THEN
      ASM_REWRITE_TAC[LIM_SEQUENTIALLY] THEN
      DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
      DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "*")) THEN
      MP_TAC(SPEC `Re(g(w:complex)) + &1 - x` REAL_ARCH_SIMPLE) THEN
      DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
      REMOVE_THEN "*" (MP_TAC o SPEC `N + M + n:num`) THEN
      REWRITE_TAC[LE_ADD; dist] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (MESON[COMPONENT_LE_NORM; REAL_LET_TRANS]
       `norm(x) < &1 ==> abs(x$1) < &1`)) THEN
      REWRITE_TAC[GSYM RE_DEF; RE_SUB; REAL_NOT_LT] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
       `g + &1 - x <= m ==> m + x <= f ==> &1 <= abs(f - g)`)) THEN
      TRANS_TAC REAL_LE_TRANS `(&N + &M) + x:real` THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; REWRITE_TAC[REAL_OF_NUM_ADD; ADD_ASSOC]] THEN
      SPEC_TAC(`N + M:num`,`m:num`) THEN GEN_TAC THEN
      SUBGOAL_THEN `m + n <= (r:num->num) (m + n)` MP_TAC THENL
       [ASM_MESON_TAC[MONOTONE_BIGGER]; REWRITE_TAC[LE_EXISTS]] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
      TRANS_TAC REAL_LE_TRANS `(&m + &d) + x:real` THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; REWRITE_TAC[REAL_OF_NUM_ADD; ADD_ASSOC]] THEN
      ONCE_REWRITE_TAC[ARITH_RULE `(m + n) + d:num = n + (m + d)`] THEN
      SPEC_TAC(`m + d:num`,`d:num`) THEN
      SUBGOAL_THEN
       `!d. real(ITER (n + d) cexp w) /\
            &d + x <= Re(ITER (n + d) cexp w)`
       (fun th -> MESON_TAC[th]) THEN
      INDUCT_TAC THEN
      ASM_SIMP_TAC[ADD_CLAUSES; ITER; REAL_CX; RE_CX; REAL_ADD_LID;
                   REAL_LE_REFL; REAL_EXP; RE_CEXP] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[real]) THEN
      ASM_REWRITE_TAC[COS_0; GSYM REAL_OF_NUM_SUC] THEN
      MATCH_MP_TAC(REAL_ARITH
       `d + y <= x /\ &1 + x <= exp x ==> (d + &1) + y <= exp(x) * &1`) THEN
      ASM_REWRITE_TAC[REAL_EXP_LE_X]]] THEN
  REPEAT STRIP_TAC THEN
  MAP_EVERY ABBREV_TAC
   [`h = {z | Re z > &4}`;
    `s = {z | abs(Im z) <= pi / &3}`;
    `w = {z | abs(Im z) <= &2 * pi /\ abs(Im(cexp z)) <= &2 * pi}`] THEN
  SUBGOAL_THEN
   `FINITE {n | ~(IMAGE (ITER n cexp) v SUBSET h)}`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `exp(&4)`) THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..N` THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; IN_ELIM_THM; LE_0] THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[NOT_LE] THEN DISCH_TAC THEN
    X_GEN_TAC `w:complex` THEN DISCH_TAC THEN EXPAND_TAC "h" THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n + 1`; `w:complex`]) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_SIMP_TAC[ARITH_RULE `N < n ==> SUC n >= N`; GSYM ADD1] THEN
    REWRITE_TAC[real_gt; ITER; NORM_CEXP; REAL_EXP_MONO_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `FINITE {n | DISJOINT (IMAGE (ITER n cexp) v) real}`
  ASSUME_TAC THENL
   [MP_TAC(SPEC `v:complex->bool` LEMMA_6) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "*")) THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..N` THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; LE_0; IN_ELIM_THM] THEN
    MATCH_MP_TAC(MESON[ARITH_RULE `~(n:num <= N) ==> n = N + (n - N)`]
     `(!d:num. ~P (N + d)) ==> (!n. P n ==> n <= N)`) THEN
    REWRITE_TAC[DISJOINT] THEN MATCH_MP_TAC num_INDUCTION THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; ITER_POINTLESS] THEN X_GEN_TAC `d:num` THEN
    REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC(SET_RULE
     `(!x. real x ==> real(cexp x))
      ==> ~(s INTER real = {}) ==> ~(IMAGE cexp s INTER real = {})`) THEN
    REWRITE_TAC[REAL_EXP];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `INFINITE {n | IMAGE (ITER n cexp) v SUBSET h /\
                   ~(DISJOINT (IMAGE (ITER n cexp) v) real) /\
                   ~(IMAGE (ITER n cexp) v SUBSET s)}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE
     `{x | P x /\ Q x /\ R x} =
      {x | R x} DIFF ({x | ~P x} UNION {x | ~Q x})`] THEN
    MATCH_MP_TAC INFINITE_DIFF_FINITE THEN
    ASM_REWRITE_TAC[FINITE_UNION; INFINITE] THEN
    DISCH_THEN(MP_TAC o ISPEC `\n:num. n` o
      MATCH_MP UPPER_BOUND_FINITE_SET) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `N:num` THEN
    SUBGOAL_THEN `?z. z IN IMAGE (ITER (N + 1) cexp) v /\ ~(real z)`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE `~(s SUBSET t) ==> ?z. z IN s /\ ~t z`) THEN
      DISCH_THEN(MP_TAC o MATCH_MP SUBSET_INTERIOR) THEN
      REWRITE_TAC[INTERIOR_REAL] THEN MATCH_MP_TAC(SET_RULE
       `interior(IMAGE f s) = IMAGE f s /\ ~(s = {})
        ==> ~(interior(IMAGE f s) SUBSET {})`) THEN
      ASM_REWRITE_TAC[INTERIOR_EQ] THEN
      SPEC_TAC(`N + 1`,`n:num`) THEN
      INDUCT_TAC THEN ASM_REWRITE_TAC[ITER_POINTLESS; IMAGE_I; IMAGE_o] THEN
      MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
         OPEN_MAPPING_THM) THEN
      EXISTS_TAC `IMAGE (ITER n cexp) v` THEN
      ASM_REWRITE_TAC[SUBSET_REFL; HOLOMORPHIC_ON_CEXP] THEN
      ASM_SIMP_TAC[CONNECTED_CONTINUOUS_IMAGE; CONTINUOUS_ON_ITER_CEXP] THEN
      DISCH_THEN(X_CHOOSE_TAC `c:complex`) THEN
      SUBGOAL_THEN `?x. x IN IMAGE (ITER n cexp) v` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPEC `x:complex` CEXP_NZ) THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC COMPLEX_DERIVATIVE_UNIQUE_AT THEN
      MAP_EVERY EXISTS_TAC [`cexp`; `x:complex`] THEN
      REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_CEXP] THEN
      MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
      MAP_EVERY EXISTS_TAC
       [`(\z. c):complex->complex`; `IMAGE (ITER n cexp) v`] THEN
      ASM_REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_CONST] THEN ASM_MESON_TAC[];
      FIRST_X_ASSUM(MP_TAC o MATCH_MP LEMMA_2b) THEN
      EXPAND_TAC "s" THEN REWRITE_TAC[real_gt; IN_ELIM_THM; SUBSET] THEN
      DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
      DISCH_THEN(MP_TAC o SPEC `n + N + 1:num`) THEN REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[ITER_ADD_POINTLESS] THEN
      SIMP_TAC[ARITH_RULE `~(n + N + 1 <= N)`; IMAGE_o; GSYM REAL_NOT_LT] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `INFINITE {n | ~(IMAGE (ITER n cexp) v SUBSET w)}`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        INFINITE_SUPERSET)) THEN
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`IMAGE (ITER n cexp) v`; `s:complex->bool`]
        CONNECTED_INTER_FRONTIER) THEN
    ASM_SIMP_TAC[CONNECTED_CONTINUOUS_IMAGE; CONTINUOUS_ON_ITER_CEXP] THEN
    REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `~(DISJOINT s real) ==> {x | real x} SUBSET t
        ==> ~(s INTER t = {})`)) THEN
      EXPAND_TAC "s" THEN SIMP_TAC[real; IN_ELIM_THM; SUBSET] THEN
      MP_TAC PI_POS THEN REAL_ARITH_TAC;
      ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `DISJOINT (frontier s) (w INTER h:complex->bool)`
    ASSUME_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    EXPAND_TAC "s" THEN
    REWRITE_TAC[IM_DEF; FRONTIER_STRIP_COMPONENT_LE] THEN
    REWRITE_TAC[GSYM IM_DEF] THEN MATCH_MP_TAC(SET_RULE
     `(!x. x IN s /\ x IN u ==> ~(x IN t)) ==> DISJOINT s (t INTER u)`) THEN
    MAP_EVERY EXPAND_TAC ["h"; "w"] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `z:complex` THEN REWRITE_TAC[IM_CEXP; real_gt] THEN
    STRIP_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[REAL_NOT_LE; REAL_ABS_MUL; REAL_ABS_EXP] THEN
    SUBGOAL_THEN `abs(sin(Im z)) = sqrt(&3) / &2` SUBST1_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o MATCH_MP (REAL_ARITH
       `abs x = a ==> x = a \/ x = --a`)) THEN
      REWRITE_TAC[SIN_NEG; SIN_PI3; REAL_ABS_NEG] THEN
      SIMP_TAC[REAL_ABS_REFL; REAL_LE_DIV; SQRT_POS_LE; REAL_POS];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
      `pi < &4 /\ &2 pow 4 <= x * y ==> &2 * pi < x * y / &2`) THEN
    CONJ_TAC THENL [MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= x /\ x * &1 <= x * s ==> a <= x * s`) THEN
    CONJ_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `exp(&4 * &1)` THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_EXP_N] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
        MP_TAC E_APPROX_32 THEN REAL_ARITH_TAC;
        REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      SUBST1_TAC(SYM SQRT_1) THEN MATCH_MP_TAC SQRT_MONO_LE THEN
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `INFINITE {n | ~(IMAGE (ITER n cexp) v SUBSET {z | abs(Im z) <= &2 * pi}) /\
                  ~DISJOINT (IMAGE (ITER n cexp) v) real}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE `{x | P x /\ ~Q x} = {x | P x} DIFF {x | Q x}`] THEN
    MATCH_MP_TAC INFINITE_DIFF_FINITE THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `INFINITE {n | ~(IMAGE (ITER n cexp) v SUBSET w)}` THEN
    REWRITE_TAC[INFINITE; CONTRAPOS_THM] THEN
    EXPAND_TAC "w" THEN
    REWRITE_TAC[SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`;
                SUBSET_INTER; FINITE_SUBSET_NUMSEG] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
    ONCE_REWRITE_TAC[SUBSET] THEN REWRITE_TAC[IN_NUMSEG; LE_0] THEN
    REWRITE_TAC[IN_ELIM_THM; CONTRAPOS_THM; GSYM NOT_LT] THEN
    DISCH_THEN(fun th -> X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      MP_TAC(SPEC `k:num` th) THEN MP_TAC(SPEC `SUC k` th)) THEN
    ASM_SIMP_TAC[LT_SUC_LE; LT_IMP_LE; ITER_POINTLESS] THEN
    REWRITE_TAC[IMAGE_o] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `INFINITE {n | ~(IMAGE (ITER n cexp) v INTER {x | abs(Im x) = pi} = {})}`
  MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      INFINITE_SUPERSET)) THEN
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; SUBSET; DISJOINT; IN_ELIM_THM] THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; IN_INTER; REAL_NOT_LE; real;
                IN_ELIM_THM; SET_RULE `x IN real <=> real x`] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `b:complex` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `a:complex` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL
     [`IMAGE (lift o abs o Im) (IMAGE (ITER n cexp) v)`;
      `(lift o abs o Im) a`; `(lift o abs o Im) b`;
      `pi`; `1`] CONNECTED_IVT_COMPONENT) THEN
    ASM_SIMP_TAC[DIMINDEX_1; LE_REFL; FUN_IN_IMAGE] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [EXISTS_IN_IMAGE] THEN
    REWRITE_TAC[GSYM drop; o_THM; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL [ALL_TAC; MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[CONNECTED_CONTINUOUS_IMAGE; CONTINUOUS_ON_ITER_CEXP] THEN
    REWRITE_TAC[o_DEF; IM_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_ABS_COMPONENT THEN
    REWRITE_TAC[CONTINUOUS_ON_ID];
    REWRITE_TAC[INFINITE]] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[FINITE_SUBSET_NUMSEG] THEN
  REWRITE_TAC[SUBSET; GE; IN_NUMSEG; LE_0; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  REWRITE_TAC[GSYM NOT_LT; CONTRAPOS_THM] THEN
  REWRITE_TAC[IN_ELIM_THM; NOT_LT;
    SET_RULE `IMAGE f s INTER t = {} <=> !x. x IN s ==> ~(f x IN t)`] THEN
  DISCH_THEN(fun th ->
   X_GEN_TAC `n:num` THEN DISCH_TAC THEN X_GEN_TAC `x:complex` THEN
   DISCH_TAC THEN MP_TAC(ISPECL [`SUC(SUC n)`; `x:complex`] th)) THEN
  ASM_SIMP_TAC[ARITH_RULE `N < n ==> N <= SUC(SUC n)`; GSYM REAL_NOT_LE;
               CONTRAPOS_THM] THEN
  SIMP_TAC[ITER; NORM_CEXP; RE_CEXP] THEN
  ONCE_REWRITE_TAC[GSYM COS_ABS] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[COS_PI; GSYM REAL_EXP_0; REAL_EXP_MONO_LE] THEN
  REWRITE_TAC[REAL_EXP_0; REAL_ARITH `x * -- &1 <= &0 <=> &0 <= x`] THEN
  REWRITE_TAC[REAL_EXP_POS_LE]);;

(* ------------------------------------------------------------------------- *)
(* Hence a strong form of topological transitivity.                          *)
(* ------------------------------------------------------------------------- *)

let STRONG = prove
 (`!u a. open u /\ ~(u = {}) /\ ~(a = Cx(&0))
         ==> ?n. a IN IMAGE (ITER n cexp) u`,
  SUBGOAL_THEN
   `!v a. open v /\ ~(v = {}) /\ connected v /\ ~(Cx(&0) IN v) /\ ~(a = Cx(&0))
         ==> ?n. a IN IMAGE (ITER n cexp) v`
  ASSUME_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `~(u SUBSET {Cx(&0),a})` MP_TAC THENL
     [DISCH_THEN(MP_TAC o MATCH_MP
        (REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET)) THEN
      REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
      ASM_MESON_TAC[FINITE_IMP_NOT_OPEN];
      REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY; NOT_FORALL_THM;
                  NOT_IMP; DE_MORGAN_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `b:complex` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
      DISCH_THEN(MP_TAC o SPEC `b:complex`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`ball(b:complex,min r (min (norm b) (dist(b,a))))`; `a:complex`]) THEN
      ASM_REWRITE_TAC[OPEN_BALL; CONNECTED_BALL; BALL_EQ_EMPTY] THEN
      ASM_REWRITE_TAC[REAL_NOT_LE; REAL_LT_MIN; GSYM DIST_NZ;
                      COMPLEX_NORM_NZ] THEN
      REWRITE_TAC[IN_BALL; dist; COMPLEX_SUB_RZERO] THEN
      ANTS_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC MONO_EXISTS] THEN
      GEN_TAC THEN MATCH_MP_TAC(SET_RULE
       `s SUBSET t ==> a IN IMAGE f s ==> a IN IMAGE f t`) THEN
      TRANS_TAC SUBSET_TRANS `ball(b:complex,r)` THEN
      ASM_REWRITE_TAC[SUBSET_BALLS; DIST_REFL] THEN REAL_ARITH_TAC]] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(MESON[] `((!x. ~P x) ==> F) ==> ?x. P x`) THEN
  DISCH_TAC THEN MP_TAC(SPEC `v:complex->bool` THEOREM) THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `q:num->num` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MP_TAC(ISPECL [`\n:num. ITER (q n) cexp`; `{ITER n cexp | n IN (:num)}`;
            `v:complex->bool`; `Cx(&0)`; `a:complex`] MONTEL_OMITTING) THEN
  ASM_REWRITE_TAC[NOT_IMP; NOT_FORALL_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL [REWRITE_TAC[FORALL_IN_GSPEC]; SET_TAC[]] THEN
  REWRITE_TAC[IN_UNIV; HOLOMORPHIC_ON_ITER_CEXP] THEN
  REWRITE_TAC[TAUT `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  INDUCT_TAC THEN REWRITE_TAC[ITER; CEXP_NZ] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The usual formulation.                                                    *)
(* ------------------------------------------------------------------------- *)

let COROLLARY = prove
 (`!u v. open u /\ ~(u = {}) /\ open v /\ ~(v = {})
         ==> ?n. ~(IMAGE (ITER n cexp) u INTER v = {})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(v SUBSET {Cx(&0)})` MP_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP
      (REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET)) THEN
    REWRITE_TAC[FINITE_SING] THEN ASM_MESON_TAC[FINITE_IMP_NOT_OPEN];
    DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
     `~(s SUBSET {z}) ==> ?a. a IN s /\ ~(a = z)`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `b:complex` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`u:complex->bool`; `b:complex`]
        STRONG) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;
