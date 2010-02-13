(* ========================================================================= *)
(* Borsuk-Ulam theorem for an ordinary 2-sphere in real^3.                   *)
(* From Andrew Browder's article, AMM vol. 113 (2006), pp. 935-6             *)
(* ========================================================================= *)

needs "Multivariate/realanalysis.ml";;

(* ------------------------------------------------------------------------- *)
(* Lemmas about choosing a continuous logarithm.                             *)
(* ------------------------------------------------------------------------- *)

let LEMMA_1 = prove
 (`!f g:real^N->complex s.
        f continuous_on s /\ g continuous_on s /\
        (!x. x IN s ==> norm(g x) < norm(f x))
        ==> ?h. h continuous_on s /\
                (!x. x IN s ==> f(x) + g(x) = f(x) * cexp(h x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^N. x IN s ==> ~(f x = Cx(&0))` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN NORM_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `\x:real^N. clog(Cx(&1) + g(x) / f(x))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CONST;
                 CONTINUOUS_ON_COMPLEX_DIV] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CLOG THEN
    REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; RE_ADD; IM_ADD;
                IM_CX; RE_CX; REAL_ADD_LID] THEN
    REWRITE_TAC[GSYM real] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `abs(x) < &1 ==> &0 < &1 + x`) THEN
    ASM_SIMP_TAC[GSYM REAL_NORM; COMPLEX_NORM_DIV; REAL_LT_LDIV_EQ;
                 COMPLEX_NORM_NZ; REAL_MUL_LID];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[COMPLEX_FIELD
     `~(z = Cx(&0)) ==> (z + w = z * u <=> u = Cx(&1) + w / z)`] THEN
    MATCH_MP_TAC CEXP_CLOG THEN REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
    MATCH_MP_TAC(NORM_ARITH `norm(a) < norm(b) ==> ~(b + a = vec 0)`) THEN
    ASM_SIMP_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_MUL_LID;
                 REAL_LT_LDIV_EQ; COMPLEX_NORM_NZ; REAL_ABS_NUM]]);;

let PROPOSITION_1 = prove
 (`!f. f continuous_on cball(Cx(&0),&1) /\
       (!z. z IN cball(Cx(&0),&1) ==> ~(f z = Cx(&0)))
       ==> ?h. h continuous_on cball(Cx(&0),&1) /\
               !z. z IN cball(Cx(&0),&1) ==> f z = cexp(h z)`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `?e. &0 < e /\ !z. z IN cball(Cx(&0),&1) ==> e <= norm(f z:complex)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (f:complex->complex) (cball(Cx(&0),&1))`;
                   `Cx(&0)`] DISTANCE_ATTAINS_INF) THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY; CBALL_EQ_EMPTY; REAL_OF_NUM_LT; ARITH] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[COMPACT_IMP_CLOSED; COMPACT_CBALL;
                    COMPACT_CONTINUOUS_IMAGE];
      REWRITE_TAC[dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN
      ASM_MESON_TAC[COMPLEX_NORM_NZ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:complex->complex) uniformly_continuous_on cball(Cx(&0),&1)`
  MP_TAC THENL
   [ASM_SIMP_TAC[COMPACT_UNIFORMLY_CONTINUOUS; COMPACT_CBALL]; ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `d:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `g = \k z. (f:complex->complex)(Cx(&k / &n) * z)` THEN
  SUBGOAL_THEN
   `!k:num. k <= n ==> ?h. h continuous_on cball(Cx(&0),&1) /\
                           !z. z IN cball(Cx(&0),&1) ==> g k z = cexp(h z)`
  (MP_TAC o SPEC `n:num`) THENL
   [ALL_TAC;
    EXPAND_TAC "g" THEN REWRITE_TAC[LE_REFL] THEN
    ASM_SIMP_TAC[REAL_DIV_REFL; REAL_OF_NUM_EQ; COMPLEX_MUL_LID]] THEN
  INDUCT_TAC THENL
   [DISCH_TAC THEN EXPAND_TAC "g" THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; COMPLEX_MUL_LZERO] THEN
    EXISTS_TAC `\z:complex. clog(f(Cx(&0)))` THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_CONST; CEXP_CLOG; CENTRE_IN_CBALL; REAL_POS];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`(g:num->complex->complex) k`;
                 `\z. (g:num->complex->complex) (SUC k) z - g k z`;
                 `cball(Cx(&0),&1)`] LEMMA_1) THEN
  SUBGOAL_THEN
   `!j z. j <= n /\ z IN cball(Cx(&0),&1)
          ==> (Cx(&j / &n) * z) IN cball(Cx(&0),&1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_CBALL; GSYM COMPLEX_VEC_0; COMPLEX_NORM_MUL;
                NORM_ARITH `dist(vec 0,x) = norm x`] THEN
    REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
    REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_DIV; REAL_ABS_NUM] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
    ASM_REWRITE_TAC[REAL_MUL_LID; REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j <= n ==> (g:num->complex->complex) j continuous_on cball(Cx(&0),&1)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "g" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN
    SIMP_TAC[CONTINUOUS_ON_COMPLEX_MUL; CONTINUOUS_ON_ID;
             CONTINUOUS_ON_CONST] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
    ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_SUB; ARITH_RULE `SUC k <= n ==> k <= n`;
               ETA_AX] THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `e:real` THEN
    EXPAND_TAC "g" THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ARITH_RULE `SUC k <= n ==> k <= n`] THEN
    REWRITE_TAC[GSYM dist] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `SUC k <= n ==> k <= n`] THEN
    REWRITE_TAC[dist; GSYM CX_SUB; COMPLEX_NORM_CX; COMPLEX_NORM_MUL;
                GSYM COMPLEX_SUB_RDISTRIB; GSYM REAL_OF_NUM_SUC] THEN
    REWRITE_TAC[REAL_ARITH `(x + &1) / n - x / n = inv(n)`] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NUM; GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&1` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_CBALL]) THEN
      REWRITE_TAC[dist; COMPLEX_SUB_LZERO; NORM_NEG];
      ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
      ASM_REWRITE_TAC[real_div; REAL_MUL_LID]];
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_RING `x + y - x:complex = y`] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_SIMP_TAC[ARITH_RULE `SUC k <= n ==> k <= n`] THEN
  DISCH_THEN(X_CHOOSE_THEN `h1:complex->complex` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `h2:complex->complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\z. (h1:complex->complex) z + h2 z` THEN
  ASM_SIMP_TAC[CEXP_ADD; CONTINUOUS_ON_ADD; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* The Borsuk-Ulam theorem for the unit sphere.                              *)
(* ------------------------------------------------------------------------- *)

let THEOREM_1 = prove
 (`!f:real^3->real^2.
        f continuous_on {x | norm(x) = &1}
        ==> ?x. norm(x) = &1 /\ f(--x) = f(x)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [TAUT `p <=> ~ ~ p`] THEN
  PURE_REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`] THEN
  DISCH_TAC THEN
  ABBREV_TAC `(g:real^3->real^2) = \x. f(x) - f(--x)` THEN
  ABBREV_TAC `k = \z. (g:real^3->real^2)
                      (vector[Re z; Im z; sqrt(&1 - norm z pow 2)])` THEN
  MP_TAC(SPEC `k:complex->complex` PROPOSITION_1) THEN
  MATCH_MP_TAC(TAUT `a /\ (a /\ b ==> c) ==> (a ==> b) ==> c`) THEN
  CONJ_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "k" THEN
      MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
                    CONTINUOUS_COMPONENTWISE] THEN
        SIMP_TAC[DIMINDEX_3; FORALL_3; VECTOR_3; ETA_AX] THEN
        REWRITE_TAC[REAL_CONTINUOUS_COMPLEX_COMPONENTS_WITHIN] THEN
        X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
        MATCH_MP_TAC(REWRITE_RULE[o_DEF] REAL_CONTINUOUS_WITHIN_COMPOSE) THEN
        SIMP_TAC[REAL_CONTINUOUS_SUB; REAL_CONTINUOUS_POW;
                 REAL_CONTINUOUS_CONST; REAL_CONTINUOUS_NORM_WITHIN] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_WITHINREAL_SUBSET THEN
        EXISTS_TAC `{t | &0 <= t}` THEN
        REWRITE_TAC[REAL_CONTINUOUS_WITHIN_SQRT_STRONG] THEN
        SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_CBALL; IN_ELIM_THM; dist;
                 COMPLEX_SUB_LZERO; NORM_NEG; REAL_SUB_LE] THEN
        REWRITE_TAC[ABS_SQUARE_LE_1; REAL_ABS_NORM];
        ALL_TAC] THEN
      EXPAND_TAC "g" THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[linear] THEN
          CONJ_TAC THEN VECTOR_ARITH_TAC;
          REWRITE_TAC[GSYM IMAGE_o]]] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `{x:real^3 | norm x = &1}` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM; IN_ELIM_THM] THEN
      SIMP_TAC[NORM_EQ_1; DOT_3; VECTOR_3; VECTOR_NEG_COMPONENT; dist;
               DIMINDEX_3; ARITH; IN_CBALL; COMPLEX_SUB_LZERO; NORM_NEG] THEN
      REWRITE_TAC[REAL_NEG_MUL2] THEN X_GEN_TAC `z:complex` THEN DISCH_TAC;
      X_GEN_TAC `z:complex` THEN
      REWRITE_TAC[dist; IN_CBALL; COMPLEX_SUB_LZERO; NORM_NEG] THEN
      DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["k"; "g"] THEN
      REWRITE_TAC[COMPLEX_RING `x - y = Cx(&0) <=> y = x`] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[NORM_EQ_1; DOT_3; VECTOR_3]] THEN
    REWRITE_TAC[GSYM REAL_POW_2; COMPLEX_SQNORM] THEN
    REWRITE_TAC[REAL_ARITH `r + i + s = &1 <=> s = &1 - (r + i)`] THEN
    MATCH_MP_TAC SQRT_POW_2 THEN REWRITE_TAC[GSYM COMPLEX_SQNORM] THEN
    ASM_SIMP_TAC[REAL_SUB_LE; ABS_SQUARE_LE_1; REAL_ABS_NORM];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `h:complex->complex` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `m = \z:complex. (h(z) - h(--z)) / (Cx pi * ii)` THEN
  SUBGOAL_THEN
    `!z:complex. norm(z) = &1 ==> cexp(Cx pi * ii * m z) = cexp(Cx pi * ii)`
  MP_TAC THENL
   [EXPAND_TAC "m" THEN
    REWRITE_TAC[COMPLEX_SUB_LDISTRIB; complex_div; COMPLEX_SUB_RDISTRIB] THEN
    SIMP_TAC[CX_INJ; PI_NZ; CEXP_SUB; COMPLEX_FIELD
     `~(p = Cx(&0)) ==> p * ii * h * inv(p * ii) = h`] THEN
    X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `cexp(h z) = k z /\ cexp(h(--z:complex)) = k(--z)`
     (CONJUNCTS_THEN SUBST1_TAC)
    THENL
     [CONJ_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[dist; IN_CBALL; COMPLEX_SUB_LZERO; NORM_NEG; REAL_LE_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[EULER; RE_MUL_CX; IM_MUL_CX; RE_II; IM_II; COMPLEX_ADD_RID;
                REAL_MUL_RZERO; REAL_MUL_RID; SIN_PI; COS_PI; REAL_EXP_0;
                COMPLEX_MUL_RZERO; COMPLEX_MUL_LID] THEN
    MATCH_MP_TAC(COMPLEX_FIELD
     `~(y = Cx(&0)) /\ x = -- y ==> x / y = Cx(-- &1)`) THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[dist; IN_CBALL; COMPLEX_SUB_LZERO; NORM_NEG; REAL_LE_REFL];
      MAP_EVERY EXPAND_TAC ["k"; "g"] THEN
      REWRITE_TAC[COMPLEX_NEG_SUB] THEN BINOP_TAC THEN AP_TERM_TAC THEN
      SIMP_TAC[CART_EQ; FORALL_3; VECTOR_3; VECTOR_NEG_COMPONENT;
               DIMINDEX_3; ARITH; RE_NEG; IM_NEG; NORM_NEG; REAL_NEG_NEG] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[SQRT_0; REAL_NEG_0]];
    ALL_TAC] THEN
  REWRITE_TAC[CEXP_EQ; CX_MUL] THEN
  SIMP_TAC[CX_INJ; PI_NZ; COMPLEX_FIELD
   `~(p = Cx(&0))
    ==> (p * ii * m = p * ii + (t * n * p) * ii <=> m = t * n + Cx(&1))`] THEN
  REWRITE_TAC[GSYM CX_ADD; GSYM CX_MUL] THEN DISCH_THEN(LABEL_TAC "*") THEN
  SUBGOAL_THEN
   `?n. !z. z IN {z | norm(z) = &1} ==> (m:complex->complex)(z) = n`
  MP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_DISCRETE_RANGE_CONSTANT THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[NORM_ARITH `norm z = norm(z - vec 0)`] THEN
      SIMP_TAC[CONNECTED_SPHERE; DIMINDEX_2; LE_REFL];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "m" THEN MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_DIV THEN
      SIMP_TAC[CONTINUOUS_ON_CONST; COMPLEX_ENTIRE; II_NZ; CX_INJ; PI_NZ] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[linear] THEN
          CONJ_TAC THEN VECTOR_ARITH_TAC;
          REWRITE_TAC[GSYM IMAGE_o]]] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
       (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
      SIMP_TAC[SUBSET; FORALL_IN_IMAGE; NORM_NEG; IN_CBALL;
               COMPLEX_SUB_LZERO; dist; IN_ELIM_THM; REAL_LE_REFL];
      ALL_TAC] THEN
    X_GEN_TAC `z:complex` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_TAC THEN EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
    X_GEN_TAC `w:complex` THEN STRIP_TAC THEN
    REMOVE_THEN "*" (fun th -> MP_TAC(SPEC `w:complex` th) THEN
                               MP_TAC(SPEC `z:complex` th)) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(DISCH_THEN(CHOOSE_THEN
     (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THEN
    REWRITE_TAC[GSYM CX_SUB; COMPLEX_NORM_CX] THEN
    MATCH_MP_TAC(REAL_ARITH
     `~(abs(x - y) < &1) ==> &1 <= abs((&2 * x + &1) - (&2 * y + &1))`) THEN
    ASM_SIMP_TAC[GSYM REAL_EQ_INTEGERS] THEN ASM_MESON_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `v:complex`)] THEN
  SUBGOAL_THEN
    `?n. integer n /\ !z:complex. norm z = &1 ==> m z = Cx(&2 * n + &1)`
  MP_TAC THENL
   [REMOVE_THEN "*" (MP_TAC o SPEC `Cx(&1)`) THEN
    ASM_SIMP_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real` MP_TAC) THEN EXPAND_TAC "m" THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `--Cx(&1)` th) THEN
                        MP_TAC(SPEC `Cx(&1)` th)) THEN
  REWRITE_TAC[NORM_NEG; COMPLEX_NORM_CX; REAL_ABS_NUM; COMPLEX_NEG_NEG] THEN
  REWRITE_TAC[complex_div; COMPLEX_SUB_RDISTRIB] THEN
  MATCH_MP_TAC(COMPLEX_RING
   `~(z = Cx(&0)) ==> a - b = z ==> ~(b - a = z)`) THEN
  REWRITE_TAC[CX_INJ; REAL_ARITH `&2 * n + &1 = &0 <=> n = --(&1 / &2)`] THEN
  UNDISCH_TAC `integer n` THEN GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
  SIMP_TAC[] THEN DISCH_TAC THEN REWRITE_TAC[integer] THEN
  REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_DIV; REAL_ABS_NUM] THEN
  REWRITE_TAC[REAL_ARITH `a / &2 = n <=> a = &2 * n`] THEN
  REWRITE_TAC[NOT_EXISTS_THM; REAL_OF_NUM_MUL; REAL_OF_NUM_EQ] THEN
  GEN_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN
  REWRITE_TAC[EVEN_MULT; ARITH]);;

(* ------------------------------------------------------------------------- *)
(* The Borsuk-Ulam theorem for a general sphere.                             *)
(* ------------------------------------------------------------------------- *)

let BORSUK_ULAM = prove
 (`!f:real^3->real^2 a r.
        &0 <= r /\ f continuous_on {z | norm(z - a) = r}
        ==> ?x. norm(x) = r /\ f(a + x) = f(a - x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `\x. (f:real^3->real^2) (a + r % x)` THEOREM_1) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN
    SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CONST;
             CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM];
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r % x:real^3` THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `a - r % x:real^3 = a + r % --x`]] THEN
  ASM_SIMP_TAC[VECTOR_ADD_SUB; NORM_MUL] THEN ASM_REAL_ARITH_TAC);;
