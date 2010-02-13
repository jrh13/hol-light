(* ========================================================================= *)
(* Minkowski's convex body theorem.                                          *)
(* ========================================================================= *)

needs "Multivariate/measure.ml";;

(* ------------------------------------------------------------------------- *)
(* An ad hoc lemma.                                                          *)
(* ------------------------------------------------------------------------- *)

let LEMMA = prove
 (`!f:real^N->bool t s:real^N->bool.
        FINITE { u | u IN f /\ ~(t u = {})} /\
        measurable s /\ &1 < measure s /\
        (!u. u IN f ==> measurable(t u)) /\
        s SUBSET UNIONS (IMAGE t f) /\
        (!u v. u IN f /\ v IN f /\ ~(u = v) ==> DISJOINT (t u) (t v)) /\
        (!u. u IN f ==> (IMAGE (\x. x - u) (t u)) SUBSET interval[vec 0,vec 1])
        ==> ?u v. u IN f /\ v IN f /\ ~(u = v) /\
                  ~(DISJOINT (IMAGE (\x. x - u) (t u))
                             (IMAGE (\x. x - v) (t v)))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN
  PURE_REWRITE_TAC[NOT_EXISTS_THM] THEN
  REWRITE_TAC[TAUT `~(a /\ b /\ ~c /\ ~d) <=> a /\ b /\ ~c ==> d`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`\u:real^N. IMAGE (\x:real^N. x - u) (t u)`;
                 `f:real^N->bool`]
                HAS_MEASURE_DISJOINT_UNIONS_IMAGE_STRONG) THEN
  ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; NOT_IMP] THEN CONJ_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH `x - u:real^N = --u + x`] THEN
    ASM_REWRITE_TAC[MEASURABLE_TRANSLATION_EQ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`vec 0:real^N`; `vec 1:real^N`] (CONJUNCT1
                HAS_MEASURE_INTERVAL)) THEN
  REWRITE_TAC[CONTENT_UNIT] THEN
  MATCH_MP_TAC(TAUT `(b /\ a ==> F) ==> a ==> ~b`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE
   [TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`] HAS_MEASURE_SUBSET)) THEN
  ASM_REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE; REAL_NOT_LE] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `&1 < a ==> a <= b ==> &1 < b`)) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `measure(UNIONS (IMAGE (t:real^N->real^N->bool) f))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MEASURE_SUBSET THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `UNIONS (IMAGE (t:real^N->real^N->bool) f) =
      UNIONS (IMAGE t {u | u IN f /\ ~(t u = {})})`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN
      REWRITE_TAC[IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN
      MESON_TAC[NOT_IN_EMPTY];
      ALL_TAC] THEN
    MATCH_MP_TAC MEASURABLE_UNIONS THEN
    ASM_REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[FINITE_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^N->real^N->bool`; `f:real^N->bool`]
                HAS_MEASURE_DISJOINT_UNIONS_IMAGE_STRONG) THEN
  ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; NOT_IMP] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP MEASURE_UNIQUE) THEN
  REWRITE_TAC[VECTOR_ARITH `x - u:real^N = --u + x`] THEN
  ASM_SIMP_TAC[MEASURE_TRANSLATION; REAL_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* This is also interesting, and Minkowski follows easily from it.           *)
(* ------------------------------------------------------------------------- *)

let BLICHFELDT = prove
 (`!s:real^N->bool.
        bounded s /\ measurable s /\ &1 < measure s
        ==> ?x y. x IN s /\ y IN s /\ ~(x = y) /\
                  !i. 1 <= i /\ i <= dimindex(:N) ==> integer(x$i - y$i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{ u:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                                   ==> integer(u$i) }`;
                 `\u. {x | (x:real^N) IN s /\
                           !i. 1 <= i /\ i <= dimindex(:N)
                               ==> (u:real^N)$i <= x$i /\ x$i < u$i + &1 }`;
                 `s:real^N->bool`]
                LEMMA) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN
    REWRITE_TAC[EXISTS_IN_IMAGE; IN_INTER] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    REWRITE_TAC[VECTOR_ARITH `x - u:real^N = y - v <=> x + (v - u) = y`] THEN
    REWRITE_TAC[UNWIND_THM1] THEN STRIP_TAC THEN
    EXISTS_TAC `x + (v - u):real^N` THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `x = x + (v - u) <=> v:real^N = u`] THEN
    ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT] THEN
    ASM_SIMP_TAC[REAL_ARITH `x - (x + v - u) = u - v`; INTEGER_CLOSED]] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `?N. !x:real^N i. x IN s /\ 1 <= i /\ i <= dimindex(:N) ==> abs(x$i) < &N`
    STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
      DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
      MP_TAC(SPEC `B:real` (MATCH_MP REAL_ARCH REAL_LT_01)) THEN
      MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[REAL_MUL_RID] THEN
      X_GEN_TAC `N:num` THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_NUM] THEN
      SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_LT_POW2] THEN
      ASM_MESON_TAC[COMPONENT_LE_NORM; REAL_LE_TRANS; REAL_LET_TRANS];
      ALL_TAC] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC
     `{u:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                      ==> integer (u$i) /\ abs(u$i) <= &N}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_CART THEN
      REWRITE_TAC[GSYM REAL_BOUNDS_LE; FINITE_INTSEG];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `u:real^N` THEN
    STRIP_TAC THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC REAL_LE_REVERSE_INTEGERS THEN
    ASM_SIMP_TAC[INTEGER_CLOSED] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `k:num`)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^N`; `k:num`]) THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC MEASURABLE_ALMOST THEN
    EXISTS_TAC `s INTER interval[u:real^N,u + vec 1]` THEN
    ASM_SIMP_TAC[MEASURABLE_INTER_INTERVAL] THEN
    EXISTS_TAC `interval[u:real^N,u + vec 1] DIFF interval(u,u + vec 1)` THEN
    REWRITE_TAC[NEGLIGIBLE_FRONTIER_INTERVAL] THEN
    MATCH_MP_TAC(SET_RULE
     `s' SUBSET i /\ j INTER s' = j INTER s
      ==> (s INTER i) UNION (i DIFF j) = s' UNION (i DIFF j)`) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERVAL; IN_INTER; EXTENSION;
                IN_ELIM_THM] THEN
    CONJ_TAC THEN X_GEN_TAC `x:real^N` THEN
    ASM_CASES_TAC `(x:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN TRY EQ_TAC THEN
    REWRITE_TAC[AND_FORALL_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
    REWRITE_TAC[TAUT `(a ==> b) /\ (a ==> c) <=> a ==> b /\ c`] THEN
    GEN_TAC THEN DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VEC_COMPONENT] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    EXISTS_TAC `(lambda i. floor((x:real^N)$i)):real^N` THEN
    ASM_SIMP_TAC[LAMBDA_BETA; FLOOR];
    MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_SIMP_TAC[CART_EQ; REAL_EQ_INTEGERS] THEN
    REWRITE_TAC[NOT_FORALL_THM; LEFT_IMP_EXISTS_THM; NOT_IMP; REAL_NOT_LT] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[DISJOINT] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM (MP_TAC o SPEC `k:num`)) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `u:real^N` THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTERVAL] THEN
    GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    SIMP_TAC[VECTOR_SUB_COMPONENT; VEC_COMPONENT] THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The usual form of the theorem.                                            *)
(* ------------------------------------------------------------------------- *)

let MINKOWSKI = prove
 (`!s:real^N->bool.
        convex s /\
        bounded s /\
        (!x. x IN s ==> (--x) IN s) /\
        &2 pow dimindex(:N) < measure s
        ==> ?u. ~(u = vec 0) /\
                (!i. 1 <= i /\ i <= dimindex(:N) ==> integer(u$i)) /\
                u IN s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `IMAGE (\x:real^N. (&1 / &2) % x) s` BLICHFELDT) THEN
  ASM_SIMP_TAC[MEASURABLE_SCALING; MEASURE_SCALING; MEASURABLE_CONVEX;
               BOUNDED_SCALING] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID; REAL_ABS_INV; REAL_ABS_NUM] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM real_div; REAL_POW_INV] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_POW2; REAL_MUL_LID] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; EXISTS_IN_IMAGE] THEN
  REWRITE_TAC[VECTOR_ARITH `inv(&2) % x:real^N = inv(&2) % y <=> x = y`] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
  SIMP_TAC[VECTOR_MUL_COMPONENT; GSYM REAL_SUB_LDISTRIB] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN STRIP_TAC THEN
  EXISTS_TAC `inv(&2) % (u - v):real^N` THEN
  ASM_SIMP_TAC[VECTOR_ARITH `inv(&2) % (u - v):real^N = vec 0 <=> u = v`] THEN
  ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT] THEN
  REWRITE_TAC[VECTOR_SUB; VECTOR_ADD_LDISTRIB] THEN
  FIRST_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [convex]) THEN
  ASM_SIMP_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* A slightly sharper variant for use when the set is also closed.           *)
(* ------------------------------------------------------------------------- *)

let MINKOWSKI_COMPACT = prove
 (`!s:real^N->bool.
        convex s /\ compact s /\
        (!x. x IN s ==> (--x) IN s) /\
        &2 pow dimindex(:N) <= measure s
        ==> ?u. ~(u = vec 0) /\
                (!i. 1 <= i /\ i <= dimindex(:N) ==> integer(u$i)) /\
                u IN s`,
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[GSYM REAL_NOT_LT; MEASURE_EMPTY; REAL_LT_POW2];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(vec 0:real^N) IN s` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
    SUBST1_TAC(VECTOR_ARITH `vec 0:real^N = inv(&2) % a + inv(&2) % --a`) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [convex]) THEN
    ASM_SIMP_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
    [`s:real^N->bool`;
     `{u | !i. 1 <= i /\ i <= dimindex(:N) ==> integer(u$i)}
      DELETE (vec 0:real^N)`]
    SEPARATE_COMPACT_CLOSED) THEN
  REWRITE_TAC[EXTENSION; IN_DELETE; IN_ELIM_THM; IN_INTER; NOT_IN_EMPTY] THEN
  MATCH_MP_TAC(TAUT
   `(~e ==> c) /\ a /\ b /\ (d ==> e)
        ==> (a /\ b /\ c ==> d) ==> e`) THEN
  CONJ_TAC THENL [MESON_TAC[]; ASM_REWRITE_TAC[]] THEN CONJ_TAC THENL
   [MATCH_MP_TAC DISCRETE_IMP_CLOSED THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01; IN_DELETE; IN_ELIM_THM] THEN
    REPEAT GEN_TAC THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[CART_EQ; REAL_NOT_LT; NOT_FORALL_THM; NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs((y - x:real^N)$k)` THEN
    ASM_SIMP_TAC[COMPONENT_LE_NORM; VECTOR_SUB_COMPONENT] THEN
    ASM_MESON_TAC[REAL_EQ_INTEGERS; REAL_NOT_LE];
    ALL_TAC] THEN
  SIMP_TAC[dist] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `B:real` THEN STRIP_TAC THEN
  MP_TAC(ISPEC `IMAGE (\x:real^N. (&1 + d / &2 / B) % x) s` MINKOWSKI) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CONVEX_SCALING; BOUNDED_SCALING; COMPACT_IMP_BOUNDED] THEN
    ASM_SIMP_TAC[MEASURABLE_COMPACT; MEASURE_SCALING] THEN CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE; IN_IMAGE] THEN
      REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_ARITH
       `--(a % x):real^N = a % y <=> a % (x + y) = vec 0`] THEN
      ASM_MESON_TAC[VECTOR_ADD_RINV];
      ALL_TAC] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `d <= m ==> m < n ==> d < n`)) THEN
    REWRITE_TAC[REAL_ARITH `m < a * m <=> &0 < m * (a - &1)`] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[MEASURABLE_COMPACT; MEASURABLE_MEASURE_POS_LT] THEN
      REWRITE_TAC[GSYM HAS_MEASURE_0] THEN
      DISCH_THEN(SUBST_ALL_TAC o MATCH_MP MEASURE_UNIQUE) THEN
      ASM_MESON_TAC[REAL_NOT_LT; REAL_LT_POW2];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_LT] THEN MATCH_MP_TAC REAL_POW_LT_1 THEN
    REWRITE_TAC[DIMINDEX_NONZERO] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &1 < abs(&1 + x)`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> c /\ b /\ a`] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; VECTOR_MUL_EQ_0; DE_MORGAN_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`u:real^N`; `(&1 + d / &2 / B) % u:real^N`]) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN
  REWRITE_TAC[VECTOR_ARITH `u - (&1 + e) % u:real^N = --(e % u)`] THEN
  REWRITE_TAC[NORM_NEG; NORM_MUL] THEN
  MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN REWRITE_TAC[REAL_NOT_LE] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs(d / &2 / B) * B` THEN
  ASM_SIMP_TAC[REAL_LE_LMUL; REAL_ABS_POS] THEN
  ASM_REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NUM] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN
  UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC);;
