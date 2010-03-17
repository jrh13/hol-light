(* ========================================================================= *)
(* Lebsegue measure (defined via the gauge integral).                        *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(* ========================================================================= *)

needs "Library/card.ml";;
needs "Library/permutations.ml";;
needs "Multivariate/integration.ml";;
needs "Multivariate/determinants.ml";;
prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Lebesgue measure (in the case where the measure is finite).               *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("has_measure",(12,"right"));;

let has_measure = new_definition
 `s has_measure m <=> ((\x. vec 1) has_integral (lift m)) s`;;

let measurable = new_definition
 `measurable s <=> ?m. s has_measure m`;;

let measure = new_definition
 `measure s = @m. s has_measure m`;;

let HAS_MEASURE_MEASURE = prove
 (`!s. measurable s <=> s has_measure (measure s)`,
  REWRITE_TAC[measure; measurable] THEN MESON_TAC[]);;

let HAS_MEASURE_UNIQUE = prove
 (`!s m1 m2. s has_measure m1 /\ s has_measure m2 ==> m1 = m2`,
  REWRITE_TAC[has_measure; GSYM LIFT_EQ] THEN MESON_TAC[HAS_INTEGRAL_UNIQUE]);;

let MEASURE_UNIQUE = prove
 (`!s m. s has_measure m ==> measure s = m`,
  MESON_TAC[HAS_MEASURE_UNIQUE; HAS_MEASURE_MEASURE; measurable]);;

let HAS_MEASURE_MEASURABLE_MEASURE = prove
 (`!s m. s has_measure m <=> measurable s /\ measure s = m`,
  REWRITE_TAC[HAS_MEASURE_MEASURE] THEN MESON_TAC[MEASURE_UNIQUE]);;

let HAS_MEASURE_IMP_MEASURABLE = prove
 (`!s m. s has_measure m ==> measurable s`,
  REWRITE_TAC[measurable] THEN MESON_TAC[]);;

let HAS_MEASURE = prove
 (`!s m. s has_measure m <=>
              ((\x. if x IN s then vec 1 else vec 0) has_integral (lift m))
              (:real^N)`,
  SIMP_TAC[HAS_INTEGRAL_RESTRICT_UNIV; has_measure]);;

let MEASURABLE = prove
 (`!s. measurable s <=> (\x. vec 1:real^1) integrable_on s`,
  REWRITE_TAC[measurable; integrable_on;
              has_measure; EXISTS_DROP; LIFT_DROP]);;

let MEASURABLE_INTEGRABLE = prove
 (`measurable s <=>
     (\x. if x IN s then vec 1 else vec 0:real^1) integrable_on UNIV`,
  REWRITE_TAC[measurable; integrable_on;
              HAS_MEASURE; EXISTS_DROP; LIFT_DROP]);;

let MEASURE_INTEGRAL = prove
 (`!s. measurable s ==> measure s = drop (integral s (\x. vec 1))`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[GSYM LIFT_EQ; LIFT_DROP] THEN
  MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  ASM_REWRITE_TAC[GSYM has_measure; GSYM HAS_MEASURE_MEASURE]);;

let MEASURE_INTEGRAL_UNIV = prove
 (`!s. measurable s
       ==> measure s =
           drop(integral UNIV (\x. if x IN s then vec 1 else vec 0))`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[GSYM LIFT_EQ; LIFT_DROP] THEN
  MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  ASM_REWRITE_TAC[GSYM HAS_MEASURE; GSYM HAS_MEASURE_MEASURE]);;

let INTEGRAL_MEASURE = prove
 (`!s. measurable s ==> integral s (\x. vec 1) = lift(measure s)`,
  SIMP_TAC[GSYM DROP_EQ; LIFT_DROP; MEASURE_INTEGRAL]);;

let INTEGRAL_MEASURE_UNIV = prove
 (`!s. measurable s
       ==> integral UNIV (\x. if x IN s then vec 1 else vec 0) =
           lift(measure s)`,
  SIMP_TAC[GSYM DROP_EQ; LIFT_DROP; MEASURE_INTEGRAL_UNIV]);;

let HAS_MEASURE_INTERVAL = prove
 (`(!a b:real^N. interval[a,b] has_measure content(interval[a,b])) /\
   (!a b:real^N. interval(a,b) has_measure content(interval[a,b]))`,
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REWRITE_TAC[has_measure] THEN
    ONCE_REWRITE_TAC[LIFT_EQ_CMUL] THEN REWRITE_TAC[HAS_INTEGRAL_CONST];
    ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN SIMP_TAC[HAS_MEASURE] THEN
  MATCH_MP_TAC(REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
                           HAS_INTEGRAL_SPIKE) THEN
  EXISTS_TAC `interval[a:real^N,b] DIFF interval(a,b)` THEN
  REWRITE_TAC[NEGLIGIBLE_FRONTIER_INTERVAL] THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
  SET_TAC[]);;

let MEASURABLE_INTERVAL = prove
 (`(!a b:real^N. measurable (interval[a,b])) /\
   (!a b:real^N. measurable (interval(a,b)))`,
  REWRITE_TAC[measurable] THEN MESON_TAC[HAS_MEASURE_INTERVAL]);;

let MEASURE_INTERVAL = prove
 (`(!a b:real^N. measure(interval[a,b]) = content(interval[a,b])) /\
   (!a b:real^N. measure(interval(a,b)) = content(interval[a,b]))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_UNIQUE THEN
  REWRITE_TAC[HAS_MEASURE_INTERVAL]);;

let MEASURE_INTERVAL_1 = prove
 (`(!a b:real^1. measure(interval[a,b]) =
                    if drop a <= drop b then drop b - drop a else &0) /\
   (!a b:real^1. measure(interval(a,b)) =
                    if drop a <= drop b then drop b - drop a else &0)`,
  REWRITE_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES] THEN
  REWRITE_TAC[DIMINDEX_1; FORALL_1; PRODUCT_1; drop]);;

let MEASURE_INTERVAL_1_ALT = prove
 (`(!a b:real^1. measure(interval[a,b]) =
                    if drop a <= drop b then drop b - drop a else &0) /\
   (!a b:real^1. measure(interval(a,b)) =
                    if drop a <= drop b then drop b - drop a else &0)`,
  REWRITE_TAC[MEASURE_INTERVAL_1] THEN REAL_ARITH_TAC);;

let MEASURE_INTERVAL_2 = prove
 (`(!a b:real^2. measure(interval[a,b]) =
                 if a$1 <= b$1 /\ a$2 <= b$2
                 then (b$1 - a$1) * (b$2 - a$2)
                 else &0) /\
   (!a b:real^2. measure(interval(a,b)) =
                 if a$1 <= b$1 /\ a$2 <= b$2
                 then (b$1 - a$1) * (b$2 - a$2)
                 else &0)`,
  REWRITE_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES] THEN
  REWRITE_TAC[DIMINDEX_2; FORALL_2; PRODUCT_2]);;

let MEASURE_INTERVAL_2_ALT = prove
 (`(!a b:real^2. measure(interval[a,b]) =
                 if a$1 < b$1 /\ a$2 < b$2
                 then (b$1 - a$1) * (b$2 - a$2)
                 else &0) /\
   (!a b:real^2. measure(interval(a,b)) =
                 if a$1 < b$1 /\ a$2 < b$2
                 then (b$1 - a$1) * (b$2 - a$2)
                 else &0)`,
  REWRITE_TAC[MEASURE_INTERVAL_2] THEN REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC
   [`(a:real^2)$1 = (b:real^2)$1`; `(a:real^2)$2 = (b:real^2)$2`] THEN
  ASM_REWRITE_TAC[REAL_LT_REFL; REAL_MUL_LZERO; REAL_MUL_RZERO;
                  REAL_SUB_REFL; REAL_LE_REFL; REAL_ABS_NUM; COND_ID] THEN
  ASM_REWRITE_TAC[REAL_LT_LE]);;

let MEASURE_INTERVAL_3 = prove
 (`(!a b:real^3. measure(interval[a,b]) =
                 if a$1 <= b$1 /\ a$2 <= b$2 /\ a$3 <= b$3
                 then (b$1 - a$1) * (b$2 - a$2) * (b$3 - a$3)
                 else &0) /\
   (!a b:real^3. measure(interval(a,b)) =
                 if a$1 <= b$1 /\ a$2 <= b$2 /\ a$3 <= b$3
                 then (b$1 - a$1) * (b$2 - a$2) * (b$3 - a$3)
                 else &0)`,
  REWRITE_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES] THEN
  REWRITE_TAC[DIMINDEX_3; FORALL_3; PRODUCT_3]);;

let MEASURE_INTERVAL_3_ALT = prove
 (`(!a b:real^3. measure(interval[a,b]) =
                 if a$1 < b$1 /\ a$2 < b$2 /\ a$3 < b$3
                 then (b$1 - a$1) * (b$2 - a$2) * (b$3 - a$3)
                 else &0) /\
   (!a b:real^3. measure(interval(a,b)) =
                 if a$1 < b$1 /\ a$2 < b$2 /\ a$3 < b$3
                 then (b$1 - a$1) * (b$2 - a$2) * (b$3 - a$3)
                 else &0)`,
  REWRITE_TAC[MEASURE_INTERVAL_3] THEN REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC
   [`(a:real^3)$1 = (b:real^3)$1`;
    `(a:real^3)$2 = (b:real^3)$2`;
    `(a:real^3)$3 = (b:real^3)$3`] THEN
  ASM_REWRITE_TAC[REAL_LT_REFL; REAL_MUL_LZERO; REAL_MUL_RZERO;
                  REAL_SUB_REFL; REAL_LE_REFL; REAL_ABS_NUM; COND_ID] THEN
  ASM_REWRITE_TAC[REAL_LT_LE]);;

let MEASURABLE_INTER = prove
 (`!s t:real^N->bool. measurable s /\ measurable t ==> measurable (s INTER t)`,
  REWRITE_TAC[MEASURABLE_INTEGRABLE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  SUBGOAL_THEN
   `(\x. if x IN s INTER t then vec 1 else vec 0):real^N->real^1 =
    (\x. lambda i. min (((if x IN s then vec 1 else vec 0):real^1)$i)
                       (((if x IN t then vec 1 else vec 0):real^1)$i))`
  SUBST1_TAC THENL
   [SIMP_TAC[FUN_EQ_THM; CART_EQ; LAMBDA_BETA] THEN
    X_GEN_TAC `x:real^N` THEN REPEAT STRIP_TAC THEN
    MAP_EVERY ASM_CASES_TAC [`(x:real^N) IN s`; `(x:real^N) IN t`] THEN
    ASM_SIMP_TAC[IN_INTER; VEC_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_MIN THEN
  CONJ_TAC THEN MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[VEC_COMPONENT; REAL_POS]);;

let MEASURABLE_UNION = prove
 (`!s t:real^N->bool. measurable s /\ measurable t ==> measurable (s UNION t)`,
  REWRITE_TAC[MEASURABLE_INTEGRABLE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  SUBGOAL_THEN
   `(\x. if x IN s UNION t then vec 1 else vec 0):real^N->real^1 =
    (\x. lambda i. max (((if x IN s then vec 1 else vec 0):real^1)$i)
                       (((if x IN t then vec 1 else vec 0):real^1)$i))`
  SUBST1_TAC THENL
   [SIMP_TAC[FUN_EQ_THM; CART_EQ; LAMBDA_BETA] THEN
    X_GEN_TAC `x:real^N` THEN REPEAT STRIP_TAC THEN
    MAP_EVERY ASM_CASES_TAC [`(x:real^N) IN s`; `(x:real^N) IN t`] THEN
    ASM_SIMP_TAC[IN_UNION; VEC_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_MAX THEN
  CONJ_TAC THEN MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[VEC_COMPONENT; REAL_POS]);;

let HAS_MEASURE_DISJOINT_UNION = prove
 (`!s1 s2 m1 m2. s1 has_measure m1 /\ s2 has_measure m2 /\ DISJOINT s1 s2
                 ==> (s1 UNION s2) has_measure (m1 + m2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_MEASURE; CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_ADD) THEN
  REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  REPEAT(COND_CASES_TAC THEN REWRITE_TAC[VECTOR_ADD_LID; VECTOR_ADD_RID]) THEN
  ASM SET_TAC[]);;

let MEASURE_DISJOINT_UNION = prove
 (`!s t. measurable s /\ measurable t /\ DISJOINT s t
         ==> measure(s UNION t) = measure s + measure t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_MEASURE_DISJOINT_UNION; GSYM HAS_MEASURE_MEASURE]);;

let MEASURE_DISJOINT_UNION_EQ = prove
 (`!s t u.
        measurable s /\ measurable t /\ s UNION t = u /\ DISJOINT s t
        ==> measure s + measure t = measure u`,
  MESON_TAC[MEASURE_DISJOINT_UNION]);;

let HAS_MEASURE_POS_LE = prove
 (`!m s:real^N->bool. s has_measure m ==> &0 <= m`,
  REWRITE_TAC[HAS_MEASURE] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM(CONJUNCT2 LIFT_DROP)] THEN
  REWRITE_TAC[drop] THEN MATCH_MP_TAC(ISPEC
   `(\x. if x IN s then vec 1 else vec 0):real^N->real^1`
   HAS_INTEGRAL_COMPONENT_POS) THEN
  EXISTS_TAC `(:real^N)` THEN ASM_REWRITE_TAC[DIMINDEX_1; ARITH; IN_UNIV] THEN
  GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[GSYM drop; DROP_VEC; REAL_POS]);;

let MEASURE_POS_LE = prove
 (`!s. measurable s ==> &0 <= measure s`,
  REWRITE_TAC[HAS_MEASURE_MEASURE; HAS_MEASURE_POS_LE]);;

let HAS_MEASURE_SUBSET = prove
 (`!s1 s2:real^N->bool m1 m2.
        s1 has_measure m1 /\ s2 has_measure m2 /\ s1 SUBSET s2
        ==> m1 <= m2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_measure] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC BINOP_CONV [GSYM(CONJUNCT2 LIFT_DROP)] THEN
  MATCH_MP_TAC(ISPEC `(\x. vec 1):real^N->real^1`
    HAS_INTEGRAL_SUBSET_DROP_LE) THEN
  MAP_EVERY EXISTS_TAC [`s1:real^N->bool`; `s2:real^N->bool`] THEN
  ASM_REWRITE_TAC[DROP_VEC; REAL_POS]);;

let MEASURE_SUBSET = prove
 (`!s t. measurable s /\ measurable t /\ s SUBSET t
         ==> measure s <= measure t`,
  REWRITE_TAC[HAS_MEASURE_MEASURE] THEN MESON_TAC[HAS_MEASURE_SUBSET]);;

let HAS_MEASURE_0 = prove
 (`!s:real^N->bool. s has_measure &0 <=> negligible s`,
  GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[NEGLIGIBLE; has_measure] THEN
    DISCH_THEN(MP_TAC o SPEC `(:real^N)`) THEN
    ONCE_REWRITE_TAC[GSYM HAS_INTEGRAL_RESTRICT_UNIV] THEN
    REWRITE_TAC[IN_UNIV; indicator; LIFT_NUM]] THEN
  REWRITE_TAC[negligible] THEN REWRITE_TAC[has_measure] THEN
  ONCE_REWRITE_TAC[GSYM HAS_INTEGRAL_RESTRICT_UNIV] THEN
  REWRITE_TAC[LIFT_NUM] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [HAS_INTEGRAL_ALT]) THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  REWRITE_TAC[integrable_on; IN_UNIV] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV)
   [GSYM HAS_INTEGRAL_RESTRICT_UNIV] THEN
  REWRITE_TAC[indicator] THEN DISCH_THEN(X_CHOOSE_TAC `y:real^1`) THEN
  SUBGOAL_THEN `y:real^1 = vec 0` (fun th -> ASM_MESON_TAC[th]) THEN
  REWRITE_TAC[GSYM DROP_EQ; GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(ISPEC
     `(\x. if x IN interval [a,b]
           then if x IN s then vec 1 else vec 0 else vec 0):real^N->real^1`
     HAS_INTEGRAL_DROP_LE) THEN
    EXISTS_TAC `(\x. if x IN s then vec 1 else vec 0):real^N->real^1`;
    REWRITE_TAC[DROP_VEC] THEN MATCH_MP_TAC(ISPEC
     `(\x. if x IN interval [a,b]
           then if x IN s then vec 1 else vec 0 else vec 0):real^N->real^1`
     HAS_INTEGRAL_DROP_POS)] THEN
  EXISTS_TAC `(:real^N)` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[DROP_VEC; REAL_POS; REAL_LE_REFL]);;

let MEASURE_EQ_0 = prove
 (`!s. negligible s ==> measure s = &0`,
  MESON_TAC[MEASURE_UNIQUE; HAS_MEASURE_0]);;

let HAS_MEASURE_EMPTY = prove
 (`{} has_measure &0`,
  REWRITE_TAC[HAS_MEASURE_0; NEGLIGIBLE_EMPTY]);;

let MEASURE_EMPTY = prove
 (`measure {} = &0`,
  SIMP_TAC[MEASURE_EQ_0; NEGLIGIBLE_EMPTY]);;

let MEASURABLE_EMPTY = prove
 (`measurable {}`,
  REWRITE_TAC[measurable] THEN MESON_TAC[HAS_MEASURE_EMPTY]);;

let MEASURABLE_MEASURE_EQ_0 = prove
 (`!s. measurable s ==> (measure s = &0 <=> negligible s)`,
  REWRITE_TAC[HAS_MEASURE_MEASURE; GSYM HAS_MEASURE_0] THEN
  MESON_TAC[MEASURE_UNIQUE]);;

let MEASURABLE_MEASURE_POS_LT = prove
 (`!s. measurable s ==> (&0 < measure s <=> ~negligible s)`,
  SIMP_TAC[REAL_LT_LE; MEASURE_POS_LE; GSYM MEASURABLE_MEASURE_EQ_0] THEN
  REWRITE_TAC[EQ_SYM_EQ]);;

let NEGLIGIBLE_INTERVAL = prove
 (`(!a b. negligible(interval[a,b]) <=> interval(a,b) = {}) /\
   (!a b. negligible(interval(a,b)) <=> interval(a,b) = {})`,
  REWRITE_TAC[GSYM HAS_MEASURE_0] THEN
  MESON_TAC[HAS_MEASURE_INTERVAL; CONTENT_EQ_0_INTERIOR;
            INTERIOR_CLOSED_INTERVAL; HAS_MEASURE_UNIQUE]);;

let MEASURABLE_UNIONS = prove
 (`!m f:(real^N->bool)->bool.
        FINITE f /\ (!s. s IN f ==> measurable s)
        ==> measurable (UNIONS f)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[UNIONS_0; UNIONS_INSERT; MEASURABLE_EMPTY] THEN
  REWRITE_TAC[IN_INSERT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURABLE_UNION THEN ASM_SIMP_TAC[]);;

let HAS_MEASURE_DIFF_SUBSET = prove
 (`!s1 s2 m1 m2. s1 has_measure m1 /\ s2 has_measure m2 /\ s2 SUBSET s1
                 ==> (s1 DIFF s2) has_measure (m1 - m2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_MEASURE; CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_SUB) THEN
  REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[VECTOR_SUB_REFL; VECTOR_SUB_RZERO] THEN
  ASM SET_TAC[]);;

let MEASURABLE_DIFF = prove
 (`!s t:real^N->bool. measurable s /\ measurable t ==> measurable (s DIFF t)`,
  SUBGOAL_THEN
   `!s t:real^N->bool. measurable s /\ measurable t /\ t SUBSET s
         ==> measurable (s DIFF t)`
  ASSUME_TAC THENL
   [REWRITE_TAC[measurable] THEN MESON_TAC[HAS_MEASURE_DIFF_SUBSET];
    ONCE_REWRITE_TAC[SET_RULE `s DIFF t = s DIFF (s INTER t)`] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[MEASURABLE_INTER] THEN
    SET_TAC[]]);;

let MEASURE_DIFF_SUBSET = prove
 (`!s t. measurable s /\ measurable t /\ t SUBSET s
         ==> measure(s DIFF t) = measure s - measure t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_MEASURE_DIFF_SUBSET; GSYM HAS_MEASURE_MEASURE]);;

let HAS_MEASURE_UNION_NEGLIGIBLE = prove
 (`!s t:real^N->bool m.
        s has_measure m /\ negligible t ==> (s UNION t) has_measure m`,
  REWRITE_TAC[HAS_MEASURE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_INTEGRAL_SPIKE THEN
  MAP_EVERY EXISTS_TAC
   [`(\x. if x IN s then vec 1 else vec 0):real^N->real^1`;
    `t:real^N->bool`] THEN
  ASM_SIMP_TAC[IN_DIFF; IN_UNIV; IN_UNION]);;

let HAS_MEASURE_DIFF_NEGLIGIBLE = prove
 (`!s t:real^N->bool m.
        s has_measure m /\ negligible t ==> (s DIFF t) has_measure m`,
  REWRITE_TAC[HAS_MEASURE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_INTEGRAL_SPIKE THEN
  MAP_EVERY EXISTS_TAC
   [`(\x. if x IN s then vec 1 else vec 0):real^N->real^1`;
    `t:real^N->bool`] THEN
  ASM_SIMP_TAC[IN_DIFF; IN_UNIV; IN_UNION]);;

let HAS_MEASURE_UNION_NEGLIGIBLE_EQ = prove
 (`!s t:real^N->bool m.
     negligible t ==> ((s UNION t) has_measure m <=> s has_measure m)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[HAS_MEASURE_UNION_NEGLIGIBLE] THEN
  SUBST1_TAC(SET_RULE `s:real^N->bool = (s UNION t) DIFF (t DIFF s)`) THEN
  MATCH_MP_TAC HAS_MEASURE_DIFF_NEGLIGIBLE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC NEGLIGIBLE_DIFF THEN ASM_REWRITE_TAC[]);;

let HAS_MEASURE_DIFF_NEGLIGIBLE_EQ = prove
 (`!s t:real^N->bool m.
     negligible t ==> ((s DIFF t) has_measure m <=> s has_measure m)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[HAS_MEASURE_DIFF_NEGLIGIBLE] THEN
  SUBST1_TAC(SET_RULE `s:real^N->bool = (s DIFF t) UNION (t INTER s)`) THEN
  MATCH_MP_TAC HAS_MEASURE_UNION_NEGLIGIBLE THEN
  ASM_SIMP_TAC[NEGLIGIBLE_INTER]);;

let HAS_MEASURE_ALMOST = prove
 (`!s s' t m. s has_measure m /\ negligible t /\ s UNION t = s' UNION t
              ==> s' has_measure m`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (SET_RULE
   `s UNION t = s' UNION t ==> s' = (s UNION t) DIFF (t DIFF s')`)) THEN
  ASM_SIMP_TAC[HAS_MEASURE_DIFF_NEGLIGIBLE; HAS_MEASURE_UNION_NEGLIGIBLE;
               NEGLIGIBLE_DIFF]);;

let HAS_MEASURE_ALMOST_EQ = prove
 (`!s s' t. negligible t /\ s UNION t = s' UNION t
            ==> (s has_measure m <=> s' has_measure m)`,
  MESON_TAC[HAS_MEASURE_ALMOST]);;

let MEASURABLE_ALMOST = prove
 (`!s s' t. measurable s /\ negligible t /\ s UNION t = s' UNION t
            ==> measurable s'`,
  REWRITE_TAC[measurable] THEN MESON_TAC[HAS_MEASURE_ALMOST]);;

let HAS_MEASURE_NEGLIGIBLE_UNION = prove
 (`!s1 s2:real^N->bool m1 m2.
        s1 has_measure m1 /\ s2 has_measure m2 /\ negligible(s1 INTER s2)
        ==> (s1 UNION s2) has_measure (m1 + m2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_MEASURE_ALMOST THEN
  MAP_EVERY EXISTS_TAC
   [`(s1 DIFF (s1 INTER s2)) UNION (s2 DIFF (s1 INTER s2)):real^N->bool`;
    `s1 INTER s2:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; SET_TAC[]] THEN
  MATCH_MP_TAC HAS_MEASURE_DISJOINT_UNION THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HAS_MEASURE_ALMOST THEN EXISTS_TAC `s1:real^N->bool`;
    MATCH_MP_TAC HAS_MEASURE_ALMOST THEN EXISTS_TAC `s2:real^N->bool`;
    SET_TAC[]] THEN
  EXISTS_TAC `s1 INTER s2:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let MEASURE_NEGLIGIBLE_UNION = prove
 (`!s t. measurable s /\ measurable t /\ negligible(s INTER t)
         ==> measure(s UNION t) = measure s + measure t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_MEASURE_NEGLIGIBLE_UNION; GSYM HAS_MEASURE_MEASURE]);;

let MEASURE_NEGLIGIBLE_UNION_EQ = prove
 (`!s t u.
        measurable s /\ measurable t /\ s UNION t = u /\ negligible(s INTER t)
        ==> measure s + measure t = measure u`,
  MESON_TAC[MEASURE_NEGLIGIBLE_UNION]);;

let HAS_MEASURE_NEGLIGIBLE_SYMDIFF = prove
 (`!s t:real^N->bool m.
        s has_measure m /\
        negligible((s DIFF t) UNION (t DIFF s))
        ==> t has_measure m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_MEASURE_ALMOST THEN
  MAP_EVERY EXISTS_TAC
   [`s:real^N->bool`; `(s DIFF t) UNION (t DIFF s):real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let MEASURABLE_NEGLIGIBLE_SYMDIFF = prove
 (`!s t:real^N->bool.
        measurable s /\ negligible((s DIFF t) UNION (t DIFF s))
        ==> measurable t`,
  REWRITE_TAC[measurable] THEN
  MESON_TAC[HAS_MEASURE_NEGLIGIBLE_SYMDIFF]);;

let MEASURABLE_NEGLIGIBLE_SYMDIFF_EQ = prove
 (`!s t:real^N->bool.
        negligible(s DIFF t UNION t DIFF s)
        ==> (measurable s <=> measurable t)`,
  MESON_TAC[MEASURABLE_NEGLIGIBLE_SYMDIFF; UNION_COMM]);;

let MEASURE_NEGLIGIBLE_SYMDIFF = prove
 (`!s t:real^N->bool.
        negligible(s DIFF t UNION t DIFF s) ==> measure s = measure t`,
  REPEAT STRIP_TAC THEN MAP_EVERY ASM_CASES_TAC
   [`measurable(s:real^N->bool)`; `measurable(t:real^N->bool)`]
  THENL
   [ASM_MESON_TAC[HAS_MEASURE_NEGLIGIBLE_SYMDIFF; MEASURE_UNIQUE;
                  HAS_MEASURE_MEASURE];
    ASM_MESON_TAC[MEASURABLE_NEGLIGIBLE_SYMDIFF_EQ];
    ASM_MESON_TAC[MEASURABLE_NEGLIGIBLE_SYMDIFF_EQ];
    REWRITE_TAC[measure] THEN AP_TERM_TAC THEN ABS_TAC THEN
    ASM_MESON_TAC[measurable]]);;

let HAS_MEASURE_NEGLIGIBLE_UNIONS = prove
 (`!m f:(real^N->bool)->bool.
        FINITE f /\
        (!s. s IN f ==> s has_measure (m s)) /\
        (!s t. s IN f /\ t IN f /\ ~(s = t) ==> negligible(s INTER t))
        ==> (UNIONS f) has_measure (sum f m)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; UNIONS_0; UNIONS_INSERT; HAS_MEASURE_EMPTY] THEN
  REWRITE_TAC[IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `f:(real^N->bool)->bool`] THEN
  STRIP_TAC THEN STRIP_TAC THEN MATCH_MP_TAC HAS_MEASURE_NEGLIGIBLE_UNION THEN
  REPEAT(CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  REWRITE_TAC[INTER_UNIONS] THEN MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let MEASURE_NEGLIGIBLE_UNIONS = prove
 (`!m f:(real^N->bool)->bool.
        FINITE f /\
        (!s. s IN f ==> s has_measure (m s)) /\
        (!s t. s IN f /\ t IN f /\ ~(s = t) ==> negligible(s INTER t))
        ==> measure(UNIONS f) = sum f m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_MEASURE_NEGLIGIBLE_UNIONS]);;

let HAS_MEASURE_DISJOINT_UNIONS = prove
 (`!m f:(real^N->bool)->bool.
        FINITE f /\
        (!s. s IN f ==> s has_measure (m s)) /\
        (!s t. s IN f /\ t IN f /\ ~(s = t) ==> DISJOINT s t)
        ==> (UNIONS f) has_measure (sum f m)`,
  REWRITE_TAC[DISJOINT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_MEASURE_NEGLIGIBLE_UNIONS THEN
  ASM_SIMP_TAC[NEGLIGIBLE_EMPTY]);;

let MEASURE_DISJOINT_UNIONS = prove
 (`!m f:(real^N->bool)->bool.
        FINITE f /\
        (!s. s IN f ==> s has_measure (m s)) /\
        (!s t. s IN f /\ t IN f /\ ~(s = t) ==> DISJOINT s t)
        ==> measure(UNIONS f) = sum f m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_MEASURE_DISJOINT_UNIONS]);;

let HAS_MEASURE_NEGLIGIBLE_UNIONS_IMAGE = prove
 (`!f:A->real^N->bool s.
        FINITE s /\
        (!x. x IN s ==> measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> negligible((f x) INTER (f y)))
        ==> (UNIONS (IMAGE f s)) has_measure (sum s (\x. measure(f x)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum s (\x. measure(f x)) = sum (IMAGE (f:A->real^N->bool) s) measure`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN ONCE_REWRITE_TAC[GSYM o_DEF] THEN
    MATCH_MP_TAC SUM_IMAGE_NONZERO THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `y:A`]) THEN
    ASM_SIMP_TAC[INTER_ACI; MEASURABLE_MEASURE_EQ_0];
    MATCH_MP_TAC HAS_MEASURE_NEGLIGIBLE_UNIONS THEN
    ASM_SIMP_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[FINITE_IMAGE; HAS_MEASURE_MEASURE]]);;

let MEASURE_NEGLIGIBLE_UNIONS_IMAGE = prove
 (`!f:A->real^N->bool s.
        FINITE s /\
        (!x. x IN s ==> measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> negligible((f x) INTER (f y)))
        ==> measure(UNIONS (IMAGE f s)) = sum s (\x. measure(f x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_MEASURE_NEGLIGIBLE_UNIONS_IMAGE]);;

let HAS_MEASURE_DISJOINT_UNIONS_IMAGE = prove
 (`!f:A->real^N->bool s.
        FINITE s /\
        (!x. x IN s ==> measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> DISJOINT (f x) (f y))
        ==> (UNIONS (IMAGE f s)) has_measure (sum s (\x. measure(f x)))`,
  REWRITE_TAC[DISJOINT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_MEASURE_NEGLIGIBLE_UNIONS_IMAGE THEN
  ASM_SIMP_TAC[NEGLIGIBLE_EMPTY]);;

let MEASURE_DISJOINT_UNIONS_IMAGE = prove
 (`!f:A->real^N->bool s.
        FINITE s /\
        (!x. x IN s ==> measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> DISJOINT (f x) (f y))
        ==> measure(UNIONS (IMAGE f s)) = sum s (\x. measure(f x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_MEASURE_DISJOINT_UNIONS_IMAGE]);;

let HAS_MEASURE_NEGLIGIBLE_UNIONS_IMAGE_STRONG = prove
 (`!f:A->real^N->bool s.
        FINITE {x | x IN s /\ ~(f x = {})} /\
        (!x. x IN s ==> measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> negligible((f x) INTER (f y)))
        ==> (UNIONS (IMAGE f s)) has_measure (sum s (\x. measure(f x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->real^N->bool`;
                 `{x | x IN s /\ ~((f:A->real^N->bool) x = {})}`]
        HAS_MEASURE_NEGLIGIBLE_UNIONS_IMAGE) THEN
  ASM_SIMP_TAC[IN_ELIM_THM; FINITE_RESTRICT] THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[NOT_IN_EMPTY];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM; TAUT `a /\ ~(a /\ b) <=> a /\ ~b`] THEN
    REWRITE_TAC[MEASURE_EMPTY]]);;

let MEASURE_NEGLIGIBLE_UNIONS_IMAGE_STRONG = prove
 (`!f:A->real^N->bool s.
        FINITE {x | x IN s /\ ~(f x = {})} /\
        (!x. x IN s ==> measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> negligible((f x) INTER (f y)))
        ==> measure(UNIONS (IMAGE f s)) = sum s (\x. measure(f x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_MEASURE_NEGLIGIBLE_UNIONS_IMAGE_STRONG]);;

let HAS_MEASURE_DISJOINT_UNIONS_IMAGE_STRONG = prove
 (`!f:A->real^N->bool s.
        FINITE {x | x IN s /\ ~(f x = {})} /\
        (!x. x IN s ==> measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> DISJOINT (f x) (f y))
        ==> (UNIONS (IMAGE f s)) has_measure (sum s (\x. measure(f x)))`,
  REWRITE_TAC[DISJOINT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_MEASURE_NEGLIGIBLE_UNIONS_IMAGE_STRONG THEN
  ASM_SIMP_TAC[NEGLIGIBLE_EMPTY]);;

let MEASURE_DISJOINT_UNIONS_IMAGE_STRONG = prove
 (`!f:A->real^N->bool s.
        FINITE {x | x IN s /\ ~(f x = {})} /\
        (!x. x IN s ==> measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> DISJOINT (f x) (f y))
        ==> measure(UNIONS (IMAGE f s)) = sum s (\x. measure(f x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_MEASURE_DISJOINT_UNIONS_IMAGE_STRONG]);;

let MEASURE_UNION = prove
 (`!s t:real^N->bool.
        measurable s /\ measurable t
        ==> measure(s UNION t) = measure(s) + measure(t) - measure(s INTER t)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE
   `s UNION t = (s INTER t) UNION (s DIFF t) UNION (t DIFF s)`] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a + b - c = c + (a - c) + (b - c)`] THEN
  MP_TAC(ISPECL [`s DIFF t:real^N->bool`; `t DIFF s:real^N->bool`]
        MEASURE_DISJOINT_UNION) THEN
  ASM_SIMP_TAC[MEASURABLE_DIFF] THEN
  ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s INTER t:real^N->bool`;
                 `(s DIFF t) UNION (t DIFF s):real^N->bool`]
                MEASURE_DISJOINT_UNION) THEN
  ASM_SIMP_TAC[MEASURABLE_DIFF; MEASURABLE_UNION; MEASURABLE_INTER] THEN
  ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN AP_TERM_TAC THEN BINOP_TAC THEN
  REWRITE_TAC[REAL_EQ_SUB_LADD] THEN MATCH_MP_TAC EQ_TRANS THENL
   [EXISTS_TAC `measure((s DIFF t) UNION (s INTER t):real^N->bool)`;
    EXISTS_TAC `measure((t DIFF s) UNION (s INTER t):real^N->bool)`] THEN
  (CONJ_TAC THENL
    [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MEASURE_DISJOINT_UNION THEN
     ASM_SIMP_TAC[MEASURABLE_DIFF; MEASURABLE_INTER];
     AP_TERM_TAC] THEN
   SET_TAC[]));;

let MEASURE_UNION_LE = prove
 (`!s t:real^N->bool.
        measurable s /\ measurable t
        ==> measure(s UNION t) <= measure s + measure t`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MEASURE_UNION] THEN
  REWRITE_TAC[REAL_ARITH `a + b - c <= a + b <=> &0 <= c`] THEN
  MATCH_MP_TAC MEASURE_POS_LE THEN ASM_SIMP_TAC[MEASURABLE_INTER]);;

let MEASURE_UNIONS_LE = prove
 (`!f:(real^N->bool)->bool.
        FINITE f /\ (!s. s IN f ==> measurable s)
        ==> measure(UNIONS f) <= sum f (\s. measure s)`,
  REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[UNIONS_0; UNIONS_INSERT; SUM_CLAUSES] THEN
  REWRITE_TAC[MEASURE_EMPTY; REAL_LE_REFL] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `f:(real^N->bool)->bool`] THEN
  REWRITE_TAC[IN_INSERT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `measure(s:real^N->bool) + measure(UNIONS f:real^N->bool)` THEN
  ASM_SIMP_TAC[MEASURE_UNION_LE; MEASURABLE_UNIONS] THEN
  REWRITE_TAC[REAL_LE_LADD] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[]);;

let MEASURE_UNIONS_LE_IMAGE = prove
 (`!f:A->bool s:A->(real^N->bool).
        FINITE f /\ (!a. a IN f ==> measurable(s a))
        ==> measure(UNIONS (IMAGE s f)) <= sum f (\a. measure(s a))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (IMAGE s (f:A->bool)) (\k:real^N->bool. measure k)` THEN
  ASM_SIMP_TAC[MEASURE_UNIONS_LE; FORALL_IN_IMAGE; FINITE_IMAGE] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
  REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC SUM_IMAGE_LE THEN
  ASM_SIMP_TAC[MEASURE_POS_LE]);;

let MEASURABLE_INNER_OUTER = prove
 (`!s:real^N->bool.
        measurable s <=>
                !e. &0 < e
                    ==> ?t u. t SUBSET s /\ s SUBSET u /\
                              measurable t /\ measurable u /\
                              abs(measure t - measure u) < e`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN REPEAT(EXISTS_TAC `s:real^N->bool`) THEN
    ASM_REWRITE_TAC[SUBSET_REFL; REAL_SUB_REFL; REAL_ABS_NUM];
    ALL_TAC] THEN
  REWRITE_TAC[MEASURABLE_INTEGRABLE] THEN MATCH_MP_TAC INTEGRABLE_STRADDLE THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `u:real^N->bool`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`(\x. if x IN t then vec 1 else vec 0):real^N->real^1`;
    `(\x. if x IN u then vec 1 else vec 0):real^N->real^1`;
    `lift(measure(t:real^N->bool))`;
    `lift(measure(u:real^N->bool))`] THEN
  ASM_REWRITE_TAC[GSYM HAS_MEASURE; GSYM HAS_MEASURE_MEASURE] THEN
  ASM_REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN
         ASM_REWRITE_TAC[DROP_VEC; REAL_POS; REAL_LE_REFL]) THEN
  ASM SET_TAC[]);;

let HAS_MEASURE_INNER_OUTER = prove
 (`!s:real^N->bool m.
        s has_measure m <=>
                (!e. &0 < e ==> ?t. t SUBSET s /\ measurable t /\
                                    m - e < measure t) /\
                (!e. &0 < e ==> ?u. s SUBSET u /\ measurable u /\
                                    measure u < m + e)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [HAS_MEASURE_MEASURABLE_MEASURE] THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "t") (LABEL_TAC "u")) THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC I [MEASURABLE_INNER_OUTER] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    REMOVE_THEN "u" (MP_TAC o SPEC `e / &2`) THEN
    REMOVE_THEN "t" (MP_TAC o SPEC `e / &2`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    REWRITE_TAC[IMP_IMP; LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
     `&0 < e /\ t <= u /\ m - e / &2 < t /\ u < m + e / &2
                          ==> abs(t - u) < e`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MEASURE_SUBSET THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH
     `~(&0 < x - y) /\ ~(&0 < y - x) ==> x = y`) THEN
    CONJ_TAC THEN DISCH_TAC THENL
     [REMOVE_THEN "u" (MP_TAC o SPEC `measure(s:real^N->bool) - m`) THEN
      ASM_REWRITE_TAC[REAL_SUB_ADD2; GSYM REAL_NOT_LE];
      REMOVE_THEN "t" (MP_TAC o SPEC `m - measure(s:real^N->bool)`) THEN
      ASM_REWRITE_TAC[REAL_SUB_SUB2; GSYM REAL_NOT_LE]] THEN
    ASM_MESON_TAC[MEASURE_SUBSET]]);;

let HAS_MEASURE_INNER_OUTER_LE = prove
 (`!s:real^N->bool m.
        s has_measure m <=>
                (!e. &0 < e ==> ?t. t SUBSET s /\ measurable t /\
                                    m - e <= measure t) /\
                (!e. &0 < e ==> ?u. s SUBSET u /\ measurable u /\
                                    measure u <= m + e)`,
  REWRITE_TAC[HAS_MEASURE_INNER_OUTER] THEN
  MESON_TAC[REAL_ARITH `&0 < e /\ m - e / &2 <= t ==> m - e < t`;
            REAL_ARITH `&0 < e /\ u <= m + e / &2 ==> u < m + e`;
            REAL_ARITH `&0 < e <=> &0 < e / &2`; REAL_LT_IMP_LE]);;

let HAS_MEASURE_LIMIT = prove
 (`!s. s has_measure m <=>
        !e. &0 < e
            ==> ?B. &0 < B /\
                    !a b. ball(vec 0,B) SUBSET interval[a,b]
                          ==> ?z. (s INTER interval[a,b]) has_measure z /\
                                  abs(z - m) < e`,
  GEN_TAC THEN REWRITE_TAC[HAS_MEASURE] THEN
  GEN_REWRITE_TAC LAND_CONV [HAS_INTEGRAL] THEN
  REWRITE_TAC[IN_UNIV] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
    [GSYM HAS_INTEGRAL_RESTRICT_UNIV] THEN
  REWRITE_TAC[MESON[IN_INTER]
        `(if x IN k INTER s then a else b) =
         (if x IN s then if x IN k then a else b else b)`] THEN
  REWRITE_TAC[EXISTS_LIFT; GSYM LIFT_SUB; NORM_LIFT]);;

(* ------------------------------------------------------------------------- *)
(* Properties of measure under simple affine transformations.                *)
(* ------------------------------------------------------------------------- *)

let HAS_MEASURE_AFFINITY = prove
 (`!s m c y. s has_measure y
             ==> (IMAGE (\x:real^N. m % x + c) s)
                 has_measure abs(m) pow (dimindex(:N)) * y`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `m = &0` THENL
   [ASM_REWRITE_TAC[REAL_ABS_NUM; VECTOR_ADD_LID; VECTOR_MUL_LZERO] THEN
    ONCE_REWRITE_TAC[MATCH_MP (ARITH_RULE `~(x = 0) ==> x = SUC(x - 1)`)
     (SPEC_ALL DIMINDEX_NONZERO)] THEN DISCH_TAC THEN
    REWRITE_TAC[real_pow; REAL_MUL_LZERO; HAS_MEASURE_0] THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{c:real^N}` THEN
    SIMP_TAC[NEGLIGIBLE_FINITE; FINITE_RULES] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[HAS_MEASURE] THEN
  ONCE_REWRITE_TAC[HAS_INTEGRAL] THEN REWRITE_TAC[IN_UNIV] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real / abs(m) pow dimindex(:N)`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_POW_LT; GSYM REAL_ABS_NZ; REAL_POW_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `abs(m) * B + norm(c:real^N)` THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < B /\ &0 <= x ==> &0 < B + x`;
               NORM_POS_LE; REAL_LT_MUL; GSYM REAL_ABS_NZ; REAL_POW_LT] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN DISCH_TAC THEN
  REWRITE_TAC[IN_IMAGE] THEN
  ASM_SIMP_TAC[VECTOR_EQ_AFFINITY; UNWIND_THM1] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`if &0 <= m then inv m % u + --(inv m % c):real^N
                 else inv m % v + --(inv m % c)`;
     `if &0 <= m then inv m % v + --(inv m % c):real^N
                 else inv m % u + --(inv m % c)`]) THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b ==> c) ==> (a ==> b) ==> c`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    DISCH_THEN(MP_TAC o SPEC `m % x + c:real^N`) THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[IN_BALL; IN_INTERVAL] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[NORM_ARITH `dist(vec 0,x) = norm(x:real^N)`] THEN
      DISCH_TAC THEN MATCH_MP_TAC(NORM_ARITH
       `norm(x:real^N) < a ==> norm(x + y) < a + norm(y)`) THEN
      ASM_SIMP_TAC[NORM_MUL; REAL_LT_LMUL; GSYM REAL_ABS_NZ];
      ALL_TAC] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_NEG_COMPONENT;
             COND_COMPONENT] THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
    REWRITE_TAC[REAL_ARITH `m * u + --(m * c):real = (u - c) * m`] THEN
    SUBST1_TAC(REAL_ARITH
      `inv(m) = if &0 <= inv(m) then abs(inv m) else --(abs(inv m))`) THEN
    SIMP_TAC[REAL_LE_INV_EQ] THEN
    REWRITE_TAC[REAL_ARITH `(x - y:real) * --z = (y - x) * z`] THEN
    REWRITE_TAC[REAL_ABS_INV; GSYM real_div] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; GSYM REAL_ABS_NZ] THEN
    ASM_REWRITE_TAC[real_abs] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `vec 0:real^N`) THEN
  ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN DISCH_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^1`
   (fun th -> EXISTS_TAC `(abs m pow dimindex (:N)) % z:real^1` THEN
              MP_TAC th)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP(REAL_FIELD `~(x = &0) ==> ~(inv x = &0)`)) THEN
  REWRITE_TAC[TAUT `a ==> b ==> c <=> b /\ a ==> c`] THEN
  DISCH_THEN(MP_TAC o SPEC `--(inv m % c):real^N` o
    MATCH_MP HAS_INTEGRAL_AFFINITY) THEN
  ASM_REWRITE_TAC[IMAGE_AFFINITY_INTERVAL; REAL_INV_INV] THEN
  SIMP_TAC[COND_ID] THEN COND_CASES_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC;
               VECTOR_MUL_LNEG; VECTOR_MUL_RNEG] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; VECTOR_MUL_LID; VECTOR_NEG_NEG] THEN
  REWRITE_TAC[VECTOR_ARITH `(u + --c) + c:real^N = u`] THEN
  REWRITE_TAC[REAL_ABS_INV; REAL_INV_INV; GSYM REAL_POW_INV] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[LIFT_CMUL; GSYM VECTOR_SUB_LDISTRIB] THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_POW; REAL_ABS_ABS] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_POW_LT; GSYM REAL_ABS_NZ]);;

let STRETCH_GALOIS = prove
 (`!x:real^N y:real^N m.
        (!k. 1 <= k /\ k <= dimindex(:N) ==>  ~(m k = &0))
        ==> ((y = (lambda k. m k * x$k)) <=> (lambda k. inv(m k) * y$k) = x)`,
  REPEAT GEN_TAC THEN SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN
  MATCH_MP_TAC(MESON[]
   `(!x. p x ==> (q x <=> r x))
    ==> (!x. p x) ==> ((!x. q x) <=> (!x. r x))`) THEN
  GEN_TAC THEN ASM_CASES_TAC `1 <= k /\ k <= dimindex(:N)` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_FIELD);;

let HAS_MEASURE_STRETCH = prove
 (`!s m y. s has_measure y
           ==> (IMAGE (\x:real^N. lambda k. m k * x$k) s :real^N->bool)
               has_measure abs(product (1..dimindex(:N)) m) * y`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC
   `!k. 1 <= k /\ k <= dimindex(:N) ==> ~(m k = &0)`
  THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
    REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `product(1..dimindex (:N)) m = &0` SUBST1_TAC THENL
     [ASM_MESON_TAC[PRODUCT_EQ_0_NUMSEG]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_NUM; REAL_MUL_LZERO; HAS_MEASURE_0] THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `{x:real^N | x$k = &0}` THEN
    ASM_SIMP_TAC[NEGLIGIBLE_STANDARD_HYPERPLANE; SUBSET; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[IN_ELIM_THM; LAMBDA_BETA; REAL_MUL_LZERO]] THEN
  UNDISCH_TAC `(s:real^N->bool) has_measure y` THEN
  REWRITE_TAC[HAS_MEASURE] THEN
  ONCE_REWRITE_TAC[HAS_INTEGRAL] THEN REWRITE_TAC[IN_UNIV] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < abs(product(1..dimindex(:N)) m)` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_ABS_NZ; REAL_LT_DIV; PRODUCT_EQ_0_NUMSEG];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real / abs(product(1..dimindex(:N)) m)`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `sup(IMAGE (\k. abs(m k) * B) (1..dimindex(:N)))` THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_SUP_FINITE; FINITE_IMAGE; NUMSEG_EMPTY; FINITE_NUMSEG;
                 IN_NUMSEG; GSYM NOT_LE; DIMINDEX_GE_1; IMAGE_EQ_EMPTY;
                 EXISTS_IN_IMAGE] THEN
    ASM_MESON_TAC[IN_NUMSEG; DIMINDEX_GE_1; LE_REFL; REAL_LT_MUL; REAL_ABS_NZ];
    DISCH_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[IN_IMAGE; STRETCH_GALOIS; UNWIND_THM1] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`(lambda k. min (inv(m k) * (u:real^N)$k)
                     (inv(m k) * (v:real^N)$k)):real^N`;
     `(lambda k. max (inv(m k) * (u:real^N)$k)
                 (inv(m k) * (v:real^N)$k)):real^N`]) THEN
  MATCH_MP_TAC(TAUT `a /\ (b ==> a ==> c) ==> (a ==> b) ==> c`) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `z:real^1` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    SUBGOAL_THEN `!k. 1 <= k /\ k <= dimindex (:N) ==> ~(inv(m k) = &0)`
    MP_TAC THENL [ASM_SIMP_TAC[REAL_INV_EQ_0]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
    DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_STRETCH)] THEN
  (MP_TAC(ISPECL [`u:real^N`; `v:real^N`; `\i:num. inv(m i)`]
    IMAGE_STRETCH_INTERVAL) THEN
   SUBGOAL_THEN `~(interval[u:real^N,v] = {})` ASSUME_TAC THENL
    [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
      `s SUBSET t ==> ~(s = {}) ==> ~(t = {})`)) THEN
     ASM_REWRITE_TAC[BALL_EQ_EMPTY; GSYM REAL_NOT_LT];
     ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM))
  THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `b SUBSET s ==> b' SUBSET IMAGE f b ==> b' SUBSET IMAGE f s`)) THEN
    REWRITE_TAC[IN_BALL; SUBSET; NORM_ARITH `dist(vec 0,x) = norm x`;
                IN_IMAGE] THEN
    ASM_SIMP_TAC[STRETCH_GALOIS; REAL_INV_EQ_0; UNWIND_THM1; REAL_INV_INV] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC
     `norm(sup(IMAGE(\k. abs(m k)) (1..dimindex(:N))) % x:real^N)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NORM_LE_COMPONENTWISE THEN
      SIMP_TAC[LAMBDA_BETA; VECTOR_MUL_COMPONENT; REAL_ABS_MUL] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= abs y`) THEN
      ASM_SIMP_TAC[REAL_LE_SUP_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY;
                  NUMSEG_EMPTY; FINITE_NUMSEG; GSYM NOT_LE; DIMINDEX_GE_1] THEN
      REWRITE_TAC[EXISTS_IN_IMAGE; IN_NUMSEG] THEN ASM_MESON_TAC[REAL_LE_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[NORM_MUL] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `abs(sup(IMAGE(\k. abs(m k)) (1..dimindex(:N)))) * B` THEN
    SUBGOAL_THEN `&0 < sup(IMAGE(\k. abs(m k)) (1..dimindex(:N)))`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_SUP_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY;
                  NUMSEG_EMPTY; FINITE_NUMSEG; GSYM NOT_LE; DIMINDEX_GE_1] THEN
      REWRITE_TAC[EXISTS_IN_IMAGE; GSYM REAL_ABS_NZ; IN_NUMSEG] THEN
      ASM_MESON_TAC[DIMINDEX_GE_1; LE_REFL];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_ARITH `&0 < x ==> &0 < abs x`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sup(IMAGE(\k. abs(m k)) (1..dimindex(:N))) * B` THEN
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ; REAL_ARITH `&0 < x ==> abs x <= x`] THEN
    ASM_SIMP_TAC[REAL_LE_SUP_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY;
                  NUMSEG_EMPTY; FINITE_NUMSEG; GSYM NOT_LE; DIMINDEX_GE_1] THEN
    ASM_SIMP_TAC[EXISTS_IN_IMAGE; REAL_LE_RMUL_EQ] THEN
    ASM_SIMP_TAC[REAL_SUP_LE_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY;
                 NUMSEG_EMPTY; FINITE_NUMSEG; GSYM NOT_LE; DIMINDEX_GE_1] THEN
    MP_TAC(ISPEC `IMAGE (\k. abs (m k)) (1..dimindex(:N))` SUP_FINITE) THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; IMAGE_EQ_EMPTY; NUMSEG_EMPTY;
                 GSYM NOT_LE; DIMINDEX_GE_1] THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];

    MATCH_MP_TAC(MESON[]
     `s = t /\ P z ==> (f has_integral z) s ==> Q
                       ==> ?w. (f has_integral w) t /\ P w`) THEN
    SIMP_TAC[GSYM PRODUCT_INV; FINITE_NUMSEG; GSYM REAL_ABS_INV] THEN
    REWRITE_TAC[REAL_INV_INV] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC(SET_RULE
       `(!x. f x = x) ==> IMAGE f s = s`) THEN
      SIMP_TAC[o_THM; LAMBDA_BETA; CART_EQ] THEN
      ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_MUL_LID];
      REWRITE_TAC[ABS_DROP; DROP_SUB; LIFT_DROP; DROP_CMUL] THEN
      REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; ETA_AX] THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_ABS] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ] THEN
      ASM_MESON_TAC[ABS_DROP; DROP_SUB; LIFT_DROP]]]);;

let HAS_MEASURE_TRANSLATION = prove
 (`!s m a. s has_measure m ==> (IMAGE (\x:real^N. a + x) s) has_measure m`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `&1`; `a:real^N`; `m:real`]
                HAS_MEASURE_AFFINITY) THEN
  REWRITE_TAC[VECTOR_MUL_LID; REAL_ABS_NUM; REAL_POW_ONE; REAL_MUL_LID] THEN
  REWRITE_TAC[VECTOR_ADD_SYM]);;

let NEGLIGIBLE_TRANSLATION = prove
 (`!s a. negligible s ==> negligible (IMAGE (\x:real^N. a + x) s)`,
  SIMP_TAC[GSYM HAS_MEASURE_0; HAS_MEASURE_TRANSLATION]);;

let HAS_MEASURE_TRANSLATION_EQ = prove
 (`!a s m. (IMAGE (\x:real^N. a + x) s) has_measure m <=> s has_measure m`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[HAS_MEASURE_TRANSLATION] THEN
  DISCH_THEN(MP_TAC o SPEC `--a:real^N` o
    MATCH_MP HAS_MEASURE_TRANSLATION) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; VECTOR_ARITH `--a + a + b:real^N = b`] THEN
  SET_TAC[]);;

add_translation_invariants [HAS_MEASURE_TRANSLATION_EQ];;

let MEASURE_TRANSLATION = prove
 (`!a s. measure(IMAGE (\x:real^N. a + x) s) = measure s`,
  REWRITE_TAC[measure; HAS_MEASURE_TRANSLATION_EQ]);;

add_translation_invariants [MEASURE_TRANSLATION];;

let NEGLIGIBLE_TRANSLATION_REV = prove
 (`!s a. negligible (IMAGE (\x:real^N. a + x) s) ==> negligible s`,
  SIMP_TAC[GSYM HAS_MEASURE_0; HAS_MEASURE_TRANSLATION_EQ]);;

let NEGLIGIBLE_TRANSLATION_EQ = prove
 (`!a s. negligible (IMAGE (\x:real^N. a + x) s) <=> negligible s`,
  SIMP_TAC[GSYM HAS_MEASURE_0; HAS_MEASURE_TRANSLATION_EQ]);;

add_translation_invariants [NEGLIGIBLE_TRANSLATION_EQ];;

let MEASURABLE_TRANSLATION_EQ = prove
 (`!a:real^N s. measurable (IMAGE (\x. a + x) s) <=> measurable s`,
  REWRITE_TAC[measurable; HAS_MEASURE_TRANSLATION_EQ]);;

add_translation_invariants [MEASURABLE_TRANSLATION_EQ];;

let MEASURABLE_TRANSLATION = prove
 (`!s a:real^N. measurable s ==> measurable (IMAGE (\x. a + x) s)`,
  REWRITE_TAC[MEASURABLE_TRANSLATION_EQ]);;

let HAS_MEASURE_SCALING = prove
 (`!s m c. s has_measure m
           ==> (IMAGE (\x:real^N. c % x) s) has_measure
               (abs(c) pow dimindex(:N)) * m`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `c:real`; `vec 0:real^N`; `m:real`]
                HAS_MEASURE_AFFINITY) THEN
  REWRITE_TAC[VECTOR_ADD_RID]);;

let HAS_MEASURE_SCALING_EQ = prove
 (`!s m c. ~(c = &0)
           ==> (IMAGE (\x:real^N. c % x) s
                  has_measure (abs(c) pow dimindex(:N)) * m <=>
                s has_measure m)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC[HAS_MEASURE_SCALING] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(c)` o MATCH_MP HAS_MEASURE_SCALING) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; GSYM REAL_ABS_MUL] THEN
  REWRITE_TAC[GSYM REAL_POW_MUL; VECTOR_MUL_ASSOC; REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[GSYM REAL_ABS_MUL; REAL_MUL_LINV] THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_ABS_NUM; REAL_MUL_LID; VECTOR_MUL_LID] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN SET_TAC[]);;

let MEASURABLE_SCALING = prove
 (`!s c. measurable s ==> measurable (IMAGE (\x:real^N. c % x) s)`,
  REWRITE_TAC[measurable] THEN MESON_TAC[HAS_MEASURE_SCALING]);;

let MEASURABLE_SCALING_EQ = prove
 (`!s c. ~(c = &0)
         ==> (measurable (IMAGE (\x:real^N. c % x) s) <=> measurable s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC[MEASURABLE_SCALING] THEN
  DISCH_THEN(MP_TAC o SPEC `inv c` o MATCH_MP MEASURABLE_SCALING) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; GSYM REAL_ABS_MUL] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID] THEN
  SET_TAC[]);;

let MEASURE_SCALING = prove
 (`!s. measurable s
       ==> measure(IMAGE (\x:real^N. c % x) s) =
              (abs(c) pow dimindex(:N)) * measure s`,
  REWRITE_TAC[HAS_MEASURE_MEASURE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURE_UNIQUE THEN ASM_SIMP_TAC[HAS_MEASURE_SCALING]);;

(* ------------------------------------------------------------------------- *)
(* Measurability of countable unions and intersections of various kinds.     *)
(* ------------------------------------------------------------------------- *)

let HAS_MEASURE_NESTED_UNIONS = prove
 (`!s:num->real^N->bool B.
        (!n. measurable(s n)) /\
        (!n. measure(s n) <= B) /\
        (!n. s(n) SUBSET s(SUC n))
        ==> measurable(UNIONS { s(n) | n IN (:num) }) /\
            ((\n. lift(measure(s n)))
                  --> lift(measure(UNIONS { s(n) | n IN (:num) })))
            sequentially`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[TAUT `a ==> b /\ c <=> (a ==> b /\ (b ==> c))`] THEN
  SIMP_TAC[MEASURE_INTEGRAL_UNIV; LIFT_DROP] THEN
  REWRITE_TAC[MEASURABLE_INTEGRABLE] THEN
  STRIP_TAC THEN MATCH_MP_TAC(TAUT `b /\ c ==> b /\ (b ==> c)`) THEN
  MATCH_MP_TAC MONOTONE_CONVERGENCE_INCREASING THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    REWRITE_TAC[DROP_VEC; REAL_POS; REAL_LE_REFL] THEN ASM SET_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN COND_CASES_TAC THENL
     [MATCH_MP_TAC LIM_EVENTUALLY THEN
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_UNIONS]) THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN REWRITE_TAC[EXISTS_IN_IMAGE] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN STRIP_TAC THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o PART_MATCH (rand o rand)
                  TRANSITIVE_STEPWISE_LE_EQ o concl) THEN
      ASM_REWRITE_TAC[SUBSET_TRANS; SUBSET_REFL] THEN ASM SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [IN_UNIONS]) THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN REWRITE_TAC[EXISTS_IN_IMAGE] THEN
      SIMP_TAC[NOT_EXISTS_THM; IN_UNIV; LIM_CONST]];
     RULE_ASSUM_TAC(REWRITE_RULE[GSYM MEASURABLE_INTEGRABLE]) THEN
     ASM_SIMP_TAC[INTEGRAL_MEASURE_UNIV] THEN
     REWRITE_TAC[bounded; SIMPLE_IMAGE; FORALL_IN_IMAGE] THEN
     EXISTS_TAC `B:real` THEN REWRITE_TAC[IN_UNIV; NORM_LIFT] THEN
     REWRITE_TAC[real_abs] THEN ASM_MESON_TAC[MEASURE_POS_LE]]);;

let MEASURABLE_NESTED_UNIONS = prove
 (`!s:num->real^N->bool B.
        (!n. measurable(s n)) /\
        (!n. measure(s n) <= B) /\
        (!n. s(n) SUBSET s(SUC n))
        ==> measurable(UNIONS { s(n) | n IN (:num) })`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_MEASURE_NESTED_UNIONS) THEN
  SIMP_TAC[]);;

let HAS_MEASURE_COUNTABLE_NEGLIGIBLE_UNIONS = prove
 (`!s:num->real^N->bool B.
        (!n. measurable(s n)) /\
        (!m n. ~(m = n) ==> negligible(s m INTER s n)) /\
        (!n. sum (0..n) (\k. measure(s k)) <= B)
        ==> measurable(UNIONS { s(n) | n IN (:num) }) /\
            ((\n. lift(measure(s n))) sums
             lift(measure(UNIONS { s(n) | n IN (:num) }))) (from 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\n. UNIONS (IMAGE s (0..n)):real^N->bool`; `B:real`]
               HAS_MEASURE_NESTED_UNIONS) THEN
  REWRITE_TAC[sums; FROM_0; INTER_UNIV] THEN
  SUBGOAL_THEN
   `!n. (UNIONS (IMAGE s (0..n)):real^N->bool) has_measure
        (sum(0..n) (\k. measure(s k)))`
  MP_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC HAS_MEASURE_NEGLIGIBLE_UNIONS_IMAGE THEN
    ASM_SIMP_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    ASSUME_TAC(GEN `n:num` (MATCH_MP MEASURE_UNIQUE (SPEC `n:num` th)))) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[measurable]; ALL_TAC] THEN
    GEN_TAC THEN MATCH_MP_TAC SUBSET_UNIONS THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[LIFT_SUM; FINITE_NUMSEG; o_DEF] THEN
  SUBGOAL_THEN
   `UNIONS {UNIONS (IMAGE s (0..n)) | n IN (:num)}:real^N->bool =
    UNIONS (IMAGE s (:num))`
   (fun th -> REWRITE_TAC[th] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
              REWRITE_TAC[]) THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_UNIONS] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; EXISTS_IN_UNIONS; IN_UNIV] THEN
  REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN
  REWRITE_TAC[IN_NUMSEG; LE_0] THEN MESON_TAC[LE_REFL]);;

let NEGLIGIBLE_COUNTABLE_UNIONS = prove
 (`!s:num->real^N->bool.
        (!n. negligible(s n)) ==> negligible(UNIONS {s(n) | n IN (:num)})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:num->real^N->bool`; `&0`]
    HAS_MEASURE_COUNTABLE_NEGLIGIBLE_UNIONS) THEN
  ASM_SIMP_TAC[MEASURE_EQ_0; SUM_0; REAL_LE_REFL; LIFT_NUM] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[HAS_MEASURE_0; measurable; INTER_SUBSET; NEGLIGIBLE_SUBSET];
    ALL_TAC] THEN
  SIMP_TAC[GSYM MEASURABLE_MEASURE_EQ_0] THEN
  STRIP_TAC THEN REWRITE_TAC[GSYM LIFT_EQ] THEN
  MATCH_MP_TAC SERIES_UNIQUE THEN REWRITE_TAC[LIFT_NUM] THEN
  MAP_EVERY EXISTS_TAC [`(\k. vec 0):num->real^1`; `from 0`] THEN
  ASM_REWRITE_TAC[SERIES_0]);;

let HAS_MEASURE_COUNTABLE_NEGLIGIBLE_UNIONS_BOUNDED = prove
 (`!s:num->real^N->bool.
        (!n. measurable(s n)) /\
        (!m n. ~(m = n) ==> negligible(s m INTER s n)) /\
        bounded(UNIONS { s(n) | n IN (:num) })
        ==> measurable(UNIONS { s(n) | n IN (:num) }) /\
            ((\n. lift(measure(s n))) sums
             lift(measure(UNIONS { s(n) | n IN (:num) }))) (from 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
  MATCH_MP_TAC HAS_MEASURE_COUNTABLE_NEGLIGIBLE_UNIONS THEN
  EXISTS_TAC `measure(interval[a:real^N,b])` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `measure(UNIONS (IMAGE (s:num->real^N->bool) (0..n)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC MEASURE_NEGLIGIBLE_UNIONS_IMAGE THEN
    ASM_SIMP_TAC[FINITE_NUMSEG];
    MATCH_MP_TAC MEASURE_SUBSET THEN REWRITE_TAC[MEASURABLE_INTERVAL] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_UNIONS THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; FORALL_IN_IMAGE];
      ASM SET_TAC[]]]);;

let MEASURABLE_COUNTABLE_UNIONS_BOUNDED = prove
 (`!s:num->real^N->bool.
        (!n. measurable(s n)) /\
        bounded(UNIONS { s(n) | n IN (:num) })
        ==> measurable(UNIONS { s(n) | n IN (:num) })`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `UNIONS { s(n):real^N->bool | n IN (:num) } =
    UNIONS { UNIONS {s(m) | m IN 0..n} | n IN (:num)}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; UNWIND_THM2; IN_UNIONS; IN_ELIM_THM] THEN
    REWRITE_TAC[IN_NUMSEG; IN_UNIV; LE_0] THEN MESON_TAC[LE_REFL];
    MATCH_MP_TAC MEASURABLE_NESTED_UNIONS THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
    EXISTS_TAC `measure(interval[a:real^N,b])` THEN
    MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC MEASURABLE_UNIONS THEN
      ASM_SIMP_TAC[FORALL_IN_GSPEC] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG];
      DISCH_TAC] THEN
    CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_REWRITE_TAC[MEASURABLE_INTERVAL] THEN ASM SET_TAC[];
      GEN_TAC THEN REWRITE_TAC[NUMSEG_CLAUSES; LE_0] THEN SET_TAC[]]]);;

let MEASURE_COUNTABLE_UNIONS_LE_STRONG = prove
 (`!d:num->(real^N->bool) B.
        (!n. measurable(d n)) /\
        (!n. measure(UNIONS {d k | k <= n}) <= B)
        ==> measurable(UNIONS {d n | n IN (:num)}) /\
            measure(UNIONS {d n | n IN (:num)}) <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\n. UNIONS {(d:num->(real^N->bool)) k | k IN (0..n)}`;
                 `B:real`]
         HAS_MEASURE_NESTED_UNIONS) THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `UNIONS {UNIONS {d k | k IN (0..n)} | n IN (:num)} =
                UNIONS {d n:real^N->bool | n IN (:num)}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV; IN_NUMSEG; LE_0] THEN
    MESON_TAC[LE_REFL];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC MEASURABLE_UNIONS THEN
      SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FINITE_NUMSEG] THEN
      ASM_REWRITE_TAC[FORALL_IN_IMAGE];
      ASM_REWRITE_TAC[IN_NUMSEG; LE_0];
      GEN_TAC THEN REWRITE_TAC[SIMPLE_IMAGE] THEN
      MATCH_MP_TAC SUBSET_UNIONS THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET_NUMSEG] THEN ARITH_TAC];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM(CONJUNCT2 LIFT_DROP)] THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_DROP_LE) THEN
    EXISTS_TAC `\n. lift(measure(UNIONS {d k | k IN 0..n} :real^N->bool))` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[LIFT_DROP; IN_NUMSEG; LE_0]]);;

let MEASURE_COUNTABLE_UNIONS_LE = prove
 (`!d:num->(real^N->bool) B.
        (!n. measurable(d n)) /\
        (!n. sum(0..n) (\k. measure(d k)) <= B)
        ==> measurable(UNIONS {d n | n IN (:num)}) /\
            measure(UNIONS {d n | n IN (:num)}) <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE_STRONG THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN
  MP_TAC(ISPECL [`0..n`;`d:num->real^N->bool`] MEASURE_UNIONS_LE_IMAGE) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  REPEAT(FIRST_X_ASSUM (MP_TAC o SPEC `n:num`)) THEN
  REWRITE_TAC[GSYM SIMPLE_IMAGE; numseg; LE_0; IN_ELIM_THM] THEN
  MESON_TAC[REAL_LE_TRANS]);;

let MEASURABLE_COUNTABLE_UNIONS_STRONG = prove
 (`!s:num->real^N->bool B.
        (!n. measurable(s n)) /\
        (!n. measure(UNIONS {s k | k <= n}) <= B)
        ==> measurable(UNIONS { s(n) | n IN (:num) })`,
  MESON_TAC[MEASURE_COUNTABLE_UNIONS_LE_STRONG; REAL_LE_REFL]);;

let MEASURABLE_COUNTABLE_UNIONS = prove
 (`!s:num->real^N->bool B.
        (!n. measurable(s n)) /\
        (!n. sum (0..n) (\k. measure(s k)) <= B)
        ==> measurable(UNIONS { s(n) | n IN (:num) })`,
  MESON_TAC[MEASURE_COUNTABLE_UNIONS_LE; REAL_LE_REFL]);;

let MEASURABLE_COUNTABLE_INTERS = prove
 (`!s:num->real^N->bool.
        (!n. measurable(s n))
        ==> measurable(INTERS { s(n) | n IN (:num) })`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `INTERS { s(n):real^N->bool | n IN (:num) } =
                s 0 DIFF (UNIONS {s 0 DIFF s n | n IN (:num)})`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_INTERS; IN_DIFF; IN_UNIONS] THEN
    REWRITE_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_DIFF THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MEASURABLE_COUNTABLE_UNIONS_STRONG THEN
  EXISTS_TAC `measure(s 0:real^N->bool)` THEN
  ASM_SIMP_TAC[MEASURABLE_DIFF; LE_0] THEN
  GEN_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_UNIONS; IN_ELIM_THM; IN_DIFF] THEN
    MESON_TAC[IN_DIFF]] THEN
  ONCE_REWRITE_TAC[GSYM IN_NUMSEG_0] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; FINITE_IMAGE; FINITE_NUMSEG;
               MEASURABLE_DIFF; MEASURABLE_UNIONS]);;

let NEGLIGIBLE_COUNTABLE = prove
 (`!s:real^N->bool. COUNTABLE s ==> negligible s`,
  let lemma = prove
   (`IMAGE f s = UNIONS {{f x} | x IN s}`,
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIONS; IN_SING; IN_ELIM_THM] THEN
    MESON_TAC[IN_SING]) in
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[NEGLIGIBLE_EMPTY] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->real^N` SUBST1_TAC o
    MATCH_MP COUNTABLE_AS_IMAGE) THEN
  ONCE_REWRITE_TAC[lemma] THEN MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS THEN
  REWRITE_TAC[NEGLIGIBLE_SING]);;

(* ------------------------------------------------------------------------- *)
(* A sledgehammer to crack a nut, but we get uncountability of R trivially.  *)
(* ------------------------------------------------------------------------- *)

let COUNTABLE_OPEN_INTERVAL = prove
 (`!a b. COUNTABLE(interval(a,b)) <=> interval(a,b) = {}`,
  MESON_TAC[COUNTABLE_EMPTY; NEGLIGIBLE_INTERVAL; NEGLIGIBLE_COUNTABLE]);;

let UNCOUNTABLE_INTERVAL = prove
 (`(!a b. ~(interval(a,b) = {}) ==> ~COUNTABLE(interval[a,b])) /\
   (!a b. ~(interval(a,b) = {}) ==> ~COUNTABLE(interval(a,b)))`,
  REWRITE_TAC[GSYM COUNTABLE_OPEN_INTERVAL] THEN
  MESON_TAC[INTERVAL_OPEN_SUBSET_CLOSED; COUNTABLE_SUBSET]);;

let UNCOUNTABLE_EUCLIDEAN = prove
 (`~COUNTABLE(:real^N)`,
  MP_TAC(ISPECL [`vec 0:real^N`; `vec 1:real^N`] COUNTABLE_OPEN_INTERVAL) THEN
  REWRITE_TAC[INTERVAL_EQ_EMPTY; VEC_COMPONENT] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT; REAL_LT_01; CONTRAPOS_THM] THEN
  MESON_TAC[COUNTABLE_SUBSET; SUBSET_UNIV]);;

let UNCOUNTABLE_REAL = prove
 (`~COUNTABLE(:real)`,
  DISCH_THEN(MP_TAC o ISPEC `lift` o MATCH_MP COUNTABLE_IMAGE) THEN
  MP_TAC(ISPECL [`vec 0:real^1`; `vec 1:real^1`] COUNTABLE_OPEN_INTERVAL) THEN
  REWRITE_TAC[INTERVAL_EQ_EMPTY_1; DROP_VEC; GSYM REAL_NOT_LT; REAL_LT_01] THEN
  REWRITE_TAC[CONTRAPOS_THM] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] COUNTABLE_SUBSET) THEN
  REWRITE_TAC[SUBSET; FORALL_LIFT; LIFT_IN_IMAGE_LIFT; IN_UNIV]);;

let UNCOUNTABLE_SEGMENT = prove
 (`(!a b:real^N. ~(a = b) ==> ~COUNTABLE(segment[a,b])) /\
   (!a b:real^N. ~(a = b) ==> ~COUNTABLE(segment(a,b)))`,
  REWRITE_TAC[open_segment] THEN
  SIMP_TAC[FINITE_INSERT; FINITE_EMPTY; COUNTABLE_DIFF_FINITE] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
  REWRITE_TAC[segment; SIMPLE_IMAGE] THEN
  MP_TAC(ISPECL [`vec 0:real^1`; `vec 1:real^1`] (CONJUNCT1
   UNCOUNTABLE_INTERVAL)) THEN
  REWRITE_TAC[INTERVAL_EQ_EMPTY_1; VEC_COMPONENT; DROP_VEC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT; REAL_LT_01; COUNTABLE; ge_c] THEN
  REWRITE_TAC[CARD_NOT_LE] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CARD_LTE_TRANS) THEN
  REWRITE_TAC[le_c; REAL_NOT_LT; IN_INTERVAL_1] THEN
  EXISTS_TAC `\u. (&1 - drop u) % (a:real^N) + drop u % b` THEN
  REWRITE_TAC[IN_ELIM_THM; LIFT_DROP; FORALL_LIFT; DROP_VEC] THEN
  CONJ_TAC THENL [MESON_TAC[]; REWRITE_TAC[LIFT_EQ]] THEN
  ASM_SIMP_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ; REAL_SUB_0; VECTOR_ARITH
   `(&1 - x) % a + x % b:real^N = (&1 - y) % a + y % b <=>
    (x - y) % (a - b) = vec 0`]);;

let UNCOUNTABLE_CONVEX = prove
 (`!s a b:real^N.
        convex s /\ a IN s /\ b IN s /\ ~(a = b) ==> ~COUNTABLE s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~COUNTABLE(segment[a:real^N,b])` MP_TAC THENL
   [ASM_SIMP_TAC[UNCOUNTABLE_SEGMENT]; REWRITE_TAC[CONTRAPOS_THM]] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] COUNTABLE_SUBSET) THEN
  ASM_MESON_TAC[CONVEX_CONTAINS_SEGMENT]);;

(* ------------------------------------------------------------------------- *)
(* Measurability of compact and bounded open sets.                           *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_COMPACT = prove
 (`!s:real^N->bool. compact s ==> measurable s`,
  let lemma = prove
   (`!f s:real^N->bool.
          (!n. FINITE(f n)) /\
          (!n. s SUBSET UNIONS(f n)) /\
          (!x. ~(x IN s) ==> ?n. ~(x IN UNIONS(f n))) /\
          (!n a. a IN f(SUC n) ==> ?b. b IN f(n) /\ a SUBSET b) /\
          (!n a. a IN f(n) ==> measurable a)
          ==> measurable s`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `!n. UNIONS(f(SUC n):(real^N->bool)->bool) SUBSET UNIONS(f n)`
    ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `s = INTERS { UNIONS(f n) | n IN (:num) }:real^N->bool`
    SUBST1_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
      REWRITE_TAC[SUBSET; IN_INTERS; FORALL_IN_IMAGE; IN_UNIV] THEN
      REWRITE_TAC[IN_IMAGE] THEN ASM SET_TAC[];
      MATCH_MP_TAC MEASURABLE_COUNTABLE_INTERS THEN
      ASM_REWRITE_TAC[] THEN GEN_TAC THEN
      MATCH_MP_TAC MEASURABLE_UNIONS THEN
      ASM_MESON_TAC[]]) in
  REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma THEN
  EXISTS_TAC
   `\n. { k | ?u:real^N. (!i. 1 <= i /\ i <= dimindex(:N)
                              ==> integer(u$i)) /\
                  k = { x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                                       ==> u$i / &2 pow n <= x$i /\
                                           x$i < (u$i + &1) / &2 pow n } /\
                  ~(s INTER k = {})}` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_LT_POW2] THEN
    SUBGOAL_THEN
     `?N. !x:real^N i. x IN s /\ 1 <= i /\ i <= dimindex(:N)
                       ==> abs(x$i * &2 pow n) < &N`
    STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
      REWRITE_TAC[BOUNDED_POS; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `B:real` THEN STRIP_TAC THEN
      MP_TAC(SPEC `B * &2 pow n` (MATCH_MP REAL_ARCH REAL_LT_01)) THEN
      MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[REAL_MUL_RID] THEN
      X_GEN_TAC `N:num` THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_NUM] THEN
      SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_LT_POW2] THEN
      ASM_MESON_TAC[COMPONENT_LE_NORM; REAL_LE_TRANS; REAL_LET_TRANS];
      ALL_TAC] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC
     `IMAGE (\u. {x | !i. 1 <= i /\ i <= dimindex(:N)
                          ==> (u:real^N)$i <= (x:real^N)$i * &2 pow n /\
                              x$i * &2 pow n < u$i + &1})
            {u | !i. 1 <= i /\ i <= dimindex(:N) ==> integer (u$i) /\
                                                     abs(u$i) <= &N}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_CART THEN
      REWRITE_TAC[GSYM REAL_BOUNDS_LE; FINITE_INTSEG];
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN
      X_GEN_TAC `l:real^N->bool` THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^N` THEN
      STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[] THEN
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_REVERSE_INTEGERS THEN
      ASM_SIMP_TAC[INTEGER_CLOSED] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^N` MP_TAC) THEN
      REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `k:num`)) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `k:num`]) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    X_GEN_TAC `n:num` THEN REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    EXISTS_TAC `(lambda i. floor(&2 pow n * (x:real^N)$i)):real^N` THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b /\ c) /\ d <=> b /\ a /\ c /\ d`] THEN
    REWRITE_TAC[UNWIND_THM2] THEN SIMP_TAC[LAMBDA_BETA; FLOOR] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN EXISTS_TAC `x:real^N` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_LT_POW2] THEN
    REWRITE_TAC[REAL_MUL_SYM; FLOOR];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_CLOSED) THEN
    REWRITE_TAC[closed; open_def] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [`inv(&2)`; `e / &(dimindex(:N))`] REAL_ARCH_POW_INV) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_RDIV_EQ; REAL_OF_NUM_LT;
                 DIMINDEX_GE_1; ARITH_RULE `0 < x <=> 1 <= x`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b /\ c) /\ d <=> b /\ a /\ c /\ d`] THEN
    REWRITE_TAC[UNWIND_THM2] THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
    X_GEN_TAC `u:real^N` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC o CONJUNCT2) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N`
     (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `d < e ==> x <= d ==> x < e`)) THEN
    REWRITE_TAC[dist] THEN
    W(MP_TAC o PART_MATCH lhand NORM_LE_L1 o lhand o snd) THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    GEN_REWRITE_TAC (funpow 3 RAND_CONV) [GSYM CARD_NUMSEG_1] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_MP_TAC SUM_BOUND THEN
    SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; VECTOR_SUB_COMPONENT] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `k:num`)) THEN
    ASM_REWRITE_TAC[real_div; REAL_ADD_RDISTRIB] THEN
    REWRITE_TAC[REAL_MUL_LID; GSYM REAL_POW_INV] THEN REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`n:num`; `a:real^N->bool`] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N`
     (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b /\ c) /\ d <=> b /\ a /\ c /\ d`] THEN
    REWRITE_TAC[UNWIND_THM2] THEN
    EXISTS_TAC `(lambda i. floor((u:real^N)$i / &2)):real^N` THEN
    ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; LAMBDA_BETA; FLOOR] THEN
    MATCH_MP_TAC(SET_RULE `~(s INTER a = {}) /\ a SUBSET b
                           ==> ~(s INTER b = {}) /\ a SUBSET b`) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "a" THEN REWRITE_TAC[SUBSET] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k:num` THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_pow; real_div; REAL_INV_MUL; REAL_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM real_div] THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_LT_POW2] THEN
    MP_TAC(SPEC `(u:real^N)$k / &2` FLOOR) THEN
    REWRITE_TAC[REAL_ARITH `u / &2 < floor(u / &2) + &1 <=>
                            u < &2 * floor(u / &2) + &2`] THEN
    ASM_SIMP_TAC[REAL_LT_INTEGERS; INTEGER_CLOSED; FLOOR_FRAC] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `a:real^N->bool`; `u:real^N`] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1 o CONJUNCT2) THEN
    ONCE_REWRITE_TAC[MEASURABLE_INNER_OUTER] THEN
    GEN_TAC THEN DISCH_TAC THEN
    EXISTS_TAC `interval(inv(&2 pow n) % u:real^N,
                         inv(&2 pow n) % (u + vec 1))` THEN
    EXISTS_TAC `interval[inv(&2 pow n) % u:real^N,
                         inv(&2 pow n) % (u + vec 1)]` THEN
    REWRITE_TAC[MEASURABLE_INTERVAL; MEASURE_INTERVAL] THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN
    REWRITE_TAC[SUBSET; IN_INTERVAL; IN_ELIM_THM] THEN
    CONJ_TAC THEN X_GEN_TAC `y:real^N` THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k:num` THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; VECTOR_ADD_COMPONENT;
                 VEC_COMPONENT] THEN
    REAL_ARITH_TAC]);;

let MEASURABLE_OPEN = prove
 (`!s:real^N->bool. bounded s /\ open s ==> measurable s`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (SET_RULE
   `s SUBSET t ==> s = t DIFF (t DIFF s)`)) THEN
  MATCH_MP_TAC MEASURABLE_DIFF THEN
  REWRITE_TAC[MEASURABLE_INTERVAL] THEN
  MATCH_MP_TAC MEASURABLE_COMPACT THEN
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED; BOUNDED_DIFF; BOUNDED_INTERVAL] THEN
  MATCH_MP_TAC CLOSED_DIFF THEN ASM_REWRITE_TAC[CLOSED_INTERVAL]);;

let MEASURABLE_CLOSURE = prove
 (`!s. bounded s ==> measurable(closure s)`,
  SIMP_TAC[MEASURABLE_COMPACT; COMPACT_EQ_BOUNDED_CLOSED; CLOSED_CLOSURE;
           BOUNDED_CLOSURE]);;

let MEASURABLE_INTERIOR = prove
 (`!s. bounded s ==> measurable(interior s)`,
  SIMP_TAC[MEASURABLE_OPEN; OPEN_INTERIOR; BOUNDED_INTERIOR]);;

let MEASURABLE_FRONTIER = prove
 (`!s:real^N->bool. bounded s ==> measurable(frontier s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[frontier] THEN
  MATCH_MP_TAC MEASURABLE_DIFF THEN
  ASM_SIMP_TAC[MEASURABLE_CLOSURE; MEASURABLE_INTERIOR] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:real^N->bool` THEN
  REWRITE_TAC[INTERIOR_SUBSET; CLOSURE_SUBSET]);;

let MEASURE_FRONTIER = prove
 (`!s:real^N->bool.
        bounded s
        ==> measure(frontier s) = measure(closure s) - measure(interior s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[frontier] THEN
  MATCH_MP_TAC MEASURE_DIFF_SUBSET THEN
  ASM_SIMP_TAC[MEASURABLE_CLOSURE; MEASURABLE_INTERIOR] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:real^N->bool` THEN
  REWRITE_TAC[INTERIOR_SUBSET; CLOSURE_SUBSET]);;

let MEASURE_CLOSURE = prove
 (`!s:real^N->bool.
        bounded s /\ negligible(frontier s)
        ==> measure(closure s) = measure s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_NEGLIGIBLE_SYMDIFF THEN
  ASM_SIMP_TAC[MEASURABLE_CLOSURE] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    NEGLIGIBLE_SUBSET)) THEN
  MP_TAC(ISPEC `s:real^N->bool` INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `s:real^N->bool` CLOSURE_SUBSET) THEN
  REWRITE_TAC[frontier] THEN SET_TAC[]);;

let MEASURE_INTERIOR = prove
 (`!s:real^N->bool.
        bounded s /\ negligible(frontier s)
        ==> measure(interior s) = measure s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_NEGLIGIBLE_SYMDIFF THEN
  ASM_SIMP_TAC[MEASURABLE_INTERIOR] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    NEGLIGIBLE_SUBSET)) THEN
  MP_TAC(ISPEC `s:real^N->bool` INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `s:real^N->bool` CLOSURE_SUBSET) THEN
  REWRITE_TAC[frontier] THEN SET_TAC[]);;

let MEASURABLE_JORDAN = prove
 (`!s:real^N->bool. bounded s /\ negligible(frontier s) ==> measurable s`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[MEASURABLE_INNER_OUTER] THEN
  GEN_TAC THEN DISCH_TAC THEN
  EXISTS_TAC `interior(s):real^N->bool` THEN
  EXISTS_TAC `closure(s):real^N->bool` THEN
  ASM_SIMP_TAC[MEASURABLE_INTERIOR; MEASURABLE_CLOSURE] THEN
  REWRITE_TAC[INTERIOR_SUBSET; CLOSURE_SUBSET] THEN
  ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
  ASM_SIMP_TAC[GSYM MEASURE_FRONTIER; REAL_ABS_NUM; MEASURE_EQ_0]);;

let HAS_MEASURE_ELEMENTARY = prove
 (`!d s. d division_of s ==> s has_measure (sum d content)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_measure] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  ASM_SIMP_TAC[LIFT_SUM] THEN
  MATCH_MP_TAC HAS_INTEGRAL_COMBINE_DIVISION THEN
  ASM_REWRITE_TAC[o_THM] THEN REWRITE_TAC[GSYM has_measure] THEN
  ASM_MESON_TAC[HAS_MEASURE_INTERVAL; division_of]);;

let MEASURABLE_ELEMENTARY = prove
 (`!d s. d division_of s ==> measurable s`,
  REWRITE_TAC[measurable] THEN MESON_TAC[HAS_MEASURE_ELEMENTARY]);;

let MEASURE_ELEMENTARY = prove
 (`!d s. d division_of s ==> measure s = sum d content`,
  MESON_TAC[HAS_MEASURE_ELEMENTARY; MEASURE_UNIQUE]);;

let MEASURABLE_INTER_INTERVAL = prove
 (`!s a b:real^N. measurable s ==> measurable (s INTER interval[a,b])`,
  SIMP_TAC[MEASURABLE_INTER; MEASURABLE_INTERVAL]);;

(* ------------------------------------------------------------------------- *)
(* A nice lemma for negligibility proofs.                                    *)
(* ------------------------------------------------------------------------- *)

let STARLIKE_NEGLIGIBLE_BOUNDED_MEASURABLE = prove
 (`!s. measurable s /\ bounded s /\
       (!c x:real^N. &0 <= c /\ x IN s /\ (c % x) IN s ==> c = &1)
       ==> negligible s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(&0 < measure(s:real^N->bool))`
   (fun th -> ASM_MESON_TAC[th; MEASURABLE_MEASURE_POS_LT]) THEN
  DISCH_TAC THEN
  MP_TAC(SPEC `(vec 0:real^N) INSERT s`
      BOUNDED_SUBSET_CLOSED_INTERVAL_SYMMETRIC) THEN
  ASM_SIMP_TAC[BOUNDED_INSERT; COMPACT_IMP_BOUNDED; NOT_EXISTS_THM] THEN
  X_GEN_TAC `a:real^N` THEN REWRITE_TAC[INSERT_SUBSET] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?N. EVEN N /\ &0 < &N /\
        measure(interval[--a:real^N,a])
         < (&N * measure(s:real^N->bool)) / &4 pow dimindex (:N)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC
     `measure(interval[--a:real^N,a]) * &4 pow (dimindex(:N))` o
     MATCH_MP REAL_ARCH) THEN
    SIMP_TAC[REAL_LT_RDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
    SIMP_TAC[GSYM REAL_LT_LDIV_EQ; ASSUME `&0 < measure(s:real^N->bool)`] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `2 * (N DIV 2 + 1)` THEN REWRITE_TAC[EVEN_MULT; ARITH] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x < a ==> a <= b ==> x < b`)) THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS (IMAGE (\m. IMAGE (\x:real^N. (&m / &N) % x) s)
                                (1..N))`;
                  `interval[--a:real^N,a]`] MEASURE_SUBSET) THEN
  MP_TAC(ISPECL [`measure:(real^N->bool)->real`;
                 `IMAGE (\m. IMAGE (\x:real^N. (&m / &N) % x) s) (1..N)`]
                HAS_MEASURE_DISJOINT_UNIONS) THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; IMP_CONJ] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM HAS_MEASURE_MEASURE] THEN
    MATCH_MP_TAC MEASURABLE_SCALING THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP] THEN
  ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ ~c ==> d <=> a /\ b /\ ~d ==> c`] THEN
  SUBGOAL_THEN
   `!m n. m IN 1..N /\ n IN 1..N /\
          ~(DISJOINT (IMAGE (\x:real^N. &m / &N % x) s)
                     (IMAGE (\x. &n / &N % x) s))
          ==> m = n`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY] THEN
    REWRITE_TAC[EXISTS_IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N`
     (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N`
     (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    DISCH_THEN(MP_TAC o AP_TERM `(%) (&N / &m) :real^N->real^N`) THEN
    SUBGOAL_THEN `~(&N = &0) /\ ~(&m = &0)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ] THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_NUMSEG])) THEN
      ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE (BINDER_CONV o BINDER_CONV)
     [GSYM CONTRAPOS_THM]) THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_FIELD
     `~(x = &0) /\ ~(y = &0) ==> x / y * y / x = &1`] THEN
    ASM_SIMP_TAC[REAL_FIELD
     `~(x = &0) /\ ~(y = &0) ==> x / y * z / x = z / y`] THEN
    REWRITE_TAC[VECTOR_MUL_LID] THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&n / &m`; `y:real^N`]) THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_FIELD
     `~(y = &0) ==> (x / y = &1 <=> x = y)`] THEN
    REWRITE_TAC[REAL_OF_NUM_EQ; EQ_SYM_EQ];
    ALL_TAC] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[measurable] THEN ASM_MESON_TAC[];
    REWRITE_TAC[MEASURABLE_INTERVAL];
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN X_GEN_TAC `x:real^N` THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`--a:real^N`; `a:real^N`] CONVEX_INTERVAL) THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[CONVEX_ALT] o CONJUNCT1) THEN
    DISCH_THEN(MP_TAC o SPECL [`vec 0:real^N`; `x:real^N`; `&n / &N`]) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
    DISCH_THEN MATCH_MP_TAC THEN SIMP_TAC[REAL_LE_DIV; REAL_POS] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_NUMSEG]) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
     `1 <= n /\ n <= N ==> 0 < N /\ n <= N`)) THEN
    SIMP_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_LT; REAL_LE_LDIV_EQ] THEN
    SIMP_TAC[REAL_MUL_LID];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP MEASURE_UNIQUE) THEN
  ASM_SIMP_TAC[MEASURE_SCALING; REAL_NOT_LE] THEN
  FIRST_X_ASSUM(K ALL_TAC o SPEC `&0`) THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC
   `sum (1..N) (measure o (\m. IMAGE (\x:real^N. &m / &N % x) s))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SUM_IMAGE THEN REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[SET_RULE `DISJOINT s s <=> s = {}`; IMAGE_EQ_EMPTY] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    ASM_MESON_TAC[REAL_LT_REFL; MEASURE_EMPTY]] THEN
  FIRST_X_ASSUM(K ALL_TAC o SPEC `0`) THEN
  ASM_SIMP_TAC[o_DEF; MEASURE_SCALING; SUM_RMUL] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `x < a ==> a <= b ==> x < b`)) THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(a * b) * c:real = (a * c) * b`] THEN
  ASM_SIMP_TAC[REAL_LE_RMUL_EQ] THEN REWRITE_TAC[GSYM SUM_RMUL] THEN
  REWRITE_TAC[GSYM REAL_POW_MUL] THEN
  REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NUM] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `M:num` SUBST_ALL_TAC o
        GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_MUL]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_ARITH `&0 < &2 * x <=> &0 < x`]) THEN
  ASM_SIMP_TAC[REAL_FIELD `&0 < y ==> x / (&2 * y) * &4 = x * &2 / y`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(M..(2*M)) (\i. (&i * &2 / &M) pow dimindex (:N))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    SIMP_TAC[REAL_POW_LE; REAL_LE_MUL; REAL_LE_DIV; REAL_POS] THEN
    REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG; SUBSET] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_OF_NUM_LT]) THEN
    ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(M..(2*M)) (\i. &2)` THEN CONJ_TAC THENL
   [REWRITE_TAC[SUM_CONST_NUMSEG] THEN
    REWRITE_TAC[ARITH_RULE `(2 * M + 1) - M = M + 1`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 pow (dimindex(:N))` THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN REWRITE_TAC[DIMINDEX_GE_1] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN
  REWRITE_TAC[REAL_POS; ARITH; real_div; REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ] THEN
  REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
  UNDISCH_TAC `M:num <= n` THEN ARITH_TAC);;

let STARLIKE_NEGLIGIBLE_LEMMA = prove
 (`!s. compact s /\
       (!c x:real^N. &0 <= c /\ x IN s /\ (c % x) IN s ==> c = &1)
       ==> negligible s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC STARLIKE_NEGLIGIBLE_BOUNDED_MEASURABLE THEN
  ASM_MESON_TAC[MEASURABLE_COMPACT; COMPACT_IMP_BOUNDED]);;

let STARLIKE_NEGLIGIBLE = prove
 (`!s a. closed s /\
         (!c x:real^N. &0 <= c /\ (a + x) IN s /\ (a + c % x) IN s ==> c = &1)
         ==> negligible s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NEGLIGIBLE_TRANSLATION_REV THEN
  EXISTS_TAC `--a:real^N` THEN ONCE_REWRITE_TAC[NEGLIGIBLE_ON_INTERVALS] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN
  MATCH_MP_TAC STARLIKE_NEGLIGIBLE_LEMMA THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_INTER_COMPACT THEN REWRITE_TAC[COMPACT_INTERVAL] THEN
    ASM_SIMP_TAC[CLOSED_TRANSLATION];
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `x:real^N = --a + y <=> y = a + x`] THEN
    REWRITE_TAC[UNWIND_THM2] THEN ASM MESON_TAC[]]);;

let STARLIKE_NEGLIGIBLE_STRONG = prove
 (`!s a. closed s /\
         (!c x:real^N. &0 <= c /\ c < &1 /\ (a + x) IN s
                       ==> ~((a + c % x) IN s))
         ==> negligible s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC STARLIKE_NEGLIGIBLE THEN
  EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`c:real`; `x:real^N`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `~(x < y) /\ ~(y < x) ==> x = y`) THEN
  STRIP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`inv c`; `c % x:real^N`]) THEN
  ASM_REWRITE_TAC[REAL_LE_INV_EQ; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_ARITH `&1 < c ==> ~(c = &0)`] THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LID] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_1] THEN
  MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[REAL_LT_01]);;

(* ------------------------------------------------------------------------- *)
(* In particular.                                                            *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_HYPERPLANE = prove
 (`!a b. ~(a = vec 0 /\ b = &0) ==> negligible {x:real^N | a dot x = b}`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^N = vec 0` THEN
  ASM_SIMP_TAC[DOT_LZERO; SET_RULE `{x | F} = {}`; NEGLIGIBLE_EMPTY] THEN
  MATCH_MP_TAC STARLIKE_NEGLIGIBLE THEN
  SUBGOAL_THEN `?x:real^N. ~(a dot x = b)` MP_TAC THENL
   [MATCH_MP_TAC(MESON[] `!a:real^N. P a \/ P(--a) ==> ?x. P x`) THEN
    EXISTS_TAC `a:real^N` THEN REWRITE_TAC[DOT_RNEG] THEN
    MATCH_MP_TAC(REAL_ARITH `~(a = &0) ==> ~(a = b) \/ ~(--a = b)`) THEN
    ASM_REWRITE_TAC[DOT_EQ_0];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[CLOSED_HYPERPLANE; IN_ELIM_THM; DOT_RADD; DOT_RMUL] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `&0 <= t /\ ac + ay = b /\ ac + t * ay = b
    ==> ((ay = &0 ==> ac = b) /\ (t - &1) * ay = &0)`)) THEN
  ASM_SIMP_TAC[REAL_ENTIRE; REAL_SUB_0] THEN CONV_TAC TAUT);;

let NEGLIGIBLE_LOWDIM = prove
 (`!s:real^N->bool. dim(s) < dimindex(:N) ==> negligible s`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP LOWDIM_SUBSET_HYPERPLANE) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `span(s):real^N->bool` THEN REWRITE_TAC[SPAN_INC] THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `{x:real^N | a dot x = &0}` THEN
  ASM_SIMP_TAC[NEGLIGIBLE_HYPERPLANE]);;

let NEGLIGIBLE_AFFINE_HULL = prove
 (`!s:real^N->bool.
        FINITE s /\ CARD(s) <= dimindex(:N) ==> negligible(affine hull s)`,
  REWRITE_TAC[IMP_CONJ] THEN  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[AFFINE_HULL_EMPTY; NEGLIGIBLE_EMPTY] THEN
  SUBGOAL_THEN
   `!x s:real^N->bool n.
        ~(x IN s) /\ (x INSERT s) HAS_SIZE n /\ n <= dimindex(:N)
        ==> negligible(affine hull(x INSERT s))`
   (fun th -> MESON_TAC[th; HAS_SIZE; FINITE_INSERT]) THEN
  X_GEN_TAC `orig:real^N` THEN GEOM_ORIGIN_TAC `orig:real^N` THEN
  SIMP_TAC[AFFINE_HULL_EQ_SPAN; IN_INSERT; SPAN_INSERT_0; HULL_INC] THEN
  REWRITE_TAC[HAS_SIZE; FINITE_INSERT; IMP_CONJ] THEN
  SIMP_TAC[CARD_CLAUSES] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NEGLIGIBLE_LOWDIM THEN
  MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `CARD(s:real^N->bool)` THEN
  ASM_SIMP_TAC[DIM_LE_CARD; DIM_SPAN] THEN ASM_ARITH_TAC);;

let NEGLIGIBLE_AFFINE_HULL_1 = prove
 (`!a:real^1. negligible (affine hull {a})`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC NEGLIGIBLE_AFFINE_HULL THEN
  SIMP_TAC[FINITE_INSERT; CARD_CLAUSES; FINITE_EMPTY; DIMINDEX_1] THEN
  ARITH_TAC);;

let NEGLIGIBLE_AFFINE_HULL_2 = prove
 (`!a b:real^2. negligible (affine hull {a,b})`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC NEGLIGIBLE_AFFINE_HULL THEN
  SIMP_TAC[FINITE_INSERT; CARD_CLAUSES; FINITE_EMPTY; DIMINDEX_2] THEN
  ARITH_TAC);;

let NEGLIGIBLE_AFFINE_HULL_3 = prove
 (`!a b c:real^3. negligible (affine hull {a,b,c})`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC NEGLIGIBLE_AFFINE_HULL THEN
  SIMP_TAC[FINITE_INSERT; CARD_CLAUSES; FINITE_EMPTY; DIMINDEX_3] THEN
  ARITH_TAC);;

let NEGLIGIBLE_CONVEX_HULL = prove
 (`!s:real^N->bool.
        FINITE s /\ CARD(s) <= dimindex(:N) ==> negligible(convex hull s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP NEGLIGIBLE_AFFINE_HULL) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] NEGLIGIBLE_SUBSET) THEN
  REWRITE_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL]);;

let NEGLIGIBLE_CONVEX_HULL_1 = prove
 (`!a:real^1. negligible (convex hull {a})`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC NEGLIGIBLE_CONVEX_HULL THEN
  SIMP_TAC[FINITE_INSERT; CARD_CLAUSES; FINITE_EMPTY; DIMINDEX_1] THEN
  ARITH_TAC);;

let NEGLIGIBLE_CONVEX_HULL_2 = prove
 (`!a b:real^2. negligible (convex hull {a,b})`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC NEGLIGIBLE_CONVEX_HULL THEN
  SIMP_TAC[FINITE_INSERT; CARD_CLAUSES; FINITE_EMPTY; DIMINDEX_2] THEN
  ARITH_TAC);;

let NEGLIGIBLE_CONVEX_HULL_3 = prove
 (`!a b c:real^3. negligible (convex hull {a,b,c})`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC NEGLIGIBLE_CONVEX_HULL THEN
  SIMP_TAC[FINITE_INSERT; CARD_CLAUSES; FINITE_EMPTY; DIMINDEX_3] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Measurability of bounded convex sets.                                     *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_CONVEX_FRONTIER = prove
 (`!s:real^N->bool. convex s ==> negligible(frontier s)`,
  SUBGOAL_THEN
   `!s:real^N->bool. convex s /\ (vec 0) IN s ==> negligible(frontier s)`
  ASSUME_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `s:real^N->bool = {}` THEN
    ASM_REWRITE_TAC[FRONTIER_EMPTY; NEGLIGIBLE_EMPTY] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (\x:real^N. --a + x) s`) THEN
    ASM_SIMP_TAC[CONVEX_TRANSLATION; IN_IMAGE] THEN
    ASM_REWRITE_TAC[UNWIND_THM2;
                    VECTOR_ARITH `vec 0:real^N = --a + x <=> x = a`] THEN
    REWRITE_TAC[FRONTIER_TRANSLATION; NEGLIGIBLE_TRANSLATION_EQ]] THEN
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `s:real^N->bool` DIM_SUBSET_UNIV) THEN
  REWRITE_TAC[ARITH_RULE `d:num <= e <=> d < e \/ d = e`] THEN STRIP_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `closure s:real^N->bool` THEN
    REWRITE_TAC[frontier; SUBSET_DIFF] THEN
    MATCH_MP_TAC NEGLIGIBLE_LOWDIM THEN ASM_REWRITE_TAC[DIM_CLOSURE];
    ALL_TAC] THEN
  SUBGOAL_THEN `?a:real^N. a IN interior s` CHOOSE_TAC THENL
   [X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC
     (ISPEC `s:real^N->bool` BASIS_EXISTS) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPEC `b:real^N->bool` INTERIOR_SIMPLEX_NONEMPTY) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC SUBSET_INTERIOR THEN MATCH_MP_TAC HULL_MINIMAL THEN
    ASM_REWRITE_TAC[INSERT_SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC STARLIKE_NEGLIGIBLE_STRONG THEN
  EXISTS_TAC `a:real^N` THEN REWRITE_TAC[FRONTIER_CLOSED] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[frontier; IN_DIFF; DE_MORGAN_THM] THEN DISJ2_TAC THEN
  SIMP_TAC[VECTOR_ARITH
   `a + c % x:real^N = (a + x) - (&1 - c) % ((a + x) - a)`] THEN
  MATCH_MP_TAC IN_INTERIOR_CLOSURE_CONVEX_SHRINK THEN
  RULE_ASSUM_TAC(REWRITE_RULE[frontier; IN_DIFF]) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let MEASURABLE_CONVEX = prove
 (`!s:real^N->bool. convex s /\ bounded s ==> measurable s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_JORDAN THEN
  ASM_SIMP_TAC[NEGLIGIBLE_CONVEX_FRONTIER]);;

(* ------------------------------------------------------------------------- *)
(* Various special cases.                                                    *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_SPHERE = prove
 (`!a r. negligible {x:real^N | dist(a,x) = r}`,
  REWRITE_TAC[GSYM FRONTIER_CBALL] THEN
  SIMP_TAC[NEGLIGIBLE_CONVEX_FRONTIER; CONVEX_CBALL]);;

let MEASURABLE_BALL = prove
 (`!a r. measurable(ball(a,r))`,
  SIMP_TAC[MEASURABLE_OPEN; BOUNDED_BALL; OPEN_BALL]);;

let MEASURABLE_CBALL = prove
 (`!a r. measurable(cball(a,r))`,
  SIMP_TAC[MEASURABLE_COMPACT; COMPACT_CBALL]);;

let HAS_INTEGRAL_OPEN_INTERVAL = prove
 (`!f a b y. (f has_integral y) (interval(a,b)) <=>
             (f has_integral y) (interval[a,b])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM INTERIOR_CLOSED_INTERVAL] THEN
  MATCH_MP_TAC HAS_INTEGRAL_INTERIOR THEN
  MATCH_MP_TAC NEGLIGIBLE_CONVEX_FRONTIER THEN
  REWRITE_TAC[CONVEX_INTERVAL]);;

let INTEGRABLE_ON_OPEN_INTERVAL = prove
 (`!f a b. f integrable_on interval(a,b) <=>
           f integrable_on interval[a,b]`,
  REWRITE_TAC[integrable_on; HAS_INTEGRAL_OPEN_INTERVAL]);;

let INTEGRAL_OPEN_INTERVAL = prove
 (`!f a b. integral(interval(a,b)) f = integral(interval[a,b]) f`,
  REWRITE_TAC[integral; HAS_INTEGRAL_OPEN_INTERVAL]);;

(* ------------------------------------------------------------------------- *)
(* Negligibility of image under non-injective linear map.                    *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_LINEAR_SINGULAR_IMAGE = prove
 (`!f:real^N->real^N s.
        linear f /\ ~(!x y. f(x) = f(y) ==> x = y)
        ==> negligible(IMAGE f s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP LINEAR_SINGULAR_IMAGE_HYPERPLANE) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `{x:real^N | a dot x = &0}` THEN
  ASM_SIMP_TAC[NEGLIGIBLE_HYPERPLANE]);;

(* ------------------------------------------------------------------------- *)
(* Some technical lemmas used in the approximation results that follow.      *)
(* Proof of the covering lemma is an obvious multidimensional generalization *)
(* of Lemma 3, p65 of Swartz's "Introduction to Gauge Integrals".            *)
(* ------------------------------------------------------------------------- *)

let COVERING_LEMMA = prove
 (`!a b:real^N s g.
        s SUBSET interval[a,b] /\ ~(interval(a,b) = {}) /\ gauge g
        ==> ?d. COUNTABLE d /\
                (!k. k IN d ==> k SUBSET interval[a,b] /\ ~(interior k = {}) /\
                                (?c d. k = interval[c,d])) /\
                (!k1 k2. k1 IN d /\ k2 IN d /\ ~(k1 = k2)
                         ==> interior k1 INTER interior k2 = {}) /\
                (!k. k IN d ==> ?x. x IN (s INTER k) /\ k SUBSET g(x)) /\
                s SUBSET UNIONS d`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?d. COUNTABLE d /\
        (!k. k IN d ==> k SUBSET interval[a,b] /\ ~(interior k = {}) /\
                        (?c d:real^N. k = interval[c,d])) /\
        (!k1 k2. k1 IN d /\ k2 IN d
                 ==> k1 SUBSET k2 \/ k2 SUBSET k1 \/
                     interior k1 INTER interior k2 = {}) /\
        (!x. x IN s ==> ?k. k IN d /\ x IN k /\ k SUBSET g(x)) /\
        (!k. k IN d ==> FINITE {l | l IN d /\ k SUBSET l})`
  ASSUME_TAC THENL
   [EXISTS_TAC
     `IMAGE (\(n,v).
             interval[(lambda i. a$i + &(v$i) / &2 pow n *
                                       ((b:real^N)$i - (a:real^N)$i)):real^N,
                      (lambda i. a$i + (&(v$i) + &1) / &2 pow n * (b$i - a$i))])
            {n,v | n IN (:num) /\
                   v IN {v:num^N | !i. 1 <= i /\ i <= dimindex(:N)
                                       ==> v$i < 2 EXP n}}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC COUNTABLE_IMAGE THEN
      MATCH_MP_TAC COUNTABLE_PRODUCT_DEPENDENT THEN
      REWRITE_TAC[NUM_COUNTABLE; IN_UNIV] THEN
      GEN_TAC THEN MATCH_MP_TAC FINITE_IMP_COUNTABLE THEN
      MATCH_MP_TAC FINITE_CART THEN REWRITE_TAC[FINITE_NUMSEG_LT];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `v:num^N`] THEN
      REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
      REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN DISCH_TAC THEN
      REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
      REWRITE_TAC[INTERIOR_CLOSED_INTERVAL] THEN
      SIMP_TAC[INTERVAL_NE_EMPTY; SUBSET_INTERVAL; LAMBDA_BETA] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN
      ASM_SIMP_TAC[REAL_LE_LADD; REAL_LE_RMUL_EQ; REAL_SUB_LT; REAL_LE_MUL_EQ;
                   REAL_LT_LADD; REAL_LT_RMUL_EQ; REAL_LE_ADDR; REAL_ARITH
                     `a + x * (b - a) <= b <=> &0 <= (&1 - x) * (b - a)`] THEN
      SIMP_TAC[REAL_LE_DIV2_EQ; REAL_LT_DIV2_EQ; REAL_LT_POW2] THEN
      REWRITE_TAC[REAL_ARITH `x <= x + &1 /\ x < x + &1`] THEN
      REWRITE_TAC[REAL_SUB_LE] THEN
      SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_LT_POW2] THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_POS; REAL_MUL_LID] THEN
      SIMP_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
      ASM_SIMP_TAC[ARITH_RULE `x + 1 <= y <=> x < y`; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[IMP_CONJ] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM; RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC[IN_ELIM_PAIR_THM; IN_UNIV] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
      GEN_REWRITE_TAC BINDER_CONV [SWAP_FORALL_THM] THEN
      MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL
       [REPEAT GEN_TAC THEN
        GEN_REWRITE_TAC RAND_CONV [SWAP_FORALL_THM] THEN
        REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN SET_TAC[];
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [`v:num^N`; `w:num^N`] THEN REPEAT DISCH_TAC THEN
      REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; SUBSET_INTERVAL] THEN
      SIMP_TAC[DISJOINT_INTERVAL; LAMBDA_BETA] THEN
      MATCH_MP_TAC(TAUT `p \/ q \/ r ==> (a ==> p) \/ (b ==> q) \/ r`) THEN
      ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> ~(a /\ b ==> ~c)`] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN
      ASM_SIMP_TAC[REAL_LE_LADD; REAL_LE_RMUL_EQ; REAL_SUB_LT; LAMBDA_BETA] THEN
      REWRITE_TAC[NOT_IMP; REAL_LE_LADD] THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_LT_POW2] THEN
      REWRITE_TAC[REAL_ARITH `~(x + &1 <= x)`] THEN DISJ2_TAC THEN
      MATCH_MP_TAC(MESON[]
       `(!i. ~P i ==> Q i) ==> (!i. Q i) \/ (?i. P i)`) THEN
      X_GEN_TAC `i:num` THEN
      DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
      ASM_REWRITE_TAC[DE_MORGAN_THM; REAL_NOT_LE] THEN
      UNDISCH_TAC `m:num <= n` THEN REWRITE_TAC[LE_EXISTS] THEN
      DISCH_THEN(X_CHOOSE_THEN `p:num` SUBST1_TAC) THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN
      REWRITE_TAC[REAL_POW_ADD; real_div; REAL_INV_MUL] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_LT_POW2; REAL_LT_DIV2_EQ] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_LT_POW2;
                   REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN
      SIMP_TAC[REAL_LT_INTEGERS; INTEGER_CLOSED] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN
        `?e. &0 < e /\ !y. (!i. 1 <= i /\ i <= dimindex(:N)
                                ==> abs((x:real^N)$i - (y:real^N)$i) <= e)
                           ==> y IN g(x)`
      STRIP_ASSUME_TAC THENL
       [FIRST_ASSUM(MP_TAC o SPEC `x:real^N` o GEN_REWRITE_RULE I [gauge]) THEN
        STRIP_TAC THEN
        FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
        DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `e / &2 / &(dimindex(:N))` THEN
        ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; LE_1; DIMINDEX_GE_1;
                     ARITH] THEN
        X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
        MATCH_MP_TAC(SET_RULE `!s. s SUBSET t /\ x IN s ==> x IN t`) THEN
        EXISTS_TAC `ball(x:real^N,e)` THEN ASM_REWRITE_TAC[IN_BALL] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x <= e / &2 ==> x < e`) THEN
        ASM_REWRITE_TAC[dist] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `sum(1..dimindex(:N)) (\i. abs((x - y:real^N)$i))` THEN
        REWRITE_TAC[NORM_LE_L1] THEN MATCH_MP_TAC SUM_BOUND_GEN THEN
        ASM_SIMP_TAC[IN_NUMSEG; FINITE_NUMSEG; NUMSEG_EMPTY; NOT_LT;
                     DIMINDEX_GE_1; VECTOR_SUB_COMPONENT; CARD_NUMSEG_1];
        ALL_TAC] THEN
      REWRITE_TAC[EXISTS_IN_IMAGE; EXISTS_PAIR_THM; IN_ELIM_PAIR_THM] THEN
      MP_TAC(SPECL [`&1 / &2`; `e / norm(b - a:real^N)`]
        REAL_ARCH_POW_INV) THEN
      SUBGOAL_THEN `&0 < norm(b - a:real^N)` ASSUME_TAC THENL
       [ASM_MESON_TAC[VECTOR_SUB_EQ; NORM_POS_LT; INTERVAL_SING]; ALL_TAC] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_SIMP_TAC[REAL_LT_DIV] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
      REWRITE_TAC[real_div; REAL_MUL_LID; REAL_POW_INV] THEN DISCH_TAC THEN
      SIMP_TAC[IN_ELIM_THM; IN_INTERVAL; SUBSET; LAMBDA_BETA] THEN
      MATCH_MP_TAC(MESON[]
       `(!x. Q x ==> R x) /\ (?x. P x /\ Q x) ==> ?x. P x /\ Q x /\ R x`) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
        MAP_EVERY X_GEN_TAC [`w:num^N`; `y:real^N`] THEN
        REWRITE_TAC[IMP_IMP; AND_FORALL_THM] THEN
        DISCH_THEN(fun th -> FIRST_X_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
        DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
         `(a + n <= x /\ x <= a + m) /\
          (a + n <= y /\ y <= a + m) ==> abs(x - y) <= m - n`)) THEN
        MATCH_MP_TAC(REAL_ARITH
         `y * z <= e
          ==> a <= ((x + &1) * y) * z - ((x * y) * z) ==> a <= e`) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN
        ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_SUB_LT] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
        (REAL_ARITH `n < e * x ==> &0 <= e * (inv y - x) ==> n <= e / y`)) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        ASM_SIMP_TAC[REAL_SUB_LT] THEN
        MP_TAC(SPECL [`b - a:real^N`; `i:num`] COMPONENT_LE_NORM) THEN
        ASM_SIMP_TAC[VECTOR_SUB_COMPONENT] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[IN_UNIV; AND_FORALL_THM] THEN
      REWRITE_TAC[TAUT `(a ==> c) /\ (a ==> b) <=> a ==> b /\ c`] THEN
      REWRITE_TAC[GSYM LAMBDA_SKOLEM] THEN X_GEN_TAC `i:num` THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(x:real^N) IN interval[a,b]` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN REWRITE_TAC[IN_INTERVAL] THEN
      DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN STRIP_TAC THEN
      DISJ_CASES_TAC(MATCH_MP (REAL_ARITH `x <= y ==> x = y \/ x < y`)
       (ASSUME `(x:real^N)$i <= (b:real^N)$i`))
      THENL
       [EXISTS_TAC `2 EXP n - 1` THEN
        SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM REAL_OF_NUM_LT;
                 EXP_LT_0; LE_1; ARITH] THEN
        ASM_REWRITE_TAC[REAL_SUB_ADD; REAL_ARITH `a - &1 < a`] THEN
        MATCH_MP_TAC(REAL_ARITH
         `&1 * (b - a) = x /\ y <= x ==> a + y <= b /\ b <= a + x`) THEN
        ASM_SIMP_TAC[REAL_EQ_MUL_RCANCEL; REAL_LT_IMP_NZ; REAL_LE_RMUL_EQ;
                     REAL_SUB_LT; REAL_LT_INV_EQ; REAL_LT_POW2] THEN
        SIMP_TAC[GSYM REAL_OF_NUM_POW; REAL_MUL_RINV; REAL_POW_EQ_0;
                 REAL_OF_NUM_EQ; ARITH_EQ] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(SPEC `&2 pow n * ((x:real^N)$i - (a:real^N)$i) /
                              ((b:real^N)$i - (a:real^N)$i)` FLOOR_POS) THEN
      ANTS_TAC THENL
       [ASM_MESON_TAC[REAL_LE_MUL; REAL_LE_MUL; REAL_POW_LE; REAL_POS;
                      REAL_SUB_LE; REAL_LT_IMP_LE; REAL_LE_DIV];
        ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_POW] THEN
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      REWRITE_TAC[REAL_ARITH `a + b * c <= x /\ x <= a + b' * c <=>
                              b * c <= x - a /\ x - a <= b' * c`] THEN
      ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; GSYM REAL_LE_RDIV_EQ;
                   REAL_SUB_LT; GSYM real_div] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_LT_POW2] THEN
      SIMP_TAC[FLOOR; REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `((x:real^N)$i - (a:real^N)$i) /
                  ((b:real^N)$i - (a:real^N)$i) *
                  &2 pow n` THEN
      REWRITE_TAC[FLOOR] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      ASM_SIMP_TAC[REAL_LT_RMUL_EQ; REAL_LT_POW2] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LID; REAL_SUB_LT] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `v:num^N`] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN DISCH_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
     `IMAGE (\(n,v).
            interval[(lambda i. a$i + &(v$i) / &2 pow n *
                                      ((b:real^N)$i - (a:real^N)$i)):real^N,
                     (lambda i. a$i + (&(v$i) + &1) / &2 pow n * (b$i - a$i))])
            {m,v | m IN 0..n /\
                   v IN {v:num^N | !i. 1 <= i /\ i <= dimindex(:N)
                                       ==> v$i < 2 EXP m}}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN
      MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN
      REWRITE_TAC[FINITE_NUMSEG] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC FINITE_CART THEN REWRITE_TAC[FINITE_NUMSEG_LT];
      ALL_TAC] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `w:num^N`] THEN DISCH_TAC THEN
    DISCH_TAC THEN SIMP_TAC[IN_IMAGE; EXISTS_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    MAP_EVERY EXISTS_TAC [`m:num`; `w:num^N`] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_NUMSEG; GSYM NOT_LT; LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET_INTERVAL]) THEN
    SIMP_TAC[NOT_IMP; LAMBDA_BETA] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN
    ASM_SIMP_TAC[REAL_LE_LADD; REAL_LE_RMUL_EQ; REAL_SUB_LT] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_LT_POW2] THEN
    REWRITE_TAC[REAL_ARITH `x <= x + &1`] THEN
    DISCH_THEN(MP_TAC o SPEC `1`) THEN
    REWRITE_TAC[LE_REFL; DIMINDEX_GE_1] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
     `w / m <= v / n /\ (v + &1) / n <= (w + &1) / m
      ==> inv n <= inv m`)) THEN
    REWRITE_TAC[REAL_NOT_LE] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
    ASM_REWRITE_TAC[REAL_LT_POW2] THEN MATCH_MP_TAC REAL_POW_MONO_LT THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?d. COUNTABLE d /\
        (!k. k IN d ==> k SUBSET interval[a,b] /\ ~(interior k = {}) /\
                        (?c d:real^N. k = interval[c,d])) /\
        (!k1 k2. k1 IN d /\ k2 IN d
                 ==> k1 SUBSET k2 \/ k2 SUBSET k1 \/
                     interior k1 INTER interior k2 = {}) /\
        (!k. k IN d ==> (?x. x IN s INTER k /\ k SUBSET g x)) /\
        (!k. k IN d ==> FINITE {l | l IN d /\ k SUBSET l}) /\
        s SUBSET UNIONS d`
  MP_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `d:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC
     `{k:real^N->bool | k IN d /\ ?x. x IN (s INTER k) /\ k SUBSET g x}` THEN
    ASM_SIMP_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COUNTABLE_SUBSET THEN
      EXISTS_TAC `d:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      X_GEN_TAC `k:real^N->bool` THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{l:real^N->bool | l IN d /\ k SUBSET l}` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC
   `{k:real^N->bool | k IN d /\ !k'. k' IN d /\ ~(k = k')
                                     ==> ~(k SUBSET k')}` THEN
  ASM_SIMP_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COUNTABLE_SUBSET THEN EXISTS_TAC `d:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] SUBSET_TRANS)) THEN
  GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[FORALL_IN_UNIONS] THEN
  MAP_EVERY X_GEN_TAC [`k:real^N->bool`; `x:real^N`] THEN DISCH_TAC THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  MP_TAC(ISPEC `\k l:real^N->bool. k IN d /\ l IN d /\ l SUBSET k /\ ~(k = l)`
     WF_FINITE) THEN
  REWRITE_TAC[WF] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN X_GEN_TAC `l:real^N->bool` THEN
    ASM_CASES_TAC `(l:real^N->bool) IN d` THEN
    ASM_REWRITE_TAC[EMPTY_GSPEC; FINITE_RULES] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{m:real^N->bool | m IN d /\ l SUBSET m}` THEN
    ASM_SIMP_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `\l:real^N->bool. l IN d /\ x IN l`) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[]);;

let COUNTABLE_ELEMENTARY_DIVISION = prove
 (`!d. COUNTABLE d /\ (!k. k IN d ==> ?a b:real^N. k = interval[a,b])
       ==> ?d'. COUNTABLE d' /\
                (!k. k IN d' ==> ~(k = {}) /\ ?a b. k = interval[a,b]) /\
                (!k l. k IN d' /\ l IN d' /\ ~(k = l)
                       ==> interior k INTER interior l = {}) /\
                UNIONS d' = UNIONS d`,
  let lemma = prove
   (`!s. UNIONS(s DELETE {}) = UNIONS s`,
    REWRITE_TAC[EXTENSION; IN_UNIONS; IN_DELETE] THEN
    MESON_TAC[NOT_IN_EMPTY]) in
  REWRITE_TAC[IMP_CONJ; FORALL_COUNTABLE_AS_IMAGE] THEN
  REWRITE_TAC[UNIONS_0; EMPTY_UNIONS] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `{}:(real^N->bool)->bool` THEN
    REWRITE_TAC[NOT_IN_EMPTY; COUNTABLE_EMPTY];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV; SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`d:num->real^N->bool`; `a:num->real^N`; `b:num->real^N`] THEN
  DISCH_TAC THEN
  (CHOOSE_THEN MP_TAC o prove_recursive_functions_exist num_RECURSION)
   `x 0 = ({}:(real^N->bool)->bool) /\
    (!n. x(SUC n) = @q. (x n) SUBSET q /\
                        q division_of (d n) UNION UNIONS(x n))` THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!n:num. (x n) division_of UNIONS {d k:real^N->bool | k < n}`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN
    ASM_REWRITE_TAC[LT; SET_RULE `UNIONS {f x |x| F} = {}`;
                    DIVISION_OF_TRIVIAL] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`(a:num->real^N) n`; `(b:num->real^N) n`] o
      MATCH_MP ELEMENTARY_UNION_INTERVAL_STRONG o
      MATCH_MP DIVISION_OF_UNION_SELF) THEN
    DISCH_THEN(ASSUME_TAC o SELECT_RULE) THEN
    REWRITE_TAC[SET_RULE `{f x | x = a \/ q x} = f a INSERT {f x | q x}`] THEN
    REWRITE_TAC[UNIONS_INSERT] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m n. m <= n ==> (x:num->(real^N->bool)->bool) m SUBSET x n`
  ASSUME_TAC THENL
   [MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
    REPEAT(CONJ_TAC THENL [SET_TAC[]; ALL_TAC]) THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(a:num->real^N) n`; `(b:num->real^N) n`] o
      MATCH_MP ELEMENTARY_UNION_INTERVAL_STRONG o
      MATCH_MP DIVISION_OF_UNION_SELF o SPEC `n:num`) THEN
    DISCH_THEN(ASSUME_TAC o SELECT_RULE) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `UNIONS(IMAGE x (:num)) DELETE ({}:real^N->bool)` THEN
  REWRITE_TAC[COUNTABLE_DELETE; IMP_CONJ; RIGHT_FORALL_IMP_THM;
              FORALL_IN_UNIONS; FORALL_IN_IMAGE; IN_DELETE; IN_UNIV] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COUNTABLE_UNIONS THEN
    SIMP_TAC[COUNTABLE_IMAGE; NUM_COUNTABLE; FORALL_IN_IMAGE; IN_UNIV] THEN
    GEN_TAC THEN MATCH_MP_TAC FINITE_IMP_COUNTABLE THEN
    ASM_MESON_TAC[DIVISION_OF_FINITE];
    MAP_EVERY X_GEN_TAC [`n:num`; `k:real^N->bool`] THEN
    ASM_MESON_TAC[division_of];
    REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP] THEN
    GEN_REWRITE_TAC BINDER_CONV [SWAP_FORALL_THM] THEN
    MATCH_MP_TAC WLOG_LE THEN
    CONJ_TAC THENL [MESON_TAC[INTER_COMM]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`k:real^N->bool`; `l:real^N->bool`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `n:num`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of] o
      SPEC `n:num`) THEN ASM SET_TAC[];
    REWRITE_TAC[lemma] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; IN_UNIV;
                FORALL_IN_UNIONS; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE]
    THENL
     [X_GEN_TAC `k:real^N->bool` THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of] o
         SPEC `n:num`) THEN
      DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN ASM SET_TAC[];
      MAP_EVERY X_GEN_TAC [`n:num`; `y:real^N`] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of] o
         SPEC `SUC n`) THEN
      DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
      REWRITE_TAC[EXTENSION; IN_UNIONS; EXISTS_IN_GSPEC] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
      ASM_MESON_TAC[ARITH_RULE `n < SUC n`]]]);;

let EXPAND_CLOSED_OPEN_INTERVAL = prove
 (`!a b:real^N e.
        &0 < e
        ==> ?c d. interval[a,b] SUBSET interval(c,d) /\
                  measure(interval(c,d)) <= measure(interval[a,b]) + e`,
  let lemma = prove
   (`!f n. (\x. lift(product(1..n) (\i. f i + drop x))) continuous at (vec 0)`,
    GEN_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC[PRODUCT_CLAUSES_NUMSEG; ARITH_EQ; CONTINUOUS_CONST] THEN
    REWRITE_TAC[ARITH_RULE `1 <= SUC n`] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[LIFT_CMUL] THEN
    MATCH_MP_TAC CONTINUOUS_MUL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[o_DEF; LIFT_ADD; LIFT_DROP] THEN
    SIMP_TAC[CONTINUOUS_ADD; CONTINUOUS_AT_ID; CONTINUOUS_CONST]) in
  REPEAT GEN_TAC THEN ABBREV_TAC `m:real^N = midpoint(a,b)` THEN
  POP_ASSUM MP_TAC THEN GEOM_ORIGIN_TAC `m:real^N` THEN
  REWRITE_TAC[midpoint; VECTOR_ARITH
   `inv(&2) % (a + b):real^N = vec 0 <=> a = --b`] THEN
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  DISCH_TAC THEN ASM_CASES_TAC `interval[--b:real^N,b] = {}` THENL
   [MAP_EVERY EXISTS_TAC [`--b:real^N`; `b:real^N`] THEN
    REWRITE_TAC[MEASURE_INTERVAL] THEN
    ASM_REWRITE_TAC[CONTENT_EMPTY; EMPTY_SUBSET] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INTERVAL_NE_EMPTY]) THEN
  REWRITE_TAC[VECTOR_NEG_COMPONENT; REAL_ARITH `--x <= x <=> &0 <= x`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`\i. &2 * (b:real^N)$i`; `dimindex(:N)`] lemma) THEN
  REWRITE_TAC[continuous_at; DIST_LIFT; FORALL_LIFT; DIST_0; DROP_VEC] THEN
  REWRITE_TAC[NORM_LIFT; LIFT_DROP; REAL_ADD_RID] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`--(b + k / &4 % vec 1:real^N)`; `b + k / &4 % vec 1:real^N`] THEN
  REWRITE_TAC[MEASURE_INTERVAL; SUBSET_INTERVAL;
              CONTENT_CLOSED_INTERVAL_CASES] THEN
  REWRITE_TAC[VECTOR_NEG_COMPONENT; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
  ASM_SIMP_TAC[REAL_ARITH `--x <= x <=> &0 <= x`; REAL_LT_ADDR;
               REAL_ARITH `&0 < k / &4 <=> &0 < k`;
               REAL_ARITH `&0 <= b /\ &0 < k ==> --(b + k) < b`;
               REAL_ARITH `&0 <= b /\ &0 < k ==> --(b + k) < --b`;
               REAL_ARITH `&0 <= b /\ &0 < k ==> &0 <= b + k`] THEN
  REWRITE_TAC[REAL_ARITH `b - --b = &2 * b`; REAL_ADD_LDISTRIB] THEN
  MATCH_MP_TAC(REAL_ARITH `abs(a - b) < e ==> a <= b + e`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Outer and inner approximation of measurable set by well-behaved sets.     *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_OUTER_INTERVALS_BOUNDED = prove
 (`!s a b:real^N e.
        measurable s /\ s SUBSET interval[a,b] /\ &0 < e
        ==> ?d. COUNTABLE d /\
                (!k. k IN d ==> k SUBSET interval[a,b] /\ ~(k = {}) /\
                                (?c d. k = interval[c,d])) /\
                (!k1 k2. k1 IN d /\ k2 IN d /\ ~(k1 = k2)
                         ==> interior k1 INTER interior k2 = {}) /\
                (!k. k IN d /\ ~(interval(a,b) = {}) ==> ~(interior k = {})) /\
                s SUBSET UNIONS d /\
                measurable (UNIONS d) /\
                measure (UNIONS d) <= measure s + e`,
  let lemma = prove
   (`(!x y. (x,y) IN IMAGE (\z. f z,g z) s ==> P x y) <=>
     (!z. z IN s ==> P (f z) (g z))`,
  REWRITE_TAC[IN_IMAGE; PAIR_EQ] THEN MESON_TAC[]) in
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `interval[a:real^N,b] = {}` THENL
   [ASM_REWRITE_TAC[SUBSET_EMPTY] THEN STRIP_TAC THEN
    EXISTS_TAC `{}:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; UNIONS_0; MEASURE_EMPTY; REAL_ADD_LID;
                    SUBSET_REFL; COUNTABLE_EMPTY; MEASURABLE_EMPTY] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_CASES_TAC `interval(a:real^N,b) = {}` THEN
  ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `{interval[a:real^N,b]}` THEN
    REWRITE_TAC[UNIONS_1; COUNTABLE_SING] THEN
    ASM_REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_INSERT;
                    NOT_IN_EMPTY; SUBSET_REFL; MEASURABLE_INTERVAL] THEN
    CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `measure(interval[a:real^N,b]) = &0 /\ measure(s:real^N->bool) = &0`
     (fun th -> ASM_SIMP_TAC[th; REAL_LT_IMP_LE; REAL_ADD_LID]) THEN
    SUBGOAL_THEN
      `interval[a:real^N,b] has_measure &0 /\ (s:real^N->bool) has_measure &0`
      (fun th -> MESON_TAC[th; MEASURE_UNIQUE]) THEN
    REWRITE_TAC[HAS_MEASURE_0] THEN
    MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[NEGLIGIBLE_INTERVAL];
      ASM_MESON_TAC[NEGLIGIBLE_SUBSET]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [measurable]) THEN
  DISCH_THEN(X_CHOOSE_TAC `m:real`) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MEASURE_UNIQUE) THEN
  SUBGOAL_THEN
   `((\x:real^N. if x IN s then vec 1 else vec 0) has_integral (lift m))
    (interval[a,b])`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM HAS_INTEGRAL_RESTRICT_UNIV] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_MEASURE]) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_EQ) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HAS_INTEGRAL_INTEGRABLE) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [has_integral]) THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`a:real^N`; `b:real^N`; `s:real^N->bool`;
                `g:real^N->real^N->bool`] COVERING_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `d:(real^N->bool)->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[INTERIOR_EMPTY]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(\x. if x IN s then vec 1 else vec 0):real^N->real^1`;
                 `a:real^N`; `b:real^N`; `g:real^N->real^N->bool`;
                 `e:real`]
                HENSTOCK_LEMMA_PART1) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "*") THEN
  SUBGOAL_THEN
   `!k l:real^N->bool. k IN d /\ l IN d /\ ~(k = l)
                       ==> negligible(k INTER l)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:real^N->bool`; `l:real^N->bool`]) THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN
     `?x y:real^N u v:real^N. k = interval[x,y] /\ l = interval[u,v]`
    MP_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    DISCH_THEN(REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN SUBST_ALL_TAC)) THEN
    REWRITE_TAC[INTERIOR_CLOSED_INTERVAL] THEN DISCH_TAC THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `(interval[x:real^N,y] DIFF interval(x,y)) UNION
                (interval[u:real^N,v] DIFF interval(u,v)) UNION
                (interval (x,y) INTER interval (u,v))` THEN
    CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    ASM_REWRITE_TAC[UNION_EMPTY] THEN
    SIMP_TAC[NEGLIGIBLE_UNION; NEGLIGIBLE_FRONTIER_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!D. FINITE D /\ D SUBSET d
         ==> measurable(UNIONS D :real^N->bool) /\ measure(UNIONS D) <= m + e`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?t:(real^N->bool)->real^N. !k. k IN D ==> t(k) IN (s INTER k) /\
                                                k SUBSET (g(t k))`
    (CHOOSE_THEN (LABEL_TAC "+")) THENL
     [REWRITE_TAC[GSYM SKOLEM_THM] THEN ASM SET_TAC[]; ALL_TAC] THEN
    REMOVE_THEN "*" (MP_TAC o SPEC
     `IMAGE (\k. (t:(real^N->bool)->real^N) k,k) D`) THEN
    ASM_SIMP_TAC[VSUM_IMAGE; PAIR_EQ] THEN REWRITE_TAC[o_DEF] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[tagged_partial_division_of; fine] THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
      REWRITE_TAC[lemma; RIGHT_FORALL_IMP_THM; IMP_CONJ; PAIR_EQ] THEN
      ASM_SIMP_TAC[] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[SUBSET]];
      ALL_TAC] THEN
    USE_THEN "+" (MP_TAC o REWRITE_RULE[IN_INTER]) THEN
    SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
    ASM_SIMP_TAC[VSUM_SUB] THEN
    SUBGOAL_THEN `D division_of (UNIONS D:real^N->bool)` ASSUME_TAC THENL
     [REWRITE_TAC[division_of] THEN ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP MEASURABLE_ELEMENTARY) THEN
    SUBGOAL_THEN `vsum D (\k:real^N->bool. content k % vec 1) =
                  lift(measure(UNIONS D))`
    SUBST1_TAC THENL
     [ONCE_REWRITE_TAC[GSYM DROP_EQ] THEN
      ASM_SIMP_TAC[LIFT_DROP; DROP_VSUM; o_DEF; DROP_CMUL; DROP_VEC] THEN
      SIMP_TAC[REAL_MUL_RID; ETA_AX] THEN ASM_MESON_TAC[MEASURE_ELEMENTARY];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `vsum D (\k. integral k (\x:real^N. if x IN s then vec 1 else vec 0)) =
      lift(sum D (\k. measure(k INTER s)))`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[LIFT_SUM; o_DEF] THEN MATCH_MP_TAC VSUM_EQ THEN
      X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `measurable(k:real^N->bool)` ASSUME_TAC THENL
       [ASM_MESON_TAC[SUBSET; MEASURABLE_INTERVAL]; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM INTEGRAL_MEASURE_UNIV; MEASURABLE_INTER] THEN
      REWRITE_TAC[MESON[IN_INTER]
        `(if x IN k INTER s then a else b) =
         (if x IN k then if x IN s then a else b else b)`] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_RESTRICT_UNIV THEN
      ONCE_REWRITE_TAC[GSYM INTEGRABLE_RESTRICT_UNIV] THEN
      REWRITE_TAC[MESON[IN_INTER]
       `(if x IN k then if x IN s then a else b else b) =
        (if x IN k INTER s then a else b)`] THEN
      ASM_SIMP_TAC[GSYM MEASURABLE_INTEGRABLE; MEASURABLE_INTER];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= m ==> abs(x - y) <= e ==> x <= m + e`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `measure(UNIONS D INTER s:real^N->bool)` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      EXPAND_TAC "m" THEN MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      MATCH_MP_TAC MEASURABLE_INTER THEN ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[INTER_UNIONS] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC MEASURE_NEGLIGIBLE_UNIONS_IMAGE_STRONG THEN
    ASM_SIMP_TAC[FINITE_RESTRICT] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET; MEASURABLE_INTERVAL; MEASURABLE_INTER];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`k:real^N->bool`; `l:real^N->bool`] THEN
    STRIP_TAC THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `k INTER l:real^N->bool` THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `FINITE(d:(real^N->bool)->bool)` THENL
   [ASM_MESON_TAC[SUBSET_REFL]; ALL_TAC] THEN
  MP_TAC(ISPEC `d:(real^N->bool)->bool` COUNTABLE_AS_INJECTIVE_IMAGE) THEN
  ASM_REWRITE_TAC[INFINITE] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num->real^N->bool`
   (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`s:num->real^N->bool`; `m + e:real`]
    HAS_MEASURE_COUNTABLE_NEGLIGIBLE_UNIONS) THEN
  MATCH_MP_TAC(TAUT `a /\ (a /\ b ==> c) ==> (a ==> b) ==> c`) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IMP_CONJ; RIGHT_FORALL_IMP_THM;
                              FORALL_IN_IMAGE; IN_UNIV]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM]) THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MEASURABLE_INTERVAL; MEASURABLE_INTER];
    ASM_MESON_TAC[];
    X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (s:num->real^N->bool) (0..n)`) THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; IMAGE_SUBSET; SUBSET_UNIV] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= e ==> y <= e`) THEN
    MATCH_MP_TAC MEASURE_NEGLIGIBLE_UNIONS_IMAGE THEN
    ASM_MESON_TAC[FINITE_NUMSEG; MEASURABLE_INTERVAL];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM(CONJUNCT2 LIFT_DROP)] THEN
  REWRITE_TAC[drop] THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_COMPONENT_UBOUND) THEN
  EXISTS_TAC
   `\n. vsum(from 0 INTER (0..n)) (\n. lift(measure(s n:real^N->bool)))` THEN
  ASM_REWRITE_TAC[GSYM sums; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  REWRITE_TAC[DIMINDEX_1; ARITH; EVENTUALLY_SEQUENTIALLY] THEN
  SIMP_TAC[VSUM_COMPONENT; ARITH; DIMINDEX_1] THEN
  ASM_REWRITE_TAC[GSYM drop; LIFT_DROP; FROM_INTER_NUMSEG]);;

let MEASURABLE_OUTER_CLOSED_INTERVALS = prove
 (`!s:real^N->bool e.
        measurable s /\ &0 < e
        ==> ?d. COUNTABLE d /\
                (!k. k IN d ==> ~(k = {}) /\ (?a b. k = interval[a,b])) /\
                (!k l. k IN d /\ l IN d /\ ~(k = l)
                       ==> interior k INTER interior l = {}) /\
                s SUBSET UNIONS d /\
                measurable (UNIONS d) /\
                measure (UNIONS d) <= measure s + e`,
  let lemma = prove
   (`UNIONS (UNIONS {d n | n IN (:num)}) =
     UNIONS {UNIONS(d n) | n IN (:num)}`,
    REWRITE_TAC[SIMPLE_IMAGE; UNIONS_IMAGE] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?d. COUNTABLE d /\
        (!k. k IN d ==> ?a b:real^N. k = interval[a,b]) /\
        s SUBSET UNIONS d /\
        measurable (UNIONS d) /\
        measure (UNIONS d) <= measure s + e`
  MP_TAC THENL
   [ALL_TAC;
    DISCH_THEN(X_CHOOSE_THEN `d1:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `d1:(real^N->bool)->bool` COUNTABLE_ELEMENTARY_DIVISION) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `d:(real^N->bool)->bool` THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL
   [`\n. s INTER (ball(vec 0:real^N,&n + &1) DIFF ball(vec 0,&n))`;
    `measure(s:real^N->bool)`] HAS_MEASURE_COUNTABLE_NEGLIGIBLE_UNIONS) THEN
  ASM_SIMP_TAC[MEASURABLE_INTER; MEASURABLE_DIFF; MEASURABLE_BALL] THEN
  SUBGOAL_THEN
   `!m n. ~(m = n)
          ==> (s INTER (ball(vec 0,&m + &1) DIFF ball(vec 0,&m))) INTER
              (s INTER (ball(vec 0,&n + &1) DIFF ball(vec 0,&n))) =
              ({}:real^N->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WLOG_LT THEN REWRITE_TAC[] THEN
    CONJ_TAC THENL [MESON_TAC[INTER_COMM]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `m1 SUBSET n
      ==> (s INTER (m1 DIFF m)) INTER (s INTER (n1 DIFF n)) = {}`) THEN
    MATCH_MP_TAC SUBSET_BALL THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[NEGLIGIBLE_EMPTY] THEN X_GEN_TAC `n:num` THEN
    W(MP_TAC o PART_MATCH (rand o rand)
      MEASURE_DISJOINT_UNIONS_IMAGE o lhand o snd) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; DISJOINT] THEN
    ASM_SIMP_TAC[MEASURABLE_INTER; MEASURABLE_DIFF; MEASURABLE_BALL] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC MEASURE_SUBSET THEN
    SIMP_TAC[SUBSET; FORALL_IN_UNIONS; IMP_CONJ; FORALL_IN_IMAGE;
             RIGHT_FORALL_IMP_THM; IN_INTER] THEN
    ASM_SIMP_TAC[MEASURABLE_UNIONS; FINITE_NUMSEG; FORALL_IN_IMAGE;
            FINITE_IMAGE; MEASURABLE_INTER; MEASURABLE_DIFF; MEASURABLE_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS {s INTER (ball(vec 0,&n + &1) DIFF ball(vec 0,&n)) | n IN (:num)} =
    (s:real^N->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV; IN_INTER] THEN
    X_GEN_TAC `x:real^N` THEN
    ASM_CASES_TAC `(x:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `?n. (x:real^N) IN ball(vec 0,&n)` MP_TAC THENL
     [REWRITE_TAC[IN_BALL_0; REAL_ARCH_LT];
      GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
      DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN ASM_CASES_TAC `n = 0` THENL
       [ASM_REWRITE_TAC[IN_BALL_0; GSYM REAL_NOT_LE; NORM_POS_LE];
        STRIP_TAC THEN EXISTS_TAC `n - 1` THEN REWRITE_TAC[IN_DIFF] THEN
        ASM_SIMP_TAC[REAL_OF_NUM_ADD; SUB_ADD; LE_1] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]];
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(MATCH_MP MONO_FORALL (GEN `n:num`
   (ISPECL
     [`s INTER (ball(vec 0:real^N,&n + &1) DIFF ball(vec 0,&n))`;
      `--(vec(n + 1)):real^N`; `vec(n + 1):real^N`;
      `e / &2 / &2 pow n`]
        MEASURABLE_OUTER_INTERVALS_BOUNDED))) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF; REAL_LT_POW2] THEN
    ASM_SIMP_TAC[MEASURABLE_INTER; MEASURABLE_DIFF; MEASURABLE_BALL] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_INTERVAL; IN_BALL_0; IN_DIFF; REAL_NOT_LT;
      REAL_OF_NUM_ADD; VECTOR_NEG_COMPONENT; VEC_COMPONENT; REAL_BOUNDS_LE] THEN
    MESON_TAC[COMPONENT_LE_NORM; REAL_LET_TRANS; REAL_LT_IMP_LE];
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; FORALL_AND_THM]] THEN
  X_GEN_TAC `d:num->(real^N->bool)->bool` THEN STRIP_TAC THEN
  EXISTS_TAC `UNIONS {d n | n IN (:num)} :(real^N->bool)->bool` THEN
  REWRITE_TAC[lemma] THEN CONJ_TAC THENL
   [MATCH_MP_TAC COUNTABLE_UNIONS THEN
    ASM_REWRITE_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE] THEN
    SIMP_TAC[COUNTABLE_IMAGE; NUM_COUNTABLE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_UNIONS; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    ASM_SIMP_TAC[FORALL_IN_GSPEC; IN_UNIV] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_UNIONS; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    ASM_SIMP_TAC[FORALL_IN_GSPEC; IN_UNIV; IN_UNIONS] THEN
    REWRITE_TAC[EXISTS_IN_GSPEC] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
   `sum(0..n) (\k. measure(s INTER (ball(vec 0:real^N,&k + &1) DIFF
                                  ball(vec 0,&k))) + e / &2 / &2 pow k)` THEN
  ASM_SIMP_TAC[SUM_LE_NUMSEG] THEN REWRITE_TAC[SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (rand o rand) MEASURE_DISJOINT_UNIONS_IMAGE o
      lhand o snd) THEN
    ASM_SIMP_TAC[DISJOINT; FINITE_NUMSEG; MEASURABLE_DIFF; MEASURABLE_INTER;
                 MEASURABLE_BALL] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC MEASURE_SUBSET THEN
    ASM_SIMP_TAC[MEASURABLE_UNIONS; FORALL_IN_IMAGE; FINITE_NUMSEG;
      FINITE_IMAGE; MEASURABLE_DIFF; MEASURABLE_INTER; MEASURABLE_BALL] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
    MATCH_MP_TAC SUBSET_UNIONS THEN REWRITE_TAC[SIMPLE_IMAGE] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET_UNIV];
    REWRITE_TAC[real_div; SUM_LMUL; REAL_INV_POW; SUM_GP; LT] THEN
    REWRITE_TAC[GSYM real_div] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_ARITH `e / &2 * (&1 - x) / (&1 / &2) <= e <=>
                            &0 <= e * x`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_POW_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV]);;

let MEASURABLE_OUTER_OPEN_INTERVALS = prove
 (`!s:real^N->bool e.
        measurable s /\ &0 < e
        ==> ?d. COUNTABLE d /\
                (!k. k IN d ==> ~(k = {}) /\ (?a b. k = interval(a,b))) /\
                s SUBSET UNIONS d /\
                measurable (UNIONS d) /\
                measure (UNIONS d) <= measure s + e`,
  let lemma = prove
   (`!s. UNIONS(s DELETE {}) = UNIONS s`,
    REWRITE_TAC[EXTENSION; IN_UNIONS; IN_DELETE] THEN
    MESON_TAC[NOT_IN_EMPTY]) in
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `e / &2`]
    MEASURABLE_OUTER_CLOSED_INTERVALS) THEN
  ASM_REWRITE_TAC[REAL_HALF; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `dset:(real^N->bool)->bool` THEN
  ASM_CASES_TAC `dset:(real^N->bool)->bool = {}` THENL
   [ASM_REWRITE_TAC[UNIONS_0; SUBSET_EMPTY] THEN STRIP_TAC THEN
    EXISTS_TAC `{}:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[UNIONS_0; NOT_IN_EMPTY; MEASURE_EMPTY; SUBSET_REFL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN
   `?f. dset = IMAGE (f:num->(real^N->bool)) (:num) DELETE {} /\
        (!m n. f m = f n ==> m = n \/ f n = {})`
  MP_TAC THENL
   [ASM_CASES_TAC `FINITE(dset:(real^N->bool)->bool)` THENL
     [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FINITE_HAS_SIZE]) THEN
      DISCH_THEN(MP_TAC o MATCH_MP HAS_SIZE_INDEX) THEN
      ABBREV_TAC `m = CARD(dset:(real^N->bool)->bool)` THEN
      DISCH_THEN(X_CHOOSE_THEN `f:num->real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `\i. if i < m then (f:num->real^N->bool) i else {}` THEN
      REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
      GEN_REWRITE_TAC I [EXTENSION] THEN
      REWRITE_TAC[IN_DELETE; IN_IMAGE; IN_UNIV] THEN ASM_MESON_TAC[];
      MP_TAC(ISPEC `dset:(real^N->bool)->bool`
        COUNTABLE_AS_INJECTIVE_IMAGE) THEN
      ASM_REWRITE_TAC[INFINITE] THEN MATCH_MP_TAC MONO_EXISTS THEN
      GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
       [ALL_TAC; ASM_MESON_TAC[]] THEN
      ASM_REWRITE_TAC[SET_RULE `s = s DELETE a <=> ~(a IN s)`] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `d:num->real^N->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV; FORALL_AND_THM; SKOLEM_THM;
              IMP_CONJ; RIGHT_FORALL_IMP_THM; IN_DELETE; lemma] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (MESON[]
   `(!x. ~(P x) ==> ~(P x) /\ Q x) ==> (!x. P x ==> Q x) ==> !x. Q x`)) THEN
  ANTS_TAC THENL [MESON_TAC[EMPTY_AS_INTERVAL]; ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:num->real^N`; `b:num->real^N`] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
  GEN_REWRITE_TAC I [IMP_CONJ] THEN
  DISCH_THEN(MP_TAC o MATCH_MP(MESON[]
   `(!x y. ~(P x) /\ ~(P y) /\ ~(f x = f y) ==> Q x y)
    ==> (!x y. P x ==> Q x y) /\ (!x y. P y ==> Q x y)
        ==> (!x y. ~(f x = f y) ==> Q x y)`)) THEN
  SIMP_TAC[INTERIOR_EMPTY; INTER_EMPTY] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?d. COUNTABLE d /\
        (!k. k IN d ==> ?a b:real^N. k = interval(a,b)) /\
        s SUBSET UNIONS d /\
        measurable (UNIONS d) /\
        measure (UNIONS d) <= measure s + e`
  MP_TAC THENL
   [ALL_TAC;
    DISCH_THEN(X_CHOOSE_TAC `d:(real^N->bool)->bool`) THEN
    EXISTS_TAC `d DELETE ({}:real^N->bool)` THEN
    ASM_SIMP_TAC[lemma; COUNTABLE_DELETE; IN_DELETE]] THEN
  MP_TAC(GEN `n:num` (ISPECL [`(a:num->real^N) n`; `(b:num->real^N) n`;
    `e / &2 pow (n + 2)`] EXPAND_CLOSED_OPEN_INTERVAL)) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_POW2; SKOLEM_THM] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; FORALL_AND_THM] THEN
  MAP_EVERY X_GEN_TAC [`A:num->real^N`; `B:num->real^N`] THEN STRIP_TAC THEN
  EXISTS_TAC `IMAGE (\n. interval(A n:real^N,B n)) (:num)` THEN
  SIMP_TAC[COUNTABLE_IMAGE; NUM_COUNTABLE; FORALL_IN_IMAGE; IN_UNIV] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] SUBSET_TRANS)) THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_UNIONS] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `x:real^N`] THEN
    ASM_REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; IN_UNIV] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
  MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE THEN
  REWRITE_TAC[MEASURABLE_INTERVAL] THEN X_GEN_TAC `n:num` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
   `sum(0..n) (\i. measure(interval[a i:real^N,b i]) + e / &2 pow (i + 2))` THEN
  ASM_SIMP_TAC[SUM_LE_NUMSEG] THEN REWRITE_TAC[SUM_ADD_NUMSEG] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; SUM_LMUL; REAL_POW_ADD; SUM_RMUL] THEN
  REWRITE_TAC[REAL_INV_POW; SUM_GP; LT] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC(REAL_ARITH
   `s <= m + e / &2 /\ &0 <= e * x
    ==> s + e * (&1 - x) / (&1 / &2) * &1 / &4 <= m + e`) THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_LT_IMP_LE;
               REAL_LE_DIV; REAL_POS] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS)) THEN
  W(MP_TAC o PART_MATCH (rhs o rand) MEASURE_NEGLIGIBLE_UNIONS_IMAGE o
        lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG; MEASURABLE_INTERVAL] THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `interval[(a:num->real^N) i,b i] = interval[a j,b j]` THENL
     [UNDISCH_TAC
       `!m n. (d:num->real^N->bool) m = d n ==> m = n \/ d n = {}` THEN
      DISCH_THEN(MP_TAC o SPECL [`i:num`; `j:num`]) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INTER_EMPTY; NEGLIGIBLE_EMPTY];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE
       (BINDER_CONV o BINDER_CONV o RAND_CONV o LAND_CONV)
       [GSYM INTERIOR_INTER]) THEN
      DISCH_THEN(MP_TAC o SPECL [`i:num`; `j:num`]) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM HAS_MEASURE_0; HAS_MEASURE_MEASURABLE_MEASURE] THEN
      SIMP_TAC[MEASURABLE_INTER; MEASURABLE_INTERVAL] THEN
      MATCH_MP_TAC(MESON[MEASURE_EMPTY]
       `measure(interior s) = measure s
        ==> interior s = {} ==> measure s = &0`) THEN
      MATCH_MP_TAC MEASURE_INTERIOR THEN
      SIMP_TAC[BOUNDED_INTER; BOUNDED_INTERVAL; NEGLIGIBLE_CONVEX_FRONTIER;
               CONVEX_INTER; CONVEX_INTERVAL]];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC MEASURE_SUBSET THEN CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_UNIONS THEN
    SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; MEASURABLE_INTERVAL;
             FINITE_NUMSEG];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_UNIONS THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    ASM_REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN MESON_TAC[]]);;

let MEASURABLE_OUTER_OPEN = prove
 (`!s:real^N->bool e.
        measurable s /\ &0 < e
        ==> ?t. open t /\ s SUBSET t /\
                measurable t /\ measure t < measure s + e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `e / &2`]
    MEASURABLE_OUTER_OPEN_INTERVALS) THEN
  ASM_REWRITE_TAC[REAL_HALF; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `d:(real^N->bool)->bool` THEN STRIP_TAC THEN
  EXISTS_TAC `UNIONS d :real^N->bool` THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < e /\ m <= s + e / &2 ==> m < s + e`] THEN
  MATCH_MP_TAC OPEN_UNIONS THEN ASM_MESON_TAC[OPEN_INTERVAL]);;

let MEASURABLE_INNER_COMPACT = prove
 (`!s:real^N->bool e.
        measurable s /\ &0 < e
        ==> ?t. compact t /\ t SUBSET s /\
                measurable t /\ measure s < measure t + e`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_MEASURE_MEASURE]) THEN
  GEN_REWRITE_TAC LAND_CONV [HAS_MEASURE_LIMIT] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &4`) THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> &0 < e / &4`] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MP_TAC(ISPEC `ball(vec 0:real^N,B)` BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  REWRITE_TAC[BOUNDED_BALL; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real^N`; `b:real^N`]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `z:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL  [`interval[a:real^N,b] DIFF s`; `e/ &4`]
        MEASURABLE_OUTER_OPEN) THEN
  ASM_SIMP_TAC[MEASURABLE_DIFF; MEASURABLE_INTERVAL;
               REAL_ARITH `&0 < e ==> &0 < e / &4`] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `interval[a:real^N,b] DIFF t` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN
    ASM_SIMP_TAC[CLOSED_DIFF; CLOSED_INTERVAL; BOUNDED_DIFF; BOUNDED_INTERVAL];
    ASM SET_TAC[];
    ASM_SIMP_TAC[MEASURABLE_DIFF; MEASURABLE_INTERVAL];
    MATCH_MP_TAC(REAL_ARITH
        `&0 < e /\
         measure(s) < measure(interval[a,b] INTER s) + e / &4 /\
         measure(t) < measure(interval[a,b] DIFF s) + e / &4 /\
         measure(interval[a,b] INTER s) +
         measure(interval[a,b] DIFF s) = measure(interval[a,b]) /\
         measure(interval[a,b] INTER t) +
         measure(interval[a,b] DIFF t) = measure(interval[a,b]) /\
         measure(interval[a,b] INTER t) <= measure t
         ==> measure s < measure(interval[a,b] DIFF t) + e`) THEN
    ASM_SIMP_TAC[MEASURE_SUBSET; INTER_SUBSET; MEASURABLE_INTER;
                 MEASURABLE_INTERVAL] THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(SUBST_ALL_TAC o SYM o MATCH_MP MEASURE_UNIQUE) THEN
      ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REAL_ARITH_TAC;
      CONJ_TAC THEN MATCH_MP_TAC MEASURE_DISJOINT_UNION_EQ THEN
      ASM_SIMP_TAC[MEASURABLE_INTER; MEASURABLE_DIFF; MEASURABLE_INTERVAL] THEN
      SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Hence for linear transformation, suffices to check compact intervals.     *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_LINEAR_IMAGE_INTERVAL = prove
 (`!f a b. linear f ==> measurable(IMAGE f (interval[a,b]))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_CONVEX THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONVEX_LINEAR_IMAGE THEN
    ASM_MESON_TAC[CONVEX_INTERVAL];
    MATCH_MP_TAC BOUNDED_LINEAR_IMAGE THEN
    ASM_MESON_TAC[BOUNDED_INTERVAL]]);;

let HAS_MEASURE_LINEAR_SUFFICIENT = prove
 (`!f:real^N->real^N m.
        linear f /\
        (!a b. IMAGE f (interval[a,b]) has_measure
               (m * measure(interval[a,b])))
        ==> !s. measurable s ==> (IMAGE f s) has_measure (m * measure s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISJ_CASES_TAC(REAL_ARITH `m < &0 \/ &0 <= m`) THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`vec 0:real^N`; `vec 1:real^N`]) THEN
    DISCH_THEN(MP_TAC o MATCH_MP HAS_MEASURE_POS_LE) THEN
    MATCH_MP_TAC(TAUT `~a ==> a ==> b`) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < --m * x ==> ~(&0 <= m * x)`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_NEG_GT0] THEN
    REWRITE_TAC[MEASURE_INTERVAL] THEN MATCH_MP_TAC CONTENT_POS_LT THEN
    SIMP_TAC[VEC_COMPONENT; REAL_LT_01];
    ALL_TAC] THEN
  ASM_CASES_TAC `!x y. (f:real^N->real^N) x = f y ==> x = y` THENL
   [ALL_TAC;
    SUBGOAL_THEN `!s. negligible(IMAGE (f:real^N->real^N) s)` ASSUME_TAC THENL
     [ASM_MESON_TAC[NEGLIGIBLE_LINEAR_SINGULAR_IMAGE]; ALL_TAC] THEN
    SUBGOAL_THEN `m * measure(interval[vec 0:real^N,vec 1]) = &0` MP_TAC THENL
     [MATCH_MP_TAC(ISPEC `IMAGE (f:real^N->real^N) (interval[vec 0,vec 1])`
        HAS_MEASURE_UNIQUE) THEN
      ASM_REWRITE_TAC[HAS_MEASURE_0];
      REWRITE_TAC[REAL_ENTIRE; MEASURE_INTERVAL] THEN
      MATCH_MP_TAC(TAUT `~b /\ (a ==> c) ==> a \/ b ==> c`) THEN CONJ_TAC THENL
       [SIMP_TAC[CONTENT_EQ_0_INTERIOR; INTERIOR_CLOSED_INTERVAL;
                 INTERVAL_NE_EMPTY; VEC_COMPONENT; REAL_LT_01];
        ASM_SIMP_TAC[REAL_MUL_LZERO; HAS_MEASURE_0]]]] THEN
  MP_TAC(ISPEC `f:real^N->real^N` LINEAR_INJECTIVE_ISOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` STRIP_ASSUME_TAC) THEN
  UNDISCH_THEN `!x y. (f:real^N->real^N) x = f y ==> x = y` (K ALL_TAC) THEN
  SUBGOAL_THEN
   `!s. bounded s /\ measurable s
        ==> (IMAGE (f:real^N->real^N) s) has_measure (m * measure s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!d. COUNTABLE d /\
          (!k. k IN d ==> k SUBSET interval[a,b] /\ ~(k = {}) /\
                          (?c d. k = interval[c,d])) /\
          (!k1 k2. k1 IN d /\ k2 IN d /\ ~(k1 = k2)
                   ==> interior k1 INTER interior k2 = {})
          ==> IMAGE (f:real^N->real^N) (UNIONS d) has_measure
                    (m * measure(UNIONS d))`
    ASSUME_TAC THENL
     [REWRITE_TAC[IMAGE_UNIONS] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN
       `!g:real^N->real^N.
          linear g
          ==> !k l. k IN d /\ l IN d /\ ~(k = l)
                    ==> negligible((IMAGE g k) INTER (IMAGE g l))`
      MP_TAC THENL
       [REPEAT STRIP_TAC THEN
        ASM_CASES_TAC `!x y. (g:real^N->real^N) x = g y ==> x = y` THENL
         [ALL_TAC;
          ASM_MESON_TAC[NEGLIGIBLE_LINEAR_SINGULAR_IMAGE;
                        NEGLIGIBLE_INTER]] THEN
        MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
        EXISTS_TAC `frontier(IMAGE (g:real^N->real^N) k INTER IMAGE g l) UNION
                    interior(IMAGE g k INTER IMAGE g l)` THEN
        CONJ_TAC THENL
         [ALL_TAC;
          REWRITE_TAC[frontier] THEN MATCH_MP_TAC(SET_RULE
           `s SUBSET t ==> s SUBSET (t DIFF u) UNION u`) THEN
          REWRITE_TAC[CLOSURE_SUBSET]] THEN
        MATCH_MP_TAC NEGLIGIBLE_UNION THEN CONJ_TAC THENL
         [MATCH_MP_TAC NEGLIGIBLE_CONVEX_FRONTIER THEN
          MATCH_MP_TAC CONVEX_INTER THEN CONJ_TAC THEN
          MATCH_MP_TAC CONVEX_LINEAR_IMAGE THEN ASM_MESON_TAC[CONVEX_INTERVAL];
          ALL_TAC] THEN
        REWRITE_TAC[INTERIOR_INTER] THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
        EXISTS_TAC `IMAGE (g:real^N->real^N) (interior k) INTER
                    IMAGE g (interior l)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
          EXISTS_TAC
           `IMAGE (g:real^N->real^N) (interior k INTER interior l)` THEN
          CONJ_TAC THENL
           [ASM_SIMP_TAC[IMAGE_CLAUSES; NEGLIGIBLE_EMPTY]; ASM SET_TAC[]];
          MATCH_MP_TAC(SET_RULE
           `s SUBSET u /\ t SUBSET v ==> (s INTER t) SUBSET (u INTER v)`) THEN
          CONJ_TAC THEN MATCH_MP_TAC INTERIOR_IMAGE_SUBSET THEN
          ASM_MESON_TAC[LINEAR_CONTINUOUS_AT]];
        ALL_TAC] THEN
      DISCH_THEN(fun th -> MP_TAC(SPEC `f:real^N->real^N` th) THEN
          MP_TAC(SPEC `\x:real^N. x` th)) THEN
      ASM_REWRITE_TAC[LINEAR_ID; SET_RULE `IMAGE (\x. x) s = s`] THEN
      REPEAT STRIP_TAC THEN ASM_CASES_TAC `FINITE(d:(real^N->bool)->bool)` THENL
       [MP_TAC(ISPECL [`IMAGE (f:real^N->real^N)`; `d:(real^N->bool)->bool`]
                  HAS_MEASURE_NEGLIGIBLE_UNIONS_IMAGE) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[measurable]; ALL_TAC] THEN
        MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
        MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC `sum d (\k:real^N->bool. m * measure k)` THEN CONJ_TAC THENL
         [MATCH_MP_TAC SUM_EQ THEN ASM_MESON_TAC[MEASURE_UNIQUE]; ALL_TAC] THEN
        REWRITE_TAC[SUM_LMUL] THEN AP_TERM_TAC THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC MEASURE_NEGLIGIBLE_UNIONS THEN
        ASM_REWRITE_TAC[GSYM HAS_MEASURE_MEASURE] THEN
        ASM_MESON_TAC[MEASURABLE_INTERVAL];
        ALL_TAC] THEN
      MP_TAC(ISPEC `d:(real^N->bool)->bool` COUNTABLE_AS_INJECTIVE_IMAGE) THEN
      ASM_REWRITE_TAC[INFINITE] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:num->real^N->bool`
       (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
      MP_TAC(ISPEC `s:num->real^N->bool`
        HAS_MEASURE_COUNTABLE_NEGLIGIBLE_UNIONS_BOUNDED) THEN
      MP_TAC(ISPEC `\n:num. IMAGE (f:real^N->real^N) (s n)`
        HAS_MEASURE_COUNTABLE_NEGLIGIBLE_UNIONS_BOUNDED) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IMP_CONJ; RIGHT_FORALL_IMP_THM;
                                  FORALL_IN_IMAGE; IN_UNIV]) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM]) THEN
      ASM_SIMP_TAC[] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ASM_MESON_TAC[MEASURABLE_LINEAR_IMAGE_INTERVAL];
          ASM_MESON_TAC[];
          ONCE_REWRITE_TAC[GSYM o_DEF] THEN
          REWRITE_TAC[GSYM IMAGE_UNIONS; IMAGE_o] THEN
          MATCH_MP_TAC BOUNDED_LINEAR_IMAGE THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC BOUNDED_SUBSET THEN REWRITE_TAC[UNIONS_SUBSET] THEN
          EXISTS_TAC `interval[a:real^N,b]` THEN
          REWRITE_TAC[BOUNDED_INTERVAL] THEN ASM SET_TAC[]];
        ALL_TAC] THEN
      STRIP_TAC THEN ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ASM_MESON_TAC[MEASURABLE_INTERVAL];
          ASM_MESON_TAC[];
          MATCH_MP_TAC BOUNDED_SUBSET THEN REWRITE_TAC[UNIONS_SUBSET] THEN
          EXISTS_TAC `interval[a:real^N,b]` THEN
          REWRITE_TAC[BOUNDED_INTERVAL] THEN ASM SET_TAC[]];
        ALL_TAC] THEN
      STRIP_TAC THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
      SUBGOAL_THEN `m * measure (UNIONS (IMAGE s (:num)):real^N->bool) =
             measure(UNIONS (IMAGE (\x. IMAGE f (s x)) (:num)):real^N->bool)`
       (fun th -> ASM_REWRITE_TAC[GSYM HAS_MEASURE_MEASURE; th]) THEN
      ONCE_REWRITE_TAC[GSYM LIFT_EQ] THEN
      MATCH_MP_TAC SERIES_UNIQUE THEN
      EXISTS_TAC `\n:num. lift(measure(IMAGE (f:real^N->real^N) (s n)))` THEN
      EXISTS_TAC `from 0` THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUMS_EQ THEN
      EXISTS_TAC `\n:num. m % lift(measure(s n:real^N->bool))` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM LIFT_CMUL; LIFT_EQ] THEN
        ASM_MESON_TAC[MEASURE_UNIQUE];
        REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC SERIES_CMUL THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[HAS_MEASURE_INNER_OUTER_LE] THEN CONJ_TAC THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THENL
     [MP_TAC(ISPECL [`interval[a,b] DIFF s:real^N->bool`; `a:real^N`;
       `b:real^N`; `e / (&1 + abs m)`] MEASURABLE_OUTER_INTERVALS_BOUNDED) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[MEASURABLE_DIFF; MEASURABLE_INTERVAL] THEN
        ASM_SIMP_TAC[REAL_ARITH `&0 < &1 + abs x`; REAL_LT_DIV] THEN SET_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `IMAGE f (interval[a,b]) DIFF
                  IMAGE (f:real^N->real^N) (UNIONS d)` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `d:(real^N->bool)->bool`) THEN
      ASM_SIMP_TAC[IMAGE_SUBSET] THEN DISCH_TAC THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[MEASURABLE_DIFF; measurable]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `measure(IMAGE f (interval[a,b])) -
                  measure(IMAGE (f:real^N->real^N) (UNIONS d))` THEN
      CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC MEASURE_DIFF_SUBSET THEN
        REPEAT(CONJ_TAC THENL [ASM_MESON_TAC[measurable]; ALL_TAC]) THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN ASM_SIMP_TAC[UNIONS_SUBSET]] THEN
      FIRST_ASSUM(ASSUME_TAC o SPECL [`a:real^N`; `b:real^N`]) THEN
      REPEAT(FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP MEASURE_UNIQUE)) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `m * measure(s:real^N->bool) - m * e / (&1 + abs m)` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[REAL_ARITH `a - x <= a - y <=> y <= x`] THEN
        REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
        REWRITE_TAC[GSYM real_div] THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &1 + abs x`] THEN
        GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
        ASM_SIMP_TAC[REAL_LE_RMUL_EQ] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
        `d <= a + e ==> a = i - s ==> s - e <= i - d`)) THEN
      MATCH_MP_TAC MEASURE_DIFF_SUBSET THEN
      ASM_REWRITE_TAC[MEASURABLE_INTERVAL];
      MP_TAC(ISPECL [`s:real^N->bool`; `a:real^N`; `b:real^N`;
                `e / (&1 + abs m)`] MEASURABLE_OUTER_INTERVALS_BOUNDED) THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &1 + abs x`] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `IMAGE (f:real^N->real^N) (UNIONS d)` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `d:(real^N->bool)->bool`) THEN
      ASM_SIMP_TAC[IMAGE_SUBSET] THEN
      SIMP_TAC[HAS_MEASURE_MEASURABLE_MEASURE] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `m * measure(s:real^N->bool) + m * e / (&1 + abs m)` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN ASM_SIMP_TAC[REAL_LE_LMUL];
        REWRITE_TAC[REAL_LE_LADD] THEN
        REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
        REWRITE_TAC[GSYM real_div] THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &1 + abs x`] THEN
        GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
        ASM_SIMP_TAC[REAL_LE_RMUL_EQ] THEN REAL_ARITH_TAC]];
      ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[HAS_MEASURE_LIMIT] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_MEASURE_MEASURE]) THEN
  GEN_REWRITE_TAC LAND_CONV [HAS_MEASURE_LIMIT] THEN
  DISCH_THEN(MP_TAC o SPEC `e / (&1 + abs m)`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &1 + abs x`] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*"))) THEN
  MP_TAC(ISPEC `ball(vec 0:real^N,B)` BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  REWRITE_TAC[BOUNDED_BALL; LEFT_IMP_EXISTS_THM] THEN
  REMOVE_THEN "*" MP_TAC THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `c:real^N` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `d:real^N` THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`interval[c:real^N,d]`; `vec 0:real^N`]
    BOUNDED_SUBSET_BALL) THEN
  REWRITE_TAC[BOUNDED_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `f:real^N->real^N` LINEAR_BOUNDED_POS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN

  EXISTS_TAC `D * C` THEN ASM_SIMP_TAC[REAL_LT_MUL] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `s INTER (IMAGE (h:real^N->real^N) (interval[a,b]))`) THEN
  SUBGOAL_THEN
   `IMAGE (f:real^N->real^N) (s INTER IMAGE h (interval [a,b])) =
    (IMAGE f s) INTER interval[a,b]`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[BOUNDED_INTER; BOUNDED_LINEAR_IMAGE; BOUNDED_INTERVAL] THEN
    ASM_SIMP_TAC[MEASURABLE_INTER; MEASURABLE_LINEAR_IMAGE_INTERVAL];
    ALL_TAC] THEN
  DISCH_TAC THEN EXISTS_TAC
   `m * measure(s INTER (IMAGE (h:real^N->real^N) (interval[a,b])))` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `m * e / (&1 + abs m)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < &1 + abs x`] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[REAL_LT_RMUL_EQ] THEN REAL_ARITH_TAC] THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [real_abs] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `abs(z - m) < e ==> z <= w /\ w <= m ==> abs(w - m) <= e`)) THEN
  SUBST1_TAC(SYM(MATCH_MP MEASURE_UNIQUE
   (ASSUME `s INTER interval [c:real^N,d] has_measure z`))) THEN
  CONJ_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
  ASM_SIMP_TAC[MEASURABLE_INTER; MEASURABLE_LINEAR_IMAGE_INTERVAL;
               MEASURABLE_INTERVAL; INTER_SUBSET] THEN
  MATCH_MP_TAC(SET_RULE
   `!v. t SUBSET v /\ v SUBSET u ==> s INTER t SUBSET s INTER u`) THEN
  EXISTS_TAC `ball(vec 0:real^N,D)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE
   `!f. (!x. h(f x) = x) /\ IMAGE f s SUBSET t ==> s SUBSET IMAGE h t`) THEN
  EXISTS_TAC `f:real^N->real^N` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(vec 0:real^N,D * C)` THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL_0] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `C * norm(x:real^N)` THEN
  ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[REAL_LT_LMUL_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Some inductions by expressing mapping in terms of elementary matrices.    *)
(* ------------------------------------------------------------------------- *)

let INDUCT_MATRIX_ROW_OPERATIONS = prove
 (`!P:real^N^N->bool.
        (!A i. 1 <= i /\ i <= dimindex(:N) /\ row i A = vec 0 ==> P A) /\
        (!A. (!i j. 1 <= i /\ i <= dimindex(:N) /\
                    1 <= j /\ j <= dimindex(:N) /\ ~(i = j)
                    ==> A$i$j = &0) ==> P A) /\
        (!A m n. P A /\ 1 <= m /\ m <= dimindex(:N) /\
                 1 <= n /\ n <= dimindex(:N) /\ ~(m = n)
                 ==> P(lambda i j. A$i$(swap(m,n) j))) /\
        (!A m n c. P A /\ 1 <= m /\ m <= dimindex(:N) /\
                   1 <= n /\ n <= dimindex(:N) /\ ~(m = n)
                   ==> P(lambda i. if i = m then row m A + c % row n A
                                   else row i A))
        ==> !A. P A`,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "zero_row") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "diagonal") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "swap_cols") (LABEL_TAC "row_op")) THEN
  SUBGOAL_THEN
   `!k A:real^N^N.
        (!i j. 1 <= i /\ i <= dimindex(:N) /\
               k <= j /\ j <= dimindex(:N) /\ ~(i = j)
               ==> A$i$j = &0)
        ==> P A`
   (fun th -> GEN_TAC THEN MATCH_MP_TAC th THEN
              EXISTS_TAC `dimindex(:N) + 1` THEN ARITH_TAC) THEN
  MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "diagonal" MATCH_MP_TAC THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[LE_0];
    ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN DISCH_THEN(LABEL_TAC "ind_hyp") THEN
  DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC (ARITH_RULE `k = 0 \/ 1 <= k`) THEN
  ASM_REWRITE_TAC[ARITH] THEN
  ASM_CASES_TAC `k <= dimindex(:N)` THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN REMOVE_THEN "ind_hyp" MATCH_MP_TAC THEN
    ASM_ARITH_TAC] THEN
  SUBGOAL_THEN
   `!A:real^N^N.
        ~(A$k$k = &0) /\
        (!i j. 1 <= i /\ i <= dimindex (:N) /\
               SUC k <= j /\ j <= dimindex (:N) /\ ~(i = j)
               ==> A$i$j = &0)
        ==> P A`
  (LABEL_TAC "nonzero_hyp") THENL
   [ALL_TAC;
    X_GEN_TAC `A:real^N^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `row k (A:real^N^N) = vec 0` THENL
     [REMOVE_THEN "zero_row" MATCH_MP_TAC THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [CART_EQ]) THEN
    SIMP_TAC[VEC_COMPONENT; row; LAMBDA_BETA] THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `l:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `l:num = k` THENL
     [REMOVE_THEN "nonzero_hyp" MATCH_MP_TAC THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REMOVE_THEN "swap_cols" (MP_TAC o SPECL
     [`(lambda i j. (A:real^N^N)$i$swap(k,l) j):real^N^N`;
      `k:num`; `l:num`]) THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN ANTS_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[swap] THEN
      REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA])] THEN
    REMOVE_THEN "nonzero_hyp" MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC[ARITH_RULE `SUC k <= i <=> 1 <= i /\ SUC k <= i`] THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN
    ASM_REWRITE_TAC[swap] THEN MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
    STRIP_TAC THEN SUBGOAL_THEN `l:num <= k` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `l:num`]) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC] THEN
   SUBGOAL_THEN
   `!l A:real^N^N.
        ~(A$k$k = &0) /\
        (!i j. 1 <= i /\ i <= dimindex (:N) /\
               SUC k <= j /\ j <= dimindex (:N) /\ ~(i = j)
               ==> A$i$j = &0) /\
        (!i. l <= i /\ i <= dimindex(:N) /\ ~(i = k) ==> A$i$k = &0)
        ==> P A`
   MP_TAC THENL
    [ALL_TAC;
     DISCH_THEN(MP_TAC o SPEC `dimindex(:N) + 1`) THEN
     REWRITE_TAC[CONJ_ASSOC; ARITH_RULE `~(n + 1 <= i /\ i <= n)`]] THEN
   MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
    [GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
     DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "main") (LABEL_TAC "aux")) THEN
     USE_THEN "ind_hyp" MATCH_MP_TAC THEN
     MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
     ASM_CASES_TAC `j:num = k` THENL
      [ASM_REWRITE_TAC[] THEN USE_THEN "aux" MATCH_MP_TAC THEN ASM_ARITH_TAC;
       REMOVE_THEN "main" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `l:num` THEN DISCH_THEN(LABEL_TAC "inner_hyp") THEN
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "main") (LABEL_TAC "aux")) THEN
  ASM_CASES_TAC `l:num = k` THENL
   [REMOVE_THEN "inner_hyp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN REMOVE_THEN "aux" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISJ_CASES_TAC(ARITH_RULE `l = 0 \/ 1 <= l`) THENL
   [REMOVE_THEN "ind_hyp" MATCH_MP_TAC THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `j:num = k` THENL
     [ASM_REWRITE_TAC[] THEN REMOVE_THEN "aux" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REMOVE_THEN "main" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `l <= dimindex(:N)` THENL
   [ALL_TAC;
    REMOVE_THEN "inner_hyp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC] THEN
  REMOVE_THEN "inner_hyp" (MP_TAC o SPECL
   [`(lambda i. if i = l then row l (A:real^N^N) + --(A$l$k/A$k$k) % row k A
                else row i A):real^N^N`]) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `!i. l <= i ==> 1 <= i` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `SUC k <= j <=> 1 <= j /\ SUC k <= j`] THEN
    ASM_SIMP_TAC[LAMBDA_BETA; row; COND_COMPONENT;
                 VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    ASM_SIMP_TAC[REAL_FIELD `~(y = &0) ==> x + --(x / y) * y = &0`] THEN
    REWRITE_TAC[AND_FORALL_THM] THEN X_GEN_TAC `i:num` THEN
    ASM_CASES_TAC `i:num = l` THEN ASM_REWRITE_TAC[] THENL
     [REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(REAL_RING `x = &0 /\ y = &0 ==> x + z * y = &0`) THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REPEAT STRIP_TAC THEN REMOVE_THEN "aux" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN REMOVE_THEN "row_op" (MP_TAC o SPECL
   [`(lambda i. if i = l then row l A + --(A$l$k / A$k$k) % row k A
                else row i (A:real^N^N)):real^N^N`;
    `l:num`; `k:num`; `(A:real^N^N)$l$k / A$k$k`]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
               VECTOR_MUL_COMPONENT; row; COND_COMPONENT] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let INDUCT_MATRIX_ELEMENTARY = prove
 (`!P:real^N^N->bool.
        (!A B. P A /\ P B ==> P(A ** B)) /\
        (!A i. 1 <= i /\ i <= dimindex(:N) /\ row i A = vec 0 ==> P A) /\
        (!A. (!i j. 1 <= i /\ i <= dimindex(:N) /\
                    1 <= j /\ j <= dimindex(:N) /\ ~(i = j)
                    ==> A$i$j = &0) ==> P A) /\
        (!m n. 1 <= m /\ m <= dimindex(:N) /\
               1 <= n /\ n <= dimindex(:N) /\ ~(m = n)
               ==> P(lambda i j. (mat 1:real^N^N)$i$(swap(m,n) j))) /\
        (!m n c. 1 <= m /\ m <= dimindex(:N) /\
                 1 <= n /\ n <= dimindex(:N) /\ ~(m = n)
                 ==> P(lambda i j. if i = m /\ j = n then c
                                   else if i = j then &1 else &0))
        ==> !A. P A`,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(fun th ->
    MATCH_MP_TAC INDUCT_MATRIX_ROW_OPERATIONS THEN MP_TAC th) THEN
  REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THEN REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> X_GEN_TAC `A:real^N^N` THEN MP_TAC th) THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(P:real^N^N->bool) A` THENL
   [REWRITE_TAC[GSYM IMP_CONJ]; REWRITE_TAC[GSYM IMP_CONJ_ALT]] THEN
  DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN MATCH_MP_TAC EQ_IMP THEN
  AP_TERM_TAC THEN REWRITE_TAC[CART_EQ] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA; matrix_mul; row] THENL
   [ASM_SIMP_TAC[mat; IN_DIMINDEX_SWAP; LAMBDA_BETA] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    SIMP_TAC[SUM_DELTA; REAL_MUL_RZERO; REAL_MUL_RID] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[swap; IN_NUMSEG]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `i:num = m` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    REWRITE_TAC[REAL_MUL_LZERO] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    ASM_SIMP_TAC[SUM_DELTA; LAMBDA_BETA; IN_NUMSEG; REAL_MUL_LID]] THEN
  ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; LAMBDA_BETA] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `sum {m,n} (\k. (if k = n then c else if m = k then &1 else &0) *
                    (A:real^N^N)$k$j)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUPERSET THEN
    ASM_SIMP_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM;
                 IN_NUMSEG; REAL_MUL_LZERO] THEN
    ASM_ARITH_TAC;
    ASM_SIMP_TAC[SUM_CLAUSES; FINITE_RULES; IN_INSERT; NOT_IN_EMPTY] THEN
    REAL_ARITH_TAC]);;

let INDUCT_MATRIX_ELEMENTARY_ALT = prove
 (`!P:real^N^N->bool.
        (!A B. P A /\ P B ==> P(A ** B)) /\
        (!A i. 1 <= i /\ i <= dimindex(:N) /\ row i A = vec 0 ==> P A) /\
        (!A. (!i j. 1 <= i /\ i <= dimindex(:N) /\
                    1 <= j /\ j <= dimindex(:N) /\ ~(i = j)
                    ==> A$i$j = &0) ==> P A) /\
        (!m n. 1 <= m /\ m <= dimindex(:N) /\
               1 <= n /\ n <= dimindex(:N) /\ ~(m = n)
               ==> P(lambda i j. (mat 1:real^N^N)$i$(swap(m,n) j))) /\
        (!m n. 1 <= m /\ m <= dimindex(:N) /\
               1 <= n /\ n <= dimindex(:N) /\ ~(m = n)
               ==> P(lambda i j. if i = m /\ j = n \/ i = j then &1 else &0))
        ==> !A. P A`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC INDUCT_MATRIX_ELEMENTARY THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `c = &0` THENL
   [FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th THEN
        MAP_EVERY X_GEN_TAC [`i:num`; `j:num`]) THEN
    ASM_SIMP_TAC[LAMBDA_BETA; COND_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(lambda i j. if i = m /\ j = n then c else if i = j then &1 else &0) =
  ((lambda i j. if i = j then if j = n then inv c else &1 else &0):real^N^N) **
    ((lambda i j. if i = m /\ j = n \/ i = j then &1 else &0):real^N^N) **
    ((lambda i j. if i = j then if j = n then c else &1 else &0):real^N^N)`
  SUBST1_TAC THENL
   [ALL_TAC;
    REPEAT(MATCH_MP_TAC(ASSUME `!A B:real^N^N. P A /\ P B ==> P(A ** B)`) THEN
           CONJ_TAC) THEN
    ASM_SIMP_TAC[] THEN FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th THEN
        MAP_EVERY X_GEN_TAC [`i:num`; `j:num`]) THEN
    ASM_SIMP_TAC[LAMBDA_BETA]] THEN
  SIMP_TAC[CART_EQ; matrix_mul; LAMBDA_BETA] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SUM_DELTA; IN_NUMSEG; REAL_ARITH
       `(if p then &1 else &0) * (if q then c else &0) =
        if q then if p then c else &0 else &0`] THEN
  REWRITE_TAC[REAL_ARITH
   `(if p then x else &0) * y = (if p then x * y else &0)`] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
  ASM_SIMP_TAC[SUM_DELTA; IN_NUMSEG] THEN
  ASM_CASES_TAC `i:num = m` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `j:num = n` THEN ASM_REWRITE_TAC[REAL_MUL_LID; EQ_SYM_EQ] THEN
  ASM_CASES_TAC `i:num = n` THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_MUL_LID; REAL_MUL_RZERO]);;

(* ------------------------------------------------------------------------- *)
(* The same thing in mapping form (might have been easier all along).        *)
(* ------------------------------------------------------------------------- *)

let INDUCT_LINEAR_ELEMENTARY = prove
 (`!P. (!f g. linear f /\ linear g /\ P f /\ P g ==> P(f o g)) /\
       (!f i. linear f /\ 1 <= i /\ i <= dimindex(:N) /\ (!x. (f x)$i = &0)
              ==> P f) /\
       (!c. P(\x. lambda i. c i * x$i)) /\
       (!m n. 1 <= m /\ m <= dimindex(:N) /\
              1 <= n /\ n <= dimindex(:N) /\ ~(m = n)
              ==> P(\x. lambda i. x$swap(m,n) i)) /\
       (!m n. 1 <= m /\ m <= dimindex(:N) /\
              1 <= n /\ n <= dimindex(:N) /\ ~(m = n)
              ==> P(\x. lambda i. if i = m then x$m + x$n else x$i))
       ==> !f:real^N->real^N. linear f ==> P f`,
  GEN_TAC THEN
  MP_TAC(ISPEC `\A:real^N^N. P(\x:real^N. A ** x):bool`
    INDUCT_MATRIX_ELEMENTARY_ALT) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC MONO_IMP THEN CONJ_TAC THENL
   [ALL_TAC;
    DISCH_TAC THEN X_GEN_TAC `f:real^N->real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `matrix(f:real^N->real^N)`) THEN
    ASM_SIMP_TAC[MATRIX_WORKS] THEN REWRITE_TAC[ETA_AX]] THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
   [DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`A:real^N^N`; `B:real^N^N`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
     [`\x:real^N. (A:real^N^N) ** x`; `\x:real^N. (B:real^N^N) ** x`]) THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR; o_DEF] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
   [DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`A:real^N^N`; `m:num`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
     [`\x:real^N. (A:real^N^N) ** x`; `m:num`]) THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `row m (A:real^N^N) = vec 0` THEN
    ASM_SIMP_TAC[CART_EQ; row; LAMBDA_BETA; VEC_COMPONENT; matrix_vector_mul;
                 REAL_MUL_LZERO; SUM_0];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `A:real^N^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `\i. (A:real^N^N)$i$i`) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[CART_EQ; matrix_vector_mul; FUN_EQ_THM; LAMBDA_BETA] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `i:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
     `sum(1..dimindex(:N)) (\j. if j = i then (A:real^N^N)$i$j * (x:real^N)$j
                                else &0)` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[SUM_DELTA; IN_NUMSEG]; ALL_TAC] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_MUL_LZERO];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `m:num` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[CART_EQ; matrix_vector_mul; FUN_EQ_THM; LAMBDA_BETA;
               mat; IN_DIMINDEX_SWAP]
  THENL
   [ONCE_REWRITE_TAC[SWAP_GALOIS] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
    ONCE_REWRITE_TAC[COND_RATOR] THEN
    SIMP_TAC[SUM_DELTA; REAL_MUL_LID; REAL_MUL_LZERO; IN_NUMSEG] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[swap] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`x:real^N`; `i:num`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `i:num = m` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    ASM_SIMP_TAC[SUM_DELTA; REAL_MUL_LZERO; REAL_MUL_LID; IN_NUMSEG] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
     `sum {m,n} (\j. if n = j \/ j = m then (x:real^N)$j else &0)` THEN
    CONJ_TAC THENL
     [SIMP_TAC[SUM_CLAUSES; FINITE_RULES; IN_INSERT; NOT_IN_EMPTY] THEN
      ASM_REWRITE_TAC[REAL_ADD_RID];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN
      ASM_SIMP_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM;
                   IN_NUMSEG; REAL_MUL_LZERO] THEN
      ASM_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Hence the effect of an arbitrary linear map on a measurable set.          *)
(* ------------------------------------------------------------------------- *)

let LAMBDA_SWAP_GALOIS = prove
 (`!x:real^N y:real^N.
        1 <= m /\ m <= dimindex(:N) /\ 1 <= n /\ n <= dimindex(:N)
        ==> (x = (lambda i. y$swap(m,n) i) <=>
             (lambda i. x$swap(m,n) i) = y)`,
  SIMP_TAC[CART_EQ; LAMBDA_BETA; IN_DIMINDEX_SWAP] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THEN
  DISCH_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `swap(m,n) (i:num)`) THEN
  ASM_SIMP_TAC[IN_DIMINDEX_SWAP] THEN
  ASM_MESON_TAC[REWRITE_RULE[FUN_EQ_THM; o_THM; I_THM] SWAP_IDEMPOTENT]);;

let LAMBDA_ADD_GALOIS = prove
 (`!x:real^N y:real^N.
        1 <= m /\ m <= dimindex(:N) /\ 1 <= n /\ n <= dimindex(:N) /\
        ~(m = n)
        ==> (x = (lambda i. if i = m then y$m + y$n else y$i) <=>
             (lambda i. if i = m then x$m - x$n else x$i) = y)`,
  SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THEN
  DISCH_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let HAS_MEASURE_SHEAR_INTERVAL = prove
 (`!a b:real^N m n.
        1 <= m /\ m <= dimindex(:N) /\
        1 <= n /\ n <= dimindex(:N) /\
        ~(m = n) /\ ~(interval[a,b] = {}) /\
        &0 <= a$n
        ==> (IMAGE (\x. (lambda i. if i = m then x$m + x$n else x$i))
                   (interval[a,b]):real^N->bool)
            has_measure measure (interval [a,b])`,
  let lemma = prove
   (`!s t u v:real^N->bool.
          measurable s /\ measurable t /\ measurable u /\
          negligible(s INTER t) /\ negligible(s INTER u) /\
          negligible(t INTER u) /\
          s UNION t UNION u = v
          ==> v has_measure (measure s) + (measure t) + (measure u)`,
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[HAS_MEASURE_MEASURABLE_MEASURE; MEASURABLE_UNION] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[MEASURE_UNION; MEASURABLE_UNION] THEN
    ASM_SIMP_TAC[MEASURE_EQ_0; UNION_OVER_INTER; MEASURE_UNION;
                 MEASURABLE_UNION; NEGLIGIBLE_INTER; MEASURABLE_INTER] THEN
    REAL_ARITH_TAC)
  and lemma' = prove
   (`!s t u a:real^N.
          measurable s /\ measurable t /\
          s UNION (IMAGE (\x. a + x) t) = u /\
          negligible(s INTER (IMAGE (\x. a + x) t))
          ==> measure s + measure t = measure u`,
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    ASM_SIMP_TAC[MEASURE_NEGLIGIBLE_UNION; MEASURABLE_TRANSLATION_EQ;
                 MEASURE_TRANSLATION]) in
  REWRITE_TAC[INTERVAL_NE_EMPTY] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `linear((\x. lambda i. if i = m then x$m + x$n else x$i):real^N->real^N)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[linear; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
                 VECTOR_MUL_COMPONENT; CART_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`IMAGE (\x. lambda i. if i = m then x$m + x$n else x$i)
            (interval[a:real^N,b]):real^N->bool`;
    `interval[a,(lambda i. if i = m then (b:real^N)$m + b$n else b$i)] INTER
       {x:real^N | (basis m - basis n) dot x <= a$m}`;
    `interval[a,(lambda i. if i = m then b$m + b$n else b$i)] INTER
       {x:real^N | (basis m - basis n) dot x >= (b:real^N)$m}`;
    `interval[a:real^N,
              (lambda i. if i = m then (b:real^N)$m + b$n else b$i)]`]
     lemma) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CONVEX_LINEAR_IMAGE; CONVEX_INTERVAL;
                 CONVEX_HALFSPACE_LE; CONVEX_HALFSPACE_GE;
                 CONVEX_INTER; MEASURABLE_CONVEX; BOUNDED_INTER;
                 BOUNDED_LINEAR_IMAGE; BOUNDED_INTERVAL] THEN
    REWRITE_TAC[INTER] THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_IMAGE] THEN
    ASM_SIMP_TAC[LAMBDA_ADD_GALOIS; UNWIND_THM1] THEN
    ASM_SIMP_TAC[IN_INTERVAL; IN_ELIM_THM; LAMBDA_BETA;
                 DOT_BASIS; DOT_LSUB] THEN
    ONCE_REWRITE_TAC[MESON[]
       `(!i:num. P i) <=> P m /\ (!i. ~(i = m) ==> P i)`] THEN
    ASM_SIMP_TAC[] THEN
    REWRITE_TAC[TAUT `(p /\ x) /\ (q /\ x) /\ r <=> x /\ p /\ q /\ r`;
                TAUT `(p /\ x) /\ q /\ (r /\ x) <=> x /\ p /\ q /\ r`;
                TAUT `((p /\ x) /\ q) /\ (r /\ x) /\ s <=>
                            x /\ p /\ q /\ r /\ s`;
            TAUT `(a /\ x \/ (b /\ x) /\ c \/ (d /\ x) /\ e <=> f /\ x) <=>
                  x ==> (a \/ b /\ c \/ d /\ e <=> f)`] THEN
    ONCE_REWRITE_TAC[SET_RULE
     `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
    REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [ALL_TAC;
      GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC NEGLIGIBLE_INTER THEN DISJ2_TAC THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THENL
     [EXISTS_TAC `{x:real^N | (basis m - basis n) dot x = (a:real^N)$m}`;
      EXISTS_TAC `{x:real^N | (basis m - basis n) dot x = (b:real^N)$m}`;
      EXISTS_TAC `{x:real^N | (basis m - basis n) dot x = (b:real^N)$m}`]
    THEN (CONJ_TAC THENL
      [MATCH_MP_TAC NEGLIGIBLE_HYPERPLANE THEN
       REWRITE_TAC[VECTOR_SUB_EQ] THEN
       ASM_MESON_TAC[BASIS_INJ];
       ASM_SIMP_TAC[DOT_LSUB; DOT_BASIS; SUBSET; IN_ELIM_THM;
                    NOT_IN_EMPTY] THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[] THEN
       ASM_REAL_ARITH_TAC]);
    ALL_TAC] THEN
  ASM_SIMP_TAC[HAS_MEASURE_MEASURABLE_MEASURE;
               MEASURABLE_LINEAR_IMAGE_INTERVAL;
               MEASURABLE_INTERVAL] THEN
  MP_TAC(ISPECL
   [`interval[a,(lambda i. if i = m then (b:real^N)$m + b$n else b$i)] INTER
       {x:real^N | (basis m - basis n) dot x <= a$m}`;
    `interval[a,(lambda i. if i = m then b$m + b$n else b$i)] INTER
       {x:real^N | (basis m - basis n) dot x >= (b:real^N)$m}`;
    `interval[a:real^N,
              (lambda i. if i = m then (a:real^N)$m + b$n
                         else (b:real^N)$i)]`;
    `(lambda i. if i = m then (a:real^N)$m - (b:real^N)$m
                else &0):real^N`]
     lemma') THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CONVEX_LINEAR_IMAGE; CONVEX_INTERVAL;
                 CONVEX_HALFSPACE_LE; CONVEX_HALFSPACE_GE;
                 CONVEX_INTER; MEASURABLE_CONVEX; BOUNDED_INTER;
                 BOUNDED_LINEAR_IMAGE; BOUNDED_INTERVAL] THEN
    REWRITE_TAC[INTER] THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_IMAGE] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `x:real^N = (lambda i. p i) + y <=>
                                   x - (lambda i. p i) = y`] THEN
    ASM_SIMP_TAC[IN_INTERVAL; IN_ELIM_THM; LAMBDA_BETA;
                 DOT_BASIS; DOT_LSUB; UNWIND_THM1;
                 VECTOR_SUB_COMPONENT] THEN
    ONCE_REWRITE_TAC[MESON[]
       `(!i:num. P i) <=> P m /\ (!i. ~(i = m) ==> P i)`] THEN
    ASM_SIMP_TAC[REAL_SUB_RZERO] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN
      FIRST_ASSUM(MP_TAC o SPEC `n:num`) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
      ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC
       `!i. ~(i = m)
            ==> 1 <= i /\ i <= dimindex (:N)
                ==> (a:real^N)$i <= (x:real^N)$i /\
                    x$i <= (b:real^N)$i` THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[TAUT `((a /\ b) /\ c) /\ (d /\ e) /\ f <=>
                             (b /\ e) /\ a /\ c /\ d /\ f`] THEN
      ONCE_REWRITE_TAC[SET_RULE
       `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
      MATCH_MP_TAC NEGLIGIBLE_INTER THEN DISJ2_TAC THEN
      MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
      EXISTS_TAC `{x:real^N | (basis m - basis n) dot x = (a:real^N)$m}`
      THEN CONJ_TAC THENL
       [MATCH_MP_TAC NEGLIGIBLE_HYPERPLANE THEN
        REWRITE_TAC[VECTOR_SUB_EQ] THEN
        ASM_MESON_TAC[BASIS_INJ];
        ASM_SIMP_TAC[DOT_LSUB; DOT_BASIS; SUBSET; IN_ELIM_THM;
                     NOT_IN_EMPTY] THEN
        FIRST_ASSUM(MP_TAC o SPEC `n:num`) THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC(REAL_ARITH
   `a = b + c ==> a = x + b ==> x = c`) THEN
  ASM_SIMP_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES;
               LAMBDA_BETA] THEN
  REPEAT(COND_CASES_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `n:num`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]) THEN
  SUBGOAL_THEN `1..dimindex(:N) = m INSERT ((1..dimindex(:N)) DELETE m)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_DELETE; IN_NUMSEG] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[PRODUCT_CLAUSES; FINITE_DELETE; FINITE_NUMSEG] THEN
  ASM_SIMP_TAC[IN_DELETE] THEN
  MATCH_MP_TAC(REAL_RING
   `s1 = s3 /\ s2 = s3
    ==> ((bm + bn) - am) * s1 =
        ((am + bn) - am) * s2 + (bm - am) * s3`) THEN
  CONJ_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN
  SIMP_TAC[IN_DELETE] THEN REAL_ARITH_TAC);;

let HAS_MEASURE_LINEAR_IMAGE = prove
 (`!f:real^N->real^N s.
        linear f /\ measurable s
        ==> (IMAGE f s) has_measure (abs(det(matrix f)) * measure s)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC INDUCT_LINEAR_ELEMENTARY THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`f:real^N->real^N`; `g:real^N->real^N`] THEN
    REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MP_TAC th) THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (MP_TAC o SPEC `IMAGE (g:real^N->real^N) s`)
     (MP_TAC o SPEC `s:real^N->bool`)) THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [HAS_MEASURE_MEASURABLE_MEASURE] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[MATRIX_COMPOSE; DET_MUL; REAL_ABS_MUL] THEN
    REWRITE_TAC[IMAGE_o; GSYM REAL_MUL_ASSOC];

    MAP_EVERY X_GEN_TAC [`f:real^N->real^N`; `m:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(!x y. (f:real^N->real^N) x = f y ==> x = y)`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[LINEAR_SINGULAR_INTO_HYPERPLANE] THEN
      EXISTS_TAC `basis m:real^N` THEN
      ASM_SIMP_TAC[BASIS_NONZERO; DOT_BASIS];
      ALL_TAC] THEN
    MP_TAC(ISPEC `matrix f:real^N^N` INVERTIBLE_DET_NZ) THEN
    ASM_SIMP_TAC[INVERTIBLE_LEFT_INVERSE; MATRIX_LEFT_INVERTIBLE_INJECTIVE;
                 MATRIX_WORKS; REAL_ABS_NUM; REAL_MUL_LZERO] THEN
    DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[HAS_MEASURE_0] THEN
    ASM_SIMP_TAC[NEGLIGIBLE_LINEAR_SINGULAR_IMAGE];

    MAP_EVERY X_GEN_TAC [`c:num->real`; `s:real^N->bool`] THEN
    DISCH_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[HAS_MEASURE_MEASURE]) THEN
    FIRST_ASSUM(MP_TAC o SPEC `c:num->real` o
     MATCH_MP HAS_MEASURE_STRETCH) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC[matrix; LAMBDA_BETA] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) DET_DIAGONAL o rand o snd) THEN
    SIMP_TAC[LAMBDA_BETA; BASIS_COMPONENT; REAL_MUL_RZERO] THEN
    DISCH_THEN(K ALL_TAC) THEN MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN
    REWRITE_TAC[REAL_MUL_RID];

    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_MEASURE_LINEAR_SUFFICIENT THEN
    ASM_SIMP_TAC[linear; LAMBDA_BETA; IN_DIMINDEX_SWAP; VECTOR_ADD_COMPONENT;
                 VECTOR_MUL_COMPONENT; CART_EQ] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
    SUBGOAL_THEN `matrix (\x:real^N. lambda i. x$swap (m,n) i):real^N^N =
                  transp(lambda i j. (mat 1:real^N^N)$i$swap (m,n) j)`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[MATRIX_EQ; LAMBDA_BETA; IN_DIMINDEX_SWAP;
                    matrix_vector_mul; CART_EQ; matrix; mat; basis;
                    COND_COMPONENT; transp] THEN
      REWRITE_TAC[EQ_SYM_EQ];
      ALL_TAC] THEN
    REWRITE_TAC[DET_TRANSP] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) DET_PERMUTE_COLUMNS o
        rand o lhand o rand o snd) THEN
    ASM_SIMP_TAC[PERMUTES_SWAP; IN_NUMSEG; ETA_AX] THEN
    DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[DET_I; REAL_ABS_SIGN; REAL_MUL_RID; REAL_MUL_LID] THEN
    ASM_CASES_TAC `interval[a:real^N,b] = {}` THENL
     [ASM_SIMP_TAC[IMAGE_CLAUSES; HAS_MEASURE_EMPTY; MEASURE_EMPTY];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `~(IMAGE (\x:real^N. lambda i. x$swap (m,n) i)
              (interval[a,b]):real^N->bool = {})`
    MP_TAC THENL [ASM_REWRITE_TAC[IMAGE_EQ_EMPTY]; ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (\x:real^N. lambda i. x$swap (m,n) i)
              (interval[a,b]):real^N->bool =
      interval[(lambda i. a$swap (m,n) i),
               (lambda i. b$swap (m,n) i)]`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTERVAL; IN_IMAGE] THEN
      ASM_SIMP_TAC[LAMBDA_SWAP_GALOIS; UNWIND_THM1] THEN
      SIMP_TAC[LAMBDA_BETA] THEN GEN_TAC THEN EQ_TAC THEN
      DISCH_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `swap(m,n) (i:num)`) THEN
      ASM_SIMP_TAC[IN_DIMINDEX_SWAP] THEN
      ASM_MESON_TAC[REWRITE_RULE[FUN_EQ_THM; o_THM; I_THM] SWAP_IDEMPOTENT];
      ALL_TAC] THEN
    REWRITE_TAC[HAS_MEASURE_MEASURABLE_MEASURE; MEASURABLE_INTERVAL] THEN
    REWRITE_TAC[MEASURE_INTERVAL] THEN
    ASM_SIMP_TAC[CONTENT_CLOSED_INTERVAL; GSYM INTERVAL_NE_EMPTY] THEN
    DISCH_THEN(K ALL_TAC) THEN SIMP_TAC[LAMBDA_BETA] THEN
    ASM_SIMP_TAC[GSYM VECTOR_SUB_COMPONENT; IN_DIMINDEX_SWAP] THEN
    MP_TAC(ISPECL [`\i. (b - a:real^N)$i`; `swap(m:num,n)`; `1..dimindex(:N)`]
                (GSYM PRODUCT_PERMUTE)) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[PERMUTES_SWAP; IN_NUMSEG];

    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_MEASURE_LINEAR_SUFFICIENT THEN
    MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[linear; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
                   VECTOR_MUL_COMPONENT; CART_EQ] THEN REAL_ARITH_TAC;
      DISCH_TAC] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
    SUBGOAL_THEN
      `det(matrix(\x. lambda i. if i = m then (x:real^N)$m + x$n
                                else x$i):real^N^N) = &1`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[matrix; basis; COND_COMPONENT; LAMBDA_BETA] THEN
      FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
       `~(m:num = n) ==> m < n \/ n < m`))
      THENL
       [W(MP_TAC o PART_MATCH (lhs o rand) DET_UPPERTRIANGULAR o lhs o snd);
        W(MP_TAC o PART_MATCH (lhs o rand) DET_LOWERTRIANGULAR o lhs o snd)]
      THEN ASM_SIMP_TAC[LAMBDA_BETA; BASIS_COMPONENT; COND_COMPONENT;
                        matrix; REAL_ADD_RID; COND_ID;
                        PRODUCT_CONST_NUMSEG; REAL_POW_ONE] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REPEAT GEN_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_NUM; REAL_MUL_LID] THEN
    ASM_CASES_TAC `interval[a:real^N,b] = {}` THENL
     [ASM_SIMP_TAC[IMAGE_CLAUSES; HAS_MEASURE_EMPTY; MEASURE_EMPTY];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (\x. lambda i. if i = m then x$m + x$n else x$i) (interval [a,b]) =
      IMAGE (\x:real^N. (lambda i. if i = m \/ i = n then a$n else &0) +
                        x)
            (IMAGE (\x:real^N. lambda i. if i = m then x$m + x$n else x$i)
                   (IMAGE (\x. (lambda i. if i = n then --(a$n) else &0) + x)
                          (interval[a,b])))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC[FUN_EQ_THM; o_THM; VECTOR_ADD_COMPONENT; LAMBDA_BETA;
                   CART_EQ] THEN
      MAP_EVERY X_GEN_TAC [`x:real^N`; `i:num`] THEN
      STRIP_TAC THEN ASM_CASES_TAC `i:num = m` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `i:num = n` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_MEASURE_TRANSLATION THEN
    SUBGOAL_THEN
     `measure(interval[a,b]) =
      measure(IMAGE (\x:real^N. (lambda i. if i = n then --(a$n) else &0) + x)
                    (interval[a,b]):real^N->bool)`
    SUBST1_TAC THENL [REWRITE_TAC[MEASURE_TRANSLATION]; ALL_TAC] THEN
    SUBGOAL_THEN
     `~(IMAGE (\x:real^N. (lambda i. if i = n then --(a$n) else &0) + x)
                    (interval[a,b]):real^N->bool = {})`
    MP_TAC THENL [ASM_SIMP_TAC[IMAGE_EQ_EMPTY]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `c + x:real^N = &1 % x + c`] THEN
    ASM_REWRITE_TAC[IMAGE_AFFINITY_INTERVAL; REAL_POS] THEN
    DISCH_TAC THEN MATCH_MP_TAC HAS_MEASURE_SHEAR_INTERVAL THEN
    ASM_SIMP_TAC[LAMBDA_BETA; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    REAL_ARITH_TAC]);;

let MEASURABLE_LINEAR_IMAGE = prove
 (`!f:real^N->real^N s.
        linear f /\ measurable s ==> measurable(IMAGE f s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_MEASURE_LINEAR_IMAGE) THEN
  SIMP_TAC[HAS_MEASURE_MEASURABLE_MEASURE]);;

let MEASURE_LINEAR_IMAGE = prove
 (`!f:real^N->real^N s.
        linear f /\ measurable s
        ==> measure(IMAGE f s) = abs(det(matrix f)) * measure s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_MEASURE_LINEAR_IMAGE) THEN
  SIMP_TAC[HAS_MEASURE_MEASURABLE_MEASURE]);;

let HAS_MEASURE_LINEAR_IMAGE_ALT = prove
 (`!f:real^N->real^N s m.
        linear f /\ s has_measure m
        ==> (IMAGE f s) has_measure (abs(det(matrix f)) * m)`,
  MESON_TAC[MEASURE_UNIQUE; measurable; HAS_MEASURE_LINEAR_IMAGE]);;

let HAS_MEASURE_LINEAR_IMAGE_SAME = prove
 (`!f s. linear f /\ measurable s /\ abs(det(matrix f)) = &1
         ==> (IMAGE f s) has_measure (measure s)`,
  MESON_TAC[HAS_MEASURE_LINEAR_IMAGE; REAL_MUL_LID]);;

let MEASURE_LINEAR_IMAGE_SAME = prove
 (`!f:real^N->real^N s.
        linear f /\ measurable s /\ abs(det(matrix f)) = &1
        ==> measure(IMAGE f s) = measure s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_MEASURE_LINEAR_IMAGE_SAME) THEN
  SIMP_TAC[HAS_MEASURE_MEASURABLE_MEASURE]);;

let MEASURABLE_LINEAR_IMAGE_EQ = prove
 (`!f:real^N->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (measurable (IMAGE f s) <=> measurable s)`,
  MATCH_ACCEPT_TAC(LINEAR_INVARIANT_RULE MEASURABLE_LINEAR_IMAGE));;

add_linear_invariants [MEASURABLE_LINEAR_IMAGE_EQ];;

let NEGLIGIBLE_LINEAR_IMAGE = prove
 (`!f:real^N->real^N s. linear f /\ negligible s ==> negligible(IMAGE f s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM HAS_MEASURE_0] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HAS_MEASURE_LINEAR_IMAGE_ALT) THEN
  REWRITE_TAC[REAL_MUL_RZERO]);;

let NEGLIGIBLE_LINEAR_IMAGE_EQ = prove
 (`!f:real^N->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (negligible (IMAGE f s) <=> negligible s)`,
  MATCH_ACCEPT_TAC(LINEAR_INVARIANT_RULE NEGLIGIBLE_LINEAR_IMAGE));;

add_linear_invariants [NEGLIGIBLE_LINEAR_IMAGE_EQ];;

let HAS_MEASURE_ORTHOGONAL_IMAGE = prove
 (`!f:real^N->real^N s m.
        orthogonal_transformation f /\ s has_measure m
        ==> (IMAGE f s) has_measure m`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR) THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_MEASURE_LINEAR_IMAGE_ALT) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(REAL_RING `x = &1 ==> x * m = m`) THEN
  REWRITE_TAC[REAL_ARITH `abs x = &1 <=> x = &1 \/ x = -- &1`] THEN
  MATCH_MP_TAC DET_ORTHOGONAL_MATRIX THEN
  ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_MATRIX]);;

let HAS_MEASURE_ORTHOGONAL_IMAGE_EQ = prove
 (`!f:real^N->real^N s m.
        orthogonal_transformation f
        ==> ((IMAGE f s) has_measure m <=> s has_measure m)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  ASM_SIMP_TAC[HAS_MEASURE_ORTHOGONAL_IMAGE] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_INVERSE_o) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
   REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_MEASURE_ORTHOGONAL_IMAGE) THEN
  ASM_SIMP_TAC[GSYM IMAGE_o; IMAGE_I]);;

add_linear_invariants
 [REWRITE_RULE[ORTHOGONAL_TRANSFORMATION] HAS_MEASURE_ORTHOGONAL_IMAGE_EQ];;

let MEASURE_ORTHOGONAL_IMAGE_EQ = prove
 (`!f:real^N->real^N s.
        orthogonal_transformation f
        ==> measure(IMAGE f s) = measure s`,
  SIMP_TAC[measure; HAS_MEASURE_ORTHOGONAL_IMAGE_EQ]);;

add_linear_invariants
 [REWRITE_RULE[ORTHOGONAL_TRANSFORMATION] MEASURE_ORTHOGONAL_IMAGE_EQ];;

(* ------------------------------------------------------------------------- *)
(* Measure of a standard simplex.                                            *)
(* ------------------------------------------------------------------------- *)

let CONGRUENT_IMAGE_STD_SIMPLEX = prove
 (`!p. p permutes 1..dimindex(:N)
       ==> {x:real^N | &0 <= x$(p 1) /\ x$(p(dimindex(:N))) <= &1 /\
                       (!i. 1 <= i /\ i < dimindex(:N)
                            ==> x$(p i) <= x$(p(i + 1)))} =
           IMAGE (\x:real^N. lambda i. sum(1..inverse p(i)) (\j. x$j))
                 {x | (!i. 1 <= i /\ i <= dimindex (:N) ==> &0 <= x$i) /\
                      sum (1..dimindex (:N)) (\i. x$i) <= &1}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^N` THEN
    ASM_SIMP_TAC[IN_ELIM_THM; LAMBDA_BETA; LAMBDA_BETA_PERM; LE_REFL;
                 ARITH_RULE `i < n ==> i <= n /\ i + 1 <= n`;
                 ARITH_RULE `1 <= n + 1`; DIMINDEX_GE_1] THEN
    STRIP_TAC THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP PERMUTES_INVERSES th]) THEN
    ASM_SIMP_TAC[SUM_SING_NUMSEG; DIMINDEX_GE_1; LE_REFL] THEN
    REWRITE_TAC[GSYM ADD1; SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
    ASM_SIMP_TAC[REAL_LE_ADDR] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
  STRIP_TAC THEN
  EXISTS_TAC `(lambda i. if i = 1 then x$(p 1)
                         else (x:real^N)$p(i) - x$p(i - 1)):real^N` THEN
  ASM_SIMP_TAC[IN_ELIM_THM; LAMBDA_BETA; LAMBDA_BETA_PERM; LE_REFL;
               ARITH_RULE `i < n ==> i <= n /\ i + 1 <= n`;
               ARITH_RULE `1 <= n + 1`; DIMINDEX_GE_1; CART_EQ] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `1 <= inverse (p:num->num) i /\
                  !x. x <= inverse p i ==> x <= dimindex(:N)`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[PERMUTES_INVERSE; IN_NUMSEG; LE_TRANS; PERMUTES_IN_IMAGE];
      ASM_SIMP_TAC[LAMBDA_BETA] THEN ASM_SIMP_TAC[SUM_CLAUSES_LEFT; ARITH]] THEN
    SIMP_TAC[ARITH_RULE `2 <= n ==> ~(n = 1)`] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o BINDER_CONV)
                [GSYM REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC[SUM_PARTIAL_PRE] THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; SUM_0; COND_ID] THEN
    REWRITE_TAC[REAL_MUL_LID; ARITH; REAL_SUB_RZERO] THEN
    FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
     `1 <= p ==> p = 1 \/ 2 <= p`) o CONJUNCT1) THEN
    ASM_SIMP_TAC[ARITH] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP PERMUTES_INVERSES th]) THEN
    REWRITE_TAC[REAL_ADD_RID] THEN TRY REAL_ARITH_TAC THEN
    ASM_MESON_TAC[PERMUTES_INVERSE_EQ; PERMUTES_INVERSE];

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_SUB_LE] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i - 1`) THEN
    ASM_SIMP_TAC[SUB_ADD] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;

    SIMP_TAC[SUM_CLAUSES_LEFT; DIMINDEX_GE_1; ARITH;
             ARITH_RULE `2 <= n ==> ~(n = 1)`] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o BINDER_CONV)
                [GSYM REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC[SUM_PARTIAL_PRE] THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; SUM_0; COND_ID] THEN
    REWRITE_TAC[REAL_MUL_LID; ARITH; REAL_SUB_RZERO] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_ADD_RID] THEN
    ASM_REWRITE_TAC[REAL_ARITH `x + y - x:real = y`] THEN
    ASM_MESON_TAC[DIMINDEX_GE_1;
                  ARITH_RULE `1 <= n /\ ~(2 <= n) ==> n = 1`]]);;

let HAS_MEASURE_IMAGE_STD_SIMPLEX = prove
 (`!p. p permutes 1..dimindex(:N)
       ==> {x:real^N | &0 <= x$(p 1) /\ x$(p(dimindex(:N))) <= &1 /\
                       (!i. 1 <= i /\ i < dimindex(:N)
                            ==> x$(p i) <= x$(p(i + 1)))}
           has_measure
           (measure (convex hull
             (vec 0 INSERT {basis i:real^N | 1 <= i /\ i <= dimindex(:N)})))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CONGRUENT_IMAGE_STD_SIMPLEX] THEN
  ASM_SIMP_TAC[GSYM STD_SIMPLEX] THEN
  MATCH_MP_TAC HAS_MEASURE_LINEAR_IMAGE_SAME THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[linear; CART_EQ] THEN
    ASM_SIMP_TAC[LAMBDA_BETA; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                 GSYM SUM_ADD_NUMSEG; GSYM SUM_LMUL] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[];
    MATCH_MP_TAC MEASURABLE_CONVEX THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
    MATCH_MP_TAC BOUNDED_CONVEX_HULL THEN REWRITE_TAC[BOUNDED_INSERT] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    MATCH_MP_TAC FINITE_IMP_BOUNDED THEN MATCH_MP_TAC FINITE_IMAGE THEN
    REWRITE_TAC[GSYM numseg; FINITE_NUMSEG];
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
     `abs(det
       ((lambda i. ((lambda i j. if j <= i then &1 else &0):real^N^N)
                   $inverse p i)
        :real^N^N))` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[CART_EQ] THEN
      ASM_SIMP_TAC[matrix; LAMBDA_BETA; BASIS_COMPONENT; COND_COMPONENT;
                   LAMBDA_BETA_PERM; PERMUTES_INVERSE] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `sum (1..inverse (p:num->num) i)
                      (\k. if k = j then &1 else &0)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_EQ THEN
        ASM_SIMP_TAC[IN_NUMSEG; PERMUTES_IN_IMAGE; basis] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC LAMBDA_BETA THEN
        ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG; LE_TRANS;
                      PERMUTES_INVERSE];
        ASM_SIMP_TAC[SUM_DELTA; IN_NUMSEG]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[PERMUTES_INVERSE; DET_PERMUTE_ROWS; ETA_AX] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_SIGN; REAL_MUL_LID] THEN
    MATCH_MP_TAC(REAL_ARITH `x = &1 ==> abs x = &1`) THEN
    ASM_SIMP_TAC[DET_LOWERTRIANGULAR; GSYM NOT_LT; LAMBDA_BETA] THEN
    REWRITE_TAC[LT_REFL; PRODUCT_CONST_NUMSEG; REAL_POW_ONE]]);;

let HAS_MEASURE_STD_SIMPLEX = prove
 (`(convex hull (vec 0:real^N INSERT {basis i | 1 <= i /\ i <= dimindex(:N)}))
   has_measure inv(&(FACT(dimindex(:N))))`,
  let lemma = prove
   (`!f:num->real. (!i. 1 <= i /\ i < n ==> f i <= f(i + 1)) <=>
                   (!i j. 1 <= i /\ i <= j /\ j <= n ==> f i <= f j)`,
    GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [GEN_TAC THEN INDUCT_TAC THEN
      SIMP_TAC[LE; REAL_LE_REFL] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_REFL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(f:num->real) j` THEN
      ASM_SIMP_TAC[ARITH_RULE `SUC x <= y ==> x <= y`] THEN
      REWRITE_TAC[ADD1] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]) in
  MP_TAC(ISPECL
   [`\p. {x:real^N | &0 <= x$(p 1) /\ x$(p(dimindex(:N))) <= &1 /\
                     (!i. 1 <= i /\ i < dimindex(:N)
                          ==> x$(p i) <= x$(p(i + 1)))}`;
    `{p | p permutes 1..dimindex(:N)}`]
    HAS_MEASURE_NEGLIGIBLE_UNIONS_IMAGE) THEN
  ASM_SIMP_TAC[REWRITE_RULE[HAS_MEASURE_MEASURABLE_MEASURE]
                            HAS_MEASURE_IMAGE_STD_SIMPLEX; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[SUM_CONST; FINITE_PERMUTATIONS; FINITE_NUMSEG;
               CARD_PERMUTATIONS; CARD_NUMSEG_1] THEN
  ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`p:num->num`; `q:num->num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `?i. i IN 1..dimindex(:N) /\ ~(p i:num = q i)` MP_TAC THENL
     [ASM_MESON_TAC[permutes; FUN_EQ_THM]; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
    REWRITE_TAC[TAUT `a ==> ~(b /\ ~c) <=> a /\ b ==> c`] THEN
    REWRITE_TAC[IN_NUMSEG] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `{x:real^N | (basis(p(k:num)) - basis(q k)) dot x = &0}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_HYPERPLANE THEN REWRITE_TAC[VECTOR_SUB_EQ] THEN
      MATCH_MP_TAC BASIS_NE THEN ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; DOT_LSUB; VECTOR_SUB_EQ] THEN
    ASM_SIMP_TAC[DOT_BASIS; GSYM IN_NUMSEG; PERMUTES_IN_IMAGE] THEN
    SUBGOAL_THEN `?l. (q:num->num) l = p(k:num)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[permutes]; ALL_TAC] THEN
    SUBGOAL_THEN `1 <= l /\ l <= dimindex(:N)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG]; ALL_TAC] THEN
    SUBGOAL_THEN `k:num < l` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NOT_LE] THEN REWRITE_TAC[LE_LT] THEN
      ASM_MESON_TAC[PERMUTES_INJECTIVE; IN_NUMSEG];
      ALL_TAC] THEN
    SUBGOAL_THEN `?m. (p:num->num) m = q(k:num)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[permutes]; ALL_TAC] THEN
    SUBGOAL_THEN `1 <= m /\ m <= dimindex(:N)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG]; ALL_TAC] THEN
    SUBGOAL_THEN `k:num < m` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NOT_LE] THEN REWRITE_TAC[LE_LT] THEN
      ASM_MESON_TAC[PERMUTES_INJECTIVE; IN_NUMSEG];
      ALL_TAC] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[lemma] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `l:num`]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `m:num`]) THEN
    ASM_SIMP_TAC[LT_IMP_LE; IMP_IMP; REAL_LE_ANTISYM; REAL_SUB_0] THEN
    MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN
    ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG; DOT_BASIS];
    ALL_TAC] THEN
  REWRITE_TAC[HAS_MEASURE_MEASURABLE_MEASURE] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_CONVEX THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
    MATCH_MP_TAC BOUNDED_CONVEX_HULL THEN REWRITE_TAC[BOUNDED_INSERT] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    MATCH_MP_TAC FINITE_IMP_BOUNDED THEN MATCH_MP_TAC FINITE_IMAGE THEN
    REWRITE_TAC[GSYM numseg; FINITE_NUMSEG];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_FIELD `~(y = &0) ==> (x = inv y <=> y * x = &1)`;
               REAL_OF_NUM_EQ; FACT_NZ] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `measure(interval[vec 0:real^N,vec 1])` THEN CONJ_TAC THENL
   [AP_TERM_TAC; REWRITE_TAC[MEASURE_INTERVAL; CONTENT_UNIT]] THEN
  REWRITE_TAC[lemma] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_UNIONS; FORALL_IN_IMAGE; IMP_CONJ;
                RIGHT_FORALL_IMP_THM; IN_ELIM_THM] THEN
    SIMP_TAC[IMP_IMP; IN_INTERVAL; LAMBDA_BETA; VEC_COMPONENT] THEN
    X_GEN_TAC `p:num->num` THEN STRIP_TAC THEN X_GEN_TAC `x:real^N` THEN
    STRIP_TAC THEN X_GEN_TAC `i:num` THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `(x:real^N)$(p 1)`;
      EXISTS_TAC `(x:real^N)$(p(dimindex(:N)))`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP PERMUTES_SURJECTIVE) THEN
    ASM_MESON_TAC[LE_REFL; PERMUTES_IN_IMAGE; IN_NUMSEG];
    ALL_TAC] THEN
  REWRITE_TAC[SET_RULE `s SUBSET UNIONS(IMAGE f t) <=>
                        !x. x IN s ==> ?y. y IN t /\ x IN f y`] THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTERVAL; IN_ELIM_THM] THEN
  SIMP_TAC[VEC_COMPONENT] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `\i j. ~((x:real^N)$j <= x$i)` TOPOLOGICAL_SORT) THEN
  REWRITE_TAC[REAL_NOT_LE; REAL_NOT_LT] THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`dimindex(:N)`; `1..dimindex(:N)`]) THEN
  REWRITE_TAC[HAS_SIZE_NUMSEG_1; EXTENSION; IN_IMAGE; IN_NUMSEG] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->num` (CONJUNCTS_THEN2
   (ASSUME_TAC o GSYM) ASSUME_TAC)) THEN
  EXISTS_TAC `\i. if i IN 1..dimindex(:N) then f(i) else i` THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ARITH_RULE
    `1 <= i /\ i <= j /\ j <= n <=>
     1 <= i /\ 1 <= j /\ i <= n /\ j <= n /\ i <= j`] THEN
  ASM_SIMP_TAC[IN_NUMSEG; LE_REFL; DIMINDEX_GE_1] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_MESON_TAC[LE_REFL; DIMINDEX_GE_1; LE_LT; REAL_LE_LT]] THEN
  SIMP_TAC[PERMUTES_FINITE_SURJECTIVE; FINITE_NUMSEG] THEN
  SIMP_TAC[IN_NUMSEG] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Hence the measure of a general simplex.                                   *)
(* ------------------------------------------------------------------------- *)

let HAS_MEASURE_SIMPLEX_0 = prove
 (`!l:(real^N)list.
        LENGTH l = dimindex(:N)
        ==> (convex hull (vec 0 INSERT set_of_list l)) has_measure
            abs(det(vector l)) / &(FACT(dimindex(:N)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `vec 0 INSERT (set_of_list l) =
        IMAGE (\x:real^N. transp(vector l:real^N^N) ** x)
              (vec 0 INSERT {basis i:real^N | 1 <= i /\ i <= dimindex(:N)})`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC[IMAGE_CLAUSES; GSYM IMAGE_o; o_DEF] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO] THEN AP_TERM_TAC THEN
    SIMP_TAC[matrix_vector_mul; vector; transp; LAMBDA_BETA; basis] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    SIMP_TAC[REAL_MUL_RZERO; SUM_DELTA] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_NUMSEG] THEN
    ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> ~(b /\ c ==> ~a)`] THEN
    X_GEN_TAC `y:real^N` THEN SIMP_TAC[LAMBDA_BETA; REAL_MUL_RID] THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN
    REWRITE_TAC[NOT_IMP; REAL_MUL_RID; GSYM CART_EQ] THEN
    ASM_REWRITE_TAC[IN_SET_OF_LIST; MEM_EXISTS_EL] THEN
    EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THENL
     [EXISTS_TAC `SUC i`; EXISTS_TAC `i - 1`] THEN
    ASM_REWRITE_TAC[SUC_SUB1] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[CONVEX_HULL_LINEAR_IMAGE; MATRIX_VECTOR_MUL_LINEAR] THEN
  SUBGOAL_THEN
   `det(vector l:real^N^N) = det(matrix(\x:real^N. transp(vector l) ** x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[MATRIX_OF_MATRIX_VECTOR_MUL; DET_TRANSP]; ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN
  ASM_SIMP_TAC[GSYM(REWRITE_RULE[HAS_MEASURE_MEASURABLE_MEASURE]
                 HAS_MEASURE_STD_SIMPLEX)] THEN
  MATCH_MP_TAC HAS_MEASURE_LINEAR_IMAGE THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
  MATCH_MP_TAC MEASURABLE_CONVEX THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
  MATCH_MP_TAC BOUNDED_CONVEX_HULL THEN REWRITE_TAC[BOUNDED_INSERT] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  MATCH_MP_TAC FINITE_IMP_BOUNDED THEN MATCH_MP_TAC FINITE_IMAGE THEN
  REWRITE_TAC[GSYM numseg; FINITE_NUMSEG]);;

let HAS_MEASURE_SIMPLEX = prove
 (`!a l:(real^N)list.
        LENGTH l = dimindex(:N)
        ==> (convex hull (set_of_list(CONS a l))) has_measure
            abs(det(vector(MAP (\x. x - a) l))) / &(FACT(dimindex(:N)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `MAP (\x:real^N. x - a) l` HAS_MEASURE_SIMPLEX_0) THEN
  ASM_REWRITE_TAC[LENGTH_MAP; set_of_list] THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^N` o MATCH_MP HAS_MEASURE_TRANSLATION) THEN
  REWRITE_TAC[GSYM CONVEX_HULL_TRANSLATION] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[IMAGE_CLAUSES; VECTOR_ADD_RID; SET_OF_LIST_MAP] THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; VECTOR_ARITH `a + x - a:real^N = x`;
              SET_RULE `IMAGE (\x. x) s = s`]);;

let MEASURABLE_CONVEX_HULL = prove
 (`!s. bounded s ==> measurable(convex hull s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_CONVEX THEN
  ASM_SIMP_TAC[CONVEX_CONVEX_HULL; BOUNDED_CONVEX_HULL]);;

let MEASURABLE_SIMPLEX = prove
 (`!l. measurable(convex hull (set_of_list l))`,
  GEN_TAC THEN MATCH_MP_TAC MEASURABLE_CONVEX_HULL THEN
  MATCH_MP_TAC FINITE_IMP_BOUNDED THEN REWRITE_TAC[FINITE_SET_OF_LIST]);;

let MEASURE_SIMPLEX = prove
 (`!a l:(real^N)list.
        LENGTH l = dimindex(:N)
        ==> measure(convex hull (set_of_list(CONS a l))) =
            abs(det(vector(MAP (\x. x - a) l))) / &(FACT(dimindex(:N)))`,
  MESON_TAC[HAS_MEASURE_SIMPLEX; HAS_MEASURE_MEASURABLE_MEASURE]);;

(* ------------------------------------------------------------------------- *)
(* Area of a triangle.                                                       *)
(* ------------------------------------------------------------------------- *)

let HAS_MEASURE_TRIANGLE = prove
 (`!a b c:real^2.
        convex hull {a,b,c} has_measure
        abs((b$1 - a$1) * (c$2 - a$2) - (b$2 - a$2) * (c$1 - a$1)) / &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^2`; `[b;c]:(real^2)list`] HAS_MEASURE_SIMPLEX) THEN
  REWRITE_TAC[LENGTH; DIMINDEX_2; ARITH; set_of_list; MAP] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[DET_2; VECTOR_2] THEN
  SIMP_TAC[VECTOR_SUB_COMPONENT; DIMINDEX_2; ARITH]);;

let MEASURABLE_TRIANGLE = prove
 (`!a b c:real^N. measurable(convex hull {a,b,c})`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC MEASURABLE_CONVEX THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
  MATCH_MP_TAC BOUNDED_CONVEX_HULL THEN MATCH_MP_TAC FINITE_IMP_BOUNDED THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_RULES]);;

let MEASURE_TRIANGLE = prove
 (`!a b c:real^2.
        measure(convex hull {a,b,c}) =
        abs((b$1 - a$1) * (c$2 - a$2) - (b$2 - a$2) * (c$1 - a$1)) / &2`,
  REWRITE_TAC[REWRITE_RULE[HAS_MEASURE_MEASURABLE_MEASURE]
               HAS_MEASURE_TRIANGLE]);;

(* ------------------------------------------------------------------------- *)
(* Volume of a tetrahedron.                                                  *)
(* ------------------------------------------------------------------------- *)

let HAS_MEASURE_TETRAHEDRON = prove
 (`!a b c d:real^3.
        convex hull {a,b,c,d} has_measure
        abs((b$1 - a$1) * (c$2 - a$2) * (d$3 - a$3) +
            (b$2 - a$2) * (c$3 - a$3) * (d$1 - a$1) +
            (b$3 - a$3) * (c$1 - a$1) * (d$2 - a$2) -
            (b$1 - a$1) * (c$3 - a$3) * (d$2 - a$2) -
            (b$2 - a$2) * (c$1 - a$1) * (d$3 - a$3) -
            (b$3 - a$3) * (c$2 - a$2) * (d$1 - a$1)) /
           &6`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^3`; `[b;c;d]:(real^3)list`] HAS_MEASURE_SIMPLEX) THEN
  REWRITE_TAC[LENGTH; DIMINDEX_3; ARITH; set_of_list; MAP] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[DET_3; VECTOR_3] THEN
  SIMP_TAC[VECTOR_SUB_COMPONENT; DIMINDEX_3; ARITH]);;

let MEASURABLE_TETRAHEDRON = prove
 (`!a b c d:real^N. measurable(convex hull {a,b,c,d})`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC MEASURABLE_CONVEX THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
  MATCH_MP_TAC BOUNDED_CONVEX_HULL THEN MATCH_MP_TAC FINITE_IMP_BOUNDED THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_RULES]);;

let MEASURE_TETRAHEDRON = prove
 (`!a b c d:real^3.
        measure(convex hull {a,b,c,d}) =
        abs((b$1 - a$1) * (c$2 - a$2) * (d$3 - a$3) +
            (b$2 - a$2) * (c$3 - a$3) * (d$1 - a$1) +
            (b$3 - a$3) * (c$1 - a$1) * (d$2 - a$2) -
            (b$1 - a$1) * (c$3 - a$3) * (d$2 - a$2) -
            (b$2 - a$2) * (c$1 - a$1) * (d$3 - a$3) -
            (b$3 - a$3) * (c$2 - a$2) * (d$1 - a$1)) / &6`,
  REWRITE_TAC[REWRITE_RULE[HAS_MEASURE_MEASURABLE_MEASURE]
               HAS_MEASURE_TETRAHEDRON]);;

(* ------------------------------------------------------------------------- *)
(* Steinhaus's theorem. (Stromberg's proof as given on Wikipedia.)           *)
(* ------------------------------------------------------------------------- *)

let STEINHAUS = prove
 (`!s:real^N->bool.
        measurable s /\ &0 < measure s
        ==> ?d. &0 < d /\ ball(vec 0,d) SUBSET {x - y | x IN s /\ y IN s}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `measure(s:real^N->bool) / &3`]
    MEASURABLE_INNER_COMPACT) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `measure(s:real^N->bool) / &3`]
    MEASURABLE_OUTER_OPEN) THEN
  ASM_REWRITE_TAC[REAL_ARITH `&0 < x / &3 <=> &0 < x`] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `(:real^N) DIFF u`]
    SEPARATE_COMPACT_CLOSED) THEN
  ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_BALL_0; IN_ELIM_THM] THEN
  X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~((IMAGE (\x:real^N. v + x) k) INTER k = {})` MP_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`IMAGE (\x:real^N. v + x) k`; `k:real^N->bool`]
        MEASURE_UNION) THEN
    ASM_REWRITE_TAC[MEASURABLE_TRANSLATION_EQ; MEASURE_EMPTY] THEN
    REWRITE_TAC[MEASURE_TRANSLATION; REAL_SUB_RZERO] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!s:real^N->bool u:real^N->bool.
        measure u < measure s + measure s / &3 /\
        measure s < measure k + measure s / &3 /\
        measure x <= measure u
        ==> ~(measure x = measure k + measure k)`) THEN
    MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `u:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MEASURE_SUBSET THEN
    ASM_SIMP_TAC[MEASURABLE_TRANSLATION_EQ; MEASURABLE_UNION] THEN
    ASM_REWRITE_TAC[UNION_SUBSET] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `v + x:real^N`]) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; NORM_ARITH
     `d <= dist(x:real^N,v + x) <=> ~(norm v < d)`];
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    REWRITE_TAC[VECTOR_ARITH `v:real^N = x - y <=> x = v + y`] THEN
    ASM SET_TAC[]]);;
