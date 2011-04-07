(* ========================================================================= *)
(* Complex path integrals and Cauchy's theorem.                              *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(* (c) Copyright, Gianni Ciolli, Graziano Gentili, Marco Maggesi 2008-2009.  *)
(*              (c) Copyright, Valentina Bruno 2010                          *)
(* ========================================================================= *)

needs "Library/binomial.ml";;
needs "Library/iter.ml";;
needs "Multivariate/transcendentals.ml";;

prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* A couple of extra tactics used in some proofs below.                      *)
(* ------------------------------------------------------------------------- *)

let ASSERT_TAC tm =
  SUBGOAL_THEN tm STRIP_ASSUME_TAC;;

let EQ_TRANS_TAC tm =
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC tm THEN CONJ_TAC;;

(* ------------------------------------------------------------------------- *)
(* Piecewise differentiability on a 1-D interval.                            *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("piecewise_differentiable_on",(12,"right"));;

let piecewise_differentiable_on = new_definition
 `f piecewise_differentiable_on i <=>
        f continuous_on i /\
        (?s. FINITE s /\ !x. x IN (i DIFF s) ==> f differentiable at x)`;;

let PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON = prove
 (`!f s. f piecewise_differentiable_on s ==> f continuous_on s`,
  SIMP_TAC[piecewise_differentiable_on]);;

let PIECEWISE_DIFFERENTIABLE_ON_SUBSET = prove
 (`!f s t.
        f piecewise_differentiable_on s /\ t SUBSET s
        ==> f piecewise_differentiable_on t`,
  REWRITE_TAC[piecewise_differentiable_on] THEN
  MESON_TAC[SUBSET; IN_DIFF; CONTINUOUS_ON_SUBSET]);;

let DIFFERENTIABLE_ON_IMP_PIECEWISE_DIFFERENTIABLE = prove
 (`!f:real^1->real^N a b.
        f differentiable_on interval[a,b]
        ==> f piecewise_differentiable_on interval[a,b]`,
  SIMP_TAC[piecewise_differentiable_on;
           DIFFERENTIABLE_IMP_CONTINUOUS_ON] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `{a,b}:real^1->bool` THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FINITE_RULES] THEN
  REWRITE_TAC[GSYM OPEN_CLOSED_INTERVAL_1] THEN
  SIMP_TAC[GSYM DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT; OPEN_INTERVAL] THEN
  MATCH_MP_TAC DIFFERENTIABLE_ON_SUBSET THEN
  EXISTS_TAC `interval[a:real^1,b]` THEN
  ASM_REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED]);;

let DIFFERENTIABLE_IMP_PIECEWISE_DIFFERENTIABLE = prove
 (`!f s. (!x. x IN s ==> f differentiable (at x))
         ==> f piecewise_differentiable_on s`,
  SIMP_TAC[piecewise_differentiable_on; DIFFERENTIABLE_IMP_CONTINUOUS_AT;
           CONTINUOUS_AT_IMP_CONTINUOUS_ON; IN_DIFF] THEN
  MESON_TAC[FINITE_RULES]);;

let PIECEWISE_DIFFERENTIABLE_COMPOSE = prove
 (`!f:real^M->real^N g:real^N->real^P s.
        f piecewise_differentiable_on s /\
        g piecewise_differentiable_on (IMAGE f s) /\
        (!b. FINITE {x | x IN s /\ f(x) = b})
        ==> (g o f) piecewise_differentiable_on s`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[piecewise_differentiable_on; CONTINUOUS_ON_COMPOSE] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `ks:real^M->bool`
                                STRIP_ASSUME_TAC))
   (CONJUNCTS_THEN2
     (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `kt:real^N->bool`
                                  STRIP_ASSUME_TAC))
     ASSUME_TAC)) THEN
  EXISTS_TAC
    `ks UNION
     UNIONS(IMAGE (\b. {x | x IN s /\ (f:real^M->real^N) x = b}) kt)` THEN
  ASM_SIMP_TAC[FINITE_UNION; FINITE_UNIONS; FINITE_IMAGE] THEN
  REWRITE_TAC[UNIONS_IMAGE; FORALL_IN_IMAGE; IN_DIFF; IN_UNION] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;

let PIECEWISE_DIFFERENTIABLE_AFFINE = prove
 (`!f:real^M->real^N s m c.
        f piecewise_differentiable_on (IMAGE (\x. m % x + c) s)
        ==> (f o (\x. m % x + c)) piecewise_differentiable_on s`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `m = &0` THENL
   [ASM_REWRITE_TAC[o_DEF; VECTOR_MUL_LZERO] THEN
    MATCH_MP_TAC DIFFERENTIABLE_IMP_PIECEWISE_DIFFERENTIABLE THEN
    SIMP_TAC[DIFFERENTIABLE_CONST];
    MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_COMPOSE THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_IMP_PIECEWISE_DIFFERENTIABLE THEN
      SIMP_TAC[DIFFERENTIABLE_ADD; DIFFERENTIABLE_CMUL; DIFFERENTIABLE_CONST;
               DIFFERENTIABLE_ID];
      X_GEN_TAC `b:real^M` THEN ASM_SIMP_TAC[VECTOR_AFFINITY_EQ] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{inv m % b + --(inv m % c):real^M}` THEN
      SIMP_TAC[FINITE_RULES] THEN SET_TAC[]]]);;

let PIECEWISE_DIFFERENTIABLE_CASES = prove
 (`!f g:real^1->real^N a b c.
        drop a <= drop c /\ drop c <= drop b /\ f c = g c /\
        f piecewise_differentiable_on interval[a,c] /\
        g piecewise_differentiable_on interval[c,b]
        ==> (\x. if drop x <= drop c then f(x) else g(x))
            piecewise_differentiable_on interval[a,b]`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 3 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[piecewise_differentiable_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `s:real^1->bool`
                                STRIP_ASSUME_TAC))
   (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:real^1->bool`
                                STRIP_ASSUME_TAC))) THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `interval[a:real^1,b] = interval[a,c] UNION interval[c,b]`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; IN_INTERVAL_1] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES THEN
    ASM_REWRITE_TAC[CLOSED_INTERVAL; IN_INTERVAL_1] THEN
    ASM_MESON_TAC[REAL_LE_ANTISYM; DROP_EQ];
    ALL_TAC] THEN
  EXISTS_TAC `(c:real^1) INSERT s UNION t` THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FINITE_UNION] THEN
  REWRITE_TAC[DE_MORGAN_THM; IN_DIFF; IN_INTERVAL_1; IN_INSERT; IN_UNION] THEN
  X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN
  DISJ_CASES_TAC(REAL_ARITH `drop x <= drop c \/ drop c <= drop x`) THEN
  MATCH_MP_TAC DIFFERENTIABLE_TRANSFORM_AT THENL
   [EXISTS_TAC `f:real^1->real^N`; EXISTS_TAC `g:real^1->real^N`] THEN
  EXISTS_TAC `dist(x:real^1,c)` THEN ASM_REWRITE_TAC[GSYM DIST_NZ] THEN
  (CONJ_TAC THENL
    [GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[dist; NORM_REAL; GSYM drop; DROP_SUB] THEN
     ASM_REAL_ARITH_TAC;
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC[IN_INTERVAL_1; IN_DIFF]]));;

let PIECEWISE_DIFFERENTIABLE_NEG = prove
 (`!f s. f piecewise_differentiable_on s
         ==> (\x. --(f x)) piecewise_differentiable_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[piecewise_differentiable_on] THEN
  MATCH_MP_TAC MONO_AND THEN SIMP_TAC[CONTINUOUS_ON_NEG] THEN
  MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[DIFFERENTIABLE_NEG]);;

(* ------------------------------------------------------------------------- *)
(* Valid paths, and their start and finish.                                  *)
(* ------------------------------------------------------------------------- *)

let valid_path = new_definition
 `valid_path (f:real^1->complex) <=>
     f piecewise_differentiable_on interval[vec 0,vec 1]`;;

let closed_path = new_definition
 `closed_path g <=> pathstart g = pathfinish g`;;

(* ------------------------------------------------------------------------- *)
(* In particular, all results for paths apply.                               *)
(* ------------------------------------------------------------------------- *)

let VALID_PATH_IMP_PATH = prove
 (`!g. valid_path g ==> path g`,
  SIMP_TAC[valid_path; path; piecewise_differentiable_on]);;

let CONNECTED_VALID_PATH_IMAGE = prove
 (`!g. valid_path g ==> connected(path_image g)`,
  MESON_TAC[CONNECTED_PATH_IMAGE; VALID_PATH_IMP_PATH]);;

let COMPACT_VALID_PATH_IMAGE = prove
 (`!g. valid_path g ==> compact(path_image g)`,
  MESON_TAC[COMPACT_PATH_IMAGE; VALID_PATH_IMP_PATH]);;

let BOUNDED_VALID_PATH_IMAGE = prove
 (`!g. valid_path g ==> bounded(path_image g)`,
  MESON_TAC[BOUNDED_PATH_IMAGE; VALID_PATH_IMP_PATH]);;

let CLOSED_VALID_PATH_IMAGE = prove
 (`!g. valid_path g ==> closed(path_image g)`,
  MESON_TAC[CLOSED_PATH_IMAGE; VALID_PATH_IMP_PATH]);;

(* ------------------------------------------------------------------------- *)
(* Integrals along a path (= piecewise differentiable function on [0,1]).    *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("has_path_integral",(12,"right"));;
parse_as_infix("path_integrable_on",(12,"right"));;

let has_path_integral = define
  `(f has_path_integral i) (g) <=>
       ((\x. f(g(x)) * vector_derivative g (at x within interval[vec 0,vec 1]))
        has_integral i)
       (interval[vec 0,vec 1])`;;

let path_integral = new_definition
 `path_integral g f = @i. (f has_path_integral i) (g)`;;

let path_integrable_on = new_definition
 `f path_integrable_on g <=> ?i. (f has_path_integral i) g`;;

let PATH_INTEGRAL_UNIQUE = prove
 (`!f g i. (f has_path_integral i) (g) ==> path_integral(g) f = i`,
  REWRITE_TAC[path_integral; has_path_integral; GSYM integral] THEN
  MESON_TAC[INTEGRAL_UNIQUE]);;

let HAS_PATH_INTEGRAL_INTEGRAL = prove
 (`!f i. f path_integrable_on i
         ==> (f has_path_integral (path_integral i f)) i`,
  REWRITE_TAC[path_integral; path_integrable_on] THEN
  MESON_TAC[PATH_INTEGRAL_UNIQUE]);;

let HAS_PATH_INTEGRAL_UNIQUE = prove
 (`!f i j g. (f has_path_integral i) g /\
             (f has_path_integral j) g
             ==> i = j`,
  REWRITE_TAC[has_path_integral] THEN MESON_TAC[HAS_INTEGRAL_UNIQUE]);;

let HAS_PATH_INTEGRAL_INTEGRABLE = prove
 (`!f g i. (f has_path_integral i) g ==> f path_integrable_on g`,
  REWRITE_TAC[path_integrable_on] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Show that we can forget about the localized derivative.                   *)
(* ------------------------------------------------------------------------- *)

let VECTOR_DERIVATIVE_WITHIN_INTERIOR = prove
 (`!a b x.
        x IN interior(interval[a,b])
        ==> vector_derivative f (at x within interval[a,b]) =
            vector_derivative f (at x)`,
  SIMP_TAC[vector_derivative; has_vector_derivative; has_derivative;
           LIM_WITHIN_INTERIOR; NETLIMIT_WITHIN_INTERIOR; NETLIMIT_AT]);;

let HAS_INTEGRAL_LOCALIZED_VECTOR_DERIVATIVE = prove
 (`((\x. f' (g x) * vector_derivative g (at x within interval [a,b]))
    has_integral i) (interval [a,b]) <=>
    ((\x. f' (g x) * vector_derivative g (at x))
     has_integral i) (interval [a,b])`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_SPIKE_EQ THEN
  EXISTS_TAC `{a:real^1,b}` THEN
  REWRITE_TAC[NEGLIGIBLE_INSERT; NEGLIGIBLE_EMPTY] THEN
  SUBGOAL_THEN `interval[a:real^1,b] DIFF {a,b} = interior(interval[a,b])`
   (fun th -> SIMP_TAC[th; VECTOR_DERIVATIVE_WITHIN_INTERIOR]) THEN
  REWRITE_TAC[INTERIOR_CLOSED_INTERVAL] THEN
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_INTERVAL; IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[DIMINDEX_1; FORALL_1; GSYM drop; GSYM DROP_EQ] THEN
  REAL_ARITH_TAC);;

let HAS_PATH_INTEGRAL = prove
 (`(f has_path_integral i) g <=>
        ((\x. f (g x) * vector_derivative g (at x)) has_integral i)
        (interval[vec 0,vec 1])`,
  SIMP_TAC[HAS_INTEGRAL_LOCALIZED_VECTOR_DERIVATIVE; has_path_integral]);;

let PATH_INTEGRABLE_ON = prove
 (`f path_integrable_on g <=>
        (\t. f(g t) * vector_derivative g (at t))
            integrable_on interval[vec 0,vec 1]`,
  REWRITE_TAC[path_integrable_on; HAS_PATH_INTEGRAL; GSYM integrable_on]);;

(* ------------------------------------------------------------------------- *)
(* Reversing a path.                                                         *)
(* ------------------------------------------------------------------------- *)

let VALID_PATH_REVERSEPATH = prove
 (`!g. valid_path(reversepath g) <=> valid_path g`,
  SUBGOAL_THEN `!g. valid_path g ==> valid_path(reversepath g)`
   (fun th -> MESON_TAC[th; REVERSEPATH_REVERSEPATH]) THEN GEN_TAC THEN
  SIMP_TAC[valid_path; piecewise_differentiable_on; GSYM path;
           PATH_REVERSEPATH] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) MP_TAC) THEN
  REWRITE_TAC[IN_DIFF] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^1->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (\x:real^1. vec 1 - x) s` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; reversepath] THEN
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN
  SIMP_TAC[DIFFERENTIABLE_SUB; DIFFERENTIABLE_CONST; DIFFERENTIABLE_ID] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `(x:real^1) IN interval[vec 0,vec 1]` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_SUB; DROP_VEC] THEN REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o ISPEC `\x:real^1. vec 1 - x` o
     MATCH_MP FUN_IN_IMAGE) THEN
    UNDISCH_TAC `~((x:real^1) IN IMAGE (\x. vec 1 - x) s)` THEN
    REWRITE_TAC[VECTOR_ARITH `vec 1 - (vec 1 - x):real^1 = x`]]);;

let HAS_PATH_INTEGRAL_REVERSEPATH = prove
 (`!f g i. valid_path g /\ (f has_path_integral i) g
           ==> (f has_path_integral (--i)) (reversepath g)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_PATH_INTEGRAL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(MP_TAC o C CONJ (REAL_ARITH `~(-- &1 = &0)`)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_AFFINITY) THEN
  DISCH_THEN(MP_TAC o SPEC `vec 1:real^1`) THEN
  REWRITE_TAC[IMAGE_AFFINITY_INTERVAL; INTERVAL_EQ_EMPTY_1; DROP_VEC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[VECTOR_ARITH `x + --x:real^1 = vec 0`] THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID; VECTOR_MUL_LNEG] THEN
  REWRITE_TAC[VECTOR_MUL_LID; VECTOR_NEG_NEG; REAL_POW_ONE] THEN
  REWRITE_TAC[reversepath; VECTOR_ARITH `-- x + a:real^N = a - x`] THEN
  REWRITE_TAC[REAL_INV_1; VECTOR_MUL_LID] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_NEG) THEN
  REWRITE_TAC[VECTOR_SUB_RZERO] THEN
  MATCH_MP_TAC(REWRITE_RULE [TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
                HAS_INTEGRAL_SPIKE_FINITE) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [valid_path]) THEN
  REWRITE_TAC[piecewise_differentiable_on] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^1->bool` STRIP_ASSUME_TAC o CONJUNCT2) THEN
  EXISTS_TAC `IMAGE (\x:real^1. vec 1 - x) s` THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[GSYM COMPLEX_MUL_RNEG] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM o_DEF] THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH `--x = --(&1) % x`] THEN
  REWRITE_TAC[GSYM DROP_VEC; GSYM DROP_NEG] THEN
  MATCH_MP_TAC VECTOR_DIFF_CHAIN_AT THEN REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH `--x:real^N = vec 0 - x`] THEN
  SIMP_TAC[HAS_VECTOR_DERIVATIVE_SUB; HAS_VECTOR_DERIVATIVE_CONST;
           HAS_VECTOR_DERIVATIVE_ID] THEN
  REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_DIFF]) THEN
  REWRITE_TAC[IN_DIFF] THEN MATCH_MP_TAC MONO_AND THEN
  REWRITE_TAC[CONTRAPOS_THM; IN_DIFF; IN_INTERVAL_1; DROP_SUB; DROP_VEC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN REWRITE_TAC[IN_IMAGE] THEN
  MESON_TAC[VECTOR_ARITH `vec 1 - (vec 1 - x):real^1 = x`]);;

(* ------------------------------------------------------------------------- *)
(* Joining two paths together.                                               *)
(* ------------------------------------------------------------------------- *)

let VALID_PATH_JOIN_EQ = prove
 (`!g1 g2.
        pathfinish g1 = pathstart g2
        ==> (valid_path(g1 ++ g2) <=> valid_path g1 /\ valid_path g2)`,
  REWRITE_TAC[valid_path; piecewise_differentiable_on; GSYM path] THEN
  ASM_SIMP_TAC[PATH_JOIN] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `path(g1:real^1->complex)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `path(g2:real^1->complex)` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `s:real^1->bool` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THENL
     [EXISTS_TAC `(vec 0) INSERT (vec 1) INSERT
                  {x:real^1 | ((&1 / &2) % x) IN s}` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[FINITE_INSERT] THEN MATCH_MP_TAC FINITE_IMAGE_INJ THEN
        ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
        ALL_TAC] THEN
      X_GEN_TAC `x:real^1` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(&1 / &2) % x:real^1`) THEN
      REWRITE_TAC[IN_DIFF; IN_ELIM_THM; IN_INTERVAL_1; DROP_CMUL; DROP_VEC;
                  IN_INSERT; DE_MORGAN_THM; GSYM DROP_EQ; NOT_EXISTS_THM] THEN
      DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN
       `(g1:real^1->complex) = (\x. g1 (&2 % x)) o (\x. &1 / &2 % x)`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
        VECTOR_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN
      SIMP_TAC[DIFFERENTIABLE_CMUL; DIFFERENTIABLE_ID] THEN
      MATCH_MP_TAC DIFFERENTIABLE_TRANSFORM_AT THEN
      EXISTS_TAC `(g1 ++ g2):real^1->complex` THEN
      EXISTS_TAC `dist(&1 / &2 % x:real^1,lift(&1 / &2))` THEN
      ASM_REWRITE_TAC[dist; NORM_REAL; GSYM drop; DROP_SUB; DROP_CMUL;
                      LIFT_DROP] THEN
      REWRITE_TAC[joinpaths] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;

      EXISTS_TAC `(vec 0) INSERT (vec 1) INSERT
                  {x:real^1 | ((&1 / &2) % (x + vec 1)) IN s}` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[FINITE_INSERT] THEN MATCH_MP_TAC FINITE_IMAGE_INJ THEN
        ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
        ALL_TAC] THEN
      X_GEN_TAC `x:real^1` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(&1 / &2) % (x + vec 1):real^1`) THEN
      REWRITE_TAC[IN_DIFF; IN_ELIM_THM; IN_INTERVAL_1; DROP_CMUL; DROP_VEC;
       DROP_ADD; IN_INSERT; DE_MORGAN_THM; GSYM DROP_EQ; NOT_EXISTS_THM] THEN
      DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN
       `(g2:real^1->complex) =
        (\x. g2 (&2 % x - vec 1)) o (\x. &1 / &2 % (x + vec 1))`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
        VECTOR_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN
      SIMP_TAC[DIFFERENTIABLE_CMUL; DIFFERENTIABLE_ADD;
               DIFFERENTIABLE_CONST; DIFFERENTIABLE_ID] THEN
      MATCH_MP_TAC DIFFERENTIABLE_TRANSFORM_AT THEN
      EXISTS_TAC `(g1 ++ g2):real^1->complex` THEN
      EXISTS_TAC `dist(&1 / &2 % (x + vec 1):real^1,lift(&1 / &2))` THEN
      ASM_REWRITE_TAC[dist; NORM_REAL; GSYM drop; DROP_SUB; DROP_CMUL;
                      DROP_ADD; DROP_VEC; LIFT_DROP] THEN
      REWRITE_TAC[joinpaths] THEN
      REPEAT STRIP_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `s1:real^1->bool` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `s2:real^1->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `(&1 / &2 % vec 1:real^1) INSERT
              {x:real^1 | (&2 % x) IN s1} UNION
              {x:real^1 | (&2 % x - vec 1) IN s2}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FINITE_INSERT; FINITE_UNION] THEN
    CONJ_TAC THEN MATCH_MP_TAC FINITE_IMAGE_INJ THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `x:real^1` THEN
  REWRITE_TAC[IN_INTERVAL_1; IN_DIFF; DROP_VEC; IN_INSERT; IN_ELIM_THM;
              DE_MORGAN_THM; IN_UNION; GSYM DROP_EQ; DROP_CMUL] THEN
  STRIP_TAC THEN
  REWRITE_TAC[joinpaths] THEN ASM_CASES_TAC `drop x <= &1 / &2` THENL
   [MATCH_MP_TAC DIFFERENTIABLE_TRANSFORM_AT THEN
    EXISTS_TAC `\x. (g1:real^1->complex)(&2 % x)` THEN
    EXISTS_TAC `abs(&1 / &2 - drop x)` THEN
    REWRITE_TAC[dist; NORM_REAL; GSYM drop; DROP_SUB; DROP_CMUL;
                    DROP_ADD; DROP_VEC; LIFT_DROP] THEN
    CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC];
    MATCH_MP_TAC DIFFERENTIABLE_TRANSFORM_AT THEN
    EXISTS_TAC `\x. (g2:real^1->complex)(&2 % x - vec 1)` THEN
    EXISTS_TAC `abs(&1 / &2 - drop x)` THEN
    REWRITE_TAC[dist; NORM_REAL; GSYM drop; DROP_SUB; DROP_CMUL;
                    DROP_ADD; DROP_VEC; LIFT_DROP] THEN
    CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC]] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN
  SIMP_TAC[DIFFERENTIABLE_CMUL; DIFFERENTIABLE_SUB; DIFFERENTIABLE_CONST;
           DIFFERENTIABLE_ID] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_SUB; IN_DIFF; DROP_VEC; DROP_CMUL] THEN
  ASM_REAL_ARITH_TAC);;

let VALID_PATH_JOIN = prove
 (`!g1 g2.
        valid_path g1 /\ valid_path g2 /\ pathfinish g1 = pathstart g2
        ==> valid_path(g1 ++ g2)`,
  MESON_TAC[VALID_PATH_JOIN_EQ]);;

let HAS_PATH_INTEGRAL_JOIN = prove
 (`!f g1 g2 i1 i2.
        (f has_path_integral i1) g1 /\
        (f has_path_integral i2) g2 /\
        valid_path g1 /\ valid_path g2
        ==> (f has_path_integral (i1 + i2)) (g1 ++ g2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_PATH_INTEGRAL; CONJ_ASSOC] THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN
   (MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_AFFINITY))) THEN
  DISCH_THEN(ASSUME_TAC o SPECL [`&2`; `--(vec 1):real^1`]) THEN
  DISCH_THEN(MP_TAC o SPECL [`&2`; `vec 0:real^1`]) THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[DIMINDEX_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[IMAGE_AFFINITY_INTERVAL] THEN
  REWRITE_TAC[INTERVAL_EQ_EMPTY_1; DROP_VEC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[VECTOR_MUL_RNEG; VECTOR_NEG_NEG; VECTOR_MUL_RZERO;
              VECTOR_ADD_LID; VECTOR_NEG_0; VECTOR_ADD_RID;
              VECTOR_ARITH `&1 / &2 % x + &1 / &2 % x = x:real^N`] THEN
  REWRITE_TAC[DROP_CMUL; DROP_ADD; DROP_NEG; DROP_VEC; VECTOR_MUL_ASSOC] THEN
  REWRITE_TAC[VECTOR_ARITH `x % (a + b) + y % b = x % a + (x + y) % b`;
              VECTOR_ARITH `x % a + y % (a + b) = (x + y) % a + y % b`] THEN
  REWRITE_TAC[REAL_ARITH `(&1 - (&2 * x + --(&1))) * inv(&2) = &1 - x`;
              REAL_ARITH `&1 - x + &2 * x + --(&1) = x`;
              REAL_ARITH `&1 - &2 * x + (&2 * x) * inv(&2) = &1 - x`;
              REAL_ARITH `(&2 * x) * inv(&2) = x`] THEN
  REWRITE_TAC[VECTOR_ARITH `b - inv(&2) % (a + b) = inv(&2) % (b - a)`;
              VECTOR_ARITH `inv(&2) % (a + b) - a = inv(&2) % (b - a)`] THEN
  REPEAT(DISCH_THEN(MP_TAC o SPEC `&2` o MATCH_MP HAS_INTEGRAL_CMUL) THEN
         REWRITE_TAC[COMPLEX_CMUL; SIMPLE_COMPLEX_ARITH
          `Cx(&2) * Cx(&1 / &2) * j = j /\
           Cx(&2) * (a * Cx(inv(&2)) * b) = a * b`] THEN DISCH_TAC) THEN
  MATCH_MP_TAC HAS_INTEGRAL_COMBINE THEN
  EXISTS_TAC `&1 / &2 % vec 1:real^1` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DROP_CMUL; DROP_VEC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  CONJ_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE
   [TAUT `a1 /\ a2 /\ b ==> c <=> b ==> a1 /\ a2 ==> c`]
   HAS_INTEGRAL_SPIKE_FINITE)) THENL
   [MP_TAC(REWRITE_RULE[valid_path] (ASSUME `valid_path g1`));
    MP_TAC(REWRITE_RULE[valid_path] (ASSUME `valid_path g2`))] THEN
  REWRITE_TAC[piecewise_differentiable_on] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^1->bool` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `((&1 / &2) % vec 1) INSERT {x:real^1 | (&2 % x) IN s}`;
    EXISTS_TAC `((&1 / &2) % vec 1) INSERT
                {x:real^1 | (&2 % x - vec 1) IN s}`] THEN
  (CONJ_TAC THENL
    [REWRITE_TAC[FINITE_INSERT] THEN MATCH_MP_TAC FINITE_IMAGE_INJ THEN
     ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
     ALL_TAC]) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FINITE_INSERT; IN_DIFF; IN_INSERT; DE_MORGAN_THM;
              joinpaths; IN_INTERVAL_1; DROP_VEC; DROP_CMUL; GSYM DROP_EQ] THEN
  SIMP_TAC[REAL_LT_IMP_LE; REAL_MUL_RID; IN_ELIM_THM;
         REAL_ARITH `&1 / &2 <= x /\ ~(x = &1 / &2) ==> ~(x <= &1 / &2)`] THEN
  REWRITE_TAC[LIFT_CMUL; LIFT_SUB; LIFT_DROP; LIFT_NUM; GSYM VECTOR_SUB] THEN
  X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN
  MATCH_MP_TAC(COMPLEX_RING `x = Cx(&2) * y ==> g * x = Cx(&2) * g * y`) THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THENL
   [EXISTS_TAC `(\x. g1(&2 % x)):real^1->complex`;
    EXISTS_TAC `(\x. g2(&2 % x - vec 1)):real^1->complex`] THEN
  EXISTS_TAC `abs(drop x - &1 / &2)` THEN
  REWRITE_TAC[DIST_REAL; GSYM drop; GSYM REAL_ABS_NZ] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NE; REAL_SUB_0] THEN
  (CONJ_TAC THENL
    [GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
     ASM_REAL_ARITH_TAC;
     ALL_TAC]) THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM o_DEF] THEN
  REWRITE_TAC[GSYM COMPLEX_CMUL] THEN
  SUBST1_TAC(SYM(SPEC `2` DROP_VEC)) THEN
  MATCH_MP_TAC VECTOR_DIFF_CHAIN_AT THEN
  (CONJ_TAC THENL
    [TRY(GEN_REWRITE_TAC LAND_CONV [GSYM VECTOR_SUB_RZERO] THEN
         MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN
         REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST]) THEN
     REWRITE_TAC[has_vector_derivative] THEN
     MATCH_MP_TAC(MESON[HAS_DERIVATIVE_LINEAR]
      `f = g /\ linear f ==> (f has_derivative g) net`) THEN
     REWRITE_TAC[linear; FUN_EQ_THM; DROP_VEC] THEN
     REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; DROP_CMUL; DROP_VEC] THEN
     REAL_ARITH_TAC;
     REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_SIMP_TAC[IN_DIFF; IN_INTERVAL_1; DROP_SUB; DROP_CMUL; DROP_VEC] THEN
     ASM_REAL_ARITH_TAC]));;

let PATH_INTEGRABLE_JOIN = prove
 (`!f g1 g2.
        valid_path g1 /\ valid_path g2
        ==> (f path_integrable_on (g1 ++ g2) <=>
             f path_integrable_on g1 /\ f path_integrable_on g2)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[path_integrable_on] THEN
    ASM_MESON_TAC[HAS_PATH_INTEGRAL_JOIN]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[valid_path]) THEN
  REWRITE_TAC[PATH_INTEGRABLE_ON; joinpaths] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] INTEGRABLE_ON_SUBINTERVAL))
  THENL
   [DISCH_THEN(MP_TAC o SPECL [`lift(&0)`; `lift(&1 / &2)`]);
    DISCH_THEN(MP_TAC o SPECL [`lift(&1 / &2)`; `lift(&1)`])] THEN
  REWRITE_TAC[SUBSET_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] INTEGRABLE_AFFINITY))
  THENL
   [DISCH_THEN(MP_TAC o SPECL [`&1 / &2`; `vec 0:real^1`]);
    DISCH_THEN(MP_TAC o SPECL [`&1 / &2`; `lift(&1 / &2)`])] THEN
  REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[IMAGE_AFFINITY_INTERVAL; INTERVAL_EQ_EMPTY_1] THEN
  REWRITE_TAC[LIFT_DROP; LIFT_NUM; VECTOR_MUL_RZERO; VECTOR_NEG_0;
              GSYM LIFT_CMUL; VECTOR_ADD_RID; VECTOR_MUL_RNEG] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[LIFT_NUM] THEN
  REWRITE_TAC[VECTOR_ARITH `vec 2 + --vec 1:real^1 = vec 1`;
              VECTOR_ARITH `vec 1 + --vec 1:real^1 = vec 0`] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &2` o MATCH_MP INTEGRABLE_CMUL) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_SPIKE_FINITE THEN
  REWRITE_TAC[IN_DIFF; IN_INTERVAL_1; DROP_VEC; DROP_CMUL; DROP_ADD;
              LIFT_DROP; COMPLEX_CMUL] THEN
  REWRITE_TAC[COMPLEX_RING `a * b = Cx(&1 / &2) * x * y <=>
                                x * y = a * Cx(&2) * b`]
  THENL
   [UNDISCH_TAC `(g1:real^1->complex) piecewise_differentiable_on
                        interval[vec 0,vec 1]`;
    UNDISCH_TAC `(g2:real^1->complex) piecewise_differentiable_on
                        interval[vec 0,vec 1]`] THEN
  REWRITE_TAC[piecewise_differentiable_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^1->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(vec 0:real^1) INSERT (vec 1) INSERT s` THEN
  ASM_REWRITE_TAC[FINITE_INSERT; IN_INSERT; DE_MORGAN_THM] THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN X_GEN_TAC `t:real^1` THEN
  STRIP_TAC THEN BINOP_TAC THENL
   [AP_TERM_TAC THEN
    ASM_SIMP_TAC[REAL_ARITH `x <= &1 ==> &1 / &2 * x <= &1 / &2`] THEN
    AP_TERM_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC;
    AP_TERM_TAC THEN ASM_SIMP_TAC[REAL_ARITH
     `&0 <= t /\ ~(t = &0) ==> ~(&1 / &2 * t + &1 / &2 <= &1 / &2)`] THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; DROP_ADD; DROP_SUB; LIFT_DROP] THEN
    REWRITE_TAC[DROP_VEC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THENL
   [EXISTS_TAC `(\x. g1(&2 % x)):real^1->complex` THEN
    EXISTS_TAC `abs(drop t - &1) / &2` THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < abs x / &2 <=> ~(x = &0)`; REAL_SUB_0] THEN
    REWRITE_TAC[DIST_REAL; GSYM drop; DROP_CMUL] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[REAL_ARITH
       `t <= &1 /\ ~(t = &1) /\ abs(x - &1 / &2 * t) < abs(t - &1) / &2
        ==> x <= &1 / &2`];
      ALL_TAC];
    EXISTS_TAC `(\x. g2(&2 % x - vec 1)):real^1->complex` THEN
    EXISTS_TAC `abs(drop t) / &2` THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < abs x / &2 <=> ~(x = &0)`; REAL_SUB_0] THEN
    REWRITE_TAC[DIST_REAL; GSYM drop; DROP_CMUL; DROP_ADD; LIFT_DROP] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[REAL_ARITH
       `&0 <= t /\ abs(x - (&1 / &2 * t + &1 / &2)) < abs(t) / &2
        ==> ~(x <= &1 / &2)`];
      ALL_TAC]] THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM o_DEF] THEN
  REWRITE_TAC[GSYM COMPLEX_CMUL] THEN
  SUBST1_TAC(SYM(SPEC `2` DROP_VEC)) THEN
  MATCH_MP_TAC VECTOR_DIFF_CHAIN_AT THEN
  (CONJ_TAC THENL
    [TRY(GEN_REWRITE_TAC LAND_CONV [GSYM VECTOR_SUB_RZERO] THEN
         MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN
         REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST]) THEN
     REWRITE_TAC[has_vector_derivative] THEN
     MATCH_MP_TAC(MESON[HAS_DERIVATIVE_LINEAR]
      `f = g /\ linear f ==> (f has_derivative g) net`) THEN
     REWRITE_TAC[linear; FUN_EQ_THM; DROP_VEC] THEN
     REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; DROP_CMUL; DROP_VEC] THEN
     REAL_ARITH_TAC;
     MATCH_MP_TAC(MESON[VECTOR_DERIVATIVE_WORKS]
       `f differentiable (at t) /\ t' = t
        ==> (f has_vector_derivative
                  (vector_derivative f (at t))) (at t')`) THEN
     CONJ_TAC THENL
      [FIRST_X_ASSUM MATCH_MP_TAC THEN
       ASM_REWRITE_TAC[IN_DIFF; IN_INTERVAL_1; DROP_VEC];
       ALL_TAC] THEN
     REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; DROP_ADD; DROP_SUB; LIFT_DROP;
                 DROP_VEC] THEN
     REAL_ARITH_TAC]));;

(* ------------------------------------------------------------------------- *)
(* Reparametrizing to shift the starting point of a (closed) path.           *)
(* ------------------------------------------------------------------------- *)

let VALID_PATH_SHIFTPATH = prove
 (`!g a. valid_path g /\ pathfinish g = pathstart g /\
         a IN interval[vec 0,vec 1]
         ==> valid_path(shiftpath a g)`,
  REWRITE_TAC[valid_path; shiftpath; DROP_ADD; GSYM DROP_VEC] THEN
  REWRITE_TAC[REAL_ARITH `a + x <= y <=> x <= y - a`; GSYM DROP_SUB] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_CASES THEN
  REPLICATE_TAC 2 (CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
    REWRITE_TAC[DROP_SUB; DROP_VEC] THEN REAL_ARITH_TAC;
    ALL_TAC]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `a + vec 1 - a - vec 1:real^1 = vec 0`;
                  VECTOR_ARITH `a + vec 1 - a:real^1 = vec 1`] THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[VECTOR_ARITH `a + x:real^1 = &1 % x + a`];
    ONCE_REWRITE_TAC[VECTOR_ARITH
     `a + x - vec 1:real^1 = &1 % x + (a - vec 1)`]] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_AFFINE THEN
  MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_SUBSET THEN
  EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
  REWRITE_TAC[IMAGE_AFFINITY_INTERVAL; REAL_POS; INTERVAL_EQ_EMPTY_1;
              IN_INTERVAL_1; DROP_SUB; DROP_VEC] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
  REWRITE_TAC[EMPTY_SUBSET; SUBSET_INTERVAL_1; DROP_ADD; DROP_CMUL;
              DROP_SUB; DROP_VEC] THEN
  REAL_ARITH_TAC);;

let HAS_PATH_INTEGRAL_SHIFTPATH = prove
 (`!f g i a.
        (f has_path_integral i) g /\ valid_path g /\
        a IN interval[vec 0,vec 1]
        ==> (f has_path_integral i) (shiftpath a g)`,
  REWRITE_TAC[HAS_PATH_INTEGRAL; IN_INTERVAL_1; DROP_VEC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `i = integral (interval[a,vec 1])
                 (\x. f ((g:real^1->real^2) x) * vector_derivative g (at x)) +
        integral (interval[vec 0,a])
                 (\x. f (g x) * vector_derivative g (at x))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:1`,`:M`; `:2`,`:N`] HAS_INTEGRAL_UNIQUE) THEN
    MAP_EVERY EXISTS_TAC
     [`\x. f ((g:real^1->real^2) x) * vector_derivative g (at x)`;
      `interval[vec 0:real^1,vec 1]`] THEN
    ONCE_REWRITE_TAC[COMPLEX_ADD_SYM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_INTEGRAL_COMBINE THEN EXISTS_TAC `a:real^1` THEN
    ASM_REWRITE_TAC[DROP_VEC] THEN
    CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_INTEGRAL THEN
    MATCH_MP_TAC INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`vec 0:real^1`; `vec 1:real^1`] THEN
    (CONJ_TAC THENL [ASM_MESON_TAC[integrable_on]; ALL_TAC]) THEN
    REWRITE_TAC[DROP_SUB; DROP_VEC; SUBSET_INTERVAL_1] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_INTEGRAL_COMBINE THEN EXISTS_TAC `vec 1 - a:real^1` THEN
  ASM_REWRITE_TAC[DROP_SUB; DROP_VEC; REAL_SUB_LE;
                  REAL_ARITH `&1 - x <= &1 <=> &0 <= x`] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [valid_path]) THEN
  REWRITE_TAC[piecewise_differentiable_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^1->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[shiftpath] THEN CONJ_TAC THEN
  MATCH_MP_TAC HAS_INTEGRAL_SPIKE_FINITE THENL
   [EXISTS_TAC `\x. f(g(a + x)) * vector_derivative g (at(a + x))` THEN
    EXISTS_TAC `(vec 1 - a) INSERT IMAGE (\x:real^1. x - a) s` THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FINITE_INSERT] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^1` THEN
      REWRITE_TAC[IN_DIFF; IN_INTERVAL_1; IN_INSERT; IN_IMAGE; UNWIND_THM2;
                  DROP_SUB; DROP_ADD; DROP_VEC; DE_MORGAN_THM;
                  VECTOR_ARITH `x:real^1 = y - a <=> y = a + x`] THEN
      REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; DROP_VEC] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[REAL_ARITH `x <= &1 - a ==> a + x <= &1`] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
      MAP_EVERY EXISTS_TAC
       [`\x. (g:real^1->complex)(a + x)`; `dist(vec 1 - a:real^1,x)`] THEN
      SIMP_TAC[CONJ_ASSOC; dist; NORM_REAL; GSYM drop; DROP_VEC; DROP_SUB] THEN
      CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM o_DEF] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM VECTOR_MUL_LID] THEN
      REWRITE_TAC[GSYM DROP_VEC] THEN MATCH_MP_TAC VECTOR_DIFF_CHAIN_AT THEN
      SUBST1_TAC(VECTOR_ARITH `vec 1:real^1 = vec 0 + vec 1`) THEN
      SIMP_TAC[HAS_VECTOR_DERIVATIVE_ADD; HAS_VECTOR_DERIVATIVE_CONST;
               HAS_VECTOR_DERIVATIVE_ID] THEN
      REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_INTERVAL_1; DROP_VEC; DROP_ADD] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(\x. f (g x) * vector_derivative g (at x)) integrable_on
                  (interval [a,vec 1])`
    MP_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`vec 0:real^1`; `vec 1:real^1`] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[integrable_on]; ALL_TAC] THEN
      ASM_REWRITE_TAC[DROP_SUB; DROP_VEC; SUBSET_INTERVAL_1; REAL_LE_REFL];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o C CONJ (REAL_ARITH `~(&1 = &0)`) o MATCH_MP
      INTEGRABLE_INTEGRAL) THEN
    DISCH_THEN(MP_TAC o SPEC `a:real^1` o MATCH_MP HAS_INTEGRAL_AFFINITY) THEN
    REWRITE_TAC[IMAGE_AFFINITY_INTERVAL] THEN
    REWRITE_TAC[VECTOR_ARITH `&1 % x + a:real^1 = a + x`] THEN
    REWRITE_TAC[REAL_INV_1; REAL_POS; REAL_ABS_NUM; REAL_POW_ONE] THEN
    ASM_REWRITE_TAC[INTERVAL_EQ_EMPTY_1; DROP_VEC; GSYM REAL_NOT_LE] THEN
    REWRITE_TAC[VECTOR_MUL_LID; GSYM VECTOR_SUB; VECTOR_SUB_REFL];
    EXISTS_TAC `\x. f(g(a + x - vec 1)) *
                    vector_derivative g (at(a + x - vec 1))` THEN
    EXISTS_TAC `(vec 1 - a) INSERT IMAGE (\x:real^1. x - a + vec 1) s` THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FINITE_INSERT] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^1` THEN
      REWRITE_TAC[IN_DIFF; IN_INTERVAL_1; IN_INSERT; IN_IMAGE; UNWIND_THM2;
                  DROP_SUB; DROP_ADD; DROP_VEC; DE_MORGAN_THM;
                  VECTOR_ARITH `x:real^1 = y - a + z <=> y = a + (x - z)`] THEN
      REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; DROP_VEC; DROP_SUB] THEN
      STRIP_TAC THEN
      ASM_SIMP_TAC[REAL_ARITH
       `&1 - a <= x /\ ~(x = &1 - a) ==> ~(a + x <= &1)`] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
      MAP_EVERY EXISTS_TAC
       [`\x. (g:real^1->complex)(a + x - vec 1)`;
        `dist(vec 1 - a:real^1,x)`] THEN
      SIMP_TAC[CONJ_ASSOC; dist; NORM_REAL; GSYM drop; DROP_VEC; DROP_SUB] THEN
      CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM o_DEF] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM VECTOR_MUL_LID] THEN
      REWRITE_TAC[GSYM DROP_VEC] THEN MATCH_MP_TAC VECTOR_DIFF_CHAIN_AT THEN
      CONJ_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM VECTOR_ADD_LID] THEN
        ONCE_REWRITE_TAC[VECTOR_ARITH
         `a + x - vec 1:real^1 = (a - vec 1) + x`] THEN
        SIMP_TAC[HAS_VECTOR_DERIVATIVE_ADD; HAS_VECTOR_DERIVATIVE_CONST;
                 HAS_VECTOR_DERIVATIVE_ID];
        ALL_TAC] THEN
      REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[IN_DIFF; DROP_SUB; IN_INTERVAL_1; DROP_VEC; DROP_ADD] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(\x. f (g x) * vector_derivative g (at x)) integrable_on
                  (interval [vec 0,a])`
    MP_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`vec 0:real^1`; `vec 1:real^1`] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[integrable_on]; ALL_TAC] THEN
      ASM_REWRITE_TAC[DROP_SUB; DROP_VEC; SUBSET_INTERVAL_1; REAL_LE_REFL];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o C CONJ (REAL_ARITH `~(&1 = &0)`) o MATCH_MP
      INTEGRABLE_INTEGRAL) THEN
    DISCH_THEN(MP_TAC o SPEC `a - vec 1:real^1` o
      MATCH_MP HAS_INTEGRAL_AFFINITY) THEN
    REWRITE_TAC[IMAGE_AFFINITY_INTERVAL] THEN
    REWRITE_TAC[VECTOR_ARITH `&1 % x + a - vec 1:real^1 = a + x - vec 1`] THEN
    REWRITE_TAC[REAL_INV_1; REAL_POS; REAL_ABS_NUM; REAL_POW_ONE] THEN
    ASM_REWRITE_TAC[INTERVAL_EQ_EMPTY_1; DROP_VEC; GSYM REAL_NOT_LE] THEN
    REWRITE_TAC[VECTOR_MUL_LID;
                VECTOR_ARITH `vec 0 + --(a - vec 1):real^1 = vec 1 - a`;
                VECTOR_ARITH `a + --(a - vec 1):real^1 = vec 1`]]);;

let HAS_PATH_INTEGRAL_SHIFTPATH_EQ = prove
 (`!f g i a.
        valid_path g /\ pathfinish g = pathstart g /\
        a IN interval[vec 0,vec 1]
        ==> ((f has_path_integral i) (shiftpath a g) <=>
             (f has_path_integral i) g)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[HAS_PATH_INTEGRAL_SHIFTPATH] THEN
  SUBGOAL_THEN
   `(f has_path_integral i) (shiftpath (vec 1 - a) (shiftpath a g))`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_PATH_INTEGRAL_SHIFTPATH THEN
    ASM_SIMP_TAC[VALID_PATH_SHIFTPATH] THEN REPEAT(POP_ASSUM MP_TAC) THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; DROP_SUB] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[HAS_PATH_INTEGRAL] THEN MATCH_MP_TAC EQ_IMP THEN
  MATCH_MP_TAC HAS_INTEGRAL_SPIKE_FINITE_EQ THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [valid_path]) THEN
  REWRITE_TAC[piecewise_differentiable_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^1->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(s:real^1->bool) UNION {vec 0,vec 1}` THEN
  ASM_SIMP_TAC[FINITE_UNION; FINITE_RULES] THEN
  REWRITE_TAC[SET_RULE `s DIFF (t UNION u) = (s DIFF u) DIFF t`] THEN
  REWRITE_TAC[GSYM OPEN_CLOSED_INTERVAL_1] THEN X_GEN_TAC `x:real^1` THEN
  STRIP_TAC THEN   BINOP_TAC THEN CONV_TAC SYM_CONV THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC SHIFTPATH_SHIFTPATH THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[INTERVAL_OPEN_SUBSET_CLOSED; SUBSET; IN_DIFF];
    ALL_TAC] THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  MAP_EVERY EXISTS_TAC
   [`g:real^1->real^2`; `interval(vec 0,vec 1) DIFF s:real^1->bool`] THEN
  ASM_SIMP_TAC[GSYM VECTOR_DERIVATIVE_WORKS; OPEN_DIFF; FINITE_IMP_CLOSED;
               OPEN_INTERVAL] THEN
  REPEAT STRIP_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SHIFTPATH_SHIFTPATH;
    FIRST_X_ASSUM MATCH_MP_TAC] THEN
  ASM_MESON_TAC[INTERVAL_OPEN_SUBSET_CLOSED; SUBSET; IN_DIFF]);;

let PATH_INTEGRAL_SHIFTPATH = prove
 (`!f g a. valid_path g /\ pathfinish g = pathstart g /\
           a IN interval[vec 0,vec 1]
           ==> path_integral (shiftpath a g) f = path_integral g f`,
  SIMP_TAC[path_integral; HAS_PATH_INTEGRAL_SHIFTPATH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* More about straight-line paths.                                           *)
(* ------------------------------------------------------------------------- *)

let HAS_VECTOR_DERIVATIVE_LINEPATH_WITHIN = prove
 (`!a b:complex x s.
    (linepath(a,b) has_vector_derivative (b - a)) (at x within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linepath; has_vector_derivative] THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH `u % (b - a) = vec 0 + u % (b - a)`] THEN
  REWRITE_TAC[VECTOR_ARITH `(&1 - u) % a + u % b = a + u % (b - a)`] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_VMUL_DROP THEN REWRITE_TAC[HAS_DERIVATIVE_ID]);;

let HAS_VECTOR_DERIVATIVE_LINEPATH_AT = prove
 (`!a b:complex x.
    (linepath(a,b) has_vector_derivative (b - a)) (at x)`,
  MESON_TAC[WITHIN_UNIV; HAS_VECTOR_DERIVATIVE_LINEPATH_WITHIN]);;

let VALID_PATH_LINEPATH = prove
 (`!a b. valid_path(linepath(a,b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[valid_path] THEN
  MATCH_MP_TAC DIFFERENTIABLE_ON_IMP_PIECEWISE_DIFFERENTIABLE THEN
  REWRITE_TAC[differentiable_on; differentiable] THEN
  MESON_TAC[HAS_VECTOR_DERIVATIVE_LINEPATH_WITHIN; has_vector_derivative]);;

let VECTOR_DERIVATIVE_LINEPATH_WITHIN = prove
 (`!a b x s. x IN interval[vec 0,vec 1]
             ==> vector_derivative (linepath(a,b))
                    (at x within interval[vec 0,vec 1]) = b - a`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
  ASM_REWRITE_TAC[HAS_VECTOR_DERIVATIVE_LINEPATH_WITHIN] THEN
  REWRITE_TAC[DROP_VEC; REAL_LT_01]);;

let VECTOR_DERIVATIVE_LINEPATH_AT = prove
 (`!a b x. vector_derivative (linepath(a,b)) (at x) = b - a`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
  ASM_REWRITE_TAC[HAS_VECTOR_DERIVATIVE_LINEPATH_AT]);;

let HAS_PATH_INTEGRAL_LINEPATH = prove
 (`!f i a b. (f has_path_integral i) (linepath(a,b)) <=>
             ((\x. f(linepath(a,b) x) * (b - a)) has_integral i)
             (interval[vec 0,vec 1])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_path_integral] THEN
  MATCH_MP_TAC HAS_INTEGRAL_EQ_EQ THEN
  SIMP_TAC[VECTOR_DERIVATIVE_LINEPATH_WITHIN]);;

let LINEPATH_IN_PATH = prove
 (`!x. x IN interval[vec 0,vec 1] ==> linepath(a,b) x IN segment[a,b]`,
  REWRITE_TAC[segment; linepath; IN_ELIM_THM; IN_INTERVAL_1; DROP_VEC] THEN
  MESON_TAC[]);;

let RE_LINEPATH_CX = prove
 (`!a b x. Re(linepath(Cx a,Cx b) x) = (&1 - drop x) * a + drop x * b`,
  REWRITE_TAC[linepath; RE_ADD; COMPLEX_CMUL; RE_MUL_CX; RE_CX]);;

let IM_LINEPATH_CX = prove
 (`!a b x. Im(linepath(Cx a,Cx b) x) = &0`,
  REWRITE_TAC[linepath; IM_ADD; COMPLEX_CMUL; IM_MUL_CX; IM_CX] THEN
  REAL_ARITH_TAC);;

let LINEPATH_CX = prove
 (`!a b x. linepath(Cx a,Cx b) x = Cx((&1 - drop x) * a + drop x * b)`,
  REWRITE_TAC[COMPLEX_EQ; RE_LINEPATH_CX; IM_LINEPATH_CX; RE_CX; IM_CX]);;

(* ------------------------------------------------------------------------- *)
(* Easier to reason about segments via convex hulls.                         *)
(* ------------------------------------------------------------------------- *)

let SEGMENTS_SUBSET_CONVEX_HULL = prove
 (`!a b c. segment[a,b] SUBSET (convex hull {a,b,c}) /\
           segment[a,c] SUBSET (convex hull {a,b,c}) /\
           segment[b,c] SUBSET (convex hull {a,b,c}) /\
           segment[b,a] SUBSET (convex hull {a,b,c}) /\
           segment[c,a] SUBSET (convex hull {a,b,c}) /\
           segment[c,b] SUBSET (convex hull {a,b,c})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
  MATCH_MP_TAC HULL_MONO THEN SET_TAC[]);;

let MIDPOINTS_IN_CONVEX_HULL = prove
 (`!x:real^N s. x IN convex hull s /\ y IN convex hull s
         ==> midpoint(x,y) IN convex hull s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[midpoint; VECTOR_ARITH
    `inv(&2) % (x + y):real^N = (&1 - inv(&2)) % x + inv(&2) % y`] THEN
  MATCH_MP_TAC IN_CONVEX_SET THEN
  ASM_REWRITE_TAC[CONVEX_CONVEX_HULL] THEN REAL_ARITH_TAC);;

let POINTS_IN_CONVEX_HULL = prove
 (`!x s. x IN s ==> x IN convex hull s`,
  MESON_TAC[SUBSET; HULL_SUBSET]);;

let CONVEX_HULL_SUBSET = prove
 (`(!x. x IN s ==> x IN convex hull t)
   ==> (convex hull s) SUBSET (convex hull t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN
  ASM_REWRITE_TAC[CONVEX_CONVEX_HULL; SUBSET]);;

let NOT_IN_INTERIOR_CONVEX_HULL_3 = prove
 (`!a b c:complex. ~(a IN interior(convex hull {a,b,c})) /\
                   ~(b IN interior(convex hull {a,b,c})) /\
                   ~(c IN interior(convex hull {a,b,c}))`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN
  MATCH_MP_TAC NOT_IN_INTERIOR_CONVEX_HULL THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT] THEN
  REWRITE_TAC[DIMINDEX_2] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Cauchy's theorem where there's a primitive.                               *)
(* ------------------------------------------------------------------------- *)

let PATH_INTEGRAL_PRIMITIVE_LEMMA = prove
 (`!f f' g a b s.
        ~(interval[a,b] = {}) /\
        (!x. x IN s ==> (f has_complex_derivative f'(x)) (at x within s)) /\
        g piecewise_differentiable_on interval[a,b] /\
        (!x. x IN interval[a,b] ==> g(x) IN s)
        ==> ((\x. f'(g x) * vector_derivative g (at x within interval[a,b]))
             has_integral (f(g b) - f(g a))) (interval[a,b])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[valid_path; piecewise_differentiable_on] THEN
  REWRITE_TAC[INTERVAL_EQ_EMPTY_1; REAL_NOT_LT] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:real^1->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR_STRONG THEN
  EXISTS_TAC `k:real^1->bool` THEN ASM_REWRITE_TAC[DROP_VEC; REAL_POS] THEN
  REWRITE_TAC[GSYM o_DEF] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:complex->bool` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_IMP_CONTINUOUS_ON THEN
    ASM_MESON_TAC[holomorphic_on];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^1` THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_vector_derivative; COMPLEX_CMUL] THEN
  SUBGOAL_THEN `(f has_complex_derivative f'(g x))
                (at (g x) within (IMAGE g (interval[a:real^1,b])))`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `s:complex->bool` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[INTERVAL_OPEN_SUBSET_CLOSED; SUBSET; IN_DIFF];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(g:real^1->complex) differentiable (at x within interval[a,b])`
  MP_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_AT_WITHIN THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[INTERVAL_OPEN_SUBSET_CLOSED; SUBSET; IN_DIFF];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [VECTOR_DERIVATIVE_WORKS] THEN
  REWRITE_TAC[has_vector_derivative; IMP_IMP; has_complex_derivative] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIFF_CHAIN_WITHIN) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    HAS_DERIVATIVE_WITHIN_SUBSET)) THEN
  DISCH_THEN(MP_TAC o SPEC `interval(a:real^1,b)`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_DIFF]) THEN
  ASM_SIMP_TAC[INTERVAL_OPEN_SUBSET_CLOSED; OPEN_INTERVAL;
               HAS_DERIVATIVE_WITHIN_OPEN] THEN
  REWRITE_TAC[o_DEF; COMPLEX_CMUL] THEN REWRITE_TAC[COMPLEX_MUL_AC]);;

let PATH_INTEGRAL_PRIMITIVE = prove
 (`!f f' g s.
        (!x. x IN s ==> (f has_complex_derivative f'(x)) (at x within s)) /\
        valid_path g /\ (path_image g) SUBSET s
        ==> (f' has_path_integral (f(pathfinish g) - f(pathstart g))) (g)`,
  REWRITE_TAC[valid_path; path_image; pathfinish; pathstart] THEN
  REWRITE_TAC[has_path_integral] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_INTEGRAL_PRIMITIVE_LEMMA THEN
  ASM_REWRITE_TAC[INTERVAL_EQ_EMPTY_1; DROP_VEC; REAL_POS; REAL_NOT_LT] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
  ASM_MESON_TAC[]);;

let CAUCHY_THEOREM_PRIMITIVE = prove
 (`!f f' g s.
        (!x. x IN s ==> (f has_complex_derivative f'(x)) (at x within s)) /\
        valid_path g /\ (path_image g) SUBSET s /\
        pathfinish g = pathstart g
        ==> (f' has_path_integral Cx(&0)) (g)`,
  MESON_TAC[PATH_INTEGRAL_PRIMITIVE; COMPLEX_SUB_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Existence of path integral for continuous function.                       *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_ON_COMPLEX_CMUL = prove
 (`!f:real^N->complex s. f continuous_on s ==> (\x. c * f(x)) continuous_on s`,
  REWRITE_TAC[CONTINUOUS_ON] THEN SIMP_TAC[LIM_COMPLEX_MUL; LIM_CONST]);;

let PATH_INTEGRABLE_CONTINUOUS_LINEPATH = prove
 (`!f a b. f continuous_on segment[a,b]
           ==> f path_integrable_on (linepath(a,b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[path_integrable_on; has_path_integral] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[GSYM integrable_on] THEN MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\x. f(linepath(a,b) x) * (b - a)` THEN
  SIMP_TAC[VECTOR_DERIVATIVE_LINEPATH_WITHIN] THEN
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_CMUL THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  ASM_REWRITE_TAC[GSYM path_image; ETA_AX; PATH_IMAGE_LINEPATH] THEN
  REWRITE_TAC[CONTINUOUS_ON_LINEPATH]);;

(* ------------------------------------------------------------------------- *)
(* A complex-specific theorem for integrals.                                 *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_COMPLEX_CMUL = prove
 (`!f y i c. (f has_integral y) i ==> ((\x. c * f(x)) has_integral (c * y)) i`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC
   (REWRITE_RULE[o_DEF] HAS_INTEGRAL_LINEAR) THEN
  ASM_REWRITE_TAC[linear; COMPLEX_CMUL] THEN CONV_TAC COMPLEX_RING);;

(* ------------------------------------------------------------------------- *)
(* Arithmetical combining theorems.                                          *)
(* ------------------------------------------------------------------------- *)

let HAS_PATH_INTEGRAL_CONST_LINEPATH = prove
 (`!a b c. ((\x. c) has_path_integral (c * (b - a))) (linepath(a,b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_PATH_INTEGRAL_LINEPATH] THEN
  MP_TAC(ISPECL [`vec 0:real^1`; `vec 1:real^1`; `c * (b - a):complex`]
         HAS_INTEGRAL_CONST) THEN
  REWRITE_TAC[CONTENT_UNIT; VECTOR_MUL_LID]);;

let HAS_PATH_INTEGRAL_NEG = prove
 (`!f i g. (f has_path_integral i) g
           ==> ((\x. --(f x)) has_path_integral (--i)) g`,
  REWRITE_TAC[has_path_integral; COMPLEX_MUL_LNEG; HAS_INTEGRAL_NEG]);;

let HAS_PATH_INTEGRAL_ADD = prove
 (`!f1 i1 f2 i2 g.
        (f1 has_path_integral i1) g /\ (f2 has_path_integral i2) g
        ==> ((\x. f1(x) + f2(x)) has_path_integral (i1 + i2)) g`,
  REWRITE_TAC[has_path_integral; COMPLEX_ADD_RDISTRIB] THEN
  SIMP_TAC[HAS_INTEGRAL_ADD]);;

let HAS_PATH_INTEGRAL_SUB = prove
 (`!f1 i1 f2 i2 g.
        (f1 has_path_integral i1) g /\ (f2 has_path_integral i2) g
         ==> ((\x. f1(x) - f2(x)) has_path_integral (i1 - i2)) g`,
  REWRITE_TAC[has_path_integral; COMPLEX_SUB_RDISTRIB] THEN
  SIMP_TAC[HAS_INTEGRAL_SUB]);;

let HAS_PATH_INTEGRAL_COMPLEX_LMUL = prove
 (`!f g i c. (f has_path_integral i) g
             ==> ((\x. c * f x) has_path_integral (c * i)) g`,
  REWRITE_TAC[has_path_integral; HAS_INTEGRAL_COMPLEX_CMUL;
              GSYM COMPLEX_MUL_ASSOC]);;

let HAS_PATH_INTEGRAL_COMPLEX_RMUL = prove
 (`!f g i c. (f has_path_integral i) g
             ==> ((\x. f x * c) has_path_integral (i * c)) g`,
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
  REWRITE_TAC[HAS_PATH_INTEGRAL_COMPLEX_LMUL]);;

let HAS_PATH_INTEGRAL_COMPLEX_DIV = prove
 (`!f g i c. (f has_path_integral i) g
             ==> ((\x. f x / c) has_path_integral (i / c)) g`,
  REWRITE_TAC[complex_div; HAS_PATH_INTEGRAL_COMPLEX_RMUL]);;

let HAS_PATH_INTEGRAL_EQ = prove
 (`!f g p y.
        (!x. x IN path_image p ==> f x = g x) /\
        (f has_path_integral y) p
        ==> (g has_path_integral y) p`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[path_image; IN_IMAGE; has_path_integral; IMP_CONJ] THEN
  DISCH_TAC THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_EQ) THEN
  ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]);;

let HAS_PATH_INTEGRAL_BOUND_LINEPATH = prove
 (`!f i a b B.
        (f has_path_integral i) (linepath(a,b)) /\
        &0 <= B /\ (!x. x IN segment[a,b] ==> norm(f x) <= B)
        ==> norm(i) <= B * norm(b - a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_path_integral] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  REWRITE_TAC[GSYM CONTENT_UNIT_1] THEN MATCH_MP_TAC HAS_INTEGRAL_BOUND THEN
  EXISTS_TAC `\x. f (linepath (a,b) x) *
                    vector_derivative (linepath (a,b))
                       (at x within interval [vec 0,vec 1])` THEN
  ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE;
               VECTOR_DERIVATIVE_LINEPATH_WITHIN] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[COMPLEX_NORM_MUL] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[GSYM PATH_IMAGE_LINEPATH; path_image] THEN
  ASM SET_TAC[]);;

let HAS_PATH_INTEGRAL_0 = prove
 (`!g. ((\x. Cx(&0)) has_path_integral Cx(&0)) g`,
  REWRITE_TAC[has_path_integral; COMPLEX_MUL_LZERO] THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0; HAS_INTEGRAL_0]);;

let HAS_PATH_INTEGRAL_VSUM = prove
 (`!f p s. FINITE s /\ (!a. a IN s ==> (f a has_path_integral i a) p)
           ==> ((\x. vsum s (\a. f a x)) has_path_integral vsum s i) p`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; HAS_PATH_INTEGRAL_0; COMPLEX_VEC_0; IN_INSERT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_PATH_INTEGRAL_ADD THEN
  ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Same thing non-relationally.                                              *)
(* ------------------------------------------------------------------------- *)

let PATH_INTEGRAL_CONST_LINEPATH = prove
 (`!a b c. path_integral (linepath(a,b)) (\x. c) = c * (b - a)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
  REWRITE_TAC[HAS_PATH_INTEGRAL_CONST_LINEPATH]);;

let PATH_INTEGRAL_NEG = prove
 (`!f g. f path_integrable_on g
         ==> path_integral g (\x. --(f x)) = --(path_integral g f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_NEG THEN
  ASM_SIMP_TAC[HAS_PATH_INTEGRAL_INTEGRAL]);;

let PATH_INTEGRAL_ADD = prove
 (`!f1 f2 g.
        f1 path_integrable_on g /\ f2 path_integrable_on g
        ==> path_integral g (\x. f1(x) + f2(x)) =
                path_integral g f1 + path_integral g f2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_ADD THEN
  ASM_SIMP_TAC[HAS_PATH_INTEGRAL_INTEGRAL]);;

let PATH_INTEGRAL_SUB = prove
 (`!f1 f2 g.
        f1 path_integrable_on g /\ f2 path_integrable_on g
        ==> path_integral g (\x. f1(x) - f2(x)) =
                path_integral g f1 - path_integral g f2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_SUB THEN
  ASM_SIMP_TAC[HAS_PATH_INTEGRAL_INTEGRAL]);;

let PATH_INTEGRAL_COMPLEX_LMUL = prove
 (`!f g c.  f path_integrable_on g
           ==> path_integral g (\x. c * f x) = c * path_integral g f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_COMPLEX_LMUL THEN
  ASM_SIMP_TAC[HAS_PATH_INTEGRAL_INTEGRAL]);;

let PATH_INTEGRAL_COMPLEX_RMUL = prove
 (`!f g c.  f path_integrable_on g
           ==> path_integral g (\x. f x * c) = path_integral g f * c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_COMPLEX_RMUL THEN
  ASM_SIMP_TAC[HAS_PATH_INTEGRAL_INTEGRAL]);;

let PATH_INTEGRAL_COMPLEX_DIV = prove
 (`!f g c.  f path_integrable_on g
           ==> path_integral g (\x. f x / c) = path_integral g f / c`,
   REWRITE_TAC[complex_div; PATH_INTEGRAL_COMPLEX_RMUL]);;

let PATH_INTEGRAL_EQ = prove
 (`!f g p y.
        (!x. x IN path_image p ==> f x = g x) /\
        f path_integrable_on p
        ==> path_integral p f = path_integral p g`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN MATCH_MP_TAC HAS_PATH_INTEGRAL_EQ THEN
  EXISTS_TAC `f:complex->complex` THEN
  ASM_SIMP_TAC[HAS_PATH_INTEGRAL_INTEGRAL]);;

let PATH_INTEGRAL_BOUND_LINEPATH = prove
 (`!f a b.
        f path_integrable_on (linepath(a,b)) /\
        &0 <= B /\ (!x. x IN segment[a,b] ==> norm(f x) <= B)
        ==> norm(path_integral (linepath(a,b)) f) <= B * norm(b - a)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_BOUND_LINEPATH THEN
  EXISTS_TAC `f:complex->complex` THEN
  ASM_SIMP_TAC[HAS_PATH_INTEGRAL_INTEGRAL]);;

let PATH_INTEGRAL_0 = prove
 (`!g. path_integral g (\x. Cx(&0)) = Cx(&0)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
  REWRITE_TAC[HAS_PATH_INTEGRAL_0]);;

let PATH_INTEGRAL_VSUM = prove
 (`!f p s. FINITE s /\ (!a. a IN s ==> (f a) path_integrable_on p)
           ==> path_integral p (\x. vsum s (\a. f a x)) =
                vsum s (\a. path_integral p (f a))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_VSUM THEN
  ASM_SIMP_TAC[HAS_PATH_INTEGRAL_INTEGRAL]);;

(* ------------------------------------------------------------------------- *)
(* Arithmetic theorems for path integrability.                               *)
(* ------------------------------------------------------------------------- *)

let PATH_INTEGRABLE_NEG = prove
 (`!f g. f path_integrable_on g
           ==> (\x. --(f x)) path_integrable_on g`,
  REWRITE_TAC[path_integrable_on] THEN MESON_TAC[HAS_PATH_INTEGRAL_NEG]);;

let PATH_INTEGRABLE_ADD = prove
 (`!f1 f2 g.
        f1 path_integrable_on g /\ f2 path_integrable_on g
        ==> (\x. f1(x) + f2(x)) path_integrable_on g`,
  REWRITE_TAC[path_integrable_on] THEN MESON_TAC[HAS_PATH_INTEGRAL_ADD]);;

let PATH_INTEGRABLE_SUB = prove
 (`!f1 f2 g.
        f1 path_integrable_on g /\ f2 path_integrable_on g
        ==> (\x. f1(x) - f2(x)) path_integrable_on g`,
  REWRITE_TAC[path_integrable_on] THEN MESON_TAC[HAS_PATH_INTEGRAL_SUB]);;

let PATH_INTEGRABLE_COMPLEX_LMUL = prove
 (`!f g c. f path_integrable_on g
             ==> (\x. c * f x) path_integrable_on g`,
  REWRITE_TAC[path_integrable_on] THEN
  MESON_TAC[HAS_PATH_INTEGRAL_COMPLEX_LMUL]);;

let PATH_INTEGRABLE_COMPLEX_RMUL = prove
 (`!f g c. f path_integrable_on g
             ==> (\x. f x * c) path_integrable_on g`,
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
  REWRITE_TAC[PATH_INTEGRABLE_COMPLEX_LMUL]);;

let PATH_INTEGRABLE_COMPLEX_DIV = prove
 (`!f g c. f path_integrable_on g
             ==> (\x. f x / c) path_integrable_on g`,
  REWRITE_TAC[path_integrable_on] THEN
  MESON_TAC[HAS_PATH_INTEGRAL_COMPLEX_DIV]);;

let PATH_INTEGRABLE_VSUM = prove
 (`!f g s. FINITE s /\ (!a. a IN s ==> f a path_integrable_on g)
           ==> (\x. vsum s (\a. f a x)) path_integrable_on g`,
  REWRITE_TAC[path_integrable_on] THEN
  MESON_TAC[HAS_PATH_INTEGRAL_VSUM]);;

(* ------------------------------------------------------------------------- *)
(* Considering a path integral "backwards".                                  *)
(* ------------------------------------------------------------------------- *)

let HAS_PATH_INTEGRAL_SWAP = prove
 (`!f a b i.
        (f has_path_integral i) (linepath(a,b))
        ==> (f has_path_integral (--i)) (linepath(b,a))`,
  MESON_TAC[REVERSEPATH_LINEPATH; VALID_PATH_LINEPATH;
            HAS_PATH_INTEGRAL_REVERSEPATH]);;

let PATH_INTEGRAL_SWAP = prove
 (`!f a b.
        f continuous_on (segment[a,b])
        ==> path_integral(linepath(a,b)) f =
            --(path_integral(linepath(b,a)) f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_SWAP THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_INTEGRAL THEN
  MATCH_MP_TAC PATH_INTEGRABLE_CONTINUOUS_LINEPATH THEN
  ASM_MESON_TAC[SEGMENT_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Splitting a path integral in a flat way.                                  *)
(* ------------------------------------------------------------------------- *)

let HAS_PATH_INTEGRAL_TRIVIAL = prove
 (`!f a. (f has_path_integral (Cx(&0))) (linepath(a,a))`,
  REWRITE_TAC[HAS_PATH_INTEGRAL_LINEPATH; COMPLEX_SUB_REFL;
              COMPLEX_MUL_RZERO] THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0; HAS_INTEGRAL_0]);;

let HAS_PATH_INTEGRAL_SPLIT = prove
 (`!f a b c i j k.
        &0 <= k /\ k <= &1 /\ c - a = k % (b - a) /\
        (f has_path_integral i) (linepath(a,c)) /\
        (f has_path_integral j) (linepath(c,b))
        ==> (f has_path_integral (i + j)) (linepath(a,b))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_CASES_TAC `k = &0` THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_SUB_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[HAS_PATH_INTEGRAL_TRIVIAL; PATH_INTEGRAL_UNIQUE;
                  COMPLEX_ADD_LID];
    ALL_TAC] THEN
  ASM_CASES_TAC `k = &1` THEN ASM_REWRITE_TAC[VECTOR_MUL_LID] THENL
   [REWRITE_TAC[VECTOR_ARITH `c - a = b - a <=> c = b:real^N`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[HAS_PATH_INTEGRAL_TRIVIAL; PATH_INTEGRAL_UNIQUE;
                  COMPLEX_ADD_RID];
    ALL_TAC] THEN
  REWRITE_TAC[HAS_PATH_INTEGRAL_LINEPATH] THEN
  REWRITE_TAC[linepath] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN
   (MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_AFFINITY))) THEN
  DISCH_THEN(ASSUME_TAC o SPECL
    [`inv(&1 - k):real`; `--(k / (&1 - k)) % vec 1:real^1`]) THEN
  DISCH_THEN(MP_TAC o SPECL [`inv(k):real`; `vec 0:real^1`]) THEN
  POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[REAL_INV_EQ_0; REAL_SUB_0] THEN
  REWRITE_TAC[REAL_INV_INV; DIMINDEX_1; REAL_POW_1; REAL_ABS_INV] THEN
  REWRITE_TAC[IMAGE_AFFINITY_INTERVAL] THEN
  REWRITE_TAC[INTERVAL_EQ_EMPTY_1; DROP_VEC] THEN
  ASM_REWRITE_TAC[REAL_SUB_LE; REAL_ARITH `~(&1 < &0)`] THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_NEG_0; VECTOR_ADD_RID] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_MUL_LNEG] THEN
  ASM_SIMP_TAC[REAL_FIELD
    `~(k = &1) ==> (&1 - k) * --(k / (&1 - k)) = --k`] THEN
  REWRITE_TAC[VECTOR_ADD_LID; VECTOR_MUL_LNEG; VECTOR_NEG_NEG;
              VECTOR_ARITH `(&1 - k) % x + k % x:real^1 = x`] THEN
  REWRITE_TAC[DROP_ADD; DROP_CMUL; DROP_NEG; DROP_VEC; REAL_MUL_RID] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (VECTOR_ARITH
    `c - a = x ==> c = x + a`)) THEN
  REWRITE_TAC[VECTOR_ARITH `b - (k % (b - a) + a) = (&1 - k) % (b - a)`] THEN
  SUBGOAL_THEN
   `!x. (&1 - (inv (&1 - k) * drop x + --(k / (&1 - k)))) % (k % (b - a) + a) +
        (inv (&1 - k) * drop x + --(k / (&1 - k))) % b =
        (&1 - drop x) % a + drop x % b`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[VECTOR_ARITH
     `x % (k % (b - a) + a) + y % b =
      (x * (&1 - k)) % a + (y + x * k) % b`] THEN
    GEN_TAC THEN BINOP_TAC THEN BINOP_TAC THEN REWRITE_TAC[] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. (&1 - inv k * drop x) % a + (inv k * drop x) % (k % (b - a) + a) =
        (&1 - drop x) % a + drop x % b`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[VECTOR_ARITH
     `x % a + y % (k % (b - a) + a) =
      (x + y * (&1 - k)) % a + (y * k) % b`] THEN
    GEN_TAC THEN BINOP_TAC THEN BINOP_TAC THEN REWRITE_TAC[] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  DISCH_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `inv(k:real)` o MATCH_MP HAS_INTEGRAL_CMUL) THEN
  FIRST_ASSUM(MP_TAC o SPEC `inv(&1 - k)` o MATCH_MP HAS_INTEGRAL_CMUL) THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= k ==> abs k = k`;
               REAL_ARITH `k <= &1 ==> abs(&1 - k) = &1 - k`] THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_SUB_0] THEN
  REWRITE_TAC[IMP_IMP; VECTOR_MUL_LID] THEN
  REWRITE_TAC[COMPLEX_CMUL] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING
   `Cx(inv a) * b * Cx(a) * c = (Cx(inv a) * Cx a) * b * c`] THEN
  ASM_SIMP_TAC[GSYM CX_MUL; REAL_MUL_LINV; REAL_SUB_0; COMPLEX_MUL_LID] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC HAS_INTEGRAL_COMBINE THEN EXISTS_TAC `k % vec 1:real^1` THEN
  ASM_REWRITE_TAC[DROP_CMUL; DROP_VEC; REAL_MUL_RID]);;

let PATH_INTEGRAL_SPLIT = prove
 (`!f a b c k.
        &0 <= k /\ k <= &1 /\ c - a = k % (b - a) /\
        f continuous_on (segment[a,b])
        ==> path_integral(linepath(a,b)) f =
            path_integral(linepath(a,c)) f +
            path_integral(linepath(c,b)) f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_SPLIT THEN
  MAP_EVERY EXISTS_TAC [`c:complex`; `k:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC HAS_PATH_INTEGRAL_INTEGRAL THEN
  MATCH_MP_TAC PATH_INTEGRABLE_CONTINUOUS_LINEPATH THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `segment[a:complex,b]` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC CONVEX_HULL_SUBSET THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[POINTS_IN_CONVEX_HULL; IN_INSERT] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (VECTOR_ARITH
   `c - a = k % (b - a) ==> c = (&1 - k) % a + k % b`)) THEN
  MATCH_MP_TAC IN_CONVEX_SET THEN
  ASM_SIMP_TAC[CONVEX_CONVEX_HULL; POINTS_IN_CONVEX_HULL; IN_INSERT]);;

(* ------------------------------------------------------------------------- *)
(* The special case of midpoints used in the main quadrisection.             *)
(* ------------------------------------------------------------------------- *)

let HAS_PATH_INTEGRAL_MIDPOINT = prove
 (`!f a b i j.
        (f has_path_integral i) (linepath(a,midpoint(a,b))) /\
        (f has_path_integral j) (linepath(midpoint(a,b),b))
        ==> (f has_path_integral (i + j)) (linepath(a,b))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_PATH_INTEGRAL_SPLIT THEN
  MAP_EVERY EXISTS_TAC [`midpoint(a:complex,b)`; `&1 / &2`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[midpoint] THEN VECTOR_ARITH_TAC);;

let PATH_INTEGRAL_MIDPOINT = prove
 (`!f a b.
        f continuous_on (segment[a,b])
        ==> path_integral(linepath(a,b)) f =
            path_integral(linepath(a,midpoint(a,b))) f +
            path_integral(linepath(midpoint(a,b),b)) f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_INTEGRAL_SPLIT THEN
  EXISTS_TAC `&1 / &2` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[midpoint] THEN VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A couple of special case lemmas that are useful below.                    *)
(* ------------------------------------------------------------------------- *)

let TRIANGLE_LINEAR_HAS_CHAIN_INTEGRAL = prove
 (`!a b c m d. ((\x. m * x + d) has_path_integral Cx(&0))
         (linepath(a,b) ++ linepath(b,c) ++ linepath(c,a))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CAUCHY_THEOREM_PRIMITIVE THEN
  MAP_EVERY EXISTS_TAC [`\x. m / Cx(&2) * x pow 2 + d * x`; `(:complex)`] THEN
  SIMP_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH; SUBSET_UNIV;
           PATHFINISH_LINEPATH; VALID_PATH_JOIN; VALID_PATH_LINEPATH] THEN
  REPEAT STRIP_TAC THEN COMPLEX_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC COMPLEX_RING);;

let HAS_CHAIN_INTEGRAL_CHAIN_INTEGRAL = prove
 (`!f i a b c d.
        (f has_path_integral i)
        (linepath(a,b) ++ linepath(b,c) ++ linepath(c,d))
        ==> path_integral (linepath(a,b)) f +
            path_integral (linepath(b,c)) f +
            path_integral (linepath(c,d)) f = i`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP PATH_INTEGRAL_UNIQUE) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP HAS_PATH_INTEGRAL_INTEGRABLE) THEN
  SIMP_TAC[PATH_INTEGRABLE_JOIN; VALID_PATH_LINEPATH; VALID_PATH_JOIN;
           PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
           PATHFINISH_LINEPATH] THEN
  STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
  REPEAT(MATCH_MP_TAC HAS_PATH_INTEGRAL_JOIN THEN
         SIMP_TAC[VALID_PATH_LINEPATH; VALID_PATH_JOIN;
                  PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
                  PATHFINISH_LINEPATH] THEN
         CONJ_TAC) THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_INTEGRAL THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The key quadrisection step.                                               *)
(* ------------------------------------------------------------------------- *)

let NORM_SUM_LEMMA = prove
 (`norm(a + b + c + d:complex) >= e
   ==> norm(a) >= e / &4 \/
       norm(b) >= e / &4 \/
       norm(c) >= e / &4 \/
       norm(d) >= e / &4`,
  NORM_ARITH_TAC);;

let CAUCHY_THEOREM_QUADRISECTION = prove
 (`!f a b c e K.
        f continuous_on (convex hull {a,b,c}) /\
        dist (a,b) <= K /\
        dist (b,c) <= K /\
        dist (c,a) <= K /\
        norm(path_integral(linepath(a,b)) f +
             path_integral(linepath(b,c)) f +
             path_integral(linepath(c,a)) f) >= e * K pow 2
        ==> ?a' b' c'. a' IN convex hull {a,b,c} /\
                       b' IN convex hull {a,b,c} /\
                       c' IN convex hull {a,b,c} /\
                       dist(a',b') <= K / &2 /\
                       dist(b',c') <= K / &2 /\
                       dist(c',a') <= K / &2 /\
                       norm(path_integral(linepath(a',b')) f +
                            path_integral(linepath(b',c')) f +
                            path_integral(linepath(c',a')) f)
                        >= e * (K / &2) pow 2`,
  REPEAT STRIP_TAC THEN MAP_EVERY ABBREV_TAC
   [`a':complex = midpoint(b,c)`;
    `b':complex = midpoint(c,a)`;
    `c':complex = midpoint(a,b)`] THEN
  SUBGOAL_THEN
   `path_integral(linepath(a,b)) f +
    path_integral(linepath(b,c)) f +
    path_integral(linepath(c,a)) f =
    (path_integral(linepath(a,c')) f +
     path_integral(linepath(c',b')) f +
     path_integral(linepath(b',a)) f) +
    (path_integral(linepath(a',c')) f +
     path_integral(linepath(c',b)) f +
     path_integral(linepath(b,a')) f) +
    (path_integral(linepath(a',c)) f +
     path_integral(linepath(c,b')) f +
     path_integral(linepath(b',a')) f) +
    (path_integral(linepath(a',b')) f +
     path_integral(linepath(b',c')) f +
     path_integral(linepath(c',a')) f)`
  SUBST_ALL_TAC THENL
   [MP_TAC(SPEC `f:complex->complex` PATH_INTEGRAL_MIDPOINT) THEN DISCH_THEN
     (fun th -> MP_TAC(SPECL [`a:complex`; `b:complex`] th) THEN
                MP_TAC(SPECL [`b:complex`; `c:complex`] th) THEN
                MP_TAC(SPECL [`c:complex`; `a:complex`] th)) THEN
    MP_TAC(SPEC `f:complex->complex` PATH_INTEGRAL_SWAP) THEN DISCH_THEN
     (fun th -> MP_TAC(SPECL [`a':complex`; `b':complex`] th) THEN
                MP_TAC(SPECL [`b':complex`; `c':complex`] th) THEN
                MP_TAC(SPECL [`c':complex`; `a':complex`] th)) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC(TAUT
     `((a /\ c ==> b /\ d) ==> e) ==> (a ==> b) ==> (c ==> d) ==> e`)) THEN
    ANTS_TAC THENL [ALL_TAC; CONV_TAC COMPLEX_RING] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `convex hull {a:complex,b,c}` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONVEX_HULL_SUBSET THEN
    SIMP_TAC[IN_INSERT; NOT_IN_EMPTY;
             TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`] THEN
    MAP_EVERY EXPAND_TAC ["a'"; "b'"; "c'"] THEN
    SIMP_TAC[MIDPOINTS_IN_CONVEX_HULL; POINTS_IN_CONVEX_HULL; IN_INSERT];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `e * (K / &2) pow 2 = (e * K pow 2) / &4`] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP NORM_SUM_LEMMA) THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`a:complex`; `c':complex`; `b':complex`];
    MAP_EVERY EXISTS_TAC [`a':complex`; `c':complex`; `b:complex`];
    MAP_EVERY EXISTS_TAC [`a':complex`; `c:complex`; `b':complex`];
    MAP_EVERY EXISTS_TAC [`a':complex`; `b':complex`; `c':complex`]] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXPAND_TAC ["a'"; "b'"; "c'"] THEN
  SIMP_TAC[MIDPOINTS_IN_CONVEX_HULL; POINTS_IN_CONVEX_HULL; IN_INSERT] THEN
  REWRITE_TAC[midpoint; dist; GSYM VECTOR_SUB_LDISTRIB;
              VECTOR_ARITH `a - inv(&2) % (a + b) = inv(&2) % (a - b)`;
              VECTOR_ARITH `inv(&2) % (c + a) - a = inv(&2) % (c - a)`;
              VECTOR_ARITH `(a + b) - (c + a) = b - c`;
              VECTOR_ARITH `(b + c) - (c + a) = b - a`] THEN
  SIMP_TAC[NORM_MUL; REAL_ARITH `abs(inv(&2)) * x <= k / &2 <=> x <= k`] THEN
  ASM_REWRITE_TAC[GSYM dist] THEN ASM_MESON_TAC[DIST_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Yet at small enough scales this cannot be the case.                       *)
(* ------------------------------------------------------------------------- *)

let TRIANGLE_POINTS_CLOSER = prove
 (`!a b c x y:real^N.
        x IN convex hull {a,b,c} /\
        y IN convex hull {a,b,c}
        ==> norm(x - y) <= norm(a - b) \/
            norm(x - y) <= norm(b - c) \/
            norm(x - y) <= norm(c - a)`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `{a:real^N,b,c}` SIMPLEX_EXTREMAL_LE) THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_RULES; NOT_INSERT_EMPTY] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `y:real^N`]) THEN
  ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
  ASM_MESON_TAC[NORM_POS_LE; REAL_LE_TRANS; NORM_SUB]);;

let HOLOMORPHIC_POINT_SMALL_TRIANGLE = prove
 (`!f s x e.
        x IN s /\ f continuous_on s /\
        f complex_differentiable (at x within s) /\
        &0 < e
        ==> ?k. &0 < k /\
                !a b c. dist(a,b) <= k /\ dist(b,c) <= k /\ dist(c,a) <= k /\
                        x IN convex hull {a,b,c} /\ convex hull {a,b,c} SUBSET s
                        ==> norm(path_integral(linepath(a,b)) f +
                                 path_integral(linepath(b,c)) f +
                                 path_integral(linepath(c,a)) f)
                            <= e * (dist(a,b) + dist(b,c) + dist(c,a)) pow 2`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [complex_differentiable]) THEN
  DISCH_THEN(X_CHOOSE_THEN `f':complex` MP_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [has_complex_derivative] THEN
  REWRITE_TAC[HAS_DERIVATIVE_WITHIN_ALT] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real` o CONJUNCT2) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [TAUT `a /\ b ==> c <=> b ==> a ==> c`] THEN
  REWRITE_TAC[APPROACHABLE_LT_LE] THEN
  ONCE_REWRITE_TAC[TAUT `b ==> a ==> c <=> a /\ b ==> c`] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[dist] THEN
  MAP_EVERY X_GEN_TAC [`a:complex`; `b:complex`; `c:complex`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `path_integral (linepath(a,b)) f +
    path_integral (linepath(b,c)) f +
    path_integral (linepath(c,a)) f =
    path_integral (linepath(a,b)) (\y. f y - f x - f' * (y - x)) +
    path_integral (linepath(b,c)) (\y. f y - f x - f' * (y - x)) +
    path_integral (linepath(c,a)) (\y. f y - f x - f' * (y - x))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `path_integral (linepath(a,b)) (\y. f y - f x - f' * (y - x)) =
      path_integral (linepath(a,b)) f -
      path_integral (linepath(a,b)) (\y. f x + f' * (y - x)) /\
      path_integral (linepath(b,c)) (\y. f y - f x - f' * (y - x)) =
      path_integral (linepath(b,c)) f -
      path_integral (linepath(b,c)) (\y. f x + f' * (y - x)) /\
      path_integral (linepath(c,a)) (\y. f y - f x - f' * (y - x)) =
      path_integral (linepath(c,a)) f -
      path_integral (linepath(c,a)) (\y. f x + f' * (y - x))`
    (REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[SIMPLE_COMPLEX_ARITH `a - b - c = a - (b + c)`] THEN
      REPEAT CONJ_TAC THEN MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
      MATCH_MP_TAC HAS_PATH_INTEGRAL_SUB THEN
      CONJ_TAC THEN MATCH_MP_TAC HAS_PATH_INTEGRAL_INTEGRAL THEN
      MATCH_MP_TAC PATH_INTEGRABLE_CONTINUOUS_LINEPATH THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `s:complex->bool` THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_ADD; CONTINUOUS_ON_CONST;
                   CONTINUOUS_ON_COMPLEX_MUL; CONTINUOUS_ON_SUB] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `convex hull {a:complex,b,c}` THEN
      ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
      MATCH_MP_TAC CONVEX_HULL_SUBSET THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[MIDPOINTS_IN_CONVEX_HULL; POINTS_IN_CONVEX_HULL; IN_INSERT];
      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_RING
     `x + y + z = (x - x') + (y - y') + (z - z') <=>
      x' + y' + z' = Cx(&0)`] THEN
    MP_TAC(ISPECL [`a:complex`; `b:complex`; `c:complex`;
                   `f':complex`; `f x - f' * x`]
           TRIANGLE_LINEAR_HAS_CHAIN_INTEGRAL) THEN
    REWRITE_TAC[COMPLEX_RING
     `f' * x' + f x - f' * x = f x + f' * (x' - x)`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP HAS_CHAIN_INTEGRAL_CHAIN_INTEGRAL) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[NORM_SUB] THEN MATCH_MP_TAC(REAL_ARITH
   `&0 <= x * y /\ &0 <= x * z /\ &0 <= y * z /\
    a <= (e * (x + y + z)) * x +
         (e * (x + y + z)) * y +
         (e * (x + y + z)) * z
    ==> a <= e * (x + y + z) pow 2`) THEN
  SIMP_TAC[REAL_LE_MUL; NORM_POS_LE] THEN
  REPEAT(MATCH_MP_TAC NORM_TRIANGLE_LE THEN
         MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC) THEN
  (MATCH_MP_TAC HAS_PATH_INTEGRAL_BOUND_LINEPATH THEN
   EXISTS_TAC `\y:complex. f y - f x - f' * (y - x)` THEN
   ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_ADD; REAL_LT_IMP_LE; NORM_POS_LE] THEN
   CONJ_TAC THENL
    [MATCH_MP_TAC HAS_PATH_INTEGRAL_INTEGRAL THEN
     MATCH_MP_TAC PATH_INTEGRABLE_CONTINUOUS_LINEPATH THEN
     MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:complex->bool` THEN
     ASM_SIMP_TAC[CONTINUOUS_ON_SUB; ETA_AX; CONTINUOUS_ON_COMPLEX_MUL;
                 CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
     MATCH_MP_TAC SUBSET_TRANS THEN
     EXISTS_TAC `convex hull {a:complex,b,c}` THEN
     ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
     MATCH_MP_TAC CONVEX_HULL_SUBSET THEN
     REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
     ASM_SIMP_TAC[MIDPOINTS_IN_CONVEX_HULL; POINTS_IN_CONVEX_HULL; IN_INSERT];
     ALL_TAC] THEN
   X_GEN_TAC `y:complex` THEN STRIP_TAC THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `e * norm(y - x:complex)` THEN CONJ_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
      [MATCH_MP_TAC(SET_RULE `!t. y IN t /\ t SUBSET s ==> y IN s`) THEN
       EXISTS_TAC `convex hull {a:complex,b,c}` THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC(REAL_ARITH
        `!n1 n2 n3. n1 <= d /\ n2 <= d /\ n3 <= d /\
                    (n <= n1 \/ n <= n2 \/ n <= n3)
                    ==> n <= d`) THEN
       MAP_EVERY EXISTS_TAC
        [`norm(a - b:complex)`; `norm(b - c:complex)`;
         `norm(c - a:complex)`] THEN
       ASM_REWRITE_TAC[] THEN MATCH_MP_TAC TRIANGLE_POINTS_CLOSER];
     ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
     ONCE_REWRITE_TAC[NORM_SUB] THEN
     MATCH_MP_TAC(REAL_ARITH
      `(x <= a \/ x <= b \/ x <= c) /\ (&0 <= a /\ &0 <= b /\ &0 <= c)
       ==> x <= a + b + c`) THEN
     REWRITE_TAC[NORM_POS_LE] THEN MATCH_MP_TAC TRIANGLE_POINTS_CLOSER THEN
     ASM_REWRITE_TAC[]] THEN
    REPEAT CONJ_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `x IN s ==> s SUBSET t ==> x IN t`)) THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC CONVEX_HULL_SUBSET THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[MIDPOINTS_IN_CONVEX_HULL; POINTS_IN_CONVEX_HULL;
                 IN_INSERT]));;

(* ------------------------------------------------------------------------- *)
(* Hence the most basic theorem for a triangle.                              *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_THEOREM_TRIANGLE = prove
 (`!f s a b c.
        f holomorphic_on (convex hull {a,b,c})
        ==> (f has_path_integral Cx(&0))
            (linepath(a,b) ++ linepath(b,c) ++ linepath(c,a))`,
  let lemma1 = prove
   (`!P Q abc.
          P abc 0 /\
          (!abc:A n. P abc n ==> ?abc'. P abc' (SUC n) /\ Q abc' abc)
          ==> ?ABC. ABC 0 = abc /\ !n. P (ABC n) n /\ Q (ABC(SUC n)) (ABC n)`,
    REPEAT STRIP_TAC THEN
    (MP_TAC o prove_recursive_functions_exist num_RECURSION)
      `ABC 0 = abc:A /\
       !n. ABC(SUC n) = @abc. P abc (SUC n) /\ Q abc (ABC n)` THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    STRIP_TAC THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[FORALL_AND_THM] THEN
    MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]) in
  let lemma3 = prove
   (`!P Q a:A b:A c:A.
          P a b c 0 /\
          (!a b c n. P a b c n
                     ==> ?a' b' c'. P a' b' c' (SUC n) /\ Q a' b' c' a b c)
          ==> ?A B C. A 0 = a /\ B 0 = b /\ C 0 = c /\
                      !n. P (A n) (B n) (C n) n /\
                          Q (A(SUC n)) (B(SUC n)) (C(SUC n)) (A n) (B n) (C n)`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL
     [`\(a,b,c). (P:A->A->A->num->bool) a b c`;
      `\(a,b,c) (a',b',c'). (Q:A->A->A->A->A->A->bool) a b c a' b' c'`;
      `(a:A,b:A,c:A)`]
          lemma1) THEN
    REWRITE_TAC[FORALL_PAIR_THM; EXISTS_PAIR_THM] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ABC:num->A#A#A` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC
     [`(\(a,b,c). a) o (ABC:num->A#A#A)`;
      `(\(a,b,c). b) o (ABC:num->A#A#A)`;
      `(\(a,b,c). c) o (ABC:num->A#A#A)`] THEN
    REWRITE_TAC[o_THM] THEN
    REPEAT(CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    SPEC_TAC(`(ABC:num->A#A#A) (SUC n)`,`y:A#A#A`) THEN
    SPEC_TAC(`(ABC:num->A#A#A) n`,`x:A#A#A`) THEN
    REWRITE_TAC[FORALL_PAIR_THM]) in
  REPEAT STRIP_TAC THEN
  STRIP_ASSUME_TAC(ISPECL [`a:complex`; `b:complex`; `c:complex`]
                SEGMENTS_SUBSET_CONVEX_HULL) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOLOMORPHIC_ON_IMP_CONTINUOUS_ON) THEN
  SUBGOAL_THEN
   `f path_integrable_on (linepath(a,b) ++ linepath(b,c) ++ linepath(c,a))`
  MP_TAC THENL
   [SIMP_TAC[PATH_INTEGRABLE_JOIN; VALID_PATH_JOIN; VALID_PATH_LINEPATH;
             PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
             PATHFINISH_LINEPATH] THEN
    ASM_MESON_TAC[PATH_INTEGRABLE_CONTINUOUS_LINEPATH; CONTINUOUS_ON_SUBSET];
    ALL_TAC] THEN
  SIMP_TAC[path_integrable_on] THEN DISCH_THEN(X_CHOOSE_TAC `y:complex`) THEN
  ASM_CASES_TAC `y = Cx(&0)` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `K = &1 + max (dist(a:complex,b)) (max (dist(b,c)) (dist(c,a)))` THEN
  SUBGOAL_THEN `&0 < K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &1 + x`) THEN
    REWRITE_TAC[REAL_LE_MAX; DIST_POS_LE];
    ALL_TAC] THEN
  ABBREV_TAC `e = norm(y:complex) / K pow 2` THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_POW_LT; COMPLEX_NORM_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?A B C. A 0 = a /\ B 0 = b /\ C 0 = c /\
            !n. (convex hull {A n,B n,C n} SUBSET convex hull {a,b,c} /\
                 dist(A n,B n) <= K / &2 pow n /\
                 dist(B n,C n) <= K / &2 pow n /\
                 dist(C n,A n) <= K / &2 pow n /\
                 norm(path_integral(linepath (A n,B n)) f +
                      path_integral(linepath (B n,C n)) f +
                      path_integral(linepath (C n,A n)) f) >=
                 e * (K / &2 pow n) pow 2) /\
                convex hull {A(SUC n),B(SUC n),C(SUC n)} SUBSET
                convex hull {A n,B n,C n}`
  MP_TAC THENL
   [MATCH_MP_TAC lemma3 THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[real_pow; REAL_DIV_1; CONJ_ASSOC; SUBSET_REFL] THEN
      CONJ_TAC THENL [EXPAND_TAC "K" THEN REAL_ARITH_TAC; ALL_TAC] THEN
      EXPAND_TAC "e" THEN
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_POW_LT] THEN
      MATCH_MP_TAC(REAL_ARITH `x = y ==> x >= y`) THEN AP_TERM_TAC THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o
        MATCH_MP HAS_CHAIN_INTEGRAL_CHAIN_INTEGRAL) THEN
      REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC
     [`a':complex`; `b':complex`; `c':complex`; `n:num`] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`f:complex->complex`; `a':complex`; `b':complex`;
       `c':complex`; `e:real`; `K / &2 pow n`]
       CAUCHY_THEOREM_QUADRISECTION) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[real_pow; REAL_FIELD `x / (&2 * y) = x / y / &2`] THEN
    MATCH_MP_TAC(SET_RULE
     `s SUBSET t /\ t SUBSET u ==> s SUBSET u /\ s SUBSET t`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONVEX_HULL_SUBSET THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?x:complex. !n:num. x IN convex hull {A n,B n,C n}`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC BOUNDED_CLOSED_NEST THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED;
      REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY];
      MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[SUBSET_REFL; SUBSET_TRANS];
      MATCH_MP_TAC COMPACT_IMP_BOUNDED] THEN
    MATCH_MP_TAC FINITE_IMP_COMPACT_CONVEX_HULL THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_RULES];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:complex->complex`; `convex hull {a:complex,b,c}`;
                 `x:complex`; `e / &10`] HOLOMORPHIC_POINT_SMALL_TRIANGLE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON; complex_differentiable] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    ASM_MESON_TAC[holomorphic_on; SUBSET];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `K:real / k` REAL_ARCH_POW2) THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM REAL_LT_LDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN FIRST_X_ASSUM(MP_TAC o SPECL
   [`(A:num->complex) n`; `(B:num->complex) n`; `(C:num->complex) n`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TRANS; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[REAL_NOT_LE] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `e * (K / &2 pow n) pow 2` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[GSYM real_ge]] THEN
  ASM_SIMP_TAC[real_div; GSYM REAL_MUL_ASSOC; REAL_LT_LMUL_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 < x /\ y <= &9 * x ==> inv(&10) * y < x`) THEN
  ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_MUL; REAL_LT_INV_EQ;
                REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[REAL_ARITH `&9 * x pow 2 = (&3 * x) pow 2`] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN
  SIMP_TAC[REAL_LE_ADD; DIST_POS_LE; GSYM real_div] THEN
  MATCH_MP_TAC(REAL_ARITH
   `x <= a /\ y <= a /\ z <= a ==> x + y + z <= &3 * a`) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Version needing function holomorphic in interior only.                    *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_THEOREM_FLAT_LEMMA = prove
 (`!f a b c k.
        f continuous_on convex hull {a,b,c} /\ c - a = k % (b - a) /\ &0 <= k
        ==> path_integral (linepath(a,b)) f +
            path_integral (linepath(b,c)) f +
            path_integral (linepath(c,a)) f = Cx(&0)`,
  REPEAT STRIP_TAC THEN
  STRIP_ASSUME_TAC(ISPECL [`a:complex`; `b:complex`; `c:complex`]
                SEGMENTS_SUBSET_CONVEX_HULL) THEN
  ASM_CASES_TAC `k <= &1` THENL
   [MP_TAC(SPECL [`f:complex->complex`; `a:complex`; `b:complex`; `c:complex`;
                  `k:real`] PATH_INTEGRAL_SPLIT) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC(COMPLEX_RING
     `x = --b /\ y = --a ==> (x + y) + (a + b) = Cx(&0)`) THEN
    CONJ_TAC THEN MATCH_MP_TAC PATH_INTEGRAL_SWAP THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    MP_TAC(SPECL [`f:complex->complex`; `a:complex`; `c:complex`; `b:complex`;
                  `inv k:real`] PATH_INTEGRAL_SPLIT) THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_LE_INV_EQ; REAL_MUL_LINV; REAL_INV_LE_1;
      VECTOR_MUL_LID; REAL_ARITH `~(k <= &1) ==> ~(k = &0) /\ &1 <= k`] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC(COMPLEX_RING
     `ac = --ca ==> ac = ab + bc ==> ab + bc + ca = Cx(&0)`) THEN
    MATCH_MP_TAC PATH_INTEGRAL_SWAP THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]]);;

let CAUCHY_THEOREM_FLAT = prove
 (`!f a b c k.
        f continuous_on convex hull {a,b,c} /\ c - a = k % (b - a)
        ==> path_integral (linepath(a,b)) f +
            path_integral (linepath(b,c)) f +
            path_integral (linepath(c,a)) f = Cx(&0)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&0 <= k` THENL
   [ASM_MESON_TAC[CAUCHY_THEOREM_FLAT_LEMMA]; ALL_TAC] THEN
  STRIP_ASSUME_TAC(ISPECL [`a:complex`; `b:complex`; `c:complex`]
                SEGMENTS_SUBSET_CONVEX_HULL) THEN
  MP_TAC(ISPECL [`f:complex->complex`; `b:complex`; `a:complex`; `c:complex`;
                 `&1 - k`] CAUCHY_THEOREM_FLAT_LEMMA) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[INSERT_AC; REAL_ARITH `~(&0 <= k) ==> &0 <= &1 - k`;
         VECTOR_ARITH `b - a = k % (c - a) ==> (b - c) = (&1 - k) % (a - c)`];
    ALL_TAC] THEN
  MATCH_MP_TAC(COMPLEX_RING
     `ab = --ba /\ ac = --ca /\ bc = --cb
      ==> ba + ac + cb = Cx(&0) ==> ab + bc + ca = Cx(&0)`) THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC PATH_INTEGRAL_SWAP THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]);;

let CAUCHY_THEOREM_TRIANGLE_INTERIOR = prove
 (`!f a b c.
        f continuous_on (convex hull {a,b,c}) /\
        f holomorphic_on interior (convex hull {a,b,c})
        ==> (f has_path_integral Cx(&0))
            (linepath(a,b) ++ linepath(b,c) ++ linepath(c,a))`,
  REPEAT STRIP_TAC THEN
  STRIP_ASSUME_TAC(ISPECL [`a:complex`; `b:complex`; `c:complex`]
                SEGMENTS_SUBSET_CONVEX_HULL) THEN
  SUBGOAL_THEN
    `?B. &0 < B /\
         !y. y IN IMAGE (f:complex->complex) (convex hull {a,b,c})
             ==> norm(y) <= B`
  MP_TAC THENL
   [REWRITE_TAC[GSYM BOUNDED_POS] THEN MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[FINITE_IMP_COMPACT_CONVEX_HULL; FINITE_INSERT; FINITE_RULES];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN STRIP_TAC] THEN
  SUBGOAL_THEN
    `?C. &0 < C /\ !x:complex. x IN convex hull {a,b,c} ==> norm(x) <= C`
  MP_TAC THENL
   [REWRITE_TAC[GSYM BOUNDED_POS] THEN
    MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
    ASM_SIMP_TAC[FINITE_IMP_COMPACT_CONVEX_HULL; FINITE_INSERT; FINITE_RULES];
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `(f:complex->complex) uniformly_continuous_on (convex hull {a,b,c})`
  MP_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIFORMLY_CONTINUOUS THEN
    ASM_SIMP_TAC[FINITE_IMP_COMPACT_CONVEX_HULL; FINITE_RULES; FINITE_INSERT];
    ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `f path_integrable_on
    (linepath (a,b) ++ linepath(b,c) ++ linepath(c,a))`
  MP_TAC THENL
   [SIMP_TAC[PATH_INTEGRABLE_JOIN; VALID_PATH_JOIN; VALID_PATH_LINEPATH;
             PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
             PATHFINISH_LINEPATH] THEN
    ASM_MESON_TAC[PATH_INTEGRABLE_CONTINUOUS_LINEPATH; CONTINUOUS_ON_SUBSET];
    ALL_TAC] THEN
  SIMP_TAC[path_integrable_on] THEN DISCH_THEN(X_CHOOSE_TAC `y:complex`) THEN
  ASM_CASES_TAC `y = Cx(&0)` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `~(y = Cx(&0))` THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o SYM o MATCH_MP
     HAS_CHAIN_INTEGRAL_CHAIN_INTEGRAL) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `c:complex = a` THENL
   [MATCH_MP_TAC CAUCHY_THEOREM_FLAT THEN
    EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_SUB_EQ];
    ALL_TAC] THEN
  ASM_CASES_TAC `b:complex = c` THENL
   [ONCE_REWRITE_TAC[COMPLEX_RING `a + b + c:complex = c + a + b`] THEN
    MATCH_MP_TAC CAUCHY_THEOREM_FLAT THEN
    EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_SUB_EQ] THEN
    ASM_MESON_TAC[INSERT_AC];
    ALL_TAC] THEN
  ASM_CASES_TAC `a:complex = b` THENL
   [ONCE_REWRITE_TAC[COMPLEX_RING `a + b + c:complex = b + c + a`] THEN
    MATCH_MP_TAC CAUCHY_THEOREM_FLAT THEN
    EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_SUB_EQ] THEN
    ASM_MESON_TAC[INSERT_AC];
    ALL_TAC] THEN
  ASM_CASES_TAC `interior(convex hull {a:complex,b,c}) = {}` THENL
   [MATCH_MP_TAC CAUCHY_THEOREM_FLAT THEN
    SUBGOAL_THEN `{a:complex,b,c} HAS_SIZE (dimindex(:2) + 1)`
    MP_TAC THENL
     [ASM_SIMP_TAC[HAS_SIZE; CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
      ASM_REWRITE_TAC[DIMINDEX_2; ARITH; IN_INSERT; NOT_IN_EMPTY];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP INTERIOR_CONVEX_HULL_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `collinear{a:complex,b,c}` MP_TAC THENL
     [ASM_REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {b,a,c}`] THEN
    ONCE_REWRITE_TAC[COLLINEAR_3] THEN
    ASM_REWRITE_TAC[COLLINEAR_LEMMA; VECTOR_SUB_EQ];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `d:complex`) THEN FIRST_X_ASSUM(MP_TAC o SYM) THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `y = Cx(&0)` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `norm(y:complex) / &24 / C`) THEN
  SUBGOAL_THEN `&0 < norm(y:complex) / &24 / C` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH; NORM_POS_LE; REAL_LTE_ADD;
                 COMPLEX_NORM_NZ; COMPLEX_SUB_0];
    ASM_REWRITE_TAC[dist]] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN ABBREV_TAC
   `e = min (&1)
            (min (d1 / (&4 * C))
                 ((norm(y:complex) / &24 / C) / B))` THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN
    ASM_SIMP_TAC[REAL_HALF; REAL_LT_MIN; REAL_LT_DIV; COMPLEX_NORM_NZ;
                 REAL_LT_MUL; REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  ABBREV_TAC `shrink = \x:complex. x - e % (x - d)` THEN
  SUBGOAL_THEN `shrink (a:complex) IN interior(convex hull {a,b,c}) /\
                shrink b IN interior(convex hull {a,b,c}) /\
                shrink c IN interior(convex hull {a,b,c})`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN EXPAND_TAC "shrink" THEN
    MATCH_MP_TAC IN_INTERIOR_CONVEX_SHRINK THEN
    ASM_REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
    (CONJ_TAC THENL [ALL_TAC; EXPAND_TAC "e" THEN REAL_ARITH_TAC]) THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN
    REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm((path_integral(linepath(shrink a,shrink b)) f -
          path_integral(linepath(a,b)) f) +
         (path_integral(linepath(shrink b,shrink c)) f -
          path_integral(linepath(b,c)) f) +
         (path_integral(linepath(shrink c,shrink a)) f -
          path_integral(linepath(c,a)) f)) <= norm(y:complex) / &2`
  MP_TAC THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[COMPLEX_RING
     `(ab' - ab) + (bc' - bc) + (ca' - ca) =
      (ab' + bc' + ca') - (ab + bc + ca)`] THEN
    SUBGOAL_THEN
     `(f has_path_integral (Cx(&0)))
      (linepath (shrink a,shrink b) ++
       linepath (shrink b,shrink c) ++
       linepath (shrink c,shrink (a:complex)))`
    MP_TAC THENL
     [MATCH_MP_TAC CAUCHY_THEOREM_TRIANGLE THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
      EXISTS_TAC `interior(convex hull {a:complex,b,c})` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MINIMAL THEN
      SIMP_TAC[CONVEX_INTERIOR; CONVEX_CONVEX_HULL] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP HAS_CHAIN_INTEGRAL_CHAIN_INTEGRAL) THEN
    SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[COMPLEX_SUB_LZERO; NORM_NEG] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= y /\ ~(y = &0) ==> ~(y <= y / &2)`) THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_ZERO; NORM_POS_LE]] THEN
  SUBGOAL_THEN
   `!x y. x IN convex hull {a,b,c} /\ y IN convex hull {a,b,c}
          ==> norm(x - y) <= &2 * C`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_MUL_2; VECTOR_SUB] THEN
    MATCH_MP_TAC NORM_TRIANGLE_LE THEN REWRITE_TAC[NORM_NEG] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `x / &2 = x / &6 + x / &6 + x / &6`] THEN
  REPEAT(MATCH_MP_TAC NORM_TRIANGLE_LE THEN
         MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC) THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM CONTENT_UNIT_1] THEN
  MATCH_MP_TAC HAS_INTEGRAL_BOUND THENL
   [EXISTS_TAC `\x. f(linepath(shrink a,shrink b) x) *
                    (shrink b - shrink a) -
                    f(linepath(a,b) x) * (b - a)`;
    EXISTS_TAC `\x. f(linepath(shrink b,shrink c) x) *
                    (shrink c - shrink b) -
                    f(linepath(b,c) x) * (c - b)`;
    EXISTS_TAC `\x. f(linepath(shrink c,shrink a) x) *
                    (shrink a - shrink c) -
                    f(linepath(c,a) x) * (a - c)`] THEN
  ASM_SIMP_TAC[COMPLEX_NORM_NZ; REAL_ARITH `&0 < x ==> &0 <= x / &6`] THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC HAS_INTEGRAL_SUB THEN
     REWRITE_TAC[GSYM HAS_PATH_INTEGRAL_LINEPATH] THEN
     CONJ_TAC THEN MATCH_MP_TAC HAS_PATH_INTEGRAL_INTEGRAL THEN
     MATCH_MP_TAC PATH_INTEGRABLE_CONTINUOUS_LINEPATH THEN
     MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
     EXISTS_TAC `convex hull {a:complex,b,c}` THEN
     ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
     MATCH_MP_TAC HULL_MINIMAL THEN
     REWRITE_TAC[CONVEX_CONVEX_HULL; SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN
     ASM_MESON_TAC[SUBSET; INTERIOR_SUBSET];
     ALL_TAC] THEN
   REPEAT STRIP_TAC THEN
   ONCE_REWRITE_TAC[COMPLEX_RING
    `f' * x' - f * x = f' * (x' - x) + x * (f' - f):complex`] THEN
   MATCH_MP_TAC NORM_TRIANGLE_LE THEN REWRITE_TAC[COMPLEX_NORM_MUL] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `B * (norm(y:complex) / &24 / C / B) * &2 * C +
               (&2 * C) * (norm y / &24 / C)` THEN
   CONJ_TAC THENL
    [ALL_TAC;
     MATCH_MP_TAC REAL_EQ_IMP_LE THEN
     MAP_EVERY UNDISCH_TAC [`&0 < B`; `&0 < C`] THEN CONV_TAC REAL_FIELD] THEN
   MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
   MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THENL
    [CONJ_TAC THENL
      [FIRST_X_ASSUM MATCH_MP_TAC THEN
       W(fun (asl,w) ->
         MP_TAC(PART_MATCH (lhand o rand) LINEPATH_IN_PATH (lhand w))) THEN
       ASM_REWRITE_TAC[] THEN
       W(fun (asl,w) -> SPEC_TAC(lhand(rand w),`x:complex`)) THEN
       REWRITE_TAC[GSYM SUBSET; SEGMENT_CONVEX_HULL] THEN
       MATCH_MP_TAC HULL_MINIMAL THEN
       REWRITE_TAC[CONVEX_CONVEX_HULL; SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN
       ASM_MESON_TAC[SUBSET; INTERIOR_SUBSET];
       ALL_TAC] THEN
     EXPAND_TAC "shrink" THEN
     REWRITE_TAC[VECTOR_ARITH `(b - e % (b - d)) - (a - e % (a - d)) -
                           (b - a) = e % (a - b)`] THEN
     REWRITE_TAC[NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
     ASM_SIMP_TAC[NORM_POS_LE; REAL_ARITH `&0 < x ==> abs x = x`;
                  REAL_ABS_POS] THEN
     CONJ_TAC THENL [EXPAND_TAC "e" THEN REAL_ARITH_TAC; ALL_TAC] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THEN
     MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN
     REWRITE_TAC[IN_INSERT];
     ALL_TAC] THEN
   CONJ_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THEN
     MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN
     REWRITE_TAC[IN_INSERT];
     ALL_TAC] THEN
   MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   CONJ_TAC THENL
    [W(fun (asl,w) ->
       MP_TAC(PART_MATCH (lhand o rand) LINEPATH_IN_PATH (lhand w))) THEN
     ASM_MESON_TAC[SUBSET];
     ALL_TAC] THEN
   CONJ_TAC THENL
    [W(fun (asl,w) ->
       MP_TAC(PART_MATCH (lhand o rand) LINEPATH_IN_PATH (lhand w))) THEN
     ASM_REWRITE_TAC[] THEN
     W(fun (asl,w) -> SPEC_TAC(lhand(rand w),`x:complex`)) THEN
     REWRITE_TAC[GSYM SUBSET; SEGMENT_CONVEX_HULL] THEN
     MATCH_MP_TAC HULL_MINIMAL THEN
     REWRITE_TAC[CONVEX_CONVEX_HULL; SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN
     ASM_MESON_TAC[SUBSET; INTERIOR_SUBSET];
     ALL_TAC] THEN
   REWRITE_TAC[linepath] THEN REWRITE_TAC[VECTOR_ARITH
     `((&1 - x) % a' + x % b') - ((&1 - x) % a + x % b) =
      (&1 - x) % (a' - a) + x % (b' - b)`] THEN
   EXPAND_TAC "shrink" THEN REWRITE_TAC[VECTOR_ARITH `a - b - a = --b`] THEN
   MATCH_MP_TAC NORM_TRIANGLE_LT THEN REWRITE_TAC[NORM_MUL; NORM_NEG] THEN
   MATCH_MP_TAC REAL_CONVEX_BOUND_LT THEN ONCE_REWRITE_TAC[TAUT
    `a /\ b /\ c /\ d /\ e <=> (c /\ d /\ e) /\ a /\ b`] THEN
   CONJ_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
     REWRITE_TAC[DROP_VEC] THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
   CONJ_TAC THEN
   MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `e * &2 * C` THEN
   ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_ARITH `&0 < x ==> abs x = x`] THEN
   (CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[SUBSET; INTERIOR_SUBSET; HULL_SUBSET; IN_INSERT];
      ALL_TAC]) THEN
   ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
   EXPAND_TAC "e" THEN REWRITE_TAC[REAL_MIN_LT] THEN
   DISJ2_TAC THEN DISJ1_TAC THEN
   REWRITE_TAC[REAL_FIELD `d / (a * b) = inv(a:real) * d / b`] THEN
   REWRITE_TAC[REAL_ARITH `inv(&4) * x < inv(&2) * x <=> &0 < x`] THEN
   ASM_SIMP_TAC[REAL_LT_DIV]));;

(* ------------------------------------------------------------------------- *)
(* Version allowing finite number of exceptional points.                     *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_THEOREM_TRIANGLE_COFINITE = prove
 (`!f s a b c.
        f continuous_on (convex hull {a,b,c}) /\
        FINITE s /\
        (!x. x IN interior(convex hull {a,b,c}) DIFF s
             ==> f complex_differentiable (at x))
        ==> (f has_path_integral Cx(&0))
            (linepath (a,b) ++ linepath(b,c) ++ linepath(c,a))`,
  GEN_TAC THEN GEN_TAC THEN WF_INDUCT_TAC `CARD(s:complex->bool)` THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:complex->bool = {}` THENL
   [MATCH_MP_TAC CAUCHY_THEOREM_TRIANGLE_INTERIOR THEN
    ASM_REWRITE_TAC[holomorphic_on] THEN X_GEN_TAC `z:complex` THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN
    ASM_REWRITE_TAC[complex_differentiable; IN_DIFF; NOT_IN_EMPTY] THEN
    MESON_TAC[HAS_COMPLEX_DERIVATIVE_AT_WITHIN];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `d:complex`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s DELETE (d:complex)`) THEN
  ASM_SIMP_TAC[CARD_DELETE; CARD_EQ_0;
                 ARITH_RULE `n - 1 < n <=> ~(n = 0)`] THEN
  ASM_CASES_TAC `(d:complex) IN convex hull {a,b,c}` THENL
   [ALL_TAC;
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[FINITE_DELETE; IN_DIFF; IN_DELETE] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_DIFF] THEN ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]] THEN
  DISCH_TAC THEN SUBGOAL_THEN
   `(f has_path_integral Cx(&0))
    (linepath(a,b) ++ linepath(b,d) ++ linepath(d,a)) /\
    (f has_path_integral Cx(&0))
    (linepath(b,c) ++ linepath(c,d) ++ linepath(d,b)) /\
    (f has_path_integral Cx(&0))
    (linepath(c,a) ++ linepath(a,d) ++ linepath(d,c))`
  MP_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM]) THEN
    REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[FINITE_DELETE] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
       EXISTS_TAC `convex hull {a:complex,b,c}` THEN ASM_REWRITE_TAC[] THEN
       MATCH_MP_TAC CONVEX_HULL_SUBSET THEN
       REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
       REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
       MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN
       REWRITE_TAC[IN_INSERT];
       ALL_TAC]) THEN
    ASM_REWRITE_TAC[FINITE_DELETE; IN_DIFF; IN_DELETE] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [DE_MORGAN_THM]) THEN
    (ASM_CASES_TAC `x:complex = d` THEN ASM_REWRITE_TAC[] THENL
      [ASM_MESON_TAC[NOT_IN_INTERIOR_CONVEX_HULL_3]; ALL_TAC]) THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[IN_DIFF] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `x IN interior s
      ==> interior s SUBSET interior t ==> x IN interior t`)) THEN
    MATCH_MP_TAC SUBSET_INTERIOR THEN
    MATCH_MP_TAC CONVEX_HULL_SUBSET THEN
    SIMP_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `f path_integrable_on
    (linepath (a,b) ++ linepath(b,c) ++ linepath(c,a))`
  MP_TAC THENL
   [SIMP_TAC[PATH_INTEGRABLE_JOIN; VALID_PATH_JOIN; VALID_PATH_LINEPATH;
             PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
             PATHFINISH_LINEPATH] THEN
    STRIP_ASSUME_TAC(ISPECL [`a:complex`; `b:complex`; `c:complex`]
                  SEGMENTS_SUBSET_CONVEX_HULL) THEN
    ASM_MESON_TAC[PATH_INTEGRABLE_CONTINUOUS_LINEPATH; CONTINUOUS_ON_SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[path_integrable_on; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `y:complex` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN
   (MP_TAC o MATCH_MP HAS_CHAIN_INTEGRAL_CHAIN_INTEGRAL)) THEN
  ASM_CASES_TAC `y = Cx(&0)` THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[]; UNDISCH_TAC `~(y = Cx(&0))`] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `(f:complex->complex) continuous_on segment[a,d] /\
                f continuous_on segment[b,d] /\
                f continuous_on segment[c,d]`
  MP_TAC THENL
   [ALL_TAC;
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (MP_TAC o MATCH_MP
               PATH_INTEGRAL_SWAP)) THEN
    CONV_TAC COMPLEX_RING] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `convex hull {a:complex,b,c}` THEN
  ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
  MATCH_MP_TAC CONVEX_HULL_SUBSET THEN
  SIMP_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN REWRITE_TAC[IN_INSERT]);;

(* ------------------------------------------------------------------------- *)
(* Existence of a primitive.                                                 *)
(* ------------------------------------------------------------------------- *)

let STARLIKE_CONVEX_SUBSET = prove
 (`!s a b c:real^N.
        a IN s /\ segment[b,c] SUBSET s /\
        (!x. x IN s ==> segment[a,x] SUBSET s)
        ==> convex hull {a,b,c} SUBSET s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{b:real^N,c}`; `a:real^N`] CONVEX_HULL_INSERT) THEN
  REWRITE_TAC[NOT_INSERT_EMPTY] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `u:real`; `v:real`; `d:real^N`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `d:real^N`) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[SUBSET; SEGMENT_CONVEX_HULL];
    ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL; CONVEX_HULL_2; IN_ELIM_THM] THEN
    ASM_MESON_TAC[]]);;

let HOLOMORPHIC_STARLIKE_PRIMITIVE = prove
 (`!f s k. open s /\ starlike s /\ FINITE k /\ f continuous_on s /\
           (!x. x IN s DIFF k ==> f complex_differentiable at x)
           ==> ?g. !x. x IN s ==> (g has_complex_derivative f(x)) (at x)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a:complex` STRIP_ASSUME_TAC o
        GEN_REWRITE_RULE I [starlike]) THEN
  EXISTS_TAC `\x. path_integral (linepath(a,x)) f` THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_complex_derivative] THEN
  REWRITE_TAC[has_derivative_at; LINEAR_COMPLEX_MUL] THEN
  MATCH_MP_TAC LIM_TRANSFORM THEN
  EXISTS_TAC `\y. inv(norm(y - x)) % (path_integral(linepath(x,y)) f -
                   f x * (y - x))` THEN
  REWRITE_TAC[VECTOR_ARITH
   `i % (x - a) - i % (y - (z + a)) = i % (x + z - y)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LIM_EVENTUALLY THEN REWRITE_TAC[EVENTUALLY_AT] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
    DISCH_THEN(MP_TAC o SPEC `x:complex`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:complex` THEN REWRITE_TAC[dist] THEN STRIP_TAC THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ2_TAC THEN
    SUBGOAL_THEN `convex hull {a:complex,x,y} SUBSET s` ASSUME_TAC THENL
     [MATCH_MP_TAC STARLIKE_CONVEX_SUBSET THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x:complex,e)` THEN
      ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
      MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_BALL] THEN
      REWRITE_TAC[SUBSET; IN_BALL; IN_INSERT; NOT_IN_EMPTY] THEN
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[dist; NORM_0; VECTOR_SUB_REFL] THEN
      ASM_MESON_TAC[NORM_SUB];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`f:complex->complex`; `k:complex->bool`;
                   `a:complex`; `x:complex`; `y:complex`]
                CAUCHY_THEOREM_TRIANGLE_COFINITE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
      REWRITE_TAC[IN_DIFF] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF] THEN
      ASM_MESON_TAC[SUBSET; INTERIOR_SUBSET];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP HAS_CHAIN_INTEGRAL_CHAIN_INTEGRAL) THEN
    REWRITE_TAC[] THEN
    MP_TAC(SPECL [`f:complex->complex`; `a:complex`; `y:complex`]
              PATH_INTEGRAL_SWAP) THEN
    ANTS_TAC THENL
       [ALL_TAC; REWRITE_TAC[COMPLEX_VEC_0] THEN CONV_TAC COMPLEX_RING] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `s:complex->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `convex hull {a:complex,x,y}` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LIM_AT] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(f:complex->complex) continuous at x` MP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_INTERIOR THEN ASM_MESON_TAC[INTERIOR_OPEN];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at; dist; VECTOR_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:complex`) THEN
  ASM_REWRITE_TAC[SUBSET; IN_BALL; dist] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `y:complex` THEN STRIP_TAC THEN
  SUBGOAL_THEN `f path_integrable_on linepath(x,y)` MP_TAC THENL
   [MATCH_MP_TAC PATH_INTEGRABLE_CONTINUOUS_LINEPATH THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:complex->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x:complex,d2)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
      MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_BALL] THEN
      REWRITE_TAC[SUBSET; IN_BALL; IN_INSERT; NOT_IN_EMPTY] THEN
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[dist; NORM_0; VECTOR_SUB_REFL] THEN
      ASM_MESON_TAC[NORM_SUB];
      ASM_REWRITE_TAC[SUBSET; IN_BALL; dist]];
    ALL_TAC] THEN
  REWRITE_TAC[path_integrable_on; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `z:complex` THEN
  MP_TAC(SPECL [`x:complex`; `y:complex`; `(f:complex->complex) x`]
                HAS_PATH_INTEGRAL_CONST_LINEPATH) THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT2 th) THEN MP_TAC th) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP PATH_INTEGRAL_UNIQUE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_PATH_INTEGRAL_SUB) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_PATH_INTEGRAL_NEG) THEN
  REWRITE_TAC[COMPLEX_NEG_SUB] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `x <= e / &2 /\ &0 < e ==> x < e`) THEN
  ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_BOUND_LINEPATH THEN
  EXISTS_TAC `\w. (f:complex->complex) w - f x` THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> &0 <= e / &2`] THEN
  X_GEN_TAC `w:complex` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[REAL_LET_TRANS; SEGMENT_BOUND]);;

(* ------------------------------------------------------------------------- *)
(* Cauchy's theorem for an open starlike set.                                *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_THEOREM_STARLIKE = prove
 (`!f s k g. open s /\ starlike s /\ FINITE k /\ f continuous_on s /\
             (!x. x IN s DIFF k ==> f complex_differentiable at x) /\
             valid_path g /\ (path_image g) SUBSET s /\
             pathfinish g = pathstart g
             ==> (f has_path_integral Cx(&0)) (g)`,
  MESON_TAC[HOLOMORPHIC_STARLIKE_PRIMITIVE; CAUCHY_THEOREM_PRIMITIVE;
            HAS_COMPLEX_DERIVATIVE_AT_WITHIN]);;

let CAUCHY_THEOREM_STARLIKE_SIMPLE = prove
 (`!f s g. open s /\ starlike s /\ f holomorphic_on s /\
           valid_path g /\ (path_image g) SUBSET s /\
           pathfinish g = pathstart g
           ==> (f has_path_integral Cx(&0)) (g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CAUCHY_THEOREM_STARLIKE THEN
  MAP_EVERY EXISTS_TAC [`s:complex->bool`; `{}:complex->bool`] THEN
  ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON; FINITE_RULES] THEN
  REWRITE_TAC[IN_DIFF; NOT_IN_EMPTY; complex_differentiable] THEN
  ASM_MESON_TAC[HAS_COMPLEX_DERIVATIVE_WITHIN_OPEN; holomorphic_on]);;

(* ------------------------------------------------------------------------- *)
(* For a convex set we can avoid assuming openness and boundary analyticity. *)
(* Split into two pieces since the first is useful for Morera's theorem etc. *)
(* ------------------------------------------------------------------------- *)

let PATHINTEGRAL_CONVEX_PRIMITIVE = prove
 (`!f s. convex s /\ f continuous_on s /\
         (!a b c. a IN s /\ b IN s /\ c IN s
                  ==>  (f has_path_integral Cx(&0))
                       (linepath (a,b) ++ linepath(b,c) ++ linepath(c,a)))
         ==> ?g. !x. x IN s
                     ==> (g has_complex_derivative f(x)) (at x within s)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:complex->bool = {}` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a:complex` STRIP_ASSUME_TAC o
        GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  EXISTS_TAC `\x. path_integral (linepath(a,x)) f` THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_complex_derivative] THEN
  REWRITE_TAC[has_derivative_within; LINEAR_COMPLEX_MUL] THEN
  MATCH_MP_TAC LIM_TRANSFORM THEN
  EXISTS_TAC `\y. inv(norm(y - x)) % (path_integral(linepath(x,y)) f -
                   f x * (y - x))` THEN
  REWRITE_TAC[VECTOR_ARITH
   `i % (x - a) - i % (y - (z + a)) = i % (x + z - y)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LIM_EVENTUALLY THEN REWRITE_TAC[EVENTUALLY_WITHIN] THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
    X_GEN_TAC `y:complex` THEN REWRITE_TAC[dist] THEN STRIP_TAC THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ2_TAC THEN
    SUBGOAL_THEN `convex hull {a:complex,x,y} SUBSET s` ASSUME_TAC THENL
     [MATCH_MP_TAC HULL_MINIMAL THEN ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:complex`; `x:complex`; `y:complex`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP HAS_CHAIN_INTEGRAL_CHAIN_INTEGRAL) THEN
    REWRITE_TAC[] THEN
    MP_TAC(SPECL [`f:complex->complex`; `a:complex`; `y:complex`]
              PATH_INTEGRAL_SWAP) THEN
    ANTS_TAC THENL
       [ALL_TAC; REWRITE_TAC[COMPLEX_VEC_0] THEN CONV_TAC COMPLEX_RING] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `s:complex->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `convex hull {a:complex,x,y}` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LIM_WITHIN] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(f:complex->complex) continuous (at x within s)` MP_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]; ALL_TAC] THEN
  REWRITE_TAC[continuous_within; dist; VECTOR_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:complex` THEN STRIP_TAC THEN
  SUBGOAL_THEN `f path_integrable_on linepath(x,y)` MP_TAC THENL
   [MATCH_MP_TAC PATH_INTEGRABLE_CONTINUOUS_LINEPATH THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:complex->bool` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    MATCH_MP_TAC HULL_MINIMAL THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[path_integrable_on; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `z:complex` THEN
  MP_TAC(SPECL [`x:complex`; `y:complex`; `(f:complex->complex) x`]
                HAS_PATH_INTEGRAL_CONST_LINEPATH) THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT2 th) THEN MP_TAC th) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP PATH_INTEGRAL_UNIQUE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_PATH_INTEGRAL_SUB) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_PATH_INTEGRAL_NEG) THEN
  REWRITE_TAC[COMPLEX_NEG_SUB] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `x <= e / &2 /\ &0 < e ==> x < e`) THEN
  ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_BOUND_LINEPATH THEN
  EXISTS_TAC `\w. (f:complex->complex) w - f x` THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> &0 <= e / &2`] THEN
  X_GEN_TAC `w:complex` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `w IN s ==> s SUBSET t ==> w IN t`)) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    MATCH_MP_TAC HULL_MINIMAL THEN ASM SET_TAC[];
    ALL_TAC] THEN
   ASM_MESON_TAC[REAL_LET_TRANS; SEGMENT_BOUND]);;

let HOLOMORPHIC_CONVEX_PRIMITIVE = prove
 (`!f s k. convex s /\ FINITE k /\ f continuous_on s /\
           (!x. x IN interior(s) DIFF k ==> f complex_differentiable at x)
           ==> ?g. !x. x IN s
                       ==> (g has_complex_derivative f(x)) (at x within s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PATHINTEGRAL_CONVEX_PRIMITIVE THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CAUCHY_THEOREM_TRIANGLE_COFINITE THEN
  EXISTS_TAC `k:complex->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:complex->bool` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `w:complex` THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
    SPEC_TAC(`w:complex`,`w:complex`) THEN ASM_REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> (s DIFF k) SUBSET (t DIFF k)`) THEN
    MATCH_MP_TAC SUBSET_INTERIOR] THEN
  MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let CAUCHY_THEOREM_CONVEX = prove
 (`!f s k g. convex s /\ FINITE k /\ f continuous_on s /\
             (!x. x IN interior(s) DIFF k ==> f complex_differentiable at x) /\
             valid_path g /\ (path_image g) SUBSET s /\
             pathfinish g = pathstart g
             ==> (f has_path_integral Cx(&0)) (g)`,
  MESON_TAC[HOLOMORPHIC_CONVEX_PRIMITIVE; CAUCHY_THEOREM_PRIMITIVE]);;

let CAUCHY_THEOREM_CONVEX_SIMPLE = prove
 (`!f s g. convex s /\ f holomorphic_on s /\
           valid_path g /\ (path_image g) SUBSET s /\
           pathfinish g = pathstart g
           ==> (f has_path_integral Cx(&0)) (g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CAUCHY_THEOREM_CONVEX THEN
  MAP_EVERY EXISTS_TAC [`s:complex->bool`; `{}:complex->bool`] THEN
  ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON; FINITE_RULES] THEN
  REWRITE_TAC[IN_DIFF; NOT_IN_EMPTY; complex_differentiable] THEN
  SUBGOAL_THEN `f holomorphic_on (interior s)` MP_TAC THENL
   [ASM_MESON_TAC[HOLOMORPHIC_ON_SUBSET; INTERIOR_SUBSET]; ALL_TAC] THEN
  MESON_TAC[holomorphic_on; HAS_COMPLEX_DERIVATIVE_WITHIN_OPEN; OPEN_INTERIOR]);;

(* ------------------------------------------------------------------------- *)
(* In particular for a disc.                                                 *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_THEOREM_DISC = prove
 (`!f g k a e.
        FINITE k /\ f continuous_on cball(a,e) /\
        (!x. x IN ball(a,e) DIFF k ==> f complex_differentiable at x) /\
        valid_path g /\ (path_image g) SUBSET cball(a,e) /\
        pathfinish g = pathstart g
        ==> (f has_path_integral Cx(&0)) (g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CAUCHY_THEOREM_CONVEX THEN
  MAP_EVERY EXISTS_TAC [`cball(a:complex,e)`; `k:complex->bool`] THEN
  ASM_REWRITE_TAC[INTERIOR_CBALL; CONVEX_CBALL]);;

let CAUCHY_THEOREM_DISC_SIMPLE = prove
 (`!f g a e.
        f holomorphic_on ball(a,e) /\
        valid_path g /\ (path_image g) SUBSET ball(a,e) /\
        pathfinish g = pathstart g
        ==> (f has_path_integral Cx(&0)) (g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CAUCHY_THEOREM_CONVEX_SIMPLE THEN
  EXISTS_TAC `ball(a:complex,e)` THEN ASM_REWRITE_TAC[CONVEX_BALL; OPEN_BALL]);;

(* ------------------------------------------------------------------------- *)
(* Generalize integrability to local primitives.                             *)
(* ------------------------------------------------------------------------- *)

let PATH_INTEGRAL_LOCAL_PRIMITIVE_LEMMA = prove
 (`!f f' g s a b.
        (!x. x IN s ==> (f has_complex_derivative f' x) (at x within s)) /\
        g piecewise_differentiable_on interval[a,b] /\
        (!x. x IN interval[a,b] ==> g(x) IN s)
        ==> (\x. f' (g x) * vector_derivative g (at x within interval[a,b]))
            integrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `interval[a:real^1,b] = {}` THENL
   [ASM_REWRITE_TAC[INTEGRABLE_ON_EMPTY];
    REWRITE_TAC[integrable_on] THEN
    EXISTS_TAC `(f:complex->complex) (g(b:real^1)) - f(g a)` THEN
    MATCH_MP_TAC PATH_INTEGRAL_PRIMITIVE_LEMMA THEN
    ASM_MESON_TAC[]]);;

let PATH_INTEGRAL_LOCAL_PRIMITIVE_ANY = prove
 (`!f g s a b.
    (!x. x IN s
         ==> ?d h. &0 < d /\
                   !y. norm(y - x) < d
                       ==> (h has_complex_derivative f(y)) (at y within s)) /\
    g piecewise_differentiable_on interval[a,b] /\
    (!x. x IN interval[a,b] ==> g(x) IN s)
    ==> (\x. f(g x) * vector_derivative g (at x)) integrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_ON_LITTLE_SUBINTERVALS THEN
  X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(g:real^1->complex) x`) THEN
  ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`d:real`; `h:complex->complex`] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP
    PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON) THEN
  REWRITE_TAC[continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `x:real^1`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `d:real`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC[integrable_on; GSYM HAS_INTEGRAL_LOCALIZED_VECTOR_DERIVATIVE] THEN
  REWRITE_TAC[GSYM integrable_on] THEN
  MATCH_MP_TAC PATH_INTEGRAL_LOCAL_PRIMITIVE_LEMMA THEN
  MAP_EVERY EXISTS_TAC
   [`h:complex->complex`; `IMAGE (g:real^1->complex) (interval[u,v])`] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `s:complex->bool` THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC; ASM SET_TAC[]] THEN
    REWRITE_TAC[GSYM dist] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[SUBSET; IN_BALL; DIST_SYM];
    ASM_MESON_TAC[PIECEWISE_DIFFERENTIABLE_ON_SUBSET];
    ASM SET_TAC[]]);;

let PATH_INTEGRAL_LOCAL_PRIMITIVE = prove
 (`!f g s.
        (!x. x IN s
         ==> ?d h. &0 < d /\
                   !y. norm(y - x) < d
                       ==> (h has_complex_derivative f(y)) (at y within s)) /\
        valid_path g /\ (path_image g) SUBSET s
        ==> f path_integrable_on g`,
  REWRITE_TAC[valid_path; path_image; SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[path_integrable_on; has_path_integral] THEN
  REWRITE_TAC[HAS_INTEGRAL_LOCALIZED_VECTOR_DERIVATIVE] THEN
  REWRITE_TAC[GSYM integrable_on; PATH_INTEGRAL_LOCAL_PRIMITIVE_ANY]);;

(* ------------------------------------------------------------------------- *)
(* In particular if a function is holomorphic.                               *)
(* ------------------------------------------------------------------------- *)

let PATH_INTEGRABLE_HOLOMORPHIC = prove
 (`!f g s k.
        open s /\ FINITE k /\
        f continuous_on s /\
        (!x. x IN s DIFF k ==> f complex_differentiable at x) /\
        valid_path g /\ path_image g SUBSET s
        ==> f path_integrable_on g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_INTEGRAL_LOCAL_PRIMITIVE THEN
  EXISTS_TAC `s:complex->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:complex->complex`; `ball(z:complex,d)`;
                 `k:complex->bool`] HOLOMORPHIC_CONVEX_PRIMITIVE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CONVEX_BALL; DIFF_EMPTY] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
    GEN_TAC THEN DISCH_THEN(fun th ->
        FIRST_X_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
    SIMP_TAC[IN_DIFF] THEN ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET];
    MATCH_MP_TAC MONO_EXISTS THEN
    SIMP_TAC[HAS_COMPLEX_DERIVATIVE_WITHIN_OPEN; OPEN_BALL] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN REWRITE_TAC[IN_BALL; dist] THEN
    ASM_MESON_TAC[HAS_COMPLEX_DERIVATIVE_AT_WITHIN]]);;

let PATH_INTEGRABLE_HOLOMORPHIC_SIMPLE = prove
 (`!f g s. open s /\ f holomorphic_on s /\ valid_path g /\ path_image g SUBSET s
           ==> f path_integrable_on g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_INTEGRABLE_HOLOMORPHIC THEN
  MAP_EVERY EXISTS_TAC [`s:complex->bool`; `{}:complex->bool`] THEN
  ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON; FINITE_RULES; DIFF_EMPTY] THEN
  ASM_MESON_TAC[HOLOMORPHIC_ON_OPEN; complex_differentiable]);;

(* ------------------------------------------------------------------------- *)
(* Winding number.                                                           *)
(* ------------------------------------------------------------------------- *)

let winding_number = new_definition
 `winding_number(g,z) = Cx(&1) / (Cx(&2) * Cx(pi) * ii) *
                        path_integral g (\w. Cx(&1) / (w - z))`;;

let CX_2PII_NZ = prove
 (`~(Cx(&2) * Cx(pi) * ii = Cx(&0))`,
  SIMP_TAC[COMPLEX_ENTIRE; CX_PI_NZ; II_NZ; CX_INJ; REAL_OF_NUM_EQ; ARITH]);;

let PATH_INTEGRABLE_INVERSEDIFF = prove
 (`!g z. valid_path g /\ ~(z IN path_image g)
         ==> (\w. Cx(&1) / (w - z)) path_integrable_on g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_INTEGRABLE_HOLOMORPHIC_SIMPLE THEN
  EXISTS_TAC `(:complex) DELETE z` THEN
  ASM_SIMP_TAC[OPEN_DELETE; OPEN_UNIV; HOLOMORPHIC_ON_OPEN; SET_RULE
   `s SUBSET (UNIV DELETE x) <=> ~(x IN s)`] THEN
  X_GEN_TAC `w:complex` THEN REWRITE_TAC[IN_UNIV; IN_DELETE] THEN
  STRIP_TAC THEN
  W(MP_TAC o DISCH_ALL o COMPLEX_DIFF_CONV o snd o dest_exists o snd) THEN
  ASM_REWRITE_TAC[COMPLEX_SUB_0] THEN MESON_TAC[]);;

let HAS_PATH_INTEGRAL_WINDING_NUMBER = prove
 (`!g z. valid_path g /\ ~(z IN path_image g)
         ==> ((\w. Cx(&1) / (w - z)) has_path_integral
              (Cx(&2) * Cx(pi) * ii * winding_number(g,z))) g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[winding_number] THEN
  SIMP_TAC[CX_PI_NZ; II_NZ; COMPLEX_FIELD
   `~(x = Cx(&0)) /\ ~(y = Cx(&0))
    ==> Cx(&2) * x * y * Cx(&1) / (Cx(&2) * x * y) * z = z`] THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_INTEGRAL THEN
  ASM_SIMP_TAC[PATH_INTEGRABLE_INVERSEDIFF]);;

let WINDING_NUMBER_JOIN = prove
 (`!g1 g2 z.
        valid_path g1 /\ valid_path g2 /\
        ~(z IN path_image g1) /\ ~(z IN path_image g2)
        ==> winding_number(g1 ++ g2,z) =
            winding_number(g1,z) + winding_number(g2,z)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[winding_number; CX_2PII_NZ; COMPLEX_FIELD
   `~(c = Cx(&0))
    ==> (Cx(&1) / c * x = Cx(&1) / c * y + Cx(&1) / c * z <=>
         x = y + z)`] THEN
  MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_JOIN THEN
  ASM_SIMP_TAC[HAS_PATH_INTEGRAL_INTEGRAL; PATH_INTEGRABLE_INVERSEDIFF]);;

let WINDING_NUMBER_REVERSEPATH = prove
 (`!g z. valid_path g /\ ~(z IN path_image g)
         ==> winding_number(reversepath g,z) = --(winding_number(g,z))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[winding_number; GSYM COMPLEX_MUL_RNEG] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_REVERSEPATH THEN
  ASM_SIMP_TAC[PATH_INTEGRABLE_INVERSEDIFF; HAS_PATH_INTEGRAL_INTEGRAL]);;

let WINDING_NUMBER_SHIFTPATH = prove
 (`!f g a z. valid_path g /\ pathfinish g = pathstart g /\
             a IN interval[vec 0,vec 1]
             ==> winding_number(shiftpath a g,z) = winding_number(g,z)`,
  SIMP_TAC[winding_number; PATH_INTEGRAL_SHIFTPATH]);;

(* ------------------------------------------------------------------------- *)
(* A combined theorem deducing several things piecewise.                     *)
(* ------------------------------------------------------------------------- *)

let WINDING_NUMBER_JOIN_POS_COMBINED = prove
 (`!g1 g2 z.
       (valid_path g1 /\
        ~(z IN path_image g1) /\
        &0 < Re(winding_number(g1,z))) /\
       (valid_path g2 /\
        ~(z IN path_image g2) /\
        &0 < Re(winding_number(g2,z))) /\
       pathfinish g1 = pathstart g2
       ==> valid_path(g1 ++ g2) /\
           ~(z IN path_image(g1 ++ g2)) /\
           &0 < Re(winding_number(g1 ++ g2,z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[VALID_PATH_JOIN] THEN
  ASM_SIMP_TAC[PATH_IMAGE_JOIN; VALID_PATH_IMP_PATH; IN_UNION] THEN
  ASM_SIMP_TAC[WINDING_NUMBER_JOIN; RE_ADD] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Useful sufficient conditions for the winding number to be positive etc.   *)
(* ------------------------------------------------------------------------- *)

let RE_WINDING_NUMBER = prove
 (`!g z. Re(winding_number(g,z)) =
         Im(path_integral g (\w. Cx(&1) / (w - z))) / (&2 * pi)`,
  REWRITE_TAC[winding_number; complex_div; COMPLEX_MUL_LID] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[COMPLEX_MUL_ASSOC; GSYM CX_MUL] THEN
  REWRITE_TAC[COMPLEX_INV_MUL; GSYM CX_INV; COMPLEX_INV_II] THEN
  REWRITE_TAC[COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG; RE_NEG] THEN
  REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC; RE_MUL_CX; RE_MUL_II] THEN
  MP_TAC PI_POS THEN CONV_TAC REAL_FIELD);;

let WINDING_NUMBER_POS_LE = prove
 (`!g z. valid_path g /\ ~(z IN path_image g) /\
         (!x. x IN interval(vec 0,vec 1)
              ==> &0 <= Im(vector_derivative g (at x) * cnj(g x - z)))
         ==> &0 <= Re(winding_number(g,z))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RE_WINDING_NUMBER] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN
  SIMP_TAC[REAL_LE_MUL; REAL_POS; PI_POS; REAL_LT_IMP_LE; IM_DEF] THEN
  MATCH_MP_TAC(INST_TYPE [`:1`,`:M`; `:2`,`:N`]
    HAS_INTEGRAL_COMPONENT_POS) THEN
  MAP_EVERY EXISTS_TAC
   [`\x:real^1. if x IN interval(vec 0,vec 1)
                then Cx(&1) / (g x - z) * vector_derivative g (at x)
                else Cx(&0)`;
    `interval[vec 0:real^1,vec 1]`] THEN
  REWRITE_TAC[ARITH; DIMINDEX_2] THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_INTEGRAL_SPIKE_INTERIOR THEN
    EXISTS_TAC `\x:real^1. Cx(&1) / (g x - z) * vector_derivative g (at x)` THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[GSYM HAS_PATH_INTEGRAL] THEN
    MATCH_MP_TAC HAS_PATH_INTEGRAL_INTEGRAL THEN
    ASM_SIMP_TAC[PATH_INTEGRABLE_INVERSEDIFF];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[GSYM IM_DEF; IM_CX; REAL_LE_REFL] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`) THEN
  ASM_REWRITE_TAC[complex_div; COMPLEX_MUL_LID] THEN
  REWRITE_TAC[complex_inv; complex_inv; complex_mul; RE; IM; cnj] THEN
  REWRITE_TAC[real_div; REAL_RING
   `(a * x) * b + (--c * x) * d:real = x * (a * b - c * d)`] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
  SIMP_TAC[REAL_POW_2; REAL_LE_INV_EQ; REAL_LE_ADD; REAL_LE_SQUARE] THEN
  ASM_REAL_ARITH_TAC);;

let WINDING_NUMBER_POS_LT_LEMMA = prove
 (`!g z e. valid_path g /\ ~(z IN path_image g) /\ &0 < e /\
           (!x. x IN interval(vec 0,vec 1)
                ==> e <= Im(vector_derivative g (at x) / (g x - z)))
           ==> &0 < Re(winding_number(g,z))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RE_WINDING_NUMBER] THEN
  MATCH_MP_TAC REAL_LT_DIV THEN
  SIMP_TAC[REAL_LT_MUL; REAL_OF_NUM_LT; ARITH; PI_POS] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `Im(ii * Cx e)` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_MUL_LNEG; IM_MUL_II; IM_NEG; RE_CX]; ALL_TAC] THEN
  REWRITE_TAC[IM_DEF] THEN
  MATCH_MP_TAC(ISPECL [`\x:real^1. ii * Cx e`;
        `\x:real^1. if x IN interval(vec 0,vec 1)
                    then Cx(&1) / (g x - z) * vector_derivative g (at x)
                    else ii * Cx e`;
        `interval[vec 0:real^1,vec 1]`; `ii * Cx e`;
        `path_integral g (\w. Cx(&1) / (w - z))`; `2`]
       HAS_INTEGRAL_COMPONENT_LE) THEN
  REWRITE_TAC[DIMINDEX_2; ARITH] THEN REPEAT CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM VECTOR_MUL_LID] THEN
    ONCE_REWRITE_TAC[GSYM CONTENT_UNIT_1] THEN
    REWRITE_TAC[HAS_INTEGRAL_CONST];
    MATCH_MP_TAC HAS_INTEGRAL_SPIKE_INTERIOR THEN
    EXISTS_TAC `\x:real^1. Cx(&1) / (g x - z) * vector_derivative g (at x)` THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[GSYM HAS_PATH_INTEGRAL] THEN
    MATCH_MP_TAC HAS_PATH_INTEGRAL_INTEGRAL THEN
    ASM_SIMP_TAC[PATH_INTEGRABLE_INVERSEDIFF];
    X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[GSYM IM_DEF; IM_CX; REAL_LE_REFL] THEN
    REWRITE_TAC[IM_MUL_II; RE_CX] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`) THEN
    ASM_REWRITE_TAC[complex_div; COMPLEX_MUL_LID; COMPLEX_MUL_SYM]]);;

let WINDING_NUMBER_POS_LT = prove
 (`!g z e. valid_path g /\ ~(z IN path_image g) /\ &0 < e /\
           (!x. x IN interval(vec 0,vec 1)
                ==> e <= Im(vector_derivative g (at x) * cnj(g x - z)))
           ==> &0 < Re(winding_number(g,z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `bounded (IMAGE (\w. w - z) (path_image g))` MP_TAC THENL
   [REWRITE_TAC[path_image; GSYM IMAGE_o] THEN
    MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    REWRITE_TAC[COMPACT_INTERVAL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
    MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
    ASM_REWRITE_TAC[GSYM valid_path];
    ALL_TAC] THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC WINDING_NUMBER_POS_LT_LEMMA THEN
  EXISTS_TAC `e:real / B pow 2` THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_POW_LT] THEN
  X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[COMPLEX_DIV_CNJ] THEN
  REWRITE_TAC[real_div; complex_div; GSYM CX_INV; GSYM CX_POW] THEN
  REWRITE_TAC[IM_MUL_CX] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ; REAL_POW_LE] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN
    UNDISCH_TAC `~((z:complex) IN path_image g)`;
    MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    FIRST_X_ASSUM MATCH_MP_TAC] THEN
  REWRITE_TAC[path_image; IN_IMAGE] THEN
  ASM_MESON_TAC[SUBSET; INTERVAL_OPEN_SUBSET_CLOSED]);;

(* ------------------------------------------------------------------------- *)
(* Winding number is zero outside a convex set containing the curve.         *)
(* ------------------------------------------------------------------------- *)

let WINDING_NUMBER_ZERO_OUTSIDE = prove
 (`!g s z. valid_path g /\ convex s /\ pathfinish g = pathstart g /\
           ~(z IN s) /\ path_image g SUBSET s
           ==> winding_number(g,z) = Cx(&0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[winding_number] THEN
  REWRITE_TAC[COMPLEX_ENTIRE] THEN DISJ2_TAC THEN
  MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC CAUCHY_THEOREM_CONVEX_SIMPLE THEN
  EXISTS_TAC `s:complex->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN
  ASM_SIMP_TAC[HOLOMORPHIC_ON_SUB; HOLOMORPHIC_ON_CONST; HOLOMORPHIC_ON_ID] THEN
  REWRITE_TAC[COMPLEX_SUB_0] THEN ASM_MESON_TAC[]);;

let WINDING_NUMBER_ZERO_ATINFINITY = prove
 (`!g. valid_path g /\ pathfinish g = pathstart g
       ==> ?B. !z. B <= norm(z) ==> winding_number(g,z) = Cx(&0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `bounded (path_image g :complex->bool)` MP_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN REWRITE_TAC[path_image] THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN SIMP_TAC[COMPACT_INTERVAL] THEN
    ASM_MESON_TAC[valid_path; PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON];
    REWRITE_TAC[bounded] THEN DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
    EXISTS_TAC `B + &1` THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC WINDING_NUMBER_ZERO_OUTSIDE THEN
    EXISTS_TAC `cball(Cx(&0),B)` THEN ASM_REWRITE_TAC[CONVEX_CBALL] THEN
    REWRITE_TAC[SUBSET; IN_CBALL; dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN
    ASM_MESON_TAC[REAL_ARITH `~(B + &1 <= z /\ z <= B)`]]);;

(* ------------------------------------------------------------------------- *)
(* The winding number is an integer (proof from Ahlfors's book).             *)
(* ------------------------------------------------------------------------- *)

let WINDING_NUMBER_AHLFORS_LEMMA = prove
 (`!g a b.
        g piecewise_differentiable_on interval [a,b] /\
        drop a <= drop b /\ (!x. x IN interval [a,b] ==> ~(g x = z))
        ==> (\x. vector_derivative g (at x within interval[a,b]) / (g(x) - z))
            integrable_on interval[a,b] /\
            cexp(--(integral (interval[a,b])
                        (\x. vector_derivative g (at x within interval[a,b]) /
                               (g(x) - z)))) *
            (g(b) - z) = g(a) - z`,
  let lemma = prove
   (`!f g g' s x z.
          (g has_vector_derivative g') (at x within s) /\
          (f has_vector_derivative (g' / (g x - z))) (at x within s) /\
          ~(g x = z)
          ==> ((\x. cexp(--f x) * (g x - z)) has_vector_derivative Cx(&0))
              (at x within s)`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `cexp(--f x) * (g' - Cx(&0)) +
      (cexp(--f x) * --(g' / ((g:real^1->complex) x - z))) * (g x - z) = Cx(&0)`
     (SUBST1_TAC o SYM)
    THENL
     [FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
      CONV_TAC COMPLEX_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC(ISPEC `( * ):complex->complex->complex`
      HAS_VECTOR_DERIVATIVE_BILINEAR_WITHIN) THEN
    REWRITE_TAC[BILINEAR_COMPLEX_MUL; GSYM COMPLEX_VEC_0] THEN
    ASM_SIMP_TAC[HAS_VECTOR_DERIVATIVE_SUB; ETA_AX;
                 HAS_VECTOR_DERIVATIVE_CONST] THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM o_DEF] THEN
    REWRITE_TAC[has_vector_derivative] THEN
    SUBGOAL_THEN `!x y. (\z. drop z % (x * y :complex)) =
                        (\w. x * w) o (\z. drop z % y)`
     (fun th -> REWRITE_TAC[th])
    THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; COMPLEX_CMUL] THEN
      SIMPLE_COMPLEX_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_WITHIN THEN
    REWRITE_TAC[GSYM has_complex_derivative; GSYM has_vector_derivative] THEN
    SIMP_TAC[HAS_COMPLEX_DERIVATIVE_CEXP; HAS_COMPLEX_DERIVATIVE_AT_WITHIN] THEN
    ASM_SIMP_TAC[HAS_VECTOR_DERIVATIVE_NEG]) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!w. ~(w = z)
        ==> ?h. !y. norm(y - w) < norm(w - z)
                    ==> (h has_complex_derivative inv(y - z)) (at y)`
   (LABEL_TAC "P")
  THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\w:complex. inv(w - z)`;
               `ball(w:complex,norm(w - z))`;
               `{}:complex->bool`]
              HOLOMORPHIC_CONVEX_PRIMITIVE) THEN
    SIMP_TAC[HAS_COMPLEX_DERIVATIVE_WITHIN_OPEN; OPEN_BALL; INTERIOR_OPEN] THEN
    REWRITE_TAC[CONVEX_BALL; FINITE_RULES; DIFF_EMPTY] THEN ANTS_TAC THENL
     [SUBGOAL_THEN `(\w. inv(w - z)) holomorphic_on ball(w:complex,norm(w - z))`
       (fun th ->
        MESON_TAC[HOLOMORPHIC_ON_OPEN; HOLOMORPHIC_ON_IMP_CONTINUOUS_ON;
                  OPEN_BALL; complex_differentiable; th]) THEN
      SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_BALL; IN_BALL] THEN
      X_GEN_TAC `u:complex` THEN DISCH_TAC THEN
      EXISTS_TAC `--Cx(&1) / (u - z) pow 2` THEN COMPLEX_DIFF_TAC THEN
      REWRITE_TAC[COMPLEX_SUB_RZERO; COMPLEX_SUB_0] THEN
      ASM_MESON_TAC[REAL_LT_REFL; dist];
      ALL_TAC] THEN
    REWRITE_TAC[IN_BALL; dist] THEN MESON_TAC[NORM_SUB];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN interval[a,b]
        ==> (\x. vector_derivative g (at x within interval[a,b]) / (g(x) - z))
            integrable_on interval[a,t] /\
            cexp(--(integral (interval[a,t])
                         (\x. vector_derivative g (at x within interval[a,b]) /
                              (g(x) - z)))) *
            (g(t) - z) = g(a) - z`
   (fun th -> MATCH_MP_TAC th THEN
              ASM_REWRITE_TAC[IN_INTERVAL_1; REAL_LE_REFL]) THEN
  REWRITE_TAC[TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`a:real^1`; `b:real^1`] THEN
    ASM_REWRITE_TAC[SUBSET_INTERVAL_1; REAL_LE_REFL] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[IN_INTERVAL_1]] THEN
    REWRITE_TAC[integrable_on; complex_div] THEN
    ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
    REWRITE_TAC[HAS_INTEGRAL_LOCALIZED_VECTOR_DERIVATIVE] THEN
    REWRITE_TAC[GSYM integrable_on] THEN
    MATCH_MP_TAC PATH_INTEGRAL_LOCAL_PRIMITIVE_ANY THEN
    EXISTS_TAC `(:complex) DELETE z` THEN
    ASM_SIMP_TAC[IN_DELETE; IN_UNIV;
                 DIFFERENTIABLE_ON_IMP_PIECEWISE_DIFFERENTIABLE] THEN
    X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
    EXISTS_TAC `norm(w - z:complex)` THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_NZ; COMPLEX_SUB_0] THEN
    ASM_MESON_TAC[HAS_COMPLEX_DERIVATIVE_AT_WITHIN];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_ZERO_UNIQUE_STRONG_INTERVAL THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [piecewise_differentiable_on]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[IN_DIFF] THEN
  X_GEN_TAC `k:real^1->bool` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CONVEX_INTERVAL; INTEGRAL_REFL] THEN
  REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_NEG_0; CEXP_0; COMPLEX_MUL_LID] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; ETA_AX;
                 PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    REWRITE_TAC[CONTINUOUS_ON_CEXP] THEN
    MATCH_MP_TAC CONTINUOUS_ON_NEG THEN
    MATCH_MP_TAC INDEFINITE_INTEGRAL_CONTINUOUS_RIGHT THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; REAL_LE_REFL];
    ALL_TAC] THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\w:complex. inv(w - z)`;
                 `ball((g:real^1->complex) t,dist(g t,z))`;
                 `{}:complex->bool`]
                HOLOMORPHIC_CONVEX_PRIMITIVE) THEN
  SIMP_TAC[HAS_COMPLEX_DERIVATIVE_WITHIN_OPEN; OPEN_BALL; INTERIOR_OPEN] THEN
  REWRITE_TAC[CONVEX_BALL; FINITE_RULES; DIFF_EMPTY] THEN ANTS_TAC THENL
   [SUBGOAL_THEN `(\w. inv(w - z)) holomorphic_on ball(g(t:real^1),dist(g t,z))`
     (fun th ->
      MESON_TAC[HOLOMORPHIC_ON_OPEN; HOLOMORPHIC_ON_IMP_CONTINUOUS_ON;
                OPEN_BALL; complex_differentiable; th]) THEN
    SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_BALL; IN_BALL] THEN
    X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
    EXISTS_TAC `--Cx(&1) / (w - z) pow 2` THEN COMPLEX_DIFF_TAC THEN
    REWRITE_TAC[COMPLEX_SUB_RZERO; COMPLEX_SUB_0] THEN
    ASM_MESON_TAC[REAL_LT_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[IN_BALL; dist] THEN
  DISCH_THEN(X_CHOOSE_TAC `h:complex->complex`) THEN
  SUBGOAL_THEN `(\h. Cx(&0)) = (\h. drop h % Cx(&0))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM COMPLEX_VEC_0; VECTOR_MUL_RZERO];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM has_vector_derivative] THEN MATCH_MP_TAC lemma THEN
  EXISTS_TAC `vector_derivative g (at t within interval[a,b]):complex` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS] THEN
    ASM_MESON_TAC[DIFFERENTIABLE_AT_WITHIN];
    ALL_TAC;
    ASM_MESON_TAC[]] THEN
  REWRITE_TAC[has_vector_derivative] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN THEN
  ASM_REWRITE_TAC[GSYM has_vector_derivative] THEN
  EXISTS_TAC `\u. integral (interval [a,t])
                  (\x. vector_derivative g (at x within interval [a,b]) /
                       ((g:real^1->complex) x - z)) + (h(g(u)) - h(g(t)))` THEN
  REWRITE_TAC[LEFT_EXISTS_AND_THM; CONJ_ASSOC] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[COMPLEX_RING `a + (b - c) = b + (a - c):complex`] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM VECTOR_ADD_RID] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN
    REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN
    REWRITE_TAC[has_vector_derivative] THEN
    SUBGOAL_THEN `!x y. (\h. drop h % x / y) =
                        (\x. inv(y) * x) o (\h. drop h % x)`
     (fun th -> REWRITE_TAC[th])
    THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; COMPLEX_CMUL] THEN
      SIMPLE_COMPLEX_ARITH_TAC;
      ALL_TAC] THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM o_DEF] THEN
    MATCH_MP_TAC DIFF_CHAIN_WITHIN THEN
    REWRITE_TAC[GSYM has_complex_derivative; GSYM has_vector_derivative] THEN
    REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[DIFFERENTIABLE_AT_WITHIN]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_AT_WITHIN THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_NORM_0; COMPLEX_NORM_NZ] THEN
    ASM_SIMP_TAC[COMPLEX_SUB_0]] THEN
  SUBGOAL_THEN
   `?d. &0 < d /\
        !y:real^1. y IN interval[a,b] /\ dist(y,t) < d
                   ==> dist(g y:complex,g t) < norm(g t - z) /\ ~(y IN k)`
  MP_TAC THENL
   [SUBGOAL_THEN `(g:real^1->complex) continuous (at t within interval[a,b])`
    MP_TAC THENL
     [ASM_MESON_TAC[PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON;
                    CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN];
      ALL_TAC] THEN
    REWRITE_TAC[continuous_within] THEN
    DISCH_THEN(MP_TAC o SPEC `norm((g:real^1->complex) t - z)`) THEN
    ASM_SIMP_TAC[COMPLEX_NORM_NZ; COMPLEX_SUB_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC o
      SPEC `t:real^1` o MATCH_MP FINITE_SET_AVOID) THEN
    EXISTS_TAC `min d1 d2` THEN ASM_SIMP_TAC[REAL_LT_MIN] THEN
    ASM_MESON_TAC[DIST_SYM; REAL_NOT_LE];
    ALL_TAC] THEN
  REWRITE_TAC[TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:real^1` THEN REWRITE_TAC[dist] THEN
  STRIP_TAC THEN
  DISJ_CASES_TAC(REAL_ARITH `drop t <= drop u \/ drop u <= drop t`) THENL
   [SUBGOAL_THEN
     `integral (interval [a,u])
        (\x. vector_derivative g (at x within interval [a,b]) / (g x - z)) =
      integral (interval [a,t])
        (\x. vector_derivative g (at x within interval [a,b]) / (g x - z)) +
      integral (interval [t,u])
        (\x. vector_derivative g (at x within interval [a,b]) / (g x - z))`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_COMBINE THEN
      ASM_MESON_TAC[IN_INTERVAL_1];
      ALL_TAC] THEN
    SIMP_TAC[COMPLEX_RING `a + x = a + y <=> y:complex = x`];
    SUBGOAL_THEN
     `integral (interval [a,t])
        (\x. vector_derivative g (at x within interval [a,b]) / (g x - z)) =
      integral (interval [a,u])
        (\x. vector_derivative g (at x within interval [a,b]) / (g x - z)) +
      integral (interval [u,t])
        (\x. vector_derivative g (at x within interval [a,b]) / (g x - z))`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_COMBINE THEN
      ASM_MESON_TAC[IN_INTERVAL_1];
      ALL_TAC] THEN
    SIMP_TAC[COMPLEX_RING `(a + x) + (w - z) = a <=> x:complex = z - w`]] THEN
  (MATCH_MP_TAC INTEGRAL_UNIQUE THEN
   MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS THEN
   ASM_REWRITE_TAC[GSYM o_DEF] THEN X_GEN_TAC `x:real^1` THEN
   REPEAT STRIP_TAC THEN REWRITE_TAC[has_vector_derivative; COMPLEX_CMUL] THEN
   SUBGOAL_THEN `!x y. (\h. Cx(drop h) * x / y) =
                       (\x. inv(y) * x) o (\h. drop h % x)`
    (fun th -> REWRITE_TAC[th])
   THENL
    [REWRITE_TAC[FUN_EQ_THM; o_THM; COMPLEX_CMUL] THEN
     SIMPLE_COMPLEX_ARITH_TAC;
     ALL_TAC] THEN
   MATCH_MP_TAC DIFF_CHAIN_WITHIN THEN
   REWRITE_TAC[GSYM has_complex_derivative; GSYM has_vector_derivative] THEN
   CONJ_TAC THENL
    [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
     EXISTS_TAC `interval[a:real^1,b]` THEN
     REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS] THEN CONJ_TAC THENL
      [MATCH_MP_TAC DIFFERENTIABLE_AT_WITHIN THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
        [ALL_TAC; FIRST_X_ASSUM MATCH_MP_TAC];
       ALL_TAC] THEN
     REPEAT(FIRST_X_ASSUM(MP_TAC o
        check (fun t -> not(is_forall (concl t))))) THEN
     REWRITE_TAC[dist; NORM_REAL; GSYM drop; DROP_SUB] THEN
     REWRITE_TAC[SUBSET_INTERVAL_1; IN_INTERVAL_1; REAL_LE_REFL] THEN
     REAL_ARITH_TAC;
     ALL_TAC] THEN
   MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_AT_WITHIN THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM dist] THEN
   ONCE_REWRITE_TAC[DIST_SYM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   CONJ_TAC THENL [ASM_MESON_TAC[IN_INTERVAL_1; REAL_LE_TRANS]; ALL_TAC] THEN
   REPEAT(FIRST_X_ASSUM(MP_TAC o
      check (fun t -> not(is_forall (concl t))))) THEN
   REWRITE_TAC[dist; NORM_REAL; GSYM drop; DROP_SUB] THEN
   REWRITE_TAC[SUBSET_INTERVAL_1; IN_INTERVAL_1; REAL_LE_REFL] THEN
   REAL_ARITH_TAC));;

let WINDING_NUMBER_AHLFORS = prove
 (`!g z a b.
        g piecewise_differentiable_on interval [a,b] /\
        drop a <= drop b /\ (!x. x IN interval [a,b] ==> ~(g x = z))
        ==> (\x. vector_derivative g (at x) / (g(x) - z))
            integrable_on interval[a,b] /\
            cexp(--(integral (interval[a,b])
                             (\x. vector_derivative g (at x) / (g(x) - z)))) *
            (g(b) - z) = g(a) - z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[integrable_on; integral] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[COMPLEX_MUL_SYM] complex_div] THEN
  REWRITE_TAC[GSYM HAS_INTEGRAL_LOCALIZED_VECTOR_DERIVATIVE] THEN
  ONCE_REWRITE_TAC[ONCE_REWRITE_RULE[COMPLEX_MUL_SYM](GSYM complex_div)] THEN
  REWRITE_TAC[GSYM integral; GSYM integrable_on] THEN
  MATCH_MP_TAC WINDING_NUMBER_AHLFORS_LEMMA THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* State in terms of complex integers. Note the useful equality version.     *)
(* ------------------------------------------------------------------------- *)

let complex_integer = new_definition
 `complex_integer z <=> integer(Re z) /\ Im z = &0`;;

let COMPLEX_INTEGER = prove
 (`complex_integer z <=> ?n. integer n /\ z = Cx n`,
  REWRITE_TAC[COMPLEX_EQ; RE_CX; IM_CX; complex_integer] THEN MESON_TAC[]);;

let INTEGER_WINDING_NUMBER_EQ = prove
 (`!g z. valid_path g /\ ~(z IN path_image g)
         ==> (complex_integer(winding_number(g,z)) <=>
              pathfinish g = pathstart g)`,
  REWRITE_TAC[valid_path; pathfinish; pathstart; path_image] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[winding_number] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `cexp(path_integral g (\w. Cx(&1) / (w - z))) = Cx(&1)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[CEXP_EQ_1; complex_integer] THEN
    REWRITE_TAC[complex_div; COMPLEX_MUL_LID; COMPLEX_INV_MUL] THEN
    SIMP_TAC[GSYM CX_INV; GSYM CX_MUL; COMPLEX_MUL_ASSOC; COMPLEX_INV_II] THEN
    REWRITE_TAC[RE_MUL_CX; IM_MUL_CX; GSYM COMPLEX_MUL_ASSOC] THEN
    REWRITE_TAC[COMPLEX_MUL_LNEG; RE_MUL_II; IM_MUL_II; RE_NEG; IM_NEG] THEN
    REWRITE_TAC[REAL_NEGNEG; REAL_ENTIRE; REAL_INV_EQ_0; REAL_NEG_EQ_0] THEN
    SIMP_TAC[REAL_OF_NUM_EQ; ARITH; REAL_LT_IMP_NZ; PI_POS] THEN
    SIMP_TAC[PI_POS; REAL_FIELD
     `&0 < p ==> (x = &2 * n * p <=> (inv(&2) * inv(p)) * x = n)`] THEN
    MESON_TAC[];
    MP_TAC(ISPECL [`g:real^1->complex`; `z:complex`;
                   `vec 0:real^1`; `vec 1:real^1`]
                  WINDING_NUMBER_AHLFORS) THEN
    ASM_REWRITE_TAC[DROP_VEC; REAL_POS] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[COMPLEX_MUL_SYM] complex_div] THEN
    REWRITE_TAC[integral; GSYM HAS_INTEGRAL_LOCALIZED_VECTOR_DERIVATIVE] THEN
    REWRITE_TAC[GSYM has_path_integral; GSYM path_integral] THEN
    REWRITE_TAC[CEXP_NEG; COMPLEX_MUL_RID] THEN
    MATCH_MP_TAC(COMPLEX_FIELD
     `~(i = Cx(&0)) /\ ~(g0 = z)
      ==> (inv i * (g1 - z) = g0 - z ==> (i = Cx(&1) <=> g1 = g0))`) THEN
    REWRITE_TAC[CEXP_NZ] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [IN_IMAGE]) THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN MESON_TAC[REAL_POS; DROP_VEC]]);;

let INTEGER_WINDING_NUMBER = prove
 (`!g z. valid_path g /\ pathfinish g = pathstart g /\ ~(z IN path_image g)
         ==> complex_integer(winding_number(g,z))`,
  MESON_TAC[INTEGER_WINDING_NUMBER_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Important limit of winding number for a simple closed path.               *)
(* ------------------------------------------------------------------------- *)

let SIMPLE_CLOSED_PATH_WINDING_NUMBER_POS = prove
 (`!g z. valid_path g /\ ~(z IN path_image g) /\
         simple_path g /\ pathfinish g = pathstart g /\
         &0 < Re(winding_number(g,z))
         ==> winding_number(g,z) = Cx(&1)`,
  SUBGOAL_THEN
   `!g z. valid_path g /\ ~(z IN path_image g) /\
          simple_path g /\ pathfinish g = pathstart g /\
          &0 < Re(winding_number(g,z)) /\
          (!x. x IN interval[vec 0,vec 1]
               ==> norm(g x - z) <= norm(pathstart g - z))
          ==> winding_number(g,z) = Cx(&1)`
  MP_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`path_image(g:real^1->complex)`; `z:complex`]
      DISTANCE_ATTAINS_SUP) THEN
    ASM_SIMP_TAC[PATH_IMAGE_NONEMPTY; VALID_PATH_IMP_PATH;
                 COMPACT_PATH_IMAGE] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; IMP_CONJ; path_image] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `a:real^1` THEN
    DISCH_TAC THEN REWRITE_TAC[dist] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`shiftpath a (g:real^1->complex)`; `z:complex`]) THEN
    ASM_SIMP_TAC[WINDING_NUMBER_SHIFTPATH] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[VALID_PATH_SHIFTPATH; SIMPLE_PATH_SHIFTPATH;
                 ENDPOINTS_SHIFTPATH; PATH_IMAGE_SHIFTPATH] THEN
    SUBGOAL_THEN
     `!w. w IN path_image (shiftpath a (g:real^1->complex))
          ==> norm(w - z) <= norm(g a - z)`
    MP_TAC THENL [ASM_SIMP_TAC[PATH_IMAGE_SHIFTPATH]; ALL_TAC] THEN
    ASM_REWRITE_TAC[path_image; FORALL_IN_IMAGE]] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^1->complex`; `z:complex`]
    INTEGER_WINDING_NUMBER) THEN
  ASM_REWRITE_TAC[complex_integer] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[COMPLEX_EQ; IM_CX; RE_CX] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 + &1 <= x /\ ~(&1 < x) ==> x = &1`) THEN
  ASM_SIMP_TAC[GSYM REAL_LT_INTEGERS; INTEGER_CLOSED] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `path(\x. Cx(&1) / (Cx(&2) * Cx pi * ii) *
             integral (interval[vec 0,x])
                      (\x. vector_derivative g (at x) / (g x - z)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[path] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC INDEFINITE_INTEGRAL_CONTINUOUS_RIGHT THEN
    REWRITE_TAC[integrable_on; GSYM HAS_PATH_INTEGRAL;
                ONCE_REWRITE_RULE[COMPLEX_MUL_SYM] complex_div;
                GSYM path_integrable_on] THEN
    MATCH_MP_TAC(REWRITE_RULE[COMPLEX_MUL_LID; complex_div]
      PATH_INTEGRABLE_INVERSEDIFF) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `bounded
   (path_image(\x. Cx(&1) / (Cx(&2) * Cx pi * ii) *
                   integral (interval[vec 0,x])
                            (\x. vector_derivative g (at x) / (g x - z))))`
  MP_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN REWRITE_TAC[path_image] THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    REWRITE_TAC[COMPACT_INTERVAL] THEN ASM_REWRITE_TAC[GSYM path];
    ALL_TAC] THEN
  REWRITE_TAC[BOUNDED_POS; path_image; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`\x. Cx(&1) / (Cx(&2) * Cx pi * ii) *
         integral (interval[vec 0,x])
                  (\x. vector_derivative g (at x) / (g x - z))`;
    `\x. Cx(&1) / (Cx(&2) * Cx pi * ii) *
         integral (interval[vec 0,x])
                  (\x. vector_derivative g (at x) / (g x - z)) + Cx(&1)`;
    `vector[--(B + &1); &0]:real^2`;
    `vector[B + &1; B + &1]:real^2`]
   FASHODA_INTERLACE) THEN
  ASM_REWRITE_TAC[pathstart; pathfinish; NOT_IMP; GSYM CONJ_ASSOC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[path; COMPLEX_NEG_ADD] THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN ASM_REWRITE_TAC[GSYM path];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[AND_FORALL_THM;
                TAUT `(a ==> b) /\ (a ==> c) <=> a ==> b /\ c`] THEN
    X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN
    REWRITE_TAC[IN_INTERVAL; FORALL_2; DIMINDEX_2; VECTOR_2] THEN
    REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; IM_ADD; RE_NEG; IM_NEG; RE_ADD] THEN
    REWRITE_TAC[RE_CX; IM_CX; REAL_ADD_RID; RE_NEG] THEN
    MATCH_MP_TAC(REAL_ARITH
     `abs(x) <= B /\ abs(y) <= B /\ &0 <= y
      ==> ((--(B + &1) <= x /\ x <= B + &1) /\
           (&0 <= y /\ y <= B + &1)) /\
          ((--(B + &1) <= (x + &1) /\ (x + &1) <= B + &1) /\
           (&0 <= y /\ y <= B + &1))`) THEN
    REPEAT(CONJ_TAC THENL
     [REWRITE_TAC[GSYM RE_NEG; GSYM IM_NEG] THEN
      REWRITE_TAC[RE_DEF; IM_DEF] THEN
      W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) COMPONENT_LE_NORM
       (lhand w))) THEN
      REWRITE_TAC[DIMINDEX_2; ARITH] THEN
      MATCH_MP_TAC(REAL_ARITH `y <= b ==> x <= y ==> x <= b`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC]) THEN
    REWRITE_TAC[COMPLEX_MUL_ASSOC; GSYM CX_MUL] THEN
    SIMP_TAC[COMPLEX_MUL_LID; complex_div; COMPLEX_INV_MUL; GSYM CX_INV] THEN
    REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC; COMPLEX_INV_II; IM_MUL_CX] THEN
    REWRITE_TAC[GSYM REAL_MUL_RNEG] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    SIMP_TAC[REAL_LE_INV_EQ; REAL_POS; REAL_LE_MUL;
             REAL_LT_IMP_LE; PI_POS] THEN
    REWRITE_TAC[COMPLEX_MUL_LNEG; IM_NEG; IM_MUL_II; REAL_NEGNEG] THEN
    MP_TAC(ISPECL
     [`g:real^1->complex`; `z:complex`; `vec 0:real^1`; `x:real^1`]
     WINDING_NUMBER_AHLFORS) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_SUBSET THEN
        EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
        ASM_REWRITE_TAC[GSYM valid_path; SUBSET_INTERVAL_1] THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      X_GEN_TAC `y:real^1` THEN REWRITE_TAC[IN_INTERVAL_1] THEN
      DISCH_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
      UNDISCH_TAC `~((z:complex) IN path_image g)` THEN
      REWRITE_TAC[path_image; IN_IMAGE; IN_INTERVAL_1] THEN
      ASM_MESON_TAC[REAL_LE_TRANS];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `norm:complex->real` o CONJUNCT2) THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; NORM_CEXP; RE_NEG] THEN
    SUBGOAL_THEN `~((g:real^1->complex) x = z)` ASSUME_TAC THENL
     [UNDISCH_TAC `~((z:complex) IN path_image g)` THEN
      REWRITE_TAC[path_image; IN_IMAGE] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((g:real^1->complex) (vec 0) = z) /\
                  norm(g x - z) <= norm(g(vec 0) - z)`
    STRIP_ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[GSYM COMPLEX_SUB_0] THEN
      REWRITE_TAC[GSYM COMPLEX_NORM_NZ] THEN
      MATCH_MP_TAC(REAL_ARITH
       `&0 < x /\ x <= y ==> &0 < y /\ x <= y`) THEN
      ASM_REWRITE_TAC[COMPLEX_NORM_NZ; COMPLEX_SUB_0] THEN
      ASM_MESON_TAC[pathstart];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_FIELD `&0 < y ==> (x * y = z <=> x = z / y)`;
                 COMPLEX_NORM_NZ; COMPLEX_SUB_0] THEN
    REWRITE_TAC[complex_div] THEN
    MATCH_MP_TAC(REAL_ARITH
     `(&1 <= q /\ (&1 <= e ==> &0 <= x)) ==> e = q ==> &0 <= x`) THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; COMPLEX_NORM_NZ; COMPLEX_SUB_0] THEN
      ASM_REWRITE_TAC[REAL_MUL_LID];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM REAL_EXP_0] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE];
    ALL_TAC] THEN
  REWRITE_TAC[INTEGRAL_REFL; VECTOR_2] THEN
  REWRITE_TAC[GSYM IM_DEF; GSYM RE_DEF; RE_NEG; IM_NEG] THEN
  REWRITE_TAC[REAL_LT_NEG2; COMPLEX_VEC_0; COMPLEX_MUL_RZERO] THEN
  REWRITE_TAC[COMPLEX_ADD_LID; RE_CX; IM_CX] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[integral; ONCE_REWRITE_RULE[COMPLEX_MUL_SYM] complex_div;
              GSYM HAS_PATH_INTEGRAL] THEN
  REWRITE_TAC[GSYM path_integral] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[COMPLEX_MUL_SYM] (GSYM complex_div)] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING `inv(x) = Cx(&1) * inv(x)`] THEN
  REWRITE_TAC[GSYM winding_number; GSYM complex_div] THEN
  ASM_SIMP_TAC[IM_ADD; IM_CX; RE_ADD; RE_CX; REAL_ADD_LID] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; REWRITE_TAC[GSYM integral]] THEN
  DISCH_THEN(X_CHOOSE_THEN `zz:complex` MP_TAC) THEN
  REWRITE_TAC[path_image; IN_IMAGE] THEN DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `x:real^1` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `y:real^1` MP_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  ASM_CASES_TAC `y:real^1 = x` THEN
  ASM_REWRITE_TAC[COMPLEX_RING `~(x = x + Cx(&1))`] THEN
  SIMP_TAC[CX_2PII_NZ; COMPLEX_FIELD
   `~(y = Cx(&0)) ==> (Cx(&1) / y * a = Cx(&1) / y * b + Cx(&1) <=>
                       a = b + y)`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL
   [`g:real^1->complex`; `z:complex`; `vec 0:real^1`]
   WINDING_NUMBER_AHLFORS) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `x:real^1` th) THEN
                       MP_TAC(SPEC `y:real^1` th)) THEN
  MATCH_MP_TAC(TAUT
   `(a1 /\ a2) /\ ~(c1 /\ c2)
    ==> (a1 ==> b1 /\ c1) ==> (a2 ==> b2 /\ c2) ==> F`) THEN
  CONJ_TAC THENL
   [CONJ_TAC THEN
    (CONJ_TAC THENL
     [MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_SUBSET THEN
      EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
      ASM_REWRITE_TAC[GSYM valid_path; SUBSET_INTERVAL_1] THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1])) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1])) THEN
      REAL_ARITH_TAC;
      ALL_TAC]) THEN
    GEN_TAC THEN REWRITE_TAC[IN_INTERVAL_1] THEN
    DISCH_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
    UNDISCH_TAC `~((z:complex) IN path_image g)` THEN
    REWRITE_TAC[path_image; IN_IMAGE; IN_INTERVAL_1] THEN
    ASM_MESON_TAC[REAL_LE_TRANS];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[CEXP_ADD; COMPLEX_NEG_ADD] THEN
  SUBGOAL_THEN `cexp (--(Cx(&2) * Cx pi * ii)) = Cx(&1)` SUBST1_TAC THENL
   [REWRITE_TAC[CEXP_EQ_1; RE_NEG; RE_MUL_CX; RE_II] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_NEG_0] THEN
    EXISTS_TAC `-- &1:real` THEN REWRITE_TAC[IM_NEG; IM_MUL_CX] THEN
    REWRITE_TAC[INTEGER_NEG; INTEGER_CLOSED; IM_II] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM)) THEN
  SIMP_TAC[CEXP_NZ; COMPLEX_FIELD
   `~(c = Cx(&0)) ==> (c * (x - z) = (c * Cx(&1)) * (y - z) <=> x = y)`] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simple_path]) THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real^1`; `y:real^1`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC
   `integral(interval [vec 0,x])
       (\x. vector_derivative g (at x) / (g x - z)) =
       integral(interval [vec 0,y])
       (\x. vector_derivative g (at x) / (g x - z)) +
       Cx(&2) * Cx pi * ii` THEN
  ASM_SIMP_TAC[CX_2PII_NZ; COMPLEX_FIELD
   `~(y = Cx(&0)) ==> (a = b + y <=>
                       Cx(&1) / y * a = Cx(&1) / y * b + Cx(&1))`] THEN
  ASM_REWRITE_TAC[INTEGRAL_REFL; COMPLEX_VEC_0; COMPLEX_MUL_RZERO] THEN
  REWRITE_TAC[integral; ONCE_REWRITE_RULE[COMPLEX_MUL_SYM] complex_div;
              GSYM HAS_PATH_INTEGRAL] THEN
  REWRITE_TAC[GSYM path_integral] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[COMPLEX_MUL_SYM] (GSYM complex_div)] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING `inv(x) = Cx(&1) * inv(x)`] THEN
  REWRITE_TAC[GSYM winding_number; GSYM complex_div] THEN
  DISCH_THEN(MP_TAC o AP_TERM `Re`) THEN
  REWRITE_TAC[RE_ADD; RE_CX] THEN
  UNDISCH_TAC `&1 < Re(winding_number (g,z))` THEN REAL_ARITH_TAC);;

let SIMPLE_CLOSED_PATH_WINDING_NUMBER_CASES = prove
 (`!g z. valid_path g /\ ~(z IN path_image g) /\
         simple_path g /\ pathfinish g = pathstart g
         ==> winding_number(g,z) IN {--Cx(&1),Cx(&0),Cx(&1)}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  MP_TAC(ISPECL [`g:real^1->complex`; `z:complex`]
    INTEGER_WINDING_NUMBER) THEN
  ASM_REWRITE_TAC[complex_integer] THEN STRIP_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (SPEC `Re(winding_number (g,z))` REAL_LT_NEGTOTAL)
  THENL
   [ASM_REWRITE_TAC[COMPLEX_EQ; RE_CX; IM_CX];
    ASM_SIMP_TAC[SIMPLE_CLOSED_PATH_WINDING_NUMBER_POS];
    MP_TAC(ISPECL [`g:real^1->complex`; `z:complex`]
      WINDING_NUMBER_REVERSEPATH) THEN
    ASM_SIMP_TAC[COMPLEX_RING `x = --Cx(&1) <=> --x = Cx(&1)`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISJ1_TAC THEN
    MATCH_MP_TAC SIMPLE_CLOSED_PATH_WINDING_NUMBER_POS THEN
    ASM_SIMP_TAC[WINDING_NUMBER_REVERSEPATH; VALID_PATH_REVERSEPATH;
                 PATH_IMAGE_REVERSEPATH; PATHSTART_REVERSEPATH;
                 PATHFINISH_REVERSEPATH; RE_NEG; SIMPLE_PATH_REVERSEPATH]]);;

(* ------------------------------------------------------------------------- *)
(* For |WN| >= 1 the path must contain points in every direction.            *)
(* We can thus bound the WN of a path that doesn't meet some "cut".          *)
(* ------------------------------------------------------------------------- *)

let WINDING_NUMBER_POS_MEETS = prove
 (`!g z. valid_path g /\ ~(z IN path_image g) /\
         Re(winding_number(g,z)) >= &1
         ==> !w. ~(w = z)
                 ==> ?a. &0 < a /\ z + (Cx a * (w - z)) IN path_image g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. t IN interval[vec 0,vec 1] ==> ~((g:real^1->complex) t = z)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `~((z:complex) IN path_image g)` THEN
    REWRITE_TAC[path_image; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `r:complex = (w - z) / (pathstart g - z)` THEN
  STRIP_ASSUME_TAC(GSYM(SPEC `r:complex` ARG)) THEN
  SUBGOAL_THEN
   `?t. t IN interval[vec 0,vec 1] /\
        Im(integral (interval[vec 0,t])
                    (\x. vector_derivative g (at x) / (g x - z))) = Arg r`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IM_DEF] THEN MATCH_MP_TAC IVT_INCREASING_COMPONENT_ON_1 THEN
    ASM_SIMP_TAC[DIMINDEX_2; DROP_VEC; ARITH; INTEGRAL_REFL; REAL_POS;
                 VEC_COMPONENT] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INDEFINITE_INTEGRAL_CONTINUOUS_RIGHT THEN
      REWRITE_TAC[ONCE_REWRITE_RULE[COMPLEX_MUL_SYM] complex_div] THEN
      REWRITE_TAC[GSYM PATH_INTEGRABLE_ON] THEN
      REWRITE_TAC[SIMPLE_COMPLEX_ARITH `inv z = Cx(&1) / z`] THEN
      MATCH_MP_TAC PATH_INTEGRABLE_INVERSEDIFF THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * pi` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    UNDISCH_TAC `Re(winding_number (g,z)) >= &1` THEN
    REWRITE_TAC[winding_number; GSYM IM_DEF] THEN
    REWRITE_TAC[path_integral; HAS_PATH_INTEGRAL; GSYM integral] THEN
    SUBST1_TAC(COMPLEX_FIELD `ii = --inv ii`) THEN
    REWRITE_TAC[complex_div; COMPLEX_INV_MUL; COMPLEX_INV_NEG] THEN
    REWRITE_TAC[GSYM CX_INV; GSYM CX_MUL; COMPLEX_MUL_ASSOC] THEN
    REWRITE_TAC[RE_MUL_CX; RE; COMPLEX_MUL_RNEG; RE_NEG; COMPLEX_MUL_LNEG;
                COMPLEX_INV_INV; GSYM COMPLEX_MUL_ASSOC; RE_MUL_II] THEN
    REWRITE_TAC[REAL_MUL_RNEG; REAL_NEGNEG] THEN
    SIMP_TAC[REAL_ARITH `((&1 * inv(&2)) * p) * x >= &1 <=> &2 <= x * p`] THEN
    SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ; PI_POS] THEN
    REWRITE_TAC[COMPLEX_MUL_LID; COMPLEX_MUL_AC];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`g:real^1->complex`; `z:complex`; `vec 0:real^1`; `t:real^1`]
   WINDING_NUMBER_AHLFORS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_SUBSET THEN
      EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
      RULE_ASSUM_TAC(REWRITE_RULE[valid_path]) THEN ASM_REWRITE_TAC[];
      ALL_TAC;
      GEN_TAC THEN
      DISCH_THEN(fun th -> FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th)] THEN
    UNDISCH_TAC `(t:real^1) IN interval[vec 0,vec 1]` THEN
    REWRITE_TAC[SUBSET; IN_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[CEXP_NEG] THEN
  ABBREV_TAC `i = integral (interval [vec 0,t])
    (\x. vector_derivative g (at x) / (g x - z))` THEN
  SUBST1_TAC(SPEC `i:complex` COMPLEX_EXPAND) THEN
  ASM_REWRITE_TAC[CEXP_ADD; COMPLEX_INV_MUL; GSYM CX_EXP] THEN
  UNDISCH_TAC `Cx(norm r) * cexp(ii * Cx(Arg r)) = r` THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP (COMPLEX_FIELD
   `x * e = r /\ (y * inv e) * w = z
    ==> ~(e = Cx(&0)) ==> x * y * w = r * z`)) THEN
  REWRITE_TAC[CEXP_NZ] THEN
  EXPAND_TAC "r" THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV) [pathstart] THEN
  SUBGOAL_THEN `~((g:real^1->complex)(vec 0) = z)` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN SIMP_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS];
    ALL_TAC] THEN
  ASM_SIMP_TAC[COMPLEX_DIV_RMUL; COMPLEX_SUB_0; GSYM CX_INV; GSYM CX_MUL;
               COMPLEX_MUL_ASSOC; GSYM real_div] THEN
  DISCH_TAC THEN
  EXISTS_TAC `exp(Re i) / norm(r:complex)` THEN
  SUBGOAL_THEN `~(r = Cx(&0))` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN MATCH_MP_TAC(COMPLEX_FIELD
   `~(x = Cx(&0)) /\ ~(y = Cx(&0)) ==> ~(x / y = Cx(&0))`) THEN
    ASM_REWRITE_TAC[COMPLEX_SUB_0; pathstart];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_EXP_POS_LT; COMPLEX_NORM_NZ] THEN
  REWRITE_TAC[path_image; IN_IMAGE] THEN
  EXISTS_TAC `t:real^1` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(COMPLEX_FIELD
   `inv i * (gt - z) = wz /\ ~(i = Cx(&0)) ==> z + i * wz = gt`) THEN
  ASM_REWRITE_TAC[GSYM CX_INV; REAL_INV_DIV; CX_INJ] THEN
  MATCH_MP_TAC(REAL_FIELD `~(x = &0) /\ ~(y = &0) ==> ~(x / y = &0)`) THEN
  ASM_REWRITE_TAC[REAL_EXP_NZ; COMPLEX_NORM_ZERO]);;

let WINDING_NUMBER_BIG_MEETS = prove
 (`!g z. valid_path g /\ ~(z IN path_image g) /\
         abs(Re(winding_number(g,z))) >= &1
         ==> !w. ~(w = z)
                 ==> ?a. &0 < a /\ z + (Cx a * (w - z)) IN path_image g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_abs] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[WINDING_NUMBER_POS_MEETS] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_SIMP_TAC[GSYM RE_NEG; GSYM WINDING_NUMBER_REVERSEPATH] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM PATH_IMAGE_REVERSEPATH] THEN
  MATCH_MP_TAC WINDING_NUMBER_POS_MEETS THEN
  ASM_SIMP_TAC[PATH_IMAGE_REVERSEPATH; VALID_PATH_REVERSEPATH]);;

let WINDING_NUMBER_LT_1 = prove
 (`!g w z. valid_path g /\ ~(z IN path_image g) /\ ~(w = z) /\
           (!a. &0 < a ==> ~(z + (Cx a * (w - z)) IN path_image g))
           ==> Re(winding_number(g,z)) < &1`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE; GSYM real_ge] THEN
  ASM_MESON_TAC[WINDING_NUMBER_POS_MEETS]);;

(* ------------------------------------------------------------------------- *)
(* One way of proving that WN=1 for a loop.                                  *)
(* ------------------------------------------------------------------------- *)

let WINDING_NUMBER_EQ_1 = prove
 (`!g z. valid_path g /\ ~(z IN path_image g) /\ pathfinish g = pathstart g /\
         &0 < Re(winding_number(g,z)) /\ Re(winding_number(g,z)) < &2
         ==> winding_number(g,z) = Cx(&1)`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 3 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN `complex_integer(winding_number(g,z))` MP_TAC THENL
   [ASM_SIMP_TAC[INTEGER_WINDING_NUMBER]; ALL_TAC] THEN
  SIMP_TAC[complex_integer; COMPLEX_EQ; RE_CX; IM_CX] THEN
  SIMP_TAC[REAL_LT_INTEGERS; INTEGER_CLOSED] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Cauchy's integral formula, again for a convex enclosing set.              *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_INTEGRAL_FORMULA_WEAK = prove
 (`!f s k g z.
        convex s /\ FINITE k /\ f continuous_on s /\
        (!x. x IN interior(s) DIFF k ==> f complex_differentiable at x) /\
        z IN interior(s) DIFF k /\
        valid_path g /\ (path_image g) SUBSET (s DELETE z) /\
        pathfinish g = pathstart g
        ==> ((\w. f(w) / (w - z)) has_path_integral
             (Cx(&2) * Cx(pi) * ii * winding_number(g,z) * f(z))) g`,
  REWRITE_TAC[IN_DIFF] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `z:complex`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[complex_differentiable; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `f':complex` THEN DISCH_TAC THEN MP_TAC(SPECL
   [`\w:complex. if w = z then f' else (f w - f z) / (w - z)`;
    `s:complex->bool`;
    `(z:complex) INSERT k`;
    `g:real^1->complex`] CAUCHY_THEOREM_CONVEX) THEN
  REWRITE_TAC[IN_DIFF; IN_INSERT; DE_MORGAN_THM] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INSERT] THEN REPEAT CONJ_TAC THENL
     [ALL_TAC;
      X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
      MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_TRANSFORM_AT THEN
      EXISTS_TAC `\w:complex. (f w - f z) / (w - z)` THEN
      EXISTS_TAC `dist(w:complex,z)` THEN ASM_SIMP_TAC[DIST_POS_LT] THEN
      CONJ_TAC THENL [MESON_TAC[DIST_SYM; REAL_LT_REFL]; ALL_TAC] THEN
      MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_DIV_AT THEN
      ASM_REWRITE_TAC[COMPLEX_SUB_0] THEN CONJ_TAC THEN
      MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_SUB THEN
      ASM_SIMP_TAC[ETA_AX; COMPLEX_DIFFERENTIABLE_CONST;
                   COMPLEX_DIFFERENTIABLE_ID];
      ASM SET_TAC[]] THEN
    REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
    ASM_CASES_TAC `w:complex = z` THENL
     [ALL_TAC;
      MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN THEN
      EXISTS_TAC `\w:complex. (f w - f z) / (w - z)` THEN
      EXISTS_TAC `dist(w:complex,z)` THEN ASM_SIMP_TAC[DIST_POS_LT] THEN
      CONJ_TAC THENL [MESON_TAC[DIST_SYM; REAL_LT_REFL]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_COMPLEX_DIV_WITHIN THEN
      RULE_ASSUM_TAC(REWRITE_RULE[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]) THEN
      ASM_SIMP_TAC[CONTINUOUS_CONST; CONTINUOUS_SUB; CONTINUOUS_WITHIN_ID;
                   ETA_AX; COMPLEX_SUB_0]] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[CONTINUOUS_WITHIN] THEN
    MATCH_MP_TAC LIM_TRANSFORM_AWAY_WITHIN THEN
    EXISTS_TAC `\w:complex. (f w - f z) / (w - z)` THEN SIMP_TAC[] THEN
    EXISTS_TAC `z + Cx(&1)` THEN
    CONJ_TAC THENL [CONV_TAC COMPLEX_RING; ALL_TAC] THEN
    REWRITE_TAC[GSYM HAS_COMPLEX_DERIVATIVE_WITHIN] THEN
    ASM_SIMP_TAC[HAS_COMPLEX_DERIVATIVE_AT_WITHIN];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g:real^1->complex`; `z:complex`]
    HAS_PATH_INTEGRAL_WINDING_NUMBER) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(f:complex->complex) z` o MATCH_MP
    HAS_PATH_INTEGRAL_COMPLEX_LMUL) THEN REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_PATH_INTEGRAL_ADD) THEN
  REWRITE_TAC[COMPLEX_RING
   `f * Cx(&2) * a * b * c + Cx(&0) = Cx(&2) * a * b * c * f`] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_PATH_INTEGRAL_EQ) THEN
  X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(w:complex = z)` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC COMPLEX_FIELD);;

let CAUCHY_INTEGRAL_FORMULA_CONVEX_SIMPLE = prove
 (`!f s g z.
        convex s /\ f holomorphic_on s /\
        z IN interior(s) /\
        valid_path g /\ (path_image g) SUBSET (s DELETE z) /\
        pathfinish g = pathstart g
        ==> ((\w. f(w) / (w - z)) has_path_integral
             (Cx(&2) * Cx(pi) * ii * winding_number(g,z) * f(z))) g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CAUCHY_INTEGRAL_FORMULA_WEAK THEN
  MAP_EVERY EXISTS_TAC [`s:complex->bool`; `{}:complex->bool`] THEN
  ASM_REWRITE_TAC[DIFF_EMPTY; FINITE_RULES] THEN
  SIMP_TAC[OPEN_INTERIOR; complex_differentiable; GSYM HOLOMORPHIC_ON_OPEN] THEN
  ASM_MESON_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON;
                HOLOMORPHIC_ON_SUBSET; INTERIOR_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Positivity of WN for a linepath.                                          *)
(* ------------------------------------------------------------------------- *)

let WINDING_NUMBER_LINEPATH_POS_LT = prove
 (`!a b z. &0 < Im((b - a) * cnj(b - z))
           ==> &0 < Re(winding_number(linepath(a,b),z))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WINDING_NUMBER_POS_LT THEN
  EXISTS_TAC `Im((b - a) * cnj(b - z))` THEN
  ASM_REWRITE_TAC[VALID_PATH_LINEPATH; VECTOR_DERIVATIVE_LINEPATH_AT] THEN
  CONJ_TAC THENL
   [POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    SPEC_TAC(`z:complex`,`z:complex`) THEN
    REWRITE_TAC[path_image; FORALL_IN_IMAGE; linepath] THEN
    REWRITE_TAC[VECTOR_ARITH
     `b - ((&1 - x) % a + x % b) = (&1 - x) % (b - a)`] THEN
    REWRITE_TAC[COMPLEX_CMUL; CNJ_MUL; CNJ_CX] THEN
    REWRITE_TAC[COMPLEX_RING `a * Cx x * cnj a = Cx x * a * cnj a`] THEN
    SIMP_TAC[COMPLEX_MUL_CNJ; GSYM CX_POW; GSYM CX_MUL; IM_CX; REAL_LT_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `segment[a,b] SUBSET
      {y | Im((b - a) * cnj(b - z)) <= Im((b - a) * cnj(y - z))}`
  MP_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SET_RULE `{a,b} SUBSET {y | P y} <=> P a /\ P b`] THEN
      POP_ASSUM MP_TAC THEN
      REWRITE_TAC[cnj; complex_mul; RE; IM; RE_SUB; IM_SUB] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_SUB_LDISTRIB; IM_SUB; CNJ_SUB; REAL_LE_SUB_LADD] THEN
    REWRITE_TAC[CONVEX_ALT; cnj; complex_mul; RE; IM; RE_SUB; IM_SUB] THEN
    REWRITE_TAC[IN_ELIM_THM; IM_ADD; RE_ADD; IM_CMUL; RE_CMUL] THEN
    REWRITE_TAC[REAL_NEG_ADD; REAL_NEG_RMUL] THEN
    ONCE_REWRITE_TAC[REAL_ARITH
     `e <= ab * ((&1 - u) * x + u * y) + ab' * ((&1 - u) * x' + u * y') <=>
      (&1 - u) * e + u * e <=
        (&1 - u) * (ab * x + ab' * x') + u * (ab * y + ab' * y')`] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM PATH_IMAGE_LINEPATH] THEN
    REWRITE_TAC[SUBSET; path_image; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    ASM_MESON_TAC[SUBSET; INTERVAL_OPEN_SUBSET_CLOSED]]);;

(* ------------------------------------------------------------------------- *)
(* Partial circle path.                                                      *)
(* ------------------------------------------------------------------------- *)

let partcirclepath = new_definition
 `partcirclepath(z,r,s,t) =
    \x. z + Cx(r) * cexp(ii * linepath(Cx(s),Cx(t)) x)`;;

let PATHSTART_PARTCIRCLEPATH = prove
 (`!r z s t. pathstart(partcirclepath(z,r,s,t)) =
                z + Cx(r) * cexp(ii * Cx(s))`,
  REWRITE_TAC[pathstart; partcirclepath;
              REWRITE_RULE[pathstart] PATHSTART_LINEPATH]);;

let PATHFINISH_PARTCIRCLEPATH = prove
 (`!r z s t. pathfinish(partcirclepath(z,r,s,t)) =
                z + Cx(r) * cexp(ii * Cx(t))`,
  REWRITE_TAC[pathfinish; partcirclepath;
              REWRITE_RULE[pathfinish] PATHFINISH_LINEPATH]);;

let HAS_VECTOR_DERIVATIVE_PARTCIRCLEPATH = prove
 (`!z r s t x.
        ((partcirclepath(z,r,s,t)) has_vector_derivative
         (ii * Cx(r) * (Cx t - Cx s) * cexp(ii * linepath(Cx(s),Cx(t)) x)))
        (at x)`,
  REWRITE_TAC[partcirclepath; linepath; COMPLEX_CMUL; CX_SUB] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_REAL_COMPLEX THEN
  COMPLEX_DIFF_TAC THEN CONV_TAC COMPLEX_RING);;

let VECTOR_DERIVATIVE_PARTCIRCLEPATH = prove
 (`!z r s t x.
        vector_derivative (partcirclepath(z,r,s,t)) (at x) =
        ii * Cx(r) * (Cx t - Cx s) * cexp(ii * linepath(Cx(s),Cx(t)) x)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
  REWRITE_TAC[HAS_VECTOR_DERIVATIVE_PARTCIRCLEPATH]);;

let VALID_PATH_PARTCIRCLEPATH = prove
 (`!z r s t. valid_path(partcirclepath(z,r,s,t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[valid_path] THEN
  MATCH_MP_TAC DIFFERENTIABLE_ON_IMP_PIECEWISE_DIFFERENTIABLE THEN
  REWRITE_TAC[differentiable_on] THEN X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN
  MATCH_MP_TAC DIFFERENTIABLE_AT_WITHIN THEN
  REWRITE_TAC[VECTOR_DERIVATIVE_WORKS; VECTOR_DERIVATIVE_PARTCIRCLEPATH;
              HAS_VECTOR_DERIVATIVE_PARTCIRCLEPATH]);;

let PATH_PARTCIRCLEPATH = prove
 (`!z r s t. path(partcirclepath(z,r,s,t))`,
  SIMP_TAC[VALID_PATH_PARTCIRCLEPATH; VALID_PATH_IMP_PATH]);;

let PATH_IMAGE_PARTCIRCLEPATH = prove
 (`!z r s t.
        &0 <= r /\ s <= t
        ==> path_image(partcirclepath(z,r,s,t)) =
                {z + Cx(r) * cexp(ii * Cx x) | s <= x /\ x <= t}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[path_image; partcirclepath] THEN
  REWRITE_TAC[EXTENSION; TAUT `(a <=> b) <=> (a ==> b) /\ (b ==> a)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
    DISCH_TAC THEN EXISTS_TAC `(&1 - drop x) * s + drop x * t` THEN
    REWRITE_TAC[linepath; CX_ADD; CX_SUB; COMPLEX_CMUL; CX_MUL] THEN
    REWRITE_TAC[REAL_ARITH `s <= (&1 - x) * s + x * t <=> &0 <= x * (t - s)`;
      REAL_ARITH `(&1 - x) * s + x * t <= t <=> &0 <= (&1 - x) * (t - s)`] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_SUB_LE];
    ALL_TAC] THEN
  X_GEN_TAC `w:complex` THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[IN_IMAGE] THEN ASM_CASES_TAC `s:real < t` THENL
   [EXISTS_TAC `lift((x - s) / (t - s))` THEN
    ASM_SIMP_TAC[IN_INTERVAL_1; REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_SUB_LT;
                 LIFT_DROP; DROP_VEC; linepath; REAL_MUL_LZERO; REAL_MUL_LID;
                 REAL_SUB_LE; REAL_ARITH `x - s:real <= t - s <=> x <= t`] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[COMPLEX_CMUL; CX_SUB; CX_DIV] THEN
    SUBGOAL_THEN `~(Cx(s) = Cx(t))` MP_TAC THENL
     [ASM_SIMP_TAC[CX_INJ; REAL_LT_IMP_NE]; CONV_TAC COMPLEX_FIELD];
    UNDISCH_TAC `s:real <= t` THEN ASM_REWRITE_TAC[REAL_LE_LT] THEN
    DISCH_THEN SUBST_ALL_TAC THEN EXISTS_TAC `vec 0:real^1` THEN
    SIMP_TAC[IN_INTERVAL_1; DROP_VEC; linepath; VECTOR_MUL_LZERO;
             REAL_SUB_RZERO; VECTOR_MUL_LID; VECTOR_ADD_RID; REAL_POS] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[CX_INJ] THEN ASM_REAL_ARITH_TAC]);;

let PATH_IMAGE_PARTCIRCLEPATH_SUBSET = prove
 (`!z r s t.
        &0 <= r /\ s <= t
        ==> path_image(partcirclepath(z,r,s,t)) SUBSET
                {w | norm(w - z) = r}`,
  SIMP_TAC[PATH_IMAGE_PARTCIRCLEPATH] THEN
  SIMP_TAC[SUBSET; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[COMPLEX_ADD_SUB; COMPLEX_NORM_MUL; NORM_CEXP; COMPLEX_NORM_CX;
              RE_MUL_II; IM_CX; REAL_NEG_0; REAL_EXP_0] THEN
  REAL_ARITH_TAC);;

let IN_PATH_IMAGE_PARTCIRCLEPATH = prove
 (`!z r s t w.
        &0 <= r /\ s <= t /\ w IN path_image(partcirclepath(z,r,s,t))
        ==> norm(w - z) = r`,
  MP_TAC PATH_IMAGE_PARTCIRCLEPATH_SUBSET THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN SET_TAC[]);;

let HAS_PATH_INTEGRAL_BOUND_PARTCIRCLEPATH_STRONG = prove
 (`!f i z r s t B k.
        FINITE k /\
        (f has_path_integral i) (partcirclepath(z,r,s,t)) /\
        &0 <= B /\ &0 < r /\ s <= t /\
        (!x. x IN path_image(partcirclepath(z,r,s,t)) DIFF k
             ==> norm(f x) <= B)
        ==> norm(i) <= B * r * (t - s)`,
  let lemma1 = prove
   (`!b w. FINITE {z | norm(z) <= b /\ cexp(z) = w}`,
    REPEAT GEN_TAC THEN ASM_CASES_TAC `w = Cx(&0)` THEN
    ASM_REWRITE_TAC[CEXP_NZ; SET_RULE `{x | F} = {}`; FINITE_RULES] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP CEXP_CLOG) THEN
    REWRITE_TAC[CEXP_EQ] THEN
    REWRITE_TAC[SET_RULE
     `{z | P z /\ ?n. Q n /\ z = f n} = IMAGE f {n | Q n /\ P(f n)}`] THEN
    MATCH_MP_TAC FINITE_IMAGE THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{n | integer n /\
                     norm(Cx (&2 * n * pi) * ii) <= b + norm(clog w)}` THEN
    CONJ_TAC THENL
     [ALL_TAC; SIMP_TAC[SUBSET; IN_ELIM_THM] THEN NORM_ARITH_TAC] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; COMPLEX_NORM_II] THEN
    REWRITE_TAC[REAL_MUL_RID; REAL_ABS_MUL; REAL_ABS_NUM; REAL_ABS_PI] THEN
    ASM_SIMP_TAC[REAL_MUL_ASSOC; GSYM REAL_LE_RDIV_EQ; PI_POS] THEN
    REWRITE_TAC[REAL_ARITH `&2 * x <= a <=> x <= a / &2`] THEN
    REWRITE_TAC[GSYM REAL_BOUNDS_LE; FINITE_INTSEG]) in
  let lemma2 = prove
   (`!a b. ~(a = Cx(&0)) ==> FINITE {z | norm(z) <= b /\ cexp(a * z) = w}`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC
     `IMAGE (\z. z / a) {z | norm(z) <= b * norm(a) /\ cexp(z) = w}` THEN
    SIMP_TAC[lemma1; FINITE_IMAGE] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[COMPLEX_FIELD `~(a = Cx(&0)) ==> (x = y / a <=> a * x = y)`;
                 UNWIND_THM1; COMPLEX_NORM_MUL; REAL_LE_LMUL; NORM_POS_LE]) in
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_PATH_INTEGRAL] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `s <= t`) THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
  STRIP_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REPEAT(POP_ASSUM MP_TAC) THEN
    REWRITE_TAC[VECTOR_DERIVATIVE_PARTCIRCLEPATH] THEN
    REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO] THEN
    SIMP_TAC[GSYM COMPLEX_VEC_0; HAS_INTEGRAL_0_EQ; NORM_0] THEN
    REAL_ARITH_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  REWRITE_TAC[GSYM CONTENT_UNIT_1] THEN MATCH_MP_TAC HAS_INTEGRAL_BOUND THEN
  EXISTS_TAC `\x. if (partcirclepath(z,r,s,t) x) IN k then Cx(&0)
                  else f(partcirclepath(z,r,s,t) x) *
                       vector_derivative (partcirclepath(z,r,s,t)) (at x)` THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE; REAL_SUB_LE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HAS_INTEGRAL_SPIKE THEN
    EXISTS_TAC `\x. f(partcirclepath(z,r,s,t) x) *
                    vector_derivative (partcirclepath(z,r,s,t)) (at x)` THEN
    EXISTS_TAC `{x | x IN interval[vec 0,vec 1] /\
                     (partcirclepath(z,r,s,t) x) IN k}` THEN
    ASM_SIMP_TAC[IN_DIFF; IN_ELIM_THM; IMP_CONJ] THEN
    MATCH_MP_TAC NEGLIGIBLE_FINITE THEN
    MATCH_MP_TAC FINITE_FINITE_PREIMAGE_GENERAL THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
    REWRITE_TAC[partcirclepath] THEN
    ASM_SIMP_TAC[CX_INJ; REAL_LT_IMP_NZ; COMPLEX_FIELD
     `~(r = Cx(&0)) ==> (z + r * e = y <=> e = (y - z) / r)`] THEN
    REWRITE_TAC[linepath; COMPLEX_CMUL] THEN
    REWRITE_TAC[GSYM CX_MUL; GSYM CX_ADD] THEN
    REWRITE_TAC[REAL_ARITH `(&1 - t) * x + t * y = x + t * (y - x)`] THEN
    REWRITE_TAC[CX_ADD; COMPLEX_ADD_LDISTRIB; CEXP_ADD] THEN
    SIMP_TAC[CEXP_NZ; COMPLEX_FIELD
     `~(e = Cx(&0)) ==> (e * x = y <=> x = y / e)`] THEN
    ABBREV_TAC `w = (y - z) / Cx r / cexp(ii * Cx s)` THEN
    REWRITE_TAC[CX_MUL; COMPLEX_RING
     `ii * Cx x * Cx(t - s) = (ii * Cx(t - s)) * Cx x`] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC
     `{x | Cx(drop x) IN
           {z | norm(z) <= &1 /\ cexp((ii * Cx(t - s)) * z) = w}}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE_INJ THEN REWRITE_TAC[CX_INJ; DROP_EQ] THEN
      MATCH_MP_TAC lemma2 THEN
      REWRITE_TAC[COMPLEX_RING `ii * x = Cx(&0) <=> x = Cx(&0)`] THEN
      ASM_SIMP_TAC[CX_INJ; REAL_SUB_0; REAL_LT_IMP_NE];
      SIMP_TAC[SUBSET; IN_ELIM_THM; IN_INTERVAL_1; DROP_VEC] THEN
      SIMP_TAC[COMPLEX_NORM_CX] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[COMPLEX_NORM_0] THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_SUB_LE] THEN
  REWRITE_TAC[VECTOR_DERIVATIVE_PARTCIRCLEPATH] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; COMPLEX_NORM_II] THEN
  REWRITE_TAC[REAL_ABS_NUM; REAL_MUL_LID] THEN
  REWRITE_TAC[NORM_CEXP; RE_MUL_II; IM_LINEPATH_CX] THEN
  REWRITE_TAC[REAL_EXP_0; REAL_NEG_0; REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[path_image] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[REAL_LE_MUL; NORM_POS_LE; REAL_ABS_POS] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_SIMP_TAC[NORM_POS_LE; GSYM CX_SUB; COMPLEX_NORM_CX] THEN
  ASM_REAL_ARITH_TAC);;

let HAS_PATH_INTEGRAL_BOUND_PARTCIRCLEPATH = prove
 (`!f i z r s t B.
        (f has_path_integral i) (partcirclepath(z,r,s,t)) /\
        &0 <= B /\ &0 < r /\ s <= t /\
        (!x. x IN path_image(partcirclepath(z,r,s,t))
             ==> norm(f x) <= B)
        ==> norm(i) <= B * r * (t - s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_BOUND_PARTCIRCLEPATH_STRONG THEN
  MAP_EVERY EXISTS_TAC
   [`f:complex->complex`; `z:complex`; `{}:complex->bool`] THEN
  ASM_REWRITE_TAC[FINITE_RULES; IN_DIFF; NOT_IN_EMPTY]);;

let PATH_INTEGRABLE_CONTINUOUS_PARTCIRCLEPATH = prove
 (`!f z r s t. f continuous_on path_image(partcirclepath(z,r,s,t))
               ==> f path_integrable_on (partcirclepath(z,r,s,t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[path_integrable_on; HAS_PATH_INTEGRAL] THEN
  REWRITE_TAC[VECTOR_DERIVATIVE_PARTCIRCLEPATH; GSYM integrable_on] THEN
  DISCH_TAC THEN MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    ASM_REWRITE_TAC[GSYM path_image; ETA_AX] THEN
    MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
    ASM_REWRITE_TAC[GSYM valid_path; VALID_PATH_PARTCIRCLEPATH];
    ALL_TAC] THEN
  REWRITE_TAC[linepath] THEN
  REPEAT(MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
         REWRITE_TAC[CONTINUOUS_ON_CONST]) THEN
  ONCE_REWRITE_TAC[GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  REWRITE_TAC[CONTINUOUS_ON_CEXP] THEN
  REPEAT(MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
         REWRITE_TAC[CONTINUOUS_ON_CONST]) THEN
  REWRITE_TAC[VECTOR_ARITH `(&1 - x) % s + x % t = s + x % (t - s)`] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
  REWRITE_TAC[linear; DROP_ADD; DROP_CMUL; CX_ADD; COMPLEX_CMUL; CX_MUL;
              CX_SUB] THEN
  CONV_TAC COMPLEX_RING);;

let WINDING_NUMBER_PARTCIRCLEPATH_POS_LT = prove
 (`!r z s t w.
        s < t /\ norm(w - z) < r
        ==> &0 < Re(winding_number(partcirclepath(z,r,s,t),w))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WINDING_NUMBER_POS_LT THEN
  EXISTS_TAC `r * (t - s) * (r - norm(w - z:complex))` THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
   `n < r ==> &0 <= n ==> &0 < r`)) THEN
  REWRITE_TAC[NORM_POS_LE] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[REAL_LT_MUL; REAL_SUB_LT; VALID_PATH_PARTCIRCLEPATH] THEN
  ASM_REWRITE_TAC[VALID_PATH_PARTCIRCLEPATH] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[IN_PATH_IMAGE_PARTCIRCLEPATH; REAL_LT_IMP_LE; REAL_LT_REFL];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
  REWRITE_TAC[VECTOR_DERIVATIVE_PARTCIRCLEPATH] THEN
  REWRITE_TAC[partcirclepath] THEN
  REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC; IM_MUL_II; RE_MUL_CX; GSYM CX_SUB] THEN
  REWRITE_TAC[CNJ_ADD; CNJ_SUB; CNJ_MUL; CNJ_CX] THEN
  REWRITE_TAC[COMPLEX_RING
   `c * ((z + r * c') - w):complex = r * c * c' - c * (w - z)`] THEN
  REWRITE_TAC[COMPLEX_MUL_CNJ; NORM_CEXP; RE_MUL_II] THEN
  REWRITE_TAC[IM_LINEPATH_CX; REAL_NEG_0; REAL_EXP_0; COMPLEX_MUL_RID;
              COMPLEX_POW_2] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_SUB_LT; RE_SUB; RE_CX] THEN
  MATCH_MP_TAC(REAL_ARITH
   `norm(x) <= norm(y) /\ abs(Re(x)) <= norm(x)
    ==> r - norm(y) <= r - Re x`) THEN
  REWRITE_TAC[COMPLEX_NORM_GE_RE_IM] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; NORM_CEXP; RE_MUL_II; IM_LINEPATH_CX] THEN
  REWRITE_TAC[REAL_EXP_0; REAL_NEG_0; REAL_MUL_LID; GSYM CNJ_SUB] THEN
  REWRITE_TAC[COMPLEX_NORM_CNJ; REAL_LE_REFL]);;

let SIMPLE_PATH_PARTCIRCLEPATH = prove
 (`!z r s t. simple_path(partcirclepath(z,r,s,t)) <=>
                ~(r = &0) /\ ~(s = t) /\ abs(s - t) <= &2 * pi`,
  let lemma = prove
   (`(!x y. (&0 <= x /\ x <= &1) /\ (&0 <= y /\ y <= &1) ==> P(abs(x - y))) <=>
     (!x. &0 <= x /\ x <= &1 ==> P x)`,
    MESON_TAC[REAL_ARITH `(&0 <= x /\ x <= &1) /\ (&0 <= y /\ y <= &1)
                          ==> &0 <= abs(x - y) /\ abs(x - y) <= &1`;
              REAL_ARITH `&0 <= &0 /\ &0 <= &1`;
              REAL_ARITH `(&0 <= x ==> abs(x - &0) = x)`]) in
  REPEAT GEN_TAC THEN REWRITE_TAC[simple_path; PATH_PARTCIRCLEPATH] THEN
  REWRITE_TAC[partcirclepath] THEN
  SIMP_TAC[COMPLEX_RING `z + r * x = z + r * y <=> r * (x - y) = Cx(&0)`] THEN
  REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ] THEN
  ASM_CASES_TAC `r = &0` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_THEN(MP_TAC o SPECL [`lift(&1 / &3)`; `lift(&1 / &2)`]) THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; GSYM LIFT_NUM; LIFT_EQ] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_CASES_TAC `s:real = t` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_THEN(MP_TAC o SPECL [`lift(&1 / &3)`; `lift(&1 / &2)`]) THEN
    REWRITE_TAC[linepath; VECTOR_ARITH `(&1 - t) % x + t % x = x`] THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; GSYM LIFT_NUM; LIFT_EQ] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[COMPLEX_SUB_0];
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_SUB_0; CEXP_EQ] THEN
  REWRITE_TAC[COMPLEX_RING
   `ii * x = ii * y + z * ii <=> ii * (x - (y + z)) = Cx(&0)`] THEN
  REWRITE_TAC[COMPLEX_ENTIRE; II_NZ; LINEPATH_CX] THEN
  REWRITE_TAC[GSYM CX_SUB; GSYM CX_ADD; CX_INJ] THEN
  REWRITE_TAC[REAL_ARITH
   `((&1 - x) * s + x * t) - (((&1 - y) * s + y * t) + z) = &0 <=>
    (x - y) * (t - s) = z`] THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_VEC; IN_INTERVAL_1] THEN
  SIMP_TAC[REAL_ARITH
   `&0 <= x /\ x <= &1 /\ &0 <= y /\ y <= &1
    ==> (x = y \/ x = &0 /\ y = &1 \/ x = &1 /\ y = &0 <=>
         abs(x - y) = &0 \/ abs(x - y) = &1)`] THEN
  SIMP_TAC[PI_POS; REAL_FIELD
   `&0 < pi ==> (x = &2 * n * pi <=> n = x / (&2 * pi))`] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[CONJ_SYM] UNWIND_THM2] THEN
  ONCE_REWRITE_TAC[GSYM INTEGER_ABS] THEN
  REWRITE_TAC[GSYM FORALL_DROP; REAL_ABS_MUL; REAL_ABS_DIV] THEN
  REWRITE_TAC[REAL_ABS_NUM; REAL_ABS_PI] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`] THEN
  REWRITE_TAC[lemma] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `(&2 * pi) / abs(t - s)`) THEN
    ASM_SIMP_TAC[REAL_ABS_SUB; REAL_FIELD
     `~(s = t) ==> x / abs(s - t) * abs(s - t) = x`] THEN
    ASM_SIMP_TAC[PI_POS; INTEGER_CLOSED; REAL_FIELD
     `&0 < pi ==> (&2 * pi) / (&2 * pi) = &1`] THEN
    ASM_SIMP_TAC[REAL_EQ_LDIV_EQ; REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ;
                 GSYM REAL_ABS_NZ; REAL_SUB_0] THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC;
    DISCH_TAC THEN X_GEN_TAC `x:real` THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
       REAL_ABS_INTEGER_LEMMA)) THEN
    SIMP_TAC[REAL_ABS_DIV; REAL_ABS_MUL; REAL_ABS_ABS; REAL_ABS_NUM;
             REAL_ABS_PI] THEN
    SIMP_TAC[REAL_EQ_LDIV_EQ; REAL_LE_RDIV_EQ; PI_POS; REAL_LT_MUL;
             REAL_OF_NUM_LT; ARITH] THEN
    ASM_CASES_TAC `x = &0` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
    ASM_REWRITE_TAC[REAL_ENTIRE; REAL_MUL_LID;
                    REAL_ARITH `abs(t - s) = &0 <=> s = t`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
     `p <= x * abs(s - t)
      ==> abs(s - t) <= p ==> &1 * abs(s - t) <= x * abs(s - t)`)) THEN
    ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ; GSYM REAL_ABS_NZ; REAL_SUB_0] THEN
    ASM_REAL_ARITH_TAC]);;

let ARC_PARTCIRCLEPATH = prove
 (`!z r s t. ~(r = &0) /\ ~(s = t) /\ abs(s - t) < &2 * pi
             ==> arc(partcirclepath(z,r,s,t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[arc; PATH_PARTCIRCLEPATH] THEN
  REWRITE_TAC[partcirclepath] THEN
  SIMP_TAC[COMPLEX_RING `z + r * x = z + r * y <=> r * (x - y) = Cx(&0)`] THEN
  ASM_REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ] THEN
  REWRITE_TAC[COMPLEX_SUB_0; CEXP_EQ] THEN
  REWRITE_TAC[COMPLEX_RING
   `ii * x = ii * y + z * ii <=> ii * (x - (y + z)) = Cx(&0)`] THEN
  REWRITE_TAC[COMPLEX_ENTIRE; II_NZ; LINEPATH_CX] THEN
  REWRITE_TAC[GSYM CX_SUB; GSYM CX_ADD; CX_INJ] THEN
  REWRITE_TAC[REAL_ARITH
   `((&1 - x) * s + x * t) - (((&1 - y) * s + y * t) + z) = &0 <=>
    (x - y) * (t - s) = z`] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `n:real` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_CASES_TAC `n = &0` THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ENTIRE; REAL_SUB_0;
                  DROP_EQ] THEN
  MP_TAC(SPEC `n:real` REAL_ABS_INTEGER_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC(REAL_ARITH `abs x < abs y ==> ~(x = y)`) THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM; REAL_ABS_PI] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&1 * &2 * pi` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[REAL_ARITH `&2 * n * pi = n * &2 * pi`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&1 * abs(t - s)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[REAL_MUL_LID] THEN ASM_MESON_TAC[REAL_ABS_SUB]] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1])) THEN
  REWRITE_TAC[DROP_VEC] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Special case of one complete circle.                                      *)
(* ------------------------------------------------------------------------- *)

let circlepath = new_definition
 `circlepath(z,r) = partcirclepath(z,r,&0,&2 * pi)`;;

let CIRCLEPATH = prove
 (`circlepath(z,r) = \x. z + Cx(r) * cexp(Cx(&2) * Cx pi * ii * Cx(drop x))`,
  REWRITE_TAC[circlepath; partcirclepath; linepath; COMPLEX_CMUL] THEN
  REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_ADD_LID] THEN
  REWRITE_TAC[CX_MUL; COMPLEX_MUL_AC]);;

let PATHSTART_CIRCLEPATH = prove
 (`!r z. pathstart(circlepath(z,r)) = z + Cx(r)`,
  REWRITE_TAC[circlepath; PATHSTART_PARTCIRCLEPATH] THEN
  REWRITE_TAC[COMPLEX_MUL_RZERO; CEXP_0; COMPLEX_MUL_RID]);;

let PATHFINISH_CIRCLEPATH = prove
 (`!r z. pathfinish(circlepath(z,r)) = z + Cx(r)`,
  REWRITE_TAC[circlepath; PATHFINISH_PARTCIRCLEPATH] THEN
  REWRITE_TAC[CEXP_EULER; GSYM CX_COS; GSYM CX_SIN] THEN
  REWRITE_TAC[SIN_NPI; COS_NPI; REAL_POW_NEG; ARITH; REAL_POW_ONE] THEN
  CONV_TAC COMPLEX_RING);;

let HAS_VECTOR_DERIVATIVE_CIRCLEPATH = prove
 (`((circlepath (z,r)) has_vector_derivative
    (Cx(&2) * Cx(pi) * ii * Cx(r) * cexp(Cx(&2) * Cx pi * ii * Cx(drop x))))
   (at x)`,
  REWRITE_TAC[CIRCLEPATH] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_REAL_COMPLEX THEN
  COMPLEX_DIFF_TAC THEN CONV_TAC COMPLEX_RING);;

let VECTOR_DERIVATIVE_CIRCLEPATH = prove
 (`vector_derivative (circlepath (z,r)) (at x) =
        Cx(&2) * Cx(pi) * ii * Cx(r) * cexp(Cx(&2) * Cx pi * ii * Cx(drop x))`,
  MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
  REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CIRCLEPATH]);;

let VALID_PATH_CIRCLEPATH = prove
 (`!z r. valid_path (circlepath(z,r))`,
  REWRITE_TAC[circlepath; VALID_PATH_PARTCIRCLEPATH]);;

let PATH_IMAGE_CIRCLEPATH = prove
 (`!z r. &0 <= r ==> path_image (circlepath(z,r)) = {w | norm(w - z) = r}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CIRCLEPATH; path_image] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_ELIM_THM; COMPLEX_RING `(z + r) - z = r:complex`] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; NORM_CEXP] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[COMPLEX_RING
     `Cx(&2) * p * i * z = (Cx(&2) * p * z) * i`] THEN
    REWRITE_TAC[RE_MUL_II; GSYM CX_MUL; IM_CX] THEN
    REWRITE_TAC[REAL_EXP_NEG; REAL_EXP_0; REAL_MUL_RID; COMPLEX_NORM_CX] THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `x:complex` THEN DISCH_TAC THEN ABBREV_TAC `w:complex = x - z` THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (COMPLEX_RING
   `x - z = w:complex ==> x = z + w`)) THEN
  REWRITE_TAC[IN_IMAGE; COMPLEX_RING `z + a = z + b:complex <=> a = b`] THEN
  ASM_CASES_TAC `w = Cx(&0)` THENL
   [UNDISCH_THEN `norm(w:complex) = r` (MP_TAC o SYM) THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_0; REAL_ABS_ZERO] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[COMPLEX_MUL_LZERO] THEN
    REWRITE_TAC[MEMBER_NOT_EMPTY; INTERVAL_EQ_EMPTY_1; DROP_VEC] THEN
    REWRITE_TAC[REAL_NOT_LT; REAL_POS];
    ALL_TAC] THEN
  MP_TAC(SPECL [`Re(w / Cx(norm w))`; `Im(w / Cx(norm w))`]
    SINCOS_TOTAL_2PI) THEN
  REWRITE_TAC[GSYM COMPLEX_SQNORM] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[REAL_DIV_REFL; REAL_POW_ONE; COMPLEX_NORM_ZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` (STRIP_ASSUME_TAC o GSYM)) THEN
  EXISTS_TAC `lift(t / (&2 * pi))` THEN
  ONCE_REWRITE_TAC[COMPLEX_RING
     `Cx(&2) * p * i * z = i * (Cx(&2) * p * z)`] THEN
  REWRITE_TAC[CEXP_EULER; LIFT_DROP; CX_DIV; CX_MUL] THEN
  ASM_SIMP_TAC[CX_PI_NZ; COMPLEX_FIELD
   `~(p = Cx(&0)) ==> Cx(&2) * p * t / (Cx(&2) * p) = t`] THEN
  ASM_REWRITE_TAC[GSYM CX_COS; GSYM CX_SIN] THEN CONJ_TAC THENL
   [REWRITE_TAC[complex_div; GSYM CX_INV] THEN
    REWRITE_TAC[SIMPLE_COMPLEX_ARITH `Re(w * Cx x) = Re(w) * x`;
                SIMPLE_COMPLEX_ARITH `Im(w * Cx x) = Im(w) * x`] THEN
    REWRITE_TAC[COMPLEX_ADD_LDISTRIB; GSYM CX_MUL] THEN
    SUBGOAL_THEN `!z:real. r * z * inv r = z` MP_TAC THENL
     [SUBGOAL_THEN `~(r = &0)` MP_TAC THENL [ALL_TAC; CONV_TAC REAL_FIELD] THEN
      ASM_MESON_TAC[COMPLEX_NORM_ZERO];
      ONCE_REWRITE_TAC[COMPLEX_RING `t * ii * s = ii * t * s`] THEN
      SIMP_TAC[GSYM CX_MUL; GSYM COMPLEX_EXPAND]];
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_LT_MUL;
                 PI_POS; REAL_OF_NUM_LT; ARITH] THEN
    ASM_REAL_ARITH_TAC]);;

let HAS_PATH_INTEGRAL_BOUND_CIRCLEPATH_STRONG = prove
 (`!f i z r B k.
        FINITE k /\
        (f has_path_integral i) (circlepath(z,r)) /\
        &0 <= B /\ &0 < r /\
        (!x. norm(x - z) = r /\ ~(x IN k) ==> norm(f x) <= B)
        ==> norm(i) <= B * (&2 * pi * r)`,
  REWRITE_TAC[circlepath] THEN REPEAT STRIP_TAC THEN
  SUBST1_TAC(REAL_ARITH `B * (&2 * pi * r) = B * r * (&2 * pi - &0)`) THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_BOUND_PARTCIRCLEPATH_STRONG THEN
  MAP_EVERY EXISTS_TAC
   [`f:complex->complex`; `z:complex`; `k:complex->bool`] THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE; PI_POS; IN_DIFF] THEN
  ASM_SIMP_TAC[PATH_IMAGE_CIRCLEPATH; GSYM circlepath; REAL_LT_IMP_LE] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM]);;

let HAS_PATH_INTEGRAL_BOUND_CIRCLEPATH = prove
 (`!f i z r B.
        (f has_path_integral i) (circlepath(z,r)) /\
        &0 <= B /\ &0 < r /\ (!x. norm(x - z) = r ==> norm(f x) <= B)
        ==> norm(i) <= B * (&2 * pi * r)`,
  REWRITE_TAC[circlepath] THEN REPEAT STRIP_TAC THEN
  SUBST1_TAC(REAL_ARITH `B * (&2 * pi * r) = B * r * (&2 * pi - &0)`) THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_BOUND_PARTCIRCLEPATH THEN
  MAP_EVERY EXISTS_TAC [`f:complex->complex`; `z:complex`] THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE; PI_POS] THEN
  ASM_SIMP_TAC[PATH_IMAGE_CIRCLEPATH; GSYM circlepath; REAL_LT_IMP_LE] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM]);;

let PATH_INTEGRABLE_CONTINUOUS_CIRCLEPATH = prove
 (`!f z r. f continuous_on path_image(circlepath(z,r))
           ==> f path_integrable_on (circlepath(z,r))`,
  SIMP_TAC[PATH_INTEGRABLE_CONTINUOUS_PARTCIRCLEPATH; circlepath]);;

let SIMPLE_PATH_CIRCLEPATH = prove
 (`!z r. simple_path(circlepath(z,r)) <=> ~(r = &0)`,
  REWRITE_TAC[circlepath; SIMPLE_PATH_PARTCIRCLEPATH] THEN
  MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let WINDING_NUMBER_CIRCLEPATH = prove
 (`!z r w. norm(w - z) < r ==> winding_number(circlepath(z,r),w) = Cx(&1)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SIMPLE_CLOSED_PATH_WINDING_NUMBER_POS THEN
  REWRITE_TAC[VALID_PATH_CIRCLEPATH; SIMPLE_PATH_CIRCLEPATH;
              PATHSTART_CIRCLEPATH; PATHFINISH_CIRCLEPATH; CONJ_ASSOC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
     `n < r ==> (&0 <= n ==> &0 <= r /\ &0 < r) /\ n < r`)) THEN
    SIMP_TAC[NORM_POS_LE; PATH_IMAGE_CIRCLEPATH; IN_ELIM_THM] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[circlepath] THEN
    MATCH_MP_TAC WINDING_NUMBER_PARTCIRCLEPATH_POS_LT THEN
    ASM_SIMP_TAC[REAL_LT_MUL; PI_POS; REAL_OF_NUM_LT; ARITH]]);;

(* ------------------------------------------------------------------------- *)
(* Hence the Cauchy formula for points inside a circle.                      *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_INTEGRAL_CIRCLEPATH = prove
 (`!f z r w.
        f continuous_on cball(z,r) /\
        f holomorphic_on ball(z,r) /\
        w IN ball(z,r)
        ==> ((\u. f(u) / (u - w)) has_path_integral
             (Cx(&2) * Cx(pi) * ii * f(w))) (circlepath(z,r))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`f:complex->complex`; `cball(z:complex,r)`;
                `{}:complex->bool`; `circlepath(z,r)`; `w:complex`]
               CAUCHY_INTEGRAL_FORMULA_WEAK) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_BALL]) THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[WINDING_NUMBER_CIRCLEPATH; COMPLEX_MUL_LID] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[VALID_PATH_CIRCLEPATH; PATHSTART_CIRCLEPATH; FINITE_RULES;
       PATHFINISH_CIRCLEPATH; CONVEX_CBALL; INTERIOR_CBALL; DIFF_EMPTY] THEN
  REWRITE_TAC[complex_differentiable] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[HOLOMORPHIC_ON_OPEN; OPEN_BALL]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
   `n < r ==> &0 <= n ==> &0 <= r`)) THEN
  SIMP_TAC[NORM_POS_LE; PATH_IMAGE_CIRCLEPATH] THEN DISCH_TAC THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DELETE; IN_CBALL] THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN SIMP_TAC[dist; REAL_LE_REFL] THEN
  ASM_MESON_TAC[REAL_LT_REFL]);;

let CAUCHY_INTEGRAL_CIRCLEPATH_SIMPLE = prove
 (`!f z r w.
        f holomorphic_on cball(z,r) /\ w IN ball(z,r)
        ==> ((\u. f(u) / (u - w)) has_path_integral
             (Cx(&2) * Cx(pi) * ii * f(w))) (circlepath(z,r))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CAUCHY_INTEGRAL_CIRCLEPATH THEN
  ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON] THEN
  ASM_MESON_TAC[BALL_SUBSET_CBALL; HOLOMORPHIC_ON_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Uniform convergence of path integral (just for circle path so far).       *)
(* ------------------------------------------------------------------------- *)

let PATH_INTEGRAL_UNIFORM_LIMIT_CIRCLEPATH = prove
 (`!net f l z r.
     &0 < r /\ ~(trivial_limit net) /\
     eventually (\n:A. (f n) path_integrable_on circlepath(z,r)) net /\
     (!e. &0 < e
          ==> eventually (\n. !x. x IN path_image (circlepath(z,r))
                                  ==> norm(f n x - l x) < e) net)
     ==> l path_integrable_on circlepath(z,r) /\
         ((\n. path_integral (circlepath(z,r)) (f n))
          --> path_integral (circlepath(z,r)) l) net`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `g = circlepath(z,r)` THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REWRITE_TAC[path_integrable_on; HAS_PATH_INTEGRAL; GSYM integrable_on] THEN
    MATCH_MP_TAC INTEGRABLE_UNIFORM_LIMIT THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / (&2 * pi * r)`) THEN
    ASM_SIMP_TAC[REAL_LT_MUL; PI_POS; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    UNDISCH_TAC `eventually (\n:A. (f n) path_integrable_on g) net` THEN
    REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
    DISCH_THEN(MP_TAC o MATCH_MP EVENTUALLY_HAPPENS) THEN
    ASM_REWRITE_TAC[path_image; path_integrable_on; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[HAS_PATH_INTEGRAL; GSYM integrable_on] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\x. f (a:A) (g x) * vector_derivative g (at x)` THEN
    ASM_REWRITE_TAC[GSYM COMPLEX_SUB_RDISTRIB] THEN
    EXPAND_TAC "g" THEN REWRITE_TAC[VECTOR_DERIVATIVE_CIRCLEPATH] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; COMPLEX_NORM_II] THEN
    REWRITE_TAC[REAL_ABS_NUM; REAL_ABS_PI; REAL_MUL_LID] THEN
    REWRITE_TAC[NORM_CEXP; RE_MUL_CX; RE_MUL_II; IM_CX] THEN
    REWRITE_TAC[REAL_NEG_0; REAL_MUL_RZERO; REAL_EXP_0; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; GSYM REAL_LE_RDIV_EQ;
                 REAL_MUL_ASSOC; PI_POS; REAL_OF_NUM_LT; ARITH] THEN
    REWRITE_TAC[real_div; GSYM REAL_INV_MUL; GSYM REAL_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_MESON_TAC[REAL_MUL_AC; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[LIM_NULL] THEN REWRITE_TAC[tendsto] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / (&4 * pi * r)`) THEN
  ASM_SIMP_TAC[REAL_LT_MUL; PI_POS; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  UNDISCH_TAC `eventually (\n:A. (f n) path_integrable_on g) net` THEN
  REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  X_GEN_TAC `a:A` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `e / (&4 * pi * r) * &2 * pi * r` THEN CONJ_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[PI_POS; REAL_FIELD
     `&0 < pi /\ &0 < r ==> e / (&4 * pi * r) * &2 * pi * r = e / &2`] THEN
    UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC] THEN
  REWRITE_TAC[dist; VECTOR_SUB_RZERO] THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_BOUND_CIRCLEPATH THEN
  EXISTS_TAC `\x. (f:A->complex->complex) a x - l x` THEN
  EXISTS_TAC `z:complex` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HAS_PATH_INTEGRAL_SUB THEN CONJ_TAC THEN
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC HAS_PATH_INTEGRAL_INTEGRAL THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE; PI_POS];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "g" THEN
    ASM_SIMP_TAC[PATH_IMAGE_CIRCLEPATH; IN_ELIM_THM; REAL_LT_IMP_LE]]);;

(* ------------------------------------------------------------------------- *)
(* General stepping result for derivative formulas.                          *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_NEXT_DERIVATIVE_CIRCLEPATH = prove
 (`!f g z r k.
        ~(k = 0) /\
        (f continuous_on path_image(circlepath(z,r))) /\
        (!w. w IN ball(z,r)
             ==> ((\u. f(u) / (u - w) pow k) has_path_integral g w)
                 (circlepath(z,r)))
        ==> !w. w IN ball(z,r)
                ==> (\u. f(u) / (u - w) pow (k + 1)) path_integrable_on
                            (circlepath(z,r)) /\
                    (g has_complex_derivative
                     (Cx(&k) * path_integral(circlepath(z,r))
                                 (\u. f(u) / (u - w) pow (k + 1))))
                    (at w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[dist] o
    GEN_REWRITE_RULE I [IN_BALL]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
    `n < r ==> &0 <= n ==> &0 < r`)) THEN
  REWRITE_TAC[NORM_POS_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?d. &0 < d /\ ball(w:complex,d) SUBSET ball(z,r)` STRIP_ASSUME_TAC
  THENL
   [EXISTS_TAC `r - norm(w - z:complex)` THEN
    ASM_REWRITE_TAC[REAL_SUB_LT; SUBSET; IN_BALL] THEN ASM_NORM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`at(w:complex)`;
    `\u x:complex. f(x) * (inv(x - u) pow k - inv(x - w) pow k) /
                   (u - w) / Cx(&k)`;
    `\u. f(u) / (u - w) pow (k + 1)`; `z:complex`; `r:real`]
        PATH_INTEGRAL_UNIFORM_LIMIT_CIRCLEPATH) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `Cx(&k)` o MATCH_MP LIM_COMPLEX_LMUL) THEN
    REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_AT] THEN
    MATCH_MP_TAC(REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
                  LIM_TRANSFORM_AT) THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:complex` THEN
    REWRITE_TAC[dist] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(u:complex = w)` ASSUME_TAC THENL
     [ASM_MESON_TAC[COMPLEX_SUB_0; COMPLEX_NORM_0; REAL_LT_REFL]; ALL_TAC] THEN
    ASM_SIMP_TAC[CX_INJ; REAL_OF_NUM_EQ; COMPLEX_FIELD
     `~(y = Cx(&0)) ==> (y * x = z <=> x = z / y)`] THEN
    ASM_SIMP_TAC[COMPLEX_SUB_0; CX_INJ; REAL_OF_NUM_EQ; COMPLEX_SUB_LDISTRIB;
           COMPLEX_FIELD `~(c = Cx(&0)) ==> (a - b) / c = a / c - b / c`] THEN
    MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
    MATCH_MP_TAC HAS_PATH_INTEGRAL_SUB THEN
    REWRITE_TAC[complex_div; COMPLEX_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM complex_div] THEN
    CONJ_TAC THEN REPEAT(MATCH_MP_TAC HAS_PATH_INTEGRAL_COMPLEX_DIV) THEN
    REWRITE_TAC[GSYM complex_div; COMPLEX_POW_INV] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    ASM_REWRITE_TAC[IN_BALL; dist] THEN ASM_MESON_TAC[NORM_SUB]] THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_AT] THEN CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_AT] THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:complex` THEN
    REWRITE_TAC[dist] THEN STRIP_TAC THEN
    REWRITE_TAC[complex_div; COMPLEX_MUL_ASSOC] THEN
    REPEAT(MATCH_MP_TAC PATH_INTEGRABLE_COMPLEX_RMUL) THEN
    REWRITE_TAC[COMPLEX_SUB_LDISTRIB; COMPLEX_POW_INV; GSYM complex_div] THEN
    MATCH_MP_TAC PATH_INTEGRABLE_SUB THEN
    REWRITE_TAC[path_integrable_on] THEN CONJ_TAC THENL
     [EXISTS_TAC `(g:complex->complex) u`;
      EXISTS_TAC `(g:complex->complex) w`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    REWRITE_TAC[IN_BALL; dist] THEN ASM_MESON_TAC[NORM_SUB];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. &0 < e
     ==> eventually
         (\n. !x. x IN path_image (circlepath (z,r))
                  ==> norm
                      ((inv (x - n) pow k - inv (x - w) pow k) /
                       (n - w) / Cx(&k) - inv(x - w) pow (k + 1)) <
                      e)
         (at w)`
  ASSUME_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `bounded(IMAGE (f:complex->complex)
       (path_image(circlepath(z,r))))`
    MP_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[path_image] THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[COMPACT_INTERVAL] THEN
      MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
      REWRITE_TAC[GSYM valid_path] THEN REWRITE_TAC[VALID_PATH_CIRCLEPATH];
      ALL_TAC] THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / B:real`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
    X_GEN_TAC `u:complex` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:complex` THEN
    DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[complex_div; GSYM COMPLEX_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM COMPLEX_SUB_LDISTRIB; COMPLEX_NORM_MUL] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> b < x ==> a < x`) THEN
    REWRITE_TAC[COMPLEX_POW_INV] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE]] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN REWRITE_TAC[EVENTUALLY_AT] THEN
  EXISTS_TAC `min (d / &2) ((e * (d / &2) pow (k + 2)) / (&k + &1))` THEN
  ASM_SIMP_TAC[REAL_LT_MIN; REAL_HALF; REAL_POW_LT; REAL_LT_MUL; dist;
               REAL_LT_DIV; REAL_ARITH `&0 < &k + &1`] THEN
  X_GEN_TAC `u:complex` THEN STRIP_TAC THEN
  X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\n w. if n = 0 then inv(x - w) pow k
                        else if n = 1 then Cx(&k) / (x - w) pow (k + 1)
                        else (Cx(&k) * Cx(&k + &1)) / (x - w) pow (k + 2)`;
                 `1`; `ball(w:complex,d / &2)`;
                 `(&k * (&k + &1)) / (d / &2) pow (k + 2)`]
         COMPLEX_TAYLOR) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[CONVEX_BALL; ADD_EQ_0; ARITH] THEN CONJ_TAC THENL
     [ALL_TAC;
      X_GEN_TAC `v:complex` THEN REWRITE_TAC[IN_BALL; dist] THEN DISCH_TAC THEN
      REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_DIV; COMPLEX_NORM_CX]THEN
      REWRITE_TAC[real_div; GSYM REAL_POW_INV; GSYM REAL_MUL_ASSOC] THEN
      REWRITE_TAC[REAL_ABS_NUM; REAL_ARITH `abs(&k + &1) = &k + &1`] THEN
      REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN
             CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC]) THEN
      REWRITE_TAC[REAL_POW_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_POW_LT; REAL_HALF] THEN
      REWRITE_TAC[COMPLEX_NORM_POW] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> &0 <= d / &2`] THEN
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN STRIP_TAC THEN
      UNDISCH_TAC `x IN path_image (circlepath (z,r))` THEN
      ASM_SIMP_TAC[PATH_IMAGE_CIRCLEPATH; REAL_LT_IMP_LE] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      MATCH_MP_TAC(REAL_ARITH `x < r ==> ~(x = r)`) THEN
      ONCE_REWRITE_TAC[NORM_SUB] THEN REWRITE_TAC[GSYM dist; GSYM IN_BALL] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      REWRITE_TAC[IN_BALL; dist] THEN
      SUBST1_TAC(SIMPLE_COMPLEX_ARITH
        `w - x = (w - v) + --(x - v):complex`) THEN
      MATCH_MP_TAC NORM_TRIANGLE_LT THEN REWRITE_TAC[NORM_NEG] THEN
      ASM_REAL_ARITH_TAC] THEN
    GEN_TAC THEN X_GEN_TAC `y:complex` THEN
    REWRITE_TAC[IN_BALL; dist] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(y:complex = x)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `x IN path_image (circlepath (z,r))` THEN
      ASM_SIMP_TAC[PATH_IMAGE_CIRCLEPATH; REAL_LT_IMP_LE; IN_ELIM_THM] THEN
      MATCH_MP_TAC(REAL_ARITH `x < r ==> ~(x = r)`) THEN
      ONCE_REWRITE_TAC[NORM_SUB] THEN REWRITE_TAC[GSYM dist; GSYM IN_BALL] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      REWRITE_TAC[IN_BALL; dist] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o MATCH_MP
      (ARITH_RULE `i <= 1 ==> i = 0 \/ i = 1`)) THEN
    REWRITE_TAC[ARITH] THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_AT_WITHIN THEN
    COMPLEX_DIFF_TAC THEN
    REWRITE_TAC[COMPLEX_POW_EQ_0; COMPLEX_INV_EQ_0; CONJ_ASSOC;
       COMPLEX_MUL_LZERO; COMPLEX_SUB_0; ADD_EQ_0; ARITH] THEN
    REWRITE_TAC[COMPLEX_SUB_LZERO; COMPLEX_NEG_NEG; complex_div] THEN
    REWRITE_TAC[COMPLEX_MUL_LID; GSYM COMPLEX_MUL_ASSOC;
     GSYM COMPLEX_POW_INV; GSYM COMPLEX_INV_MUL; GSYM COMPLEX_POW_ADD] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> k - 1 + 2 = k + 1`] THEN
    REWRITE_TAC[COMPLEX_INV_INV; ADD_SUB; COMPLEX_MUL_RNEG;
                COMPLEX_NEG_NEG; COMPLEX_MUL_RID; COMPLEX_POW_POW] THEN
    REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC; GSYM REAL_OF_NUM_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[COMPLEX_POW_INV] THEN
    ASM_SIMP_TAC[COMPLEX_POW_EQ_0; COMPLEX_INV_EQ_0; COMPLEX_SUB_0;
                 COMPLEX_FIELD `~(x = Cx(&0)) /\ ~(y = Cx(&0))
                                ==> (z * inv x = inv y <=> y * z = x)`] THEN
    REWRITE_TAC[GSYM COMPLEX_POW_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`w:complex`; `u:complex`]) THEN
  ASM_REWRITE_TAC[CENTRE_IN_BALL; REAL_HALF; NUMSEG_CONV `0..1`] THEN
  ASM_SIMP_TAC[IN_BALL; dist; VSUM_CLAUSES; FINITE_RULES] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[NORM_SUB]; ALL_TAC] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH] THEN
  REWRITE_TAC[complex_pow; VECTOR_ADD_RID; ARITH; FACT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[COMPLEX_DIV_1; COMPLEX_MUL_RID; COMPLEX_POW_1] THEN
  SUBGOAL_THEN `~(u:complex = w)` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPLEX_SUB_REFL; COMPLEX_NORM_0; REAL_LT_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(x:complex = w)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `w IN path_image (circlepath (z,r))` THEN
    ASM_SIMP_TAC[IN_ELIM_THM; PATH_IMAGE_CIRCLEPATH; REAL_LT_IMP_LE] THEN
    ASM_MESON_TAC[NORM_SUB; REAL_LT_REFL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[COMPLEX_SUB_0; COMPLEX_POW_EQ_0; CX_INJ; REAL_OF_NUM_EQ;
     COMPLEX_FIELD
        `~(d = Cx(&0)) /\ ~(c = Cx(&0)) /\ ~(e = Cx(&0))
         ==> a - (b + c / d * e) = ((a - b) / e / c - inv d) * c * e`] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_DIV_1] THEN
  REWRITE_TAC[REAL_ABS_NUM; GSYM COMPLEX_POW_INV] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN
  EXISTS_TAC `&k * norm(u - w:complex)` THEN
  ASM_SIMP_TAC[REAL_LT_MUL; REAL_OF_NUM_LT; LT_NZ] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `n <= x ==> x < y ==> n < y`)) THEN
  REWRITE_TAC[REAL_POW_2; REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_POW_2; REAL_MUL_ASSOC; REAL_LT_RMUL_EQ] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a * b * c:real = (c * a) * b`] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ; REAL_HALF; REAL_POW_LT] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_ARITH `&0 < &k + &1`]);;

(* ------------------------------------------------------------------------- *)
(* In particular, the first derivative formula.                              *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_DERIVATIVE_INTEGRAL_CIRCLEPATH = prove
 (`!f z r w.
        f continuous_on cball(z,r) /\
        f holomorphic_on ball(z,r) /\
        w IN ball(z,r)
        ==> (\u. f(u) / (u - w) pow 2) path_integrable_on circlepath(z,r) /\
            (f has_complex_derivative
                (Cx(&1) / (Cx(&2) * Cx(pi) * ii) *
                 path_integral(circlepath(z,r)) (\u. f(u) / (u - w) pow 2)))
            (at w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`f:complex->complex`; `\x:complex. Cx(&2) * Cx(pi) * ii * f x`;
                `z:complex`; `r:real`; `1`]
         CAUCHY_NEXT_DERIVATIVE_CIRCLEPATH) THEN
  ASM_SIMP_TAC[COMPLEX_POW_1; ARITH; CAUCHY_INTEGRAL_CIRCLEPATH] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(z:complex,r)` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_BALL]) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
     `n < r ==> &0 <= n ==> &0 <= r`)) THEN
    SIMP_TAC[DIST_POS_LE; PATH_IMAGE_CIRCLEPATH] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_CBALL] THEN
    SIMP_TAC[dist; REAL_LE_REFL; NORM_SUB];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `w:complex`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[COMPLEX_MUL_LID] THEN
  DISCH_THEN(MP_TAC o SPEC `Cx(&1) / (Cx(&2) * Cx pi * ii)` o
        MATCH_MP HAS_COMPLEX_DERIVATIVE_LMUL_AT) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN MP_TAC CX_2PII_NZ THEN CONV_TAC COMPLEX_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Existence of all higher derivatives.                                      *)
(* ------------------------------------------------------------------------- *)

let HOLOMORPHIC_DERIVATIVE = prove
 (`!f f' s. open s /\ (!z. z IN s ==> (f has_complex_derivative f'(z)) (at z))
            ==> f' holomorphic_on s`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[HOLOMORPHIC_ON_OPEN] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`\x. Cx(&1) / (Cx(&2) * Cx pi * ii) * f(x:complex)`;
                `f':complex->complex`; `z:complex`; `r:real`; `2`]
               CAUCHY_NEXT_DERIVATIVE_CIRCLEPATH) THEN
  ANTS_TAC THENL [ALL_TAC; ASM_MESON_TAC[CENTRE_IN_BALL]] THEN
  SUBGOAL_THEN `f holomorphic_on cball(z,r)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[holomorphic_on] THEN
    ASM_MESON_TAC[SUBSET; HAS_COMPLEX_DERIVATIVE_AT_WITHIN];
    ALL_TAC] THEN
  REWRITE_TAC[ARITH] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_CMUL THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(z:complex,r)` THEN
    ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON] THEN
    ASM_SIMP_TAC[PATH_IMAGE_CIRCLEPATH; REAL_LT_IMP_LE] THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM; IN_CBALL; dist; NORM_SUB; REAL_LE_REFL];
    ALL_TAC] THEN
  X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`f:complex->complex`; `z:complex`; `r:real`; `w:complex`]
               CAUCHY_DERIVATIVE_INTEGRAL_CIRCLEPATH) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON; HOLOMORPHIC_ON_SUBSET;
                  BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HAS_PATH_INTEGRAL_INTEGRAL) THEN
  DISCH_THEN(MP_TAC o SPEC `Cx(&1) / (Cx(&2) * Cx pi * ii)` o
    MATCH_MP HAS_PATH_INTEGRAL_COMPLEX_LMUL) THEN
  REWRITE_TAC[complex_div; GSYM COMPLEX_MUL_ASSOC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[COMPLEX_MUL_ASSOC; GSYM complex_div] THEN
  MATCH_MP_TAC COMPLEX_DERIVATIVE_UNIQUE_AT THEN
  MAP_EVERY EXISTS_TAC [`f:complex->complex`; `w:complex`] THEN
  ASM_REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC] THEN
  ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL]);;

let HOLOMORPHIC_COMPLEX_DERIVATIVE = prove
 (`!f s. open s /\ f holomorphic_on s
         ==> (complex_derivative f) holomorphic_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOLOMORPHIC_DERIVATIVE THEN
  EXISTS_TAC `f:complex->complex` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[HAS_COMPLEX_DERIVATIVE_DERIVATIVE; HOLOMORPHIC_ON_OPEN]);;

let ANALYTIC_COMPLEX_DERIVATIVE = prove
 (`!f s. f analytic_on s ==> (complex_derivative f) analytic_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[analytic_on] THEN DISCH_TAC THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  SIMP_TAC[HOLOMORPHIC_COMPLEX_DERIVATIVE; OPEN_BALL]);;

let HOLOMORPHIC_HIGHER_COMPLEX_DERIVATIVE = prove
 (`!f s n. open s /\ f holomorphic_on s
           ==> (higher_complex_derivative n f) holomorphic_on s`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  INDUCT_TAC THEN
  ASM_SIMP_TAC[HOLOMORPHIC_COMPLEX_DERIVATIVE; higher_complex_derivative]);;

let ANALYTIC_HIGHER_COMPLEX_DERIVATIVE = prove
 (`!f s n. f analytic_on s ==> (higher_complex_derivative n f) analytic_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[analytic_on] THEN DISCH_TAC THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  ASM_SIMP_TAC[HOLOMORPHIC_HIGHER_COMPLEX_DERIVATIVE; OPEN_BALL]);;

let HAS_COMPLEX_DERIVATIVE_HIGHER_COMPLEX_DERIVATIVE = prove
 (`!f s x n. open s /\ f holomorphic_on s /\ x IN s
             ==> ((higher_complex_derivative n f) has_complex_derivative
                          (higher_complex_derivative (SUC n) f x)) (at x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[higher_complex_derivative] THEN
  REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT THEN
  EXISTS_TAC `s:complex->bool` THEN
  ASM_SIMP_TAC[HOLOMORPHIC_HIGHER_COMPLEX_DERIVATIVE]);;

(* ------------------------------------------------------------------------- *)
(* Combining theorems for higher derivatives including Leibniz rule.         *)
(* ------------------------------------------------------------------------- *)

let HIGHER_COMPLEX_DERIVATIVE_HOLOMORPHIC_ON = prove
 (`!f s n. open s /\ f holomorphic_on s
           ==> higher_complex_derivative n f holomorphic_on s`,
  REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  INDUCT_TAC THEN
  ASM_SIMP_TAC [higher_complex_derivative; HOLOMORPHIC_COMPLEX_DERIVATIVE]);;

let HIGHER_COMPLEX_DERIVATIVE_EQ_ITER = prove
 (`!n. higher_complex_derivative n = ITER n complex_derivative`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC [FUN_EQ_THM; ITER; higher_complex_derivative]);;

let HIGHER_COMPLEX_DERIVATIVE_HIGHER_COMPLEX_DERIVATIVE = prove
 (`!f m n. higher_complex_derivative m (higher_complex_derivative n f) =
           higher_complex_derivative (m + n) f`,
  REWRITE_TAC[HIGHER_COMPLEX_DERIVATIVE_EQ_ITER; ITER_ADD]);;

let higher_complex_derivative_alt = prove
 (`(!f z. higher_complex_derivative 0 f = f) /\
   (!f z n. higher_complex_derivative (SUC n) f =
            higher_complex_derivative n (complex_derivative f))`,
  REWRITE_TAC [HIGHER_COMPLEX_DERIVATIVE_EQ_ITER; ITER_ALT]);;

let HIGHER_COMPLEX_DERIVATIVE_LINEAR = prove
 (`!c n. higher_complex_derivative n (\w. c * w) =
    \z. if n = 0 then c * z else if n = 1 then c else (Cx(&0))`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC [higher_complex_derivative; NOT_SUC; SUC_INJ; ONE] THEN
  STRUCT_CASES_TAC (SPEC `n:num` num_CASES) THEN
  REWRITE_TAC [NOT_SUC; SUC_INJ;
               COMPLEX_DERIVATIVE_LINEAR; COMPLEX_DERIVATIVE_CONST]);;

let HIGHER_COMPLEX_DERIVATIVE_CONST = prove
 (`!i c. higher_complex_derivative i (\w.c) = \w. if i=0 then c else Cx(&0)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC [higher_complex_derivative_alt; NOT_SUC;
                                   COMPLEX_DERIVATIVE_CONST; FUN_EQ_THM] THEN
  MESON_TAC[]);;

let HIGHER_COMPLEX_DERIVATIVE_ID = prove
 (`!z i. higher_complex_derivative i (\w.w) z =
            if i = 0 then z else if i = 1 then Cx(&1) else Cx(&0)`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC [higher_complex_derivative_alt; NOT_SUC; ONE; SUC_INJ] THEN
  REWRITE_TAC[COMPLEX_DERIVATIVE_ID; HIGHER_COMPLEX_DERIVATIVE_CONST; ONE]);;

let HAS_COMPLEX_DERIVATIVE_ITER_1 = prove
 (`!f n z. f z = z /\ (f has_complex_derivative Cx(&1)) (at z)
           ==> (ITER n f has_complex_derivative Cx(&1)) (at z)`,
  GEN_TAC THEN INDUCT_TAC THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC [ITER_POINTLESS; I_DEF; HAS_COMPLEX_DERIVATIVE_ID] THEN
  SUBGOAL_THEN `Cx(&1) = Cx(&1) * Cx(&1)` SUBST1_TAC THENL
  [REWRITE_TAC [COMPLEX_MUL_LID];
   ASM_SIMP_TAC [ITER_FIXPOINT; COMPLEX_DIFF_CHAIN_AT]]);;

let HIGHER_COMPLEX_DERIVATIVE_NEG = prove
 (`!f g s n z.
     open s /\ f holomorphic_on s /\ z IN s
     ==> higher_complex_derivative n (\w. --(f w)) z =
                --(higher_complex_derivative n f z)`,
  REWRITE_TAC [IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN
  REPEAT DISCH_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC [higher_complex_derivative] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  EXISTS_TAC `(\w. --(higher_complex_derivative n f w))` THEN
  EXISTS_TAC `s:complex->bool` THEN ASM_SIMP_TAC [] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_NEG THEN
  REWRITE_TAC [ETA_AX; GSYM higher_complex_derivative] THEN
  ASM_MESON_TAC [HAS_COMPLEX_DERIVATIVE_HIGHER_COMPLEX_DERIVATIVE]);;

let HIGHER_COMPLEX_DERIVATIVE_ADD = prove
 (`!f g s n z.
     open s /\ f holomorphic_on s /\ g holomorphic_on s /\ z IN s ==>
     higher_complex_derivative n (\w. f w + g w) z  =
     higher_complex_derivative n f z + higher_complex_derivative n g z`,
  REWRITE_TAC [IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN
  REPEAT DISCH_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC [higher_complex_derivative] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  EXISTS_TAC `(\w. higher_complex_derivative n f w +
                   higher_complex_derivative n g w)` THEN
  EXISTS_TAC `s:complex->bool` THEN ASM_SIMP_TAC [] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_ADD THEN
  REWRITE_TAC [ETA_AX; GSYM higher_complex_derivative] THEN
  ASM_MESON_TAC [HAS_COMPLEX_DERIVATIVE_HIGHER_COMPLEX_DERIVATIVE]);;

let HIGHER_COMPLEX_DERIVATIVE_SUB = prove
 (`!f g s n z.
     open s /\ f holomorphic_on s /\ g holomorphic_on s /\ z IN s ==>
     higher_complex_derivative n (\w. f w - g w) z  =
     higher_complex_derivative n f z - higher_complex_derivative n g z`,
  REWRITE_TAC [IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN
  REPEAT DISCH_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC [higher_complex_derivative] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  EXISTS_TAC `(\w. higher_complex_derivative n f w -
                   higher_complex_derivative n g w)` THEN
  EXISTS_TAC `s:complex->bool` THEN ASM_SIMP_TAC [] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_SUB THEN
  REWRITE_TAC [ETA_AX; GSYM higher_complex_derivative] THEN
  ASM_MESON_TAC [HAS_COMPLEX_DERIVATIVE_HIGHER_COMPLEX_DERIVATIVE]);;

let HIGHER_COMPLEX_DERIVATIVE_MUL = prove
 (`!f g s n z.
     open s /\ f holomorphic_on s /\ g holomorphic_on s /\ z IN s
     ==> higher_complex_derivative n (\w. f w * g w) z =
         vsum (0..n) (\i. Cx(&(binom(n,i))) *
                          higher_complex_derivative i f z *
                          higher_complex_derivative (n-i) g z)`,
  REWRITE_TAC [IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN
  REPEAT DISCH_TAC THEN INDUCT_TAC THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC [NUMSEG_SING; VSUM_SING; SUB] THEN
  REWRITE_TAC [higher_complex_derivative; binom; COMPLEX_MUL_LID] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  EXISTS_TAC `\w. vsum (0..n)
                    (\i. Cx (&(binom (n,i))) *
                         higher_complex_derivative i f w *
                         higher_complex_derivative (n-i) g w)` THEN
  EXISTS_TAC `s:complex->bool` THEN ASM_SIMP_TAC [] THEN
  SUBGOAL_THEN `vsum (0..SUC n) (\i. Cx (&(binom (SUC n,i))) *
                                     higher_complex_derivative i f z *
                                     higher_complex_derivative (SUC n-i) g z) =
                vsum (0..n) (\i. Cx (&(binom (n,i))) *
                                 (higher_complex_derivative i f z *
                                  higher_complex_derivative (SUC n-i) g z +
                                  higher_complex_derivative (SUC i) f z *
                                  higher_complex_derivative (n-i) g z))`
    SUBST1_TAC THENL
  [SUBGOAL_THEN
       `!i. binom(SUC n,i) = binom(n,i) + if i=0 then 0 else binom(n,PRE i)`
     (fun th -> REWRITE_TAC[th; GSYM REAL_OF_NUM_ADD; CX_ADD]) THENL
   [INDUCT_TAC THEN REWRITE_TAC[binom; NOT_SUC; PRE; ADD_SYM; ADD_0];
    REWRITE_TAC [COMPLEX_ADD_LDISTRIB; COMPLEX_ADD_RDISTRIB]] THEN
   SIMP_TAC [VSUM_ADD; FINITE_NUMSEG] THEN BINOP_TAC THENL
   [REWRITE_TAC [VSUM_CLAUSES_NUMSEG; LE_0] THEN
    SUBGOAL_THEN `binom(n,SUC n)=0` SUBST1_TAC THENL
    [REWRITE_TAC [BINOM_EQ_0] THEN ARITH_TAC; CONV_TAC COMPLEX_RING];
    SIMP_TAC [VSUM_CLAUSES_LEFT; SPEC `SUC n` LE_0] THEN
    REWRITE_TAC [COMPLEX_MUL_LZERO; COMPLEX_ADD_LID; GSYM ADD1;
                 VSUM_SUC; o_DEF; SUB_SUC; NOT_SUC; PRE]];
   MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_VSUM THEN
   REWRITE_TAC [FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
   MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_LMUL_AT THEN
   MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_MUL_AT THEN
   ASM_SIMP_TAC [ETA_AX; ARITH_RULE `i <= n ==> SUC n - i = SUC (n-i)`] THEN
   ASM_MESON_TAC [HAS_COMPLEX_DERIVATIVE_HIGHER_COMPLEX_DERIVATIVE]]);;

let HIGHER_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN = prove
 (`!f g s i z.
     open s /\ f holomorphic_on s /\ g holomorphic_on s /\
     (!w. w IN s ==> f w = g w) /\ z IN s
     ==> higher_complex_derivative i f z = higher_complex_derivative i g z`,
  REWRITE_TAC [IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN
  REPEAT DISCH_TAC THEN INDUCT_TAC THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC [higher_complex_derivative] THEN
  MATCH_MP_TAC COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  ASM_MESON_TAC [HOLOMORPHIC_HIGHER_COMPLEX_DERIVATIVE]);;

let HIGHER_COMPLEX_DERIVATIVE_COMPOSE_LINEAR = prove
 (`!f u s t n z.
     f holomorphic_on t /\ open s /\ open t /\
     (!w. w IN s ==> u * w IN t) /\ z IN s
     ==> higher_complex_derivative n (\w. f (u * w)) z =
         u pow n * higher_complex_derivative n f (u * z)`,
  REWRITE_TAC [RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC [higher_complex_derivative; complex_pow; COMPLEX_MUL_LID] THEN
  REPEAT STRIP_TAC THEN EQ_TRANS_TAC
    `complex_derivative
      (\z. u pow n * higher_complex_derivative n f (u * z)) z` THENL
  [MATCH_MP_TAC COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
   EXISTS_TAC `s:complex->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_HIGHER_COMPLEX_DERIVATIVE THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC
     (REWRITE_RULE [o_DEF]
       (SPECL [`\z:complex. u * z`; `f:complex->complex`]
              HOLOMORPHIC_ON_COMPOSE_GEN)) THEN
    EXISTS_TAC `t:complex->bool` THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC
     (REWRITE_RULE [o_DEF]
       (SPECL [`\w:complex. u:complex`; `\w:complex. w`]
              HOLOMORPHIC_ON_MUL)) THEN
    REWRITE_TAC [HOLOMORPHIC_ON_CONST; HOLOMORPHIC_ON_ID];
    MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN
    SIMP_TAC [HOLOMORPHIC_ON_POW; HOLOMORPHIC_ON_CONST] THEN MATCH_MP_TAC
     (REWRITE_RULE [o_DEF]
       (SPECL [`\w. u * w`; `higher_complex_derivative f n`]
              HOLOMORPHIC_ON_COMPOSE_GEN)) THEN
    EXISTS_TAC `t:complex->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [MATCH_MP_TAC
      (REWRITE_RULE [o_DEF]
        (SPECL [`\w:complex. u:complex`; `\w:complex. w`]
               HOLOMORPHIC_ON_MUL)) THEN
     REWRITE_TAC [HOLOMORPHIC_ON_CONST; HOLOMORPHIC_ON_ID];
     ASM_SIMP_TAC [HOLOMORPHIC_HIGHER_COMPLEX_DERIVATIVE]]];
   EQ_TRANS_TAC
     `u pow n * complex_derivative
        (\z. higher_complex_derivative n f (u * z)) z` THENL
   [MATCH_MP_TAC COMPLEX_DERIVATIVE_LMUL THEN
    MATCH_MP_TAC ANALYTIC_ON_IMP_DIFFERENTIABLE_AT THEN
    EXISTS_TAC `s:complex->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC (REWRITE_RULE [o_DEF] ANALYTIC_ON_COMPOSE_GEN) THEN
    EXISTS_TAC `t:complex->bool` THEN
    ASM_SIMP_TAC [ANALYTIC_ON_LINEAR; ANALYTIC_HIGHER_COMPLEX_DERIVATIVE;
                  ANALYTIC_ON_OPEN];
    ABBREV_TAC `a = u:complex pow n` THEN
    REWRITE_TAC [COMPLEX_MUL_AC; COMPLEX_EQ_MUL_LCANCEL] THEN
    ASM_CASES_TAC `a = Cx(&0)` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC RAND_CONV [COMPLEX_MUL_SYM] THEN MATCH_MP_TAC
     (REWRITE_RULE [o_DEF; COMPLEX_DIFFERENTIABLE_LINEAR;
                    COMPLEX_DERIVATIVE_LINEAR]
       (SPECL [`\w. u * w`;`higher_complex_derivative n f`]
              COMPLEX_DERIVATIVE_CHAIN)) THEN
    ASM_MESON_TAC [HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT;
                   HOLOMORPHIC_HIGHER_COMPLEX_DERIVATIVE]]]);;

let HIGHER_COMPLEX_DERIVATIVE_ADD_AT = prove
 (`!f g n z.
     f analytic_on {z} /\ g analytic_on {z}
     ==> higher_complex_derivative n (\w. f w + g w) z =
         higher_complex_derivative n f z +
         higher_complex_derivative n g z`,
  REWRITE_TAC [ANALYTIC_AT_TWO] THEN
  MESON_TAC [HIGHER_COMPLEX_DERIVATIVE_ADD]);;

let HIGHER_COMPLEX_DERIVATIVE_SUB_AT = prove
 (`!f g n z.
     f analytic_on {z} /\ g analytic_on {z}
     ==> higher_complex_derivative n (\w. f w - g w) z =
         higher_complex_derivative n f z -
         higher_complex_derivative n g z`,
  REWRITE_TAC [ANALYTIC_AT_TWO] THEN
  MESON_TAC [HIGHER_COMPLEX_DERIVATIVE_SUB]);;

let HIGHER_COMPLEX_DERIVATIVE_NEG_AT = prove
 (`!f g n z.
     f analytic_on {z} /\ g analytic_on {z}
     ==> higher_complex_derivative n (\w. f w - g w) z =
         higher_complex_derivative n f z -
         higher_complex_derivative n g z`,
  REWRITE_TAC [ANALYTIC_AT_TWO] THEN
  MESON_TAC [HIGHER_COMPLEX_DERIVATIVE_SUB]);;

let HIGHER_COMPLEX_DERIVATIVE_MUL_AT = prove
 (`!f g n z.
     f analytic_on {z} /\ g analytic_on {z}
     ==> higher_complex_derivative n (\w. f w * g w) z =
         vsum (0..n) (\i. Cx(&(binom(n,i))) *
                          higher_complex_derivative i f z *
                          higher_complex_derivative (n-i) g z)`,
  REWRITE_TAC [ANALYTIC_AT_TWO] THEN
  MESON_TAC [HIGHER_COMPLEX_DERIVATIVE_MUL]);;

(* ------------------------------------------------------------------------- *)
(* Nonexistence of isolated singularities and a stronger integral formula.   *)
(* ------------------------------------------------------------------------- *)

let NO_ISOLATED_SINGULARITY = prove
 (`!f s k. open s /\ FINITE k /\
           f continuous_on s /\ f holomorphic_on (s DIFF k)
           ==> f holomorphic_on s`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_DIFF; FINITE_IMP_CLOSED; IMP_CONJ] THEN
  REWRITE_TAC[GSYM complex_differentiable] THEN REPEAT DISCH_TAC THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(z:complex) IN k` THEN ASM_SIMP_TAC[IN_DIFF] THEN
  MP_TAC(ISPECL [`z:complex`; `k:complex->bool`] FINITE_SET_AVOID) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `d:real` THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `f holomorphic_on ball(z,min d e)` MP_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_BALL; CENTRE_IN_BALL; REAL_LT_MIN;
                 complex_differentiable]] THEN
  SUBGOAL_THEN
   `?g. !w. w IN ball(z,min d e)
            ==> (g has_complex_derivative f w) (at w within ball(z,min d e))`
  MP_TAC THENL
   [ALL_TAC;
    SIMP_TAC[HAS_COMPLEX_DERIVATIVE_WITHIN_OPEN; OPEN_BALL] THEN
    MESON_TAC[HOLOMORPHIC_DERIVATIVE; OPEN_BALL]] THEN
  MATCH_MP_TAC PATHINTEGRAL_CONVEX_PRIMITIVE THEN
  REWRITE_TAC[CONVEX_BALL] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:complex->bool` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (SET_RULE `b SUBSET s ==> c SUBSET b ==> c SUBSET s`)) THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CAUCHY_THEOREM_TRIANGLE_COFINITE THEN
  EXISTS_TAC `k:complex->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:complex->bool` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `w:complex` THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
    SPEC_TAC(`w:complex`,`w:complex`) THEN ASM_REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> (s DIFF k) SUBSET (t DIFF k)`) THEN
    MATCH_MP_TAC(SET_RULE
     `interior s SUBSET s /\ s SUBSET t ==> interior s SUBSET t`) THEN
    REWRITE_TAC[INTERIOR_SUBSET]] THEN
  (MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(z:complex,e)` THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(z:complex,min d e)` THEN
   CONJ_TAC THENL
    [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_BALL] THEN
     ASM SET_TAC[];
     REWRITE_TAC[SUBSET; IN_BALL] THEN REAL_ARITH_TAC]));;

let CAUCHY_INTEGRAL_FORMULA_CONVEX = prove
 (`!f s k g z.
        convex s /\ FINITE k /\ f continuous_on s /\
        (!x. x IN interior(s) DIFF k ==> f complex_differentiable at x) /\
        z IN interior(s) /\
        valid_path g /\ (path_image g) SUBSET (s DELETE z) /\
        pathfinish g = pathstart g
        ==> ((\w. f(w) / (w - z)) has_path_integral
             (Cx(&2) * Cx(pi) * ii * winding_number(g,z) * f(z))) g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CAUCHY_INTEGRAL_FORMULA_WEAK THEN
  MAP_EVERY EXISTS_TAC [`s:complex->bool`; `{}:complex->bool`] THEN
  ASM_REWRITE_TAC[DIFF_EMPTY; FINITE_RULES] THEN
  SIMP_TAC[GSYM HOLOMORPHIC_ON_OPEN; complex_differentiable; OPEN_INTERIOR] THEN
  MATCH_MP_TAC NO_ISOLATED_SINGULARITY THEN
  EXISTS_TAC `k:complex->bool` THEN
  ASM_REWRITE_TAC[OPEN_INTERIOR] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:complex->bool` THEN
    ASM_REWRITE_TAC[INTERIOR_SUBSET];
    ASM_SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_DIFF; FINITE_IMP_CLOSED; OPEN_INTERIOR;
                 GSYM complex_differentiable]]);;

(* ------------------------------------------------------------------------- *)
(* Formula for higher derivatives.                                           *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_HAS_PATH_INTEGRAL_HIGHER_DERIVATIVE_CIRCLEPATH = prove
 (`!f z r k w.
        f continuous_on cball(z,r) /\
        f holomorphic_on ball(z,r) /\
        w IN ball(z,r)
        ==> ((\u. f(u) / (u - w) pow (k + 1))
             has_path_integral
             ((Cx(&2) * Cx(pi) * ii) / Cx(&(FACT k)) *
              higher_complex_derivative k f w))
            (circlepath(z,r))`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `&0 < r` THENL
   [ALL_TAC;
    REWRITE_TAC[IN_BALL] THEN
    ASM_MESON_TAC[NORM_ARITH `~(&0 < r) ==> ~(dist(a,b) < r)`]] THEN
  INDUCT_TAC THEN REWRITE_TAC[higher_complex_derivative] THENL
   [REWRITE_TAC[ARITH; COMPLEX_POW_1; FACT; COMPLEX_DIV_1] THEN
    ASM_SIMP_TAC[GSYM COMPLEX_MUL_ASSOC; CAUCHY_INTEGRAL_CIRCLEPATH];
    ALL_TAC] THEN
  MP_TAC(SPECL
   [`f:complex->complex`;
    `\x. (Cx(&2) * Cx(pi) * ii) / Cx(&(FACT k)) *
         higher_complex_derivative k f x`;
    `z:complex`; `r:real`; `k + 1`] CAUCHY_NEXT_DERIVATIVE_CIRCLEPATH) THEN
  ASM_REWRITE_TAC[ADD1; ARITH_RULE `(k + 1) + 1 = k + 2`] THEN ANTS_TAC THENL
   [REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `cball(z:complex,r)` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[PATH_IMAGE_CIRCLEPATH; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[SUBSET; IN_CBALL; IN_ELIM_THM] THEN NORM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(fun th ->
    X_GEN_TAC `w:complex` THEN DISCH_TAC THEN MP_TAC(SPEC `w:complex` th)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[path_integrable_on; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `y:complex` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(COMPLEX_FIELD
   `~(a = Cx(&0)) /\ ~(b = Cx(&0)) /\ x = b / a * y ==> y = a / b * x`) THEN
  REWRITE_TAC[CX_2PII_NZ; CX_INJ; REAL_OF_NUM_EQ; FACT_NZ] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HAS_COMPLEX_DERIVATIVE_LMUL_AT) THEN
  DISCH_THEN(MP_TAC o SPEC `Cx(&(FACT k)) / (Cx(&2) * Cx pi * ii)`) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    MATCH_MP_TAC(COMPLEX_FIELD
     `~(a = Cx(&0)) /\ ~(b = Cx(&0)) ==> (a / b) * (b / a) * x = x`) THEN
    REWRITE_TAC[CX_2PII_NZ; CX_INJ; REAL_OF_NUM_EQ; FACT_NZ];
    REWRITE_TAC[FACT; GSYM REAL_OF_NUM_MUL; GSYM ADD1; CX_MUL] THEN
    MATCH_MP_TAC(COMPLEX_FIELD
     `z:complex = y /\ ~(d = Cx(&0))
      ==> k / d * k1 * z = (k1 * k) / d * y`) THEN
    REWRITE_TAC[CX_2PII_NZ] THEN MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
    ASM_REWRITE_TAC[]]);;

let CAUCHY_HIGHER_DERIVATIVE_INTEGRAL_CIRCLEPATH = prove
 (`!f z r k w.
        f continuous_on cball(z,r) /\
        f holomorphic_on ball(z,r) /\
        w IN ball(z,r)
        ==> (\u. f(u) / (u - w) pow (k + 1))
                path_integrable_on circlepath(z,r) /\
            higher_complex_derivative k f w =
              Cx(&(FACT k)) / (Cx(&2) * Cx(pi) * ii) *
              path_integral(circlepath(z,r)) (\u. f(u) / (u - w) pow (k + 1))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP
    CAUCHY_HAS_PATH_INTEGRAL_HIGHER_DERIVATIVE_CIRCLEPATH) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[path_integrable_on]; ALL_TAC] THEN
  MATCH_MP_TAC(COMPLEX_FIELD
   `~(a = Cx(&0)) /\ ~(b = Cx(&0)) /\ x = b / a * y ==> y = a / b * x`) THEN
  REWRITE_TAC[CX_2PII_NZ; CX_INJ; REAL_OF_NUM_EQ; FACT_NZ] THEN
  MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* An holomorphic function is analytic, i.e. has local power series.         *)
(* ------------------------------------------------------------------------- *)

let HOLOMORPHIC_POWER_SERIES = prove
 (`!f z w r.
     f holomorphic_on ball(z,r) /\ w IN ball(z,r)
     ==> ((\n. higher_complex_derivative n f z / Cx(&(FACT n)) * (w - z) pow n)
          sums f(w)) (from 0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?r. &0 < r /\ f holomorphic_on cball(z,r) /\ w IN ball(z,r)`
  MP_TAC THENL
   [EXISTS_TAC `(r + dist(w:complex,z)) / &2` THEN REPEAT CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
      EXISTS_TAC `ball(z:complex,r)` THEN ASM_REWRITE_TAC[SUBSET];
      ALL_TAC] THEN
    UNDISCH_TAC `(w:complex) IN ball(z,r)` THEN
    REWRITE_TAC[IN_BALL; IN_CBALL] THEN NORM_ARITH_TAC;
    ALL_TAC] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `f holomorphic_on ball(z,r) /\ f continuous_on cball(z,r)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN ASM_MESON_TAC[BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\k. path_integral (circlepath(z,r)) (\u. f u / (u - z) pow (k + 1)) *
          (w - z) pow k)
     sums path_integral (circlepath(z,r)) (\u. f u / (u - w))) (from 0)`
  MP_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPEC `inv(Cx(&2) * Cx(pi) * ii)` o
        MATCH_MP SERIES_COMPLEX_LMUL) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `k:num` THEN
      MP_TAC(SPECL [`f:complex->complex`; `z:complex`; `r:real`; `k:num`;
       `z:complex`] CAUCHY_HAS_PATH_INTEGRAL_HIGHER_DERIVATIVE_CIRCLEPATH) THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
      DISCH_THEN(SUBST1_TAC o MATCH_MP PATH_INTEGRAL_UNIQUE) THEN
      MATCH_MP_TAC(COMPLEX_FIELD
       `~(pit = Cx(&0)) /\ ~(fact = Cx(&0))
        ==> inv(pit) * ((pit / fact) * d) * wz = d / fact * wz`) THEN
      REWRITE_TAC[CX_2PII_NZ; CX_INJ; REAL_OF_NUM_EQ; FACT_NZ];
      MP_TAC(SPECL [`f:complex->complex`; `z:complex`; `r:real`; `w:complex`]
        CAUCHY_INTEGRAL_CIRCLEPATH_SIMPLE) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(SUBST1_TAC o MATCH_MP PATH_INTEGRAL_UNIQUE) THEN
      MATCH_MP_TAC(COMPLEX_FIELD
       `~(x * y * z = Cx(&0)) ==> inv(x * y * z) * x * y * z * w = w`) THEN
      REWRITE_TAC[CX_2PII_NZ]]] THEN
  REWRITE_TAC[sums; FROM_0; INTER_UNIV] THEN
  MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\n. path_integral (circlepath(z,r))
                   (\u. vsum (0..n)
                         (\k. f u * (w - z) pow k / (u - z) pow (k + 1)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
    X_GEN_TAC `k:num` THEN REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) PATH_INTEGRAL_VSUM o lhand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
      ONCE_REWRITE_TAC[SIMPLE_COMPLEX_ARITH
       `a * b / c:complex = b * a / c`] THEN
      MATCH_MP_TAC PATH_INTEGRABLE_COMPLEX_LMUL THEN
      ASM_SIMP_TAC[CAUCHY_HIGHER_DERIVATIVE_INTEGRAL_CIRCLEPATH;
                   CENTRE_IN_BALL];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[SIMPLE_COMPLEX_ARITH `a * b / c:complex = a / c * b`] THEN
    MATCH_MP_TAC PATH_INTEGRAL_COMPLEX_RMUL THEN
    ASM_SIMP_TAC[CAUCHY_HIGHER_DERIVATIVE_INTEGRAL_CIRCLEPATH; CENTRE_IN_BALL];
    ALL_TAC] THEN
  MATCH_MP_TAC(CONJUNCT2
   (REWRITE_RULE[FORALL_AND_THM; TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`]
        PATH_INTEGRAL_UNIFORM_LIMIT_CIRCLEPATH)) THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
    X_GEN_TAC `k:num` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PATH_INTEGRABLE_VSUM THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[SIMPLE_COMPLEX_ARITH `a * b / c:complex = b * a / c`] THEN
    MATCH_MP_TAC PATH_INTEGRABLE_COMPLEX_LMUL THEN
    ASM_SIMP_TAC[CAUCHY_HIGHER_DERIVATIVE_INTEGRAL_CIRCLEPATH; CENTRE_IN_BALL];
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[PATH_IMAGE_CIRCLEPATH; REAL_LT_IMP_LE; IN_ELIM_THM] THEN
  SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_NUMSEG; complex_div] THEN
  REWRITE_TAC[GSYM COMPLEX_SUB_LDISTRIB; COMPLEX_NORM_MUL] THEN
  REWRITE_TAC[COMPLEX_POW_ADD; COMPLEX_INV_MUL; COMPLEX_POW_1] THEN
  SIMP_TAC[COMPLEX_MUL_ASSOC; VSUM_COMPLEX_RMUL; FINITE_NUMSEG] THEN
  REWRITE_TAC[GSYM complex_div; GSYM COMPLEX_POW_DIV] THEN
  REWRITE_TAC[VSUM_GP; CONJUNCT1 LT; CONJUNCT1 complex_pow] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  SUBGOAL_THEN
   `?B. &0 < B /\
        !u:complex. u IN cball(z,r) ==> norm(f u:complex) <= B`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE (f:complex->complex) (cball(z,r))`
      COMPACT_IMP_BOUNDED) THEN
    ASM_SIMP_TAC[COMPACT_CONTINUOUS_IMAGE; COMPACT_CBALL] THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `?k. &0 < k /\ k <= r /\ norm(w - z) <= r - k /\
                    !u. norm(u - z) = r ==> k <= norm(u - w)`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `r - dist(z:complex,w)` THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[IN_BALL] THEN
    NORM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`(r - k) / r:real`; `e / B * k:real`] REAL_ARCH_POW_INV) THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_DIV; REAL_HALF; REAL_LT_MUL] THEN
  ASM_REWRITE_TAC[REAL_ARITH `r - k < &1 * r <=> &0 < k`] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `u:complex` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(u:complex = z) /\ ~(u = w)` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_BALL]) THEN
    MAP_EVERY UNDISCH_TAC [`&0 < r`; `norm(u - z:complex) = r`] THEN
    NORM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[COMPLEX_FIELD
   `~(u = z) /\ ~(u = w) ==> ~((w - z) / (u - z) = Cx(&1))`] THEN
  ASM_SIMP_TAC[COMPLEX_FIELD
   `~(u = z) /\ ~(u = w)
    ==> x / (Cx(&1) - (w - z) / (u - z)) / (u - z) = x / (u - w)`] THEN
  ASM_SIMP_TAC[COMPLEX_FIELD
   `~(u = w)
    ==> (Cx(&1) - e) / (u - w) - inv(u - w) = --(e / (u - w))`] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; NORM_NEG; COMPLEX_NORM_POW] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `B * ((r - k) / r) pow N / k:real` THEN CONJ_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_LT_LDIV_EQ]] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[NORM_POS_LE] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_CBALL] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[dist; REAL_LE_REFL];
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE];
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  REWRITE_TAC[GSYM real_div] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE];
    ALL_TAC;
    REWRITE_TAC[REAL_LE_INV_EQ; NORM_POS_LE];
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `((r - k) / r:real) pow (SUC n)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_LE_DIV; NORM_POS_LE; REAL_LT_IMP_LE];
    MATCH_MP_TAC REAL_POW_MONO_INV THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN
    ASM_SIMP_TAC[ARITH_RULE `N <= n ==> N <= SUC n`] THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Liouville's theorem.                                                      *)
(* ------------------------------------------------------------------------- *)

let LIOUVILLE_THEOREM = prove
 (`!f. f holomorphic_on (:complex) /\ bounded (IMAGE f (:complex))
       ==> ?c. !z. f(z) = c`,
  GEN_TAC THEN
  SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_UNIV; BOUNDED_POS; IN_UNIV;
           FORALL_IN_IMAGE; SKOLEM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `f':complex->complex`)
               (X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!w. w IN (:complex) ==> f w:complex = f z`
   (fun th -> MESON_TAC[th; IN_UNIV]) THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_ZERO_UNIQUE THEN
  EXISTS_TAC `z:complex` THEN
  REWRITE_TAC[IN_UNIV; CONVEX_UNIV; WITHIN_UNIV] THEN
  X_GEN_TAC `w:complex` THEN
  SUBGOAL_THEN `(f':complex->complex) w = Cx(&0)`
   (fun th -> ASM_MESON_TAC[th]) THEN
  REWRITE_TAC[GSYM COMPLEX_NORM_ZERO] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(&0 < x) ==> x = &0`) THEN
  REWRITE_TAC[NORM_POS_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?R. &0 < R /\ B / R < norm((f':complex->complex) w)`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `&2 * B / norm((f':complex->complex) w)` THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
    REWRITE_TAC[real_div; REAL_INV_MUL; REAL_INV_INV; GSYM REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_FIELD
     `&0 < B ==> B * inv(&2) * inv(B) * c = c / &2`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`f:complex->complex`; `w:complex`;
                `R:real`; `w:complex`]
               CAUCHY_DERIVATIVE_INTEGRAL_CIRCLEPATH) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; HOLOMORPHIC_ON_OPEN;
                 OPEN_BALL; CENTRE_IN_BALL; REAL_LT_DIV; REAL_HALF] THEN
    ASM_MESON_TAC[HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT;
                  CONTINUOUS_AT_WITHIN];
    ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HAS_PATH_INTEGRAL_INTEGRAL) THEN
  DISCH_THEN(MP_TAC o SPEC `B:real / R pow 2` o MATCH_MP
   (ONCE_REWRITE_RULE[IMP_CONJ] HAS_PATH_INTEGRAL_BOUND_CIRCLEPATH)) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_IMP_LE; REAL_POW_LT] THEN
  ASM_SIMP_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_POW; REAL_LE_DIV2_EQ;
               REAL_POW_LT; REAL_NOT_LE] THEN
  MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN
  EXISTS_TAC `norm(Cx(&1) / (Cx (&2) * Cx pi * ii))` THEN
  REWRITE_TAC[GSYM COMPLEX_NORM_MUL] THEN
  SUBGOAL_THEN
   `Cx(&1) / (Cx(&2) * Cx pi * ii) *
    path_integral (circlepath (w,R)) (\u. f u / (u - w) pow 2) =
    f' w`
  SUBST1_TAC THENL [ASM_MESON_TAC[COMPLEX_DERIVATIVE_UNIQUE_AT]; ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_NZ] THEN
  ASM_SIMP_TAC[CX_2PII_NZ;
    COMPLEX_FIELD `~(y = Cx(&0)) ==> ~(Cx(&1) / y = Cx(&0))`] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
  REWRITE_TAC[REAL_ABS_NUM; REAL_ABS_PI; COMPLEX_NORM_II] THEN
  ASM_SIMP_TAC[PI_POS; REAL_FIELD
   `&0 < R /\ &0 < pi
   ==> &1 / (&2 * pi * &1) * B / R pow 2 * &2 * pi * R = B / R`]);;

(* ------------------------------------------------------------------------- *)
(* These weaker versions don't even need the derivative formula.             *)
(* ------------------------------------------------------------------------- *)

let LIOUVILLE_WEAK = prove
 (`!f. f holomorphic_on (:complex) /\ (f --> Cx(&0)) at_infinity
       ==> !z. f(z) = Cx(&0)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[TAUT `p = ~ ~ p`] THEN
  PURE_REWRITE_TAC[GSYM COMPLEX_NORM_NZ] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_AT_INFINITY]) THEN
  DISCH_THEN(MP_TAC o SPEC `norm((f:complex->complex) z) / &2`) THEN
  ASM_REWRITE_TAC[dist; REAL_HALF; COMPLEX_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`f:complex->complex`; `z:complex`;
                `&1 + abs B + norm(z:complex)`; `z:complex`]
                CAUCHY_INTEGRAL_CIRCLEPATH) THEN
  ASM_SIMP_TAC[CONVEX_UNIV; INTERIOR_OPEN; OPEN_UNIV; IN_UNIV] THEN
  ABBREV_TAC `R = &1 + abs B + norm(z:complex)` THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL
   [ASM_MESON_TAC[NORM_POS_LE; REAL_ABS_POS; REAL_ARITH
     `&0 <= x /\ &0 <= y ==> &0 < &1 + x + y`]; ALL_TAC] THEN
  ASM_REWRITE_TAC[CENTRE_IN_BALL; NOT_IMP; CONJ_ASSOC] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON; HOLOMORPHIC_ON_SUBSET;
                  SUBSET_UNIV];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP
   (ONCE_REWRITE_RULE[IMP_CONJ] HAS_PATH_INTEGRAL_BOUND_CIRCLEPATH)) THEN
  DISCH_THEN(MP_TAC o SPEC `norm((f:complex->complex) z) / &2 / R`) THEN
  ASM_SIMP_TAC[REAL_LE_DIV; NORM_POS_LE; REAL_POS; REAL_LT_IMP_LE] THEN
  ASM_SIMP_TAC[REAL_FIELD `&0 < R ==> x / R * &2 * pi * R = &2 * pi * x`] THEN
  REWRITE_TAC[NOT_IMP; REAL_NOT_LE] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[COMPLEX_NORM_DIV; REAL_LE_DIV2_EQ] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `norm(x - z:complex) = R` THEN EXPAND_TAC "R" THEN
    MATCH_MP_TAC(REAL_ARITH
     `d <= x + z ==> d = &1 + abs b + z ==> x >= b`) THEN
    REWRITE_TAC[VECTOR_SUB] THEN MESON_TAC[NORM_TRIANGLE; NORM_NEG];
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_NUM; REAL_ABS_PI;
                COMPLEX_NORM_II] THEN
    SIMP_TAC[REAL_LT_LMUL_EQ; REAL_OF_NUM_LT; ARITH; PI_POS; REAL_MUL_LID] THEN
    SUBGOAL_THEN `?w:complex. norm w = abs B` MP_TAC THENL
     [MESON_TAC[VECTOR_CHOOSE_SIZE; REAL_ABS_POS]; ALL_TAC] THEN
    ASM_MESON_TAC[NORM_POS_LE; REAL_ARITH
     `abs B >= B /\ (&0 <= x /\ x < z / &2 ==> z / &2 < z)`]]);;

let LIOUVILLE_WEAK_INVERSE = prove
 (`!f. f holomorphic_on (:complex) /\
       (!B. eventually (\x. norm(f x) >= B) at_infinity)
       ==> ?z. f(z) = Cx(&0)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  PURE_REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_TAC THEN
  MP_TAC(SPEC `\x:complex. Cx(&1) / (f(x))` LIOUVILLE_WEAK) THEN
  ASM_SIMP_TAC[COMPLEX_FIELD `~(y = Cx(&0)) ==> ~(Cx(&1) / y = Cx(&0))`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[holomorphic_on; complex_div; COMPLEX_MUL_LID; IN_UNIV] THEN
    GEN_TAC THEN REWRITE_TAC[GSYM complex_differentiable; WITHIN_UNIV] THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_INV_AT THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[OPEN_UNIV; HOLOMORPHIC_ON_OPEN; IN_UNIV;
                  complex_differentiable];
    REWRITE_TAC[tendsto] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&2/ e`) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
    REWRITE_TAC[dist; COMPLEX_SUB_RZERO; real_ge; COMPLEX_NORM_DIV;
                COMPLEX_NORM_CX; REAL_ABS_POS] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LE_LDIV_EQ; COMPLEX_NORM_NZ] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* In particular we get the Fundamental Theorem of Algebra.                  *)
(* ------------------------------------------------------------------------- *)

let FTA = prove
 (`!a n. a(0) = Cx(&0) \/ ~(!k. k IN 1..n ==> a(k) = Cx(&0))
         ==> ?z. vsum(0..n) (\i. a(i) * z pow i) = Cx(&0)`,
  REPEAT STRIP_TAC THENL
   [EXISTS_TAC `Cx(&0)` THEN
    SIMP_TAC[VSUM_CLAUSES_LEFT; LE_0] THEN
    ASM_SIMP_TAC[ADD_CLAUSES; COMPLEX_POW_ZERO; LE_1; COMPLEX_ADD_LID;
                 COMPLEX_MUL_RZERO; COMPLEX_MUL_LZERO] THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0; VSUM_0];
    MATCH_MP_TAC LIOUVILLE_WEAK_INVERSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_ON_VSUM THEN
      SIMP_TAC[FINITE_NUMSEG; HOLOMORPHIC_ON_POW; HOLOMORPHIC_ON_MUL;
               HOLOMORPHIC_ON_CONST; HOLOMORPHIC_ON_ID];
      ASM_MESON_TAC[COMPLEX_POLYFUN_EXTREMAL]]]);;

let EXISTS_COMPLEX_ROOT = prove
 (`!a n. ~(n = 0) ==> ?z. z pow n = a`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[COMPLEX_ROOT_POLYFUN; LE_1] THEN
  MATCH_MP_TAC FTA THEN DISJ2_TAC THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
  ASM_SIMP_TAC[IN_NUMSEG; LE_REFL; LE_1] THEN CONV_TAC COMPLEX_RING);;

(* ------------------------------------------------------------------------- *)
(* Weierstrass convergence theorem.                                          *)
(* ------------------------------------------------------------------------- *)

let HOLOMORPHIC_UNIFORM_LIMIT = prove
 (`!net:(A net) f g z r.
        ~(trivial_limit net) /\
        eventually
           (\n. (f n) continuous_on cball(z,r) /\
                (f n) holomorphic_on ball(z,r))
           net /\
        (!e. &0 < e
             ==> eventually (\n. !x. x IN cball(z,r) ==> norm(f n x - g x) < e)
                            net)
        ==> g continuous_on cball(z,r) /\ g holomorphic_on ball(z,r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISJ_CASES_TAC(REAL_ARITH `r <= &0 \/ &0 < r`) THENL
   [ASM_SIMP_TAC[BALL_EMPTY; holomorphic_on; NOT_IN_EMPTY] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
     `r <= &0 ==> r < &0 \/ r = &0`)) THEN
    ASM_SIMP_TAC[continuous_on; CBALL_EMPTY; CBALL_SING; NOT_IN_EMPTY] THEN
    SIMP_TAC[IN_SING; DIST_REFL] THEN MESON_TAC[REAL_LT_01];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_UNIFORM_LIMIT THEN
    MAP_EVERY EXISTS_TAC [`net:A net`; `f:A->complex->complex`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[EVENTUALLY_AND]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\x. Cx(&1) / (Cx(&2) * Cx pi * ii) * g(x:complex)`;
    `g:complex->complex`; `z:complex`; `r:real`; `1`]
     CAUCHY_NEXT_DERIVATIVE_CIRCLEPATH) THEN
  SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_BALL] THEN
  ANTS_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  REWRITE_TAC[ARITH] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    ASM_SIMP_TAC[PATH_IMAGE_CIRCLEPATH; REAL_LT_IMP_LE] THEN
    EXISTS_TAC `cball(z:complex,r)` THEN ASM_REWRITE_TAC[ETA_AX] THEN
    SIMP_TAC[SUBSET; IN_CBALL; IN_ELIM_THM; NORM_SUB; dist; REAL_LE_REFL];
    ALL_TAC] THEN
  X_GEN_TAC `w:complex` THEN DISCH_TAC THEN REWRITE_TAC[COMPLEX_POW_1] THEN
  REWRITE_TAC[complex_div; GSYM COMPLEX_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM complex_div] THEN REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM complex_div] THEN REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC] THEN
  SUBGOAL_THEN
   `(\u. g u / (u - w)) path_integrable_on circlepath(z,r) /\
    ((\n:A. path_integral(circlepath(z,r))
            (\u. f n u / (u - w))) -->
     path_integral(circlepath(z,r)) (\u. g u / (u - w))) net`
  MP_TAC THENL
   [MATCH_MP_TAC PATH_INTEGRAL_UNIFORM_LIMIT_CIRCLEPATH THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(fun th -> MP_TAC th THEN
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO)) THEN
      X_GEN_TAC `a:A` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
      MATCH_MP_TAC PATH_INTEGRABLE_CONTINUOUS_CIRCLEPATH THEN
      ASM_SIMP_TAC[PATH_IMAGE_CIRCLEPATH; REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_DIV THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `cball(z:complex,r)` THEN ASM_REWRITE_TAC[ETA_AX] THEN
        SIMP_TAC[SUBSET; IN_CBALL; IN_ELIM_THM; NORM_SUB; dist; REAL_LE_REFL];
        ALL_TAC] THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_COMPLEX_POW; CONTINUOUS_ON_SUB;
                   CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
      REWRITE_TAC[COMPLEX_POW_EQ_0; ARITH; IN_ELIM_THM] THEN
      GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
      SIMP_TAC[COMPLEX_SUB_0] THEN DISCH_THEN SUBST_ALL_TAC THEN
      ASM_MESON_TAC[IN_BALL; dist; REAL_LT_REFL; DIST_SYM];
      ALL_TAC] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e * abs(r - norm(w - z:complex))`) THEN
    SUBGOAL_THEN `&0 < e * abs(r - norm(w - z:complex))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[GSYM REAL_ABS_NZ] THEN
      SIMP_TAC[REAL_SUB_0] THEN
      ASM_MESON_TAC[IN_BALL; dist; REAL_LT_REFL; DIST_SYM];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
    X_GEN_TAC `a:A` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:complex` THEN
    ASM_SIMP_TAC[PATH_IMAGE_CIRCLEPATH; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[IN_CBALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
    ASM_REWRITE_TAC[dist; REAL_LE_REFL] THEN
    SUBGOAL_THEN `~(x:complex = w)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      ASM_MESON_TAC[IN_BALL; dist; NORM_SUB; REAL_LT_REFL];
      ALL_TAC] THEN
    ASM_SIMP_TAC[COMPLEX_FIELD
     `~(x = w) ==> a / (x - w) - b / (x - w) =
                   (a - b:complex) / (x - w)`] THEN
    ASM_SIMP_TAC[COMPLEX_NORM_DIV; REAL_LT_LDIV_EQ; COMPLEX_NORM_NZ;
                 COMPLEX_POW_EQ_0; COMPLEX_SUB_0] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x < a ==> x < b`) THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_LT_IMP_LE; COMPLEX_NORM_POW] THEN
    MATCH_MP_TAC(REAL_ARITH `w < r /\ r <= x + w ==> abs(r - w) <= x`) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[IN_BALL; dist; NORM_SUB]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM dist] THEN MESON_TAC[DIST_TRIANGLE];
    ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP HAS_PATH_INTEGRAL_INTEGRAL) THEN
  DISCH_THEN(MP_TAC o SPEC `Cx(&1) / (Cx(&2) * Cx pi * ii)` o
    MATCH_MP HAS_PATH_INTEGRAL_COMPLEX_LMUL) THEN
  MATCH_MP_TAC EQ_IMP THEN REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC LIM_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`net:A net`; `\n. (f:A->complex->complex) n w`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[tendsto; dist] THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
    REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL]] THEN
  SUBGOAL_THEN
   `((\n:A. Cx(&2) * Cx pi * ii * f n w)
     --> path_integral (circlepath (z,r)) (\u. g u / (u - w))) net`
  MP_TAC THENL
   [MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN EXISTS_TAC
     `\n:A. path_integral (circlepath (z,r)) (\u. f n u / (u - w))` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> MP_TAC th THEN
     MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO)) THEN
    X_GEN_TAC `a:A` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
    MATCH_MP_TAC CAUCHY_INTEGRAL_CIRCLEPATH THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `Cx(&1) / (Cx(&2) * Cx pi * ii)` o
    MATCH_MP LIM_COMPLEX_LMUL) THEN
  SIMP_TAC[CX_2PII_NZ; COMPLEX_FIELD
   `~(x * y * z = Cx(&0)) ==> Cx(&1) / (x * y * z) * x * y * z * w = w`]);;

(* ------------------------------------------------------------------------- *)
(* Version showing that the limit is the limit of the derivatives.           *)
(* ------------------------------------------------------------------------- *)

let HAS_COMPLEX_DERIVATIVE_UNIFORM_LIMIT = prove
 (`!net:(A net) f f' g z r.
        &0 < r /\ ~(trivial_limit net) /\
        eventually
          (\n. (f n) continuous_on cball(z,r) /\
               (!w. w IN ball(z,r)
                    ==> ((f n) has_complex_derivative (f' n w)) (at w)))
          net /\
        (!e. &0 < e
             ==> eventually (\n. !x. x IN cball(z,r) ==> norm(f n x - g x) < e)
                            net)
        ==> g continuous_on cball(z,r) /\
            ?g'. !w. w IN ball(z,r)
                     ==> (g has_complex_derivative (g' w)) (at w) /\
                         ((\n. f' n w) --> g' w) net`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`net:(A)net`; `f:A->complex->complex`;
                `g:complex->complex`; `z:complex`; `r:real`]
               HOLOMORPHIC_UNIFORM_LIMIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(fun th ->
      MP_TAC th THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ]
        EVENTUALLY_MONO)) THEN
    SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_BALL] THEN MESON_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_BALL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM])) THEN
  REWRITE_TAC[SKOLEM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `g':complex->complex` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[LIM_NULL] THEN MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC
   `\n. Cx(&1) / (Cx(&2) * Cx pi * ii) *
        (path_integral(circlepath(z,r)) (\x. f (n:A) x / (x - w) pow 2) -
         path_integral(circlepath(z,r)) (\x. g x / (x - w) pow 2))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      MP_TAC th THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ]
        EVENTUALLY_MONO)) THEN
    X_GEN_TAC `a:A` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[COMPLEX_SUB_LDISTRIB] THEN BINOP_TAC THEN
    MATCH_MP_TAC COMPLEX_DERIVATIVE_UNIQUE_AT THENL
     [EXISTS_TAC `(f:A->complex->complex) a`;
      EXISTS_TAC `g:complex->complex`] THEN
    EXISTS_TAC `w:complex` THEN ASM_SIMP_TAC[] THEN
    W(fun (asl,w) -> MP_TAC(PART_MATCH (rand o rand)
      CAUCHY_DERIVATIVE_INTEGRAL_CIRCLEPATH w)) THEN
    ASM_SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_BALL] THEN
    ANTS_TAC THEN SIMP_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_VEC_0] THEN
  SUBST1_TAC(SYM(SPEC `Cx(&1) / (Cx(&2) * Cx pi * ii)` COMPLEX_MUL_RZERO)) THEN
  MATCH_MP_TAC LIM_COMPLEX_MUL THEN REWRITE_TAC[LIM_CONST] THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN REWRITE_TAC[GSYM LIM_NULL] THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (rand o rand)
      PATH_INTEGRAL_UNIFORM_LIMIT_CIRCLEPATH w)) THEN
  ANTS_TAC THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(fun th -> MP_TAC th THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO)) THEN
    X_GEN_TAC `a:A` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC PATH_INTEGRABLE_CONTINUOUS_CIRCLEPATH THEN
    ASM_SIMP_TAC[PATH_IMAGE_CIRCLEPATH; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_DIV THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `cball(z:complex,r)` THEN ASM_REWRITE_TAC[ETA_AX] THEN
      SIMP_TAC[SUBSET; IN_CBALL; IN_ELIM_THM; NORM_SUB; dist; REAL_LE_REFL];
      ALL_TAC] THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_COMPLEX_POW; CONTINUOUS_ON_SUB;
                 CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
    REWRITE_TAC[COMPLEX_POW_EQ_0; ARITH; IN_ELIM_THM] THEN
    GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    SIMP_TAC[COMPLEX_SUB_0] THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_MESON_TAC[IN_BALL; dist; REAL_LT_REFL; DIST_SYM];
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e * abs(r - norm(w - z:complex)) pow 2`) THEN
  SUBGOAL_THEN `&0 < e * abs(r - norm(w - z:complex)) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[GSYM REAL_ABS_NZ] THEN
    SIMP_TAC[REAL_SUB_0] THEN
    ASM_MESON_TAC[IN_BALL; dist; REAL_LT_REFL; DIST_SYM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  X_GEN_TAC `a:A` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:complex` THEN
  ASM_SIMP_TAC[PATH_IMAGE_CIRCLEPATH; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[IN_CBALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  ASM_REWRITE_TAC[dist; REAL_LE_REFL] THEN
  SUBGOAL_THEN `~(x:complex = w)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    ASM_MESON_TAC[IN_BALL; dist; NORM_SUB; REAL_LT_REFL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[COMPLEX_FIELD
   `~(x = w) ==> a / (x - w) pow 2 - b / (x - w) pow 2 =
                 (a - b:complex) / (x - w) pow 2`] THEN
  ASM_SIMP_TAC[COMPLEX_NORM_DIV; REAL_LT_LDIV_EQ; COMPLEX_NORM_NZ;
               COMPLEX_POW_EQ_0; COMPLEX_SUB_0] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x < a ==> x < b`) THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_LT_IMP_LE; COMPLEX_NORM_POW] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
  MATCH_MP_TAC(REAL_ARITH `w < r /\ r <= x + w ==> abs(r - w) <= x`) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[IN_BALL; dist; NORM_SUB]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM dist] THEN MESON_TAC[DIST_TRIANGLE]);;

(* ------------------------------------------------------------------------- *)
(* Some more simple/convenient versions for applications.                    *)
(* ------------------------------------------------------------------------- *)

let HOLOMORPHIC_UNIFORM_SEQUENCE = prove
 (`!f g s.
        open s /\
        (!n. (f n) holomorphic_on s) /\
        (!x. x IN s
             ==> ?d. &0 < d /\ cball(x,d) SUBSET s /\
                     !e. &0 < e
                         ==> eventually (\n. !y. y IN cball(x,d)
                                                 ==> norm(f n y - g y) < e)
                                        sequentially)
        ==> g holomorphic_on s`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[HOLOMORPHIC_ON_OPEN] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`sequentially`; `f:num->complex->complex`;
                 `g:complex->complex`; `z:complex`; `r:real`]
                HOLOMORPHIC_UNIFORM_LIMIT) THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN ANTS_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
    ASM_MESON_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON; HOLOMORPHIC_ON_SUBSET;
                  BALL_SUBSET_CBALL];
    SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_BALL] THEN
    ASM_MESON_TAC[CENTRE_IN_BALL]]);;

let HAS_COMPLEX_DERIVATIVE_UNIFORM_SEQUENCE = prove
 (`!f f' g s.
        open s /\
        (!n x. x IN s ==> ((f n) has_complex_derivative f' n x) (at x)) /\
        (!x. x IN s
             ==> ?d. &0 < d /\ cball(x,d) SUBSET s /\
                     !e. &0 < e
                         ==> eventually (\n. !y. y IN cball(x,d)
                                                 ==> norm(f n y - g y) < e)
                                        sequentially)
        ==> ?g'. !x. x IN s ==> (g has_complex_derivative g'(x)) (at x) /\
                                ((\n. f' n x) --> g'(x)) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`sequentially`; `f:num->complex->complex`;
                 `f':num->complex->complex`;
                 `g:complex->complex`; `z:complex`; `r:real`]
                HAS_COMPLEX_DERIVATIVE_UNIFORM_LIMIT) THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN ANTS_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[CENTRE_IN_BALL]] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    ASM_MESON_TAC[HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT; SUBSET];
    ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET]]);;

(* ------------------------------------------------------------------------- *)
(* A one-stop shop for an analytic function defined by a series.             *)
(* ------------------------------------------------------------------------- *)

let SERIES_AND_DERIVATIVE_COMPARISON = prove
 (`!f f' s k h.
     open s /\
     (!n x. n IN k /\ x IN s ==> (f n has_complex_derivative f' n x) (at x)) /\
     (?l. (lift o h sums l) k) /\
     (?N. !n x. N <= n /\ n IN k /\ x IN s ==> norm(f n x) <= h n)
          ==> ?g g'. !x. x IN s
                         ==> ((\n. f n x) sums g x) k /\
                             ((\n. f' n x) sums g' x) k /\
                             (g has_complex_derivative g' x) (at x)`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SERIES_COMPARISON_UNIFORM) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:complex->complex` THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[TAUT `a ==> b /\ c /\ d <=> (a ==> b) /\ (a ==> d /\ c)`] THEN
  REWRITE_TAC[FORALL_AND_THM; RIGHT_EXISTS_AND_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[sums; LIM_SEQUENTIALLY] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[sums] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_UNIFORM_SEQUENCE THEN
  EXISTS_TAC `\n x. vsum
    (k INTER (0..n)) (\n. (f:num->complex->complex) n x)` THEN
  ASM_SIMP_TAC[HAS_COMPLEX_DERIVATIVE_VSUM; FINITE_INTER_NUMSEG; IN_INTER] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[GSYM dist] THEN
  MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  ASM_MESON_TAC[SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* A version where we only have local uniform/comparative convergence.       *)
(* ------------------------------------------------------------------------- *)

let SERIES_AND_DERIVATIVE_COMPARISON_LOCAL = prove
 (`!f f' s k.
     open s /\
     (!n x. n IN k /\ x IN s ==> (f n has_complex_derivative f' n x) (at x)) /\
     (!x. x IN s
          ==> ?d h N. &0 < d /\ (?l. (lift o h sums l) k) /\
                      !n y. N <= n /\ n IN k /\ y IN ball(x,d)
                               ==> norm(f n y) <= h n)
     ==> ?g g'. !x. x IN s
                    ==> ((\n. f n x) sums g x) k /\
                        ((\n. f' n x) sums g' x) k /\
                        (g has_complex_derivative g' x) (at x)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\x. infsum k (\n. (f:num->complex->complex) n x)` THEN
  REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`d:real`; `h:num->real`; `N:num`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:num->complex->complex`; `f':num->complex->complex`;
                 `ball(z:complex,d) INTER s`; `k:num->bool`; `h:num->real`]
                SERIES_AND_DERIVATIVE_COMPARISON) THEN
  ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; IN_INTER] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:complex->complex` MP_TAC) THEN
  ONCE_REWRITE_TAC[TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM; RIGHT_EXISTS_AND_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_AND_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN
  MATCH_MP_TAC MONO_EXISTS THEN ASM_SIMP_TAC[CENTRE_IN_BALL] THEN
  X_GEN_TAC `g':complex` THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[SUMS_INFSUM; CENTRE_IN_BALL; summable]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `g:complex->complex` THEN
  MP_TAC(ISPEC `ball(z:complex,d) INTER s` OPEN_CONTAINS_BALL) THEN
  ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN
  ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL] THEN MATCH_MP_TAC MONO_EXISTS THEN
  REWRITE_TAC[SUBSET; IN_BALL; IN_INTER] THEN
  ASM_MESON_TAC[INFSUM_UNIQUE; SUBSET; IN_BALL; DIST_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Sometimes convenient to compare with a complex series of +ve reals.       *)
(* ------------------------------------------------------------------------- *)

let SERIES_AND_DERIVATIVE_COMPARISON_COMPLEX = prove
 (`!f f' s k.
     open s /\
     (!n x. n IN k /\ x IN s ==> (f n has_complex_derivative f' n x) (at x)) /\
     (!x. x IN s
          ==> ?d h N. &0 < d /\ summable k h /\
                      (!n. n IN k ==> real(h n) /\ &0 <= Re(h n)) /\
                      (!n y. N <= n /\ n IN k /\ y IN ball(x,d)
                             ==> norm(f n y) <= norm(h n)))
     ==> ?g g'. !x. x IN s
                    ==> ((\n. f n x) sums g x) k /\
                        ((\n. f' n x) sums g' x) k /\
                        (g has_complex_derivative g' x) (at x)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SERIES_AND_DERIVATIVE_COMPARISON_LOCAL THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:complex` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `d:real` THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  DISCH_THEN(X_CHOOSE_THEN `h:num->complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\n. norm((h:num->complex) n)` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [summable]) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `lift(Re l)` THEN MATCH_MP_TAC SUMS_EQ THEN
  EXISTS_TAC `\i:num. lift(Re(h i))` THEN
  ASM_SIMP_TAC[REAL_NORM_POS; o_DEF] THEN
  REWRITE_TAC[RE_DEF] THEN MATCH_MP_TAC SERIES_COMPONENT THEN
  ASM_REWRITE_TAC[DIMINDEX_2; ARITH]);;

let SERIES_DIFFERENTIABLE_COMPARISON_COMPLEX = prove
 (`!f s k.
     open s /\
     (!n x. n IN k /\ x IN s ==> (f n) complex_differentiable (at x)) /\
     (!x. x IN s
          ==> ?d h N. &0 < d /\ summable k h /\
                      (!n. n IN k ==> real(h n) /\ &0 <= Re(h n)) /\
                      (!n y. N <= n /\ n IN k /\ y IN ball(x,d)
                             ==> norm(f n y) <= norm(h n)))
     ==> ?g. !x. x IN s
                 ==> ((\n. f n x) sums g x) k /\
                      g complex_differentiable (at x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[complex_differentiable; RIGHT_AND_EXISTS_THM] THEN
  GEN_REWRITE_TAC (PAT_CONV `\x. a /\ x /\ b ==> x` o ONCE_DEPTH_CONV)
   [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM] THEN
  DISCH_THEN(CHOOSE_THEN (MP_TAC o MATCH_MP
     SERIES_AND_DERIVATIVE_COMPARISON_COMPLEX)) THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* In particular, a power series is analytic inside circle of convergence.   *)
(* ------------------------------------------------------------------------- *)

let POWER_SERIES_AND_DERIVATIVE_0 = prove
 (`!k a r. summable k (\n. a(n) * Cx(r) pow n)
           ==> ?g g'.
                  !z. norm(z) < r
                      ==> ((\n. a(n) * z pow n) sums g(z)) k /\
                          ((\n. Cx(&n) * a(n) * z pow (n - 1)) sums g'(z)) k /\
                          (g has_complex_derivative g' z) (at z)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `&0 < r` THEN
  ASM_SIMP_TAC[NORM_ARITH `~(&0 < r) ==> ~(norm z < r)`] THEN
  SUBGOAL_THEN `!z. norm(z) < r <=> z IN ball(Cx(&0),r)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [REWRITE_TAC[IN_BALL; dist; COMPLEX_SUB_LZERO; NORM_NEG]; ALL_TAC] THEN
  MATCH_MP_TAC SERIES_AND_DERIVATIVE_COMPARISON_COMPLEX THEN
  REWRITE_TAC[OPEN_BALL; IN_BALL; dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN COMPLEX_DIFF_TAC THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`(r - norm(z:complex)) / &2`;
    `\n. Cx(norm(a(n):complex) * ((r + norm(z:complex)) / &2) pow n)`;
    `0`] THEN
  ASM_REWRITE_TAC[REAL_SUB_LT; REAL_HALF; REAL_CX; RE_CX] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[CX_MUL; CX_POW] THEN
    MATCH_MP_TAC POWER_SERIES_CONV_IMP_ABSCONV_WEAK THEN
    EXISTS_TAC `Cx r` THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[COMPLEX_NORM_CX];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[NORM_POS_LE] THEN MATCH_MP_TAC REAL_POW_LE;
    REPEAT STRIP_TAC THEN REWRITE_TAC[COMPLEX_NORM_CX; COMPLEX_NORM_MUL] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NORM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    REWRITE_TAC[COMPLEX_NORM_POW; REAL_ABS_POW] THEN
    MATCH_MP_TAC REAL_POW_LE2] THEN
  ASM_NORM_ARITH_TAC);;

let POWER_SERIES_AND_DERIVATIVE = prove
 (`!k a r w.
        summable k (\n. a(n) * Cx(r) pow n)
        ==> ?g g'.
             !z. z IN ball(w,r)
                 ==> ((\n. a(n) * (z - w) pow n) sums g(z)) k /\
                     ((\n. Cx(&n) * a(n) * (z - w) pow (n - 1)) sums g'(z)) k /\
                     (g has_complex_derivative g' z) (at z)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP POWER_SERIES_AND_DERIVATIVE_0) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`g:complex->complex`; `g':complex->complex`] THEN
  DISCH_TAC THEN
  EXISTS_TAC `(\z. g(z - w)):complex->complex` THEN
  EXISTS_TAC `(\z. g'(z - w)):complex->complex` THEN
  REWRITE_TAC[IN_BALL; dist] THEN X_GEN_TAC `z:complex` THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `z - w:complex`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[NORM_SUB]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM o_DEF] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM COMPLEX_MUL_RID] THEN
  MATCH_MP_TAC COMPLEX_DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
  COMPLEX_DIFF_TAC THEN REWRITE_TAC[COMPLEX_SUB_RZERO]);;

let POWER_SERIES_HOLOMORPHIC = prove
 (`!a k f z r. (!w. w IN ball(z,r) ==> ((\n. a(n) * (w - z) pow n) sums f w) k)
               ==> f holomorphic_on ball(z,r)`,
  REPEAT STRIP_TAC THEN SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_BALL] THEN
  X_GEN_TAC `w:complex` THEN REWRITE_TAC[IN_BALL; dist] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:num->bool`; `a:num->complex`;
                 `(norm(z - w:complex) + r) / &2`; `z:complex`]
                POWER_SERIES_AND_DERIVATIVE) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `z + Cx((norm(z - w) + r) / &2)`) THEN
    REWRITE_TAC[IN_BALL; dist; COMPLEX_RING `(z + w) - z:complex = w`;
                NORM_ARITH `norm(z - (z + w)) = norm w`; summable] THEN
    ANTS_TAC THENL [REWRITE_TAC[COMPLEX_NORM_CX]; MESON_TAC[]] THEN
    POP_ASSUM MP_TAC THEN NORM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:complex->complex` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `g':complex->complex` (LABEL_TAC "*")) THEN
  EXISTS_TAC `(g':complex->complex) w` THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT THEN
  MAP_EVERY EXISTS_TAC
   [`g:complex->complex`; `(r - norm(z - w:complex)) / &2`] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `norm(z - w:complex) < r` THEN NORM_ARITH_TAC;
    ALL_TAC;
    REMOVE_THEN "*" (MP_TAC o SPEC `w:complex`) THEN ANTS_TAC THENL
     [ALL_TAC; SIMP_TAC[]] THEN REWRITE_TAC[IN_BALL] THEN
    UNDISCH_TAC `norm(z - w:complex) < r` THEN NORM_ARITH_TAC] THEN
  X_GEN_TAC `u:complex` THEN REWRITE_TAC[dist] THEN DISCH_TAC THEN
  MATCH_MP_TAC SERIES_UNIQUE THEN
  EXISTS_TAC `(\n. a(n) * (u - z) pow n):num->complex` THEN
  EXISTS_TAC `k:num->bool` THEN CONJ_TAC THENL
   [REMOVE_THEN "*" (MP_TAC o SPEC `u:complex`) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]];
    FIRST_X_ASSUM MATCH_MP_TAC] THEN
  REWRITE_TAC[IN_BALL] THEN ASM_NORM_ARITH_TAC);;

let HOLOMORPHIC_IFF_POWER_SERIES = prove
 (`!f z r. f holomorphic_on ball(z,r) <=>
             !w. w IN ball(z,r)
                 ==> ((\n. higher_complex_derivative n f z / Cx(&(FACT n)) *
                       (w - z) pow n) sums
                      f w)
                     (from 0)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[HOLOMORPHIC_POWER_SERIES]; ALL_TAC] THEN
  MATCH_MP_TAC POWER_SERIES_HOLOMORPHIC THEN
  MAP_EVERY EXISTS_TAC
   [`\n. higher_complex_derivative n f z / Cx(&(FACT n))`;
    `from 0`] THEN
  ASM_REWRITE_TAC[]);;

let POWER_SERIES_ANALYTIC = prove
 (`!a k f z r. (!w. w IN ball(z,r) ==> ((\n. a(n) * (w - z) pow n) sums f w) k)
               ==> f analytic_on ball(z,r)`,
  SIMP_TAC[ANALYTIC_ON_OPEN; OPEN_BALL] THEN
  REWRITE_TAC[POWER_SERIES_HOLOMORPHIC]);;

let ANALYTIC_IFF_POWER_SERIES = prove
 (`!f z r. f analytic_on ball(z,r) <=>
             !w. w IN ball(z,r)
                 ==> ((\n. higher_complex_derivative n f z / Cx(&(FACT n)) *
                       (w - z) pow n) sums
                      f w)
                     (from 0)`,
  SIMP_TAC[ANALYTIC_ON_OPEN; OPEN_BALL] THEN
  REWRITE_TAC[HOLOMORPHIC_IFF_POWER_SERIES]);;

(* ------------------------------------------------------------------------- *)
(* Equality between holomorphic functions, on open ball then connected set.  *)
(* ------------------------------------------------------------------------- *)

let HOLOMORPHIC_FUN_EQ_ON_BALL = prove
 (`!f g z r w.
     f holomorphic_on ball(z,r) /\ g holomorphic_on ball(z,r) /\
     w IN ball(z,r) /\
     (!n. higher_complex_derivative n f z = higher_complex_derivative n g z)
     ==> f w = g w`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SERIES_UNIQUE THEN
  EXISTS_TAC `(\n. higher_complex_derivative n f z /
                   Cx (&(FACT n)) * (w - z) pow n)` THEN
  EXISTS_TAC `(from 0)` THEN CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC []] THEN
  ASM_MESON_TAC [HOLOMORPHIC_POWER_SERIES]);;

let HOLOMORPHIC_FUN_EQ_0_ON_BALL = prove
 (`!f z r w.
     w IN ball(z,r) /\ f holomorphic_on ball(z,r) /\
     (!n. higher_complex_derivative n f z = Cx(&0))
     ==> f w = Cx(&0)`,
  REPEAT STRIP_TAC THEN
  SUBST1_TAC (GSYM (BETA_CONV `(\z:complex. Cx(&0)) w`)) THEN
  MATCH_MP_TAC HOLOMORPHIC_FUN_EQ_ON_BALL THEN
  REWRITE_TAC [HOLOMORPHIC_ON_CONST; HIGHER_COMPLEX_DERIVATIVE_CONST] THEN
  ASM_MESON_TAC []);;

let HOLOMORPHIC_FUN_EQ_0_ON_CONNECTED = prove
 (`!f s z.
        open s /\ connected s /\ f holomorphic_on s /\
        z IN s /\ (!n. higher_complex_derivative n f z = Cx(&0))
        ==> !w. w IN s ==> f w = Cx(&0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONNECTED_CLOPEN] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `{w | w IN s /\ !n. higher_complex_derivative n f w = Cx(&0)}`) THEN
  ANTS_TAC THENL [ALL_TAC; ASM SET_TAC[higher_complex_derivative]] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_SUBSET THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `open(s:complex->bool)` THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL; IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `w:complex` THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    X_GEN_TAC `u:complex` THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HOLOMORPHIC_FUN_EQ_0_ON_BALL THEN
    MAP_EVERY EXISTS_TAC [`w:complex`; `e:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_HIGHER_COMPLEX_DERIVATIVE THEN
      ASM_MESON_TAC[HOLOMORPHIC_ON_SUBSET; OPEN_BALL; SUBSET];
      ASM_REWRITE_TAC[HIGHER_COMPLEX_DERIVATIVE_HIGHER_COMPLEX_DERIVATIVE]];
    SUBGOAL_THEN
     `closed_in (subtopology euclidean s)
                (INTERS (IMAGE
              (\n. {w | w IN s /\ higher_complex_derivative n f w = Cx(&0)})
                (:num)))`
    MP_TAC THENL
     [MATCH_MP_TAC CLOSED_IN_INTERS THEN
      REWRITE_TAC[IMAGE_EQ_EMPTY; UNIV_NOT_EMPTY] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `n:num` THEN
      MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE_CONSTANT THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_IMP_CONTINUOUS_ON THEN SIMP_TAC[ETA_AX] THEN
      MATCH_MP_TAC HOLOMORPHIC_HIGHER_COMPLEX_DERIVATIVE THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      SIMP_TAC[INTERS; IN_IMAGE; IN_UNIV; LEFT_IMP_EXISTS_THM; IN_ELIM_THM] THEN
      ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
      REWRITE_TAC[LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN SET_TAC[]]]);;

let HOLOMORPHIC_FUN_EQ_ON_CONNECTED = prove
 (`!f g z s w.
     open s /\ connected s /\ f holomorphic_on s /\ g holomorphic_on s /\
     w IN s /\ z IN s /\
     (!n. higher_complex_derivative n f z = higher_complex_derivative n g z)
     ==> f w = g w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. (f:complex->complex) z - g z`; `s:complex->bool`;
                 `z:complex`] HOLOMORPHIC_FUN_EQ_0_ON_CONNECTED) THEN
  ASM_REWRITE_TAC[RIGHT_IMP_FORALL_THM; HOLOMORPHIC_ON_SUB] THEN
  DISCH_THEN(MP_TAC o SPEC `w:complex`) THEN
  ASM_REWRITE_TAC[COMPLEX_SUB_0] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[HOLOMORPHIC_ON_SUB] THEN
  MP_TAC(ISPECL [`f:complex->complex`; `g:complex->complex`; `s:complex->bool`]
        HIGHER_COMPLEX_DERIVATIVE_SUB) THEN
  ASM_SIMP_TAC[COMPLEX_SUB_0]);;

(* ------------------------------------------------------------------------- *)
(* Some basic lemmas about poles/singularities.                              *)
(* ------------------------------------------------------------------------- *)

let POLE_LEMMA = prove
 (`!f g s a.
        g holomorphic_on s /\ a IN interior(s) /\
        (!z. z IN s /\ ~(z = a) ==> g(z) = (z - a) * f(z))
        ==> (\z. if z = a then complex_derivative g a
                 else (g(z) - g(a)) / (z - a)) holomorphic_on s`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `(a:complex) IN s` ASSUME_TAC THENL
   [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN s /\ ~(z = a)
        ==> (\z. if z = a then complex_derivative g a
                 else (g(z) - g(a)) / (z - a))
            complex_differentiable (at z within s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_TRANSFORM_WITHIN THEN
    EXISTS_TAC `\z:complex. (g(z) - g(a)) / (z - a)` THEN
    EXISTS_TAC `dist(a:complex,z)` THEN ASM_SIMP_TAC[DIST_POS_LT] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `w:complex` THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[REAL_LT_REFL] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `w:complex`) THEN ASM_REWRITE_TAC[] THEN
      REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC COMPLEX_FIELD;
      MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_DIV_WITHIN THEN
      ASM_REWRITE_TAC[COMPLEX_SUB_0] THEN CONJ_TAC THEN
      MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_SUB THEN
      REWRITE_TAC[COMPLEX_DIFFERENTIABLE_CONST; COMPLEX_DIFFERENTIABLE_ID] THEN
      ASM_MESON_TAC[holomorphic_on; complex_differentiable]];
    ALL_TAC] THEN
  REWRITE_TAC[holomorphic_on; GSYM complex_differentiable] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  ASM_CASES_TAC `z:complex = a` THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERIOR]) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_AT_WITHIN THEN
  SUBGOAL_THEN
   `(\z. if z = a then complex_derivative g a else (g z - g a) / (z - a))
    holomorphic_on ball(a,e)`
  MP_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_BALL; GSYM complex_differentiable;
                 CENTRE_IN_BALL; COMPLEX_DIFFERENTIABLE_AT_WITHIN]] THEN
  MATCH_MP_TAC NO_ISOLATED_SINGULARITY THEN
  EXISTS_TAC `{a:complex}` THEN SIMP_TAC[OPEN_BALL; FINITE_RULES] THEN
  MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
    EXISTS_TAC `s DELETE (a:complex)` THEN
    ASM_SIMP_TAC[SET_RULE `b SUBSET s ==> b DIFF {a} SUBSET s DELETE a`] THEN
    ASM_SIMP_TAC[holomorphic_on; GSYM complex_differentiable; IN_DELETE] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_WITHIN_SUBSET THEN
    EXISTS_TAC `s:complex->bool` THEN ASM_SIMP_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[HOLOMORPHIC_ON_OPEN; CONTINUOUS_ON_EQ_CONTINUOUS_AT;
           OPEN_DIFF; FINITE_IMP_CLOSED; OPEN_BALL; FINITE_INSERT;
           FINITE_RULES; GSYM complex_differentiable] THEN
  REWRITE_TAC[IN_DIFF; IN_BALL; IN_SING] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `w:complex` THEN
  ASM_CASES_TAC `w:complex = a` THENL
   [ALL_TAC; ASM_SIMP_TAC[COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT]] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `g holomorphic_on ball(a,e)` MP_TAC THENL
   [ASM_MESON_TAC[HOLOMORPHIC_ON_SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_BALL] THEN
  REWRITE_TAC[GSYM complex_differentiable; IN_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `a:complex`) THEN
  ASM_REWRITE_TAC[GSYM HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_AT; CONTINUOUS_AT] THEN
  MATCH_MP_TAC(REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
              LIM_TRANSFORM_AT) THEN
  EXISTS_TAC `&1` THEN REWRITE_TAC[GSYM DIST_NZ; REAL_LT_01] THEN
  X_GEN_TAC `u:complex` THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let POLE_LEMMA_OPEN = prove
 (`!f g s a.
        open s /\ g holomorphic_on s /\
        (!z. z IN s /\ ~(z = a) ==> g z = (z - a) * f z)
        ==> (\z. if z = a
                 then complex_derivative g a
                 else (g z - g a) / (z - a)) holomorphic_on s`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(a:complex) IN s` THENL
   [MATCH_MP_TAC POLE_LEMMA THEN EXISTS_TAC `f:complex->complex` THEN
    ASM_SIMP_TAC[INTERIOR_OPEN];
    ALL_TAC] THEN
  REWRITE_TAC[holomorphic_on; GSYM complex_differentiable] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_TRANSFORM_WITHIN THEN
  MAP_EVERY EXISTS_TAC [`\z:complex. (g(z) - g(a)) / (z - a)`; `&1`] THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_DIV_WITHIN THEN
  ASM_REWRITE_TAC[COMPLEX_SUB_0; CONJ_ASSOC] THEN
  CONJ_TAC THENL [CONJ_TAC; ASM_MESON_TAC[]] THEN
  MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_SUB THEN
  REWRITE_TAC[COMPLEX_DIFFERENTIABLE_CONST; COMPLEX_DIFFERENTIABLE_ID] THEN
  ASM_MESON_TAC[holomorphic_on; complex_differentiable]);;

let POLE_THEOREM = prove
 (`!f g s a.
        g holomorphic_on s /\ a IN interior(s) /\
        (!z. z IN s /\ ~(z = a) ==> g(z) = (z - a) * f(z))
        ==> (\z. if z = a then complex_derivative g a
                 else f(z) - g(a) / (z - a)) holomorphic_on s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP POLE_LEMMA) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HOLOMORPHIC_TRANSFORM) THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:complex` o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(POP_ASSUM MP_TAC) THEN
  CONV_TAC COMPLEX_FIELD);;

let POLE_THEOREM_OPEN = prove
 (`!f g s a.
        open s /\ g holomorphic_on s /\
        (!z. z IN s /\ ~(z = a) ==> g(z) = (z - a) * f(z))
        ==> (\z. if z = a then complex_derivative g a
                 else f(z) - g(a) / (z - a)) holomorphic_on s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP POLE_LEMMA_OPEN) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HOLOMORPHIC_TRANSFORM) THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:complex` o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(POP_ASSUM MP_TAC) THEN
  CONV_TAC COMPLEX_FIELD);;

let POLE_THEOREM_0 = prove
 (`!f g s a.
        g holomorphic_on s /\ a IN interior(s) /\
        (!z. z IN s /\ ~(z = a) ==> g(z) = (z - a) * f(z)) /\
        f a = complex_derivative g a /\ g(a) = Cx(&0)
        ==> f holomorphic_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. if z = a then complex_derivative g a
         else f(z) - g(a) / (z - a)) holomorphic_on s`
  MP_TAC THENL [ASM_SIMP_TAC[POLE_THEOREM]; ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HOLOMORPHIC_TRANSFORM) THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[complex_div] THEN
  CONV_TAC COMPLEX_RING);;

let POLE_THEOREM_OPEN_0 = prove
 (`!f g s a.
        open s /\ g holomorphic_on s /\
        (!z. z IN s /\ ~(z = a) ==> g(z) = (z - a) * f(z)) /\
        f a = complex_derivative g a /\ g(a) = Cx(&0)
        ==> f holomorphic_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. if z = a then complex_derivative g a
         else f(z) - g(a) / (z - a)) holomorphic_on s`
  MP_TAC THENL [ASM_SIMP_TAC[POLE_THEOREM_OPEN]; ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HOLOMORPHIC_TRANSFORM) THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[complex_div] THEN
  CONV_TAC COMPLEX_RING);;

let POLE_THEOREM_ANALYTIC = prove
 (`!f g s a.
        g analytic_on s /\
        (!z. z IN s
             ==> ?d. &0 < d /\
                     !w. w IN ball(z,d) /\ ~(w = a) ==> g(w) = (w - a) * f(w))
        ==> (\z. if z = a then complex_derivative g a
                 else f(z) - g(a) / (z - a)) analytic_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[analytic_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "A") (LABEL_TAC "B")) THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  REMOVE_THEN "A" (MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min (d:real) e` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MATCH_MP_TAC POLE_THEOREM_OPEN THEN
  ASM_SIMP_TAC[BALL_MIN_INTER; OPEN_BALL; IN_INTER] THEN
  ASM_MESON_TAC[HOLOMORPHIC_ON_SUBSET; INTER_SUBSET]);;

let POLE_THEOREM_ANALYTIC_0 = prove
 (`!f g s a.
        g analytic_on s /\
        (!z. z IN s
             ==> ?d. &0 < d /\
                     !w. w IN ball(z,d) /\ ~(w = a)
                         ==> g(w) = (w - a) * f(w)) /\
        f a = complex_derivative g a /\ g(a) = Cx(&0)
        ==> f analytic_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. if z = a then complex_derivative g a
         else f(z) - g(a) / (z - a)) analytic_on s`
  MP_TAC THENL [ASM_SIMP_TAC[POLE_THEOREM_ANALYTIC]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[complex_div] THEN CONV_TAC COMPLEX_RING);;

let POLE_THEOREM_ANALYTIC_OPEN_SUPERSET = prove
 (`!f g s a t.
        s SUBSET t /\ open t /\ g analytic_on s /\
        (!z. z IN t /\ ~(z = a) ==> g(z) = (z - a) * f(z))
        ==> (\z. if z = a then complex_derivative g a
                 else f(z) - g(a) / (z - a)) analytic_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC POLE_THEOREM_ANALYTIC THEN
  ASM_MESON_TAC[OPEN_CONTAINS_BALL; SUBSET]);;

let POLE_THEOREM_ANALYTIC_OPEN_SUPERSET_0 = prove
 (`!f g s a t.
        s SUBSET t /\ open t /\ g analytic_on s /\
        (!z. z IN t /\ ~(z = a) ==> g(z) = (z - a) * f(z)) /\
        f a = complex_derivative g a /\ g(a) = Cx(&0)
        ==> f analytic_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. if z = a then complex_derivative g a
         else f(z) - g(a) / (z - a)) analytic_on s`
  MP_TAC THENL
   [MATCH_MP_TAC POLE_THEOREM_ANALYTIC_OPEN_SUPERSET THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[complex_div] THEN CONV_TAC COMPLEX_RING);;

(* ------------------------------------------------------------------------- *)
(* First Cartan Theorem.                                                     *)
(* ------------------------------------------------------------------------- *)

let HIGHER_COMPLEX_DERIVATIVE_COMP_LEMMA = prove
 (`!f g z s t n i.
     open s /\ f holomorphic_on s /\ z IN s /\
     open t /\ g holomorphic_on t /\ (!w. w IN s ==> f w IN t) /\
     complex_derivative f z = Cx(&1) /\
     (!i. 1 < i /\ i <= n ==> higher_complex_derivative i f z = Cx(&0)) /\
     i <= n
     ==> higher_complex_derivative i (g o f) z =
         higher_complex_derivative i g (f z)`,
  REPEAT GEN_TAC  THEN
  SUBGOAL_THEN
   `open s /\ f holomorphic_on s /\ z IN s /\ open t /\
      (!w. w IN s ==> f w IN t) /\
      complex_derivative f z = Cx(&1) /\
      (!i. 1 < i /\ i <= n ==> higher_complex_derivative i f z = Cx(&0))
      ==> !i g. g holomorphic_on t /\ i <= n
          ==> higher_complex_derivative i (g o f) z =
              higher_complex_derivative i g (f z)`
    (fun th -> MESON_TAC [th])  THEN
  STRIP_TAC  THEN
  INDUCT_TAC THEN
  REWRITE_TAC [LE_SUC_LT; higher_complex_derivative_alt; o_THM]  THEN
  REPEAT STRIP_TAC  THEN
  EQ_TRANS_TAC `higher_complex_derivative i
             (\w. complex_derivative g (f w) * complex_derivative f w) z` THENL
   [MATCH_MP_TAC HIGHER_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN  THEN
    EXISTS_TAC `s:complex->bool`  THEN
    ASM_REWRITE_TAC []  THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_COMPLEX_DERIVATIVE  THEN
      ASM_REWRITE_TAC []  THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE_GEN  THEN
      EXISTS_TAC `t:complex->bool`  THEN
      ASM_SIMP_TAC [];
      MATCH_MP_TAC HOLOMORPHIC_ON_MUL  THEN
      CONJ_TAC THENL
       [REWRITE_TAC [GSYM o_DEF]  THEN
        MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE_GEN  THEN
        EXISTS_TAC `t:complex->bool`  THEN
        ASM_REWRITE_TAC []  THEN
        MATCH_MP_TAC HOLOMORPHIC_COMPLEX_DERIVATIVE  THEN
        ASM_REWRITE_TAC [];
        ASM_REWRITE_TAC [ETA_AX]  THEN
        MATCH_MP_TAC HOLOMORPHIC_COMPLEX_DERIVATIVE  THEN
        ASM_REWRITE_TAC []];
      REPEAT STRIP_TAC  THEN
      MATCH_MP_TAC COMPLEX_DERIVATIVE_CHAIN  THEN
      ASM_MESON_TAC [HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT]];
    EQ_TRANS_TAC
     `vsum (0..i)
        (\j. Cx (&(binom (i,j))) *
             higher_complex_derivative j (\w. complex_derivative g (f w)) z *
             higher_complex_derivative (i - j) (complex_derivative f) z)` THENL
     [MATCH_MP_TAC HIGHER_COMPLEX_DERIVATIVE_MUL  THEN
      EXISTS_TAC `s:complex->bool`  THEN
      ASM_REWRITE_TAC []  THEN
      ASM_SIMP_TAC [HOLOMORPHIC_COMPLEX_DERIVATIVE]  THEN
      REWRITE_TAC [GSYM o_DEF]  THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE_GEN  THEN
      EXISTS_TAC `t:complex->bool`  THEN
      ASM_REWRITE_TAC []  THEN
      ASM_SIMP_TAC [HOLOMORPHIC_COMPLEX_DERIVATIVE];
      REWRITE_TAC [GSYM higher_complex_derivative_alt]  THEN
      EQ_TRANS_TAC
        `vsum (i..i)
           (\j. Cx (&(binom (i,j))) *
                higher_complex_derivative j
                  (\w. complex_derivative g (f w)) z *
                higher_complex_derivative (SUC (i - j)) f z)` THENL
       [MATCH_MP_TAC VSUM_SUPERSET  THEN
        REWRITE_TAC[SUBSET_NUMSEG; LT_REFL; LE_0;
                    LE_REFL; IN_NUMSEG_0; NUMSEG_SING; IN_SING]  THEN
        X_GEN_TAC `j:num`  THEN
        REWRITE_TAC [ARITH_RULE `j:num <= i /\ ~(j = i) <=> j < i`]  THEN
        DISCH_TAC  THEN
        ASSERT_TAC `1 < SUC (i - j) /\ SUC (i - j) <= n`  THENL
         [ASM_SIMP_TAC [ARITH_RULE
           `i < n /\ j < i ==> 1 < SUC (i - j) /\ SUC (i - j) <= n`]  THEN
          MATCH_MP_TAC (ARITH_RULE `i < n /\ j < i ==> 1 < SUC (i - j)`)  THEN
          ASM_REWRITE_TAC [];
          ASM_SIMP_TAC [COMPLEX_MUL_RZERO; COMPLEX_VEC_0]];
        REWRITE_TAC [NUMSEG_SING; VSUM_SING; BINOM_REFL; SUB_REFL]  THEN
        ASM_REWRITE_TAC [COMPLEX_MUL_LID; COMPLEX_MUL_RID;
                         higher_complex_derivative]  THEN
        ASM_REWRITE_TAC [GSYM o_DEF]  THEN
        REWRITE_TAC [GSYM higher_complex_derivative;
                     higher_complex_derivative_alt]  THEN
        FIRST_X_ASSUM MATCH_MP_TAC  THEN
        ASM_SIMP_TAC [ARITH_RULE `i:num < n ==> i <= n`]  THEN
        MATCH_MP_TAC HOLOMORPHIC_COMPLEX_DERIVATIVE  THEN
        ASM_REWRITE_TAC []]]]);;

let HIGHER_COMPLEX_DERIVATIVE_COMP_ITER_LEMMA = prove
 (`!f s z n m i.
     open s /\ f holomorphic_on s /\ (!w. w IN s ==> f w IN s) /\
     z IN s /\ f z = z /\ complex_derivative f z = Cx (&1) /\
     (!i. 1 < i /\ i <= n ==> higher_complex_derivative i f z = Cx (&0)) /\
     i <= n
     ==> higher_complex_derivative i (ITER m f) z =
         higher_complex_derivative i f z`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC  THEN
  REWRITE_TAC [RIGHT_FORALL_IMP_THM; IMP_CONJ]  THEN
  REWRITE_TAC [IMP_IMP]  THEN
  STRIP_TAC  THEN
  ASSERT_TAC `!m. ITER m f z = z:complex`  THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC [ITER]; ALL_TAC] THEN
  ASSERT_TAC `!m (w:complex). w IN s ==> ITER m f w IN s`  THENL
   [INDUCT_TAC THEN ASM_SIMP_TAC [ITER]; ALL_TAC] THEN
  ASSERT_TAC `!m. ITER m f holomorphic_on s`  THENL
   [INDUCT_TAC THEN REWRITE_TAC [ITER_POINTLESS] THENL
     [ASM_SIMP_TAC [I_DEF; HOLOMORPHIC_ON_ID];
      MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE_GEN  THEN
      EXISTS_TAC `s:complex ->bool`  THEN
      ASM_REWRITE_TAC []];
    ALL_TAC] THEN
  INDUCT_TAC  THENL
   [REWRITE_TAC [ITER_POINTLESS; I_DEF; HIGHER_COMPLEX_DERIVATIVE_ID]  THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
     [ASM_REWRITE_TAC [higher_complex_derivative]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
     [ASM_REWRITE_TAC [higher_complex_derivative; ONE]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_SYM  THEN
    FIRST_X_ASSUM MATCH_MP_TAC  THEN
    ASM_SIMP_TAC [ARITH_RULE `~(i = 0) /\ ~(i = 1) ==> 1 < i`];
    GEN_TAC THEN DISCH_TAC  THEN
    REWRITE_TAC [ITER_ALT_POINTLESS]  THEN
    EQ_TRANS_TAC `higher_complex_derivative i (ITER m f) (f z)`  THENL
     [MATCH_MP_TAC HIGHER_COMPLEX_DERIVATIVE_COMP_LEMMA  THEN
      EXISTS_TAC `s:complex ->bool`  THEN
      EXISTS_TAC `s:complex ->bool`  THEN
      EXISTS_TAC `n:num`  THEN
      ASM_REWRITE_TAC [];
      ASM_REWRITE_TAC []  THEN
      FIRST_X_ASSUM MATCH_MP_TAC  THEN
      ASM_REWRITE_TAC []]]);;

let HIGHER_COMPLEX_DERIVATIVE_ITER_TOP_LEMMA = prove
 (`!f s z n m.
     open s /\ f holomorphic_on s /\ (!w. w IN s ==> f w IN s) /\
     z IN s /\ f z = z /\ complex_derivative f z = Cx (&1) /\
     (!i. 1 < i /\ i < n ==> higher_complex_derivative i f z = Cx (&0)) /\
     1 < n
     ==> higher_complex_derivative n (ITER m f) z =
         Cx(&m) * higher_complex_derivative n f z`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC  THEN
  INDUCT_TAC THEN REWRITE_TAC [LT_SUC_LE] THEN REWRITE_TAC [LT]  THEN
  REWRITE_TAC [RIGHT_FORALL_IMP_THM]  THEN
  STRIP_TAC  THEN
  ASSERT_TAC `!m. ITER m f z = z:complex`  THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC [ITER]; ALL_TAC] THEN
  ASSERT_TAC `!m (w:complex). w IN s ==> ITER m f w IN s`  THENL
   [INDUCT_TAC THEN ASM_SIMP_TAC [ITER]; ALL_TAC] THEN
  ASSERT_TAC `!m. ITER m f holomorphic_on s`  THENL
   [INDUCT_TAC THEN REWRITE_TAC [ITER_POINTLESS]  THEN
    ASM_SIMP_TAC [I_DEF; HOLOMORPHIC_ON_ID]  THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE_GEN  THEN
    EXISTS_TAC `s:complex ->bool`  THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
  ASSERT_TAC `!w. w IN s ==> f complex_differentiable at w`  THENL
   [ASM_MESON_TAC [HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT]; ALL_TAC] THEN
  ASSERT_TAC `!m w. w IN s ==> ITER m f complex_differentiable at w`  THENL
   [ASM_MESON_TAC [HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT]; ALL_TAC] THEN
  ASSERT_TAC `!m. complex_derivative (ITER m f) z = Cx(&1)`  THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC [ITER_POINTLESS]  THENL
     [REWRITE_TAC [I_DEF; COMPLEX_DERIVATIVE_ID]; ALL_TAC] THEN
    ASM_SIMP_TAC [COMPLEX_DERIVATIVE_CHAIN;
                  HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT]  THEN
    REWRITE_TAC [COMPLEX_MUL_LID];
    ALL_TAC] THEN
  INDUCT_TAC THEN
  REWRITE_TAC [higher_complex_derivative_alt; ITER_POINTLESS]  THENL
   [ASM_REWRITE_TAC [COMPLEX_MUL_LZERO; I_DEF; COMPLEX_DERIVATIVE_ID;
                     HIGHER_COMPLEX_DERIVATIVE_CONST;
                     ARITH_RULE `n = 0 <=> ~(1 <= n)`];
    ALL_TAC] THEN
  EQ_TRANS_TAC `higher_complex_derivative n
             (\w. complex_derivative f (ITER m f w) *
                  complex_derivative (ITER m f) w) z`  THENL
   [MATCH_MP_TAC HIGHER_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN  THEN
    EXISTS_TAC `s:complex->bool`  THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC  THENL
     [REWRITE_TAC [o_DEF]  THEN
      MATCH_MP_TAC HOLOMORPHIC_COMPLEX_DERIVATIVE  THEN
      ASM_REWRITE_TAC []  THEN
      ONCE_REWRITE_TAC [GSYM o_DEF]  THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE_GEN  THEN
      EXISTS_TAC `s:complex->bool`  THEN
      ASM_REWRITE_TAC [ETA_AX];
      ALL_TAC] THEN
    CONJ_TAC  THENL
     [MATCH_MP_TAC HOLOMORPHIC_ON_MUL  THEN CONJ_TAC  THENL
       [ONCE_REWRITE_TAC [GSYM o_DEF]  THEN
        MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE_GEN  THEN
        EXISTS_TAC `s:complex->bool`  THEN
        ASM_REWRITE_TAC[ETA_AX]  THEN
        MATCH_MP_TAC HOLOMORPHIC_COMPLEX_DERIVATIVE  THEN
        ASM_REWRITE_TAC[];
        ONCE_REWRITE_TAC [GSYM o_DEF]  THEN
        MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE_GEN  THEN
        EXISTS_TAC `s:complex->bool`  THEN
        ASM_REWRITE_TAC[HOLOMORPHIC_ON_ID]  THEN
        MATCH_MP_TAC HOLOMORPHIC_COMPLEX_DERIVATIVE  THEN
        ASM_REWRITE_TAC[]];
      GEN_TAC THEN DISCH_TAC  THEN
      MATCH_MP_TAC COMPLEX_DERIVATIVE_CHAIN  THEN
      CONJ_TAC  THENL
       [MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT  THEN
        ASM_MESON_TAC [];
        MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT  THEN
        ASM_MESON_TAC []]];
    ALL_TAC] THEN
  EQ_TRANS_TAC
   `vsum (0..n)
      (\i. Cx (&(binom (n,i))) *
           higher_complex_derivative i
             (\w. complex_derivative f (ITER m f w)) z *
           higher_complex_derivative (n - i)
             (complex_derivative (ITER m f)) z)`  THENL
   [MATCH_MP_TAC HIGHER_COMPLEX_DERIVATIVE_MUL  THEN
    EXISTS_TAC `s:complex->bool`  THEN
    ASM_REWRITE_TAC[]  THEN CONJ_TAC  THENL
     [ONCE_REWRITE_TAC [GSYM o_DEF]  THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE_GEN  THEN
      EXISTS_TAC `s:complex->bool`  THEN
      ASM_REWRITE_TAC[ETA_AX]  THEN
      MATCH_MP_TAC HOLOMORPHIC_COMPLEX_DERIVATIVE  THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC HOLOMORPHIC_COMPLEX_DERIVATIVE  THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EQ_TRANS_TAC
   `vsum {0,n}
      (\i. Cx (&(binom (n,i))) *
           higher_complex_derivative i
             (\w. complex_derivative f (ITER m f w)) z *
           higher_complex_derivative (n - i)
             (complex_derivative (ITER m f)) z)`  THENL
   [MATCH_MP_TAC VSUM_SUPERSET  THEN
    REWRITE_TAC [INSERT_SUBSET; EMPTY_SUBSET; IN_NUMSEG_0; LE_0; LE_REFL;
                 IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM]  THEN
    X_GEN_TAC `i:num`  THEN
    STRIP_TAC  THEN
    REWRITE_TAC [GSYM higher_complex_derivative_alt]  THEN
    ASSERT_TAC `1 < SUC (n-i) /\ SUC (n-i) <= n`  THENL
     [ASM_SIMP_TAC [ARITH_RULE `i <= n /\ ~(i=0) /\ ~(i=n)
                                ==> 1 < SUC (n-i) /\ SUC (n-i) <= n`];
      ALL_TAC] THEN
    ASM_SIMP_TAC []  THEN
    SUBGOAL_THEN
      `higher_complex_derivative (SUC (n - i)) (ITER m f) z = Cx(&0)`
      SUBST1_TAC  THENL
     [EQ_TRANS_TAC `higher_complex_derivative (SUC (n - i)) f z`  THENL
       [MATCH_MP_TAC HIGHER_COMPLEX_DERIVATIVE_COMP_ITER_LEMMA  THEN
        EXISTS_TAC `s:complex->bool`  THEN
        ASM_REWRITE_TAC []  THEN
        EXISTS_TAC `n:num`  THEN
        ASM_REWRITE_TAC [];
        FIRST_X_ASSUM MATCH_MP_TAC  THEN
        ASM_REWRITE_TAC []];
      ASM_REWRITE_TAC [COMPLEX_MUL_RZERO; COMPLEX_VEC_0]];
    ALL_TAC] THEN
  SIMP_TAC [VSUM_CLAUSES; FINITE_RULES; IN_INSERT; NOT_IN_EMPTY]  THEN
  REWRITE_TAC [binom; BINOM_REFL; COMPLEX_MUL_LID;
               SUB_REFL; SUB; higher_complex_derivative]  THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC []  THENL
   [REWRITE_TAC [higher_complex_derivative]  THEN
    POP_ASSUM SUBST_ALL_TAC  THEN
    RULE_ASSUM_TAC (REWRITE_RULE [higher_complex_derivative])  THEN
    ASM_REWRITE_TAC [COMPLEX_MUL_RID; COMPLEX_MUL_LID;
                     COMPLEX_VEC_0; COMPLEX_ADD_RID]  THEN
    ASM_MESON_TAC [ARITH_RULE `~(1 <= 0)`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC [COMPLEX_MUL_LID; COMPLEX_VEC_0; COMPLEX_ADD_RID]  THEN
  ASM_REWRITE_TAC [COMPLEX_MUL_RID]  THEN
  ASM_REWRITE_TAC [GSYM higher_complex_derivative_alt]  THEN
  SUBGOAL_THEN
    `(\w. complex_derivative f (ITER m f w)) = complex_derivative f o ITER m f`
    SUBST1_TAC
  THENL [REWRITE_TAC [FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
    `higher_complex_derivative n (complex_derivative f o ITER m f) z =
     higher_complex_derivative n (complex_derivative f) (ITER m f z)`
  SUBST1_TAC  THENL
   [MATCH_MP_TAC HIGHER_COMPLEX_DERIVATIVE_COMP_LEMMA  THEN
    EXISTS_TAC `s:complex->bool`  THEN
    EXISTS_TAC `s:complex->bool`  THEN
    EXISTS_TAC `n:num`  THEN
    ASM_REWRITE_TAC[]  THEN
    ASM_SIMP_TAC[HOLOMORPHIC_COMPLEX_DERIVATIVE; LE_REFL]  THEN
    REPEAT STRIP_TAC  THEN
    EQ_TRANS_TAC `higher_complex_derivative i f z`  THENL
     [MATCH_MP_TAC HIGHER_COMPLEX_DERIVATIVE_COMP_ITER_LEMMA  THEN
      EXISTS_TAC `s:complex->bool`  THEN
      EXISTS_TAC `n:num`  THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASSERT_TAC `Cx (&(SUC m)) = Cx (&m) +  Cx (&1)`  THENL
   [REWRITE_TAC [GSYM CX_ADD; REAL_OF_NUM_ADD; ONE; ADD_SUC; ADD_0];
    ASM_REWRITE_TAC[COMPLEX_POLY_CLAUSES;
                    GSYM higher_complex_derivative_alt]]);;

let CAUCHY_HIGHER_COMPLEX_DERIVATIVE_BOUND = prove
 (`!f z y r B0 n.
     &0 < r /\ 0 < n /\
     f holomorphic_on ball(z,r) /\
     f continuous_on cball(z,r) /\
     (!w. w IN ball(z,r) ==> f w IN ball(y,B0))
     ==> norm (higher_complex_derivative n f z) <= &(FACT n) * B0 / r pow n`,
  REPEAT STRIP_TAC  THEN
  SUBGOAL_THEN `higher_complex_derivative n f z =
                higher_complex_derivative n (\w. f w - y) z`
  SUBST1_TAC  THENL
   [EQ_TRANS_TAC `higher_complex_derivative n (\w. f w) z -
             higher_complex_derivative n (\w. y) z`  THENL
     [ASM_SIMP_TAC
       [HIGHER_COMPLEX_DERIVATIVE_CONST; ARITH_RULE `0<n ==> ~(n=0)`]  THEN
      REWRITE_TAC [COMPLEX_SUB_RZERO; ETA_AX];
      MATCH_MP_TAC EQ_SYM  THEN
      REWRITE_TAC [ETA_AX]  THEN
      MATCH_MP_TAC HIGHER_COMPLEX_DERIVATIVE_SUB  THEN
      EXISTS_TAC `ball(z:complex,r)`  THEN
      ASM_SIMP_TAC [OPEN_BALL; HOLOMORPHIC_ON_CONST; CENTRE_IN_BALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm ((Cx (&2) * Cx pi * ii) / Cx (&(FACT n))
          * higher_complex_derivative n (\w. f w - y) z)
    <= (B0 / r pow (n + 1)) * &2 * pi * r`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_PATH_INTEGRAL_BOUND_CIRCLEPATH  THEN
    EXISTS_TAC `(\u. (f u - y) / (u - z) pow (n + 1))`  THEN
    EXISTS_TAC `z:complex`  THEN STRIP_TAC  THENL
     [MATCH_MP_TAC CAUCHY_HAS_PATH_INTEGRAL_HIGHER_DERIVATIVE_CIRCLEPATH  THEN
      ASM_SIMP_TAC[CENTRE_IN_BALL]  THEN CONJ_TAC  THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUB  THEN
        ASM_REWRITE_TAC [CONTINUOUS_ON_CONST];
        MATCH_MP_TAC HOLOMORPHIC_ON_SUB  THEN
        ASM_REWRITE_TAC [HOLOMORPHIC_ON_CONST]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[]  THEN STRIP_TAC  THENL
     [MATCH_MP_TAC REAL_LE_DIV  THEN STRIP_TAC  THENL
       [MATCH_MP_TAC REAL_LT_IMP_LE  THEN
        MATCH_MP_TAC
         (prove(`(?x. &0 <= x /\ x < B0) ==> &0 < B0`, REAL_ARITH_TAC))  THEN
        EXISTS_TAC `norm ((\u. (f:complex->complex) u - y) z)`  THEN
        SIMP_TAC[NORM_POS_LE]  THEN
        SUBGOAL_THEN
         `!w:complex. f w IN ball(y,B0) ==> norm (f w - y) < B0`
        MATCH_MP_TAC  THENL
         [ASM_MESON_TAC [dist; DIST_SYM; IN_BALL; CENTRE_IN_BALL];
          ALL_TAC] THEN
        FIRST_ASSUM MATCH_MP_TAC  THEN
        ASM_SIMP_TAC[CENTRE_IN_BALL];
        MATCH_MP_TAC(SPECL [`r:real`;`n + 1`] REAL_POW_LE)  THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      REPEAT STRIP_TAC  THEN
      ASM_REWRITE_TAC[COMPLEX_NORM_DIV;COMPLEX_NORM_POW]  THEN
      ASM_SIMP_TAC [REAL_LE_DIV2_EQ; REAL_POW_LT]  THEN
      ONCE_REWRITE_TAC[MESON[] `!(f:complex->complex).
        (f x - y) = (\w. f w - y) x`]  THEN
      MATCH_MP_TAC CONTINUOUS_ON_CLOSURE_NORM_LE  THEN
      EXISTS_TAC `ball(z:complex,r)`  THEN
      ASM_SIMP_TAC[CLOSURE_BALL]  THEN
      REPEAT STRIP_TAC  THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUB  THEN
        ASM_SIMP_TAC[CONTINUOUS_ON_CONST];
        SUBGOAL_THEN
        `!w:complex. f w IN ball(y,B0) ==> norm (f w - y) <= B0`
        MATCH_MP_TAC  THENL
         [REWRITE_TAC[GSYM dist;IN_BALL;DIST_SYM;REAL_LT_IMP_LE];
          ASM_MESON_TAC [dist; DIST_SYM; IN_BALL; CENTRE_IN_BALL]];
        ASM_REWRITE_TAC[cball;IN_ELIM_THM;dist;DIST_SYM]  THEN
        ASM_SIMP_TAC[REAL_EQ_IMP_LE]]];
      ALL_TAC] THEN
  REWRITE_TAC [COMPLEX_NORM_MUL; COMPLEX_NORM_DIV; COMPLEX_NORM_II;
               COMPLEX_NORM_CX; REAL_ABS_NUM; REAL_ABS_PI;
               REAL_MUL_RID]  THEN
  STRIP_TAC  THEN
  ABBREV_TAC `a = (&2 * pi) / &(FACT n)`  THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC  THENL
   [EXPAND_TAC "a"  THEN
    SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_OF_NUM_LT; FACT_LT; ARITH; PI_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
  `B0 / r pow (n + 1) * &2 * pi * r = a * (&(FACT n) * B0 / r pow n)`
  SUBST_ALL_TAC  THENL
   [EXPAND_TAC "a"  THEN
    REWRITE_TAC [GSYM ADD1; real_pow] THEN
    SUBGOAL_THEN `~(&(FACT n) = &0) /\ &0 < r` MP_TAC  THENL
     [ASM_REWRITE_TAC[FACT_NZ; REAL_OF_NUM_EQ];
      CONV_TAC REAL_FIELD];
   ASM_MESON_TAC [REAL_LE_LCANCEL_IMP]]);;

let FIRST_CARTAN_THM_DIM_1 = prove
  (`!f s z n m w.
      open s /\ connected s /\ bounded s /\
      (!w. w IN s ==> f w IN s) /\ f holomorphic_on s /\
      z IN s /\ f z = z /\
      complex_derivative f z = Cx (&1) /\ w IN s
      ==> f w = w`,
   REWRITE_TAC [RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN REPEAT GEN_TAC THEN
   REPEAT DISCH_TAC THEN REPEAT STRIP_TAC THEN EQ_TRANS_TAC `I w:complex` THENL
   [MATCH_MP_TAC HOLOMORPHIC_FUN_EQ_ON_CONNECTED;
    REWRITE_TAC [I_THM]] THEN
   EXISTS_TAC `z:complex` THEN EXISTS_TAC `s:complex->bool` THEN
   ASM_REWRITE_TAC [I_DEF; HOLOMORPHIC_ON_ID] THEN
   GEN_TAC THEN STRIP_ASSUME_TAC (ARITH_RULE `n = 0 \/ n = 1 \/ 1 < n`) THENL
   [ASM_REWRITE_TAC [higher_complex_derivative];
    ASM_REWRITE_TAC [ONE; higher_complex_derivative; COMPLEX_DERIVATIVE_ID];
    ASM_REWRITE_TAC [HIGHER_COMPLEX_DERIVATIVE_ID]] THEN
   ASM_SIMP_TAC [ARITH_RULE `1 < n ==> ~(n=0) /\ ~(n=1)`] THEN
   POP_ASSUM MP_TAC THEN SPEC_TAC (`n:num`,`n:num`) THEN
   MATCH_MP_TAC num_WF THEN REPEAT STRIP_TAC THEN
   REWRITE_TAC [GSYM COMPLEX_NORM_ZERO] THEN
   MATCH_MP_TAC REAL_ARCH_RDIV_EQ_0 THEN REWRITE_TAC [NORM_POS_LE] THEN
   ASSERT_TAC `?c. s SUBSET ball(z:complex,c)` THENL
   [ASSERT_TAC `?c. !w:complex. w IN s ==> norm w <= c` THENL
    [ASM_REWRITE_TAC[GSYM bounded];
     EXISTS_TAC `&2 * c + &1` THEN REWRITE_TAC [SUBSET] THEN GEN_TAC THEN
     DISCH_TAC THEN
     SUBGOAL_THEN `norm (x:complex) <= c /\ norm (z:complex) <= c` MP_TAC THENL
     [ASM_MESON_TAC[]; REWRITE_TAC [IN_BALL] THEN NORM_ARITH_TAC]];
    ALL_TAC] THEN
   ASSERT_TAC `?r. &0 < r /\ cball(z:complex,r) SUBSET s` THENL
   [ASM_MESON_TAC [OPEN_CONTAINS_CBALL];
    EXISTS_TAC `&(FACT n) * c / r pow n`] THEN
   ASSERT_TAC `&0 < c` THENL
   [SUBGOAL_THEN `~(ball(z:complex,c) = {})` MP_TAC THENL
    [ASM SET_TAC[]; ASM_REWRITE_TAC [BALL_EQ_EMPTY; REAL_NOT_LE]];
    ALL_TAC] THEN
   ASSERT_TAC `ball(z:complex,r) SUBSET s` THENL
   [ASM_MESON_TAC [SUBSET_TRANS; BALL_SUBSET_CBALL]; ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
     EXISTS_TAC `&1` THEN REWRITE_TAC [REAL_LT_01; FACT_LE; REAL_OF_NUM_LE];
     MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC [REAL_LT_IMP_LE; REAL_POW_LE]];
    ALL_TAC] THEN
   REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [GSYM COMPLEX_NORM_NUM] THEN
   REWRITE_TAC [GSYM COMPLEX_NORM_MUL] THEN SUBGOAL_THEN
      `Cx(&m) * higher_complex_derivative n f z =
       higher_complex_derivative n (ITER m f) z`
     SUBST1_TAC THENL
   [MATCH_MP_TAC (GSYM HIGHER_COMPLEX_DERIVATIVE_ITER_TOP_LEMMA) THEN
    EXISTS_TAC `s:complex->bool` THEN ASM_SIMP_TAC [];
    ALL_TAC] THEN
   REWRITE_TAC [COMPLEX_NORM_CX; REAL_ABS_NUM; REAL_POS] THEN
   MATCH_MP_TAC CAUCHY_HIGHER_COMPLEX_DERIVATIVE_BOUND THEN
   EXISTS_TAC `z:complex` THEN ASM_SIMP_TAC [ARITH_RULE `1<n ==> 0 < n`] THEN
   ASSERT_TAC `!m w. w:complex IN s ==> ITER m f w IN s` THENL
   [INDUCT_TAC THEN ASM_SIMP_TAC [ITER];
    ASSERT_TAC `!m. ITER m f holomorphic_on s` THENL
    [INDUCT_TAC THEN REWRITE_TAC [ITER_POINTLESS] THENL
     [ASM_SIMP_TAC [I_DEF; HOLOMORPHIC_ON_ID];
      MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE_GEN THEN
      EXISTS_TAC `s:complex->bool` THEN ASM_REWRITE_TAC []];
     ASSERT_TAC `ITER m f holomorphic_on ball(z,r)` THENL
     [MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN ASM SET_TAC [];
      ASM_REWRITE_TAC[]] THEN
     CONJ_TAC THENL
     [ASM_MESON_TAC [CONTINUOUS_ON_SUBSET; HOLOMORPHIC_ON_IMP_CONTINUOUS_ON];
      ASM SET_TAC []]]]);;

(* ------------------------------------------------------------------------- *)
(* Second Cartan Theorem.                                                    *)
(* ------------------------------------------------------------------------- *)

let SECOND_CARTAN_THM_DIM_1 = prove
 (`!g f r.
     &0 < r /\
     g holomorphic_on ball(Cx(&0),r) /\
     (!z. z IN ball(Cx(&0),r) ==> g z IN ball(Cx(&0),r)) /\
     g(Cx(&0)) = Cx(&0) /\
     f holomorphic_on ball(Cx(&0),r) /\
     (!z. z IN ball(Cx(&0),r) ==> f z IN ball(Cx(&0),r)) /\
     f (Cx(&0)) = Cx(&0) /\
     (!z. z IN ball(Cx(&0),r) ==> g (f z) = z) /\
     (!z. z IN ball(Cx(&0),r) ==> f (g z) = z)
     ==> ?t. !z. z IN ball(Cx(&0),r) ==> g z = cexp (ii * Cx t) * z`,
  let COMPLEX_DERIVATIVE_LEFT_INVERSE = prove
    (`!s t f g w.
       open s /\ open t /\
       (!z. z IN s ==> f z IN t) /\ f holomorphic_on s /\
       (!z. z IN t ==> g z IN s) /\ g holomorphic_on t /\
       (!z. z IN s ==> g (f z) = z) /\ w IN s
       ==> complex_derivative f w * complex_derivative g (f w) = Cx(&1)`,
     REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [COMPLEX_MUL_SYM] THEN
     SUBGOAL_THEN `complex_derivative g (f w) * complex_derivative f w =
                   complex_derivative (g o f) w ` SUBST1_TAC THENL
     [ASM_MESON_TAC [HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT;
                     COMPLEX_DERIVATIVE_CHAIN];
      EQ_TRANS_TAC `complex_derivative (\u. u) w` THENL
      [MATCH_MP_TAC COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
       EXISTS_TAC `s:complex->bool` THEN
       ASM_SIMP_TAC[HOLOMORPHIC_ON_ID;o_THM] THEN
       ASM_MESON_TAC [HOLOMORPHIC_ON_COMPOSE_GEN];
       ASM_SIMP_TAC[COMPLEX_DERIVATIVE_ID]]]) in
  let LEMMA_1 = prove
    (`!s f.
        open s /\ connected s /\ f holomorphic_on s /\ Cx(&0) IN s /\
        (!u z. norm u = &1 /\ z IN s ==> u * z IN s) /\
        (!u z. norm u = &1 /\ z IN s ==> f (u * z) = u * f z)
        ==> ?c. !z. z IN s ==> f z = c * z`,
     REPEAT STRIP_TAC THEN ABBREV_TAC `c = complex_derivative f (Cx(&0))` THEN
     EXISTS_TAC `c : complex` THEN
     SUBGOAL_THEN `f(Cx(&0)) = Cx(&0)` ASSUME_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o SPECL [`--Cx(&1)`;`Cx(&0)`]) THEN
      ASM_REWRITE_TAC [NORM_NEG; COMPLEX_NORM_NUM; COMPLEX_MUL_RZERO] THEN
      CONV_TAC COMPLEX_RING; ALL_TAC] THEN
     SUBGOAL_THEN
       `!n u z.
          norm u = &1 /\ z IN s ==>
          u pow n * higher_complex_derivative n f (u * z) =
       u * higher_complex_derivative n f z`
       ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      EQ_TRANS_TAC `higher_complex_derivative n (\w. f (u * w)) z` THENL
      [MATCH_MP_TAC EQ_SYM THEN
       MATCH_MP_TAC HIGHER_COMPLEX_DERIVATIVE_COMPOSE_LINEAR THEN
       EXISTS_TAC `s:complex->bool` THEN EXISTS_TAC `s:complex->bool` THEN
       ASM_SIMP_TAC[]; ALL_TAC] THEN
      EQ_TRANS_TAC `higher_complex_derivative n (\w. u * f w) z` THENL
      [MATCH_MP_TAC HIGHER_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
       EXISTS_TAC `s:complex->bool` THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC
         (REWRITE_RULE [o_DEF]
           (SPECL [`\w:complex. u*w`; `f:complex->complex`]
               HOLOMORPHIC_ON_COMPOSE_GEN)) THEN
        EXISTS_TAC `s:complex->bool` THEN
        ASM_SIMP_TAC [HOLOMORPHIC_ON_LINEAR];
        MATCH_MP_TAC
          (REWRITE_RULE [o_DEF]
            (SPECL [`f:complex->complex`; `\w:complex. u*w`]
                   HOLOMORPHIC_ON_COMPOSE_GEN)) THEN
        EXISTS_TAC `(:complex)` THEN
        ASM_REWRITE_TAC [HOLOMORPHIC_ON_LINEAR; IN_UNIV]];
        POP_ASSUM MP_TAC THEN SPEC_TAC (`z:complex`,`z:complex`) THEN
       SPEC_TAC (`n:num`,`n:num`) THEN INDUCT_TAC THEN
       REWRITE_TAC [higher_complex_derivative] THEN GEN_TAC THEN
       DISCH_TAC THEN EQ_TRANS_TAC
         `complex_derivative (\w. u * higher_complex_derivative n f w) z`
       THENL
       [MATCH_MP_TAC COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
        EXISTS_TAC `s:complex->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
        [MATCH_MP_TAC HIGHER_COMPLEX_DERIVATIVE_HOLOMORPHIC_ON THEN
         ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN
         ASM_REWRITE_TAC [HOLOMORPHIC_ON_CONST];
         MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN
         ASM_REWRITE_TAC [HOLOMORPHIC_ON_CONST; ETA_AX] THEN
         MATCH_MP_TAC HIGHER_COMPLEX_DERIVATIVE_HOLOMORPHIC_ON THEN
         ASM_REWRITE_TAC[]];
        MATCH_MP_TAC COMPLEX_DERIVATIVE_LMUL THEN
        MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT THEN
        ASM_MESON_TAC [HIGHER_COMPLEX_DERIVATIVE_HOLOMORPHIC_ON]]];
      SUBGOAL_THEN
        `!n. 2 <= n ==> higher_complex_derivative n f (Cx(&0)) = Cx(&0)`
        ASSUME_TAC THENL
      [GEN_TAC THEN  DISCH_TAC THEN SUBGOAL_THEN
         `!n z. 2 <= n /\
                (!u. norm u = &1 ==> u pow n * z = u * z) ==> z = Cx(&0)`
         MATCH_MP_TAC THENL
       [REPEAT STRIP_TAC THEN MATCH_MP_TAC
         (COMPLEX_RING
           `!u. ~(u pow n' = u) /\ u pow n' * z = u * z ==> z = Cx(&0)`) THEN
        SUBGOAL_THEN `2 <= n' ==> ?u. norm u = &1 /\ ~(u pow n' = u)`
          (fun th -> ASM_MESON_TAC [th]) THEN
        STRUCT_CASES_TAC (SPEC `n':num` num_CASES) THEN
        REWRITE_TAC
          [ARITH_LE; ARITH_RULE `2 <= SUC n'' <=> 1 <= n''`; complex_pow] THEN
        DISCH_TAC THEN MP_TAC (SPEC `n'':num` COMPLEX_NOT_ROOT_UNITY) THEN
        ASM_REWRITE_TAC [] THEN STRIP_TAC THEN EXISTS_TAC `u:complex` THEN
        ASM_REWRITE_TAC [] THEN POP_ASSUM MP_TAC THEN
        REWRITE_TAC [CONTRAPOS_THM] THEN
        SUBGOAL_THEN `~(u = Cx(&0))` MP_TAC THENL
        [ASM_REWRITE_TAC [GSYM COMPLEX_NORM_ZERO; REAL_OF_NUM_EQ; ARITH_EQ];
         CONV_TAC COMPLEX_FIELD];
        EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPECL [`n:num`;`u:complex`;`Cx(&0)`]) THEN
        ASM_REWRITE_TAC[COMPLEX_MUL_RZERO]];
       REPEAT STRIP_TAC THEN MATCH_MP_TAC
        (REWRITE_RULE []
          (SPECL [`f:complex->complex`; `\z. c*z`; `Cx(&0)`;
                  `s:complex->bool`]
             HOLOMORPHIC_FUN_EQ_ON_CONNECTED)) THEN
       ASM_REWRITE_TAC [COMPLEX_MUL_RZERO; HOLOMORPHIC_ON_LINEAR;
                        HIGHER_COMPLEX_DERIVATIVE_LINEAR] THEN
       GEN_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC `n:num`) THEN
       STRUCT_CASES_TAC (ARITH_RULE `n = 0 \/ n = 1 \/ 2 <= n`) THEN
       ASM_SIMP_TAC [higher_complex_derivative; ARITH_EQ; ARITH_LE; ONE] THEN
       ASM_SIMP_TAC [ARITH_RULE `2 <= n ==> ~(n=0)`] THEN
       ASM_SIMP_TAC [ARITH_RULE `2 <= n ==> ~(n=SUC 0)`]]]) in
  let LEMMA_2 = prove
    (`!r c. &0 < r /\ &0 <= c /\
            (!x. &0 <= x /\ x < r ==> c * x < r)
            ==> c <= &1`,
     REPEAT STRIP_TAC THEN REWRITE_TAC [GSYM REAL_NOT_LT] THEN STRIP_TAC THEN
     FIRST_X_ASSUM (MP_TAC o SPEC `r * (c + &1) / (&2 * c)`) THEN
     REWRITE_TAC [MESON [] `((a ==> b) ==> F) <=> (a /\ ~b)`] THEN
     CONJ_TAC THENL
     [CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
       ALL_TAC] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `r * &1` THEN
      CONJ_TAC THENL [ALL_TAC; REWRITE_TAC [REAL_MUL_RID; REAL_LE_REFL]] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < &2 * c` ASSUME_TAC THENL
      [ASM_REAL_ARITH_TAC;
       ASM_SIMP_TAC [REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC [REAL_NOT_LT] THEN
      ONCE_REWRITE_TAC [REAL_RING `!a b c:real. a * b * c = b * a * c`] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `r * &1` THEN CONJ_TAC THENL
      [REWRITE_TAC [REAL_MUL_RID; REAL_LE_REFL]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
      [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < &2 * c` ASSUME_TAC THENL
      [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
       ASM_SIMP_TAC [REAL_ARITH `&0 < c ==> a * b / c = (a * b) / c`] THEN
       SUBGOAL_THEN `(c * (c + &1)) / (&2 * c) = (c + &1) / &2`
         SUBST1_TAC THENL
       [ASM_SIMP_TAC [RAT_LEMMA5; REAL_ARITH `&0 < &2`] THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]]) in
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
    `!u z. norm u = &1 /\ z IN ball(Cx(&0),r) ==> u * g z = g (u * z)`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN SUBGOAL_THEN `~(u = Cx(&0))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM COMPLEX_NORM_NZ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `!w. w IN ball(Cx(&0),r) ==> f (u * g w) / u = w`
     ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC FIRST_CARTAN_THM_DIM_1 THEN
    EXISTS_TAC `ball(Cx(&0),r)` THEN EXISTS_TAC `Cx(&0)` THEN
    ASM_REWRITE_TAC [OPEN_BALL;CONNECTED_BALL;BOUNDED_BALL;
                    COMPLEX_MUL_RZERO; CENTRE_IN_BALL] THEN
    ASSERT_TAC `!z. norm (u * z) = norm z` THENL
    [ASM_REWRITE_TAC [COMPLEX_NORM_MUL; REAL_MUL_LID]; ALL_TAC] THEN
    ASSERT_TAC `!z. z IN ball(Cx(&0),r) ==> u * z IN ball(Cx(&0),r)` THENL
    [ASM_REWRITE_TAC [COMPLEX_IN_BALL_0]; ALL_TAC] THEN
    ASSERT_TAC `!z. z IN ball(Cx(&0),r) ==> z / u IN ball(Cx(&0),r)` THENL
    [ASM_REWRITE_TAC [COMPLEX_IN_BALL_0; COMPLEX_NORM_DIV; REAL_DIV_1];
     ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
    [MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN CONJ_TAC THENL
     [ALL_TAC; ASM_REWRITE_TAC[HOLOMORPHIC_ON_CONST]] THEN
     SUBGOAL_THEN `(\w:complex. f (u * g w) : complex) = f o (\w. u * g w)`
       SUBST1_TAC THENL
     [REWRITE_TAC [o_DEF]; MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE_GEN] THEN
     EXISTS_TAC `ball(Cx(&0),r)` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN
      ASM_REWRITE_TAC[HOLOMORPHIC_ON_CONST];
      ASM_SIMP_TAC[]];
     ALL_TAC] THEN
    CONJ_TAC THENL
    [REWRITE_TAC [complex_div; COMPLEX_MUL_LZERO]; ALL_TAC] THEN
    SUBGOAL_THEN `Cx(&1) = u / u` SUBST1_TAC THENL
    [ASM_SIMP_TAC [COMPLEX_DIV_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_CDIV_AT THEN
    SUBGOAL_THEN `(\w:complex. f (u * g w) : complex) = f o (\w. u * g w)`
    SUBST1_TAC THENL [REWRITE_TAC [o_DEF]; ALL_TAC] THEN
    SUBGOAL_THEN
    `((\w. f (u * g w)) has_complex_derivative
      complex_derivative f (u * g(Cx(&0))) *
      (u * complex_derivative g (Cx(&0))))
     (at (Cx (&0)))` MP_TAC THENL
    [MATCH_MP_TAC (REWRITE_RULE [o_DEF]
      (SPECL [`\w:complex. u * g(w):complex`; `f:complex->complex`]
      COMPLEX_DIFF_CHAIN_AT)) THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_LMUL_AT THEN
      REWRITE_TAC [HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT THEN
      EXISTS_TAC `ball(Cx(&0),r)` THEN
      ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL];
      REWRITE_TAC [HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT THEN
      EXISTS_TAC `ball(Cx(&0),r)` THEN
      ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL; COMPLEX_MUL_RZERO]];
     SUBGOAL_THEN
       `complex_derivative f (u * g (Cx (&0))) *
        (u * complex_derivative g (Cx (&0))) = u`
       SUBST1_TAC THENL
     [ALL_TAC; REWRITE_TAC[o_DEF]] THEN
     ABBREV_TAC `g' = complex_derivative g (Cx(&0))` THEN
     ABBREV_TAC `f' = complex_derivative f (Cx(&0))` THEN
     SUBGOAL_THEN `f' * g' = Cx(&1)` ASSUME_TAC THENL
     [EXPAND_TAC "g'" THEN EXPAND_TAC "f'" THEN
      SUBGOAL_THEN `complex_derivative g (Cx(&0)) =
                    complex_derivative g (f (Cx(&0)))` SUBST1_TAC THENL
      [ASM_REWRITE_TAC [];
       MATCH_MP_TAC COMPLEX_DERIVATIVE_LEFT_INVERSE THEN
       EXISTS_TAC `ball(Cx(&0),r)` THEN EXISTS_TAC `ball(Cx(&0),r)` THEN
       ASM_REWRITE_TAC [OPEN_BALL; CENTRE_IN_BALL]];
      ASM_REWRITE_TAC [COMPLEX_MUL_RZERO] THEN
      POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_RING]];
    SUBGOAL_THEN `f(u*g(z)) = f (g (u * z)) : complex` MP_TAC THENL
    [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `u * z:complex` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `!x y:complex. x / u = y ==> x = u * y` MATCH_MP_TAC THENL
      [REWRITE_TAC [complex_div] THEN GEN_TAC THEN GEN_TAC THEN
       DISCH_THEN (SUBST1_TAC o GSYM) THEN
       SUBGOAL_THEN `x = (inv u * u) * x` MP_TAC THENL
       [ASM_SIMP_TAC [COMPLEX_MUL_LINV; COMPLEX_MUL_LID];
        REWRITE_TAC [COMPLEX_MUL_AC]];
       POP_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []];
      MATCH_MP_TAC EQ_SYM THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [COMPLEX_IN_BALL_0; COMPLEX_NORM_MUL; REAL_MUL_LID] THEN
      ASM_REWRITE_TAC [GSYM COMPLEX_IN_BALL_0]];
     DISCH_TAC THEN SUBGOAL_THEN
       `g (f (u * g z)) = g (f (g (u * z : complex))) : complex` MP_TAC THENL
     [POP_ASSUM SUBST1_TAC THEN REWRITE_TAC [];
      SUBGOAL_THEN `u * g z IN ball (Cx(&0),r) /\ u * z IN ball(Cx(&0),r)`
      MP_TAC THENL
      [ASM_REWRITE_TAC [COMPLEX_IN_BALL_0; COMPLEX_NORM_MUL; REAL_MUL_LID] THEN
       REWRITE_TAC [GSYM COMPLEX_IN_BALL_0] THEN ASM_SIMP_TAC[];
       ASM_SIMP_TAC[]]]]];
   SUBGOAL_THEN `?c. !z. z IN ball(Cx(&0),r) ==> g z = c * z`
     STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC LEMMA_1 THEN
    ASM_SIMP_TAC [OPEN_BALL; CONNECTED_BALL; CENTRE_IN_BALL] THEN
    SIMP_TAC [COMPLEX_IN_BALL_0; COMPLEX_NORM_MUL; REAL_MUL_LID];
    ALL_TAC] THEN
   SUBGOAL_THEN `norm (c:complex) = &1` ASSUME_TAC THENL
   [ALL_TAC; ASM_MESON_TAC [COMPLEX_NORM_EQ_1_CEXP]] THEN
   SUBGOAL_THEN `~(norm (c:complex) = &0)` ASSUME_TAC THENL
   [REWRITE_TAC [COMPLEX_NORM_ZERO] THEN STRIP_TAC THEN
    SUBGOAL_THEN `Cx(&0) = Cx(r / &2)` MP_TAC THENL
    [ALL_TAC; REWRITE_TAC [CX_INJ] THEN ASM_REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `Cx(r / &2) IN ball(Cx(&0),r)` ASSUME_TAC THENL
    [REWRITE_TAC [COMPLEX_IN_BALL_0; CX_DIV; COMPLEX_NORM_DIV;
                  COMPLEX_NORM_NUM] THEN
     REWRITE_TAC [COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC;
     EQ_TRANS_TAC `g (f (Cx(r / &2)):complex):complex` THENL
     [EQ_TRANS_TAC `c * (f (Cx(r / &2)):complex)` THENL
      [ASM_REWRITE_TAC [COMPLEX_MUL_LZERO]; ASM_MESON_TAC[]];
      ASM_MESON_TAC[]]];
    ALL_TAC] THEN SUBGOAL_THEN `&0 < norm (c:complex)` ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN CONV_TAC NORM_ARITH; ALL_TAC] THEN
    REWRITE_TAC [GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LEMMA_2 THEN EXISTS_TAC `r : real` THEN
    ASM_REWRITE_TAC [NORM_POS_LE] THEN GEN_TAC THEN STRIP_TAC THEN
    ABBREV_TAC `p = Cx x` THEN
    SUBGOAL_THEN `x = norm (p:complex)` SUBST_ALL_TAC THENL
    [EXPAND_TAC "p" THEN REWRITE_TAC [COMPLEX_NORM_CX] THEN
     ASM_REAL_ARITH_TAC;
     REWRITE_TAC [GSYM COMPLEX_NORM_MUL] THEN
     SUBGOAL_THEN `c * p = g p` SUBST1_TAC THENL
     [ALL_TAC; ASM_MESON_TAC [COMPLEX_IN_BALL_0]] THEN
     FIRST_X_ASSUM (MATCH_MP_TAC o GSYM) THEN
     ASM_MESON_TAC [COMPLEX_IN_BALL_0]];
    ALL_TAC] THEN
   SUBST1_TAC (GSYM (SPEC `norm (c:complex)` REAL_INV_INV)) THEN
   MATCH_MP_TAC REAL_INV_1_LE THEN CONJ_TAC THENL
   [ASM_MESON_TAC [REAL_LT_INV]; ALL_TAC] THEN
   MATCH_MP_TAC LEMMA_2 THEN EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC [] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `x = norm (g (f (Cx x):complex):complex)` SUBST1_TAC THENL
   [SUBGOAL_THEN `g (f (Cx x):complex) = Cx x` SUBST1_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN
     REWRITE_TAC [COMPLEX_IN_BALL_0; COMPLEX_NORM_CX] THEN
     ASM_REAL_ARITH_TAC;
     REWRITE_TAC [COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `g (f (Cx x):complex) = c * f (Cx x) : complex`
      SUBST1_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
     REWRITE_TAC [COMPLEX_IN_BALL_0; COMPLEX_NORM_CX] THEN
     ASM_REAL_ARITH_TAC;
     REWRITE_TAC [COMPLEX_NORM_MUL; REAL_MUL_ASSOC] THEN
     ASM_SIMP_TAC [REAL_MUL_LINV; REAL_MUL_LID; GSYM COMPLEX_IN_BALL_0] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     REWRITE_TAC [COMPLEX_IN_BALL_0; COMPLEX_NORM_CX] THEN
     ASM_REAL_ARITH_TAC]]]);;

(* ------------------------------------------------------------------------- *)
(* Cauchy's inequality.                                                      *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_INEQUALITY = prove
 (`!f z r (B:real) n.
     f continuous_on cball(z,r) /\
     f holomorphic_on ball(z,r) /\ &0 < r /\
     (!x:complex. norm(z-x) = r ==> norm(f x) <= B)
     ==> norm (higher_complex_derivative n f z) <= &(FACT n) * B / r pow n`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
  [SUBGOAL_THEN `?x:complex. norm (z-x) = r` STRIP_ASSUME_TAC THENL [
  EXISTS_TAC `z + Cx r` THEN ASM_SIMP_TAC[COMPLEX_ADD_SUB2;NORM_NEG;
  COMPLEX_NORM_CX;REAL_ABS_REFL;REAL_LT_IMP_LE];ALL_TAC] THEN
  ASM_MESON_TAC [NORM_POS_LE;REAL_LE_TRANS];
  SUBGOAL_THEN `norm ((Cx(&2) * Cx pi * ii) / Cx(&(FACT n))
          * higher_complex_derivative n f z)
    <= (B / r pow (n + 1)) * &2 * pi * r` MP_TAC THENL[
  MATCH_MP_TAC HAS_PATH_INTEGRAL_BOUND_CIRCLEPATH THEN
  EXISTS_TAC `\u. (f:complex->complex) u / (u - z) pow (n + 1)` THEN
  EXISTS_TAC `z:complex` THEN CONJ_TAC THENL [MATCH_MP_TAC
  CAUCHY_HAS_PATH_INTEGRAL_HIGHER_DERIVATIVE_CIRCLEPATH THEN
  ASM_SIMP_TAC [CENTRE_IN_BALL]; ALL_TAC] THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC
  [REAL_POW_LE;REAL_LT_IMP_LE];ALL_TAC]THEN ASM_REWRITE_TAC []
  THEN GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC [COMPLEX_NORM_DIV;COMPLEX_NORM_POW] THEN MATCH_MP_TAC
  REAL_LE_TRANS THEN EXISTS_TAC `B:real / r pow (n+1)` THEN
  ASM_SIMP_TAC[ REAL_LE_DIV2_EQ; REAL_POW_LT;NORM_SUB;REAL_LE_REFL];
  REWRITE_TAC[COMPLEX_NORM_DIV;COMPLEX_NORM_MUL; COMPLEX_NORM_II;
  COMPLEX_NORM_CX; REAL_ABS_NUM; REAL_ABS_PI; REAL_MUL_RID;REAL_ABS_NUM]
  THEN SUBGOAL_THEN `B / r pow (n + 1) * &2 * pi * r =
                (&2 * pi) / &(FACT n) * (((&(FACT n) * B) * r/ r pow (n+1)))`
  SUBST1_TAC THENL [SUBGOAL_THEN `~(&(FACT n) = &0)` MP_TAC THENL
  [REWRITE_TAC [FACT_NZ;REAL_OF_NUM_EQ];ALL_TAC]
  THEN CONV_TAC REAL_FIELD;SUBGOAL_THEN `&0 < (&2 * pi) / &(FACT n)` ASSUME_TAC
  THENL[MATCH_MP_TAC REAL_LT_DIV THEN SIMP_TAC[FACT_LT;REAL_OF_NUM_LT] THEN
  MP_TAC PI_POS THEN REAL_ARITH_TAC;SUBGOAL_THEN `(&(FACT n) * B) * r / r pow
  (n + 1) = &(FACT n) * B / r pow n` SUBST1_TAC THENL
  [REWRITE_TAC[GSYM ADD1; real_pow] THEN MP_TAC (ASSUME `&0 < r`) THEN
  CONV_TAC REAL_FIELD; ASM_MESON_TAC [REAL_LE_LCANCEL_IMP]]]]]]);;

(* ------------------------------------------------------------------------- *)
(* A holomorphic function f has only isolated zeros unless f is 0.           *)
(* ------------------------------------------------------------------------- *)

let ISOLATED_ZEROS = prove
 (`!f a z w.
     open a /\ connected a /\ f holomorphic_on a /\ z IN a /\ f z = Cx(&0) /\
     w IN a /\ ~(f w = Cx(&0))
     ==> (?r. &0 < r /\ ball(z,r) SUBSET a /\
              (!w. w IN ball(z,r) /\ ~(w=z) ==> ~(f w = Cx(&0))))`,
  REPEAT STRIP_TAC THEN ASSERT_TAC `?k.
         ~(higher_complex_derivative k f z = Cx(&0)) /\
         (!n. n < k ==> higher_complex_derivative n f z = Cx(&0))` THENL
  [EXISTS_TAC `minimal n. (~(higher_complex_derivative n f z = Cx(&0)))`
  THEN SUBGOAL_THEN `?k'. ~(higher_complex_derivative k' f z = Cx(&0))`
  (fun th-> ASM_MESON_TAC[th;MINIMAL]) THEN REWRITE_TAC[GSYM NOT_FORALL_THM]
  THEN STRIP_TAC THEN ASM_MESON_TAC[HOLOMORPHIC_FUN_EQ_0_ON_CONNECTED];
  ALL_TAC] THEN SUBGOAL_THEN `~(k = 0)`ASSUME_TAC THENL
  [STRIP_TAC THEN MP_TAC(ASSUME `~(higher_complex_derivative k f z = Cx(&0))`)
  THEN ASM_MESON_TAC[higher_complex_derivative];
  STRIP_ASSUME_TAC (MESON [OPEN_CONTAINS_BALL;ASSUME `open (a:complex->bool)`;
  ASSUME `z:complex IN a`] `?s. &0 < s /\ ball (z:complex,s) SUBSET a`)
  THEN ASSUME_TAC (MESON [HOLOMORPHIC_POWER_SERIES;
  ASSUME `f holomorphic_on a`;ASSUME `ball (z:complex,s)
  SUBSET a`;HOLOMORPHIC_ON_SUBSET] `!w:complex. w IN ball(z,s) ==>
  ((\n. higher_complex_derivative n f z / Cx(&(FACT n))*(w -z) pow n) sums f w)
  (from 0)`) THEN ASSERT_TAC `?g:complex->complex. !x:complex.
                x IN ball(z,s) ==>
        (((\n. higher_complex_derivative n f z / Cx(&(FACT n)) *
          (x - z) pow (n-k))) sums g x) (from k)` THENL
  [EXISTS_TAC `\x:complex. lim sequentially
  (\m. vsum (k..m) (\n. higher_complex_derivative n f z / Cx(&(FACT n)) *
  (x - z) pow (n-k)))` THEN GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!m. k..m = (0..m) INTER from k` ASSUME_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_FROM; IN_INTER; IN_ELIM_THM; IN_NUMSEG] THEN
  ARITH_TAC;ASM_REWRITE_TAC[] THEN REWRITE_TAC
  [SET_RULE `!m. (0..m) INTER from k = from k INTER (0..m)`;SUMS_LIM]] THEN
  ASM_CASES_TAC `x:complex = z` THENL
  [ASM_REWRITE_TAC[COMPLEX_SUB_REFL;summable] THEN
  EXISTS_TAC `higher_complex_derivative k f z / Cx(&(FACT k))` THEN
  MATCH_MP_TAC SUMS_EQ THEN EXISTS_TAC `\n. if n = k then
  higher_complex_derivative k f z / Cx(&(FACT k)) else Cx(&0)`
  THEN CONJ_TAC THENL [REWRITE_TAC [IN_FROM] THEN GEN_TAC THEN DISCH_TAC
  THEN COND_CASES_TAC THENL
  [ASM_REWRITE_TAC[COMPLEX_POW_ZERO;SUB_REFL;COMPLEX_MUL_RID];
  ASM_SIMP_TAC[COMPLEX_POW_ZERO; ARITH_RULE `k <= x' /\ ~(x' = k) ==>
  ~(x' - k = 0)`;COMPLEX_MUL_RZERO]]; MATCH_MP_TAC SERIES_VSUM THEN
  EXISTS_TAC `{k:num}` THEN SIMP_TAC [FINITE_SING;from;IN_SING;
  COMPLEX_VEC_0;VSUM_SING] THEN SET_TAC[LE_REFL]];
  MATCH_MP_TAC SUMMABLE_EQ THEN EXISTS_TAC
  `\n. higher_complex_derivative n f z / Cx(&(FACT n)) *
  (x - z) pow n / (x-z) pow k` THEN CONJ_TAC THENL [REWRITE_TAC [IN_FROM]
  THEN GEN_TAC THEN DISCH_TAC THEN SUBGOAL_THEN `(x:complex - z) pow (x' - k)
  = (x - z) pow x' / (x - z) pow k` (fun th->
  REWRITE_TAC[th;COMPLEX_EQ_MUL_LCANCEL]) THEN MATCH_MP_TAC
  COMPLEX_DIV_POW THEN ASM_SIMP_TAC [COMPLEX_SUB_0];
  SUBGOAL_THEN `(\n. higher_complex_derivative n f z / Cx(&(FACT n)) *
  (x - z) pow n / (x - z) pow k) = (\n. (higher_complex_derivative n f z /
  Cx(&(FACT n)) *(x - z) pow n) / (x - z) pow k) ` SUBST1_TAC
  THENL [REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN CONV_TAC COMPLEX_FIELD;
  MATCH_MP_TAC SUMMABLE_COMPLEX_DIV THEN MATCH_MP_TAC SUMMABLE_FROM_ELSEWHERE
  THEN EXISTS_TAC `0` THEN ASM_MESON_TAC[summable]]]];ALL_TAC] THEN
  ASSERT_TAC `~(g (z:complex) = Cx(&0)) /\
  (!x. x IN ball(z,s) ==> f x = (x - z) pow k * g(x))` THENL
  [CONJ_TAC THENL [MATCH_MP_TAC
  (COMPLEX_FIELD `!x y:complex. x = y /\ ~(y= Cx(&0)) ==> ~(x=Cx(&0))`) THEN
  EXISTS_TAC `higher_complex_derivative k f z / Cx(&(FACT k))` THEN
  CONJ_TAC THENL [ONCE_REWRITE_TAC [GSYM COMPLEX_SUB_0] THEN
  MATCH_MP_TAC SERIES_UNIQUE THEN EXISTS_TAC
  `(\n. higher_complex_derivative n f z / Cx(&(FACT n)) *
  Cx(&0) pow (n-k))` THEN EXISTS_TAC `from (k +1)` THEN
  CONJ_TAC THENL [SUBST1_TAC (MESON [VSUM_SING_NUMSEG]
  `higher_complex_derivative k f z / Cx(&(FACT k)) =
  vsum (k..k) (\n. higher_complex_derivative n f z / Cx(&(FACT n))) `)
  THEN SUBGOAL_THEN  `vsum (k..k)  (\n. higher_complex_derivative n f z
  / Cx(&(FACT n))) = vsum (k..((k+1)-1)) (\n. higher_complex_derivative n f z
  / Cx(&(FACT n)) * Cx(&0) pow (n - k))` SUBST1_TAC THENL [
  REWRITE_TAC[VSUM_SING_NUMSEG; COMPLEX_POW_ZERO;SUB_REFL;COMPLEX_MUL_RID;
  ARITH_RULE `((k:num) + 1) -1 = k`];
  MATCH_MP_TAC SUMS_OFFSET THEN ASM_REWRITE_TAC[ARITH_RULE `k:num < k+1`]
  THEN POP_ASSUM (MP_TAC o SPEC `z:complex`) THEN
  ASM_REWRITE_TAC[CENTRE_IN_BALL;COMPLEX_SUB_REFL]];MATCH_MP_TAC
  SUMS_COMPLEX_0 THEN GEN_TAC THEN SIMP_TAC [IN_FROM;COMPLEX_POW_ZERO;
  ARITH_RULE `k + 1 <= n <=> ~(n-k= 0)`;COMPLEX_MUL_RZERO]];
  MATCH_MP_TAC (COMPLEX_FIELD `!x y. ~(x = Cx(&0)) /\ ~(y = Cx(&0))
  ==> ~(x / y = Cx(&0))`) THEN ASM_REWRITE_TAC[GSYM COMPLEX_NORM_ZERO] THEN
  SUBST1_TAC (MESON [COMPLEX_NORM_CX]
  `norm (Cx(&(FACT k))) = abs ((&(FACT k)))`) THEN
  SIMP_TAC [REAL_ABS_ZERO;FACT_LT;REAL_OF_NUM_LT;REAL_LT_IMP_NZ]]; ALL_TAC]
  THEN GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SERIES_UNIQUE THEN
  EXISTS_TAC `(\n. higher_complex_derivative n f z / Cx(&(FACT n)) *
  (x - z) pow n)`THEN EXISTS_TAC `(from 0)` THEN
  CONJ_TAC  THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
  ASM_CASES_TAC `x:complex = z` THENL [
  ASM_REWRITE_TAC[COMPLEX_SUB_REFL] THEN MATCH_MP_TAC SUMS_EQ THEN
  EXISTS_TAC `\n:num. Cx(&0)` THEN  CONJ_TAC THENL
  [REWRITE_TAC[IN_FROM;COMPLEX_POW_ZERO] THEN X_GEN_TAC `n:num` THEN
  DISCH_TAC THEN  COND_CASES_TAC THENL [
  ASM_REWRITE_TAC[higher_complex_derivative] THEN CONV_TAC COMPLEX_FIELD;
  REWRITE_TAC[COMPLEX_MUL_RZERO]];
  ASM_REWRITE_TAC[COMPLEX_POW_ZERO;COMPLEX_MUL_LZERO] THEN
  ASM_REWRITE_TAC[SERIES_0;GSYM COMPLEX_VEC_0]];ALL_TAC] THEN
  MATCH_MP_TAC SUMS_EQ THEN EXISTS_TAC `\n.(x-z) pow k *
  higher_complex_derivative n f z / Cx(&(FACT n)) *(x - z) pow (n - k)`
  THEN CONJ_TAC THENL [REWRITE_TAC[IN_FROM] THEN X_GEN_TAC `n:num`
  THEN DISCH_TAC THEN ASM_CASES_TAC `n:num < k` THENL [ASM_SIMP_TAC[]
  THEN CONV_TAC COMPLEX_FIELD;
  SUBGOAL_THEN `(x:complex-z) pow (n-k) = (x-z) pow n / (x-z) pow k`
  SUBST1_TAC THENL [MATCH_MP_TAC COMPLEX_DIV_POW THEN
  ASM_SIMP_TAC[COMPLEX_SUB_0; ARITH_RULE `~(n:num < k) ==> k <= n`];
  SUBST1_TAC (COMPLEX_FIELD `(x - z) pow k *
     higher_complex_derivative n f z / Cx(&(FACT n)) *
     (x - z) pow n / (x - z) pow k =
         higher_complex_derivative n f z / Cx(&(FACT n)) * (x-z) pow k *
     (x - z) pow n / (x - z) pow k`) THEN MESON_TAC [ASSUME `~(x:complex = z)`;
  COMPLEX_DIV_LMUL;COMPLEX_SUB_0;COMPLEX_POW_EQ_0]]];
  MATCH_MP_TAC SERIES_COMPLEX_LMUL THEN SUBST1_TAC
  (MESON [COMPLEX_ADD_RID] `(g:complex->complex) x = g x + Cx(&0)`) THEN
  SUBGOAL_THEN `Cx(&0) = vsum (0.. (k-1))
  (\n. higher_complex_derivative n f z / Cx(&(FACT n)) * (x - z) pow (n - k))`
  SUBST1_TAC THENL [ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
  REWRITE_TAC [GSYM COMPLEX_VEC_0] THEN MATCH_MP_TAC VSUM_EQ_0 THEN
  REWRITE_TAC [IN_NUMSEG] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE ` ~(k = 0) /\ n <= k - 1 ==> n < k`] THEN
  REWRITE_TAC[COMPLEX_VEC_0] THEN CONV_TAC COMPLEX_FIELD;
  MATCH_MP_TAC SUMS_OFFSET_REV THEN
  ASM_SIMP_TAC[ARITH_RULE `0 <= k /\ ~(k = 0) ==> 0 < k`;LE_0]]]];ALL_TAC] THEN
  ASSERT_TAC `?r. &0 < r /\ (!x:complex. dist (z,x) < r ==>
                ~((g:complex->complex) x = Cx(&0)))` THENL [
  MATCH_MP_TAC CONTINUOUS_ON_OPEN_AVOID THEN
  EXISTS_TAC `ball(z:complex, s)` THEN
  ASM_REWRITE_TAC[OPEN_BALL;CENTRE_IN_BALL]
  THEN MATCH_MP_TAC HOLOMORPHIC_ON_IMP_CONTINUOUS_ON THEN
  MATCH_MP_TAC ANALYTIC_IMP_HOLOMORPHIC THEN MATCH_MP_TAC POWER_SERIES_ANALYTIC
  THEN EXISTS_TAC `\n. higher_complex_derivative (n+k) f z / Cx(&(FACT (n+k)))`
  THEN EXISTS_TAC `from 0` THEN REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC
  THEN REWRITE_TAC[SERIES_FROM] THEN MATCH_MP_TAC LIM_TRANSFORM THEN
  EXISTS_TAC `(\n.vsum (k..(k+n))
  (\n. higher_complex_derivative n f z / Cx(&(FACT n)) *(w' - z) pow (n-k)))`
  THEN CONJ_TAC THENL [SIMP_TAC [VSUM_OFFSET_0;ARITH_RULE
  `!k n :num.(k + n) - k = n`; ARITH_RULE `!k n:num. k <= k + n`;ADD_ASSOC;
  ARITH_RULE `!k n :num.(n + k) - k = n`] THEN
  SUBGOAL_THEN `(\x. vsum (0..x) (\i. higher_complex_derivative (i + k)
         f z / Cx(&(FACT (i + k))) * (w' - z) pow i)
         - vsum (0..x) (\n. higher_complex_derivative (n + k) f z
        / Cx(&(FACT (n + k))) * (w' - z) pow n)) = (\x. Cx(&0))`
        (fun th-> SIMP_TAC[th;COMPLEX_VEC_0;LIM_CONST]) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REWRITE_TAC[COMPLEX_SUB_0];
  SUBGOAL_THEN `(\n. vsum (k..k + n)
  (\n. higher_complex_derivative n f z / Cx(&(FACT n)) *(w' - z) pow (n - k)))
  = (\n. vsum (k..n+k)(\n. higher_complex_derivative n f z / Cx(&(FACT n)) *
  (w' - z) pow (n - k)))` SUBST1_TAC THENL [
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REWRITE_TAC[ADD_SYM];
  MP_TAC (ISPECL [`(\n. vsum (k..n)
        (\n. higher_complex_derivative n f z / Cx(&(FACT n)) *
        (w' - z) pow (n - k)))`;`(g:complex->complex) w'`;`k:num`]
  SEQ_OFFSET) THEN ONCE_REWRITE_TAC[GSYM SERIES_FROM] THEN ASM_SIMP_TAC[]]];
  ALL_TAC] THEN EXISTS_TAC `min r s` THEN CONJ_TAC THENL
  [MP_TAC (CONJ (ASSUME `&0 < r`) (ASSUME `&0 < s`)) THEN REAL_ARITH_TAC;
  CONJ_TAC THENL [REWRITE_TAC[real_min] THEN COND_CASES_TAC
  THENL [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(z:complex,s)`
  THEN ASM_REWRITE_TAC[ball] THEN SET_TAC[ASSUME `r:real <= s`;REAL_LTE_TRANS];
  ASM_REWRITE_TAC[]];GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:complex->complex) w' =
                (w' - z) pow k * (g:complex->complex) w'` SUBST1_TAC
   THENL [FIRST_ASSUM MATCH_MP_TAC THEN
  MP_TAC (ASSUME `w':complex IN ball (z,min r s)`) THEN REWRITE_TAC [real_min]
  THEN COND_CASES_TAC THENL [ASM_MESON_TAC[IN_BALL;REAL_LTE_TRANS];
  REWRITE_TAC[]];SIMP_TAC [COMPLEX_ENTIRE;DE_MORGAN_THM] THEN
  CONJ_TAC THENL  [REWRITE_TAC[COMPLEX_POW_EQ_0;DE_MORGAN_THM]
  THEN DISJ1_TAC THEN ASM_REWRITE_TAC [COMPLEX_SUB_0];
  FIRST_X_ASSUM MATCH_MP_TAC THEN MP_TAC (ASSUME `w':complex IN
  ball (z,min r s)`) THEN REWRITE_TAC [real_min] THEN COND_CASES_TAC
  THENL [REWRITE_TAC[IN_BALL];
  ASM_MESON_TAC[REAL_NOT_LE;IN_BALL;REAL_LT_TRANS]]]]]]]);;

(* ------------------------------------------------------------------------- *)
(* Analytic continuation.                                                    *)
(* ------------------------------------------------------------------------- *)

let ANALYTIC_CONTINUATION = prove
 (`!f a u z.
     open a /\ connected a /\ f holomorphic_on a /\ u SUBSET a /\ z IN a /\
     z limit_point_of u /\ (!w. w IN u ==> f w = Cx(&0))
     ==> (!w. w IN a ==> f w = Cx(&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[TAUT ` (p ==> q) <=> ~( p /\ (~ q))`;GSYM NOT_EXISTS_THM]
  THEN STRIP_TAC THEN SUBGOAL_THEN  `(f:complex->complex) z = Cx(&0)`
  ASSUME_TAC THENL [STRIP_ASSUME_TAC(MESON [OPEN_CONTAINS_CBALL;
  ASSUME `open (a:complex->bool)`; ASSUME `z:complex IN a`]
  `?e. &0 < e /\ cball (z:complex,e) SUBSET a`) THEN ABBREV_TAC
  `s = cball(z:complex,e) INTER (u:complex->bool)` THEN
  ASSERT_TAC `f:complex->complex continuous_on closure s /\
                (!x:complex. x IN s ==> f x = Cx(&0)) /\
                z:complex IN closure s`
  THENL [CONJ_TAC THENL [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `a:complex->bool` THEN
  ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON] THEN MATCH_MP_TAC
  SUBSET_TRANS THEN EXISTS_TAC `cball(z:complex,e)` THEN
  ASM_MESON_TAC[CLOSED_CBALL;INTER_SUBSET;CLOSURE_MINIMAL];
  CONJ_TAC THENL [ASM_MESON_TAC[INTER_SUBSET;SUBSET];
  ASM_SIMP_TAC[closure;IN_UNION] THEN DISJ2_TAC THEN SUBGOAL_THEN
  `z:complex limit_point_of s` (fun thm-> SET_TAC[thm]) THEN
  REWRITE_TAC [LIMPT_APPROACHABLE] THEN GEN_TAC THEN DISCH_TAC THEN
  ASSERT_TAC `?x:complex. x IN u /\ ~(x = z) /\ dist (x , z) < min e' e`
  THENL [MP_TAC (ISPECL [`z:complex`;`u:complex->bool`] LIMPT_APPROACHABLE)
  THEN ASM_SIMP_TAC[REAL_LT_MIN];EXISTS_TAC `x:complex` THEN ASM_REWRITE_TAC[]
  THEN CONJ_TAC THENL
  [REWRITE_TAC [GSYM (ASSUME `cball (z:complex,e) INTER u = s`);IN_INTER;
  ASSUME `x:complex IN u`;IN_CBALL] THEN ASM_MESON_TAC[REAL_LT_IMP_LE;
  REAL_LT_MIN;DIST_SYM]; ASM_MESON_TAC [REAL_LT_MIN]]]]];
  ASM_MESON_TAC [CONTINUOUS_CONSTANT_ON_CLOSURE]];
  MP_TAC(SPECL [`f:complex->complex`;`a:complex->bool`;`z:complex`;`w:complex`]
  ISOLATED_ZEROS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?x:complex. x IN ball(z,r) /\ x IN u /\ ~(x=z) /\
    (f:complex->complex) x = Cx(&0)`(fun thm->ASM_MESON_TAC[thm]) THEN
  MP_TAC (ISPECL [`z:complex`;`u:complex->bool`] LIMPT_APPROACHABLE) THEN
  ASM_REWRITE_TAC [] THEN DISCH_TAC THEN POP_ASSUM (MP_TAC o SPEC `r:real`)
  THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN EXISTS_TAC `x':complex`
  THEN ASM_MESON_TAC[IN_BALL;DIST_SYM]]);;

(* ------------------------------------------------------------------------- *)
(* Open mapping theorem.                                                     *)
(* ------------------------------------------------------------------------- *)

let OPEN_MAPPING_THM = prove
  (`!a f.
     open a /\ connected a /\ f holomorphic_on a /\
     ~(?c:complex. !z:complex. z IN a ==> f z = c)
     ==> (!u. open u /\ u SUBSET a ==> open(IMAGE f u))`,
  let LEMMA_ZERO = prove
  (`!f z r. f continuous_on cball(z,r) /\ f holomorphic_on ball(z,r) /\
      &0 < r /\ (!w. norm(z-w) =r ==> norm(f z) < norm(f w))
      ==> (?w. w IN ball(z,r) /\ f w = Cx(&0))`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN  ` ((!x:complex. x IN ball(z,r) ==>
  ~((f:complex->complex) x = Cx(&0))) ==> F ) ==> ( ?w:complex. w IN ball(z,r)
  /\ f w = Cx(&0))` MATCH_MP_TAC THENL [MESON_TAC[];
  STRIP_TAC THEN SUBGOAL_THEN `&0 < norm ((f:complex->complex) z)` ASSUME_TAC
  THENL [ASM_SIMP_TAC[COMPLEX_NORM_NZ; CENTRE_IN_BALL; SPEC `z:complex`
  (ASSUME`!x:complex. x IN ball(z,r) ==> ~((f:complex->complex) x = Cx(&0))`)];
  ALL_TAC] THEN SUBGOAL_THEN
    `(!x:complex. x IN cball(z,r) ==> ~((f:complex->complex) x = Cx(&0)))`
  ASSUME_TAC THENL [GEN_TAC THEN REWRITE_TAC [IN_CBALL;dist]
  THEN REWRITE_TAC[REAL_ARITH `a <= b <=> a < b \/ a = b`] THEN
  REWRITE_TAC [TAUT `((p \/ q) ==> r ) <=> ((p ==> r ) /\ (q ==> r))`] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[IN_BALL;dist];
  DISCH_TAC THEN REWRITE_TAC[GSYM COMPLEX_NORM_ZERO] THEN MATCH_MP_TAC
  REAL_LT_IMP_NZ THEN MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC
  `norm ((f:complex->complex) z)` THEN
  ASM_SIMP_TAC [SPEC `z':complex` (ASSUME `!w:complex. norm (w - z) = r
                ==> norm ((f:complex->complex) z) < norm (f w)`)]];
  ALL_TAC] THEN SUBGOAL_THEN `~(frontier(cball(z:complex,r))={})` ASSUME_TAC
  THENL [REWRITE_TAC[FRONTIER_CBALL;dist] THEN SUBGOAL_THEN `?x:complex.
  norm(z-x) = r` (fun th-> SET_TAC [MEMBER_NOT_EMPTY;th]) THEN EXISTS_TAC
  `z + Cx r` THEN ASM_SIMP_TAC[COMPLEX_ADD_SUB2;NORM_NEG;COMPLEX_NORM_CX;
  REAL_ABS_REFL;REAL_LT_IMP_LE];ALL_TAC] THEN
  ABBREV_TAC `g = \z. inv ((f:complex->complex) z)` THEN ASSERT_TAC
  `(g:complex->complex) continuous_on cball(z,r) /\ g holomorphic_on ball(z,r)`
   THENL [CONJ_TAC THENL [EXPAND_TAC "g" THEN
   REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN GEN_TAC THEN DISCH_TAC
  THEN MATCH_MP_TAC CONTINUOUS_COMPLEX_INV_WITHIN THEN ASM_MESON_TAC
  [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN];EXPAND_TAC "g" THEN MATCH_MP_TAC
  HOLOMORPHIC_ON_INV THEN ASM_REWRITE_TAC[]];ALL_TAC] THEN
  SUBGOAL_THEN `?w:complex. w IN frontier(cball(z,r)) /\
                (!x:complex. x IN frontier(cball(z,r)) ==>
                norm ((f:complex->complex) w) <= norm (f x))`
  STRIP_ASSUME_TAC THENL [MATCH_MP_TAC CONTINUOUS_ATTAINS_INF
  THEN ASM_SIMP_TAC[COMPACT_FRONTIER;COMPACT_CBALL;CBALL_EQ_EMPTY;
  REAL_ARITH `!r:real. &0 < r ==> ~(r < &0)` ] THEN
  SUBGOAL_THEN `lift o (\x. norm ((f:complex->complex) x)) =
                 (lift o norm) o (\x. f x) ` SUBST1_TAC THENL
  [REWRITE_TAC[o_DEF]; MATCH_MP_TAC CONTINUOUS_ON_COMPOSE
  THEN CONJ_TAC THENL [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC
  `cball(z:complex,r)` THEN ASM_REWRITE_TAC[ETA_AX] THEN
  ASM_SIMP_TAC[SUBSET_TRANS;CLOSED_CBALL;FRONTIER_SUBSET_CLOSED];
  ASM_MESON_TAC [CONTINUOUS_ON_LIFT_NORM; HOLOMORPHIC_ON_SUBSET;
  HOLOMORPHIC_ON_IMP_CONTINUOUS_ON;SUBSET_TRANS;CLOSED_CBALL;
  FRONTIER_SUBSET_CLOSED]]];ALL_TAC] THEN
  SUBGOAL_THEN `?w:complex. norm (z-w) = r /\
                norm ((f:complex->complex) w) <= norm (f z)`
                (fun thm -> ASM_MESON_TAC[thm;REAL_NOT_LE])
  THEN EXISTS_TAC `w:complex` THEN CONJ_TAC
  THENL [MP_TAC (ASSUME `w:complex IN frontier (cball (z,r))`) THEN
  REWRITE_TAC[FRONTIER_CBALL;dist] THEN SET_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm ((f:complex->complex) w)` ASSUME_TAC THENL
  [REWRITE_TAC[NORM_POS_LT;COMPLEX_VEC_0] THEN MATCH_MP_TAC (ASSUME `!x.
  x:complex IN cball (z,r) ==> ~(f x = Cx(&0))`) THEN MATCH_MP_TAC
  (SET_RULE `!x:complex u s. x IN u /\ u SUBSET s ==> x IN s `) THEN
  EXISTS_TAC `frontier(cball(z:complex,r))` THEN
  ASM_SIMP_TAC[CLOSED_CBALL;FRONTIER_SUBSET_CLOSED];ALL_TAC] THEN
  SUBGOAL_THEN `inv (norm ((f:complex-> complex) w)) = &1/ (norm (f w))`
  ASSUME_TAC THENL [MATCH_MP_TAC REAL_MUL_RINV_UNIQ THEN MATCH_MP_TAC
  REAL_DIV_LMUL THEN ASM_REWRITE_TAC[COMPLEX_NORM_ZERO;GSYM COMPLEX_NORM_NZ];
  ASSERT_TAC `?x:complex. x IN frontier(cball(z,r)) /\ (!y. y IN
  frontier(cball(z,r)) ==> norm ((g:complex->complex) y) <= norm (g x))`
  THENL [MATCH_MP_TAC CONTINUOUS_ATTAINS_SUP THEN
  ASM_SIMP_TAC[COMPACT_FRONTIER;
  COMPACT_CBALL;CBALL_EQ_EMPTY; REAL_ARITH `!r:real. &0 < r ==> ~(r < &0)`]
  THEN SUBGOAL_THEN `lift o (\x. norm ((g:complex->complex) x)) =
                          (lift o norm) o (\x. g x) ` SUBST1_TAC
  THENL [REWRITE_TAC[o_DEF]; MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  CONJ_TAC THENL [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `cball(z:complex,r)` THEN ASM_REWRITE_TAC[ETA_AX]
  THEN ASM_SIMP_TAC[SUBSET_TRANS;CLOSED_CBALL;
  FRONTIER_SUBSET_CLOSED]; ASM_MESON_TAC [CONTINUOUS_ON_LIFT_NORM;
  HOLOMORPHIC_ON_SUBSET; HOLOMORPHIC_ON_IMP_CONTINUOUS_ON;SUBSET_TRANS;
  CLOSED_CBALL; FRONTIER_SUBSET_CLOSED]]];ALL_TAC] THEN SUBGOAL_THEN
  `&0 < norm ((f:complex->complex) x)` ASSUME_TAC THENL
  [REWRITE_TAC[NORM_POS_LT;COMPLEX_VEC_0] THEN MATCH_MP_TAC
  (ASSUME `!x. x:complex IN cball (z,r) ==> ~(f x = Cx(&0))`)
  THEN MATCH_MP_TAC (SET_RULE `!x:complex u s. x IN u /\ u SUBSET s
                ==> x IN s `) THEN  EXISTS_TAC `frontier(cball(z:complex,r))`
  THEN ASM_SIMP_TAC[CLOSED_CBALL;FRONTIER_SUBSET_CLOSED];
  ABBREV_TAC `B = norm ((g:complex->complex) x)`
  THEN SUBGOAL_THEN `norm (higher_complex_derivative 0 g z) <=
                (&(FACT 0)) * B / (r pow 0) `
  MP_TAC THENL[MATCH_MP_TAC CAUCHY_INEQUALITY THEN
  ASM_REWRITE_TAC[] THEN MP_TAC
  (ASSUME `!y:complex. y IN frontier (cball (z,r)) ==>
                 norm ((g:complex ->complex) y) <= B`)
  THEN SIMP_TAC [FRONTIER_CBALL;dist] THEN SET_TAC[];
  REWRITE_TAC [higher_complex_derivative;FACT;real_pow;
  REAL_MUL_LID;REAL_DIV_1] THEN DISCH_TAC THEN SUBGOAL_THEN
        `inv (norm ((f:complex->complex) z)) <=
        inv (norm (f w)) ==> norm (f w) <= norm (f z)` MATCH_MP_TAC
  THENL [SUBGOAL_THEN `inv (norm ((f:complex-> complex) z)) =
                         &1/ (norm (f z))` SUBST1_TAC
  THENL [MATCH_MP_TAC REAL_MUL_RINV_UNIQ THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < norm ((f:complex->complex) z) ==>
  ~(norm (f z) = &0) `]; ASM_REWRITE_TAC[] THEN DISCH_TAC THEN SUBST1_TAC
  (REAL_ARITH `norm ((f:complex->complex) w)= &1 * norm (f w)`) THEN
   SUBST1_TAC(REAL_ARITH `norm ((f:complex->complex) z)=
                        &1 * norm (f z)`) THEN POP_ASSUM
  MP_TAC THEN MATCH_MP_TAC (TAUT `(p <=> q ) ==> ( p ==> q)`)
  THEN MATCH_MP_TAC RAT_LEMMA4 THEN ASM_REWRITE_TAC[]];
  REWRITE_TAC[GSYM COMPLEX_NORM_INV] THEN
  SUBGOAL_THEN `inv ((f:complex->complex) z) = g z /\ inv (f w) = g w`
                (fun thm -> REWRITE_TAC[thm])
  THENL [ASM_MESON_TAC[];MATCH_MP_TAC (REAL_ARITH
  `!x y z:real. x <= y /\ y = z ==> x <= z`) THEN  EXISTS_TAC `B:real` THEN
  ASM_REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL [EXPAND_TAC "B"
  THEN REWRITE_TAC[SYM (ASSUME`(\z. inv ((f:complex->complex) z)) =
  g`);COMPLEX_NORM_INV] THEN SUBGOAL_THEN `inv (norm ((f:complex->complex) x))
  = &1 / norm (f x)` (fun thm -> REWRITE_TAC[thm]) THENL [MATCH_MP_TAC
  REAL_MUL_RINV_UNIQ THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ]; ASM_REWRITE_TAC[] THEN
  MP_TAC (SPEC `x:complex`(ASSUME`!x:complex. x IN frontier (cball (z,r))
                ==> norm ((f:complex->complex) w) <= norm (f x)`))
  THEN REWRITE_TAC [ASSUME`x:complex IN frontier
  (cball (z,r))`] THEN SUBST1_TAC
  (REAL_ARITH `norm ((f:complex->complex) w)= &1* norm (f w)`) THEN
  SUBST1_TAC (REAL_ARITH `norm ((f:complex->complex) x)= &1 * norm (f x)`)
  THEN  DISCH_TAC THEN REWRITE_TAC[REAL_MUL_LID] THEN POP_ASSUM
  MP_TAC THEN MATCH_MP_TAC (TAUT `(q <=> p ) ==> ( p ==> q)`) THEN MATCH_MP_TAC
  (RAT_LEMMA4) THEN ASM_REWRITE_TAC[]];ASM_MESON_TAC[]]]]]]]]) in
  REPEAT STRIP_TAC THEN ASSUME_TAC (MESON [HOLOMORPHIC_ON_SUBSET;
  ASSUME `(u:complex->bool) SUBSET a`;ASSUME `f holomorphic_on a`]
  `f holomorphic_on u`) THEN ASM_CASES_TAC `(u:complex->bool)={}` THENL [
  ASM_MESON_TAC[SUBSET_EMPTY;IMAGE_EQ_EMPTY;OPEN_EMPTY];ALL_TAC] THEN
  SUBGOAL_THEN `!f u. ~(u={}) /\ open u /\ connected u /\
                 f holomorphic_on u /\
         ~(?c:complex. !z:complex. z IN u ==> f z=c) ==>
                         open (IMAGE f u)` ASSUME_TAC
  THENL [REPEAT STRIP_TAC THEN REWRITE_TAC[OPEN_CONTAINS_BALL;IN_IMAGE]
  THEN GEN_TAC THEN STRIP_TAC THEN
  ASSERT_TAC `(\z:complex.(f':complex->complex)z - f' x') holomorphic_on
  (u':complex->bool) /\ (\z:complex. f' z - f' x')x' = Cx(&0)` THENL [
  ASM_SIMP_TAC[HOLOMORPHIC_ON_CONST;HOLOMORPHIC_ON_SUB;
  BETA_THM;COMPLEX_SUB_REFL];ALL_TAC] THEN
  ASSERT_TAC `?s:real. &0 < s /\ ball(x',s) SUBSET u' /\
        (!z:complex. z IN ball(x',s) /\ ~(z = x') ==>
        ~((\z:complex.(f':complex->complex)z - f' x') z = Cx(&0)))` THENL [
  MATCH_MP_TAC ISOLATED_ZEROS THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[COMPLEX_SUB_0];
  ASSERT_TAC `?r. &0 < r /\ cball(x':complex,r) SUBSET ball(x',s)` THENL[
  EXISTS_TAC `s:real / &2` THEN ASM_SIMP_TAC [REAL_ARITH `&0 < s
  ==> &0 < s/ &2`;SUBSET;IN_CBALL;IN_BALL] THEN MP_TAC (ASSUME `&0 < s`)
  THEN REAL_ARITH_TAC;ALL_TAC] THEN
  ASSERT_TAC `cball(x',r) SUBSET u' /\
     (!z:complex. z IN cball(x',r) /\
        ~(z=x')==> ~((\z:complex.(f':complex->complex)z - f' x') z = Cx(&0)))`
  THENL [CONJ_TAC THENL [ASM_MESON_TAC[SUBSET_TRANS];
  MESON_TAC[ASSUME `!z:complex. z IN ball (x',s) /\ ~(z = x')
  ==> ~((\z. (f':complex->complex) z - f' x') z = Cx(&0))`;
  ASSUME `cball (x':complex,r) SUBSET ball (x',s)`;SUBSET]];ALL_TAC]
  THEN SUBGOAL_THEN `frontier (cball (x':complex,r)) SUBSET u'` ASSUME_TAC
  THENL [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x':complex,r)`
  THEN ASM_MESON_TAC[CLOSED_CBALL;FRONTIER_SUBSET_CLOSED];ALL_TAC] THEN
  ASSERT_TAC `?w. w IN frontier(cball(x':complex,r)) /\
        (!z. z IN frontier(cball(x',r)) ==>
        norm ((f':complex->complex)w - f' x') <= norm(f' z - f' x'))`
  THENL [MATCH_MP_TAC CONTINUOUS_ATTAINS_INF THEN
  ASM_SIMP_TAC[COMPACT_FRONTIER;COMPACT_CBALL;CBALL_EQ_EMPTY;
  REAL_ARITH `!r:real. &0 < r ==> ~(r < &0)` ] THEN
  CONJ_TAC THENL [REWRITE_TAC[FRONTIER_CBALL;dist] THEN
  SUBGOAL_THEN `?x:complex. norm(x'-x) = r` (fun th-> SET_TAC
   [MEMBER_NOT_EMPTY;th]) THEN EXISTS_TAC `x' + Cx r` THEN
  ASM_SIMP_TAC[COMPLEX_ADD_SUB2;NORM_NEG;COMPLEX_NORM_CX;
  REAL_ABS_REFL;REAL_LT_IMP_LE];
  SUBGOAL_THEN `lift o (\z. norm ((f':complex->complex) z - f' x')) =
        (lift o norm) o (\z. f' z - f' x') ` SUBST1_TAC THENL [
  REWRITE_TAC[o_DEF]; MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  ASM_MESON_TAC [CONTINUOUS_ON_LIFT_NORM; HOLOMORPHIC_ON_SUBSET;
  HOLOMORPHIC_ON_IMP_CONTINUOUS_ON]]];ALL_TAC] THEN
  ABBREV_TAC `e = (norm ((f':complex->complex) w - f' x'))*(&1/ &3)`
  THEN SUBGOAL_THEN `&0<e` ASSUME_TAC THENL [
  EXPAND_TAC "e" THEN MATCH_MP_TAC REAL_LT_MUL THEN
  REWRITE_TAC [REAL_ARITH `&0 < &1 / &3`; COMPLEX_NORM_NZ] THEN
  SUBST1_TAC (MESON [BETA_THM] `(f':complex->complex) w - f' x' =
  (\w. f' w - f' x')w `) THEN FIRST_ASSUM MATCH_MP_TAC THEN
  CONJ_TAC THENL[MESON_TAC[ASSUME `w:complex IN frontier (cball (x',r))`;
  FRONTIER_SUBSET_CLOSED; CLOSED_CBALL;SET_RULE `!x:complex s t. x IN s /\
  s SUBSET t ==> x IN t` ];ONCE_REWRITE_TAC[GSYM COMPLEX_SUB_0] THEN
  REWRITE_TAC[GSYM COMPLEX_NORM_ZERO] THEN MATCH_MP_TAC REAL_LT_IMP_NZ
  THEN MATCH_MP_TAC (REAL_ARITH `&0 < r /\ r = norm (w:complex - x') ==>
  &0 < norm (w - x')`) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC (ASSUME `w:complex IN frontier (cball (x',r))`) THEN
  SIMP_TAC [EQ_SYM_EQ;FRONTIER_CBALL;dist;NORM_SUB] THEN SET_TAC[]]; ALL_TAC]
  THEN EXISTS_TAC `e:real` THEN REWRITE_TAC[ASSUME `&0<e`] THEN
  REWRITE_TAC[SUBSET;IN_IMAGE] THEN GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC [GSYM COMPLEX_SUB_0] THEN
  SUBGOAL_THEN `(?x:complex. x IN ball(x',r) /\
        x'' - (f':complex->complex) x = Cx(&0)) ==>
                ?x. x'' - f' x = Cx(&0) /\ x IN u'` MATCH_MP_TAC THENL [
  STRIP_TAC THEN EXISTS_TAC `x''':complex` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC (SET_RULE `!x:complex u s. x IN u /\ u SUBSET s ==> x IN s`)
  THEN EXISTS_TAC `ball(x':complex,r)` THEN ASM_REWRITE_TAC[]
  THEN ASM_MESON_TAC[BALL_SUBSET_CBALL;SUBSET_TRANS];
  MATCH_MP_TAC LEMMA_ZERO THEN CONJ_TAC THENL
  [MATCH_MP_TAC HOLOMORPHIC_ON_IMP_CONTINUOUS_ON THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_SUB THEN ASM_MESON_TAC
  [HOLOMORPHIC_ON_CONST; HOLOMORPHIC_ON_SUBSET];
  CONJ_TAC THENL [MATCH_MP_TAC HOLOMORPHIC_ON_SUB THEN ASM_MESON_TAC[
  HOLOMORPHIC_ON_CONST;HOLOMORPHIC_ON_SUBSET;BALL_SUBSET_CBALL];
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `w':complex` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC  `e:real` THEN CONJ_TAC THENL
  [MESON_TAC [NORM_SUB;dist;IN_BALL; ASSUME`x'':complex IN ball (x,e)`;
  ASSUME `x:complex = (f':complex->complex) x'`];
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2*e` THEN
  ASM_SIMP_TAC[REAL_ARITH `&0<e ==> e <= &2 * e`;NORM_SUB] THEN
  SUBST1_TAC (COMPLEX_RING `(f':complex->complex) w' - x'' =
                 f' w' -x + x - x''`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm ((f':complex->complex) w' - x) - norm (x-x'')` THEN
  CONJ_TAC THENL [SUBST1_TAC (REAL_ARITH `&2 * e = &3 *e - e`) THEN
  MATCH_MP_TAC (REAL_ARITH `!x y z w:real. x<=y /\ z<w ==> x-w <= y-z`)
  THEN CONJ_TAC THENL [EXPAND_TAC "e" THEN
  ASM_REWRITE_TAC[REAL_ARITH `&3 * norm ((f':complex->complex) w - f' x') *
  &1 / &3 = norm (f' w - f' x')`] THEN FIRST_ASSUM MATCH_MP_TAC THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[FRONTIER_CBALL;dist;NORM_SUB] THEN
  SET_TAC[];UNDISCH_TAC `x'':complex IN ball (x,e)` THEN
  REWRITE_TAC [IN_BALL;dist;ASSUME`x:complex = (f':complex->complex) x'`]];
  MATCH_MP_TAC (REAL_ARITH `!x y z:real. x<=y+z ==> x-z<=y`) THEN
  REWRITE_TAC[COMPLEX_NORM_TRIANGLE_SUB]]]]]]];ALL_TAC] THEN
  ASM_CASES_TAC `connected (u:complex->bool)` THENL [
  SUBGOAL_THEN `~(?c:complex. !z:complex. z IN u ==> f z=c)`
          (fun th-> ASM_MESON_TAC [th]) THEN
  ONCE_REWRITE_TAC[GSYM COMPLEX_SUB_0]
  THEN STRIP_TAC THEN ABBREV_TAC `w:complex= CHOICE u` THEN
  ASSUME_TAC (MESON [CHOICE_DEF;GSYM (ASSUME `CHOICE u = w:complex`);
  ASSUME `~(u:complex->bool = {})`] `w:complex IN u`) THEN
  ASSERT_TAC `w:complex limit_point_of u` THENL
  [MATCH_MP_TAC INTERIOR_LIMIT_POINT THEN ASM_SIMP_TAC [INTERIOR_OPEN];
  SUBGOAL_THEN `(\z. (f:complex->complex) z - c) holomorphic_on a` ASSUME_TAC
  THENL [ASM_SIMP_TAC [HOLOMORPHIC_ON_SUB; HOLOMORPHIC_ON_CONST];
  ASSUME_TAC (MESON [ASSUME `w:complex IN u`;ASSUME `u:complex->bool SUBSET a`;
  SET_RULE `w:complex IN u /\ u SUBSET a ==> w IN a`] `w:complex IN a`) THEN
  MP_TAC(SPECL [`\z:complex.(f:complex->complex)z - c`;
        `a:complex->bool`; `u:complex->bool`; `w:complex`]
         ANALYTIC_CONTINUATION) THEN
  ASM_REWRITE_TAC [] THEN MP_TAC (ASSUME `~(?c:complex. !z. z IN a ==>
  (f:complex->complex) z = c)`) THEN ONCE_REWRITE_TAC [GSYM COMPLEX_SUB_0;
  GSYM COMPLEX_SUB_RZERO] THEN ONCE_REWRITE_TAC [COMPLEX_SUB_RZERO] THEN
  MESON_TAC[]]];ALL_TAC] THEN SUBST1_TAC (MESON [UNIONS_COMPONENTS]
  `u:complex->bool = UNIONS ( components u)`) THEN
  REWRITE_TAC [IMAGE_UNIONS] THEN MATCH_MP_TAC OPEN_UNIONS THEN
  REWRITE_TAC[IN_IMAGE] THEN GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  STRIP_ASSUME_TAC(MESON [IN_COMPONENTS;
  ASSUME `(x:complex->bool) IN components u`]
  `?w:complex. w IN u /\ x = connected_component u w`) THEN
  ASM_SIMP_TAC[CONNECTED_COMPONENT_EQ_EMPTY;OPEN_CONNECTED_COMPONENT;
  CONNECTED_CONNECTED_COMPONENT] THEN CONJ_TAC THENL
  [ASM_MESON_TAC [CONNECTED_COMPONENT_SUBSET;
  HOLOMORPHIC_ON_SUBSET]; ONCE_REWRITE_TAC[GSYM COMPLEX_SUB_0] THEN
  STRIP_TAC THEN ABBREV_TAC `y = CHOICE (x:complex->bool)` THEN
  SUBGOAL_THEN `y:complex IN x` ASSUME_TAC THENL
  [EXPAND_TAC "y" THEN MATCH_MP_TAC CHOICE_DEF THEN
  ASM_MESON_TAC [CONNECTED_COMPONENT_EQ_EMPTY];
  ASSUME_TAC (MESON [OPEN_COMPONENTS;ASSUME `open (u:complex->bool)`;
  ASSUME` x:complex->bool IN components u`] `open (x:complex->bool)`) THEN
  ASSERT_TAC `y:complex limit_point_of x` THENL [
  MATCH_MP_TAC INTERIOR_LIMIT_POINT THEN ASSUME_TAC
  (MESON [OPEN_COMPONENTS;ASSUME `open (u:complex->bool)`;
  ASSUME` x:complex->bool IN components u`] `open (x:complex->bool)`) THEN
  SIMP_TAC [INTERIOR_OPEN;ASSUME `open (x:complex->bool)`;
  ASSUME `y:complex IN x`]; SUBGOAL_THEN `(\z. (f:complex->complex) z - c)
  holomorphic_on a` ASSUME_TAC THENL [
  ASM_SIMP_TAC [HOLOMORPHIC_ON_SUB; HOLOMORPHIC_ON_CONST];
  SUBGOAL_THEN `x:complex->bool SUBSET a` ASSUME_TAC THENL [
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `u:complex->bool` THEN
  ASM_REWRITE_TAC[CONNECTED_COMPONENT_SUBSET];
  SUBGOAL_THEN `y:complex IN a` ASSUME_TAC THENL [
  MATCH_MP_TAC (SET_RULE `y:complex IN x /\ x SUBSET a ==> y IN a`)
  THEN ASM_REWRITE_TAC[]; MP_TAC(SPECL [`\z:complex.(f:complex->complex)z - c`;
  `a:complex->bool`; `x:complex->bool`; `y:complex`] ANALYTIC_CONTINUATION)
  THEN ASM_REWRITE_TAC [] THEN MP_TAC (ASSUME `~(?c:complex. !z. z IN a ==>
  (f:complex->complex) z = c)`) THEN
  ONCE_REWRITE_TAC [GSYM COMPLEX_SUB_0;GSYM COMPLEX_SUB_RZERO] THEN
  ONCE_REWRITE_TAC [COMPLEX_SUB_RZERO] THEN MESON_TAC[]]]]]]]);;

(* ------------------------------------------------------------------------- *)
(* Maximum modulus principle.                                                *)
(* ------------------------------------------------------------------------- *)

let MAXIMUM_MODULUS_PRINCIPLE = prove
  (`!f a u w.
      open a /\ connected a /\ f holomorphic_on a /\
      open u /\ u SUBSET a /\ w IN u /\
      (!z. z IN u ==> norm(f z) <= norm(f w))
      ==> (?c. !z. z IN a ==> f z = c)`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
    `~(open (IMAGE (f:complex->complex) u))`
    (fun th -> ASM_MESON_TAC[th; OPEN_MAPPING_THM]) THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL;NOT_FORALL_THM] THEN
  EXISTS_TAC `(f:complex->complex) w` THEN
  MATCH_MP_TAC (TAUT `!p q. (p /\ ~ q) ==> ~(p ==> q)`) THEN CONJ_TAC THENL
  [ASM_MESON_TAC[IN_IMAGE]; ALL_TAC] THEN
  REWRITE_TAC[NOT_EXISTS_THM;DE_MORGAN_THM;SUBSET] THEN
  GEN_TAC THEN ASM_CASES_TAC `~(&0 < e)` THENL
  [ASM_REWRITE_TAC[]; ALL_TAC] THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[] THEN
  DISCH_TAC THEN DISJ2_TAC THEN REWRITE_TAC[NOT_FORALL_THM] THEN
  EXISTS_TAC `if &0 < Re((f:complex->complex) w)
              then f w + Cx(e / &2)
              else f w - Cx(e/ &2) ` THEN
  ABBREV_TAC `x = if &0<Re((f:complex->complex) w)
                  then f w + Cx(e / &2)
                  else f w - Cx(e / &2)` THEN
  MATCH_MP_TAC (TAUT `!p q. (p /\ ~ q) ==> ~(p ==> q)`) THEN CONJ_TAC THENL
  [REWRITE_TAC[IN_BALL;dist] THEN
  MATCH_MP_TAC (REAL_ARITH `!x y z:real. x = y /\ y < z ==> x < z `) THEN
  EXISTS_TAC `e / &2` THEN EXPAND_TAC "x" THEN COND_CASES_TAC THENL
  [ASM_SIMP_TAC [NORM_NEG;COMPLEX_ADD_SUB2;REAL_ARITH `&0 < e ==> e / &2 <e`;
                  COMPLEX_NORM_CX;REAL_ABS_REFL;
                  REAL_ARITH `&0 < e ==> &0 <= e / &2`];
  ASM_SIMP_TAC [COMPLEX_SUB_SUB2; REAL_ARITH `&0 < e ==> e / &2 <e`;
                  COMPLEX_NORM_CX; REAL_ABS_REFL;
                  REAL_ARITH `&0 < e ==> &0 <= e / &2`]]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; NOT_EXISTS_THM; DE_MORGAN_THM] THEN
  GEN_TAC THEN ASM_CASES_TAC `~(x':complex IN u)` THENL
  [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISJ1_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC (NORM_ARITH `!x y:complex. ~(norm x=norm y) ==> ~(x=y)`) THEN
  REWRITE_TAC[REAL_NOT_EQ] THEN DISJ2_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `norm ((f:complex->complex) w)` THEN ASM_SIMP_TAC[] THEN
  EXPAND_TAC "x" THEN COND_CASES_TAC THEN
  REWRITE_TAC [complex_norm;RE_ADD;IM_ADD; IM_CX;RE_CX;REAL_ADD_RID] THENL
  [MATCH_MP_TAC SQRT_MONO_LT THEN CONJ_TAC THENL
  [SIMP_TAC[REAL_ARITH `!x:real. x pow 2 = x*x`;
               REAL_LE_SQUARE;REAL_LE_ADD]; ALL_TAC] THEN
  MATCH_MP_TAC (REAL_ARITH `!x:real y z. x < y ==> x + z < y + z`) THEN
  REWRITE_TAC[GSYM REAL_LT_SQUARE_ABS] THEN
  ASM_SIMP_TAC [REAL_ARITH `!x y. &0 < x /\ &0 < y
                          ==> abs (x+y) = abs x + abs y`;
                REAL_ARITH `!x:real. &0 < x ==> &0 < x / &2`] THEN
  ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC [complex_norm;RE_SUB;IM_SUB; IM_CX;RE_CX;REAL_SUB_RZERO] THEN
  MATCH_MP_TAC SQRT_MONO_LT THEN CONJ_TAC THENL
  [SIMP_TAC[REAL_LE_SQUARE; REAL_LE_ADD;
                REAL_ARITH `!x:real. x pow 2 = x*x`]; ALL_TAC] THEN
  MATCH_MP_TAC (REAL_ARITH `!x:real y z. x < y ==> x + z < y + z`) THEN
  REWRITE_TAC[GSYM REAL_LT_SQUARE_ABS] THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
  ASM_SIMP_TAC [REAL_ARITH `!x y. x <= &0 /\ &0 < y
                            ==> abs (x - y) = abs x + abs y`;
              REAL_ARITH `!x. &0 < x ==> &0 < x/ &2`] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The Schwarz lemma.                                                        *)
(* ------------------------------------------------------------------------- *)

let SCHWARZ_LEMMA = prove
 (`!f. f holomorphic_on ball(Cx(&0),&1) /\
       (!z:complex. norm z < &1 ==> norm (f z) < &1) /\
       f(Cx(&0)) = Cx(&0)
       ==> (!z. norm z < &1 ==> norm(f z) <= norm z) /\
           norm(complex_derivative f(Cx(&0))) <= &1 /\
           ((?z. norm z < &1 /\ ~(z= Cx(&0)) /\ norm(f z) = norm z) \/
            norm(complex_derivative f (Cx(&0))) = &1
            ==> ?c. (!z. norm z < &1 ==> f z = c*z) /\ norm c = &1)`,
  let LEMMA1 = prove
  (`!f a. open a /\ connected a /\ bounded a /\ ~(a = {}) /\
         f holomorphic_on a /\ f continuous_on (closure a)
         ==> (?w. w IN (frontier a) /\
                  (!z. z IN (closure a) ==> norm (f z) <= norm (f w)))`,
  REPEAT STRIP_TAC THEN ASSERT_TAC
    `?x. x IN closure a /\
         (!z. z IN closure a ==>
              norm((f:complex->complex) z) <= norm(f x))` THENL
  [MATCH_MP_TAC CONTINUOUS_ATTAINS_SUP THEN
  ASM_SIMP_TAC [COMPACT_CLOSURE;CLOSURE_EQ_EMPTY] THEN
  SUBGOAL_THEN `lift o (\x. norm((f:complex->complex) x)) =
                 (lift o norm) o (\x. f x) ` SUBST1_TAC THENL
  [REWRITE_TAC[o_DEF]; MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  ASM_REWRITE_TAC [CONTINUOUS_ON_LIFT_NORM;ETA_AX]]; ALL_TAC] THEN
  ASM_CASES_TAC `x:complex IN frontier a` THENL
  [EXISTS_TAC `x:complex` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `x:complex IN interior a` MP_TAC THENL
  [POP_ASSUM MP_TAC THEN REWRITE_TAC[frontier;DIFF] THEN
  SET_TAC[ASSUME `x:complex IN closure a`]; ALL_TAC] THEN
  ASM_SIMP_TAC[INTERIOR_OPEN] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?c. !z. z IN a ==> (f:complex->complex) z = c`
  STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC MAXIMUM_MODULUS_PRINCIPLE THEN
  EXISTS_TAC `a:complex->bool` THEN
  EXISTS_TAC `x:complex` THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN GEN_TAC THEN
  DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[closure;UNION] THEN
  SET_TAC[ASSUME `z:complex IN a`]; ALL_TAC] THEN
  SUBGOAL_THEN `CHOICE(frontier(a:complex->bool)) IN frontier a`
  ASSUME_TAC THENL
  [MATCH_MP_TAC CHOICE_DEF THEN MATCH_MP_TAC FRONTIER_NOT_EMPTY THEN
   CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[NOT_BOUNDED_UNIV]];
   ALL_TAC] THEN
  EXISTS_TAC `CHOICE(frontier(a:complex->bool))` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  SUBGOAL_THEN `!z. z IN closure a ==> (f:complex->complex) z = c`
  ASSUME_TAC THENL
  [MP_TAC (ISPECL [`f:complex->complex`; `closure (a:complex->bool)`;
  `{c:complex}`] CONTINUOUS_CLOSED_PREIMAGE) THEN
  ASM_REWRITE_TAC [CLOSED_CLOSURE; CLOSED_SING] THEN
  ABBREV_TAC `s = {x | x IN closure(a:complex->bool) /\
  (f:complex->complex) x IN {c}}` THEN DISCH_TAC THEN
  SUBGOAL_THEN `closure a SUBSET (s:complex->bool)` ASSUME_TAC THENL
  [MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
  [REWRITE_TAC[SUBSET] THEN EXPAND_TAC "s" THEN
   ASSUME_TAC (MESON [CLOSURE_SUBSET;GSYM SUBSET]
       `!x:complex. x IN a ==> x IN closure a`) THEN
  SET_TAC [ASSUME `!x:complex. x IN a ==> x IN closure a`;
              ASSUME `!z:complex. z IN a ==> f z = c:complex`];
  ASM_REWRITE_TAC[]];
  POP_ASSUM MP_TAC THEN EXPAND_TAC "s" THEN SET_TAC[]];
  EQ_TRANS_TAC `norm(c:complex)` THENL
  [ASM_SIMP_TAC[]; ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
  MATCH_MP_TAC (NORM_ARITH `!x y:complex. x = y ==> norm x = norm y`) THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[frontier;IN_DIFF]]])
  in
  let LEMMA2 = prove
  (`!(f:complex->complex) r w s.
      &0 < r /\ f holomorphic_on ball(Cx(&0),r) /\
      &0 < s /\ ball(w,s) SUBSET ball(Cx(&0),r) /\
      (!z. norm (w-z) < s ==> norm(f z) <= norm(f w))
      ==> (?c. !z. norm z < r ==> f z = c)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL[`f:complex->complex`;`ball (Cx(&0),r)`; `ball (w:complex,s)`;
                `w:complex`] MAXIMUM_MODULUS_PRINCIPLE) THEN
  ASM_REWRITE_TAC[OPEN_BALL; CONNECTED_BALL; IN_BALL;DIST_REFL] THEN
  ASM_REWRITE_TAC[dist;COMPLEX_SUB_LZERO;NORM_NEG])
  in
  let LEMMA3 = prove
  (`!r:real f. f holomorphic_on (ball(Cx(&0),r)) /\ f (Cx(&0))=Cx(&0)
   ==> (?h. h holomorphic_on (ball(Cx(&0),r)) /\
  ((!z. norm z < r ==> f z=z*(h z)) /\
  (complex_derivative f (Cx(&0)))= h (Cx(&0))))`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `h = \z. if z = Cx(&0) then
  complex_derivative f (Cx(&0)) else f z/z` THEN EXISTS_TAC
  `h:complex->complex` THEN ASSERT_TAC `(!z:complex. norm z < r ==>
  (f:complex->complex) z = z * h z) /\ complex_derivative f (Cx(&0))
  = h (Cx(&0))` THENL [CONJ_TAC THENL
  [GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "h" THEN
  COND_CASES_TAC THENL [ASM_REWRITE_TAC[COMPLEX_MUL_LZERO];
  POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_FIELD];
  EXPAND_TAC "h" THEN ASM_REWRITE_TAC[]];ALL_TAC] THEN ASM_REWRITE_TAC[]
  THEN MATCH_MP_TAC  POLE_THEOREM_OPEN_0 THEN  EXISTS_TAC `(f:complex->complex)`
  THEN EXISTS_TAC `Cx(&0)` THEN
  ASM_SIMP_TAC[OPEN_BALL;IN_BALL;COMPLEX_SUB_RZERO;
   dist;COMPLEX_SUB_LZERO;NORM_NEG])
  in
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPECL [`&1`;`f:complex->complex`] LEMMA3) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN SUBGOAL_THEN
    `!z. norm z < &1 ==> norm ((h:complex->complex) z) <= &1`
    ASSUME_TAC THENL
  [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC
  (prove
  (`!x y:real. (!a. y<a ==> x<a) ==> x <= y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  ONCE_REWRITE_TAC[REAL_LT_BETWEEN] THEN REWRITE_TAC[NOT_EXISTS_THM;
  DE_MORGAN_THM] THEN X_GEN_TAC `z:real` THEN
  POP_ASSUM (MP_TAC o SPEC `z:real`) THEN REAL_ARITH_TAC)) THEN
  X_GEN_TAC `a:real` THEN
  DISCH_TAC THEN SUBGOAL_THEN
   `?r. norm (z:complex) < r /\ inv r < a /\ r < &1` MP_TAC THENL
  [SUBGOAL_THEN `max (inv a) (norm(z:complex)) < &1` MP_TAC THENL
  [ASM_SIMP_TAC[REAL_MAX_LT; REAL_INV_LT_1];
  GEN_REWRITE_TAC LAND_CONV [REAL_LT_BETWEEN] THEN
  DISCH_THEN (X_CHOOSE_TAC `r:real`) THEN EXISTS_TAC `r:real` THEN
  POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[REAL_MAX_LT] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_LINV THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
  [ASM_MESON_TAC[REAL_LET_TRANS; NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `inv (r:real) = &1/r` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_MUL_RINV_UNIQ THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `?w. norm w = r /\ (!z. norm z < r
                    ==> norm((h:complex->complex) z) <= norm(h w))`
                  STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC(prove (`!f r. &0 < r /\ f holomorphic_on ball(Cx(&0),r) /\
         f continuous_on cball(Cx(&0),r)
         ==> (?w. norm w = r /\ (!z. norm z < r ==> norm(f z) <= norm(f w)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL[`f:complex->complex`; `ball(Cx(&0),r)`] LEMMA1) THEN
  ASM_REWRITE_TAC[OPEN_BALL; CONNECTED_BALL; BOUNDED_BALL; BALL_EQ_EMPTY;
                  REAL_ARITH `!r:real. ~(r <= &0) <=> &0 < r`] THEN
  ASM_SIMP_TAC[CLOSURE_BALL] THEN STRIP_TAC THEN EXISTS_TAC `w:complex` THEN
  CONJ_TAC THENL
  [UNDISCH_TAC `w:complex IN frontier(ball(Cx(&0),r))` THEN
  ASM_SIMP_TAC[FRONTIER_BALL;dist;COMPLEX_SUB_LZERO;NORM_NEG] THEN SET_TAC[];
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[IN_CBALL;dist;COMPLEX_SUB_LZERO;NORM_NEG] THEN
  MESON_TAC [REAL_LT_IMP_LE]])) THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET
  THEN EXISTS_TAC `ball(Cx(&0),&1)` THEN
  ASM_SIMP_TAC [SUBSET_BALL;REAL_LT_IMP_LE];
  MATCH_MP_TAC HOLOMORPHIC_ON_IMP_CONTINUOUS_ON THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN EXISTS_TAC `ball(Cx(&0),&1)` THEN
  ASM_REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN
  ASM_MESON_TAC[REAL_LET_TRANS]]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `norm(h(w:complex):complex)` THEN CONJ_TAC THENL
  [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `h w:complex = f w / w` SUBST1_TAC THENL
  [ASM_SIMP_TAC[] THEN
  MP_TAC (MESON [GSYM COMPLEX_NORM_ZERO;REAL_NOT_EQ;
                    ASSUME `norm(w:complex) =r`;
                    ASSUME `&0 < r`] `~(w=Cx(&0))`) THEN
  CONV_TAC(COMPLEX_FIELD);
  ASM_REWRITE_TAC[COMPLEX_NORM_DIV] THEN MATCH_MP_TAC REAL_LT_TRANS THEN
  EXISTS_TAC `&1/(r:real)` THEN ASM_SIMP_TAC [REAL_LT_DIV2_EQ] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv (r:real)` THEN
  ASM_REWRITE_TAC[REAL_LE_REFL]]; ALL_TAC] THEN
  CONJ_TAC THENL
  [GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THENL
  [ASM_SIMP_TAC[COMPLEX_MUL_LZERO;REAL_LE_REFL];
  SUBST1_TAC (REAL_ARITH `norm (z:complex) = norm z * &1`) THEN
  ASM_SIMP_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[NORM_POS_LE]]; ALL_TAC] THEN CONJ_TAC THENL
  [ASM_MESON_TAC [COMPLEX_NORM_ZERO;REAL_LT_01]; ALL_TAC] THEN
  REWRITE_TAC[TAUT `((p \/ q) ==> r) <=> ((p ==> r) /\ (q ==> r))`] THEN
  CONJ_TAC THENL [STRIP_TAC THEN SUBGOAL_THEN
   `norm ((h:complex->complex) z) = &1` ASSUME_TAC THENL
  [SUBGOAL_THEN `(h:complex->complex) z = f z/z` SUBST1_TAC THENL
  [UNDISCH_THEN `!z:complex. norm z < &1  ==> f z = z * h z`
  (MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(z = Cx(&0))` THEN CONV_TAC(COMPLEX_FIELD);
  ASM_SIMP_TAC[COMPLEX_NORM_ZERO;REAL_DIV_REFL;COMPLEX_NORM_DIV]];
  SUBGOAL_THEN `?c. (!z. norm z < &1 ==> (h:complex->complex) z = c)`
  STRIP_ASSUME_TAC THENL [MATCH_MP_TAC LEMMA2
  THEN EXISTS_TAC `z:complex` THEN EXISTS_TAC `&1 - norm(z:complex)`
  THEN ASM_REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
  [ASM_MESON_TAC[REAL_SUB_LT]; CONJ_TAC THENL
  [REWRITE_TAC[SUBSET;IN_BALL] THEN GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `dist(Cx(&0), z) + dist(z,x)` THEN
  REWRITE_TAC[DIST_TRIANGLE] THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[dist;COMPLEX_SUB_LZERO;NORM_NEG] THEN REAL_ARITH_TAC;
  GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `norm(z:complex) + norm(z' - z)` THEN
  REWRITE_TAC[NORM_TRIANGLE_SUB] THEN REWRITE_TAC[NORM_SUB] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[NORM_SUB] THEN REAL_ARITH_TAC]];
  EXISTS_TAC `c:complex` THEN CONJ_TAC THENL
  [ASM_SIMP_TAC[COMPLEX_MUL_SYM];
  POP_ASSUM (MP_TAC o SPEC `z:complex`) THEN ASM_MESON_TAC[]]]];
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?c. (!z. norm z < &1 ==> (h:complex->complex) z = c)`
  STRIP_ASSUME_TAC THENL[MATCH_MP_TAC LEMMA2 THEN EXISTS_TAC `Cx(&0)`
  THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_ARITH `&0 < &1`;
  SUBSET_REFL; COMPLEX_SUB_LZERO; NORM_NEG];
  EXISTS_TAC `c:complex` THEN CONJ_TAC THENL
  [ASM_SIMP_TAC[COMPLEX_MUL_SYM];POP_ASSUM (MP_TAC o SPEC `Cx(&0)`) THEN
  ASM_MESON_TAC[COMPLEX_NORM_0; REAL_LT_01]]]]);;
