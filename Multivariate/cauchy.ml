(* ========================================================================= *)
(* Complex path integrals and Cauchy's theorem.                              *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(* (c) Copyright, Gianni Ciolli, Graziano Gentili, Marco Maggesi 2008-2009.  *)
(*              (c) Copyright, Valentina Bruno 2010                          *)
(* ========================================================================= *)

needs "Library/binomial.ml";;
needs "Library/iter.ml";;
needs "Multivariate/polytope.ml";;
needs "Multivariate/realanalysis.ml";;

prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* A couple of extra tactics used in some proofs below.                      *)
(* ------------------------------------------------------------------------- *)

let ASSERT_TAC tm =
  SUBGOAL_THEN tm STRIP_ASSUME_TAC;;

let EQ_TRANS_TAC tm =
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC tm THEN CONJ_TAC;;

(* ------------------------------------------------------------------------- *)
(* Piecewise differentiability on a 1-D interval. The definition doesn't     *)
(* tie it to real^1 but it's not obviously that useful elsewhere.            *)
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
 (`!f:real^M->real^N s.
        f piecewise_differentiable_on s
        ==> (\x. --(f x)) piecewise_differentiable_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[piecewise_differentiable_on] THEN
  MATCH_MP_TAC MONO_AND THEN SIMP_TAC[CONTINUOUS_ON_NEG] THEN
  MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[DIFFERENTIABLE_NEG]);;

let PIECEWISE_DIFFERENTIABLE_ADD = prove
 (`!f g:real^M->real^N s.
        f piecewise_differentiable_on s /\
        g piecewise_differentiable_on s
        ==> (\x. f x + g x) piecewise_differentiable_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[piecewise_differentiable_on] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_ADD] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `t:real^M->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t UNION u :real^M->bool` THEN
  ASM_SIMP_TAC[FINITE_UNION; DIFFERENTIABLE_ADD; IN_INTER;
               SET_RULE `s DIFF (t UNION u) = (s DIFF t) INTER (s DIFF u)`]);;

let PIECEWISE_DIFFERENTIABLE_SUB = prove
 (`!f g:real^M->real^N s.
        f piecewise_differentiable_on s /\
        g piecewise_differentiable_on s
        ==> (\x. f x - g x) piecewise_differentiable_on s`,
  SIMP_TAC[VECTOR_SUB; PIECEWISE_DIFFERENTIABLE_ADD;
           PIECEWISE_DIFFERENTIABLE_NEG]);;

(* ------------------------------------------------------------------------- *)
(* Valid paths, and their start and finish.                                  *)
(* ------------------------------------------------------------------------- *)

let valid_path = new_definition
 `valid_path (f:real^1->complex) <=>
     f piecewise_differentiable_on interval[vec 0,vec 1]`;;

let closed_path = new_definition
 `closed_path g <=> pathstart g = pathfinish g`;;

let VALID_PATH_COMPOSE = prove
 (`!f g. valid_path g /\ f differentiable_on (path_image g)
         ==> valid_path (f o g)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[valid_path; piecewise_differentiable_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `s:real^1->bool` STRIP_ASSUME_TAC)) THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_COMPOSE; DIFFERENTIABLE_IMP_CONTINUOUS_ON] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    ASM_MESON_TAC[DIFFERENTIABLE_IMP_CONTINUOUS_ON; path_image];
    EXISTS_TAC `{vec 0:real^1,vec 1} UNION s` THEN
    ASM_REWRITE_TAC[FINITE_UNION; FINITE_INSERT; FINITE_EMPTY] THEN
    REWRITE_TAC[SET_RULE `s DIFF (t UNION u) = (s DIFF t) DIFF u`] THEN
    REWRITE_TAC[GSYM OPEN_CLOSED_INTERVAL_1] THEN
    X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `((f:complex->complex) o (g:real^1->complex))
      differentiable (at t within (interval(vec 0,vec 1) DIFF s))`
    MP_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_CHAIN_WITHIN THEN CONJ_TAC THENL
       [MATCH_MP_TAC DIFFERENTIABLE_AT_WITHIN THEN
        FIRST_X_ASSUM MATCH_MP_TAC;
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [differentiable_on]) THEN
        DISCH_THEN(MP_TAC o SPEC `(g:real^1->complex) t`) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[path_image; IN_IMAGE] THEN EXISTS_TAC `t:real^1`;
          MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT]
            DIFFERENTIABLE_WITHIN_SUBSET) THEN
          REWRITE_TAC[path_image] THEN MATCH_MP_TAC IMAGE_SUBSET]] THEN
      MP_TAC(ISPECL [`vec 0:real^1`; `vec 1:real^1`]
        INTERVAL_OPEN_SUBSET_CLOSED) THEN ASM SET_TAC[];
      ASM_SIMP_TAC[DIFFERENTIABLE_WITHIN_OPEN; OPEN_DIFF; OPEN_INTERVAL;
                   FINITE_IMP_CLOSED]]]);;

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
(* Theorems about rectifiable valid paths.                                   *)
(* ------------------------------------------------------------------------- *)

let RECTIFIABLE_VALID_PATH = prove
 (`!g. valid_path g
       ==> (rectifiable_path g <=>
              (\t. vector_derivative g (at t)) absolutely_integrable_on
              interval [vec 0,vec 1])`,
  REWRITE_TAC[valid_path; piecewise_differentiable_on; GSYM path] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RECTIFIABLE_PATH_DIFFERENTIABLE THEN
  ASM_MESON_TAC[FINITE_IMP_COUNTABLE]);;

let PATH_LENGTH_VALID_PATH = prove
 (`!g. valid_path g /\ rectifiable_path g
       ==> path_length g =
                 drop(integral (interval[vec 0,vec 1])
                               (\t. lift(norm(vector_derivative g (at t)))))`,
  REWRITE_TAC[valid_path; piecewise_differentiable_on; GSYM path] THEN

  REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_LENGTH_DIFFERENTIABLE THEN
  ASM_MESON_TAC[FINITE_IMP_COUNTABLE]);;

(* ------------------------------------------------------------------------- *)
(* Negligibility of valid_path image                                         *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_VALID_PATH_IMAGE = prove
 (`!g. valid_path g ==> negligible(path_image g)`,
  REWRITE_TAC[piecewise_differentiable_on; piecewise_differentiable_on;
              valid_path; path_image] THEN
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^1->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `IMAGE (g:real^1->real^2)
                    (k UNION (interval [vec 0,vec 1] DIFF k))` THEN
  CONJ_TAC THENL [REWRITE_TAC[IMAGE_UNION]; SET_TAC[]] THEN
  ASM_SIMP_TAC[NEGLIGIBLE_UNION_EQ; NEGLIGIBLE_FINITE; FINITE_IMAGE] THEN
  MATCH_MP_TAC NEGLIGIBLE_DIFFERENTIABLE_IMAGE_LOWDIM THEN
  REWRITE_TAC[DIMINDEX_1; DIMINDEX_2; ARITH] THEN
  ASM_SIMP_TAC[DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON]);;

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

let PATH_INTEGRABLE_REVERSEPATH = prove
 (`!f g. valid_path g /\ f path_integrable_on g
         ==> f path_integrable_on (reversepath g)`,
  REWRITE_TAC[path_integrable_on] THEN
  MESON_TAC[HAS_PATH_INTEGRAL_REVERSEPATH]);;

let PATH_INTEGRABLE_REVERSEPATH_EQ = prove
 (`!f g. valid_path g
         ==> (f path_integrable_on (reversepath g) <=>
              f path_integrable_on g)`,
  MESON_TAC[PATH_INTEGRABLE_REVERSEPATH; VALID_PATH_REVERSEPATH;
            REVERSEPATH_REVERSEPATH]);;

let PATH_INTEGRAL_REVERSEPATH = prove
 (`!f g. valid_path g /\ f path_integrable_on g
         ==> path_integral (reversepath g) f = --(path_integral g f)`,
  MESON_TAC[PATH_INTEGRAL_UNIQUE; HAS_PATH_INTEGRAL_REVERSEPATH;
            HAS_PATH_INTEGRAL_INTEGRAL]);;

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

let PATH_INTEGRAL_JOIN = prove
 (`!f g1 g2:real^1->complex.
        valid_path g1 /\ valid_path g2 /\
        f path_integrable_on g1 /\ f path_integrable_on g2
        ==> path_integral (g1 ++ g2) f =
            path_integral g1 f + path_integral g2 f`,
  MESON_TAC[PATH_INTEGRAL_UNIQUE; HAS_PATH_INTEGRAL_INTEGRAL;
            HAS_PATH_INTEGRAL_JOIN]);;

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
 (`!a b x. x IN interval[vec 0,vec 1]
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

let HAS_PATH_INTEGRAL_TRIVIAL = prove
 (`!f a. (f has_path_integral (Cx(&0))) (linepath(a,a))`,
  REWRITE_TAC[HAS_PATH_INTEGRAL_LINEPATH; COMPLEX_SUB_REFL;
              COMPLEX_MUL_RZERO] THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0; HAS_INTEGRAL_0]);;

let PATH_INTEGRAL_TRIVIAL = prove
 (`!f a. path_integral (linepath(a,a)) f = Cx(&0)`,
  MESON_TAC[HAS_PATH_INTEGRAL_TRIVIAL; PATH_INTEGRAL_UNIQUE]);;

(* ------------------------------------------------------------------------- *)
(* Relation to subpath construction.                                         *)
(* ------------------------------------------------------------------------- *)

let VALID_PATH_SUBPATH = prove
 (`!g u v. valid_path g /\
           u IN interval[vec 0,vec 1] /\ v IN interval[vec 0,vec 1]
           ==> valid_path(subpath u v g)`,
  SIMP_TAC[valid_path; PATH_SUBPATH] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[subpath] THEN
  ASM_CASES_TAC `v:real^1 = u` THENL
   [MATCH_MP_TAC DIFFERENTIABLE_ON_IMP_PIECEWISE_DIFFERENTIABLE THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL; VECTOR_MUL_LZERO; DROP_VEC] THEN
    REWRITE_TAC[DIFFERENTIABLE_ON_CONST];
    MATCH_MP_TAC(REWRITE_RULE[o_DEF] PIECEWISE_DIFFERENTIABLE_COMPOSE) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_ON_IMP_PIECEWISE_DIFFERENTIABLE THEN
      MATCH_MP_TAC DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_ADD THEN
      REWRITE_TAC[DIFFERENTIABLE_CONST] THEN
      MATCH_MP_TAC DIFFERENTIABLE_CMUL THEN REWRITE_TAC[DIFFERENTIABLE_ID];
      MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_SUBSET THEN
      EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[VECTOR_ADD_SYM] THEN
      REWRITE_TAC[IMAGE_AFFINITY_INTERVAL] THEN
      REPEAT(COND_CASES_TAC THEN REWRITE_TAC[EMPTY_SUBSET]) THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1])) THEN
      SIMP_TAC[SUBSET_INTERVAL_1; DROP_ADD; DROP_CMUL; DROP_SUB; DROP_VEC] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; DROP_ADD; DROP_SUB] THEN
      ASM_SIMP_TAC[DROP_EQ; REAL_FIELD `~(u:real = v) ==>
        (u + (v - u) * x = b <=> x = (b - u) / (v - u))`] THEN
      X_GEN_TAC `b:real^1` THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{lift((drop b - drop u) / (drop v - drop u))}` THEN
      REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; SUBSET; IN_ELIM_THM] THEN
      SIMP_TAC[GSYM LIFT_EQ; LIFT_DROP; IN_SING]]]);;

let HAS_PATH_INTEGRAL_SUBPATH_REFL = prove
 (`!f g u. (f has_path_integral (Cx(&0))) (subpath u u g)`,
  REWRITE_TAC[HAS_PATH_INTEGRAL; subpath; VECTOR_SUB_REFL] THEN
  REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO; VECTOR_DERIVATIVE_CONST_AT] THEN
  REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_RZERO] THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0; HAS_INTEGRAL_0]);;

let PATH_INTEGRABLE_SUBPATH_REFL = prove
 (`!f g u. f path_integrable_on (subpath u u g)`,
  REWRITE_TAC[path_integrable_on] THEN
  MESON_TAC[HAS_PATH_INTEGRAL_SUBPATH_REFL]);;

let PATH_INTEGRAL_SUBPATH_REFL = prove
 (`!f g u. path_integral (subpath u u g) f = Cx(&0)`,
  MESON_TAC[PATH_INTEGRAL_UNIQUE; HAS_PATH_INTEGRAL_SUBPATH_REFL]);;

let HAS_PATH_INTEGRAL_SUBPATH = prove
 (`!f g u v.
        valid_path g /\ f path_integrable_on g /\
        u IN interval[vec 0,vec 1] /\ v IN interval[vec 0,vec 1] /\
        drop u <= drop v
        ==> (f has_path_integral
             integral (interval[u,v])
                      (\x. f(g x) * vector_derivative g (at x)))
            (subpath u v g)`,
  REWRITE_TAC[path_integrable_on; HAS_PATH_INTEGRAL; subpath] THEN
  REWRITE_TAC[GSYM integrable_on] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `v:real^1 = u` THENL
   [ASM_REWRITE_TAC[INTEGRAL_REFL; VECTOR_SUB_REFL; DROP_VEC] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_DERIVATIVE_CONST_AT] THEN
    REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_RZERO] THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0; HAS_INTEGRAL_0];
    SUBGOAL_THEN `drop u < drop v` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_LE; DROP_EQ]; ALL_TAC]] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^1`; `v:real^1`] o
   MATCH_MP(REWRITE_RULE[IMP_CONJ] INTEGRABLE_ON_SUBINTERVAL)) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[SUBSET_INTERVAL_1; IN_INTERVAL_1; REAL_LT_IMP_LE];
    REWRITE_TAC[HAS_INTEGRAL_INTEGRAL]] THEN
  DISCH_THEN(MP_TAC o SPECL [`drop(v - u)`; `u:real^1`] o
   MATCH_MP(REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_AFFINITY)) THEN
  ASM_SIMP_TAC[DROP_SUB; REAL_ARITH `u < v ==> ~(v - u = &0)`] THEN
  REWRITE_TAC[IMAGE_AFFINITY_INTERVAL; INTERVAL_EQ_EMPTY_1; DROP_SUB] THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_ARITH `u < v ==> ~(v < u) /\ &0 <= v - u`;
               VECTOR_ARITH `a % u + --(a % v):real^N = a % (u - v)`] THEN
  REWRITE_TAC[VECTOR_SUB_REFL; VECTOR_MUL_RZERO] THEN
  SUBGOAL_THEN `inv(drop v - drop u) % (v - u) = vec 1` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM DROP_EQ; DROP_VEC; DROP_CMUL; DROP_SUB] THEN
    UNDISCH_TAC `drop u < drop v` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `drop(v - u)` o MATCH_MP HAS_INTEGRAL_CMUL) THEN
  ASM_SIMP_TAC[real_abs; REAL_LT_IMP_LE; REAL_SUB_LE] THEN
  REWRITE_TAC[DIMINDEX_1; REAL_POW_1; VECTOR_MUL_ASSOC; DROP_SUB] THEN
  ASM_SIMP_TAC[REAL_FIELD `u < v ==> (v - u) * inv(v - u) = &1`] THEN
  REWRITE_TAC[VECTOR_MUL_LID] THEN
  MATCH_MP_TAC(REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
    HAS_INTEGRAL_SPIKE_FINITE) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [valid_path]) THEN
  REWRITE_TAC[piecewise_differentiable_on; IN_DIFF] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^1->bool` STRIP_ASSUME_TAC o CONJUNCT2) THEN
  EXISTS_TAC `{t | ((drop v - drop u) % t + u) IN k}` THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ THEN
    ASM_REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; DROP_SUB; DROP_ADD] THEN
    UNDISCH_TAC `drop u < drop v` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
  X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN REWRITE_TAC[COMPLEX_CMUL] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING `a * b * c:complex = b * a * c`] THEN
  REWRITE_TAC[VECTOR_ARITH `x + a % y:real^N = a % y + x`] THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM COMPLEX_CMUL; GSYM DROP_SUB] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_UNIQUE_AT THEN
  MATCH_MP_TAC(REWRITE_RULE[o_DEF] VECTOR_DIFF_CHAIN_AT) THEN
  REWRITE_TAC[DROP_SUB] THEN CONJ_TAC THENL
   [SUBST1_TAC(VECTOR_ARITH `v - u:real^1 = (v - u) + vec 0`) THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN
    REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN
    SUBST1_TAC(MESON[LIFT_DROP; LIFT_EQ_CMUL]
     `v - u = drop(v - u) % vec 1`) THEN REWRITE_TAC[GSYM DROP_SUB] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN
    REWRITE_TAC[HAS_VECTOR_DERIVATIVE_ID];
    REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTERVAL_1] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1])) THEN
    REWRITE_TAC[DROP_ADD; DROP_SUB; DROP_CMUL; DROP_VEC] THEN
    REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
      TRY(MATCH_MP_TAC REAL_LE_MUL) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(drop v - drop u) * &1 + drop u` THEN
      ASM_SIMP_TAC[REAL_LE_RADD; REAL_LE_LMUL;
                   REAL_SUB_LE; REAL_LT_IMP_LE] THEN
      ASM_REAL_ARITH_TAC]]);;

let PATH_INTEGRABLE_SUBPATH = prove
 (`!f g u v.
        valid_path g /\ f path_integrable_on g /\
        u IN interval[vec 0,vec 1] /\ v IN interval[vec 0,vec 1]
        ==> f path_integrable_on (subpath u v g)`,
  REPEAT STRIP_TAC THEN DISJ_CASES_TAC(REAL_ARITH
   `drop u <= drop v \/ drop v <= drop u`)
  THENL
   [ASM_MESON_TAC[path_integrable_on; HAS_PATH_INTEGRAL_SUBPATH];
    ONCE_REWRITE_TAC[GSYM REVERSEPATH_SUBPATH] THEN
    MATCH_MP_TAC PATH_INTEGRABLE_REVERSEPATH THEN
    ASM_SIMP_TAC[VALID_PATH_SUBPATH] THEN
    ASM_MESON_TAC[path_integrable_on; HAS_PATH_INTEGRAL_SUBPATH]]);;

let HAS_INTEGRAL_PATH_INTEGRAL_SUBPATH = prove
 (`!f g u v.
        valid_path g /\ f path_integrable_on g /\
        u IN interval[vec 0,vec 1] /\ v IN interval[vec 0,vec 1] /\
        drop u <= drop v
        ==> (((\x. f(g x) * vector_derivative g (at x))) has_integral
             path_integral (subpath u v g) f)
            (interval[u,v])`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[HAS_INTEGRAL_INTEGRABLE_INTEGRAL] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
    ASM_REWRITE_TAC[GSYM PATH_INTEGRABLE_ON; SUBSET_INTERVAL_1] THEN
    ASM_MESON_TAC[IN_INTERVAL_1];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
    ASM_SIMP_TAC[HAS_PATH_INTEGRAL_SUBPATH]]);;

let PATH_INTEGRAL_SUBPATH_INTEGRAL = prove
 (`!f g u v.
        valid_path g /\ f path_integrable_on g /\
        u IN interval[vec 0,vec 1] /\ v IN interval[vec 0,vec 1] /\
        drop u <= drop v
        ==> path_integral (subpath u v g) f =
            integral (interval[u,v])
                     (\x. f(g x) * vector_derivative g (at x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
  ASM_SIMP_TAC[HAS_PATH_INTEGRAL_SUBPATH]);;

let PATH_INTEGRAL_SUBPATH_COMBINE = prove
 (`!f g u v w.
        valid_path g /\ f path_integrable_on g /\
        u IN interval[vec 0,vec 1] /\
        v IN interval[vec 0,vec 1] /\
        w IN interval[vec 0,vec 1]
        ==> path_integral (subpath u v g) f + path_integral (subpath v w g) f =
            path_integral (subpath u w g) f`,
  REPLICATE_TAC 3 GEN_TAC THEN
  SUBGOAL_THEN
   `!u v w.
        drop u <= drop v /\ drop v <= drop w
        ==> valid_path g /\ f path_integrable_on g /\
            u IN interval[vec 0,vec 1] /\
            v IN interval[vec 0,vec 1] /\
            w IN interval[vec 0,vec 1]
            ==> path_integral (subpath u v g) f +
                path_integral (subpath v w g) f =
                path_integral (subpath u w g) f`
  ASSUME_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (REAL_ARITH `drop u <= drop v /\ drop v <= drop w \/
                  drop u <= drop w /\ drop w <= drop v \/
                  drop v <= drop u /\ drop u <= drop w \/
                  drop v <= drop w /\ drop w <= drop u \/
                  drop w <= drop u /\ drop u <= drop v \/
                  drop w <= drop v /\ drop v <= drop u`) THEN
    FIRST_ASSUM(ANTE_RES_THEN MP_TAC) THEN ASM_REWRITE_TAC[] THEN
    REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC (MESON[REVERSEPATH_SUBPATH]
     `subpath v u (g:real^1->complex) = reversepath(subpath u v g) /\
      subpath w u g = reversepath(subpath u w g) /\
      subpath w v g = reversepath(subpath v w g)`) THEN
    ASM_SIMP_TAC[PATH_INTEGRAL_REVERSEPATH; PATH_INTEGRABLE_SUBPATH;
                 VALID_PATH_REVERSEPATH; VALID_PATH_SUBPATH] THEN
    CONV_TAC COMPLEX_RING] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `drop u <= drop w` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_SIMP_TAC[PATH_INTEGRAL_SUBPATH_INTEGRAL] THEN
  MATCH_MP_TAC INTEGRAL_COMBINE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
  EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
  ASM_REWRITE_TAC[GSYM PATH_INTEGRABLE_ON; SUBSET_INTERVAL_1] THEN
  ASM_MESON_TAC[IN_INTERVAL_1]);;

let PATH_INTEGRAL_INTEGRAL = prove
 (`!f g. path_integral g f =
         integral (interval [vec 0,vec 1])
                  (\x. f (g x) * vector_derivative g (at x))`,
  REWRITE_TAC[path_integral; integral; HAS_PATH_INTEGRAL]);;

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
  ASM_SIMP_TAC[FINITE_IMP_COUNTABLE; GSYM o_DEF] THEN CONJ_TAC THENL
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

let HAS_PATH_INTEGRAL_IS_0 = prove
 (`!f g. (!z. z IN path_image g ==> f(z) = Cx(&0))
         ==> (f has_path_integral Cx(&0)) g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_PATH_INTEGRAL_EQ THEN
  EXISTS_TAC `\z:complex. Cx(&0)` THEN
  ASM_REWRITE_TAC[HAS_PATH_INTEGRAL_0] THEN ASM_MESON_TAC[]);;

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
 (`!f g p.
        (!x. x IN path_image p ==> f x = g x)
        ==> path_integral p f = path_integral p g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[path_integral] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  ASM_MESON_TAC[HAS_PATH_INTEGRAL_EQ]);;

let PATH_INTEGRAL_EQ_0 = prove
 (`!f g. (!z. z IN path_image g ==> f(z) = Cx(&0))
         ==> path_integral g f = Cx(&0)`,
  MESON_TAC[HAS_PATH_INTEGRAL_IS_0; PATH_INTEGRAL_UNIQUE]);;

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

let PATH_INTEGRABLE_EQ = prove
 (`!f g p. (!x. x IN path_image p ==> f x = g x) /\ f path_integrable_on p
           ==> g path_integrable_on p`,
  REWRITE_TAC[path_integrable_on] THEN MESON_TAC[HAS_PATH_INTEGRAL_EQ]);;

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

let HAS_PATH_INTEGRAL_REVERSE_LINEPATH = prove
 (`!f a b i.
        (f has_path_integral i) (linepath(a,b))
        ==> (f has_path_integral (--i)) (linepath(b,a))`,
  MESON_TAC[REVERSEPATH_LINEPATH; VALID_PATH_LINEPATH;
            HAS_PATH_INTEGRAL_REVERSEPATH]);;

let PATH_INTEGRAL_REVERSE_LINEPATH = prove
 (`!f a b.
        f continuous_on (segment[a,b])
        ==> path_integral(linepath(a,b)) f =
            --(path_integral(linepath(b,a)) f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_REVERSE_LINEPATH THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_INTEGRAL THEN
  MATCH_MP_TAC PATH_INTEGRABLE_CONTINUOUS_LINEPATH THEN
  ASM_MESON_TAC[SEGMENT_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Splitting a path integral in a flat way.                                  *)
(* ------------------------------------------------------------------------- *)

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

let PATH_INTEGRAL_SPLIT_LINEPATH = prove
 (`!f a b c.
        f continuous_on segment[a,b] /\ c IN segment[a,b]
        ==> path_integral(linepath (a,b)) f =
            path_integral(linepath (a,c)) f +
            path_integral(linepath (c,b)) f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_INTEGRAL_SPLIT THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  VECTOR_ARITH_TAC);;

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
(* Reversing the order in a double path integral. The condition is           *)
(* stronger than needed but it's often true in typical situations.           *)
(* ------------------------------------------------------------------------- *)

let PATH_INTEGRAL_SWAP = prove
 (`!f g h.
    (\y. f (fstcart y) (sndcart y)) continuous_on
      { pastecart w z | w IN path_image g /\ z IN path_image h} /\
    valid_path g /\ valid_path h /\
    (\t. vector_derivative g (at t)) continuous_on interval[vec 0,vec 1] /\
    (\t. vector_derivative h (at t)) continuous_on interval[vec 0,vec 1]
    ==> path_integral g (\w. path_integral h (f w)) =
        path_integral h (\z. path_integral g (\w. f w z))`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[PATH_INTEGRAL_INTEGRAL] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `integral (interval[vec 0,vec 1])
             (\x. path_integral h
                    (\y. f (g x) y * vector_derivative g (at x)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `x:real^1` THEN
    DISCH_TAC THEN REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC PATH_INTEGRAL_COMPLEX_RMUL THEN
    REWRITE_TAC[PATH_INTEGRABLE_ON] THEN
    MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(\t:real^1. (f:complex->complex->complex) (g x) (h t)) =
      (\y. f (fstcart y) (sndcart y)) o
      (\t. pastecart (g(x:real^1)) (h t))`
    SUBST1_TAC THENL
     [REWRITE_TAC[o_DEF; FSTCART_PASTECART; SNDCART_PASTECART];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_CONST; GSYM path; VALID_PATH_IMP_PATH];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
         CONTINUOUS_ON_SUBSET)) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_PASTECART_THM] THEN
      ASM_SIMP_TAC[path_image; FUN_IN_IMAGE]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `integral (interval[vec 0,vec 1])
             (\y. path_integral g
                    (\x. f x (h y) * vector_derivative h (at y)))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `y:real^1` THEN
    DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PATH_INTEGRAL_COMPLEX_RMUL THEN
    REWRITE_TAC[PATH_INTEGRABLE_ON] THEN
    MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(\t:real^1. (f:complex->complex->complex) (g t) (h y)) =
      (\z. f (fstcart z) (sndcart z)) o
      (\t. pastecart (g t) (h(y:real^1)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[o_DEF; FSTCART_PASTECART; SNDCART_PASTECART];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_CONST; GSYM path; VALID_PATH_IMP_PATH];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
         CONTINUOUS_ON_SUBSET)) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_PASTECART_THM] THEN
      ASM_SIMP_TAC[path_image; FUN_IN_IMAGE]]] THEN
  REWRITE_TAC[PATH_INTEGRAL_INTEGRAL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand)
     INTEGRAL_SWAP_CONTINUOUS o lhs o snd) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
    REPEAT(MATCH_MP_TAC INTEGRAL_EQ THEN
           REWRITE_TAC[] THEN REPEAT STRIP_TAC) THEN
    REWRITE_TAC[COMPLEX_MUL_AC]] THEN
  REPEAT(MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC) THENL
   [ALL_TAC;
    SUBGOAL_THEN
     `(\z:real^(1,1)finite_sum. vector_derivative g (at (fstcart z))) =
      (\t. vector_derivative (g:real^1->complex) (at t)) o fstcart`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_PASTECART_THM;
             FORALL_PASTECART; GSYM PASTECART_INTERVAL; FSTCART_PASTECART];
    SUBGOAL_THEN
     `(\z:real^(1,1)finite_sum. vector_derivative h (at (sndcart z))) =
      (\t. vector_derivative (h:real^1->complex) (at t)) o sndcart`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_PASTECART_THM;
          FORALL_PASTECART; GSYM PASTECART_INTERVAL; SNDCART_PASTECART]] THEN
  SUBGOAL_THEN
   `(\z. f (g (fstcart z)) (h (sndcart z))) =
    (\y. (f:complex->complex->complex) (fstcart y) (sndcart y)) o
    (\p. pastecart (g(fstcart p:real^1)) (h(sndcart p:real^1)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[o_DEF; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
    CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART] THEN
    REWRITE_TAC[GSYM PASTECART_INTERVAL; GSYM SIMPLE_IMAGE] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART;
                SET_RULE `{f x | x IN {g a b | P a /\ Q b}} =
                          {f(g a b) | P a /\ Q b}`] THEN
    REPEAT(FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[path] o
        MATCH_MP VALID_PATH_IMP_PATH)) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      CONTINUOUS_ON_SUBSET)) THEN
    SIMP_TAC[SUBSET; FORALL_IN_GSPEC];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_PASTECART_THM;
                FORALL_PASTECART; GSYM PASTECART_INTERVAL;
                path_image; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    SIMP_TAC[FUN_IN_IMAGE]]);;

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
    MP_TAC(SPEC `f:complex->complex` PATH_INTEGRAL_REVERSE_LINEPATH) THEN DISCH_THEN
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
 (`!f a b c.
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
    CONJ_TAC THEN MATCH_MP_TAC PATH_INTEGRAL_REVERSE_LINEPATH THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    MP_TAC(SPECL [`f:complex->complex`; `a:complex`; `c:complex`; `b:complex`;
                  `inv k:real`] PATH_INTEGRAL_SPLIT) THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_LE_INV_EQ; REAL_MUL_LINV; REAL_INV_LE_1;
      VECTOR_MUL_LID; REAL_ARITH `~(k <= &1) ==> ~(k = &0) /\ &1 <= k`] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC(COMPLEX_RING
     `ac = --ca ==> ac = ab + bc ==> ab + bc + ca = Cx(&0)`) THEN
    MATCH_MP_TAC PATH_INTEGRAL_REVERSE_LINEPATH THEN
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
  REPEAT CONJ_TAC THEN MATCH_MP_TAC PATH_INTEGRAL_REVERSE_LINEPATH THEN
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
               PATH_INTEGRAL_REVERSE_LINEPATH)) THEN
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

let TRIANGLE_PATH_INTEGRALS_STARLIKE_PRIMITIVE = prove
 (`!f s a.
      a IN s /\ open s /\ f continuous_on s /\
      (!z. z IN s ==> segment[a,z] SUBSET s) /\
      (!b c. segment[b,c] SUBSET s
             ==> path_integral (linepath(a,b)) f +
                 path_integral (linepath(b,c)) f +
                 path_integral (linepath(c,a)) f = Cx(&0))
      ==> ?g. !z. z IN s ==> (g has_complex_derivative f(z)) (at z)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\x. path_integral (linepath(a,x)) f` THEN
  X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
  REWRITE_TAC[has_complex_derivative] THEN
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
    MP_TAC(SPECL [`f:complex->complex`; `a:complex`; `y:complex`]
         PATH_INTEGRAL_REVERSE_LINEPATH) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `s:complex->bool` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
      ASM_REWRITE_TAC[IN_BALL; ONCE_REWRITE_RULE[NORM_SUB] dist];
      REWRITE_TAC[COMPLEX_VEC_0] THEN MATCH_MP_TAC(COMPLEX_RING
        `ax + xy + ya = Cx(&0) ==> ay = --ya ==> xy + ax - ay = Cx(&0)`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o
       MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] SUBSET_TRANS)) THEN
      REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
      MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_BALL] THEN
      REWRITE_TAC[SUBSET; IN_BALL; IN_INSERT; NOT_IN_EMPTY] THEN
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[dist; NORM_0; VECTOR_SUB_REFL] THEN
      ASM_MESON_TAC[NORM_SUB]];
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
    ASM_MESON_TAC[REAL_LET_TRANS; SEGMENT_BOUND]]);;

let HOLOMORPHIC_STARLIKE_PRIMITIVE = prove
 (`!f s k. open s /\ starlike s /\ FINITE k /\ f continuous_on s /\
           (!x. x IN s DIFF k ==> f complex_differentiable at x)
           ==> ?g. !x. x IN s ==> (g has_complex_derivative f(x)) (at x)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a:complex` STRIP_ASSUME_TAC o
        GEN_REWRITE_RULE I [starlike]) THEN
  MATCH_MP_TAC TRIANGLE_PATH_INTEGRALS_STARLIKE_PRIMITIVE THEN
  EXISTS_TAC `a:complex` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:complex`; `y:complex`] THEN STRIP_TAC THEN
  MATCH_MP_TAC HAS_CHAIN_INTEGRAL_CHAIN_INTEGRAL THEN
  MATCH_MP_TAC CAUCHY_THEOREM_TRIANGLE_COFINITE THEN
  EXISTS_TAC `k:complex->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `convex hull {a:complex,x,y} SUBSET s` ASSUME_TAC THENL
   [MATCH_MP_TAC STARLIKE_CONVEX_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[IN_DIFF] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF] THEN
  ASM_MESON_TAC[SUBSET; INTERIOR_SUBSET]);;

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
(* ------------------------------------------------------------------------- *)

let TRIANGLE_PATH_INTEGRALS_CONVEX_PRIMITIVE = prove
 (`!f s a.
      a IN s /\ convex s /\ f continuous_on s /\
      (!b c. b IN s /\ c IN s
             ==> path_integral (linepath(a,b)) f +
                 path_integral (linepath(b,c)) f +
                 path_integral (linepath(c,a)) f = Cx(&0))
      ==> ?g. !z. z IN s ==> (g has_complex_derivative f(z)) (at z within s)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\x. path_integral (linepath(a,x)) f` THEN
  X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
  REWRITE_TAC[has_complex_derivative] THEN
  REWRITE_TAC[has_derivative_within; LINEAR_COMPLEX_MUL] THEN
  MATCH_MP_TAC LIM_TRANSFORM THEN
  EXISTS_TAC `\y. inv(norm(y - x)) % (path_integral(linepath(x,y)) f -
                   f x * (y - x))` THEN
  REWRITE_TAC[VECTOR_ARITH
   `i % (x - a) - i % (y - (z + a)) = i % (x + z - y)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LIM_EVENTUALLY THEN REWRITE_TAC[EVENTUALLY_WITHIN] THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
    X_GEN_TAC `y:complex` THEN STRIP_TAC THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ2_TAC THEN
    MP_TAC(SPECL [`f:complex->complex`; `a:complex`; `y:complex`]
         PATH_INTEGRAL_REVERSE_LINEPATH) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `s:complex->bool` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
      MATCH_MP_TAC HULL_MINIMAL THEN ASM SET_TAC[];
      REWRITE_TAC[COMPLEX_VEC_0] THEN MATCH_MP_TAC(COMPLEX_RING
        `ax + xy + ya = Cx(&0) ==> ay = --ya ==> xy + ax - ay = Cx(&0)`) THEN
      ASM_SIMP_TAC[]];
    REWRITE_TAC[LIM_WITHIN] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(f:complex->complex) continuous (at x within s)` MP_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]; ALL_TAC] THEN
    REWRITE_TAC[continuous_within; dist; VECTOR_SUB_RZERO] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d1:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:complex` THEN STRIP_TAC THEN
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
       `w IN t ==> t SUBSET s ==> w IN s`)) THEN
      REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
      MATCH_MP_TAC HULL_MINIMAL THEN ASM SET_TAC[];
      ASM_MESON_TAC[REAL_LET_TRANS; SEGMENT_BOUND]]]);;

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
  MATCH_MP_TAC TRIANGLE_PATH_INTEGRALS_CONVEX_PRIMITIVE THEN
  EXISTS_TAC `a:complex` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_CHAIN_INTEGRAL_CHAIN_INTEGRAL THEN
  ASM_SIMP_TAC[]);;

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
  MESON_TAC[holomorphic_on; HAS_COMPLEX_DERIVATIVE_WITHIN_OPEN;
            OPEN_INTERIOR]);;

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
(* Key fact that path integral is the same for a "nearby" path. This is the  *)
(* main lemma for the homotopy form of Cauchy's theorem and is also useful   *)
(* if we want "without loss of generality" to assume some niceness of our    *)
(* path (e.g. smoothness). It can also be used to define the integrals of    *)
(* analytic functions over arbitrary continuous paths. This is just done for *)
(* winding numbers now; I'm not sure if it's worth going further with that.  *)
(* ------------------------------------------------------------------------- *)

let PATH_INTEGRAL_NEARBY_ENDS,PATH_INTEGRAL_NEARBY_LOOP = (CONJ_PAIR o prove)
 (`(!s p.
      open s /\ path p /\ path_image p SUBSET s
      ==> ?d. &0 < d /\
              !g h. valid_path g /\ valid_path h /\
                    (!t. t IN interval[vec 0,vec 1]
                         ==> norm(g t - p t) < d /\ norm(h t - p t) < d) /\
                    pathstart h = pathstart g /\ pathfinish h = pathfinish g
                    ==> path_image g SUBSET s /\
                        path_image h SUBSET s /\
                        !f. f holomorphic_on s
                            ==> path_integral h f = path_integral g f) /\
   (!s p.
      open s /\ path p /\ path_image p SUBSET s
      ==> ?d. &0 < d /\
              !g h. valid_path g /\ valid_path h /\
                    (!t. t IN interval[vec 0,vec 1]
                         ==> norm(g t - p t) < d /\ norm(h t - p t) < d) /\
                    pathfinish g = pathstart g /\ pathfinish h = pathstart h
                    ==> path_image g SUBSET s /\
                        path_image h SUBSET s /\
                        !f. f holomorphic_on s
                            ==> path_integral h f = path_integral g f)`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  MAP_EVERY (fun t -> ASM_CASES_TAC t THEN ASM_REWRITE_TAC[])
   [`open(s:complex->bool)`;
    `path(p:real^1->complex)`;
    `path_image(p:real^1->complex) SUBSET s`] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM] THEN
  MATCH_MP_TAC(MESON[] `(?x. P x /\ Q x) ==> (?x. P x) /\ (?x. Q x)`) THEN
  SUBGOAL_THEN
   `!z. z IN path_image p ==> ?e. &0 < e /\ ball(z:complex,e) SUBSET s`
  MP_TAC THENL
   [ASM_MESON_TAC[OPEN_CONTAINS_BALL; SUBSET]; ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [RIGHT_IMP_EXISTS_THM; RIGHT_AND_EXISTS_THM; SKOLEM_THM] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `ee:complex->real` THEN
  DISCH_THEN(LABEL_TAC "*") THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_HEINE_BOREL o
    MATCH_MP COMPACT_PATH_IMAGE) THEN
  DISCH_THEN(MP_TAC o SPEC
   `IMAGE (\z:complex. ball(z,ee z / &3)) (path_image p)`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL; SUBSET] THEN
    X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    REWRITE_TAC[UNIONS_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `z:complex` THEN
    ASM_SIMP_TAC[CENTRE_IN_BALL; REAL_ARITH `&0 < e / &3 <=> &0 < e`];
    ALL_TAC] THEN
  REWRITE_TAC[path_image; GSYM IMAGE_o] THEN REWRITE_TAC[GSYM path_image] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> b /\ a /\ c`] THEN
  REWRITE_TAC[CONJ_ASSOC; FINITE_SUBSET_IMAGE] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; MESON[]
   `(?f s. (P s /\ f = g s) /\ Q f) <=> ?s. P s /\ Q(g s)`] THEN
  REWRITE_TAC[UNIONS_IMAGE; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `k:real^1->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM; o_THM] THEN
  ASM_CASES_TAC `k:real^1->bool = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY; GSYM NOT_EXISTS_THM; MEMBER_NOT_EMPTY] THEN
    REWRITE_TAC[PATH_IMAGE_NONEMPTY];
    DISCH_THEN(LABEL_TAC "+")] THEN
  SUBGOAL_THEN
    `!i:real^1. i IN k ==> &0 < ee((p i):complex)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; path_image; IN_IMAGE]; ALL_TAC] THEN
  ABBREV_TAC `e = inf(IMAGE ((ee:complex->real) o (p:real^1->complex)) k)` THEN
  MP_TAC(ISPEC `IMAGE ((ee:complex->real) o (p:real^1->complex)) k`
    INF_FINITE) THEN
  MP_TAC(ISPECL [`IMAGE ((ee:complex->real) o (p:real^1->complex)) k`; `&0`]
    REAL_LT_INF_FINITE) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
  ASM_REWRITE_TAC[o_THM] THEN DISCH_TAC THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  EXISTS_TAC `e / &3` THEN
  MP_TAC(ISPECL [`p:real^1->complex`; `interval[vec 0:real^1,vec 1]`]
        COMPACT_UNIFORMLY_CONTINUOUS) THEN REWRITE_TAC[COMPACT_INTERVAL] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[path]; ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN
  ASM_REWRITE_TAC[REAL_ARITH `&0 < e / &3 <=> &0 < e`] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; AND_FORALL_THM] THEN
  MAP_EVERY X_GEN_TAC [`g:real^1->complex`; `h:real^1->complex`] THEN
  MAP_EVERY (fun t -> ASM_CASES_TAC t THEN ASM_REWRITE_TAC[])
   [`!t. t IN interval[vec 0,vec 1]
         ==> norm((g:real^1->complex) t - p t) < e / &3 /\
             norm((h:real^1->complex) t - p t) < e / &3`;
    `valid_path(g:real^1->complex)`; `valid_path(h:real^1->complex)`] THEN
  MATCH_MP_TAC(TAUT
   `q /\ (p1 \/ p2 ==> q ==> r) ==> (p1 ==> q /\ r) /\ (p2 ==> q /\ r)`) THEN
  CONJ_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    REMOVE_THEN "+" (MP_TAC o SPEC `(p:real^1->complex) t`) THEN
    ASM_SIMP_TAC[path_image; FUN_IN_IMAGE; IN_BALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^1` STRIP_ASSUME_TAC) THENL
     [SUBGOAL_THEN `(g:real^1->complex) t IN ball(p(u:real^1),ee(p u))`
      MP_TAC THENL [ALL_TAC; ASM_MESON_TAC[path_image; IN_IMAGE; SUBSET]];
      SUBGOAL_THEN `(h:real^1->complex) t IN ball(p(u:real^1),ee(p u))`
      MP_TAC THENL [ALL_TAC; ASM_MESON_TAC[path_image; IN_IMAGE; SUBSET]]] THEN
    REWRITE_TAC[IN_BALL] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NORM_ARITH `dist(gu,gt) < eu / &3
                  ==> norm(ht - gt) < e / &3 /\ e <= eu
                  ==> dist(gu,ht) < eu`)) THEN
    ASM_SIMP_TAC[];
    DISCH_TAC THEN STRIP_TAC THEN
    X_GEN_TAC `f:complex->complex` THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `?ff. !z. z IN path_image p
             ==> &0 < ee z /\ ball(z,ee z) SUBSET s /\
                 !w. w IN ball(z,ee z)
                     ==> (ff z has_complex_derivative f w) (at w)`
  MP_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM;
                RIGHT_EXISTS_AND_THM] THEN
    X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `z:complex`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f:complex->complex`; `ball(z:complex,ee z)`;
                   `{}:complex->bool`] HOLOMORPHIC_CONVEX_PRIMITIVE) THEN
    SIMP_TAC[HAS_COMPLEX_DERIVATIVE_WITHIN_OPEN; OPEN_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[CONVEX_BALL; FINITE_EMPTY] THEN
    SIMP_TAC[DIFF_EMPTY; INTERIOR_OPEN; OPEN_BALL] THEN
    SUBGOAL_THEN `f holomorphic_on ball(z,ee z)` MP_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN EXISTS_TAC `s:complex->bool` THEN
      ASM_REWRITE_TAC[];
      SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON] THEN
      SIMP_TAC[holomorphic_on; HAS_COMPLEX_DERIVATIVE_WITHIN_OPEN; OPEN_BALL;
               complex_differentiable]];
    REMOVE_THEN "*" (K ALL_TAC) THEN
    DISCH_THEN(CHOOSE_THEN (LABEL_TAC "*"))] THEN
  MP_TAC(ISPEC `d:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!n. n <= N
        ==> path_integral(subpath (vec 0) (&n / &N % vec 1) h) f -
            path_integral(subpath (vec 0) (&n / &N % vec 1) g) f =
            path_integral(linepath (g(&n / &N % vec 1),h(&n / &N % vec 1))) f -
            path_integral(linepath (g(vec 0),h(vec 0))) f`
  (MP_TAC o SPEC `N:num`) THENL
   [ALL_TAC;
    ASM_SIMP_TAC[LE_REFL; REAL_DIV_REFL; REAL_OF_NUM_EQ; VECTOR_MUL_LID] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN MP_TAC) THEN
    REWRITE_TAC[pathstart; pathfinish] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[SUBPATH_TRIVIAL; PATH_INTEGRAL_TRIVIAL] THEN
    CONV_TAC COMPLEX_RING] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_LZERO; VECTOR_MUL_LZERO] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN MP_TAC) THEN
    REWRITE_TAC[pathstart; pathfinish] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[PATH_INTEGRAL_TRIVIAL; PATH_INTEGRAL_SUBPATH_REFL] THEN
    REWRITE_TAC[COMPLEX_SUB_REFL];
    DISCH_TAC THEN FIRST_X_ASSUM(K ALL_TAC o check (is_disj o concl))] THEN
  REMOVE_THEN "+" (MP_TAC o SPEC `(p:real^1->complex)(&n / &N % vec 1)`) THEN
  REWRITE_TAC[IN_BALL] THEN ANTS_TAC THENL
   [REWRITE_TAC[path_image] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_CMUL; DROP_VEC; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL
   [`(ff:complex->complex->complex) (p(t:real^1))`; `f:complex->complex`;
    `subpath (&n / &N % vec 1) (&(SUC n) / &N % vec 1) (g:real^1->complex) ++
     linepath(g (&(SUC n) / &N % vec 1),h(&(SUC n) / &N % vec 1)) ++
     subpath (&(SUC n) / &N % vec 1) (&n / &N % vec 1) h ++
     linepath(h (&n / &N % vec 1),g (&n / &N % vec 1))`;
    `ball((p:real^1->complex) t,ee(p t))`] CAUCHY_THEOREM_PRIMITIVE) THEN
  ASM_SIMP_TAC[VALID_PATH_JOIN_EQ; PATHSTART_JOIN; PATHFINISH_JOIN;
   PATHSTART_SUBPATH; PATHFINISH_SUBPATH; PATH_IMAGE_JOIN; PATHSTART_LINEPATH;
   PATHFINISH_LINEPATH; VALID_PATH_LINEPATH; UNION_SUBSET] THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN ANTS_TAC THENL
   [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `(p:real^1->complex) t`) THEN ANTS_TAC THENL
     [ASM_MESON_TAC[path_image; IN_IMAGE; SUBSET];
      ASM_SIMP_TAC[HAS_COMPLEX_DERIVATIVE_AT_WITHIN; CENTRE_IN_BALL]];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ q /\ (p ==> r ==> s) ==> (p /\ q ==> r) ==> s`) THEN
  CONJ_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC VALID_PATH_SUBPATH THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_CMUL; DROP_VEC; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `drop(&n / &N % vec 1) <= drop(&(SUC n) / &N % vec 1)`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[DROP_CMUL; DROP_VEC; REAL_MUL_RID; REAL_LE_DIV2_EQ;
                   REAL_OF_NUM_LT; LE_1; REAL_OF_NUM_LE] THEN
      ARITH_TAC;
      ASM_SIMP_TAC[PATH_IMAGE_SUBPATH; PATH_IMAGE_LINEPATH] THEN
      ONCE_REWRITE_TAC[GSYM REVERSEPATH_SUBPATH] THEN
      ASM_SIMP_TAC[PATH_IMAGE_SUBPATH; PATH_IMAGE_REVERSEPATH]] THEN
    MATCH_MP_TAC(TAUT
     `(p /\ r) /\ (p /\ r ==> q /\ s) ==> p /\ q /\ r /\ s`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      REWRITE_TAC[AND_FORALL_THM; TAUT
        `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
      X_GEN_TAC `u:real^1` THEN REWRITE_TAC[IN_INTERVAL_1] THEN
      REWRITE_TAC[DROP_CMUL; DROP_VEC; REAL_MUL_RID] THEN STRIP_TAC THEN
      REWRITE_TAC[IN_BALL] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NORM_ARITH
       `!e pu. dist(pt,pn) < ee / &3
               ==> dist(pn,pu) < e / &3 /\ e <= ee /\
                   norm(gu - pu) < e / &3 /\ norm(hu - pu) < e / &3
                   ==> dist(pt,gu) < ee /\ dist(pt,hu) < ee`)) THEN
      MAP_EVERY EXISTS_TAC [`e:real`; `(p:real^1->complex) u`] THEN
      ASM_SIMP_TAC[] THEN
      SUBGOAL_THEN `(u:real^1) IN interval[vec 0,vec 1]` ASSUME_TAC THENL
       [REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN CONJ_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
           REAL_LE_TRANS)) THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS];
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
           REAL_LE_TRANS)) THEN
          ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
          ASM_REWRITE_TAC[REAL_MUL_LID; REAL_OF_NUM_LE]];
        ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[DIST_REAL; GSYM drop; IN_INTERVAL_1;
                    DROP_VEC; DROP_CMUL; REAL_MUL_RID] THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POS; REAL_LE_DIV;
              REAL_OF_NUM_LT; LE_1; REAL_MUL_LID; REAL_OF_NUM_LE;
              ARITH_RULE `SUC n <= N ==> n <= N`] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
         `u <= s ==> n <= u /\ s - n < d ==> abs(n - u) < d`)) THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[real_div; GSYM REAL_SUB_RDISTRIB] THEN
        SIMP_TAC[REAL_OF_NUM_SUB; ARITH_RULE `n <= SUC n`] THEN
        ASM_REWRITE_TAC[ARITH_RULE `SUC n - n = 1`; REAL_MUL_LID]];
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SUBSET] THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN STRIP_TAC THEN
      REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN CONJ_TAC THEN
      MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_BALL] THEN
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[ENDS_IN_INTERVAL; INTERVAL_EQ_EMPTY_1; REAL_NOT_LT] THEN
      REWRITE_TAC[DROP_VEC; DROP_CMUL; REAL_MUL_RID] THEN
        ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_POS; REAL_LE_DIV;
              REAL_OF_NUM_LT; LE_1; REAL_MUL_LID; REAL_OF_NUM_LE] THEN
      ARITH_TAC];
    STRIP_TAC THEN DISCH_THEN(fun th ->
        MP_TAC(MATCH_MP PATH_INTEGRAL_UNIQUE th) THEN
        MP_TAC(MATCH_MP HAS_PATH_INTEGRAL_INTEGRABLE th)) THEN
    ASM_SIMP_TAC[PATH_INTEGRABLE_JOIN; VALID_PATH_JOIN_EQ; VALID_PATH_LINEPATH;
      PATHSTART_SUBPATH; PATHFINISH_SUBPATH; PATHSTART_JOIN; PATHFINISH_JOIN;
      PATHSTART_LINEPATH; PATHFINISH_LINEPATH; VALID_PATH_LINEPATH;
      PATH_INTEGRAL_JOIN] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check(is_imp o concl)) THEN
    ASM_SIMP_TAC[ARITH_RULE `SUC n <= N ==> n <= N`] THEN
    MATCH_MP_TAC(COMPLEX_RING
     `hn - he = hn' /\ gn + gd = gn' /\ hgn = --ghn
      ==> hn - gn = ghn - gh0
          ==> gd + ghn' + he + hgn = Cx(&0)
              ==> hn' - gn' = ghn' - gh0`) THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[complex_sub; GSYM PATH_INTEGRAL_REVERSEPATH] THEN
      REWRITE_TAC[REVERSEPATH_SUBPATH] THEN
      MATCH_MP_TAC PATH_INTEGRAL_SUBPATH_COMBINE;
      MATCH_MP_TAC PATH_INTEGRAL_SUBPATH_COMBINE;
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
       [GSYM REVERSEPATH_LINEPATH] THEN
      MATCH_MP_TAC PATH_INTEGRAL_REVERSEPATH] THEN
    ASM_REWRITE_TAC[VALID_PATH_LINEPATH] THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_CMUL; DROP_VEC; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1;
                 REAL_MUL_LID; REAL_OF_NUM_LE] THEN
    ASM_SIMP_TAC[ARITH_RULE `SUC n <= N ==> n <= N`] THEN
    TRY(MATCH_MP_TAC PATH_INTEGRABLE_HOLOMORPHIC_SIMPLE THEN
        EXISTS_TAC `s:complex->bool` THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    ASM_MESON_TAC[PATH_INTEGRABLE_REVERSEPATH; VALID_PATH_LINEPATH;
                  REVERSEPATH_LINEPATH]]);;

(* ------------------------------------------------------------------------- *)
(* Hence we can treat even non-rectifiable paths as having a "length"        *)
(* for bounds on analytic functions in open sets.                            *)
(* ------------------------------------------------------------------------- *)

let VALID_PATH_VECTOR_POLYNOMIAL_FUNCTION = prove
 (`!p:real^1->complex.
     vector_polynomial_function p ==> valid_path p`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[valid_path] THEN
  MATCH_MP_TAC DIFFERENTIABLE_ON_IMP_PIECEWISE_DIFFERENTIABLE THEN
  MATCH_MP_TAC DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON THEN
  REWRITE_TAC[VECTOR_DERIVATIVE_WORKS] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[vector_derivative] THEN
  CONV_TAC SELECT_CONV THEN
  ASM_MESON_TAC[HAS_VECTOR_DERIVATIVE_VECTOR_POLYNOMIAL_FUNCTION]);;

let PATH_INTEGRAL_BOUND_EXISTS = prove
 (`!s g. open s /\ valid_path g /\ path_image g SUBSET s
         ==> ?L. &0 < L /\
                 !f B. f holomorphic_on s /\ (!z. z IN s ==> norm(f z) <= B)
                       ==> norm(path_integral g f) <= L * B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:complex->bool`; `g:real^1->complex`]
        PATH_INTEGRAL_NEARBY_ENDS) THEN
  ASM_SIMP_TAC[VALID_PATH_IMP_PATH] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o SPEC `g:real^1->complex`) THEN
  ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  MP_TAC(ISPECL [`g:real^1->complex`; `d:real`]
   PATH_APPROX_VECTOR_POLYNOMIAL_FUNCTION) THEN
  ASM_SIMP_TAC[VALID_PATH_IMP_PATH] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^1->complex` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p:real^1->complex`) THEN
  ASM_SIMP_TAC[VALID_PATH_VECTOR_POLYNOMIAL_FUNCTION] THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `p':real^1->complex` STRIP_ASSUME_TAC o
    MATCH_MP HAS_VECTOR_DERIVATIVE_VECTOR_POLYNOMIAL_FUNCTION) THEN
  SUBGOAL_THEN `bounded(IMAGE (p':real^1->complex) (interval[vec 0,vec 1]))`
  MP_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    REWRITE_TAC[COMPACT_INTERVAL] THEN
    ASM_MESON_TAC[CONTINUOUS_VECTOR_POLYNOMIAL_FUNCTION;
                  CONTINUOUS_AT_IMP_CONTINUOUS_ON];
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE]] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `L:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `f path_integrable_on p /\ valid_path p` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PATH_INTEGRABLE_HOLOMORPHIC_SIMPLE;
                  VALID_PATH_VECTOR_POLYNOMIAL_FUNCTION];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:complex->complex`; `p:real^1->complex`]
        PATH_INTEGRAL_INTEGRAL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
   `drop(integral (interval[vec 0,vec 1]) (\x:real^1. lift(L * B)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
    ASM_REWRITE_TAC[INTEGRABLE_CONST; GSYM PATH_INTEGRABLE_ON] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[LIFT_DROP; COMPLEX_NORM_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[path_image; SUBSET; IN_IMAGE];
      ASM_MESON_TAC[HAS_VECTOR_DERIVATIVE_UNIQUE_AT]];
    REWRITE_TAC[INTEGRAL_CONST; CONTENT_UNIT_1; VECTOR_MUL_LID] THEN
    REWRITE_TAC[LIFT_DROP; REAL_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Winding number.                                                           *)
(* ------------------------------------------------------------------------- *)

let winding_number = new_definition
 `winding_number(g,z) =
    @n. !e. &0 < e
            ==> ?p. valid_path p /\ ~(z IN path_image p) /\
                    pathstart p = pathstart g /\
                    pathfinish p = pathfinish g /\
                    (!t. t IN interval[vec 0,vec 1] ==> norm(g t - p t) < e) /\
                    path_integral p (\w. Cx(&1) / (w - z)) =
                    Cx(&2) * Cx(pi) * ii * n`;;

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

let WINDING_NUMBER = prove
 (`!g z e.
        path g /\ ~(z IN path_image g) /\ &0 < e
         ==> ?p. valid_path p /\ ~(z IN path_image p) /\
                 pathstart p = pathstart g /\
                 pathfinish p = pathfinish g /\
                 (!t. t IN interval[vec 0,vec 1] ==> norm(g t - p t) < e) /\
                 path_integral p (\w. Cx(&1) / (w - z)) =
                 Cx(&2) * Cx(pi) * ii * winding_number(g,z)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[winding_number] THEN CONV_TAC SELECT_CONV THEN
  MP_TAC(ISPECL [`(:complex) DELETE z`; `g:real^1->complex`]
        PATH_INTEGRAL_NEARBY_ENDS) THEN
  ASM_SIMP_TAC[OPEN_DELETE; OPEN_UNIV] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g:real^1->complex`; `d / &2`]
    PATH_APPROX_VECTOR_POLYNOMIAL_FUNCTION) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^1->complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `Cx (&1) / (Cx (&2) * Cx pi * ii) *
              path_integral h (\w. Cx (&1) / (w - z))` THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g:real^1->complex`; `min d e / &2`]
    PATH_APPROX_VECTOR_POLYNOMIAL_FUNCTION) THEN
  ASM_REWRITE_TAC[REAL_HALF; REAL_LT_MIN] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:real^1->complex` THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC[VALID_PATH_VECTOR_POLYNOMIAL_FUNCTION; CX_2PII_NZ; COMPLEX_FIELD
   `~(a * b * c = Cx(&0))
    ==> a * b * c * Cx(&1) / (a * b * c) * z = z`] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`h:real^1->complex`; `p:real^1->complex`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[VALID_PATH_VECTOR_POLYNOMIAL_FUNCTION] THEN
    ASM_MESON_TAC[NORM_ARITH
     `norm(h - g) < d / &2 /\ norm(p - g) < min d e / &2
      ==> norm(h - g) < d /\ norm(p - g) < d`];
    ALL_TAC] THEN
  REWRITE_TAC[SET_RULE `t SUBSET UNIV DELETE x <=> ~(x IN t)`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[NORM_SUB; REAL_ARITH `&0 < e /\ x < min d e / &2 ==> x < e`];
    ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[OPEN_DELETE; OPEN_UNIV; HOLOMORPHIC_ON_OPEN] THEN
  REWRITE_TAC[IN_DELETE; IN_UNIV; GSYM complex_differentiable] THEN
  REPEAT STRIP_TAC THEN COMPLEX_DIFFERENTIABLE_TAC THEN
  ASM_REWRITE_TAC[COMPLEX_SUB_0]);;

let WINDING_NUMBER_UNIQUE = prove
 (`!g z e n.
        path g /\ ~(z IN path_image g) /\
        (!e. &0 < e
             ==> ?p. valid_path p /\ ~(z IN path_image p) /\
                     pathstart p = pathstart g /\
                     pathfinish p = pathfinish g /\
                     (!t. t IN interval[vec 0,vec 1]
                          ==> norm(g t - p t) < e) /\
                     path_integral p (\w. Cx(&1) / (w - z)) =
                     Cx(&2) * Cx(pi) * ii * n)
        ==> winding_number(g,z) = n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:complex) DELETE z`; `g:real^1->complex`]
        PATH_INTEGRAL_NEARBY_ENDS) THEN
  ASM_SIMP_TAC[OPEN_DELETE; OPEN_UNIV] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^1->complex` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g:real^1->complex`; `z:complex`] WINDING_NUMBER) THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^1->complex` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:real^1->complex`; `q:real^1->complex`]) THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_SIMP_TAC[] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `\w. Cx(&1) / (w - z)`) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_DELETE; OPEN_UNIV; HOLOMORPHIC_ON_OPEN] THEN
    REWRITE_TAC[IN_DELETE; IN_UNIV; GSYM complex_differentiable] THEN
    REPEAT STRIP_TAC THEN COMPLEX_DIFFERENTIABLE_TAC THEN
    ASM_REWRITE_TAC[COMPLEX_SUB_0];
    ASM_REWRITE_TAC[] THEN MP_TAC CX_2PII_NZ THEN
    CONV_TAC COMPLEX_RING]);;

let WINDING_NUMBER_UNIQUE_LOOP = prove
 (`!g z e n.
        path g /\ ~(z IN path_image g) /\ pathfinish g = pathstart g /\
        (!e. &0 < e
             ==> ?p. valid_path p /\ ~(z IN path_image p) /\
                     pathfinish p = pathstart p /\
                     (!t. t IN interval[vec 0,vec 1]
                          ==> norm(g t - p t) < e) /\
                     path_integral p (\w. Cx(&1) / (w - z)) =
                     Cx(&2) * Cx(pi) * ii * n)
        ==> winding_number(g,z) = n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:complex) DELETE z`; `g:real^1->complex`]
        PATH_INTEGRAL_NEARBY_LOOP) THEN
  ASM_SIMP_TAC[OPEN_DELETE; OPEN_UNIV] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^1->complex` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g:real^1->complex`; `z:complex`] WINDING_NUMBER) THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^1->complex` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:real^1->complex`; `q:real^1->complex`]) THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_SIMP_TAC[] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `\w. Cx(&1) / (w - z)`) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_DELETE; OPEN_UNIV; HOLOMORPHIC_ON_OPEN] THEN
    REWRITE_TAC[IN_DELETE; IN_UNIV; GSYM complex_differentiable] THEN
    REPEAT STRIP_TAC THEN COMPLEX_DIFFERENTIABLE_TAC THEN
    ASM_REWRITE_TAC[COMPLEX_SUB_0];
    ASM_REWRITE_TAC[] THEN MP_TAC CX_2PII_NZ THEN
    CONV_TAC COMPLEX_RING]);;

let WINDING_NUMBER_VALID_PATH = prove
 (`!g z. valid_path g /\ ~(z IN path_image g)
         ==> winding_number(g,z) =
             Cx(&1) / (Cx(&2) * Cx(pi) * ii) *
             path_integral g (\w. Cx(&1) / (w - z))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WINDING_NUMBER_UNIQUE THEN
  ASM_SIMP_TAC[VALID_PATH_IMP_PATH] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `g:real^1->complex` THEN
  ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
  MP_TAC CX_2PII_NZ THEN CONV_TAC COMPLEX_FIELD);;

let HAS_PATH_INTEGRAL_WINDING_NUMBER = prove
 (`!g z. valid_path g /\ ~(z IN path_image g)
         ==> ((\w. Cx(&1) / (w - z)) has_path_integral
              (Cx(&2) * Cx(pi) * ii * winding_number(g,z))) g`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WINDING_NUMBER_VALID_PATH] THEN
  ASM_SIMP_TAC[CX_2PII_NZ; COMPLEX_FIELD
   `~(a * b * c = Cx(&0))
    ==> a * b * c * Cx(&1) / (a * b * c) * z = z`] THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_INTEGRAL THEN
  ASM_SIMP_TAC[PATH_INTEGRABLE_INVERSEDIFF]);;

let WINDING_NUMBER_TRIVIAL = prove
 (`!a z. ~(z = a) ==> winding_number(linepath(a,a),z) = Cx(&0)`,
  SIMP_TAC[VALID_PATH_LINEPATH; PATH_INTEGRAL_TRIVIAL; COMPLEX_MUL_RZERO;
           WINDING_NUMBER_VALID_PATH; PATH_IMAGE_LINEPATH; SEGMENT_REFL;
           IN_SING]);;

let WINDING_NUMBER_JOIN = prove
 (`!g1 g2 z.
        path g1 /\ path g2 /\ pathfinish g1 = pathstart g2 /\
        ~(z IN path_image g1) /\ ~(z IN path_image g2)
        ==> winding_number(g1 ++ g2,z) =
            winding_number(g1,z) + winding_number(g2,z)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WINDING_NUMBER_UNIQUE THEN
  ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; IN_UNION] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g2:real^1->complex`; `z:complex`; `e:real`]
    WINDING_NUMBER) THEN
  MP_TAC(ISPECL [`g1:real^1->complex`; `z:complex`; `e:real`]
    WINDING_NUMBER) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `p1:real^1->complex` THEN STRIP_TAC THEN
  X_GEN_TAC `p2:real^1->complex` THEN STRIP_TAC THEN
  EXISTS_TAC `p1 ++ p2:real^1->complex` THEN
  ASM_SIMP_TAC[VALID_PATH_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN] THEN
  ASM_SIMP_TAC[PATH_IMAGE_JOIN; IN_UNION] THEN  CONJ_TAC THENL
   [REWRITE_TAC[joinpaths; IN_INTERVAL_1; DROP_VEC] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; DROP_CMUL; DROP_SUB] THEN
    ASM_REAL_ARITH_TAC;
    W(MP_TAC o PART_MATCH (lhs o rand) PATH_INTEGRAL_JOIN o lhand o snd) THEN
    ASM_REWRITE_TAC[COMPLEX_ADD_LDISTRIB] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THEN MATCH_MP_TAC PATH_INTEGRABLE_INVERSEDIFF THEN
    ASM_REWRITE_TAC[]]);;

let WINDING_NUMBER_REVERSEPATH = prove
 (`!g z. path g /\ ~(z IN path_image g)
         ==> winding_number(reversepath g,z) = --(winding_number(g,z))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WINDING_NUMBER_UNIQUE THEN
  ASM_SIMP_TAC[PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g:real^1->complex`; `z:complex`; `e:real`]
    WINDING_NUMBER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^1->complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `reversepath p:real^1->complex` THEN
  ASM_SIMP_TAC[VALID_PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH;
               PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
               PATH_INTEGRAL_REVERSEPATH; PATH_INTEGRABLE_INVERSEDIFF] THEN
  REWRITE_TAC[COMPLEX_MUL_RNEG; reversepath; IN_INTERVAL_1; DROP_VEC] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; DROP_SUB] THEN ASM_REAL_ARITH_TAC);;

let WINDING_NUMBER_SHIFTPATH = prove
 (`!g a z. path g /\ pathfinish g = pathstart g /\ ~(z IN path_image g) /\
           a IN interval[vec 0,vec 1]
           ==> winding_number(shiftpath a g,z) = winding_number(g,z)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WINDING_NUMBER_UNIQUE_LOOP THEN
  ASM_SIMP_TAC[PATH_SHIFTPATH; PATH_IMAGE_SHIFTPATH] THEN CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
    ASM_SIMP_TAC[PATHSTART_SHIFTPATH; PATHFINISH_SHIFTPATH];
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g:real^1->complex`; `z:complex`; `e:real`]
    WINDING_NUMBER) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^1->complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `shiftpath a p:real^1->complex` THEN
  ASM_SIMP_TAC[VALID_PATH_SHIFTPATH; PATH_IMAGE_SHIFTPATH;
               PATH_INTEGRAL_SHIFTPATH; PATH_INTEGRABLE_INVERSEDIFF] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
  ASM_SIMP_TAC[PATHSTART_SHIFTPATH; PATHFINISH_SHIFTPATH] THEN
  SIMP_TAC[COMPLEX_MUL_RNEG; shiftpath; IN_INTERVAL_1; DROP_ADD; DROP_VEC] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; DROP_SUB; DROP_ADD] THEN
  ASM_REAL_ARITH_TAC);;

let WINDING_NUMBER_SPLIT_LINEPATH = prove
 (`!a b c z.
    c IN segment[a,b] /\ ~(z IN segment[a,b])
    ==> winding_number(linepath(a,b),z) =
        winding_number(linepath(a,c),z) +
        winding_number(linepath(c,b),z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~((z:complex) IN segment[a,c]) /\ ~(z IN segment[c,b])`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `~(z IN s) ==> t SUBSET s ==> ~(z IN t)`)) THEN
    ASM_REWRITE_TAC[SUBSET_SEGMENT; ENDS_IN_SEGMENT];
    ASM_SIMP_TAC[WINDING_NUMBER_VALID_PATH; PATH_IMAGE_LINEPATH;
                 VALID_PATH_LINEPATH] THEN
    REWRITE_TAC[GSYM COMPLEX_ADD_LDISTRIB] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC PATH_INTEGRAL_SPLIT_LINEPATH THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_DIV THEN
    SIMP_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID] THEN
    ASM_MESON_TAC[COMPLEX_SUB_0]]);;

let WINDING_NUMBER_EQUAL = prove
 (`!p q z. (!t. t IN interval[vec 0,vec 1] ==> p t = q t)
           ==> winding_number(p,z) = winding_number(q,z)`,
  REPEAT STRIP_TAC THEN SIMP_TAC[winding_number; PATH_INTEGRAL_INTEGRAL] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `W:complex` THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `e:real` THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `g:real^1->complex` THEN
  ASM_SIMP_TAC[pathstart; pathfinish; ENDS_IN_UNIT_INTERVAL]);;

let WINDING_NUMBER_OFFSET = prove
 (`!p z. winding_number(p,z) = winding_number((\w. p w - z),Cx(&0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[winding_number; PATH_INTEGRAL_INTEGRAL] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `W:complex` THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `e:real` THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `&0 < e` THEN
  ASM_REWRITE_TAC[path_image; valid_path; pathstart; pathfinish] THEN
  EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->complex` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `\t. (g:real^1->complex) t - z`;
    EXISTS_TAC `\t. (g:real^1->complex) t + z`] THEN
  ASM_REWRITE_TAC[COMPLEX_RING `(p - z) - (g - z):complex = p - g`;
                  COMPLEX_RING `p - (g + z):complex = p - z - g`;
                  COMPLEX_RING `(p - z) + z:complex = p`;
                  COMPLEX_SUB_RZERO] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_IMAGE]) THEN
  ASM_SIMP_TAC[PIECEWISE_DIFFERENTIABLE_ADD; PIECEWISE_DIFFERENTIABLE_SUB;
               DIFFERENTIABLE_ON_IMP_PIECEWISE_DIFFERENTIABLE;
               DIFFERENTIABLE_ON_CONST; IN_IMAGE] THEN
  ASM_REWRITE_TAC[COMPLEX_RING `Cx(&0) = w - z <=> z = w`;
                  COMPLEX_RING `z = w + z <=> Cx(&0) = w`] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN
  REWRITE_TAC[COMPLEX_RING `(w + z) - z = w - Cx(&0)`] THEN AP_TERM_TAC THEN
  REWRITE_TAC[vector_derivative; has_vector_derivative; HAS_DERIVATIVE_AT;
              COMPLEX_RING `(x - z) - (w - z):complex = x - w`;
              COMPLEX_RING `(x + z) - (w + z):complex = x - w`]);;

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
  ASM_SIMP_TAC[WINDING_NUMBER_JOIN; VALID_PATH_IMP_PATH; RE_ADD] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Useful sufficient conditions for the winding number to be positive etc.   *)
(* ------------------------------------------------------------------------- *)

let RE_WINDING_NUMBER = prove
 (`!g z. valid_path g /\ ~(z IN path_image g)
         ==> Re(winding_number(g,z)) =
             Im(path_integral g (\w. Cx(&1) / (w - z))) / (&2 * pi)`,
  SIMP_TAC[WINDING_NUMBER_VALID_PATH; complex_div; COMPLEX_MUL_LID] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[COMPLEX_MUL_ASSOC; GSYM CX_MUL] THEN
  REWRITE_TAC[COMPLEX_INV_MUL; GSYM CX_INV; COMPLEX_INV_II] THEN
  REWRITE_TAC[COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG; RE_NEG] THEN
  REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC; RE_MUL_CX; RE_MUL_II] THEN
  MP_TAC PI_POS THEN CONV_TAC REAL_FIELD);;

let WINDING_NUMBER_POS_LE = prove
 (`!g z. valid_path g /\ ~(z IN path_image g) /\
         (!x. x IN interval(vec 0,vec 1)
              ==> &0 <= Im(vector_derivative g (at x) * cnj(g x - z)))
         ==> &0 <= Re(winding_number(g,z))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RE_WINDING_NUMBER] THEN
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
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RE_WINDING_NUMBER] THEN
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
  MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[IN_DIFF; FINITE_IMP_COUNTABLE] THEN
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

let WINDING_NUMBER_AHLFORS_FULL = prove
 (`!p z. path p /\ ~(z IN path_image p)
         ==> pathfinish p - z =
             cexp(Cx(&2) * Cx pi * ii * winding_number(p,z)) *
             (pathstart p - z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:real^1->complex`; `z:complex`; `&1`] WINDING_NUMBER) THEN
  ASM_REWRITE_TAC[REAL_LT_01; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g:real^1->complex` THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[valid_path; path_image; IN_IMAGE;
        NOT_EXISTS_THM]) THEN
  MP_TAC(ISPECL
   [`g:real^1->complex`; `z:complex`; `vec 0:real^1`; `vec 1:real^1`]
   WINDING_NUMBER_AHLFORS) THEN
  ASM_SIMP_TAC[DROP_VEC; REAL_POS; pathstart; pathfinish] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[]; DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2)] THEN
  REWRITE_TAC[GSYM CEXP_ADD; COMPLEX_MUL_ASSOC; PATH_INTEGRAL_INTEGRAL] THEN
  REWRITE_TAC[SIMPLE_COMPLEX_ARITH `Cx(&1) / z * w = w / z`] THEN
  REWRITE_TAC[GSYM complex_sub; COMPLEX_SUB_REFL; CEXP_0; COMPLEX_MUL_LID]);;

(* ------------------------------------------------------------------------- *)
(* State in terms of complex integers. Note the useful equality version.     *)
(* ------------------------------------------------------------------------- *)

let complex_integer = new_definition
 `complex_integer z <=> integer(Re z) /\ Im z = &0`;;

let COMPLEX_INTEGER = prove
 (`complex_integer z <=> ?n. integer n /\ z = Cx n`,
  REWRITE_TAC[COMPLEX_EQ; RE_CX; IM_CX; complex_integer] THEN MESON_TAC[]);;

let INTEGER_WINDING_NUMBER_EQ = prove
 (`!g z. path g /\ ~(z IN path_image g)
         ==> (complex_integer(winding_number(g,z)) <=>
              pathfinish g = pathstart g)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `(:complex) DIFF path_image g` OPEN_CONTAINS_BALL) THEN
  ASM_SIMP_TAC[GSYM closed; CLOSED_PATH_IMAGE; VALID_PATH_IMP_PATH] THEN
  DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g:real^1->complex`; `z:complex`; `e:real`]
    WINDING_NUMBER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^1->complex` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `complex_integer(winding_number(p,z)) <=>
    pathfinish p = pathstart p`
  MP_TAC THENL
   [UNDISCH_THEN
     `path_integral p (\w. Cx (&1) / (w - z)) =
      Cx (&2) * Cx pi * ii * winding_number (g,z)` (K ALL_TAC) THEN
    ASM_SIMP_TAC[WINDING_NUMBER_VALID_PATH];
    ASM_SIMP_TAC[WINDING_NUMBER_VALID_PATH; CX_2PII_NZ; COMPLEX_FIELD
     `~(a * b * c = Cx(&0))
      ==> Cx(&1) / (a * b * c) * a * b * c * z = z`]] THEN
  UNDISCH_THEN `pathstart p:complex = pathstart g` (SUBST_ALL_TAC o SYM) THEN
  UNDISCH_THEN `pathfinish p:complex = pathfinish g` (SUBST_ALL_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[valid_path; path_image]) THEN
  REWRITE_TAC[pathfinish; pathstart] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `cexp(path_integral p (\w. Cx(&1) / (w - z))) = Cx(&1)` THEN
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
    MP_TAC(ISPECL [`p:real^1->complex`; `z:complex`;
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
 (`!g z. path g /\ pathfinish g = pathstart g /\ ~(z IN path_image g)
         ==> complex_integer(winding_number(g,z))`,
  MESON_TAC[INTEGER_WINDING_NUMBER_EQ]);;

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
    ASM_SIMP_TAC[WINDING_NUMBER_VALID_PATH; GSYM IM_DEF] THEN
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
  ASM_SIMP_TAC[GSYM RE_NEG; VALID_PATH_IMP_PATH;
               GSYM WINDING_NUMBER_REVERSEPATH] THEN
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
   [ASM_SIMP_TAC[INTEGER_WINDING_NUMBER; VALID_PATH_IMP_PATH]; ALL_TAC] THEN
  SIMP_TAC[complex_integer; COMPLEX_EQ; RE_CX; IM_CX] THEN
  SIMP_TAC[REAL_LT_INTEGERS; INTEGER_CLOSED] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Continuity of winding number and invariance on connected sets.            *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_AT_WINDING_NUMBER = prove
 (`!g z. path g /\ ~(z IN path_image g)
         ==> (\w. winding_number(g,w)) continuous (at z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `(:complex) DIFF path_image g` OPEN_CONTAINS_CBALL) THEN
  ASM_SIMP_TAC[GSYM closed; CLOSED_PATH_IMAGE] THEN
  DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; SUBSET; IN_CBALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`(:complex) DIFF cball(z,e / &2)`; `g:real^1->complex`]
        PATH_INTEGRAL_NEARBY_ENDS) THEN
  ASM_SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_CBALL] THEN ANTS_TAC THENL
   [REWRITE_TAC[SUBSET; IN_DIFF; IN_CBALL; SUBSET; IN_UNIV] THEN
    GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g:real^1->complex`; `z:complex`; `min d e / &2`]
    WINDING_NUMBER) THEN
  ASM_REWRITE_TAC[REAL_HALF; REAL_LT_MIN] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^1->complex` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
  MAP_EVERY EXISTS_TAC [`\w. winding_number(p,w)`; `min d e / &2`] THEN
  ASM_REWRITE_TAC[REAL_HALF; REAL_LT_MIN] THEN CONJ_TAC THENL
   [X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
    MATCH_MP_TAC WINDING_NUMBER_UNIQUE THEN
    ASM_SIMP_TAC[VALID_PATH_IMP_PATH] THEN
    MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [REWRITE_TAC[path_image; IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(g:real^1->complex) t`) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1`) THEN
      ASM_SIMP_TAC[path_image; FUN_IN_IMAGE] THEN
      UNDISCH_TAC `dist (w:complex,z) < min d e / &2` THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NORM_ARITH;
      DISCH_TAC THEN X_GEN_TAC `k:real` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`g:real^1->complex`; `w:complex`; `min k (min d e) / &2`]
         WINDING_NUMBER) THEN
      ASM_REWRITE_TAC[REAL_HALF; REAL_LT_MIN] THEN ANTS_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^1->complex` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `p:real^1->complex` THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM(MP_TAC o SPECL
        [`p:real^1->complex`; `q:real^1->complex`]) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1`)) THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC NORM_ARITH;
        DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS)] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN
      SIMP_TAC[HOLOMORPHIC_ON_SUB; HOLOMORPHIC_ON_ID; HOLOMORPHIC_ON_CONST;
               IN_DELETE; IN_UNIV; COMPLEX_SUB_0] THEN
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN SIMP_TAC[IN_DIFF] THEN
      REWRITE_TAC[IN_UNIV; IN_CBALL] THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC];
    UNDISCH_TAC `~((z:complex) IN path_image p)` THEN
    UNDISCH_TAC `valid_path(p:real^1->complex)` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN SPEC_TAC(`z:complex`,`z:complex`) THEN
    SPEC_TAC(`p:real^1->complex`,`g:real^1->complex`)] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `(:complex) DIFF path_image g` OPEN_CONTAINS_BALL) THEN
  ASM_SIMP_TAC[GSYM closed; CLOSED_PATH_IMAGE; VALID_PATH_IMP_PATH] THEN
  DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`(:complex) DIFF cball(z, &3 / &4 * d)`; `g:real^1->complex`]
        PATH_INTEGRAL_BOUND_EXISTS) THEN
  ASM_REWRITE_TAC[GSYM closed; CLOSED_CBALL; SUBSET; IN_DIFF;
                  IN_CBALL; IN_UNIV; REAL_NOT_LE] THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[REAL_ARITH `&0 < d /\ ~(&3 / &4 * d < x) ==> x < d`];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[continuous_at] THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  EXISTS_TAC `min (d / &4) (e / &2 * d pow 2 / L / &4)` THEN
  ASM_SIMP_TAC[REAL_LT_MIN; REAL_POW_LT; REAL_LT_DIV; REAL_LT_MUL; REAL_HALF;
               REAL_ARITH `&0 < x / &4 <=> &0 < x`] THEN
  X_GEN_TAC `w:complex` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((w:complex) IN path_image g)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[dist; WINDING_NUMBER_VALID_PATH; GSYM COMPLEX_SUB_LDISTRIB] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_DIV; COMPLEX_NORM_CX] THEN
  REWRITE_TAC[REAL_ABS_NUM; COMPLEX_NORM_II; REAL_ABS_PI] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID; REAL_MUL_RID] THEN
  MATCH_MP_TAC(REAL_ARITH
    `inv p * x <= &1 * x /\ x < e ==> inv p * x < e`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_INV_LE_1 THEN MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `!d. &0 < e /\ d = e / &2 /\ x <= d ==> x < e`) THEN
  EXISTS_TAC `L * (e / &2 * d pow 2 / L / &4) * inv(d / &2) pow 2` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 < d`; `&0 < L`] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `path_integral g (\x. Cx(&1) / (x - w)) -
    path_integral g (\x. Cx(&1) / (x - z)) =
    path_integral g (\x. Cx(&1) / (x - w) - Cx(&1) / (x - z))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC PATH_INTEGRAL_SUB THEN
    CONJ_TAC THEN MATCH_MP_TAC PATH_INTEGRABLE_INVERSEDIFF THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SIMP_TAC[HOLOMORPHIC_ON_OPEN; GSYM closed; CLOSED_CBALL] THEN
  REWRITE_TAC[IN_UNIV; IN_DIFF; IN_CBALL; REAL_NOT_LE; AND_FORALL_THM] THEN
  X_GEN_TAC `x:complex` THEN
  REWRITE_TAC[TAUT `(a ==> b) /\ (a ==> c) <=> a ==> b /\ c`] THEN
  DISCH_TAC THEN REWRITE_TAC[GSYM complex_differentiable] THEN
  SUBGOAL_THEN `~(x:complex = w) /\ ~(x = z)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_NOT_LE])) THEN
    CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_SUB THEN
    CONJ_TAC THEN MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_DIV_AT THEN
    ASM_SIMP_TAC[COMPLEX_SUB_0; COMPLEX_DIFFERENTIABLE_SUB;
                 COMPLEX_DIFFERENTIABLE_ID; COMPLEX_DIFFERENTIABLE_CONST];
    ALL_TAC] THEN
  ASM_SIMP_TAC[COMPLEX_FIELD
   `~(x = w) /\ ~(x = z)
    ==> Cx(&1) / (x - w) - Cx(&1) / (x - z) =
        (w - z) * inv((x - w) * (x - z))`] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_SIMP_TAC[NORM_POS_LE; GSYM dist; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[COMPLEX_NORM_INV; REAL_POW_INV] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  ASM_SIMP_TAC[REAL_POW_2; REAL_LT_MUL; REAL_HALF; COMPLEX_NORM_MUL] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_HALF; REAL_LT_IMP_LE] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_NOT_LE])) THEN
  CONV_TAC NORM_ARITH);;

let CONTINUOUS_ON_WINDING_NUMBER = prove
 (`!g. path g
       ==> (\w. winding_number(g,w)) continuous_on
           ((:complex) DIFF path_image g)`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; GSYM closed;
           OPEN_UNIV; CLOSED_PATH_IMAGE; VALID_PATH_IMP_PATH] THEN
  SIMP_TAC[IN_DIFF; IN_UNIV; CONTINUOUS_AT_WINDING_NUMBER]);;

let WINDING_NUMBER_CONSTANT = prove
 (`!s g. path g /\ pathfinish g = pathstart g /\
         connected s /\ s INTER path_image g = {}
         ==> ?k. !z. z IN s ==> winding_number(g,z) = k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_DISCRETE_RANGE_CONSTANT THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:complex) DIFF path_image g` THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_WINDING_NUMBER] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
  X_GEN_TAC `w:complex` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN
   `complex_integer(winding_number(g,w)) /\
    complex_integer(winding_number(g,z))`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC INTEGER_WINDING_NUMBER THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    REWRITE_TAC[COMPLEX_INTEGER] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[GSYM CX_SUB; CX_INJ; COMPLEX_NORM_CX] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN
  ASM_SIMP_TAC[REAL_SUB_0; INTEGER_CLOSED]);;

let WINDING_NUMBER_EQ = prove
 (`!g s w z.
        path g /\ pathfinish g = pathstart g /\
        w IN s /\ z IN s /\ connected s /\ s INTER path_image g = {}
        ==> winding_number(g,w) = winding_number(g,z)`,
  MESON_TAC[WINDING_NUMBER_CONSTANT]);;

let OPEN_WINDING_NUMBER_LEVELSETS = prove
 (`!g k. path g /\ pathfinish g = pathstart g
         ==> open {z | ~(z IN path_image g) /\ winding_number(g,z) = k}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[open_def; IN_ELIM_THM] THEN
  X_GEN_TAC `z:complex` THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(:complex) DIFF path_image g` OPEN_CONTAINS_BALL) THEN
  ASM_SIMP_TAC[GSYM closed; CLOSED_PATH_IMAGE; VALID_PATH_IMP_PATH] THEN
  DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; SUBSET; IN_BALL] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:complex` THEN
  REPEAT STRIP_TAC THENL [ASM_MESON_TAC[DIST_SYM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(z:complex,e)`; `g:real^1->complex`]
        WINDING_NUMBER_CONSTANT) THEN
  ASM_SIMP_TAC[CONNECTED_BALL; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_BALL] THEN
  ASM_MESON_TAC[DIST_REFL; DIST_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Winding number is zero "outside" a curve, in various senses.              *)
(* ------------------------------------------------------------------------- *)

let WINDING_NUMBER_ZERO_IN_OUTSIDE = prove
 (`!g z. path g /\ pathfinish g = pathstart g /\ z IN outside(path_image g)
         ==> winding_number(g,z) = Cx(&0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`path_image(g:real^1->complex)`; `Cx(&0)`]
   BOUNDED_SUBSET_BALL) THEN ASM_SIMP_TAC[BOUNDED_PATH_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?w. ~(w IN ball(Cx(&0),B + &1))` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `~(s = UNIV) ==> ?z. ~(z IN s)`) THEN
    MESON_TAC[BOUNDED_BALL; NOT_BOUNDED_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Cx(&0)`; `B:real`; `B + &1`] SUBSET_BALL) THEN
  REWRITE_TAC[REAL_ARITH `B <= B + &1`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`path_image(g:real^1->complex)`; `ball(Cx(&0),B + &1)`]
        OUTSIDE_SUBSET_CONVEX) THEN
  ASM_REWRITE_TAC[CONVEX_BALL] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_UNIV; IN_DIFF] THEN DISCH_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `winding_number(g,w)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`outside(path_image(g:real^1->complex))`;
                   `g:real^1->complex`] WINDING_NUMBER_CONSTANT) THEN
    ASM_SIMP_TAC[OUTSIDE_NO_OVERLAP; CONNECTED_OUTSIDE;
                 DIMINDEX_2; LE_REFL; BOUNDED_PATH_IMAGE] THEN
    ASM SET_TAC[];
    MATCH_MP_TAC WINDING_NUMBER_UNIQUE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [ASM SET_TAC[]; DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC] THEN
    MP_TAC(ISPECL [`g:real^1->complex`; `min e (&1)`]
        PATH_APPROX_VECTOR_POLYNOMIAL_FUNCTION) THEN
    ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:real^1->complex` THEN
    STRIP_TAC THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
    ASM_SIMP_TAC[VALID_PATH_VECTOR_POLYNOMIAL_FUNCTION] THEN CONJ_TAC THENL
     [UNDISCH_TAC `~(w IN ball (Cx (&0),B + &1))` THEN
      REWRITE_TAC[CONTRAPOS_THM; path_image; IN_BALL] THEN
      SPEC_TAC(`w:complex`,`x:complex`) THEN REWRITE_TAC[FORALL_IN_IMAGE];
      REWRITE_TAC[COMPLEX_MUL_RZERO] THEN
      MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
      MATCH_MP_TAC CAUCHY_THEOREM_CONVEX_SIMPLE THEN
      EXISTS_TAC `ball(Cx(&0),B + &1)` THEN
      ASM_SIMP_TAC[CONVEX_BALL; VALID_PATH_VECTOR_POLYNOMIAL_FUNCTION] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN
        SIMP_TAC[HOLOMORPHIC_ON_SUB; HOLOMORPHIC_ON_ID; HOLOMORPHIC_ON_CONST;
                 COMPLEX_SUB_0] THEN
        ASM_MESON_TAC[];
        REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE; IN_BALL]]] THEN
      X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
      REWRITE_TAC[dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN
      MATCH_MP_TAC(NORM_ARITH
       `!g:real^1->complex. norm(p t - g t) < &1 /\ norm(g t) <= B
                            ==> norm(p t) < B + &1`) THEN
      EXISTS_TAC `g:real^1->complex` THEN
      UNDISCH_TAC `path_image g SUBSET ball (Cx (&0),B)` THEN
      ASM_SIMP_TAC[SUBSET; IN_BALL; path_image; FORALL_IN_IMAGE] THEN
      ASM_SIMP_TAC[dist; COMPLEX_SUB_LZERO; NORM_NEG; REAL_LT_IMP_LE]]);;

let WINDING_NUMBER_ZERO_OUTSIDE = prove
 (`!g s z. path g /\ convex s /\ pathfinish g = pathstart g /\
           ~(z IN s) /\ path_image g SUBSET s
           ==> winding_number(g,z) = Cx(&0)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WINDING_NUMBER_ZERO_IN_OUTSIDE THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`path_image(g:real^1->complex)`; `s:complex->bool`]
        OUTSIDE_SUBSET_CONVEX) THEN
  ASM SET_TAC[]);;

let WINDING_NUMBER_ZERO_ATINFINITY = prove
 (`!g. path g /\ pathfinish g = pathstart g
       ==> ?B. !z. B <= norm(z) ==> winding_number(g,z) = Cx(&0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `bounded (path_image g :complex->bool)` MP_TAC THENL
   [ASM_SIMP_TAC[BOUNDED_PATH_IMAGE]; ALL_TAC] THEN
  REWRITE_TAC[bounded] THEN DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  EXISTS_TAC `B + &1` THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC WINDING_NUMBER_ZERO_OUTSIDE THEN
  EXISTS_TAC `cball(Cx(&0),B)` THEN ASM_REWRITE_TAC[CONVEX_CBALL] THEN
  REWRITE_TAC[SUBSET; IN_CBALL; dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN
  ASM_MESON_TAC[REAL_ARITH `~(B + &1 <= z /\ z <= B)`]);;

let WINDING_NUMBER_ZERO_POINT = prove
 (`!g s. path g /\ pathfinish g = pathstart g /\
         open s /\ path_image g SUBSET s
         ==> ?z. z IN s /\ winding_number(g,z) = Cx(&0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`path_image g:complex->bool`; `s:complex->bool`]
        OUTSIDE_COMPACT_IN_OPEN) THEN
  ASM_SIMP_TAC[COMPACT_PATH_IMAGE] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[SUBSET_EMPTY; PATH_IMAGE_NONEMPTY]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN MATCH_MP_TAC MONO_EXISTS THEN
  GEN_TAC THEN REWRITE_TAC[IN_INTER] THEN
  ASM_SIMP_TAC[WINDING_NUMBER_ZERO_IN_OUTSIDE]);;

(* ------------------------------------------------------------------------- *)
(* If a path winds round a set, it winds rounds its inside.                  *)
(* ------------------------------------------------------------------------- *)

let WINDING_NUMBER_AROUND_INSIDE = prove
 (`!g s z.
        path g /\ pathfinish g = pathstart g /\
        closed s /\ connected s /\ s INTER path_image g = {} /\
        z IN s /\ ~(winding_number(g,z) = Cx(&0))
        ==> !w. w IN s UNION inside(s)
                ==> winding_number(g,w) = winding_number(g,z)`,
  MAP_EVERY X_GEN_TAC
   [`g:real^1->complex`; `s:complex->bool`; `z0:complex`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z. z IN s ==> winding_number(g,z) = winding_number(g,z0)`
  ASSUME_TAC THENL [ASM_MESON_TAC[WINDING_NUMBER_EQ]; ALL_TAC] THEN
  ABBREV_TAC `k = winding_number (g,z0)` THEN
  SUBGOAL_THEN `(s:complex->bool) SUBSET inside(path_image g)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; INSIDE_OUTSIDE; IN_DIFF; IN_UNIV; IN_UNION] THEN
    X_GEN_TAC `z:complex` THEN REPEAT STRIP_TAC THENL
     [ASM SET_TAC[]; ASM_MESON_TAC[WINDING_NUMBER_ZERO_IN_OUTSIDE]];
    ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN REWRITE_TAC[IN_UNION] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`s:complex->bool`;
                 `path_image g:complex->bool`]
        INSIDE_INSIDE_COMPACT_CONNECTED) THEN
  ASM_SIMP_TAC[COMPACT_PATH_IMAGE; CONNECTED_PATH_IMAGE] THEN STRIP_TAC THEN
  EXPAND_TAC "k" THEN MATCH_MP_TAC WINDING_NUMBER_EQ THEN
  EXISTS_TAC `s UNION inside s :complex->bool` THEN
  ASM_SIMP_TAC[CONNECTED_WITH_INSIDE; IN_UNION] THEN
  MP_TAC(ISPEC `path_image g :complex->bool` INSIDE_NO_OVERLAP) THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Bounding a WN by 1/2 for a path and point in opposite halfspaces.         *)
(* ------------------------------------------------------------------------- *)

let WINDING_NUMBER_SUBPATH_CONTINUOUS = prove
 (`!g z. valid_path g /\ ~(z IN path_image g)
         ==> (\a. winding_number(subpath (vec 0) a g,z)) continuous_on
             interval[vec 0,vec 1]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC
    `\a. Cx(&1) / (Cx(&2) * Cx pi * ii) *
         integral (interval[vec 0,a])
                  (\t. Cx(&1) / (g t - z) * vector_derivative g (at t))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `a:real^1` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
     `Cx(&1) / (Cx(&2) * Cx pi * ii) *
      path_integral (subpath (vec 0) a g) (\w. Cx (&1) / (w - z))` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC PATH_INTEGRAL_SUBPATH_INTEGRAL THEN
      ASM_SIMP_TAC[ENDS_IN_UNIT_INTERVAL; PATH_INTEGRABLE_INVERSEDIFF] THEN
      ASM_MESON_TAC[IN_INTERVAL_1];
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC WINDING_NUMBER_VALID_PATH THEN
      ASM_MESON_TAC[VALID_PATH_SUBPATH; SUBSET; VALID_PATH_IMP_PATH;
                 ENDS_IN_UNIT_INTERVAL; PATH_IMAGE_SUBPATH_SUBSET]];
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_CMUL THEN
    MATCH_MP_TAC INDEFINITE_INTEGRAL_CONTINUOUS_RIGHT THEN
    REWRITE_TAC[GSYM PATH_INTEGRABLE_ON] THEN
    ASM_SIMP_TAC[PATH_INTEGRABLE_INVERSEDIFF]]);;

let WINDING_NUMBER_IVT_POS = prove
 (`!g z w.
        valid_path g /\ ~(z IN path_image g) /\
        &0 <= w /\ w <= Re(winding_number(g,z))
        ==> ?t. t IN interval[vec 0,vec 1] /\
                Re(winding_number(subpath (vec 0) t g,z)) = w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RE_DEF] THEN
  MATCH_MP_TAC IVT_INCREASING_COMPONENT_ON_1 THEN
  ASM_SIMP_TAC[WINDING_NUMBER_SUBPATH_CONTINUOUS] THEN
  ASM_REWRITE_TAC[SUBPATH_TRIVIAL; GSYM RE_DEF; DIMINDEX_2; ARITH] THEN
  REWRITE_TAC[DROP_VEC; REAL_POS; SUBPATH_REFL] THEN
  MP_TAC(ISPECL [`(g:real^1->complex) (vec 0)`; `z:complex`]
        WINDING_NUMBER_TRIVIAL) THEN
  ASM_MESON_TAC[pathstart; PATHSTART_IN_PATH_IMAGE; RE_CX]);;

let WINDING_NUMBER_IVT_NEG = prove
 (`!g z w.
        valid_path g /\ ~(z IN path_image g) /\
        Re(winding_number(g,z)) <= w /\ w <= &0
        ==> ?t. t IN interval[vec 0,vec 1] /\
                Re(winding_number(subpath (vec 0) t g,z)) = w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RE_DEF] THEN
  MATCH_MP_TAC IVT_DECREASING_COMPONENT_ON_1 THEN
  ASM_SIMP_TAC[WINDING_NUMBER_SUBPATH_CONTINUOUS] THEN
  ASM_REWRITE_TAC[SUBPATH_TRIVIAL; GSYM RE_DEF; DIMINDEX_2; ARITH] THEN
  REWRITE_TAC[DROP_VEC; REAL_POS; SUBPATH_REFL] THEN
  MP_TAC(ISPECL [`(g:real^1->complex) (vec 0)`; `z:complex`]
        WINDING_NUMBER_TRIVIAL) THEN
  ASM_MESON_TAC[pathstart; PATHSTART_IN_PATH_IMAGE; RE_CX]);;

let WINDING_NUMBER_IVT_ABS = prove
 (`!g z w.
        valid_path g /\ ~(z IN path_image g) /\
        &0 <= w /\ w <= abs(Re(winding_number(g,z)))
        ==> ?t. t IN interval[vec 0,vec 1] /\
                abs(Re(winding_number(subpath (vec 0) t g,z))) = w`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `&0 <= Re(winding_number(g,z))` THEN
  ASM_REWRITE_TAC[real_abs] THEN REWRITE_TAC[GSYM real_abs] THEN
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`g:real^1->complex`; `z:complex`; `w:real`]
        WINDING_NUMBER_IVT_POS);
    MP_TAC(ISPECL [`g:real^1->complex`; `z:complex`; `--w:real`]
        WINDING_NUMBER_IVT_NEG)] THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[] THEN ASM_REAL_ARITH_TAC);;

let WINDING_NUMBER_LT_HALF = prove
 (`!g z a b.
        valid_path g /\ a dot z <= b /\ path_image g SUBSET {w | a dot w > b}
        ==> abs(Re(winding_number(g,z))) < &1 / &2`,
  let lemma = prove
   (`!g z a b.
          valid_path g /\ ~(z IN path_image g) /\
          a dot z <= b /\ path_image g SUBSET {w | a dot w > b}
          ==> Re(winding_number(g,z)) < &1 / &2`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`g:real^1->complex`; `z:complex`; `&1 / &2`]
      WINDING_NUMBER_IVT_POS) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
    X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`subpath (vec 0) t (g:real^1->complex)`; `z:complex`]
          WINDING_NUMBER_AHLFORS_FULL) THEN
    ASM_SIMP_TAC[VALID_PATH_SUBPATH; VALID_PATH_IMP_PATH;
                 ENDS_IN_UNIT_INTERVAL; NOT_IMP] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `~(z IN t) ==> s SUBSET t ==> ~(z IN s)`)) THEN
      ASM_SIMP_TAC[PATH_IMAGE_SUBPATH_SUBSET; ENDS_IN_UNIT_INTERVAL;
                   VALID_PATH_IMP_PATH];
      ASM_REWRITE_TAC[EULER; RE_MUL_CX; RE_MUL_II; IM_MUL_CX; IM_MUL_II] THEN
      REWRITE_TAC[REAL_ARITH `&2 * pi * &1 / &2 = pi`; SIN_PI; COS_PI] THEN
      REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_ADD_RID] THEN
      REWRITE_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
      REWRITE_TAC[COMPLEX_MUL_ASSOC; GSYM CX_MUL] THEN
      REWRITE_TAC[REAL_MUL_RNEG; REAL_MUL_RID; GSYM COMPLEX_CMUL] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `&0 < a dot ((g:real^1->complex) t - z) /\
                    &0 < a dot (g(vec 0) - z)`
      MP_TAC THENL
       [REWRITE_TAC[DOT_RSUB; REAL_SUB_LT] THEN CONJ_TAC THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `b:real` THEN
        ASM_REWRITE_TAC[GSYM real_gt] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `g SUBSET {z | a dot z > b} ==> t IN g ==> a dot t > b`)) THEN
        REWRITE_TAC[path_image] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL];
        ASM_REWRITE_TAC[DOT_RMUL] THEN
        DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
        ASM_SIMP_TAC[REAL_LT_MUL_EQ] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(&0 < -- x)`) THEN
        REWRITE_TAC[REAL_EXP_POS_LT]]]) in
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
  DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; REAL_ARITH `a:real > b <=> ~(a <= b)`] THEN
  DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH `x < a /\ --x < a ==> abs x < a`) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[lemma]; ALL_TAC] THEN
  MP_TAC(ISPECL [`reversepath g:real^1->complex`; `z:complex`;
                 `a:complex`; `b:real`] lemma) THEN
  ASM_SIMP_TAC[VALID_PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH;
               WINDING_NUMBER_REVERSEPATH; VALID_PATH_IMP_PATH; RE_NEG] THEN
  REAL_ARITH_TAC);;

let WINDING_NUMBER_LE_HALF = prove
 (`!g z a b.
        valid_path g /\ ~(z IN path_image g) /\
        ~(a = vec 0) /\ a dot z <= b /\ path_image g SUBSET {w | a dot w >= b}
        ==> abs(Re(winding_number(g,z))) <= &1 / &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g:real^1->complex`; `z:complex`]
   CONTINUOUS_AT_WINDING_NUMBER) THEN
  ASM_SIMP_TAC[VALID_PATH_IMP_PATH; continuous_at] THEN
  DISCH_THEN(MP_TAC o SPEC `abs(Re(winding_number(g,z))) - &1 / &2`) THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z - d / &2 / norm(a) % a:complex`) THEN
  REWRITE_TAC[NORM_ARITH `dist(z - d:complex,z) = norm d`] THEN
  ASM_SIMP_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM; REAL_DIV_RMUL;
               NORM_EQ_0; NOT_IMP] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH
    `abs(Re w' - Re w) <= norm(w' - w) /\ abs(Re w') < &1 / &2
     ==> ~(dist(w',w) < abs(Re w) - &1 / &2)`) THEN
  REWRITE_TAC[GSYM RE_SUB] THEN CONJ_TAC THENL
   [SIMP_TAC[COMPONENT_LE_NORM; RE_DEF; DIMINDEX_2; ARITH]; ALL_TAC] THEN
  MATCH_MP_TAC WINDING_NUMBER_LT_HALF THEN EXISTS_TAC `a:complex` THEN
  EXISTS_TAC `b - d / &3 * norm(a:complex)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[DOT_RSUB; DOT_RMUL; GSYM NORM_POW_2] THEN
    ASM_SIMP_TAC[NORM_EQ_0; REAL_FIELD
     `~(a = &0) ==> x / a * a pow 2 = x * a`] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `a:real <= b ==> d <= e ==> a - e <= b - d`)) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        SUBSET_TRANS)) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MATCH_MP_TAC(REAL_ARITH
     `&0 < e ==> !x. a dot x >= b ==> a dot x > b - e`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[NORM_POS_LT] THEN
    ASM_REAL_ARITH_TAC]);;

let WINDING_NUMBER_LT_HALF_LINEPATH = prove
 (`!a b z.
        ~(z IN segment[a,b])
        ==> abs(Re(winding_number(linepath(a,b),z))) < &1 / &2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WINDING_NUMBER_LT_HALF THEN
  MP_TAC(ISPECL [`segment[a:complex,b]`; `z:complex`]
        SEPARATING_HYPERPLANE_CLOSED_POINT) THEN
  ASM_REWRITE_TAC[CONVEX_SEGMENT; CLOSED_SEGMENT] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  SIMP_TAC[VALID_PATH_LINEPATH; PATH_IMAGE_LINEPATH; SUBSET; IN_ELIM_THM;
           REAL_LT_IMP_LE]);;

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
(* Winding number for a triangle.                                            *)
(* ------------------------------------------------------------------------- *)

let WINDING_NUMBER_TRIANGLE = prove
 (`!a b c z.
        z IN interior(convex hull {a,b,c})
        ==> winding_number(linepath(a,b) ++ linepath(b,c) ++ linepath(c,a),z) =
            if &0 < Im((b - a) * cnj (b - z)) then Cx(&1) else --Cx(&1)`,
  let lemma1 = prove
   (`!a b c. vec 0 IN interior(convex hull {a,b,c})
             ==> ~(Im(a / b) <= &0 /\ &0 <= Im(b / c))`,
    REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN SIMP_TAC[] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)
     [GSYM COMPLEX_INV_DIV] THEN
    REWRITE_TAC[IM_COMPLEX_INV_GE_0] THEN
    GEOM_BASIS_MULTIPLE_TAC 1 `b:complex` THEN
    REWRITE_TAC[COMPLEX_CMUL; COMPLEX_BASIS; GSYM CX_MUL; REAL_MUL_RID] THEN
    X_GEN_TAC `x:real` THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
    REWRITE_TAC[IM_DIV_CX] THEN ASM_CASES_TAC `x = &0` THEN
    ASM_REWRITE_TAC[NOT_IN_INTERIOR_CONVEX_HULL_3; COMPLEX_VEC_0] THEN
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO] THEN STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `!s. ~(x IN s) /\ t SUBSET s ==> ~(x IN t)`) THEN
    EXISTS_TAC `interior {z | Im z <= &0}` THEN CONJ_TAC THENL
     [REWRITE_TAC[IM_DEF; INTERIOR_HALFSPACE_COMPONENT_LE] THEN
      REWRITE_TAC[GSYM COMPLEX_VEC_0; IN_ELIM_THM; VEC_COMPONENT] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_INTERIOR THEN MATCH_MP_TAC HULL_MINIMAL THEN
      REWRITE_TAC[CONVEX_HALFSPACE_IM_LE] THEN
      ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM] THEN
      REWRITE_TAC[IM_CX; REAL_LE_REFL]]) in
  let lemma2 = prove
   (`z IN interior(convex hull {a,b,c})
     ==>  &0 < Im((b - a) * cnj (b - z)) /\
          &0 < Im((c - b) * cnj (c - z)) /\
          &0 < Im((a - c) * cnj (a - z)) \/
          Im((b - a) * cnj (b - z)) < &0 /\
          &0 < Im((b - c) * cnj (b - z)) /\
          &0 < Im((a - b) * cnj (a - z)) /\
          &0 < Im((c - a) * cnj (c - z))`,
    GEOM_ORIGIN_TAC `z:complex` THEN
    REWRITE_TAC[VECTOR_SUB_RZERO; COMPLEX_SUB_RDISTRIB] THEN
    REWRITE_TAC[COMPLEX_MUL_CNJ; IM_SUB; GSYM CX_POW; IM_CX] THEN
    REWRITE_TAC[REAL_ARITH `&0 < &0 - x <=> x < &0`;
                REAL_ARITH `&0 - x < &0 <=> &0 < x`] THEN
    REWRITE_TAC[GSYM IM_COMPLEX_DIV_GT_0; GSYM IM_COMPLEX_DIV_LT_0] THEN
    REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM COMPLEX_INV_DIV] THEN
    REWRITE_TAC[IM_COMPLEX_INV_LT_0; IM_COMPLEX_INV_GT_0] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV o RAND_CONV)
     [GSYM COMPLEX_INV_DIV] THEN
    REWRITE_TAC[IM_COMPLEX_INV_LT_0] THEN
    MP_TAC(ISPECL [`a:complex`; `b:complex`; `c:complex`] lemma1) THEN
    MP_TAC(ISPECL [`b:complex`; `c:complex`; `a:complex`] lemma1) THEN
    MP_TAC(ISPECL [`c:complex`; `a:complex`; `b:complex`] lemma1) THEN
    POP_ASSUM MP_TAC THEN SIMP_TAC[INSERT_AC] THEN REAL_ARITH_TAC) in
  let lemma3 = prove
   (`!a b c z.
          z IN interior(convex hull {a,b,c}) /\
          &0 < Im((b - a) * cnj (b - z)) /\
          &0 < Im((c - b) * cnj (c - z)) /\
          &0 < Im((a - c) * cnj (a - z))
          ==> winding_number
               (linepath(a,b) ++ linepath(b,c) ++ linepath(c,a),z) = Cx(&1)`,
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC WINDING_NUMBER_EQ_1 THEN
    REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; CONJ_ASSOC;
                PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM CONJ_ASSOC] THEN
      REPEAT(MATCH_MP_TAC WINDING_NUMBER_JOIN_POS_COMBINED THEN
             REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN;
                         PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
             CONJ_TAC) THEN
      ASM_SIMP_TAC[WINDING_NUMBER_LINEPATH_POS_LT; VALID_PATH_LINEPATH] THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [INTERIOR_OF_TRIANGLE; IN_DIFF; IN_UNION; DE_MORGAN_THM]) THEN
      ASM_REWRITE_TAC[PATH_IMAGE_LINEPATH];
      RULE_ASSUM_TAC(REWRITE_RULE
         [INTERIOR_OF_TRIANGLE; IN_DIFF; IN_UNION; DE_MORGAN_THM]) THEN
      ASM_SIMP_TAC[WINDING_NUMBER_JOIN; PATH_IMAGE_JOIN; PATH_JOIN; IN_UNION;
             PATH_LINEPATH; PATHSTART_JOIN; PATHFINISH_JOIN; RE_ADD;
             PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
      MATCH_MP_TAC(REAL_ARITH
       `abs a < &1 / &2 /\ abs b < &1 / &2 /\ abs c < &1 / &2
        ==> a + b + c < &2`) THEN
      REPEAT CONJ_TAC THEN MATCH_MP_TAC WINDING_NUMBER_LT_HALF_LINEPATH THEN
      ASM_REWRITE_TAC[]]) in
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP lemma2) THEN
  ASM_SIMP_TAC[lemma3; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  SUBGOAL_THEN
   `winding_number
      (linepath(c,b) ++ linepath(b,a) ++ linepath(a,c),z) = Cx(&1)`
  MP_TAC THENL
   [MATCH_MP_TAC lemma3 THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[INSERT_AC];
    COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [INTERIOR_OF_TRIANGLE; IN_DIFF; IN_UNION; DE_MORGAN_THM]) THEN
  FIRST_ASSUM(ASSUME_TAC o ONCE_REWRITE_RULE[SEGMENT_SYM] o CONJUNCT2) THEN
  ASM_SIMP_TAC[WINDING_NUMBER_JOIN; PATH_IMAGE_JOIN; PATH_JOIN; IN_UNION;
         PATH_LINEPATH; PATHSTART_JOIN; PATHFINISH_JOIN; RE_ADD;
         PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
  ASM_SIMP_TAC[COMPLEX_NEG_ADD; GSYM WINDING_NUMBER_REVERSEPATH;
              PATH_IMAGE_LINEPATH; PATH_LINEPATH; REVERSEPATH_LINEPATH] THEN
  CONV_TAC COMPLEX_RING);;

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
(* Homotopy forms of Cauchy's theorem. The first two proofs are almost the   *)
(* same and could potentially be unified with a little more work.            *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_THEOREM_HOMOTOPIC_PATHS = prove
 (`!f g h s.
        open s /\ f holomorphic_on s /\
        valid_path g /\ valid_path h /\ homotopic_paths s g h
        ==> path_integral g f = path_integral h f`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o SYM o MATCH_MP HOMOTOPIC_PATHS_IMP_PATHSTART) THEN
  FIRST_ASSUM(ASSUME_TAC o SYM o MATCH_MP HOMOTOPIC_PATHS_IMP_PATHFINISH) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homotopic_paths]) THEN
  REWRITE_TAC[homotopic_with; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `k:real^(1,1)finite_sum->complex` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. t IN interval[vec 0:real^1,vec 1]
        ==> ?e. &0 < e /\
              !t1 t2. t1 IN interval[vec 0:real^1,vec 1] /\
                      t2 IN interval[vec 0,vec 1] /\
                      norm(t1 - t) < e /\ norm(t2 - t) < e
                   ==> ?d. &0 < d /\
                        !g1 g2. valid_path g1 /\ valid_path g2 /\
                                (!u. u IN interval[vec 0,vec 1]
                                     ==> norm(g1 u - k(pastecart t1 u)) < d /\
                                         norm(g2 u - k(pastecart t2 u)) < d) /\
                                pathstart g1 = pathstart g /\
                                pathfinish g1 = pathfinish g /\
                                pathstart g2 = pathstart g /\
                                pathfinish g2 = pathfinish g
                                ==> path_image g1 SUBSET s /\
                                    path_image g2 SUBSET s /\
                                    path_integral g2 f = path_integral g1 f`
  MP_TAC THENL
   [X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`s:complex->bool`; `\u. (k:real^(1,1)finite_sum->complex)(pastecart t u)`]
     PATH_INTEGRAL_NEARBY_ENDS) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM o_DEF] THEN
      REWRITE_TAC[path_image; path; IMAGE_o] THEN CONJ_TAC THENL
       [ALL_TAC; ASM SET_TAC[]] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ID;
               CONTINUOUS_ON_CONST] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC)] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          COMPACT_UNIFORMLY_CONTINUOUS)) THEN
    SIMP_TAC[COMPACT_PASTECART; COMPACT_INTERVAL] THEN
    REWRITE_TAC[uniformly_continuous_on] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &4`) THEN
    ASM_REWRITE_TAC[REAL_ARITH `&0 < e / &4 <=> &0 < e`] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN
    REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (MESON[]
     `(!t x t' x'. P t x t' x') ==> (!t t' u. P t u t' u)`)) THEN
    REWRITE_TAC[dist; NORM_PASTECART; PASTECART_SUB] THEN
    REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[TAUT `a /\ b /\ c /\ b /\ d <=> a /\ c /\ b /\ d`] THEN
    SIMP_TAC[REAL_ADD_RID; POW_2_SQRT; NORM_POS_LE] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`t1:real^1`; `t2:real^1`] THEN
    STRIP_TAC THEN EXISTS_TAC `e / &4` THEN
    ASM_REWRITE_TAC[REAL_ARITH `&0 < e / &4 <=> &0 < e`] THEN
    MAP_EVERY X_GEN_TAC [`g1:real^1->complex`; `g2:real^1->complex`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM
     (MP_TAC o SPECL [`g1:real^1->complex`; `g2:real^1->complex`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    X_GEN_TAC `u:real^1` THEN STRIP_TAC THEN
    ASM_MESON_TAC[NORM_ARITH
     `norm(g1 - k1) < e / &4 /\ norm(g2 - k2) < e / &4 /\
      norm(k1 - kt) < e / &4 /\ norm(k2 - kt) < e / &4
      ==> norm(g1 - kt) < e /\ norm(g2 - kt) < e`];
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[ SKOLEM_THM; LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `ee:real^1->real` THEN DISCH_THEN(LABEL_TAC "*") THEN
  MP_TAC(ISPEC `interval[vec 0:real^1,vec 1]` COMPACT_IMP_HEINE_BOREL) THEN
  REWRITE_TAC[COMPACT_INTERVAL] THEN
  DISCH_THEN(MP_TAC o SPEC
   `IMAGE (\t:real^1. ball(t,ee t / &3)) (interval[vec 0,vec 1])`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL; SUBSET] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[UNIONS_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `t:real^1` THEN
    ASM_SIMP_TAC[CENTRE_IN_BALL; REAL_ARITH `&0 < e / &3 <=> &0 < e`];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> b /\ a /\ c`] THEN
  REWRITE_TAC[CONJ_ASSOC; FINITE_SUBSET_IMAGE] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; MESON[]
   `(?f s. (P s /\ f = g s) /\ Q f) <=> ?s. P s /\ Q(g s)`] THEN
  REWRITE_TAC[UNIONS_IMAGE; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `k:real^1->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_CASES_TAC `k:real^1->bool = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY; GSYM NOT_EXISTS_THM; MEMBER_NOT_EMPTY] THEN
    REWRITE_TAC[INTERVAL_EQ_EMPTY_1; DROP_VEC] THEN REAL_ARITH_TAC;
    DISCH_THEN(LABEL_TAC "+")] THEN
  SUBGOAL_THEN `!i:real^1. i IN k ==> &0 < ee(i)`
  ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `e = inf(IMAGE (ee:real^1->real) k)` THEN
  MP_TAC(ISPEC `IMAGE (ee:real^1->real) k` INF_FINITE) THEN
  MP_TAC(ISPECL [`IMAGE (ee:real^1->real) k`; `&0`]
    REAL_LT_INF_FINITE) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
  DISCH_TAC THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  MP_TAC(ISPEC `e / &3` REAL_ARCH_INV) THEN
  ASM_REWRITE_TAC[REAL_ARITH `&0 < e / &3 <=> &0 < e`] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!n. n <= N
        ==> ?d. &0 < d /\
                !j. valid_path j /\
                    (!u. u IN interval [vec 0,vec 1]
                        ==> norm(j u - k(pastecart (lift(&n / &N)) u)) < d) /\
                    pathstart j = pathstart g /\
                    pathfinish j = pathfinish g
                    ==> path_image j SUBSET s /\
                        path_integral j f = path_integral g f`
  (MP_TAC o SPEC `N:num`) THENL
   [ALL_TAC;
    REWRITE_TAC[LE_REFL; LEFT_IMP_EXISTS_THM] THEN
    GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `h:real^1->complex`) THEN
    ASM_SIMP_TAC[REAL_DIV_REFL; REAL_OF_NUM_EQ; LIFT_NUM] THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN MESON_TAC[]] THEN
  INDUCT_TAC THENL
   [REMOVE_THEN "*" (MP_TAC o SPEC `vec 0:real^1`) THEN
    ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; LE_0; LIFT_NUM] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REPEAT(DISCH_THEN(MP_TAC o SPEC `vec 0:real^1`) THEN
           REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL]) THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:real^1->complex` THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
     [`g:real^1->complex`; `j:real^1->complex`]) THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN MESON_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `lift(&n / &N) IN interval[vec 0,vec 1] /\
                lift(&(SUC n) / &N) IN interval[vec 0,vec 1]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "+" (MP_TAC o SPEC `lift(&n / &N)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "1"))) THEN
  REMOVE_THEN "*" (MP_TAC o SPEC `t:real^1`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(MP_TAC o SPECL [`lift(&n / &N)`; `lift(&(SUC n) / &N)`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_BALL]) THEN
    MATCH_MP_TAC(NORM_ARITH
     `!e. norm(n' - n:real^N) < e / &3 /\ e <= ee
     ==> dist(t,n) < ee / &3 ==> norm(n - t) < ee /\ norm(n' - t) < ee`) THEN
    EXISTS_TAC `e:real` THEN
    REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB; LIFT_DROP] THEN
    REWRITE_TAC[real_div; GSYM REAL_SUB_RDISTRIB] THEN
    SIMP_TAC[REAL_OF_NUM_SUB; ARITH_RULE `n <= SUC n`] THEN
    REWRITE_TAC[ARITH_RULE `SUC n - n = 1`; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NUM] THEN
    ASM_SIMP_TAC[GSYM real_div];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d2:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `j:real^1->complex` THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\u:real^1. (k(pastecart (lift (&n / &N)) u):complex)`;
    `min d1 d2`] PATH_APPROX_VECTOR_POLYNOMIAL_FUNCTION) THEN
  ASM_SIMP_TAC[REAL_LT_MIN; REAL_ARITH `&0 < e / &4 <=> &0 < e`] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[path] THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ID;
             CONTINUOUS_ON_CONST] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `p:real^1->complex` STRIP_ASSUME_TAC)] THEN
  REMOVE_THEN "1" (MP_TAC o SPEC `p:real^1->complex`) THEN
  ASM_SIMP_TAC[VALID_PATH_VECTOR_POLYNOMIAL_FUNCTION] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:real^1->complex`; `j:real^1->complex`]) THEN
  ASM_SIMP_TAC[VALID_PATH_VECTOR_POLYNOMIAL_FUNCTION]);;

let CAUCHY_THEOREM_HOMOTOPIC_LOOPS = prove
 (`!f g h s.
        open s /\ f holomorphic_on s /\
        valid_path g /\ valid_path h /\ homotopic_loops s g h
        ==> path_integral g f = path_integral h f`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_LOOP) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homotopic_loops]) THEN
  REWRITE_TAC[homotopic_with; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `k:real^(1,1)finite_sum->complex` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. t IN interval[vec 0:real^1,vec 1]
        ==> ?e. &0 < e /\
              !t1 t2. t1 IN interval[vec 0:real^1,vec 1] /\
                      t2 IN interval[vec 0,vec 1] /\
                      norm(t1 - t) < e /\ norm(t2 - t) < e
                   ==> ?d. &0 < d /\
                        !g1 g2. valid_path g1 /\ valid_path g2 /\
                                (!u. u IN interval[vec 0,vec 1]
                                     ==> norm(g1 u - k(pastecart t1 u)) < d /\
                                         norm(g2 u - k(pastecart t2 u)) < d) /\
                                pathfinish g1 = pathstart g1 /\
                                pathfinish g2 = pathstart g2
                                ==> path_image g1 SUBSET s /\
                                    path_image g2 SUBSET s /\
                                    path_integral g2 f = path_integral g1 f`
  MP_TAC THENL
   [X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`s:complex->bool`; `\u. (k:real^(1,1)finite_sum->complex)(pastecart t u)`]
     PATH_INTEGRAL_NEARBY_LOOP) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM o_DEF] THEN
      REWRITE_TAC[path_image; path; IMAGE_o] THEN CONJ_TAC THENL
       [ALL_TAC; ASM SET_TAC[]] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ID;
               CONTINUOUS_ON_CONST] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC)] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          COMPACT_UNIFORMLY_CONTINUOUS)) THEN
    SIMP_TAC[COMPACT_PASTECART; COMPACT_INTERVAL] THEN
    REWRITE_TAC[uniformly_continuous_on] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &4`) THEN
    ASM_REWRITE_TAC[REAL_ARITH `&0 < e / &4 <=> &0 < e`] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN
    REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (MESON[]
     `(!t x t' x'. P t x t' x') ==> (!t t' u. P t u t' u)`)) THEN
    REWRITE_TAC[dist; NORM_PASTECART; PASTECART_SUB] THEN
    REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[TAUT `a /\ b /\ c /\ b /\ d <=> a /\ c /\ b /\ d`] THEN
    SIMP_TAC[REAL_ADD_RID; POW_2_SQRT; NORM_POS_LE] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`t1:real^1`; `t2:real^1`] THEN
    STRIP_TAC THEN EXISTS_TAC `e / &4` THEN
    ASM_REWRITE_TAC[REAL_ARITH `&0 < e / &4 <=> &0 < e`] THEN
    MAP_EVERY X_GEN_TAC [`g1:real^1->complex`; `g2:real^1->complex`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM
     (MP_TAC o SPECL [`g1:real^1->complex`; `g2:real^1->complex`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    X_GEN_TAC `u:real^1` THEN STRIP_TAC THEN
    ASM_MESON_TAC[NORM_ARITH
     `norm(g1 - k1) < e / &4 /\ norm(g2 - k2) < e / &4 /\
      norm(k1 - kt) < e / &4 /\ norm(k2 - kt) < e / &4
      ==> norm(g1 - kt) < e /\ norm(g2 - kt) < e`];
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[ SKOLEM_THM; LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `ee:real^1->real` THEN DISCH_THEN(LABEL_TAC "*") THEN
  MP_TAC(ISPEC `interval[vec 0:real^1,vec 1]` COMPACT_IMP_HEINE_BOREL) THEN
  REWRITE_TAC[COMPACT_INTERVAL] THEN
  DISCH_THEN(MP_TAC o SPEC
   `IMAGE (\t:real^1. ball(t,ee t / &3)) (interval[vec 0,vec 1])`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL; SUBSET] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[UNIONS_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `t:real^1` THEN
    ASM_SIMP_TAC[CENTRE_IN_BALL; REAL_ARITH `&0 < e / &3 <=> &0 < e`];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> b /\ a /\ c`] THEN
  REWRITE_TAC[CONJ_ASSOC; FINITE_SUBSET_IMAGE] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; MESON[]
   `(?f s. (P s /\ f = g s) /\ Q f) <=> ?s. P s /\ Q(g s)`] THEN
  REWRITE_TAC[UNIONS_IMAGE; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `k:real^1->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_CASES_TAC `k:real^1->bool = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY; GSYM NOT_EXISTS_THM; MEMBER_NOT_EMPTY] THEN
    REWRITE_TAC[INTERVAL_EQ_EMPTY_1; DROP_VEC] THEN REAL_ARITH_TAC;
    DISCH_THEN(LABEL_TAC "+")] THEN
  SUBGOAL_THEN `!i:real^1. i IN k ==> &0 < ee(i)`
  ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `e = inf(IMAGE (ee:real^1->real) k)` THEN
  MP_TAC(ISPEC `IMAGE (ee:real^1->real) k` INF_FINITE) THEN
  MP_TAC(ISPECL [`IMAGE (ee:real^1->real) k`; `&0`]
    REAL_LT_INF_FINITE) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
  DISCH_TAC THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  MP_TAC(ISPEC `e / &3` REAL_ARCH_INV) THEN
  ASM_REWRITE_TAC[REAL_ARITH `&0 < e / &3 <=> &0 < e`] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!n. n <= N
        ==> ?d. &0 < d /\
                !j. valid_path j /\
                    (!u. u IN interval [vec 0,vec 1]
                        ==> norm(j u - k(pastecart (lift(&n / &N)) u)) < d) /\
                    pathfinish j = pathstart j
                    ==> path_image j SUBSET s /\
                        path_integral j f = path_integral g f`
  (MP_TAC o SPEC `N:num`) THENL
   [ALL_TAC;
    REWRITE_TAC[LE_REFL; LEFT_IMP_EXISTS_THM] THEN
    GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `h:real^1->complex`) THEN
    ASM_SIMP_TAC[REAL_DIV_REFL; REAL_OF_NUM_EQ; LIFT_NUM] THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN MESON_TAC[]] THEN
  INDUCT_TAC THENL
   [REMOVE_THEN "*" (MP_TAC o SPEC `vec 0:real^1`) THEN
    ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; LE_0; LIFT_NUM] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REPEAT(DISCH_THEN(MP_TAC o SPEC `vec 0:real^1`) THEN
           REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL]) THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:real^1->complex` THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
     [`g:real^1->complex`; `j:real^1->complex`]) THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN MESON_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `lift(&n / &N) IN interval[vec 0,vec 1] /\
                lift(&(SUC n) / &N) IN interval[vec 0,vec 1]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "+" (MP_TAC o SPEC `lift(&n / &N)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "1"))) THEN
  REMOVE_THEN "*" (MP_TAC o SPEC `t:real^1`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(MP_TAC o SPECL [`lift(&n / &N)`; `lift(&(SUC n) / &N)`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_BALL]) THEN
    MATCH_MP_TAC(NORM_ARITH
     `!e. norm(n' - n:real^N) < e / &3 /\ e <= ee
     ==> dist(t,n) < ee / &3 ==> norm(n - t) < ee /\ norm(n' - t) < ee`) THEN
    EXISTS_TAC `e:real` THEN
    REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB; LIFT_DROP] THEN
    REWRITE_TAC[real_div; GSYM REAL_SUB_RDISTRIB] THEN
    SIMP_TAC[REAL_OF_NUM_SUB; ARITH_RULE `n <= SUC n`] THEN
    REWRITE_TAC[ARITH_RULE `SUC n - n = 1`; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NUM] THEN
    ASM_SIMP_TAC[GSYM real_div];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d2:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `j:real^1->complex` THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\u:real^1. (k(pastecart (lift (&n / &N)) u):complex)`;
    `min d1 d2`] PATH_APPROX_VECTOR_POLYNOMIAL_FUNCTION) THEN
  ASM_SIMP_TAC[REAL_LT_MIN; REAL_ARITH `&0 < e / &4 <=> &0 < e`] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[path] THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ID;
             CONTINUOUS_ON_CONST] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `p:real^1->complex` STRIP_ASSUME_TAC)] THEN
  REMOVE_THEN "1" (MP_TAC o SPEC `p:real^1->complex`) THEN
  ASM_SIMP_TAC[VALID_PATH_VECTOR_POLYNOMIAL_FUNCTION] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:real^1->complex`; `j:real^1->complex`]) THEN
  ASM_SIMP_TAC[VALID_PATH_VECTOR_POLYNOMIAL_FUNCTION]);;

let CAUCHY_THEOREM_NULL_HOMOTOPIC = prove
 (`!f g s a.
        open s /\ f holomorphic_on s /\ a IN s /\ valid_path g /\
        homotopic_loops s g (linepath(a,a))
        ==> (f has_path_integral Cx(&0)) g`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_SUBSET) THEN
  MATCH_MP_TAC
   (MESON[HAS_PATH_INTEGRAL_INTEGRAL; path_integrable_on; PATH_INTEGRAL_UNIQUE]
     `!p. f path_integrable_on g /\ (f has_path_integral y) p /\
          path_integral g f = path_integral p f
          ==> (f has_path_integral y) g`) THEN
  EXISTS_TAC `linepath(a:complex,a)` THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[PATH_INTEGRABLE_HOLOMORPHIC_SIMPLE];
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
    DISCH_THEN(MP_TAC o SPEC `a:complex`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC CAUCHY_THEOREM_CONVEX_SIMPLE THEN
    EXISTS_TAC `ball(a:complex,e)` THEN
    ASM_REWRITE_TAC[VALID_PATH_LINEPATH; CONVEX_BALL; PATH_IMAGE_LINEPATH;
                    PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    ASM_REWRITE_TAC[SEGMENT_REFL; SING_SUBSET; IN_BALL; CENTRE_IN_BALL] THEN
    ASM_MESON_TAC[HOLOMORPHIC_ON_SUBSET];
    MATCH_MP_TAC CAUCHY_THEOREM_HOMOTOPIC_LOOPS THEN
    EXISTS_TAC `s:complex->bool` THEN ASM_REWRITE_TAC[VALID_PATH_LINEPATH]]);;

let CAUCHY_THEOREM_SIMPLY_CONNECTED = prove
 (`!f g s. open s /\ simply_connected s /\ f holomorphic_on s /\
           valid_path g /\ path_image g SUBSET s /\ pathfinish g = pathstart g
           ==> (f has_path_integral Cx(&0)) g`,
  REWRITE_TAC[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_PATH] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CAUCHY_THEOREM_NULL_HOMOTOPIC THEN
  MAP_EVERY EXISTS_TAC [`s:complex->bool`; `pathstart g :complex`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; SUBSET];
    MATCH_MP_TAC HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS THEN
    ASM_SIMP_TAC[PATHFINISH_LINEPATH; VALID_PATH_IMP_PATH]]);;

(* ------------------------------------------------------------------------- *)
(* More winding number properties, including the fact that it's +-1 inside   *)
(* a simple closed curve.                                                    *)
(* ------------------------------------------------------------------------- *)

let WINDING_NUMBER_HOMOTOPIC_PATHS = prove
 (`!g h z. homotopic_paths ((:complex) DELETE z) g h
           ==> winding_number(g,z) = winding_number(h,z)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_PATHS_IMP_PATH) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_PATHS_IMP_SUBSET) THEN
  REWRITE_TAC[SET_RULE `s SUBSET UNIV DELETE z <=> ~(z IN s)`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^1->complex`; `(:complex) DELETE z`]
     HOMOTOPIC_NEARBY_PATHS) THEN
  ASM_SIMP_TAC[OPEN_DELETE; OPEN_UNIV; SET_RULE
   `s SUBSET UNIV DELETE z <=> ~(z IN s)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g:real^1->complex`; `z:complex`; `d:real`]
    WINDING_NUMBER) THEN ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^1->complex` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`h:real^1->complex`; `(:complex) DELETE z`]
     HOMOTOPIC_NEARBY_PATHS) THEN
  ASM_SIMP_TAC[OPEN_DELETE; OPEN_UNIV; SET_RULE
   `s SUBSET UNIV DELETE z <=> ~(z IN s)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`h:real^1->complex`; `z:complex`; `e:real`]
    WINDING_NUMBER) THEN ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^1->complex` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `path_integral p (\w. Cx(&1) / (w - z)) =
    path_integral q (\w. Cx(&1) / (w - z))`
  MP_TAC THENL
   [MATCH_MP_TAC CAUCHY_THEOREM_HOMOTOPIC_PATHS THEN
    EXISTS_TAC `(:complex) DELETE z` THEN
    ASM_SIMP_TAC[OPEN_DELETE; OPEN_UNIV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN
      SIMP_TAC[HOLOMORPHIC_ON_CONST; HOLOMORPHIC_ON_ID;
               HOLOMORPHIC_ON_SUB; IN_DELETE; COMPLEX_SUB_0];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC `g:real^1->complex` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[NORM_SUB; VALID_PATH_IMP_PATH];
      MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
      EXISTS_TAC `h:real^1->complex` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[NORM_SUB; VALID_PATH_IMP_PATH]];
    ASM_REWRITE_TAC[] THEN MP_TAC CX_2PII_NZ THEN CONV_TAC COMPLEX_RING]);;

let WINDING_NUMBER_HOMOTOPIC_LOOPS = prove
 (`!g h z. homotopic_loops ((:complex) DELETE z) g h
           ==> winding_number(g,z) = winding_number(h,z)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_PATH) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_LOOP) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_SUBSET) THEN
  REWRITE_TAC[SET_RULE `s SUBSET UNIV DELETE z <=> ~(z IN s)`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^1->complex`; `(:complex) DELETE z`]
     HOMOTOPIC_NEARBY_LOOPS) THEN
  ASM_SIMP_TAC[OPEN_DELETE; OPEN_UNIV; SET_RULE
   `s SUBSET UNIV DELETE z <=> ~(z IN s)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g:real^1->complex`; `z:complex`; `d:real`]
    WINDING_NUMBER) THEN ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^1->complex` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`h:real^1->complex`; `(:complex) DELETE z`]
     HOMOTOPIC_NEARBY_LOOPS) THEN
  ASM_SIMP_TAC[OPEN_DELETE; OPEN_UNIV; SET_RULE
   `s SUBSET UNIV DELETE z <=> ~(z IN s)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`h:real^1->complex`; `z:complex`; `e:real`]
    WINDING_NUMBER) THEN ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^1->complex` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `path_integral p (\w. Cx(&1) / (w - z)) =
    path_integral q (\w. Cx(&1) / (w - z))`
  MP_TAC THENL
   [MATCH_MP_TAC CAUCHY_THEOREM_HOMOTOPIC_LOOPS THEN
    EXISTS_TAC `(:complex) DELETE z` THEN
    ASM_SIMP_TAC[OPEN_DELETE; OPEN_UNIV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN
      SIMP_TAC[HOLOMORPHIC_ON_CONST; HOLOMORPHIC_ON_ID;
               HOLOMORPHIC_ON_SUB; IN_DELETE; COMPLEX_SUB_0];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `g:real^1->complex` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMOTOPIC_LOOPS_SYM] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[NORM_SUB; VALID_PATH_IMP_PATH];
      MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
      EXISTS_TAC `h:real^1->complex` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[NORM_SUB; VALID_PATH_IMP_PATH]];
    ASM_REWRITE_TAC[] THEN MP_TAC CX_2PII_NZ THEN CONV_TAC COMPLEX_RING]);;

let WINDING_NUMBER_PATHS_LINEAR_EQ = prove
 (`!g h z.
        path g /\ path h /\
        pathstart h = pathstart g /\
        pathfinish h = pathfinish g /\
        (!t. t IN interval[vec 0,vec 1] ==> ~(z IN segment[g t,h t]))
        ==> winding_number(h,z) = winding_number(g,z)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC WINDING_NUMBER_HOMOTOPIC_PATHS THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_LINEAR THEN ASM SET_TAC[]);;

let WINDING_NUMBER_LOOPS_LINEAR_EQ = prove
 (`!g h z.
        path g /\ path h /\
        pathfinish g = pathstart g /\
        pathfinish h = pathstart h /\
        (!t. t IN interval[vec 0,vec 1] ==> ~(z IN segment[g t,h t]))
        ==> winding_number(h,z) = winding_number(g,z)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC WINDING_NUMBER_HOMOTOPIC_LOOPS THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_LINEAR THEN ASM SET_TAC[]);;

let WINDING_NUMBER_NEARBY_PATHS_EQ = prove
 (`!g h z.
        path g /\ path h /\
        pathstart h = pathstart g /\
        pathfinish h = pathfinish g /\
        (!t. t IN interval[vec 0,vec 1] ==> norm(h t - g t) < norm(g t - z))
        ==> winding_number(h,z) = winding_number(g,z)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC WINDING_NUMBER_HOMOTOPIC_PATHS THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_NEARBY_EXPLICIT THEN ASM SET_TAC[]);;

let WINDING_NUMBER_NEARBY_LOOPS_EQ = prove
 (`!g h z.
        path g /\ path h /\
        pathfinish g = pathstart g /\
        pathfinish h = pathstart h /\
        (!t. t IN interval[vec 0,vec 1] ==> norm(h t - g t) < norm(g t - z))
        ==> winding_number(h,z) = winding_number(g,z)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC WINDING_NUMBER_HOMOTOPIC_LOOPS THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_NEARBY_EXPLICIT THEN ASM SET_TAC[]);;

let WINDING_NUMBER_SUBPATH_COMBINE = prove
 (`!g u v w z.
        path g /\ ~(z IN path_image g) /\
        u IN interval [vec 0,vec 1] /\
        v IN interval [vec 0,vec 1] /\
        w IN interval [vec 0,vec 1]
        ==> winding_number(subpath u v g,z) +
            winding_number(subpath v w g,z) =
            winding_number(subpath u w g,z)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `winding_number(subpath u v g ++ subpath v w g,z)` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC WINDING_NUMBER_JOIN THEN
    ASM_SIMP_TAC[PATH_SUBPATH; PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
    ASM_MESON_TAC[SUBSET; PATH_IMAGE_SUBPATH_SUBSET];
    MATCH_MP_TAC WINDING_NUMBER_HOMOTOPIC_PATHS THEN
    MATCH_MP_TAC HOMOTOPIC_JOIN_SUBPATHS THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let WINDING_NUMBER_STRONG = prove
 (`!g z e.
        path g /\ ~(z IN path_image g) /\ &0 < e
         ==> ?p. vector_polynomial_function p /\ valid_path p /\
                 ~(z IN path_image p) /\
                 pathstart p = pathstart g /\
                 pathfinish p = pathfinish g /\
                 (!t. t IN interval[vec 0,vec 1] ==> norm(g t - p t) < e) /\
                 path_integral p (\w. Cx(&1) / (w - z)) =
                 Cx(&2) * Cx(pi) * ii * winding_number(g,z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?d. &0 < d /\
       !t. t IN interval[vec 0,vec 1] ==> d <= norm((g:real^1->complex) t - z)`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `setdist({z:complex},path_image g)` THEN
    REWRITE_TAC[SETDIST_POS_LE; REAL_ARITH
     `&0 < x <=> &0 <= x /\ ~(x = &0)`] THEN
     ASM_SIMP_TAC[SETDIST_EQ_0_CLOSED_COMPACT; CLOSED_SING; COMPACT_PATH_IMAGE;
                  PATH_IMAGE_NONEMPTY] THEN
     CONJ_TAC THENL [ASM SET_TAC[]; REPEAT STRIP_TAC] THEN
     REWRITE_TAC[ONCE_REWRITE_RULE[DIST_SYM] (GSYM dist)] THEN
     MATCH_MP_TAC SETDIST_LE_DIST THEN REWRITE_TAC[path_image] THEN
     ASM SET_TAC[];
     MP_TAC(ISPECL [`g:real^1->complex`; `min d e`]
      PATH_APPROX_VECTOR_POLYNOMIAL_FUNCTION) THEN
     ASM_REWRITE_TAC[REAL_LT_MIN] THEN MATCH_MP_TAC MONO_EXISTS THEN
     X_GEN_TAC `p:real^1->complex` THEN STRIP_TAC THEN
     ONCE_REWRITE_TAC[NORM_SUB] THEN
     ASM_SIMP_TAC[VALID_PATH_VECTOR_POLYNOMIAL_FUNCTION] THEN
     MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
      [REWRITE_TAC[path_image; IN_IMAGE] THEN
       ASM_MESON_TAC[NORM_SUB; REAL_NOT_LT];
       DISCH_TAC THEN MATCH_MP_TAC(COMPLEX_FIELD
        `!w'. ~(a * b * c = Cx(&0)) /\ w' = w /\ w' = Cx(&1) / (a * b * c) * i
              ==> i = a * b * c * w`) THEN
       EXISTS_TAC `winding_number(p,z)` THEN
       REWRITE_TAC[CX_2PII_NZ] THEN CONJ_TAC THENL
        [MATCH_MP_TAC WINDING_NUMBER_NEARBY_PATHS_EQ; ALL_TAC] THEN
       ASM_SIMP_TAC[WINDING_NUMBER_VALID_PATH; VALID_PATH_IMP_PATH;
                    VALID_PATH_VECTOR_POLYNOMIAL_FUNCTION] THEN
       ASM_MESON_TAC[REAL_LTE_TRANS; NORM_SUB]]]);;

let WINDING_NUMBER_FROM_INNERPATH = prove
 (`!c1 c2 c a b z:complex d.
        ~(a = b) /\
        simple_path c1 /\ pathstart c1 = a /\ pathfinish c1 = b /\
        simple_path c2 /\ pathstart c2 = a /\ pathfinish c2 = b /\
        simple_path c /\ pathstart c = a /\ pathfinish c = b /\
        path_image c1 INTER path_image c2 = {a,b} /\
        path_image c1 INTER path_image c = {a,b} /\
        path_image c2 INTER path_image c = {a,b} /\
        ~(path_image c INTER inside(path_image c1 UNION path_image c2) = {}) /\
        z IN inside(path_image c1 UNION path_image c) /\
        winding_number(c1 ++ reversepath c,z) = d /\ ~(d = Cx(&0))
        ==> z IN inside(path_image c1 UNION path_image c2) /\
            winding_number(c1 ++ reversepath c2,z) = d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c1:real^1->complex`; `c2:real^1->complex`;
                 `c:real^1->complex`; `a:complex`; `b:complex`]
         SPLIT_INSIDE_SIMPLE_CLOSED_CURVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `winding_number(c1 ++ reversepath c,z) = d` THEN
  MP_TAC(ISPECL
   [`c ++ reversepath(c2:real^1->complex)`; `z:complex`]
   WINDING_NUMBER_ZERO_IN_OUTSIDE) THEN
  SUBGOAL_THEN
   `~((z:complex) IN path_image c) /\
    ~(z IN path_image c1) /\
    ~(z IN path_image c2)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `(path_image c1 UNION path_image c):complex->bool`
                 INSIDE_NO_OVERLAP) THEN
    MP_TAC(ISPEC `(path_image c1 UNION path_image c2):complex->bool`
                 INSIDE_NO_OVERLAP) THEN
    ASM SET_TAC[];
    ASM_SIMP_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATH_IMAGE_JOIN;
      PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH; PATH_IMAGE_REVERSEPATH;
      PATH_JOIN; PATH_REVERSEPATH; SIMPLE_PATH_IMP_PATH;
      WINDING_NUMBER_JOIN; WINDING_NUMBER_REVERSEPATH] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[OUTSIDE_INSIDE; IN_DIFF; IN_UNION; IN_UNIV] THEN
      ONCE_REWRITE_TAC[UNION_COMM] THEN ASM SET_TAC[];
      CONV_TAC COMPLEX_RING]]);;

let SIMPLE_CLOSED_PATH_WINDING_NUMBER_INSIDE = prove
 (`!g. simple_path g
       ==> (!z. z IN inside(path_image g) ==> winding_number(g,z) = Cx(&1)) \/
           (!z. z IN inside(path_image g) ==> winding_number(g,z) = --Cx(&1))`,
  let lemma1 = prove
   (`!p a e.
          &0 < e /\
          simple_path(p ++ linepath(a - e % basis 1,a + e % basis 1)) /\
          pathstart p = a + e % basis 1 /\ pathfinish p = a - e % basis 1 /\
          ball(a,e) INTER path_image p = {}
          ==> ?z. z IN inside(path_image
                         (p ++ linepath(a - e % basis 1,a + e % basis 1))) /\
                  norm(winding_number
                   (p ++ linepath(a - e % basis 1,a + e % basis 1),z)) = &1`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL
     [`p:real^1->complex`; `linepath(a - e % basis 1,a + e % basis 1)`]
     SIMPLE_PATH_JOIN_LOOP_EQ) THEN
    ASM_REWRITE_TAC[PATHFINISH_LINEPATH; PATHSTART_LINEPATH] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
      `(a:complex) IN frontier(inside
       (path_image(p ++ linepath(a - e % basis 1,a + e % basis 1))))`
    MP_TAC THENL
     [FIRST_ASSUM
       (MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] JORDAN_INSIDE_OUTSIDE)) THEN
      ASM_REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN;
                      PATHFINISH_LINEPATH] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_LINEPATH] THEN
      REWRITE_TAC[IN_UNION; PATH_IMAGE_LINEPATH] THEN DISJ2_TAC THEN
      REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `&1 / &2` THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[FRONTIER_STRADDLE] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:complex` STRIP_ASSUME_TAC o CONJUNCT1) THEN
    MP_TAC(ISPEC
     `path_image (p ++ linepath(a - e % basis 1:complex,a + e % basis 1))`
     INSIDE_NO_OVERLAP) THEN
    REWRITE_TAC[EXTENSION] THEN DISCH_THEN(MP_TAC o SPEC `c:complex`) THEN
    ASM_REWRITE_TAC[IN_INTER; NOT_IN_EMPTY] THEN
    ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_LINEPATH; PATH_IMAGE_LINEPATH] THEN
    REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SEGMENT_AS_BALL] THEN
    ASM_REWRITE_TAC[IN_INTER;
      VECTOR_ARITH `inv(&2) % ((a - e) + (a + e)):complex = a`;
      VECTOR_ARITH `(a + e) - (a - e):complex = &2 % e`] THEN
    ASM_SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_2; ARITH] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> (abs(&2) * abs e * &1) / &2 = e`] THEN
    ASM_SIMP_TAC[IN_CBALL; REAL_LT_IMP_LE] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `~collinear{a - e % basis 1,c:complex,a + e % basis 1}`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL
       [`a - e % basis 1:complex`; `a + e % basis  1:complex`; `c:complex`]
       COLLINEAR_3_AFFINE_HULL) THEN
      ASM_SIMP_TAC[VECTOR_ARITH `a - x:complex = a + x <=> x = vec 0`;
                   BASIS_NONZERO; DIMINDEX_2; ARITH; VECTOR_MUL_EQ_0;
                   REAL_LT_IMP_NZ] THEN
      REWRITE_TAC[INSERT_AC];
      ALL_TAC] THEN
    SUBGOAL_THEN
    `~(interior(convex hull {a - e % basis 1,c:complex,a + e % basis 1}) = {})`
    MP_TAC THENL
     [ASM_SIMP_TAC[INTERIOR_CONVEX_HULL_3_MINIMAL] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      REPEAT(ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN EXISTS_TAC `&1 / &3`) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o AP_TERM `norm:complex->real` o
      MATCH_MP WINDING_NUMBER_TRIANGLE) THEN
    REWRITE_TAC[] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
    REWRITE_TAC[NORM_NEG; COND_ID; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL
     [`linepath(a + e % basis 1:complex,a - e % basis 1)`;
      `p:real^1->complex`;
      `linepath(a + e % basis 1:complex,c) ++ linepath(c,a - e % basis 1)`;
      `a + e % basis 1:complex`; `a - e % basis 1:complex`;
      `z:complex`;
      `winding_number
        (linepath(a - e % basis 1,c) ++
         linepath(c,a + e % basis 1) ++
         linepath(a + e % basis 1,a - e % basis 1),
         z)`] WINDING_NUMBER_FROM_INNERPATH) THEN
    ASM_SIMP_TAC[SIMPLE_PATH_LINEPATH; PATHSTART_JOIN; PATHFINISH_JOIN;
             VECTOR_ARITH `a + x:complex = a - x <=> x = vec 0`;
             BASIS_NONZERO; DIMINDEX_2; ARITH; VECTOR_MUL_EQ_0;
             REAL_LT_IMP_NZ; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
             ARC_IMP_SIMPLE_PATH; PATH_IMAGE_JOIN; PATH_IMAGE_LINEPATH] THEN
    ANTS_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC(TAUT
       `(p ==> p') /\ (p /\ q ==> q') ==> p /\ q ==> p' /\ q'`) THEN
      CONJ_TAC THENL [MESON_TAC[UNION_COMM; SEGMENT_SYM]; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM)) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NORM_ARITH
       `norm(z:complex) = &1 ==> u = --z ==> norm u = &1`)) THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
       [GSYM REVERSEPATH_LINEPATH] THEN
      ASM_SIMP_TAC[GSYM REVERSEPATH_JOINPATHS; PATHSTART_LINEPATH] THEN
      ONCE_REWRITE_TAC[COMPLEX_RING `a:complex = --b <=> b = --a`] THEN
      MATCH_MP_TAC WINDING_NUMBER_REVERSEPATH THEN
      ASM_SIMP_TAC[PATH_JOIN; PATHSTART_LINEPATH; PATH_IMAGE_JOIN;
                   PATH_LINEPATH; ARC_IMP_PATH; PATH_IMAGE_LINEPATH] THEN
      ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ONCE_REWRITE_TAC[UNION_COMM] THEN
      ASM_MESON_TAC[INSIDE_NO_OVERLAP; IN_INTER; NOT_IN_EMPTY]] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ARC_IMP_SIMPLE_PATH THEN MATCH_MP_TAC ARC_JOIN THEN
      REWRITE_TAC[ARC_LINEPATH_EQ; PATHSTART_LINEPATH;
                  PATHFINISH_LINEPATH] THEN
      REPEAT(CONJ_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        RULE_ASSUM_TAC(REWRITE_RULE[INSERT_AC; COLLINEAR_2]) THEN
        FIRST_X_ASSUM CONTR_TAC;
        ALL_TAC]) THEN
      REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN
      MATCH_MP_TAC(SET_RULE `s = t ==> s SUBSET t`) THEN
      MATCH_MP_TAC INTER_SEGMENT THEN ASM_MESON_TAC[INSERT_AC];
      REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `b INTER p = {}
        ==> s SUBSET b /\ k SUBSET p
            ==> (s UNION k) INTER p = k`)) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_SEGMENT; IN_BALL] THEN
        REWRITE_TAC[VECTOR_ARITH
         `(&1 - u) % (a + e) + u % (a - e):complex =
          a + (&1 - &2 * u) % e`] THEN
        REPEAT STRIP_TAC THEN
        ASM_REWRITE_TAC[NORM_ARITH `dist(a:complex,a + e) = norm e`] THEN
        SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_2; ARITH] THEN
        MATCH_MP_TAC(REAL_ARITH
         `x * e < &1 * e /\ &0 < e ==> x * abs e * &1 < e`) THEN
        ASM_SIMP_TAC[REAL_LT_RMUL_EQ] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
        ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE]];
      MATCH_MP_TAC(SET_RULE
       `s INTER t1 = {a} /\ s INTER t2 = {b}
        ==> s INTER (t1 UNION t2) = {a,b}`) THEN
      CONJ_TAC THENL
       [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SEGMENT_SYM];
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SEGMENT_SYM]] THEN
      MATCH_MP_TAC INTER_SEGMENT THEN DISJ2_TAC THEN
      ASM_MESON_TAC[INSERT_AC];
      MATCH_MP_TAC(SET_RULE
       `s INTER t1 = {a} /\ s INTER t2 = {b}
        ==> s INTER (t1 UNION t2) = {a,b}`) THEN
      CONJ_TAC THENL [ONCE_REWRITE_TAC[SEGMENT_SYM]; ALL_TAC] THEN
      REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
      MATCH_MP_TAC(SET_RULE
       `b IN p /\ ~(c IN p) /\ p INTER s = {}
        ==> p INTER (s UNION {c,b}) = {b}`) THEN
      (CONJ_TAC THENL
        [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE];
         ASM_REWRITE_TAC[]]) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `b INTER p = {} ==> s SUBSET b ==> p INTER s = {}`)) THEN
      REWRITE_TAC[GSYM INTERIOR_CBALL] THEN
      MATCH_MP_TAC IN_INTERIOR_CLOSURE_CONVEX_SEGMENT THEN
      ASM_REWRITE_TAC[CONVEX_CBALL; INTERIOR_CBALL; IN_BALL] THEN
      MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
      REWRITE_TAC[IN_CBALL;
                  NORM_ARITH `dist(a:complex,a - e) = norm e`;
                  NORM_ARITH `dist(a:complex,a + e) = norm e`] THEN
      ASM_SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_2; ARITH] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `c:complex` THEN
      REWRITE_TAC[IN_INTER; ENDS_IN_SEGMENT; IN_UNION] THEN
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `c IN s ==> s = t ==> c IN t`)) THEN
      ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_LINEPATH] THEN
      REWRITE_TAC[UNION_COMM; PATH_IMAGE_LINEPATH; SEGMENT_SYM];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [GSYM
        INSIDE_OF_TRIANGLE]) THEN
      REWRITE_TAC[UNION_ACI; SEGMENT_SYM];
      ASM_SIMP_TAC[REVERSEPATH_JOINPATHS; PATHSTART_JOIN; PATHFINISH_JOIN;
           PATHSTART_LINEPATH; PATHFINISH_LINEPATH; REVERSEPATH_LINEPATH] THEN
      RULE_ASSUM_TAC(REWRITE_RULE
        [INTERIOR_OF_TRIANGLE; IN_DIFF; IN_UNION; DE_MORGAN_THM]) THEN
      ASM_SIMP_TAC[WINDING_NUMBER_JOIN; PATH_JOIN; PATH_LINEPATH;
          PATH_IMAGE_JOIN; IN_UNION; PATHSTART_JOIN; PATHFINISH_JOIN;
          PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
      CONV_TAC COMPLEX_RING;
      DISCH_THEN SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE LAND_CONV [COMPLEX_NORM_CX]) THEN
      REAL_ARITH_TAC]) in
  let lemma2 = prove
   (`!p a d e.
          &0 < d /\ &0 < e /\
          simple_path(p ++ linepath(a - d % basis 1,a + e % basis 1)) /\
          pathstart p = a + e % basis 1 /\ pathfinish p = a - d % basis 1
          ==> ?z. z IN inside(path_image
                         (p ++ linepath(a - d % basis 1,a + e % basis 1))) /\
                  norm(winding_number
                   (p ++ linepath(a - d % basis 1,a + e % basis 1),z)) = &1`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL
     [`p:real^1->complex`; `linepath(a - d % basis 1,a + e % basis 1)`]
     SIMPLE_PATH_JOIN_LOOP_EQ) THEN
    ASM_REWRITE_TAC[PATHFINISH_LINEPATH; PATHSTART_LINEPATH] THEN
    REWRITE_TAC[ARC_LINEPATH_EQ; PATH_IMAGE_LINEPATH] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~((a:complex) IN path_image p)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `p INTER s SUBSET {d,e}
        ==> a IN s /\ ~(d = a) /\ ~(e = a) ==> ~(a IN p)`)) THEN
      REWRITE_TAC[GSYM BETWEEN_IN_SEGMENT; between] THEN
      REWRITE_TAC[NORM_ARITH `dist(a - d:complex,a + e) = norm(d + e)`;
        NORM_ARITH `dist(a - d:complex,a) + dist(a,a + e) = norm(d) + norm(e)`;
        VECTOR_ARITH `a + e:complex = a <=> e = vec 0`;
        VECTOR_ARITH `a - d:complex = a <=> d = vec 0`] THEN
      SIMP_TAC[GSYM VECTOR_ADD_RDISTRIB; NORM_MUL; VECTOR_MUL_EQ_0] THEN
      ASM_SIMP_TAC[BASIS_NONZERO; NORM_BASIS; DIMINDEX_2; ARITH] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPEC `(:complex) DIFF path_image p` OPEN_CONTAINS_BALL) THEN
    ASM_SIMP_TAC[GSYM closed; CLOSED_ARC_IMAGE; IN_UNIV; IN_DIFF] THEN
    DISCH_THEN(MP_TAC o SPEC `a:complex`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SET_RULE `s SUBSET UNIV DIFF t <=> s INTER t = {}`] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `kde:real = min k (min d e) / &2` THEN
    SUBGOAL_THEN `&0 < kde /\ kde < k /\ kde < d /\ kde < e`
    STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL
     [`linepath(a + kde % basis 1,a + e % basis 1) ++ p ++
       linepath(a - d % basis 1,a - kde % basis 1)`;
      `a:complex`; `kde:real`] lemma1) THEN
    ASM_SIMP_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATH_IMAGE_JOIN;
      PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH;
      SIMPLE_PATH_JOIN_LOOP_EQ] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC ARC_JOIN THEN
        ASM_SIMP_TAC[ARC_JOIN_EQ; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                     PATHSTART_JOIN; PATHFINISH_JOIN; PATH_IMAGE_LINEPATH;
                     ARC_LINEPATH_EQ; PATH_IMAGE_JOIN] THEN
        REWRITE_TAC[VECTOR_ARITH `a + e:complex = a + d <=> e - d = vec 0`;
                  VECTOR_ARITH `a - d:complex = a - e <=> e - d = vec 0`] THEN
        REWRITE_TAC[GSYM VECTOR_SUB_RDISTRIB; VECTOR_MUL_EQ_0; REAL_SUB_0] THEN
        ASM_SIMP_TAC[BASIS_NONZERO; NORM_BASIS; DIMINDEX_2; ARITH] THEN
        ASM_SIMP_TAC[REAL_LT_IMP_NE] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `p INTER de SUBSET {e,d}
          ==> dk SUBSET de /\ ke SUBSET de /\ ~(e IN dk) /\ ~(d IN ke) /\
              ke INTER dk = {}
          ==> p INTER dk SUBSET {d} /\ ke INTER (p UNION dk) SUBSET {e}`)) THEN
        REWRITE_TAC[SUBSET_SEGMENT; ENDS_IN_SEGMENT] THEN
        REWRITE_TAC[GSYM BETWEEN_IN_SEGMENT; between] THEN
        REWRITE_TAC[NORM_ARITH `dist(a - d:complex,a + e) = norm(d + e) /\
                                dist(a + d,a - e) = norm(d + e) /\
                                dist(a - d,a - e) = norm(d - e) /\
                                dist(a + d,a + e) = norm(d - e)`] THEN
        REWRITE_TAC[GSYM VECTOR_ADD_RDISTRIB; GSYM VECTOR_SUB_RDISTRIB] THEN
        ASM_SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_2; ARITH] THEN
        REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
        REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; NOT_IN_EMPTY] THEN
        MATCH_MP_TAC(MESON[REAL_LT_ANTISYM]
         `!a:complex. (!x. x IN t ==> x$1 < a$1) /\ (!x. x IN s ==> a$1 < x$1)
                      ==> !x. ~(x IN s /\ x IN t)`) THEN
        EXISTS_TAC `a:complex` THEN
        SIMP_TAC[IN_SEGMENT; LEFT_IMP_EXISTS_THM] THEN
        SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT;
                 VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
        REWRITE_TAC[REAL_ARITH
         `(a < (&1 - u) * (a + x) + u * (a + y) <=>
           &0 < (&1 - u) * x + u * y) /\
          ((&1 - u) * (a - x) + u * (a - y) < a <=>
           &0 < (&1 - u) * x + u * y)`] THEN
        REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_MUL_RID] THEN
        REWRITE_TAC[REAL_ARITH `&0 < (&1 - u) * x + u * y <=>
                                (&1 - u) * --x + u * --y < &0`] THEN
        MATCH_MP_TAC REAL_CONVEX_BOUND_LT THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[ARC_LINEPATH_EQ; VECTOR_MUL_EQ_0;
                    VECTOR_ARITH `a - k:complex = a + k <=> k = vec 0`] THEN
        ASM_SIMP_TAC[REAL_LT_IMP_NZ; BASIS_NONZERO; DIMINDEX_2; ARITH];
        MATCH_MP_TAC(SET_RULE
          `kk INTER p = {} /\ kk INTER ke = {kp} /\ dk INTER kk = {kn}
           ==> (ke UNION p UNION dk) INTER kk SUBSET {kp,kn}`) THEN
        CONJ_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
           `b INTER p = {} ==> s SUBSET b ==> s INTER p = {}`)) THEN
          SIMP_TAC[SUBSET; IN_SEGMENT; IN_BALL; LEFT_IMP_EXISTS_THM] THEN
          REWRITE_TAC[VECTOR_ARITH
            `(&1 - u) % (a - d) + u % (a + d):complex = a - (&1 - &2 * u) % d`;
           NORM_ARITH `dist(a:complex,a - d) = norm d`] THEN
          REPEAT STRIP_TAC THEN
          SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_2; ARITH] THEN
          MATCH_MP_TAC(REAL_ARITH
           `&0 < kd /\ a * kd <= &1 * kd /\ kd < k
            ==> a * abs kd * &1 < k`) THEN
          ASM_SIMP_TAC[REAL_LE_RMUL_EQ] THEN ASM_REAL_ARITH_TAC;
          CONJ_TAC THEN MATCH_MP_TAC INTER_SEGMENT THEN DISJ1_TAC THEN
          REWRITE_TAC[GSYM BETWEEN_IN_SEGMENT; between] THEN
          REWRITE_TAC[NORM_ARITH `dist(a - d:complex,a + e) = norm(d + e) /\
                                  dist(a + d,a - e) = norm(d + e) /\
                                  dist(a - d,a - e) = norm(d - e) /\
                                  dist(a + d,a + e) = norm(d - e)`] THEN
          REWRITE_TAC[GSYM VECTOR_ADD_RDISTRIB; GSYM VECTOR_SUB_RDISTRIB] THEN
          ASM_SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_2; ARITH] THEN
          ASM_REAL_ARITH_TAC];
        REWRITE_TAC[UNION_OVER_INTER; EMPTY_UNION] THEN
        ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> b /\ a /\ c`] THEN CONJ_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
           `b INTER p = {} ==> c SUBSET b ==> c INTER p = {}`)) THEN
          MATCH_MP_TAC SUBSET_BALL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
          ALL_TAC] THEN
        REWRITE_TAC[SET_RULE `s INTER t = {} <=>
                              !x. x IN t ==> ~(x IN s)`] THEN
        SIMP_TAC[IN_SEGMENT; LEFT_IMP_EXISTS_THM; IN_BALL] THEN
        REWRITE_TAC[VECTOR_ARITH
        `(&1 - u) % (a - d) + u % (a - e):complex =
         a - ((&1 - u) % d + u % e) /\
         (&1 - u) % (a + d) + u % (a + e):complex =
         a + ((&1 - u) % d + u % e)`;
        NORM_ARITH
         `dist(a:complex,a + d) = norm d /\ dist(a,a - e) = norm e`] THEN
        REWRITE_TAC[VECTOR_MUL_ASSOC; GSYM VECTOR_ADD_RDISTRIB] THEN
        SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_2; ARITH] THEN
        REWRITE_TAC[REAL_NOT_LT; REAL_MUL_RID] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= abs y`) THEN
        REWRITE_TAC[REAL_ARITH
         `(k <= (&1 - u) * k + u * e <=> &0 <= u * (e - k)) /\
          (k <= (&1 - u) * d + u * k <=> &0 <= (&1 - u) * (d - k))`] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:complex` THEN
    MATCH_MP_TAC(TAUT
     `(p <=> p') /\ (p /\ p' ==> (q <=> q')) ==> p /\ q ==> p' /\ q'`) THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN AP_TERM_TAC THEN
      ONCE_REWRITE_TAC[SET_RULE
       `(c UNION p UNION a) UNION b = p UNION (a UNION b UNION c)`] THEN
      AP_TERM_TAC THEN
      W(MP_TAC o PART_MATCH (lhand o rand) UNION_SEGMENT o
         rand o lhand o snd) THEN
      REWRITE_TAC[GSYM BETWEEN_IN_SEGMENT; between;
                  NORM_ARITH `dist(a - d:complex,a + e) = norm(d + e)`;
                  NORM_ARITH `dist(a + d:complex,a + e) = norm(d - e)`] THEN
      ASM_SIMP_TAC[GSYM VECTOR_ADD_RDISTRIB; GSYM VECTOR_SUB_RDISTRIB;
                   NORM_MUL; NORM_BASIS; DIMINDEX_2; ARITH] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      MATCH_MP_TAC UNION_SEGMENT THEN
      REWRITE_TAC[GSYM BETWEEN_IN_SEGMENT; between;
                  NORM_ARITH `dist(a - d:complex,a + e) = norm(d + e)`;
                  NORM_ARITH `dist(a - d:complex,a - e) = norm(d - e)`] THEN
      ASM_SIMP_TAC[GSYM VECTOR_ADD_RDISTRIB; GSYM VECTOR_SUB_RDISTRIB;
                   NORM_MUL; NORM_BASIS; DIMINDEX_2; ARITH] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN (MP_TAC o MATCH_MP
     (MESON[INSIDE_NO_OVERLAP; IN_INTER; NOT_IN_EMPTY]
       `z IN inside s ==> ~(z IN s)`))) THEN
    REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[WINDING_NUMBER_JOIN; PATH_JOIN; ARC_IMP_PATH; PATH_LINEPATH;
      PATH_IMAGE_JOIN; IN_UNION; PATH_IMAGE_LINEPATH; PATHSTART_JOIN;
      PATHFINISH_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    MATCH_MP_TAC(COMPLEX_RING
     `d + k + e:complex = z ==> (e + p + d) + k = p + z`) THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `winding_number(linepath (a - d % basis 1:complex,a - kde % basis 1),z) +
      winding_number(linepath (a - kde % basis 1,a + e % basis 1),z)` THEN
    CONJ_TAC THENL [AP_TERM_TAC; ALL_TAC] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC WINDING_NUMBER_SPLIT_LINEPATH THEN
    ASM_REWRITE_TAC[] THENL
     [CONJ_TAC THENL
       [ALL_TAC;
        SUBGOAL_THEN
         `~(z IN segment[a - kde % basis 1:complex,a + kde % basis 1]) /\
          ~(z IN segment[a + kde % basis 1,a + e % basis 1])`
        MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC(SET_RULE
         `s UNION t = u ==> ~(z IN s) /\ ~(z IN t) ==> ~(z IN u)`) THEN
        MATCH_MP_TAC UNION_SEGMENT];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM BETWEEN_IN_SEGMENT; between] THEN
    REWRITE_TAC[NORM_ARITH `dist(a - d:complex,a + e) = norm(d + e)`;
                NORM_ARITH `dist(a - d:complex,a - e) = norm(d - e)`;
                NORM_ARITH `dist(a + d:complex,a + e) = norm(d - e)`] THEN
    ASM_SIMP_TAC[GSYM VECTOR_ADD_RDISTRIB; GSYM VECTOR_SUB_RDISTRIB; NORM_MUL;
                   NORM_BASIS; DIMINDEX_2; ARITH] THEN
    ASM_REAL_ARITH_TAC) in
  let lemma3 = prove
   (`!p:real^1->complex.
          simple_path p /\ pathfinish p = pathstart p
          ==> ?z. z IN inside(path_image p) /\ norm(winding_number(p,z)) = &1`,
    GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPEC `p:real^1->complex` JORDAN_INSIDE_OUTSIDE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `~(inside(path_image p):complex->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `a:complex`) THEN
    MP_TAC(ISPECL [`inside(path_image p):complex->bool`;
                   `a:complex`; `basis 1:complex`]
          RAY_TO_FRONTIER) THEN
    MP_TAC(ISPECL [`inside(path_image p):complex->bool`;
                   `a:complex`; `--basis 1:complex`]
          RAY_TO_FRONTIER) THEN
    ASM_SIMP_TAC[INTERIOR_OPEN; VECTOR_NEG_EQ_0; BASIS_NONZERO;
                 DIMINDEX_2; ARITH] THEN
    REWRITE_TAC[VECTOR_ARITH `a + d % --b:complex = a - d % b`] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `?t. t IN interval[vec 0,vec 1] /\
          (p:real^1->complex) t = a - d % basis 1`
    STRIP_ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[path_image; IN_IMAGE]) THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?q. simple_path q /\
          pathstart q:complex = a - d % basis 1 /\
          pathfinish q = a - d % basis 1 /\
          path_image q = path_image p /\
          (!z. z IN inside(path_image p)
               ==> winding_number(q,z) = winding_number(p,z))`
    MP_TAC THENL
     [EXISTS_TAC `shiftpath t (p:real^1->complex)` THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
      ASM_SIMP_TAC[PATHSTART_SHIFTPATH; PATHFINISH_SHIFTPATH; DROP_VEC;
                   SIMPLE_PATH_SHIFTPATH; PATH_IMAGE_SHIFTPATH] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC WINDING_NUMBER_SHIFTPATH THEN
      ASM_SIMP_TAC[SIMPLE_PATH_IMP_PATH] THEN
      ASM_MESON_TAC[INSIDE_NO_OVERLAP; IN_INTER; NOT_IN_EMPTY];
      DISCH_THEN(X_CHOOSE_THEN `q:real^1->complex` MP_TAC) THEN
      REPLICATE_TAC 3 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC[IMP_CONJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      SUBGOAL_THEN
       `?z. z IN inside(path_image q) /\ norm(winding_number(q,z)) = &1`
       (fun th -> MESON_TAC[th]) THEN
      POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev o
          filter (fun tm -> not(free_in `t:real^1` (concl tm) or
                                free_in `p:real^1->complex` (concl tm)))) THEN
      STRIP_TAC] THEN
    SUBGOAL_THEN
     `?t. t IN interval[vec 0,vec 1] /\
          (q:real^1->complex) t = a + e % basis 1`
    STRIP_ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[path_image; IN_IMAGE]) THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(a - d % basis 1:complex = a + e % basis 1)`
    ASSUME_TAC THENL
     [REWRITE_TAC[VECTOR_ARITH
       `a - d % l:complex = a + e % l <=> (e + d) % l = vec 0`] THEN
      SIMP_TAC[VECTOR_MUL_EQ_0; BASIS_NONZERO; DIMINDEX_2; ARITH] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
      `path_image q INTER segment[a - d % basis 1,a + e % basis 1] =
       {a - d % basis 1:complex,a + e % basis 1}`
    ASSUME_TAC THENL
     [REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
      MATCH_MP_TAC(SET_RULE
       `a IN p /\ b IN p /\ p INTER s = {}
        ==> p INTER (s UNION {a,b}) = {a,b}`) THEN
      CONJ_TAC THENL [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[path_image; IN_IMAGE]; ALL_TAC] THEN
      ASM_SIMP_TAC[PATH_IMAGE_SUBPATH_SUBSET; SIMPLE_PATH_IMP_PATH;
                   ENDS_IN_UNIT_INTERVAL] THEN
      REWRITE_TAC[SET_RULE `s INTER t = {} <=> !x. x IN t ==> ~(x IN s)`] THEN
      REWRITE_TAC[IN_SEGMENT; VECTOR_ARITH
       `(&1 - u) % (a - d % l) + u % (a + e % l):complex =
         a + (u * e - (&1 - u) * d) % l`] THEN
      X_GEN_TAC `y:complex` THEN
      DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON
       [INSIDE_NO_OVERLAP; IN_INTER; NOT_IN_EMPTY]
       `x IN inside s ==> ~(x IN s)`) THEN
      ASM_CASES_TAC `&0 <= k * e - (&1 - k) * d` THENL
       [ALL_TAC;
        ONCE_REWRITE_TAC[VECTOR_ARITH
         `a + (s - t) % l:complex = a - (t - s) % l`]] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[REAL_ARITH `~(&0 <= a - b) ==> &0 <= b - a`] THEN
      REWRITE_TAC[REAL_ARITH `k * e - (&1 - k) * d < e <=>
                              &0 < (&1 - k) * (d + e)`] THEN
      REWRITE_TAC[REAL_ARITH `(&1 - k) * d - k * e < d <=>
                              &0 < k * (d + e)`] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`subpath t (vec 0) (q:real^1->complex)`;
      `a:complex`; `d:real`; `e:real`] lemma2) THEN
    ASM_SIMP_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH;
                 PATH_IMAGE_JOIN; PATHSTART_LINEPATH] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[pathstart]] THEN
      MATCH_MP_TAC SIMPLE_PATH_JOIN_LOOP THEN
      ASM_REWRITE_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH;
                      PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
      ASM_REWRITE_TAC[ARC_LINEPATH_EQ] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC ARC_SIMPLE_PATH_SUBPATH THEN
        RULE_ASSUM_TAC(REWRITE_RULE[pathstart]) THEN
        ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL];
        RULE_ASSUM_TAC(REWRITE_RULE[pathstart]) THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `p INTER s = {a,b} ==> p' SUBSET p ==> p' INTER s SUBSET {b,a}`)) THEN
        ASM_SIMP_TAC[PATH_IMAGE_SUBPATH_SUBSET; SIMPLE_PATH_IMP_PATH;
                     ENDS_IN_UNIT_INTERVAL]];
      DISCH_THEN(X_CHOOSE_THEN `z:complex` STRIP_ASSUME_TAC)] THEN
    MP_TAC(ISPECL
     [`subpath (vec 0) t (q:real^1->complex)`;
      `subpath (vec 1) t (q:real^1->complex)`;
      `linepath(a - d % basis 1:complex,a + e % basis 1)`;
      `a - d % basis 1:complex`; `a + e % basis 1:complex`;
      `z:complex`;
      `--winding_number
          (subpath t (vec 0) q ++
           linepath (a - d % basis 1,a + e % basis 1),z)`]
      WINDING_NUMBER_FROM_INNERPATH) THEN
    ASM_REWRITE_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH;
                    PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    REWRITE_TAC[REVERSEPATH_SUBPATH; REVERSEPATH_LINEPATH] THEN
    SUBGOAL_THEN
     `path_image (subpath (vec 0) t q) UNION
      path_image (subpath (vec 1) t q) :complex->bool =
      path_image q`
    SUBST1_TAC THENL
     [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
      SIMP_TAC[DROP_VEC; PATH_IMAGE_SUBPATH] THEN
      ONCE_REWRITE_TAC[GSYM PATH_IMAGE_REVERSEPATH] THEN
      REWRITE_TAC[REVERSEPATH_SUBPATH] THEN
      SIMP_TAC[DROP_VEC; PATH_IMAGE_SUBPATH] THEN STRIP_TAC THEN
      REWRITE_TAC[GSYM IMAGE_UNION; PATH_IMAGE_REVERSEPATH] THEN
      SUBGOAL_THEN `interval[vec 0:real^1,t] UNION interval[t,vec 1] =
                    interval[vec 0,vec 1]`
        (fun th -> ASM_REWRITE_TAC[th; GSYM path_image]) THEN
      REWRITE_TAC[EXTENSION; IN_UNION; IN_INTERVAL_1; DROP_VEC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ANTS_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
      REPLICATE_TAC 2 (ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SIMPLE_PATH_SUBPATH THEN
        ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN ASM_MESON_TAC[];
        ALL_TAC]) THEN
      ASM_REWRITE_TAC[SIMPLE_PATH_LINEPATH_EQ; PATH_IMAGE_LINEPATH] THEN
      REPEAT CONJ_TAC THENL
       [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
        SIMP_TAC[DROP_VEC; PATH_IMAGE_SUBPATH] THEN
        ONCE_REWRITE_TAC[GSYM PATH_IMAGE_REVERSEPATH] THEN
        REWRITE_TAC[REVERSEPATH_SUBPATH] THEN
        SIMP_TAC[DROP_VEC; PATH_IMAGE_SUBPATH] THEN STRIP_TAC THEN
        MATCH_MP_TAC(SET_RULE
          `a IN s /\ a IN t /\ b IN s /\ b IN t /\
           (!x. x IN s ==> !y. y IN t ==> x = y ==> x = a \/ x = b)
           ==> s INTER t = {a,b}`) THEN
        REPEAT CONJ_TAC THENL
         [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^1` THEN
          ASM_REWRITE_TAC[ENDS_IN_INTERVAL; INTERVAL_EQ_EMPTY_1; DROP_VEC] THEN
          ASM_REAL_ARITH_TAC;
          REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 1:real^1` THEN
          ASM_REWRITE_TAC[ENDS_IN_INTERVAL; INTERVAL_EQ_EMPTY_1; DROP_VEC] THEN
          ASM_REAL_ARITH_TAC;
          REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `t:real^1` THEN
          ASM_REWRITE_TAC[ENDS_IN_INTERVAL; INTERVAL_EQ_EMPTY_1; DROP_VEC] THEN
          ASM_REAL_ARITH_TAC;
          REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `t:real^1` THEN
          ASM_REWRITE_TAC[ENDS_IN_INTERVAL; INTERVAL_EQ_EMPTY_1; DROP_VEC] THEN
          ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        REWRITE_TAC[FORALL_IN_IMAGE; IN_INTERVAL_1; DROP_VEC] THEN
        X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN
        X_GEN_TAC `u:real^1` THEN STRIP_TAC THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simple_path]) THEN
        DISCH_THEN(MP_TAC o SPECL [`s:real^1`; `u:real^1`] o CONJUNCT2) THEN
        ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN
          (REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC)) THEN
        ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `drop u = drop t` MP_TAC THENL
         [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[DROP_EQ]];
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `p INTER s = {a,b}
          ==> a IN q /\ b IN q /\ q SUBSET p ==> q INTER s = {a,b}`)) THEN
        ASM_SIMP_TAC[PATH_IMAGE_SUBPATH_SUBSET; SIMPLE_PATH_IMP_PATH;
                     ENDS_IN_UNIT_INTERVAL] THEN
        FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
        SIMP_TAC[DROP_VEC; PATH_IMAGE_SUBPATH] THEN STRIP_TAC THEN
        REWRITE_TAC[IN_IMAGE] THEN CONJ_TAC THENL
         [EXISTS_TAC `vec 0:real^1`; EXISTS_TAC `t:real^1`] THEN
        ASM_REWRITE_TAC[ENDS_IN_INTERVAL; INTERVAL_EQ_EMPTY_1; DROP_VEC] THEN
        ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `p INTER s = {a,b}
          ==> a IN q /\ b IN q /\ q SUBSET p ==> q INTER s = {a,b}`)) THEN
        ASM_SIMP_TAC[PATH_IMAGE_SUBPATH_SUBSET; SIMPLE_PATH_IMP_PATH;
                     ENDS_IN_UNIT_INTERVAL] THEN
        ONCE_REWRITE_TAC[GSYM PATH_IMAGE_REVERSEPATH] THEN
        REWRITE_TAC[REVERSEPATH_SUBPATH] THEN
        FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
        SIMP_TAC[DROP_VEC; PATH_IMAGE_SUBPATH] THEN STRIP_TAC THEN
        REWRITE_TAC[IN_IMAGE] THEN CONJ_TAC THENL
         [EXISTS_TAC `vec 1:real^1`; EXISTS_TAC `t:real^1`] THEN
        ASM_REWRITE_TAC[ENDS_IN_INTERVAL; INTERVAL_EQ_EMPTY_1; DROP_VEC] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `a:complex` THEN
        ASM_REWRITE_TAC[GSYM BETWEEN_IN_SEGMENT; between] THEN
        REWRITE_TAC[NORM_ARITH `dist(a - d:complex,a + e) = norm(d + e)`;
              NORM_ARITH `dist(a - d:complex,a) = norm(d)`;
              NORM_ARITH `dist(a:complex,a + e) = norm e`] THEN
        ASM_SIMP_TAC[GSYM VECTOR_ADD_RDISTRIB; NORM_MUL;
                 NORM_BASIS; DIMINDEX_2; ARITH] THEN
        ASM_REAL_ARITH_TAC;
        ONCE_REWRITE_TAC[GSYM PATH_IMAGE_REVERSEPATH] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[PATH_IMAGE_LINEPATH]) THEN
        ASM_REWRITE_TAC[REVERSEPATH_SUBPATH];
        W(MP_TAC o PART_MATCH (rand o rand) WINDING_NUMBER_REVERSEPATH o
          rand o snd) THEN
        ANTS_TAC THENL
         [ASM_SIMP_TAC[PATH_JOIN_EQ; PATH_IMAGE_JOIN; PATH_LINEPATH;
            SIMPLE_PATH_IMP_PATH; PATHSTART_LINEPATH; PATHFINISH_SUBPATH;
            PATH_SUBPATH; ENDS_IN_UNIT_INTERVAL] THEN
          ASM_MESON_TAC[INSIDE_NO_OVERLAP; IN_INTER; NOT_IN_EMPTY];
          DISCH_THEN(SUBST1_TAC o SYM) THEN
          ASM_SIMP_TAC[REVERSEPATH_JOINPATHS; REVERSEPATH_LINEPATH;
                       REVERSEPATH_SUBPATH; PATHFINISH_SUBPATH;
                       PATHSTART_LINEPATH] THEN
          MATCH_MP_TAC(MESON[COMPLEX_ADD_SYM]
           `winding_number(g ++ h,z) =
            winding_number(g,z) + winding_number(h,z) /\
            winding_number(h ++ g,z) =
            winding_number(h,z) + winding_number(g,z)
            ==> winding_number(g ++ h,z) =winding_number(h ++ g,z)`) THEN
          CONJ_TAC THEN MATCH_MP_TAC WINDING_NUMBER_JOIN THEN
          ASM_SIMP_TAC[PATH_LINEPATH; PATH_SUBPATH; PATH_SUBPATH;
                       SIMPLE_PATH_IMP_PATH; ENDS_IN_UNIT_INTERVAL;
                       PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                       PATHSTART_SUBPATH; PATHFINISH_SUBPATH]
          THENL [ALL_TAC; ONCE_REWRITE_TAC[CONJ_SYM]] THEN
          REWRITE_TAC[SET_RULE
           `~(z IN s) /\ ~(z IN t) <=> ~(z IN s UNION t)`] THEN
          ONCE_REWRITE_TAC[GSYM PATH_IMAGE_REVERSEPATH] THEN
          REWRITE_TAC[REVERSEPATH_LINEPATH; REVERSEPATH_SUBPATH] THEN
          ASM_MESON_TAC[INSIDE_NO_OVERLAP; IN_INTER; NOT_IN_EMPTY]];
        REWRITE_TAC[COMPLEX_NEG_EQ_0] THEN DISCH_THEN SUBST_ALL_TAC THEN
        RULE_ASSUM_TAC(REWRITE_RULE
         [COMPLEX_NORM_CX; REAL_OF_NUM_EQ; REAL_ABS_NUM; ARITH]) THEN
        FIRST_X_ASSUM CONTR_TAC];
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ONCE_REWRITE_TAC[COMPLEX_RING `a:complex = --b <=> --a = b`] THEN
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[NORM_NEG])] THEN
    EXISTS_TAC `z:complex` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `winding_number(subpath (vec 0) t q ++ subpath t (vec 1) q,z) =
      winding_number(subpath (vec 0) (vec 1) q,z)`
     (fun th -> ASM_MESON_TAC[th; SUBPATH_TRIVIAL]) THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `winding_number(subpath (vec 0) t q,z) +
                winding_number(subpath t (vec 1) q,z)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC WINDING_NUMBER_JOIN THEN
      ASM_SIMP_TAC[PATH_SUBPATH; ENDS_IN_UNIT_INTERVAL; SIMPLE_PATH_IMP_PATH;
                   PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
      SUBGOAL_THEN `~((z:complex) IN path_image q)` MP_TAC THENL
       [ASM_MESON_TAC[INSIDE_NO_OVERLAP; IN_INTER; NOT_IN_EMPTY];
        MATCH_MP_TAC(SET_RULE
          `s1 SUBSET s /\ s2 SUBSET s
           ==> ~(z IN s) ==> ~(z IN s1) /\ ~(z IN s2)`) THEN
        ASM_SIMP_TAC[PATH_IMAGE_SUBPATH_SUBSET; ENDS_IN_UNIT_INTERVAL;
                  SIMPLE_PATH_IMP_PATH]];
      MATCH_MP_TAC WINDING_NUMBER_SUBPATH_COMBINE THEN
      ASM_REWRITE_TAC[ENDS_IN_INTERVAL; GSYM IN_INTERVAL_1] THEN
      ASM_SIMP_TAC[UNIT_INTERVAL_NONEMPTY; SIMPLE_PATH_IMP_PATH] THEN
      ASM_MESON_TAC[INSIDE_NO_OVERLAP; IN_INTER; NOT_IN_EMPTY]]) in
  GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `pathfinish g:complex = pathstart g` THENL
   [ALL_TAC; ASM_MESON_TAC[INSIDE_SIMPLE_CURVE_IMP_CLOSED]] THEN
  MATCH_MP_TAC(MESON[]
   `(?k. !z. z IN s ==> f z = k) /\
    (?z. z IN s /\ (f z = a \/ f z = b))
    ==> (!z. z IN s ==> f z = a) \/ (!z. z IN s ==> f z = b)`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WINDING_NUMBER_CONSTANT THEN
    ASM_SIMP_TAC[INSIDE_NO_OVERLAP; SIMPLE_PATH_IMP_PATH] THEN
    ASM_SIMP_TAC[JORDAN_INSIDE_OUTSIDE];
    MP_TAC(SPEC `g:real^1->complex` lemma3) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:complex` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`g:real^1->complex`; `z:complex`]
      INTEGER_WINDING_NUMBER) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[SIMPLE_PATH_IMP_PATH] THEN
      ASM_MESON_TAC[INSIDE_NO_OVERLAP; IN_INTER; NOT_IN_EMPTY];
      SIMP_TAC[complex_integer; COMPLEX_EQ; IM_NEG; IM_CX] THEN
      SIMP_TAC[GSYM real; REAL_NORM; RE_NEG; RE_CX] THEN REAL_ARITH_TAC]]);;

let SIMPLE_CLOSED_PATH_ABS_WINDING_NUMBER_INSIDE = prove
 (`!g z. simple_path g /\ z IN inside(path_image g)
         ==> abs(Re(winding_number(g,z))) = &1`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP
    SIMPLE_CLOSED_PATH_WINDING_NUMBER_INSIDE) THEN
  ASM_SIMP_TAC[RE_NEG; RE_CX; REAL_ABS_NUM; REAL_ABS_NEG]);;

let SIMPLE_CLOSED_PATH_NORM_WINDING_NUMBER_INSIDE = prove
 (`!g z. simple_path g /\ z IN inside(path_image g)
         ==> norm(winding_number(g,z)) = &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `pathfinish g:complex = pathstart g` ASSUME_TAC THENL
   [ASM_MESON_TAC[INSIDE_SIMPLE_CURVE_IMP_CLOSED]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^1->complex`; `z:complex`]
      INTEGER_WINDING_NUMBER) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SIMPLE_PATH_IMP_PATH] THEN
    ASM_MESON_TAC[INSIDE_NO_OVERLAP; IN_INTER; NOT_IN_EMPTY];
    ASM_SIMP_TAC[complex_integer; GSYM real; REAL_NORM;
                 SIMPLE_CLOSED_PATH_ABS_WINDING_NUMBER_INSIDE]]);;

let SIMPLE_CLOSED_PATH_WINDING_NUMBER_CASES = prove
 (`!g z. simple_path g /\ pathfinish g = pathstart g /\ ~(z IN path_image g)
         ==> winding_number(g,z) IN {--Cx(&1),Cx(&0),Cx(&1)}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `path_image g:complex->bool` INSIDE_UNION_OUTSIDE) THEN
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNIV; IN_UNION] THEN
  DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[WINDING_NUMBER_ZERO_IN_OUTSIDE; SIMPLE_PATH_IMP_PATH] THEN
  ASM_MESON_TAC[SIMPLE_CLOSED_PATH_WINDING_NUMBER_INSIDE]);;

let SIMPLE_CLOSED_PATH_WINDING_NUMBER_POS = prove
 (`!g z. simple_path g /\ pathfinish g = pathstart g /\ ~(z IN path_image g) /\
         &0 < Re(winding_number(g,z))
         ==> winding_number(g,z) = Cx(&1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^1->complex`; `z:complex`]
      SIMPLE_CLOSED_PATH_WINDING_NUMBER_CASES) THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  STRIP_TAC THEN UNDISCH_TAC `&0 < Re(winding_number(g,z))` THEN
  ASM_REWRITE_TAC[RE_NEG; RE_CX] THEN REAL_ARITH_TAC);;

let SIMPLY_CONNECTED_IMP_WINDING_NUMBER_ZERO = prove
 (`!s g z. simply_connected s /\
           path g /\ path_image g SUBSET s /\
           pathfinish g = pathstart g /\ ~(z IN s)
           ==> winding_number(g,z) = Cx(&0)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `winding_number(linepath(pathstart g,pathstart g),z)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WINDING_NUMBER_HOMOTOPIC_PATHS THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_PATHS_NULL THEN
    EXISTS_TAC `pathstart(g:real^1->complex)` THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_SUBSET THEN
    EXISTS_TAC `s:complex->bool` THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [simply_connected]) THEN
    ASM_REWRITE_TAC[PATH_LINEPATH; PATHSTART_LINEPATH;
                    PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH; SEGMENT_REFL;
                    INSERT_SUBSET; EMPTY_SUBSET];
    MATCH_MP_TAC WINDING_NUMBER_TRIVIAL] THEN
  MP_TAC(ISPEC `g:real^1->complex` PATHSTART_IN_PATH_IMAGE) THEN
  ASM SET_TAC[]);;

let NO_BOUNDED_CONNECTED_COMPONENT_IMP_WINDING_NUMBER_ZERO = prove
 (`!s. ~(?z. ~(z IN s) /\ bounded(connected_component ((:complex) DIFF s) z))
       ==> !g z. path g /\ path_image g SUBSET s /\
                 pathfinish g = pathstart g /\ ~(z IN s)
                 ==> winding_number(g,z) = Cx(&0)`,
  REWRITE_TAC[NOT_EXISTS_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC WINDING_NUMBER_ZERO_IN_OUTSIDE THEN
  ASM_REWRITE_TAC[outside; IN_ELIM_THM] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN
  ASM_REWRITE_TAC[CONTRAPOS_THM] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] BOUNDED_SUBSET) THEN
  MATCH_MP_TAC CONNECTED_COMPONENT_MONO THEN ASM SET_TAC[]);;

let NO_BOUNDED_PATH_COMPONENT_IMP_WINDING_NUMBER_ZERO = prove
 (`!s. ~(?z. ~(z IN s) /\ bounded(path_component ((:complex) DIFF s) z))
       ==> !g z. path g /\ path_image g SUBSET s /\
                 pathfinish g = pathstart g /\ ~(z IN s)
                 ==> winding_number(g,z) = Cx(&0)`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC NO_BOUNDED_CONNECTED_COMPONENT_IMP_WINDING_NUMBER_ZERO THEN
  ASM_MESON_TAC[PATH_COMPONENT_SUBSET_CONNECTED_COMPONENT; BOUNDED_SUBSET]);;

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
  REWRITE_TAC[SIMPLE_PATH_CIRCLEPATH;
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
(* Uniform convergence of path integral when the derivative of the path is   *)
(* bounded, and in particular for the special case of a circle.              *)
(* ------------------------------------------------------------------------- *)

let PATH_INTEGRAL_UNIFORM_LIMIT = prove
 (`!net f B g l.
     ~(trivial_limit net) /\ valid_path g /\
     (!t. t IN interval[vec 0,vec 1]
          ==> norm(vector_derivative g (at t)) <= B) /\
     eventually (\n:A. (f n) path_integrable_on g) net /\
     (!e. &0 < e
          ==> eventually (\n. !x. x IN path_image g
                                  ==> norm(f n x - l x) < e) net)
     ==> l path_integrable_on g /\
         ((\n. path_integral g (f n)) --> path_integral g l) net`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REWRITE_TAC[path_integrable_on; HAS_PATH_INTEGRAL; GSYM integrable_on] THEN
    MATCH_MP_TAC INTEGRABLE_UNIFORM_LIMIT THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / (abs B + &1)`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < abs B + &1`] THEN
    UNDISCH_TAC `eventually (\n:A. (f n) path_integrable_on g) net` THEN
    REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
    DISCH_THEN(MP_TAC o MATCH_MP EVENTUALLY_HAPPENS) THEN
    ASM_REWRITE_TAC[path_image; path_integrable_on; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[HAS_PATH_INTEGRAL; GSYM integrable_on] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\x. f (a:A) (g x) * vector_derivative g (at x)` THEN
    ASM_REWRITE_TAC[GSYM COMPLEX_SUB_RDISTRIB] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `e / (abs B + &1) * B` THEN CONJ_TAC THENL
     [REWRITE_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[NORM_POS_LE] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      REWRITE_TAC[REAL_ARITH `e / x * B <= e <=> &0 <= e * (&1 - B / x)`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_SUB_LE; REAL_LE_LDIV_EQ;
                   REAL_ARITH `&0 < abs B + &1`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[LIM_NULL] THEN REWRITE_TAC[tendsto] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2 / (abs B + &1)`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < abs B + &1`; REAL_HALF] THEN
  UNDISCH_TAC `eventually (\n:A. (f n) path_integrable_on g) net` THEN
  REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  X_GEN_TAC `a:A` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[PATH_INTEGRAL_INTEGRAL; DIST_0; GSYM INTEGRAL_SUB;
               GSYM PATH_INTEGRABLE_ON; ETA_AX] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC
   `drop(integral (interval[vec 0,vec 1]) (\x:real^1. lift(e / &2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
    ASM_SIMP_TAC[INTEGRABLE_SUB; GSYM PATH_INTEGRABLE_ON; ETA_AX] THEN
    REWRITE_TAC[INTEGRABLE_CONST; GSYM COMPLEX_SUB_RDISTRIB; LIFT_DROP] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `e / &2 / (abs B + &1) * B` THEN CONJ_TAC THENL
     [REWRITE_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[NORM_POS_LE] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[IN_IMAGE; path_image] THEN ASM_MESON_TAC[];
      REWRITE_TAC[REAL_ARITH `e / x * B <= e <=> &0 <= e * (&1 - B / x)`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_SUB_LE; REAL_LE_LDIV_EQ;
                   REAL_ARITH `&0 < abs B + &1`] THEN
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[INTEGRAL_CONST; CONTENT_UNIT_1; VECTOR_MUL_LID; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC]);;

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
  MATCH_MP_TAC PATH_INTEGRAL_UNIFORM_LIMIT THEN EXISTS_TAC `&2 * pi * r` THEN
  ASM_SIMP_TAC[PI_POS; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[VALID_PATH_CIRCLEPATH; VECTOR_DERIVATIVE_CIRCLEPATH] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; COMPLEX_NORM_II] THEN
  REWRITE_TAC[REAL_ABS_NUM; REAL_ABS_PI; REAL_MUL_LID] THEN
  REWRITE_TAC[NORM_CEXP; RE_MUL_CX; RE_MUL_II; IM_CX] THEN
  REWRITE_TAC[REAL_NEG_0; REAL_MUL_RZERO; REAL_EXP_0; REAL_MUL_RID] THEN
  ASM_SIMP_TAC[real_abs; REAL_LE_REFL; REAL_LT_IMP_LE]);;

(* ------------------------------------------------------------------------- *)
(* General stepping result for derivative formulas.                          *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_NEXT_DERIVATIVE = prove
 (`!f' f g s k B.
     ~(k = 0) /\
     open s /\ valid_path g /\
     (!t. t IN interval[vec 0,vec 1]
          ==> norm(vector_derivative g (at t)) <= B) /\
     f' continuous_on path_image g /\
     (!w. w IN s DIFF path_image g
          ==> ((\u. f'(u) / (u - w) pow k) has_path_integral f w) g)
     ==> !w. w IN s DIFF path_image g
             ==> (\u. f'(u) / (u - w) pow (k + 1)) path_integrable_on g /\
                 (f has_complex_derivative
                  (Cx(&k) * path_integral g (\u. f'(u) / (u - w) pow (k + 1))))
                  (at w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `w:complex` THEN
  REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `s DIFF path_image(g:real^1->complex)`
        OPEN_CONTAINS_BALL) THEN
  ASM_SIMP_TAC[OPEN_DIFF; CLOSED_PATH_IMAGE; VALID_PATH_IMP_PATH] THEN
  DISCH_THEN(MP_TAC o SPEC `w:complex`) THEN
  ASM_REWRITE_TAC[IN_DIFF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`at(w:complex)`;
    `\u x:complex. f'(x) * (inv(x - u) pow k - inv(x - w) pow k) /
                   (u - w) / Cx(&k)`;
    `B:real`; `g:real^1->complex`;
    `\u. f'(u) / (u - w) pow (k + 1)`]
        PATH_INTEGRAL_UNIFORM_LIMIT) THEN
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
    ASM_REWRITE_TAC[IN_BALL; dist; VECTOR_SUB_REFL; NORM_0] THEN
    ASM_MESON_TAC[NORM_SUB]] THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_AT] THEN CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_AT] THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:complex` THEN
    REWRITE_TAC[dist] THEN STRIP_TAC THEN
    REWRITE_TAC[complex_div; COMPLEX_MUL_ASSOC] THEN
    REPEAT(MATCH_MP_TAC PATH_INTEGRABLE_COMPLEX_RMUL) THEN
    REWRITE_TAC[COMPLEX_SUB_LDISTRIB; COMPLEX_POW_INV; GSYM complex_div] THEN
    MATCH_MP_TAC PATH_INTEGRABLE_SUB THEN
    REWRITE_TAC[path_integrable_on] THEN CONJ_TAC THENL
     [EXISTS_TAC `(f:complex->complex) u`;
      EXISTS_TAC `(f:complex->complex) w`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    REWRITE_TAC[IN_BALL; dist; VECTOR_SUB_REFL; NORM_0] THEN
    ASM_MESON_TAC[NORM_SUB];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. &0 < e
     ==> eventually
         (\n. !x. x IN path_image g
                  ==> norm
                      ((inv (x - n) pow k - inv (x - w) pow k) /
                       (n - w) / Cx(&k) - inv(x - w) pow (k + 1)) <
                      e)
         (at w)`
  ASSUME_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `bounded(IMAGE (f':complex->complex) (path_image g))`
    MP_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_SIMP_TAC[COMPACT_VALID_PATH_IMAGE];
      ALL_TAC] THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / C:real`) THEN
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
      UNDISCH_TAC `ball(w:complex,d) SUBSET s DIFF path_image g` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `x:complex`) THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_BALL] THEN
      UNDISCH_TAC `norm(w - v:complex) < d / &2` THEN
      CONV_TAC NORM_ARITH] THEN
    GEN_TAC THEN X_GEN_TAC `y:complex` THEN
    REWRITE_TAC[IN_BALL; dist] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(y:complex = x)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `ball(w:complex,d) SUBSET s DIFF path_image g` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `x:complex`) THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_BALL; dist] THEN ASM_REAL_ARITH_TAC;
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
   [ASM_MESON_TAC[]; ALL_TAC] THEN
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
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `&0 <= r` THENL
   [ALL_TAC;
    GEN_TAC THEN REWRITE_TAC[IN_BALL] THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    UNDISCH_TAC `~(&0 <= r)` THEN CONV_TAC NORM_ARITH] THEN
  MP_TAC(ISPECL
   [`f:complex->complex`; `g:complex->complex`; `circlepath(z,r)`;
    `ball(z:complex,r)`; `k:num`; `&2 * pi * r`] CAUCHY_NEXT_DERIVATIVE) THEN
  ASM_REWRITE_TAC[OPEN_BALL; VALID_PATH_CIRCLEPATH] THEN
  SUBGOAL_THEN `ball(z,r) DIFF path_image(circlepath (z,r)) = ball(z,r)`
  SUBST1_TAC THENL
   [REWRITE_TAC[SET_RULE `s DIFF t = s <=> !x. x IN t ==> ~(x IN s)`] THEN
    ASM_SIMP_TAC[PATH_IMAGE_CIRCLEPATH; FORALL_IN_GSPEC; IN_BALL] THEN
    CONV_TAC NORM_ARITH;
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_DERIVATIVE_CIRCLEPATH] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; COMPLEX_NORM_II] THEN
    REWRITE_TAC[REAL_ABS_NUM; REAL_ABS_PI; REAL_MUL_LID] THEN
    REWRITE_TAC[NORM_CEXP; RE_MUL_CX; RE_MUL_II; IM_CX] THEN
    REWRITE_TAC[REAL_NEG_0; REAL_MUL_RZERO; REAL_EXP_0; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[real_abs; REAL_LE_REFL]]);;

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
(* Morera's theorem.                                                         *)
(* ------------------------------------------------------------------------- *)

let MORERA_LOCAL_TRIANGLE_GEN = prove
 (`!f s.
     (!z. z IN s
          ==> ?e a. &0 < e /\ z IN ball(a,e) /\ f continuous_on ball(a,e) /\
                    !b c. segment[b,c] SUBSET ball(a,e)
                           ==> path_integral (linepath(a,b)) f +
                               path_integral (linepath(b,c)) f +
                               path_integral (linepath(c,a)) f = Cx(&0))
     ==> f analytic_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[analytic_on] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`e:real`; `a:complex`] THEN STRIP_TAC THEN
  EXISTS_TAC `e - dist(a:complex,z)` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_BALL]) THEN NORM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN EXISTS_TAC `ball(a:complex,e)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_DERIVATIVE THEN REWRITE_TAC[OPEN_BALL] THEN
    MATCH_MP_TAC TRIANGLE_PATH_INTEGRALS_STARLIKE_PRIMITIVE THEN
    EXISTS_TAC `a:complex` THEN ASM_REWRITE_TAC[CENTRE_IN_BALL; OPEN_BALL] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_BALL] THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; CENTRE_IN_BALL];
    REWRITE_TAC[SUBSET; IN_BALL] THEN NORM_ARITH_TAC]);;

let MORERA_LOCAL_TRIANGLE = prove
 (`!f s. (!z. z IN s
              ==> ?t. open t /\ z IN t /\ f continuous_on t /\
                      !a b c. convex hull {a,b,c} SUBSET t
                              ==> path_integral (linepath(a,b)) f +
                                  path_integral (linepath(b,c)) f +
                                  path_integral (linepath(c,a)) f = Cx(&0))
         ==> f analytic_on s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC MORERA_LOCAL_TRIANGLE_GEN THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `t:complex->bool` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  EXISTS_TAC `z:complex` THEN ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:complex`; `w:complex`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM
   (MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] SUBSET_TRANS)) THEN
  MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_BALL] THEN
  ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; CENTRE_IN_BALL] THEN
  MP_TAC(ISPECL [`x:complex`; `w:complex`] ENDS_IN_SEGMENT) THEN
  ASM SET_TAC[]);;

let MORERA_TRIANGLE = prove
 (`!f s. open s /\ f continuous_on s /\
         (!a b c. convex hull {a,b,c} SUBSET s
                  ==> path_integral (linepath(a,b)) f +
                      path_integral (linepath(b,c)) f +
                      path_integral (linepath(c,a)) f = Cx(&0))
         ==> f analytic_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MORERA_LOCAL_TRIANGLE THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN EXISTS_TAC `s:complex->bool` THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Combining theorems for higher derivatives including Leibniz rule.         *)
(* ------------------------------------------------------------------------- *)

let HIGHER_COMPLEX_DERIVATIVE_EQ_ITER = prove
 (`!n. higher_complex_derivative n = ITER n complex_derivative`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC [FUN_EQ_THM; ITER; higher_complex_derivative]);;

let HIGHER_COMPLEX_DERIVATIVE_HIGHER_COMPLEX_DERIVATIVE = prove
 (`!f m n. higher_complex_derivative m (higher_complex_derivative n f) =
           higher_complex_derivative (m + n) f`,
  REWRITE_TAC[HIGHER_COMPLEX_DERIVATIVE_EQ_ITER; ITER_ADD]);;

let higher_complex_derivative_alt = prove
 (`(!f. higher_complex_derivative 0 f = f) /\
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
 (`!f s n z.
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
 (`!f n z.
     f analytic_on {z}
     ==> higher_complex_derivative n (\w. --(f w)) z =
         --(higher_complex_derivative n f z)`,
  REWRITE_TAC [ANALYTIC_AT] THEN
  MESON_TAC [HIGHER_COMPLEX_DERIVATIVE_NEG]);;

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
    ASM_SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_DIFF; FINITE_IMP_CLOSED;
                 OPEN_INTERIOR; GSYM complex_differentiable]]);;

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

let HOLOMORPHIC_FUN_EQ_CONST_ON_CONNECTED = prove
 (`!f s z.
        open s /\
        connected s /\
        f holomorphic_on s /\
        z IN s /\
        (!n. 0 < n ==> higher_complex_derivative n f z = Cx (&0))
        ==> !w. w IN s ==> f w = f z`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`\w. (f:complex->complex) w - f z`; `s:complex->bool`; `z:complex`]
   HOLOMORPHIC_FUN_EQ_0_ON_CONNECTED) THEN
  ASM_REWRITE_TAC[COMPLEX_SUB_0; RIGHT_IMP_FORALL_THM; IMP_IMP] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[HOLOMORPHIC_ON_SUB; HOLOMORPHIC_ON_CONST] THEN
  X_GEN_TAC `n:num` THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[higher_complex_derivative; COMPLEX_SUB_REFL] THEN
  MP_TAC(ISPECL
   [`f:complex->complex`; `(\w. f(z:complex)):complex->complex`;
    `s:complex->bool`; `n:num`; `z:complex`]
   HIGHER_COMPLEX_DERIVATIVE_SUB) THEN
  ASM_REWRITE_TAC[HOLOMORPHIC_ON_CONST] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[LE_1; HIGHER_COMPLEX_DERIVATIVE_CONST; COMPLEX_SUB_REFL]);;

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
(* General, homology form of Cauchy's theorem. Proof is based on Dixon's,    *)
(* as presented in Lang's "Complex Analysis" book.                           *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_INTEGRAL_FORMULA_GLOBAL = prove
 (`!f s g z.
        open s /\ f holomorphic_on s /\ z IN s /\
        valid_path g /\ pathfinish g = pathstart g /\
        path_image g SUBSET s DELETE z /\
        (!w. ~(w IN s) ==> winding_number(g,w) = Cx(&0))
        ==> ((\w. f(w) / (w - z)) has_path_integral
             (Cx(&2) * Cx(pi) * ii * winding_number(g,z) * f(z))) g`,
  MATCH_MP_TAC(MESON[]
   `((!f s g. vector_polynomial_function g ==> P f s g) ==> !f s g. P f s g) /\
    (!f s g. vector_polynomial_function g ==> P f s g)
    ==> !f s g. P f s g`) THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s DELETE (z:complex)`; `g:real^1->complex`]
      PATH_INTEGRAL_NEARBY_ENDS) THEN
    ASM_SIMP_TAC[VALID_PATH_IMP_PATH; OPEN_DELETE] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`g:real^1->complex`; `d:real`]
      PATH_APPROX_VECTOR_POLYNOMIAL_FUNCTION) THEN
    ASM_SIMP_TAC[VALID_PATH_IMP_PATH] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^1->complex` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`g:real^1->complex`; `p:real^1->complex`]) THEN
    ASM_SIMP_TAC[VECTOR_SUB_REFL; NORM_0;
                 VALID_PATH_VECTOR_POLYNOMIAL_FUNCTION] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
     [`f:complex->complex`; `s:complex->bool`; `p:real^1->complex`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN
    SUBGOAL_THEN
     `winding_number(p,z) = winding_number(g,z) /\
      !w. ~(w IN s) ==> winding_number(p,w) = winding_number(g,w)`
     (fun th -> SIMP_TAC[th])
    THENL
     [FIRST_X_ASSUM(K ALL_TAC o SPEC `z:complex`) THEN
      REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (SET_RULE
       `g SUBSET s DELETE z
        ==> ~(z IN g) /\ (!y. ~(y IN s) ==> ~(y IN g))`))) THEN
      ASM_SIMP_TAC[WINDING_NUMBER_VALID_PATH;
                   VALID_PATH_VECTOR_POLYNOMIAL_FUNCTION] THEN
      REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[complex_div; COMPLEX_MUL_LID] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_INV THEN
      SIMP_TAC[HOLOMORPHIC_ON_SUB; HOLOMORPHIC_ON_ID; HOLOMORPHIC_ON_CONST;
               IN_DELETE; COMPLEX_SUB_0] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[VALID_PATH_VECTOR_POLYNOMIAL_FUNCTION] THEN
    MATCH_MP_TAC(MESON[HAS_PATH_INTEGRAL_INTEGRAL; path_integrable_on;
                       PATH_INTEGRAL_UNIQUE]
     `f path_integrable_on g /\ path_integral p f = path_integral g f
      ==> (f has_path_integral y) p ==> (f has_path_integral y) g`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PATH_INTEGRABLE_HOLOMORPHIC_SIMPLE THEN
      EXISTS_TAC `s DELETE (z:complex)` THEN ASM_SIMP_TAC[OPEN_DELETE];
      FIRST_X_ASSUM MATCH_MP_TAC] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN
    SIMP_TAC[HOLOMORPHIC_ON_SUB; HOLOMORPHIC_ON_ID; HOLOMORPHIC_ON_CONST;
             IN_DELETE; COMPLEX_SUB_0] THEN
    ASM_MESON_TAC[HOLOMORPHIC_ON_SUBSET; DELETE_SUBSET];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`f:complex->complex`; `u:complex->bool`; `g:real^1->complex`] THEN
  DISCH_TAC THEN X_GEN_TAC `z:complex` THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `g':real^1->complex` STRIP_ASSUME_TAC o
      MATCH_MP HAS_VECTOR_DERIVATIVE_VECTOR_POLYNOMIAL_FUNCTION) THEN
  SUBGOAL_THEN
   `bounded(IMAGE (g':real^1->complex) (interval[vec 0,vec 1]))`
  MP_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    REWRITE_TAC[COMPACT_INTERVAL] THEN
    ASM_MESON_TAC[CONTINUOUS_VECTOR_POLYNOMIAL_FUNCTION;
                  CONTINUOUS_AT_IMP_CONTINUOUS_ON];
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC)] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP VALID_PATH_IMP_PATH) THEN
  MAP_EVERY ABBREV_TAC
   [`d = \z w. if w = z then complex_derivative f z
              else (f(w) - f(z)) / (w - z)`;
    `v = {w | ~(w IN path_image g) /\ winding_number(g,w) = Cx(&0)}`] THEN
  SUBGOAL_THEN `open(v:complex->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN MATCH_MP_TAC OPEN_WINDING_NUMBER_LEVELSETS THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `u UNION v = (:complex)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:complex. y IN u ==> (d y) holomorphic_on u` ASSUME_TAC THENL
   [X_GEN_TAC `y:complex` THEN STRIP_TAC THEN EXPAND_TAC "d" THEN
    MATCH_MP_TAC NO_ISOLATED_SINGULARITY THEN EXISTS_TAC `{y:complex}` THEN
    ASM_REWRITE_TAC[FINITE_SING] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT] THEN
      X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
      ASM_CASES_TAC `w:complex = y` THENL
       [UNDISCH_THEN `w:complex = y` SUBST_ALL_TAC THEN
        REWRITE_TAC[CONTINUOUS_AT] THEN
        MATCH_MP_TAC LIM_TRANSFORM_AWAY_AT THEN
        EXISTS_TAC `\w:complex. (f w - f y) / (w - y)` THEN SIMP_TAC[] THEN
        EXISTS_TAC `y + Cx(&1)` THEN
        CONJ_TAC THENL [CONV_TAC COMPLEX_RING; ALL_TAC] THEN
        REWRITE_TAC[GSYM HAS_COMPLEX_DERIVATIVE_AT] THEN
        REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
        ASM_MESON_TAC[HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT];
        MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT];
      ASM_SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_DELETE; IN_DELETE;
        SET_RULE `s DIFF {x} = s DELETE x`; GSYM complex_differentiable] THEN
      X_GEN_TAC `w:complex` THEN STRIP_TAC] THEN
     MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_TRANSFORM_AT THEN
     EXISTS_TAC `\w:complex. (f w - f y) / (w - y)` THEN
     EXISTS_TAC `dist(w:complex,y)` THEN ASM_SIMP_TAC[DIST_POS_LT] THEN
     (CONJ_TAC THENL [MESON_TAC[DIST_SYM; REAL_LT_REFL]; ALL_TAC]) THEN
     MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_DIV_AT THEN
     ASM_REWRITE_TAC[COMPLEX_SUB_0] THEN CONJ_TAC THEN
     MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_SUB THEN
     ASM_SIMP_TAC[ETA_AX; COMPLEX_DIFFERENTIABLE_CONST;
                  COMPLEX_DIFFERENTIABLE_ID] THEN
     ASM_MESON_TAC[HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT];
     ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. ~(y IN path_image g)
        ==> (\x. (f x - f y) / (x - y)) path_integrable_on g`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
    MATCH_MP_TAC PATH_INTEGRABLE_HOLOMORPHIC_SIMPLE THEN
    EXISTS_TAC `u DELETE (y:complex)` THEN ASM_SIMP_TAC[OPEN_DELETE] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN
    SIMP_TAC[IN_DELETE; COMPLEX_SUB_0] THEN
    CONJ_TAC THEN MATCH_MP_TAC HOLOMORPHIC_ON_SUB THEN
    ASM_REWRITE_TAC[HOLOMORPHIC_ON_CONST; HOLOMORPHIC_ON_ID] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
    EXISTS_TAC `u:complex->bool` THEN ASM_REWRITE_TAC[DELETE_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:complex. d y path_integrable_on g`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:complex` THEN
    ASM_CASES_TAC `(y:complex) IN path_image g` THENL
     [MATCH_MP_TAC PATH_INTEGRABLE_HOLOMORPHIC_SIMPLE THEN
      EXISTS_TAC `u:complex->bool` THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[];
      MATCH_MP_TAC PATH_INTEGRABLE_EQ THEN
      EXISTS_TAC `\x:complex. (f x - f y) / (x - y)` THEN
      ASM_SIMP_TAC[] THEN EXPAND_TAC "d" THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?h. (!z. z IN u ==> ((d z) has_path_integral h(z)) g) /\
        (!z. z IN v ==> ((\w. f(w) / (w - z)) has_path_integral h(z)) g)`
   (CHOOSE_THEN (CONJUNCTS_THEN2 (LABEL_TAC "u") (LABEL_TAC "v")))
  THENL
   [EXISTS_TAC `\z. if z IN u then path_integral g (d z)
                    else path_integral g (\w. f(w) / (w - z))` THEN
    SIMP_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `w:complex` THEN DISCH_TAC THENL
     [ASM_MESON_TAC[HAS_PATH_INTEGRAL_INTEGRAL]; ALL_TAC] THEN
    ASM_CASES_TAC `(w:complex) IN u` THEN ASM_REWRITE_TAC[] THENL
     [ALL_TAC;
      MATCH_MP_TAC HAS_PATH_INTEGRAL_INTEGRAL THEN
      MATCH_MP_TAC PATH_INTEGRABLE_HOLOMORPHIC_SIMPLE THEN
      EXISTS_TAC `u:complex->bool` THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN
        ASM_SIMP_TAC[COMPLEX_SUB_0; HOLOMORPHIC_ON_SUB; HOLOMORPHIC_ON_CONST;
                     HOLOMORPHIC_ON_ID] THEN
        ASM_MESON_TAC[];
        ASM SET_TAC[]]] THEN
    MATCH_MP_TAC HAS_PATH_INTEGRAL_EQ THEN
    EXISTS_TAC `\x:complex. (f x - f w) / (x - w) + f(w) / (x - w)` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:complex` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      SIMPLE_COMPLEX_ARITH_TAC;
      ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM COMPLEX_ADD_RID] THEN
    MATCH_MP_TAC HAS_PATH_INTEGRAL_ADD THEN
    UNDISCH_TAC `(w:complex) IN v` THEN EXPAND_TAC "v" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC(MESON[PATH_INTEGRAL_UNIQUE; HAS_PATH_INTEGRAL_INTEGRAL;
                   path_integrable_on; PATH_INTEGRAL_EQ; PATH_INTEGRABLE_EQ]
       `g path_integrable_on p /\
        (!x. x IN path_image p ==> f x = g x)
        ==> (f has_path_integral path_integral p g) p`) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "d" THEN ASM_MESON_TAC[];
      SUBGOAL_THEN
       `Cx(&0) = (f w) * Cx(&2) * Cx pi * ii * winding_number(g,w)`
      SUBST1_TAC THENL [ASM_REWRITE_TAC[COMPLEX_MUL_RZERO]; ALL_TAC] THEN
      ONCE_REWRITE_TAC[SIMPLE_COMPLEX_ARITH `x / y = x * Cx(&1) / y`] THEN
      MATCH_MP_TAC HAS_PATH_INTEGRAL_COMPLEX_LMUL THEN
      MATCH_MP_TAC HAS_PATH_INTEGRAL_WINDING_NUMBER THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. (h:complex->complex) z = Cx(&0)` ASSUME_TAC THENL
   [ALL_TAC;
    REMOVE_THEN "u" (MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "d" THEN REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `\w. (f w - f z) / (w - z)` o
     MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] HAS_PATH_INTEGRAL_EQ)) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`g:real^1->complex`; `z:complex`]
      HAS_PATH_INTEGRAL_WINDING_NUMBER) THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP HAS_PATH_INTEGRAL_COMPLEX_RMUL) THEN
    DISCH_THEN(MP_TAC o SPEC `(f:complex->complex) z`) THEN
    REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP HAS_PATH_INTEGRAL_ADD) THEN
    REWRITE_TAC[complex_div; COMPLEX_ADD_RID; COMPLEX_RING
     `(Cx(&1) * i) * fz + (fx - fz) * i = fx * i`] THEN
    REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC]] THEN
  UNDISCH_THEN `(z:complex) IN u` (K ALL_TAC) THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (SET_RULE
   `p SUBSET u DELETE z ==> p SUBSET u`)) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN STRIP_TAC THEN
  MATCH_MP_TAC LIOUVILLE_WEAK THEN
  MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `?t:complex->bool.
        compact t /\ path_image g SUBSET interior t /\ t SUBSET u`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN
       `?dd. &0 < dd /\
            {y + k | y IN path_image g /\ k IN ball(vec 0,dd)} SUBSET u`
      STRIP_ASSUME_TAC THENL
       [ASM_CASES_TAC `u = (:complex)` THENL
         [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01; SUBSET_UNIV];
          ALL_TAC] THEN
        MP_TAC(ISPECL [`path_image g:complex->bool`; `(:complex) DIFF u`]
          SEPARATE_COMPACT_CLOSED) THEN
        ASM_SIMP_TAC[COMPACT_PATH_IMAGE; GSYM OPEN_CLOSED] THEN
        ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `dd:real` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `dd / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
        MAP_EVERY X_GEN_TAC [`y:complex`; `k:complex`] THEN
        MATCH_MP_TAC(TAUT `(a /\ ~c ==> ~b) ==> a /\ b ==> c`) THEN
        STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`y:complex`; `y + k:complex`]) THEN
        ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; IN_BALL] THEN CONV_TAC NORM_ARITH;
        ALL_TAC] THEN
      EXISTS_TAC `{y + k:complex |
                   y IN path_image g /\ k IN cball(vec 0,dd / &2)}` THEN
      ASM_SIMP_TAC[COMPACT_SUMS; COMPACT_PATH_IMAGE; COMPACT_CBALL] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_INTERIOR; IN_ELIM_THM] THEN
        X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
        EXISTS_TAC `dd / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
        X_GEN_TAC `x:complex` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
        MAP_EVERY EXISTS_TAC [`y:complex`; `x - y:complex`] THEN
        ASM_REWRITE_TAC[IN_CBALL] THEN
        UNDISCH_TAC `dist(y:complex,x) < dd / &2` THEN CONV_TAC NORM_ARITH;
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `{x + y:real^N | x IN s /\ y IN t} SUBSET u
          ==> t' SUBSET t ==> {x + y | x IN s /\ y IN t'} SUBSET u`)) THEN
        REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN
        UNDISCH_TAC `&0 < dd` THEN CONV_TAC NORM_ARITH];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`interior t:complex->bool`; `g:real^1->complex`]
        PATH_INTEGRAL_BOUND_EXISTS) THEN
    ASM_REWRITE_TAC[OPEN_INTERIOR] THEN
    DISCH_THEN(X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `bounded(IMAGE (f:complex->complex) t)` MP_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_MESON_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON; CONTINUOUS_ON_SUBSET];
      REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `D:real` STRIP_ASSUME_TAC)] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS] THEN
    DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[LIM_AT_INFINITY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    EXISTS_TAC `(D * L) / (e / &2) + C:real` THEN REWRITE_TAC[real_ge] THEN
    X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
    REWRITE_TAC[dist; COMPLEX_SUB_RZERO] THEN
    SUBGOAL_THEN `h y = path_integral g (\w. f w / (w - y))` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "v" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
       [DISCH_TAC THEN
        UNDISCH_TAC `(D * L) / (e / &2) + C <= norm(y:complex)` THEN
        MATCH_MP_TAC(REAL_ARITH `&0 < d /\ x <= c ==> d + c <= x ==> F`) THEN
        ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV; REAL_HALF] THEN
        ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET];
        MATCH_MP_TAC WINDING_NUMBER_ZERO_OUTSIDE THEN
        EXISTS_TAC `cball(Cx(&0),C)` THEN
        ASM_REWRITE_TAC[CONVEX_CBALL; SUBSET; IN_CBALL; dist;
                        COMPLEX_SUB_LZERO; NORM_NEG] THEN
        CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]] THEN
        UNDISCH_TAC `(D * L) / (e / &2) + C <= norm(y:complex)` THEN
        MATCH_MP_TAC(REAL_ARITH `&0 < d ==> d + c <= x ==> ~(x <= c)`) THEN
        ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV; REAL_HALF]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `L * (e / &2 / L)` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_HALF] THEN
      ASM_REAL_ARITH_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN CONJ_TAC THENL
       [ASM_MESON_TAC[HOLOMORPHIC_ON_SUBSET; SUBSET_TRANS; INTERIOR_SUBSET];
        SIMP_TAC[HOLOMORPHIC_ON_SUB; HOLOMORPHIC_ON_ID;
                 HOLOMORPHIC_ON_CONST; COMPLEX_SUB_0]] THEN
      X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NORM_ARITH
       `d + c <= norm y ==> &0 < d /\ norm w <= c ==> ~(w = y)`)) THEN
      ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV; REAL_HALF] THEN
      ASM_MESON_TAC[SUBSET; INTERIOR_SUBSET];
      ALL_TAC] THEN
    X_GEN_TAC `w:complex` THEN DISCH_TAC THEN SIMP_TAC[COMPLEX_NORM_DIV] THEN
    SUBGOAL_THEN `&0 < norm(w - y)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NORM_ARITH
       `d + c <= norm y ==> &0 < d /\ norm w <= c ==> &0 < norm(w - y)`)) THEN
      ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV; REAL_HALF] THEN
      ASM_MESON_TAC[SUBSET; INTERIOR_SUBSET];
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ]] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `D:real` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET; INTERIOR_SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `e / &2 / L * x = (x * (e / &2)) / L`] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; GSYM REAL_LE_LDIV_EQ; REAL_HALF] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NORM_ARITH
       `d + c <= norm y ==> norm w <= c ==> d <= norm(w - y)`)) THEN
    ASM_MESON_TAC[SUBSET; INTERIOR_SUBSET];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `(\y. (d:complex->complex->complex) (fstcart y) (sndcart y)) continuous_on
    {pastecart x z | x IN u /\ z IN u}`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN EXPAND_TAC "d" THEN
    REWRITE_TAC[FORALL_IN_GSPEC; continuous_within; IMP_CONJ] THEN
    MAP_EVERY X_GEN_TAC [`x:complex`; `z:complex`] THEN REPEAT DISCH_TAC THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; FORALL_PASTECART] THEN
    REWRITE_TAC[dist; IMP_IMP; GSYM CONJ_ASSOC; PASTECART_SUB] THEN
    ASM_CASES_TAC `z:complex = x` THEN ASM_REWRITE_TAC[] THENL
     [UNDISCH_THEN `z:complex = x` (SUBST_ALL_TAC o SYM);
      SUBGOAL_THEN
        `(\y. (f(sndcart y) - f(fstcart y)) / (sndcart y - fstcart y))
         continuous at (pastecart x z)`
      MP_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_COMPLEX_DIV_AT THEN
        ASM_SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART; COMPLEX_SUB_0] THEN
        CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_SUB THEN
        SIMP_TAC[LINEAR_CONTINUOUS_AT; LINEAR_FSTCART; LINEAR_SNDCART] THEN
        CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
        MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
        SIMP_TAC[LINEAR_CONTINUOUS_AT; LINEAR_FSTCART; LINEAR_SNDCART] THEN
        REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
        ASM_MESON_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON;
                      CONTINUOUS_ON_EQ_CONTINUOUS_AT];
        ALL_TAC] THEN
      REWRITE_TAC[continuous_at; dist; FORALL_PASTECART] THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_SUB] THEN
      DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `k1:real` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN
       `open({pastecart x z | x IN u /\ z IN u} DIFF
             {y | y IN UNIV /\ fstcart y - sndcart y = Cx(&0)})`
      MP_TAC THENL
       [MATCH_MP_TAC OPEN_DIFF THEN ASM_SIMP_TAC[OPEN_PASTECART] THEN
        MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_CONSTANT THEN
        REWRITE_TAC[CLOSED_UNIV] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART];
        SIMP_TAC[OPEN_CONTAINS_BALL; IN_DIFF; IMP_CONJ; FORALL_IN_GSPEC] THEN
        DISCH_THEN(MP_TAC o SPECL [`x:complex`; `z:complex`]) THEN
        ASM_REWRITE_TAC[IN_ELIM_THM; IN_UNIV; COMPLEX_SUB_0] THEN
        ASM_REWRITE_TAC[SUBSET; IN_BALL; FORALL_PASTECART; IN_DIFF;
          IN_ELIM_PASTECART_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
        REWRITE_TAC[IN_ELIM_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
        REWRITE_TAC[ONCE_REWRITE_RULE[NORM_SUB] dist; PASTECART_SUB;
               FSTCART_PASTECART; SNDCART_PASTECART] THEN
        DISCH_THEN(X_CHOOSE_THEN `k2:real` STRIP_ASSUME_TAC)] THEN
      EXISTS_TAC `min k1 k2:real` THEN
      ASM_SIMP_TAC[REAL_LT_MIN; COMPLEX_NORM_NZ; COMPLEX_SUB_0]] THEN
    SUBGOAL_THEN `(complex_derivative f) continuous at z` MP_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_INTERIOR THEN
      EXISTS_TAC `u:complex->bool` THEN ASM_SIMP_TAC[INTERIOR_OPEN] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_IMP_CONTINUOUS_ON THEN
      MATCH_MP_TAC HOLOMORPHIC_COMPLEX_DERIVATIVE THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
      ASM_REWRITE_TAC[dist; REAL_HALF]] THEN
    DISCH_THEN(X_CHOOSE_THEN `k1:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `u:complex->bool` OPEN_CONTAINS_BALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `k2:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min k1 k2:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    MAP_EVERY X_GEN_TAC [`x':complex`; `z':complex`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x <= e / &2 ==> x < e`) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[NORM_LE_PASTECART; REAL_LET_TRANS; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `e / &2 = e / &2 / norm(z' - x') * norm(z' - x':complex)`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_EQ_0; VECTOR_SUB_EQ]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_PATH_INTEGRAL_BOUND_LINEPATH THEN
    EXISTS_TAC `\u. (complex_derivative f u - complex_derivative f z) /
                    (z' - x')` THEN
    ASM_SIMP_TAC[REAL_LE_DIV; NORM_POS_LE; REAL_LT_IMP_LE; REAL_HALF] THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[COMPLEX_FIELD
       `~(z:complex = x)
         ==> a / (z - x) - b = (a - b * (z - x)) / (z - x)`] THEN
      MATCH_MP_TAC HAS_PATH_INTEGRAL_COMPLEX_DIV THEN
      MATCH_MP_TAC HAS_PATH_INTEGRAL_SUB THEN
      REWRITE_TAC[HAS_PATH_INTEGRAL_CONST_LINEPATH] THEN
      MP_TAC(ISPECL [`f:complex->complex`; `complex_derivative f`;
                     `linepath(x':complex,z')`; `u:complex->bool`]
                PATH_INTEGRAL_PRIMITIVE) THEN
      REWRITE_TAC[ETA_AX; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[VALID_PATH_LINEPATH] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE;
                      GSYM HOLOMORPHIC_ON_DIFFERENTIABLE;
                      HAS_COMPLEX_DERIVATIVE_AT_WITHIN; HOLOMORPHIC_ON_OPEN;
                      complex_differentiable];
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(z:complex,k2)`];
      X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
      REWRITE_TAC[COMPLEX_NORM_DIV; real_div] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[REAL_LE_INV_EQ; NORM_POS_LE] THEN
      MATCH_MP_TAC(REAL_ARITH `x < e / &2 ==> x <= e * inv(&2)`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[REWRITE_RULE[ONCE_REWRITE_RULE[NORM_SUB] dist]
       (GSYM IN_BALL)] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `w IN s ==> s SUBSET t ==> w IN t`))] THEN
    ASM_REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_CONVEX_HULL] THEN
    MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_BALL] THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_BALL; dist] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN
    ASM_MESON_TAC[NORM_LE_PASTECART; REAL_LET_TRANS];
    ALL_TAC] THEN
  SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_UNIV; IN_UNIV;
           GSYM complex_differentiable] THEN
  X_GEN_TAC `z0:complex` THEN ASM_CASES_TAC `(z0:complex) IN v` THENL
   [MP_TAC(ISPECL
    [`f:complex->complex`; `h:complex->complex`; `g:real^1->complex`;
     `v:complex->bool`; `1`; `B:real`]
        CAUCHY_NEXT_DERIVATIVE) THEN
    ASM_SIMP_TAC[IN_DIFF; ARITH_EQ; COMPLEX_POW_1] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[HAS_VECTOR_DERIVATIVE_UNIQUE_AT]; ALL_TAC] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_IMP_CONTINUOUS_ON THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
      EXISTS_TAC `u:complex->bool` THEN ASM SET_TAC[];
      DISCH_THEN(MP_TAC o SPEC `z0:complex`) THEN
      UNDISCH_TAC `(z0:complex) IN v` THEN EXPAND_TAC "v" THEN
      SIMP_TAC[IN_ELIM_THM; complex_differentiable] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z0:complex) IN u` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `u:complex->bool` OPEN_CONTAINS_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z0:complex`) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT THEN
  EXISTS_TAC `ball(z0:complex,e)` THEN
  ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
  MATCH_MP_TAC ANALYTIC_IMP_HOLOMORPHIC THEN MATCH_MP_TAC MORERA_TRIANGLE THEN
  REWRITE_TAC[OPEN_BALL] THEN
  SUBGOAL_THEN `(h:complex->complex) continuous_on u` ASSUME_TAC THENL
   [REWRITE_TAC[CONTINUOUS_ON_SEQUENTIALLY] THEN
    MAP_EVERY X_GEN_TAC [`a:num->complex`; `x:complex`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`sequentially`; `\n:num x. (d:complex->complex->complex) (a n) x`;
      `B:real`; `g:real^1->complex`; `(d:complex->complex->complex) x`]
      PATH_INTEGRAL_UNIFORM_LIMIT) THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; ETA_AX; EVENTUALLY_TRUE] THEN
    ANTS_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THEN
      REWRITE_TAC[FUN_EQ_THM; o_THM] THEN REPEAT GEN_TAC THEN
      MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[HAS_VECTOR_DERIVATIVE_UNIQUE_AT]; ALL_TAC] THEN
    X_GEN_TAC `ee:real` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `u:complex->bool` OPEN_CONTAINS_CBALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:complex`) THEN
    ASM_SIMP_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `dd:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `(\y. (d:complex->complex->complex) (fstcart y) (sndcart y))
      uniformly_continuous_on
      {pastecart w z | w IN cball(x,dd) /\ z IN path_image g}`
    MP_TAC THENL
     [MATCH_MP_TAC COMPACT_UNIFORMLY_CONTINUOUS THEN
      ASM_SIMP_TAC[COMPACT_PASTECART; COMPACT_CBALL;
                   COMPACT_VALID_PATH_IMAGE] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_ELIM_PASTECART_THM] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[uniformly_continuous_on] THEN
    DISCH_THEN(MP_TAC o SPEC `ee:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `kk:real`
      (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(MP_TAC o GENL [`w:complex`; `z:complex`] o
     SPECL [`pastecart (x:complex) (z:complex)`;
            `pastecart (w:complex) (z:complex)`]) THEN
    SIMP_TAC[IN_ELIM_PASTECART_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    ASM_SIMP_TAC[CENTRE_IN_CBALL; REAL_LT_IMP_LE; dist; PASTECART_SUB] THEN
    REWRITE_TAC[VECTOR_SUB_REFL; NORM_0; NORM_PASTECART] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[TAUT `b /\ (a /\ b) /\ c ==> d <=> a /\ b /\ c ==> d`] THEN
    SIMP_TAC[REAL_ADD_RID; POW_2_SQRT; NORM_POS_LE] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY]) THEN
    DISCH_THEN(MP_TAC o SPEC `min dd kk:real`) THEN
    ASM_REWRITE_TAC[EVENTUALLY_SEQUENTIALLY; REAL_LT_MIN] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[ONCE_REWRITE_RULE[DIST_SYM] IN_CBALL; GSYM dist;
                 REAL_LT_IMP_LE];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN

  SUBGOAL_THEN
   `!w. w IN u ==> (\z. d z w) holomorphic_on u`
  ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN X_GEN_TAC `y:complex` THEN STRIP_TAC THEN
    MATCH_MP_TAC NO_ISOLATED_SINGULARITY THEN EXISTS_TAC `{y:complex}` THEN
    ASM_REWRITE_TAC[FINITE_SING] THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `((\y. (d:complex->complex->complex) (fstcart y) (sndcart y)) o
        (\z. pastecart y z))
        continuous_on u`
      MP_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ID;
                 CONTINUOUS_ON_CONST] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_PASTECART_THM];
        EXPAND_TAC "d" THEN
        REWRITE_TAC[o_DEF; FSTCART_PASTECART; SNDCART_PASTECART] THEN
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_EQ) THEN
        GEN_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_TAC THEN REWRITE_TAC[complex_div] THEN MATCH_MP_TAC(COMPLEX_RING
         `x':complex = --x /\ y' = --y ==> x * y = x' * y'`) THEN
        REWRITE_TAC[GSYM COMPLEX_INV_NEG; COMPLEX_NEG_SUB]];
      ASM_SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_DELETE; IN_DELETE;
        SET_RULE `s DIFF {x} = s DELETE x`; GSYM complex_differentiable] THEN
      X_GEN_TAC `w:complex` THEN STRIP_TAC THEN
      MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_TRANSFORM_AT THEN
      EXISTS_TAC `\w:complex. (f y - f w) / (y - w)` THEN
      EXISTS_TAC `dist(w:complex,y)` THEN ASM_SIMP_TAC[DIST_POS_LT] THEN
      (CONJ_TAC THENL [MESON_TAC[DIST_SYM; REAL_LT_REFL]; ALL_TAC]) THEN
      MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_DIV_AT THEN
      ASM_REWRITE_TAC[COMPLEX_SUB_0] THEN CONJ_TAC THEN
      MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_SUB THEN
      ASM_SIMP_TAC[ETA_AX; COMPLEX_DIFFERENTIABLE_CONST;
                   COMPLEX_DIFFERENTIABLE_ID] THEN
      ASM_MESON_TAC[HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w a b:complex. w IN u /\ segment[a,b] SUBSET u
                    ==> (\z. d z w) path_integrable_on (linepath(a,b))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC PATH_INTEGRABLE_CONTINUOUS_LINEPATH THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; HOLOMORPHIC_ON_IMP_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b:complex.
        segment[a,b] SUBSET u
        ==> (\w. path_integral (linepath(a,b)) (\z. d z w))
            continuous_on u`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `a:complex = b` THENL
     [ASM_SIMP_TAC[PATH_INTEGRAL_TRIVIAL; CONTINUOUS_ON_CONST]; ALL_TAC] THEN
    REWRITE_TAC[continuous_on] THEN X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
    X_GEN_TAC `ee:real` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[dist; GSYM PATH_INTEGRAL_SUB] THEN
    MP_TAC(ISPEC `u:complex->bool` OPEN_CONTAINS_CBALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:complex`) THEN
    ASM_SIMP_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `dd:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `(\y. (d:complex->complex->complex) (fstcart y) (sndcart y))
      uniformly_continuous_on
      {pastecart z t | z IN segment[a,b] /\ t IN cball(w,dd)}`
    MP_TAC THENL
     [MATCH_MP_TAC COMPACT_UNIFORMLY_CONTINUOUS THEN
      ASM_SIMP_TAC[COMPACT_PASTECART; COMPACT_CBALL; COMPACT_SEGMENT] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_ELIM_PASTECART_THM] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[uniformly_continuous_on] THEN
    DISCH_THEN(MP_TAC o SPEC `ee / &2 / norm(b - a:complex)`) THEN
    ASM_SIMP_TAC[REAL_HALF; REAL_LT_DIV; COMPLEX_NORM_NZ; COMPLEX_SUB_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `kk:real`
      (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(MP_TAC o GENL [`z:complex`; `r:complex`] o
     SPECL [`pastecart (r:complex) (z:complex)`;
            `pastecart (r:complex) (w:complex)`]) THEN
    SIMP_TAC[IN_ELIM_PASTECART_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    ASM_SIMP_TAC[CENTRE_IN_CBALL; REAL_LT_IMP_LE; dist; PASTECART_SUB] THEN
    REWRITE_TAC[VECTOR_SUB_REFL; NORM_0; NORM_PASTECART] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[TAUT `(a /\ b) /\ a /\ c ==> d <=> a /\ b /\ c ==> d`] THEN
    SIMP_TAC[REAL_ADD_LID; POW_2_SQRT; NORM_POS_LE] THEN DISCH_TAC THEN
    EXISTS_TAC `min dd kk:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    X_GEN_TAC `x:complex` THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x <= e / &2 ==> x < e`) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `ee / &2 = ee / &2 / norm(b - a) * norm(b - a:complex)`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_EQ_0; VECTOR_SUB_EQ]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_PATH_INTEGRAL_BOUND_LINEPATH THEN
    EXISTS_TAC `\r. (d:complex->complex->complex) r x - d r w` THEN
    ASM_SIMP_TAC[REAL_LE_DIV; NORM_POS_LE; REAL_LT_IMP_LE; REAL_HALF] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HAS_PATH_INTEGRAL_INTEGRAL THEN
      MATCH_MP_TAC PATH_INTEGRABLE_SUB THEN ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [NORM_SUB] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_CBALL; dist] THEN
      ASM_MESON_TAC[NORM_SUB; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. segment[a,b] SUBSET u
          ==> (\w. path_integral (linepath (a,b)) (\z. d z w))
              path_integrable_on g`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[PATH_INTEGRABLE_ON] THEN
    MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `((\w. path_integral (linepath(a,b)) (\z. d z w)) o (g:real^1->complex))
        continuous_on interval[vec 0,vec 1]`
      MP_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        ASM_SIMP_TAC[GSYM path; VALID_PATH_IMP_PATH] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `u:complex->bool` THEN ASM_SIMP_TAC[GSYM path_image];
        REWRITE_TAC[o_DEF]];
      FIRST_ASSUM(fun th -> REWRITE_TAC
       [MATCH_MP HAS_VECTOR_DERIVATIVE_UNIQUE_AT (SPEC_ALL th)]) THEN
      ASM_SIMP_TAC[ETA_AX; GSYM path; VALID_PATH_IMP_PATH;
                   VALID_PATH_VECTOR_POLYNOMIAL_FUNCTION]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. segment[a,b] SUBSET u
          ==> path_integral (linepath(a,b)) h =
              path_integral g (\w. path_integral (linepath (a,b)) (\z. d z w))`
  ASSUME_TAC THENL
   [ALL_TAC;
    MAP_EVERY X_GEN_TAC [`a:complex`; `b:complex`; `c:complex`] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `segment[a:complex,b] SUBSET u /\
      segment[b,c] SUBSET u /\ segment[c,a] SUBSET u`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[SEGMENTS_SUBSET_CONVEX_HULL; SUBSET_TRANS]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    ASM_SIMP_TAC[GSYM PATH_INTEGRAL_ADD; PATH_INTEGRABLE_ADD] THEN
    MATCH_MP_TAC PATH_INTEGRAL_EQ_0 THEN
    X_GEN_TAC `w:complex` THEN REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:complex) IN u` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM PATH_INTEGRAL_JOIN; VALID_PATH_LINEPATH;
     VALID_PATH_JOIN; PATHSTART_JOIN;
     PATH_INTEGRABLE_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
    MATCH_MP_TAC CAUCHY_THEOREM_TRIANGLE THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN EXISTS_TAC `u:complex->bool` THEN
    ASM_SIMP_TAC[] THEN ASM SET_TAC[]] THEN
  MAP_EVERY X_GEN_TAC [`a:complex`; `b:complex`] THEN DISCH_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `path_integral (linepath(a,b)) (\z. path_integral g (d z))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PATH_INTEGRAL_EQ THEN
    REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET];
    MATCH_MP_TAC PATH_INTEGRAL_SWAP THEN
    REWRITE_TAC[VALID_PATH_LINEPATH; VECTOR_DERIVATIVE_LINEPATH_AT;
                CONTINUOUS_ON_CONST] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC
     [MATCH_MP HAS_VECTOR_DERIVATIVE_UNIQUE_AT (SPEC_ALL th)]) THEN
    ASM_SIMP_TAC[ETA_AX; CONTINUOUS_VECTOR_POLYNOMIAL_FUNCTION;
                 CONTINUOUS_AT_IMP_CONTINUOUS_ON] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_ELIM_PASTECART_THM] THEN
    REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN ASM SET_TAC[]]);;

let CAUCHY_THEOREM_GLOBAL = prove
 (`!f s g.
        open s /\ f holomorphic_on s /\
        valid_path g /\ pathfinish g = pathstart g /\ path_image g SUBSET s /\
        (!z. ~(z IN s) ==> winding_number(g,z) = Cx(&0))
        ==> (f has_path_integral Cx(&0)) g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?z:complex. z IN s /\ ~(z IN path_image g)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `t SUBSET s /\ ~(t = s) ==> ?z. z IN s /\ ~(z IN t)`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON
     [CLOPEN; COMPACT_EQ_BOUNDED_CLOSED; NOT_BOUNDED_UNIV]
     `open s /\ compact t /\ ~(t = {}) ==> ~(t = s)`) THEN
    ASM_SIMP_TAC[COMPACT_PATH_IMAGE; PATH_IMAGE_NONEMPTY; VALID_PATH_IMP_PATH];
    MP_TAC(ISPECL [`\w:complex. (w - z) * f(w)`; `s:complex->bool`;
                   `g:real^1->complex`; `z:complex`]
      CAUCHY_INTEGRAL_FORMULA_GLOBAL) THEN
    ASM_SIMP_TAC[COMPLEX_SUB_REFL; COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO;
                 HOLOMORPHIC_ON_MUL; HOLOMORPHIC_ON_SUB;
                 HOLOMORPHIC_ON_ID; HOLOMORPHIC_ON_CONST] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_PATH_INTEGRAL_EQ) THEN
    X_GEN_TAC `w:complex` THEN ASM_CASES_TAC `w:complex = z` THEN
    ASM_SIMP_TAC[COMPLEX_FIELD
     `~(w:complex = z) ==> ((w - z) * f) / (w - z) = f`]]);;

let CAUCHY_THEOREM_GLOBAL_OUTSIDE = prove
 (`!f s g.
        open s /\ f holomorphic_on s /\
        valid_path g /\ pathfinish g = pathstart g /\
        (!z. ~(z IN s) ==> z IN outside(path_image g))
        ==> (f has_path_integral Cx(&0)) g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CAUCHY_THEOREM_GLOBAL THEN
  EXISTS_TAC `s:complex->bool` THEN
  ASM_SIMP_TAC[WINDING_NUMBER_ZERO_IN_OUTSIDE; VALID_PATH_IMP_PATH] THEN
  MP_TAC(ISPEC `path_image(g:real^1->complex)` OUTSIDE_NO_OVERLAP) THEN
  ASM SET_TAC[]);;

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
  (`!f s z w.
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
        [MATCH_MP_TAC HOLOMORPHIC_HIGHER_COMPLEX_DERIVATIVE THEN
         ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN
         ASM_REWRITE_TAC [HOLOMORPHIC_ON_CONST];
         MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN
         ASM_REWRITE_TAC [HOLOMORPHIC_ON_CONST; ETA_AX] THEN
         MATCH_MP_TAC HOLOMORPHIC_HIGHER_COMPLEX_DERIVATIVE THEN
         ASM_REWRITE_TAC[]];
        MATCH_MP_TAC COMPLEX_DERIVATIVE_LMUL THEN
        MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT THEN
        ASM_MESON_TAC [HOLOMORPHIC_HIGHER_COMPLEX_DERIVATIVE]]];
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
(* Factoring out a zero according to its order.                              *)
(* ------------------------------------------------------------------------- *)

let HOLOMORPHIC_FACTOR_ORDER_OF_ZERO = prove
 (`!f s n.
      open s /\ z IN s /\ f holomorphic_on s /\
      0 < n /\ ~(higher_complex_derivative n f z = Cx(&0)) /\
      (!m. 0 < m /\ m < n ==> higher_complex_derivative m f z = Cx(&0))
      ==> ?g r. &0 < r /\
                g holomorphic_on ball(z,r) /\
                (!w. w IN ball(z,r) ==> f(w) - f(z) = (w - z) pow n * g(w)) /\
                (!w. w IN ball(z,r) ==> ~(g w = Cx(&0)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!w. w IN ball(z,r)
        ==> ((\m. higher_complex_derivative m f z / Cx(&(FACT m)) *
                  (w - z) pow m) sums f(w) - f(z)) (from n)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`f:complex->complex`; `z:complex`; `w:complex`; `r:real`]
        HOLOMORPHIC_POWER_SERIES) THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[HOLOMORPHIC_ON_SUBSET]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `1` o
      MATCH_MP (REWRITE_RULE[IMP_CONJ] SUMS_OFFSET)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[VSUM_SING_NUMSEG] THEN
    REWRITE_TAC[FACT; higher_complex_derivative; COMPLEX_DIV_1] THEN
    REWRITE_TAC[complex_pow; COMPLEX_MUL_RID] THEN
    ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `n:num` o
      MATCH_MP (REWRITE_RULE[IMP_CONJ] SUMS_OFFSET)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; MATCH_MP_TAC EQ_IMP] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC(COMPLEX_RING
     `p = Cx(&0) ==> w - z - p = w - z`) THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN MATCH_MP_TAC VSUM_EQ_0 THEN
    REWRITE_TAC[IN_NUMSEG; COMPLEX_VEC_0] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[COMPLEX_ENTIRE; complex_div] THEN REPEAT DISJ1_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `g = \w. infsum (from 0)
                   (\m. higher_complex_derivative (m + n) f z /
                        Cx(&(FACT(m + n))) * (w - z) pow m)` THEN
  SUBGOAL_THEN
   `!w. w IN ball(z,r)
        ==> ((\m. higher_complex_derivative (m + n) f z /
                  Cx(&(FACT(m + n))) * (w - z) pow m)
             sums g(w)) (from 0)`
  (LABEL_TAC "*") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "g" THEN REWRITE_TAC[SUMS_INFSUM] THEN
    ASM_CASES_TAC `w:complex = z` THENL
     [MATCH_MP_TAC SUMMABLE_FROM_ELSEWHERE THEN EXISTS_TAC `1` THEN
      MATCH_MP_TAC SUMMABLE_EQ THEN EXISTS_TAC `\n:num. Cx(&0)` THEN
      REWRITE_TAC[SUMMABLE_0; GSYM COMPLEX_VEC_0] THEN
      ASM_SIMP_TAC[IN_FROM; COMPLEX_VEC_0; COMPLEX_SUB_REFL;
                   COMPLEX_POW_ZERO; LE_1; COMPLEX_MUL_RZERO];
      SUBGOAL_THEN
       `!x:complex m. x * (w - z) pow m =
                      (x * (w - z) pow (m + n)) / (w - z) pow n`
       (fun th -> ONCE_REWRITE_TAC[th])
      THENL
       [REPEAT GEN_TAC THEN
        SIMP_TAC[complex_div; GSYM COMPLEX_MUL_ASSOC; COMPLEX_POW_ADD] THEN
        ASM_SIMP_TAC[COMPLEX_MUL_RINV; COMPLEX_POW_EQ_0; COMPLEX_SUB_0] THEN
        REWRITE_TAC[COMPLEX_MUL_RID];
        MATCH_MP_TAC SUMMABLE_COMPLEX_DIV THEN
        MP_TAC(GEN `a:num->complex`
          (ISPECL [`n:num`; `a:num->complex`] SUMMABLE_REINDEX)) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
        REWRITE_TAC[summable; ADD_CLAUSES] THEN ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `g holomorphic_on ball(z,r)` ASSUME_TAC THENL
   [MATCH_MP_TAC POWER_SERIES_HOLOMORPHIC THEN
    EXISTS_TAC `\m. higher_complex_derivative (m + n) f z /
                    Cx(&(FACT (m + n)))` THEN
    EXISTS_TAC `from 0` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN ball(z,r) ==> f w - f z = (w - z) pow n * g(w)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SERIES_UNIQUE THEN
    EXISTS_TAC `\m. higher_complex_derivative m f z / Cx(&(FACT m)) *
                    (w - z) pow m` THEN
    EXISTS_TAC `from n` THEN ASM_SIMP_TAC[] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [ARITH_RULE `n = 0 + n`] THEN
    REWRITE_TAC[GSYM SUMS_REINDEX] THEN REWRITE_TAC[COMPLEX_POW_ADD] THEN
    ONCE_REWRITE_TAC[COMPLEX_RING `a * b * c:complex = c * a * b`] THEN
    MATCH_MP_TAC SERIES_COMPLEX_LMUL THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `g:complex->complex` THEN
  SUBGOAL_THEN `(g:complex->complex) continuous_on ball(z,r)` MP_TAC THENL
   [ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON]; ALL_TAC] THEN
  REWRITE_TAC[continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN
  ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN DISCH_THEN(MP_TAC o SPEC
   `norm((g:complex->complex) z)`) THEN
  ANTS_TAC THENL
   [REMOVE_THEN "*" (MP_TAC o SPEC `z:complex`) THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `1` o
      MATCH_MP (REWRITE_RULE[IMP_CONJ] SUMS_OFFSET)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[VSUM_SING_NUMSEG] THEN
    DISCH_THEN(MP_TAC o SPEC `Cx(&0)` o
        MATCH_MP(REWRITE_RULE[IMP_CONJ] SERIES_UNIQUE)) THEN
    REWRITE_TAC[complex_pow; ADD_CLAUSES; COMPLEX_MUL_RID] THEN ANTS_TAC THENL
     [REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN MATCH_MP_TAC SUMS_0 THEN
      SIMP_TAC[IN_FROM; LE_1; COMPLEX_SUB_REFL; COMPLEX_POW_ZERO] THEN
      REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_RZERO];
      SIMP_TAC[COMPLEX_SUB_0; NORM_POS_LT] THEN DISCH_THEN(K ALL_TAC) THEN
      ASM_REWRITE_TAC[COMPLEX_VEC_0; complex_div; COMPLEX_ENTIRE] THEN
      REWRITE_TAC[COMPLEX_INV_EQ_0; CX_INJ; REAL_OF_NUM_EQ; FACT_NZ]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d r:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  SUBGOAL_THEN `ball(z,min d r) SUBSET ball(z:complex,r)` ASSUME_TAC THENL
   [SIMP_TAC[SUBSET_BALL; REAL_ARITH `min d r <= r`]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[HOLOMORPHIC_ON_SUBSET]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[IN_BALL; REAL_LT_MIN; GSYM COMPLEX_VEC_0] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_BALL]) THEN
  ASM_MESON_TAC[DIST_SYM; NORM_ARITH `dist(x,y) < norm y ==> ~(x = vec 0)`]);;

let HOLOMORPHIC_FACTOR_ORDER_OF_ZERO_STRONG = prove
 (`!f s n z.
      open s /\ z IN s /\ f holomorphic_on s /\
      0 < n /\ ~(higher_complex_derivative n f z = Cx(&0)) /\
      (!m. 0 < m /\ m < n ==> higher_complex_derivative m f z = Cx(&0))
      ==> ?g r. &0 < r /\
                g holomorphic_on ball(z,r) /\
                (!w. w IN ball(z,r)
                     ==> f(w) - f(z) = ((w - z) * g w) pow n) /\
                (!w. w IN ball(z,r) ==> ~(g w = Cx(&0)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:complex->complex`; `s:complex->bool`; `n:num`]
        HOLOMORPHIC_FACTOR_ORDER_OF_ZERO) THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `r:real` THEN
  DISCH_THEN(X_CHOOSE_THEN `g:complex->complex` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`\z. complex_derivative g z / g z`; `ball(z:complex,r)`;
    `{}:complex->bool`] HOLOMORPHIC_CONVEX_PRIMITIVE) THEN
  REWRITE_TAC[CONVEX_BALL; FINITE_RULES; DIFF_EMPTY] THEN ANTS_TAC THENL
   [SIMP_TAC[GSYM HOLOMORPHIC_ON_OPEN; OPEN_BALL;
             INTERIOR_OPEN; complex_differentiable] THEN
    MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN
    REWRITE_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON] THEN
    ASM_SIMP_TAC[HOLOMORPHIC_COMPLEX_DERIVATIVE; OPEN_BALL;
                 HOLOMORPHIC_ON_DIV; ETA_AX];
    SIMP_TAC[OPEN_BALL; HAS_COMPLEX_DERIVATIVE_WITHIN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `h:complex->complex` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`\z:complex. cexp(h z) / g z`; `ball(z:complex,r)`]
    HAS_COMPLEX_DERIVATIVE_ZERO_CONNECTED_CONSTANT) THEN
  REWRITE_TAC[OPEN_BALL; CONNECTED_BALL] THEN ANTS_TAC THENL
   [X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `Cx(&0) = ((complex_derivative g w / g w * cexp (h w)) * g w -
                cexp (h w) * complex_derivative g w) / g w pow 2`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[COMPLEX_FIELD
       `~(z = Cx(&0)) ==> (d / z * e) * z = e * d`] THEN
      SIMPLE_COMPLEX_ARITH_TAC;
      MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DIV_AT THEN
      ASM_SIMP_TAC[] THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM o_DEF] THEN
        ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
        MATCH_MP_TAC COMPLEX_DIFF_CHAIN_AT THEN
        ASM_SIMP_TAC[HAS_COMPLEX_DERIVATIVE_CEXP];
        ASM_MESON_TAC[HOLOMORPHIC_ON_OPEN; complex_differentiable;
          OPEN_BALL; HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE]]];
    DISCH_THEN(X_CHOOSE_THEN `c:complex` MP_TAC) THEN
    ASM_CASES_TAC `c = Cx(&0)` THENL
     [ASM_SIMP_TAC[CEXP_NZ; COMPLEX_FIELD
       `~(x = Cx(&0)) /\ ~(y = Cx(&0)) ==> ~(x / y = Cx(&0))`] THEN
      ASM_MESON_TAC[];
      ASM_SIMP_TAC[COMPLEX_FIELD
       `~(y = Cx(&0)) /\ ~(z = Cx(&0))
        ==> (x / y = z <=> y = inv(z) * x)`] THEN
      DISCH_TAC THEN EXISTS_TAC
       `\z:complex. cexp((clog(inv c) + h z) / Cx(&n))` THEN
      REWRITE_TAC[CEXP_NZ; GSYM CEXP_N; COMPLEX_POW_MUL] THEN
      ASM_SIMP_TAC[COMPLEX_DIV_LMUL; CX_INJ; REAL_OF_NUM_EQ; LE_1] THEN
      ASM_SIMP_TAC[CEXP_ADD; CEXP_CLOG; COMPLEX_INV_EQ_0] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN
      REWRITE_TAC[HOLOMORPHIC_ON_CEXP] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN
      ASM_SIMP_TAC[HOLOMORPHIC_ON_CONST; CX_INJ; REAL_OF_NUM_EQ; LE_1] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_ADD THEN
      REWRITE_TAC[HOLOMORPHIC_ON_CONST] THEN
      ASM_MESON_TAC[HOLOMORPHIC_ON_OPEN; OPEN_BALL]]]);;

let HOLOMORPHIC_FACTOR_ZERO_NONCONSTANT = prove
 (`!f s z.
        open s /\ connected s /\ z IN s /\
        f holomorphic_on s /\ f(z) = Cx(&0) /\ ~(?c. !w. w IN s ==> f w = c)
        ==> ?g r n.
                0 < n /\ &0 < r /\ ball(z,r) SUBSET s /\
                g holomorphic_on ball(z,r) /\
                (!w. w IN ball(z,r) ==> f w = (w - z) pow n * g w) /\
                (!w. w IN ball(z,r) ==> ~(g w = Cx (&0)))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `!n. 0 < n ==> higher_complex_derivative n f z = Cx(&0)` THENL
   [MP_TAC(ISPECL
     [`f:complex->complex`; `s:complex->bool`; `z:complex`]
     HOLOMORPHIC_FUN_EQ_CONST_ON_CONNECTED) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
    DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
    GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
    REWRITE_TAC[NOT_IMP; GSYM IMP_CONJ_ALT] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`f:complex->complex`; `s:complex->bool`; `n:num`]
        HOLOMORPHIC_FACTOR_ORDER_OF_ZERO) THEN
    ASM_REWRITE_TAC[COMPLEX_SUB_RZERO] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `g:complex->complex` THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min r0 r1:real` THEN EXISTS_TAC `n:num` THEN
    ASM_SIMP_TAC[BALL_MIN_INTER; IN_INTER; REAL_LT_MIN] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        HOLOMORPHIC_ON_SUBSET)) THEN
      ASM SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Relating invertibility and nonvanishing of derivative.                    *)
(* ------------------------------------------------------------------------- *)

let HAS_COMPLEX_DERIVATIVE_LOCALLY_INJECTIVE = prove
 (`!f s z.
        f holomorphic_on s /\ open s /\ z IN s /\
        ~(complex_derivative f z = Cx(&0))
        ==> ?t. z IN t /\
                open t /\
                (!x x'. x IN t /\ x' IN t /\ f x' = f x ==> x' = x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_LOCALLY_INJECTIVE THEN
  EXISTS_TAC `\z h. complex_derivative f z * h` THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN EXISTS_TAC `s:complex->bool` THEN
  ASM_REWRITE_TAC[GSYM has_complex_derivative] THEN
  REWRITE_TAC[CONJ_ASSOC; LEFT_EXISTS_AND_THM] THEN
  ASM_REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC LINEAR_INJECTIVE_LEFT_INVERSE THEN
    ASM_SIMP_TAC[LINEAR_COMPLEX_MUL; COMPLEX_EQ_MUL_LCANCEL];
    ASM_MESON_TAC[HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(complex_derivative f) continuous_on s` MP_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_ON_IMP_CONTINUOUS_ON THEN
      ASM_SIMP_TAC[HOLOMORPHIC_COMPLEX_DERIVATIVE];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[continuous_on] THEN
    DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
    ASM_REWRITE_TAC[dist; REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
    DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN
    ASM_REWRITE_TAC[SUBSET; IN_BALL; ONCE_REWRITE_RULE[DIST_SYM] dist] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d r:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x <= e / &2 ==> x < e`) THEN
    ASM_REWRITE_TAC[GSYM COMPLEX_SUB_RDISTRIB] THEN MATCH_MP_TAC
     (CONJUNCT2(MATCH_MP ONORM (SPEC_ALL LINEAR_COMPLEX_MUL))) THEN
    GEN_TAC THEN REWRITE_TAC[COMPLEX_NORM_MUL] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE]]);;

let HAS_COMPLEX_DERIVATIVE_LOCALLY_INVERTIBLE = prove
 (`!f s z.
        f holomorphic_on s /\ open s /\ z IN s /\
        ~(complex_derivative f z = Cx(&0))
        ==> ?t g. z IN t /\ open t /\ open(IMAGE f t) /\ t SUBSET s /\
                  (!w. w IN t ==> g(f w) = w) /\
                  (!y. y IN (IMAGE f t) ==> f(g y) = y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HAS_COMPLEX_DERIVATIVE_LOCALLY_INJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:complex->bool` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
  REWRITE_TAC[INJECTIVE_ON_LEFT_INVERSE] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:complex->complex`) THEN
  EXISTS_TAC `s INTER t:complex->bool` THEN
  EXISTS_TAC `g:complex->complex` THEN
  ASM_SIMP_TAC[OPEN_INTER; IN_INTER; INTER_SUBSET; FORALL_IN_IMAGE] THEN
  MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN
  ASM_SIMP_TAC[OPEN_INTER; IN_INTER] THEN
  ASM_MESON_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON;
                HOLOMORPHIC_ON_SUBSET; INTER_SUBSET]);;

let HOLOMORPHIC_INJECTIVE_IMP_REGULAR = prove
 (`!f s.
        f holomorphic_on s /\ open s /\
        (!w z. w IN s /\ z IN s /\ f w = f z ==> w = z)
        ==> !z. z IN s ==> ~(complex_derivative f z = Cx(&0))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `!n. 0 < n ==> higher_complex_derivative n f z = Cx(&0)` THENL
   [MP_TAC(ISPECL
     [`f:complex->complex`; `ball(z:complex,r)`; `z:complex`]
     HOLOMORPHIC_FUN_EQ_CONST_ON_CONNECTED) THEN
    ASM_SIMP_TAC[OPEN_BALL; CONNECTED_BALL; CENTRE_IN_BALL; NOT_IMP] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[HOLOMORPHIC_ON_SUBSET]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `z + Cx(r / &2)`) THEN
    REWRITE_TAC[IN_BALL; NORM_ARITH `dist(z,z + r) = norm r`] THEN
    REWRITE_TAC[COMPLEX_NORM_CX; NOT_IMP] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`z:complex`; `z + Cx(r / &2)`]) THEN
    ASM_REWRITE_TAC[COMPLEX_RING `z = z + a <=> a = Cx(&0)`] THEN
    REWRITE_TAC[NOT_IMP; CX_INJ] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    REWRITE_TAC[IN_BALL; NORM_ARITH `dist(z,z + r) = norm r`] THEN
    REWRITE_TAC[COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM])] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  REWRITE_TAC[NOT_IMP; GSYM IMP_CONJ_ALT] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:complex->complex`; `s:complex->bool`; `n:num`; `z:complex`]
     HOLOMORPHIC_FACTOR_ORDER_OF_ZERO_STRONG) THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`g:complex->complex`; `k:real`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `n = 1` THENL
   [ASM_MESON_TAC[HIGHER_COMPLEX_DERIVATIVE_1]; ALL_TAC] THEN
  MP_TAC(ISPECL[`\w:complex. (w - z) * g(w)`; `ball(z:complex,min r k)`;
                `z:complex`] HAS_COMPLEX_DERIVATIVE_LOCALLY_INVERTIBLE) THEN
  ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL; NOT_IMP; REAL_LT_MIN] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `!w. w IN ball(z,min r k)
          ==> ((\w. (w - z) * g w) has_complex_derivative
               ((w - z) * complex_derivative g w + (Cx(&1) - Cx(&0)) * g w))
              (at w)`
    (LABEL_TAC "*")
    THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `w IN ball(z:complex,k)` ASSUME_TAC THENL
       [ASM_MESON_TAC[SUBSET; SUBSET_BALL; REAL_ARITH `min r k <= k`];
        ALL_TAC] THEN
      MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_MUL_AT THEN
      SIMP_TAC[HAS_COMPLEX_DERIVATIVE_ID; HAS_COMPLEX_DERIVATIVE_SUB;
       HAS_COMPLEX_DERIVATIVE_CONST; HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
      ASM_MESON_TAC[HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT; OPEN_BALL];
      SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_BALL] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REMOVE_THEN "*" (MP_TAC o SPEC `z:complex`) THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL; REAL_LT_MIN] THEN
      DISCH_THEN(SUBST1_TAC o  MATCH_MP HAS_COMPLEX_DERIVATIVE_DERIVATIVE) THEN
      REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_MUL_LZERO; COMPLEX_ADD_LID;
                  COMPLEX_SUB_RZERO; COMPLEX_MUL_LID] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL]];
    REWRITE_TAC[NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`t:complex->bool`; `h:complex->complex`] THEN
    ABBREV_TAC `u = IMAGE (\w:complex. (w - z) * g w) t` THEN STRIP_TAC THEN
    MP_TAC(ISPEC `u:complex->bool` OPEN_CONTAINS_CBALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `Cx(&0)`) THEN
    ANTS_TAC THENL
     [EXPAND_TAC "u" THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `z:complex` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    REWRITE_TAC[NOT_EXISTS_THM; SUBSET; IN_CBALL; dist;
                COMPLEX_SUB_LZERO; NORM_NEG] THEN
    X_GEN_TAC `e:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(fun th ->
     MP_TAC(ISPEC `Cx(e) * cexp(Cx(&2) * Cx pi * ii * Cx(&0 / &n))` th) THEN
     MP_TAC(ISPEC `Cx(e) * cexp(Cx(&2) * Cx pi * ii * Cx(&1 / &n))` th)) THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; NORM_CEXP; RE_MUL_CX; RE_MUL_II] THEN
    REWRITE_TAC[IM_CX; REAL_NEG_0; REAL_MUL_RZERO; REAL_EXP_0] THEN
    REWRITE_TAC[COMPLEX_NORM_CX; REAL_MUL_RID] THEN
    SIMP_TAC[REAL_ARITH `&0 < e ==> abs e <= e`; ASSUME `&0 < e`] THEN
    EXPAND_TAC "u" THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y1:complex` (STRIP_ASSUME_TAC o GSYM)) THEN
    DISCH_THEN(X_CHOOSE_THEN `y0:complex` (STRIP_ASSUME_TAC o GSYM)) THEN
    UNDISCH_THEN `!w. w IN ball (z,k) ==> f w - f z = ((w - z) * g w) pow n`
      (fun th -> MP_TAC(SPEC `y1:complex` th) THEN
                 MP_TAC(SPEC `y0:complex` th)) THEN
    MATCH_MP_TAC(TAUT `(p1 /\ p2) /\ ~(q1 /\ q2)
                       ==> (p1 ==> q1) ==> (p2 ==> q2) ==> F`) THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET; SUBSET_BALL; REAL_ARITH `min r k <= k`];
      MATCH_MP_TAC(MESON[] `x' = y' /\ ~(x = y) ==> ~(x = x' /\ y = y')`)] THEN
    CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[INJECTIVE_ON_LEFT_INVERSE]) THEN
      ASM_SIMP_TAC[] THEN REWRITE_TAC[COMPLEX_POW_MUL] THEN
      ASM_SIMP_TAC[COMPLEX_ROOT_UNITY; LE_1];
      REWRITE_TAC[COMPLEX_RING `x - a:complex = y - a <=> x = y`] THEN
      DISCH_TAC THEN UNDISCH_THEN
       `!w z. w IN s /\ z IN s /\ (f:complex->complex) w = f z ==> w = z`
       (MP_TAC o SPECL [`y0:complex`; `y1:complex`]) THEN
      ASM_REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[SUBSET; SUBSET_BALL; REAL_ARITH `min r k <= r`];
        DISCH_THEN SUBST_ALL_TAC] THEN
      MP_TAC(ISPECL [`n:num`; `0`; `1`] COMPLEX_ROOT_UNITY_EQ) THEN
      ASM_SIMP_TAC[LE_1] THEN MATCH_MP_TAC(TAUT `a /\ ~b ==> ~(a <=> b)`) THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (COMPLEX_RING
         `z = e * y ==> z = e * x /\ ~(e = Cx(&0)) ==> x = y`)) THEN
        ASM_SIMP_TAC[CX_INJ; REAL_LT_IMP_NZ];
        REWRITE_TAC[num_congruent; int_congruent] THEN
        DISCH_THEN(X_CHOOSE_THEN `d:int`
         (MP_TAC o AP_TERM `abs:int->int` o SYM)) THEN
        REWRITE_TAC[INT_ABS_NUM; INT_SUB_LZERO; INT_ABS_NEG] THEN
        ASM_REWRITE_TAC[INT_ABS_MUL_1; INT_OF_NUM_EQ; INT_ABS_NUM]]]]);;

(* ------------------------------------------------------------------------- *)
(* Hence a nice clean inverse function theorem.                              *)
(* ------------------------------------------------------------------------- *)

let HOLOMORPHIC_ON_INVERSE = prove
 (`!f s. f holomorphic_on s /\ open s /\
         (!w z. w IN s /\ z IN s /\ f w = f z ==> w = z)
         ==> open(IMAGE f s) /\
             ?g. g holomorphic_on (IMAGE f s) /\
                 (!z. z IN s
                      ==> complex_derivative f z * complex_derivative g (f z) =
                          Cx(&1)) /\
                 (!z. z IN s ==> g(f z) = z) /\
                 (!y. y IN (IMAGE f s) ==> f(g y) = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN
    ASM_MESON_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON];
    DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INJECTIVE_ON_LEFT_INVERSE]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:complex->complex` THEN
  STRIP_TAC THEN ASM_SIMP_TAC[FORALL_IN_IMAGE] THEN
  ASM_SIMP_TAC[HOLOMORPHIC_ON_OPEN; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[AND_FORALL_THM] THEN X_GEN_TAC `z:complex` THEN
  ASM_CASES_TAC `(z:complex) IN s` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`f:complex->complex`; `g:complex->complex`;
    `complex_derivative f z`; `s:complex->bool`;
    `z:complex`] HAS_COMPLEX_DERIVATIVE_INVERSE_STRONG) THEN
  ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON; IMP_CONJ] THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE; HOLOMORPHIC_ON_OPEN;
                        complex_differentiable];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:complex->complex`; `s:complex->bool`]
        HOLOMORPHIC_INJECTIVE_IMP_REGULAR) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(MP_TAC o SPEC `z:complex`)] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[COMPLEX_FIELD
   `~(z = Cx(&0)) ==> (z * w = Cx(&1) <=> w = inv z)`] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_DERIVATIVE]);;

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

(* ------------------------------------------------------------------------- *)
(* Montel's theorem: a sequence of holomorphic functions uniformly bounded   *)
(* on compact subsets of an open set S has a subsequence that converges to a *)
(* holomorphic function, and converges *uniformly* on compact subsets of S.  *)
(* ------------------------------------------------------------------------- *)

let MONTEL = prove
 (`!(f:num->complex->complex) p s.
    open s /\ (!h. h IN p ==> h holomorphic_on s) /\
    (!k. compact k /\ k SUBSET s
         ==> ?b. !h z. h IN p /\ z IN k ==> norm(h z) <= b) /\
    (!n. (f n) IN p)
    ==> ?g r. g holomorphic_on s /\
              (!m n:num. m < n ==> r m < r n) /\
              (!x. x IN s ==> ((\n. f (r n) x) --> g(x)) sequentially) /\
              (!k e. compact k /\ k SUBSET s /\ &0 < e
                     ==> ?N. !n x. n >= N /\ x IN k
                                   ==> norm(f (r n) x - g x) < e)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SPEC_TAC(`f:num->complex->complex`,`f:num->complex->complex`) THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM GE; dist] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_UNION_COMPACT_SUBSETS) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num->complex->bool`
   (fun th -> FIRST_X_ASSUM(MP_TAC o GEN `i:num `o
                SPEC `(k:num->complex->bool) i`) THEN
              STRIP_ASSUME_TAC th)) THEN
  ASM_REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `B:num->real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!(f:num->complex->complex) (i:num).
        (!n. f n IN p)
        ==>  ?r g. (!m n:num. m < n ==> r m < r n) /\
                   (!e. &0 < e ==> ?N. !n x. n >= N /\ x IN k i
                                             ==> norm((f o r) n x - g x) < e)`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
    MP_TAC(ISPECL [`f:num->complex->complex`; `(k:num->complex->bool) i`;
                   `(B:num->real) i`] ARZELA_ASCOLI) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; MESON_TAC[]] THEN
    MAP_EVERY X_GEN_TAC [`z:complex`; `e:real`] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
    DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[SUBSET; IN_CBALL]] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `?M. &0 < M /\
          !n w. dist(z,w) <= &2 / &3 * r
                ==> norm((f:num->complex->complex) n w) <= M`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `cball(z:complex,&2 / &3 * r)`) THEN
      ASM_SIMP_TAC[SUBSET; IN_CBALL; COMPACT_CBALL;
              NORM_ARITH `dist(a,b) <= &2 / &3 * r ==> dist(a,b) <= r`] THEN
      DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN
      REWRITE_TAC[GE; LE_REFL] THEN DISCH_TAC THEN
      EXISTS_TAC `abs(B(N:num)) + &1` THEN
      REWRITE_TAC[REAL_ARITH `&0 < abs x + &1`] THEN
      ASM_MESON_TAC[SUBSET; REAL_ARITH `x <= b ==> x <= abs b + &1`];
      ALL_TAC] THEN
    EXISTS_TAC `min (r / &3) ((e * r) / (&6 * M))` THEN
    ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_DIV;
                 REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:complex`] THEN STRIP_TAC THEN
    MP_TAC
     (ISPECL [`(f:num->complex->complex) n`;  `cball(z:complex,&2 / &3 * r)`;
              `circlepath(z:complex,&2 / &3 * r)`]
        CAUCHY_INTEGRAL_FORMULA_CONVEX_SIMPLE) THEN
    REWRITE_TAC[CONVEX_CBALL; VALID_PATH_CIRCLEPATH] THEN
    REWRITE_TAC[PATHSTART_CIRCLEPATH; PATHFINISH_CIRCLEPATH] THEN
    SIMP_TAC[INTERIOR_CBALL; IN_BALL; WINDING_NUMBER_CIRCLEPATH;
             NORM_ARITH `dist(z,w) = norm(w - z)`] THEN
    ASM_SIMP_TAC[PATH_IMAGE_CIRCLEPATH;
                 REAL_ARITH `&0 < r ==> &0 <= &2 / &3 * r`] THEN
    SIMP_TAC[SUBSET; IN_CBALL; IN_DELETE; IN_ELIM_THM; REAL_LE_REFL;
             NORM_ARITH `dist(z,w) = norm(w - z)`] THEN
    ONCE_REWRITE_TAC[TAUT `p ==> ~q <=> q ==> ~p`] THEN
    SIMP_TAC[FORALL_UNWIND_THM2; IMP_CONJ; REAL_LT_IMP_NE] THEN
    REWRITE_TAC[RIGHT_FORALL_IMP_THM; COMPLEX_MUL_LID] THEN ANTS_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
      EXISTS_TAC `s:complex->bool` THEN ASM_SIMP_TAC[SUBSET; IN_CBALL] THEN
      ASM_SIMP_TAC[NORM_ARITH `dist(a,b) <= &2 / &3 * r ==> dist(a,b) <= r`];
      ALL_TAC] THEN
    DISCH_THEN(fun th ->
      MP_TAC(SPEC `y:complex` th) THEN MP_TAC(SPEC `z:complex` th)) THEN
    ASM_SIMP_TAC[VECTOR_SUB_REFL; NORM_0; REAL_LT_MUL; REAL_LT_DIV;
      REAL_OF_NUM_LT; ARITH; NORM_ARITH
       `norm(z - y) < r / &3 ==> norm(y - z) < &2 / &3 * r`] THEN
    REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP HAS_PATH_INTEGRAL_SUB) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        HAS_PATH_INTEGRAL_BOUND_CIRCLEPATH)) THEN
    REWRITE_TAC[GSYM COMPLEX_SUB_LDISTRIB; COMPLEX_NORM_MUL] THEN
    REWRITE_TAC[COMPLEX_NORM_II; COMPLEX_NORM_CX; REAL_ABS_PI;
                REAL_ABS_NUM; REAL_MUL_LID] THEN
    DISCH_THEN(MP_TAC o SPEC `e / r:real`) THEN
    ASM_SIMP_TAC[REAL_FIELD
     `&0 < r ==> e / r * &2 * pi * c * r = &2 * pi * e * c`] THEN
    SIMP_TAC[REAL_LE_LMUL_EQ; REAL_OF_NUM_LT; ARITH; PI_POS] THEN
    ANTS_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH;
                 REAL_LT_MUL] THEN
    X_GEN_TAC `w:complex` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(w:complex = z) /\ ~(w = y)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[NORM_0; VECTOR_SUB_REFL]) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[NORM_SUB]) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[COMPLEX_FIELD
     `~(w:complex = z) /\ ~(w = y)
      ==> (a / (w - z) - a / (w - y) =
           (a * (z - y)) / ((w - z) * (w - y)))`] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_DIV] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_MUL; NORM_POS_LT; VECTOR_SUB_EQ;
     REAL_FIELD `&0 < r ==> e / r * (&2 / &3 * r) * x = &2 / &3 * e * x`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `M * (e * r) / (&6 * M)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[NORM_ARITH `dist(x,y) = norm(y - x)`; REAL_LE_REFL];
      ASM_SIMP_TAC[REAL_FIELD `&0 < M ==> M * e / (&6 * M) = e / &6`] THEN
      MATCH_MP_TAC(REAL_ARITH
       `&0 < x /\ x <= y * &3 ==> x / &6 <= &2 / &3 * y`) THEN
      ASM_SIMP_TAC[REAL_LT_MUL; GSYM REAL_MUL_ASSOC; REAL_LE_LMUL_EQ] THEN
      MAP_EVERY UNDISCH_TAC
       [`norm(w - z:complex) = &2 / &3 * r`;
        `norm(z - y:complex) < r / &3`] THEN
      CONV_TAC NORM_ARITH];
    ALL_TAC] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
  DISCH_THEN(fun th -> X_GEN_TAC `f:num->complex->complex` THEN
                       DISCH_TAC THEN MP_TAC th) THEN
  DISCH_THEN(MP_TAC o GENL [`i:num`; `r:num->num`] o
    SPECL [`(f:num->complex->complex) o (r:num->num)`; `i:num`]) THEN
  GEN_REWRITE_TAC
   (LAND_CONV o funpow 2 BINDER_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [o_THM] THEN ASM_REWRITE_TAC[GSYM o_ASSOC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    SUBSEQUENCE_DIAGONALIZATION_LEMMA)) THEN
  ANTS_TAC THENL
   [SIMP_TAC[o_THM; GE] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:complex->complex` THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
    EXISTS_TAC `MAX M N` THEN
    REWRITE_TAC[ARITH_RULE `MAX m n <= x <=> m <= x /\ n <= x`] THEN
    ASM_MESON_TAC[LE_TRANS];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `I:num->num`) THEN
  REWRITE_TAC[I_O_ID; RIGHT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:num->num` THEN
  REWRITE_TAC[o_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!x. x IN s
        ==> ?l. !e. &0 < e
                    ==> ?N:num. !n. n >= N
                                ==> norm((f:num->complex->complex) (r n) x - l)
                                    < e`
  MP_TAC THENL
   [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `{z:complex}`) THEN
    ASM_REWRITE_TAC[COMPACT_SING; SING_SUBSET] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SKOLEM_THM]) THEN
    DISCH_THEN(X_CHOOSE_THEN `G:num->complex->complex` MP_TAC) THEN
    DISCH_THEN(LABEL_TAC "*" o SPEC `N:num`) THEN
    EXISTS_TAC `(G:num->complex->complex) N z` THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `e:real`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `M:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `MAX M N` THEN
    REWRITE_TAC[ARITH_RULE `a >= MAX m n <=> a >= m /\ a >= n`] THEN
    ASM_MESON_TAC[GE_REFL];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; RIGHT_IMP_FORALL_THM; IMP_IMP] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:complex->complex` THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t:complex->bool`; `e:real`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:complex->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `h:complex->complex` (LABEL_TAC "*") o
      SPEC `N:num`) THEN
    SUBGOAL_THEN
     `!w. w IN t ==> g w = (h:complex->complex) w`
     (fun th -> ASM_MESON_TAC[GE_REFL; SUBSET; th]) THEN
    X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\n:num. (f:num->complex->complex)(r n) w` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; LIM_SEQUENTIALLY] THEN
    REWRITE_TAC[GSYM GE; dist; o_THM] THEN
    ASM_MESON_TAC[SUBSET; GE_REFL];
    DISCH_THEN(LABEL_TAC "*")] THEN
  MATCH_MP_TAC HOLOMORPHIC_UNIFORM_SEQUENCE THEN
  EXISTS_TAC `(f:num->complex->complex) o (r:num->num)` THEN
  ASM_SIMP_TAC[o_THM] THEN X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN ASM_MESON_TAC[COMPACT_CBALL; GE]);;

(* ------------------------------------------------------------------------- *)
(* Moebius functions are biholomorphisms of the unit disc.                   *)
(* ------------------------------------------------------------------------- *)

let moebius_function = new_definition
  `!t w z. moebius_function t w z =
           cexp (ii * Cx t) * (z - w) / (Cx(&1) - cnj w * z)`;;

let MOEBIUS_FUNCTION_SIMPLE = prove
 (`!w z. moebius_function (&0) w z = (z - w) / (Cx(&1) - cnj w * z)`,
  REWRITE_TAC[moebius_function; COMPLEX_MUL_RZERO; CEXP_0; COMPLEX_MUL_LID]);;

let MOEBIUS_FUNCTION_EQ_ZERO = prove
  (`!t w. moebius_function t w w = Cx(&0)`,
   REWRITE_TAC [moebius_function] THEN CONV_TAC COMPLEX_FIELD);;

let MOEBIUS_FUNCTION_OF_ZERO = prove
  (`!t w. moebius_function t w (Cx(&0)) = -- cexp (ii * Cx t) * w`,
   REWRITE_TAC [moebius_function] THEN CONV_TAC COMPLEX_FIELD);;

let MOEBIUS_FUNCTION_NORM_LT_1 = prove
  (`!t w z. norm w < &1 /\ norm z < &1
            ==> norm (moebius_function t w z) < &1`,
   REPEAT STRIP_TAC THEN SUBGOAL_THEN
     `!a. &0 <= a /\ &0 < &1 - a pow 2 ==> a < &1` MATCH_MP_TAC THENL
   [GEN_TAC THEN ASM_CASES_TAC `&0 <= a` THEN
    ASM_REWRITE_TAC [REAL_FIELD `&1 - a pow 2 = (&1 - a) * (&1 + a)`;
                     REAL_MUL_POS_LT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
   REWRITE_TAC [NORM_POS_LE] THEN
   SUBGOAL_THEN `~(Cx (&1) - cnj w * z = Cx (&0))` ASSUME_TAC THENL
   [REWRITE_TAC [COMPLEX_SUB_0] THEN
    SUBGOAL_THEN `~(norm (Cx(&1)) = norm (cnj w * z))`
     (fun th -> MESON_TAC [th]) THEN
    REWRITE_TAC [COMPLEX_NORM_NUM; COMPLEX_NORM_MUL; COMPLEX_NORM_CNJ] THEN
    MATCH_MP_TAC (REAL_ARITH `a * b < &1  ==> ~(&1 = a * b)`) THEN
    STRIP_ASSUME_TAC (NORM_ARITH `norm (z:complex) = &0 \/ &0 < norm z`) THENL
    [ASM_REWRITE_TAC [REAL_MUL_RZERO; REAL_LT_01];
     MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `&1 * norm (z:complex)` THEN
     ASM_SIMP_TAC[REAL_LT_RMUL; REAL_MUL_LID]];
   ALL_TAC] THEN
   SUBGOAL_THEN
    `&1 - norm (moebius_function t w z) pow 2 =
     ((&1 - norm w pow 2) / (norm (Cx(&1) - cnj w * z) pow 2)) *
     (&1 - norm z pow 2)`
   SUBST1_TAC THENL
   [REWRITE_TAC [moebius_function;
                 GSYM CX_INJ; CX_SUB; CX_MUL; CX_DIV; CX_POW; CNJ_SUB; CNJ_CX;
                 CNJ_MUL; CNJ_DIV; CNJ_CNJ; COMPLEX_NORM_POW_2] THEN
    SUBGOAL_THEN
      `cnj (cexp (ii * Cx t)) * (cexp (ii * Cx t)) = Cx(&1) /\
       ~(Cx(&1) - cnj w * z = Cx(&0)) /\ ~(Cx(&1) - w * cnj z = Cx(&0))`
     MP_TAC THENL [ALL_TAC; CONV_TAC COMPLEX_FIELD] THEN
    REWRITE_TAC [CNJ_CEXP; CNJ_MUL; CNJ_II; CNJ_CX;
                  COMPLEX_MUL_LNEG; CEXP_NEG_LMUL] THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN `~(cnj (Cx (&1) - cnj w * z) = Cx (&0))` MP_TAC THENL
    [ASM_REWRITE_TAC [CNJ_EQ_0];
     REWRITE_TAC [CNJ_SUB; CNJ_CX; CNJ_MUL; CNJ_CNJ]];
    SUBGOAL_THEN `!u:complex. norm u < &1 ==> &0 < &1 - norm u pow 2`
      ASSUME_TAC THENL
    [REWRITE_TAC [REAL_FIELD `!a. &1 - a pow 2 = (&1 - a) * (&1 + a)`] THEN
     ASM_SIMP_TAC [REAL_LT_MUL; REAL_SUB_LT; REAL_LTE_ADD; REAL_LT_01;
                   NORM_POS_LE];
     SUBGOAL_THEN `&0 < norm (Cx (&1) - cnj w * z) pow 2`
      (fun th -> ASM_MESON_TAC [th; REAL_LT_MUL; REAL_LT_DIV]) THEN
     ASM_REWRITE_TAC [REAL_RING `!a:real. a pow 2 =  a * a`;
                      REAL_LT_SQUARE; COMPLEX_NORM_ZERO]]]);;

let MOEBIUS_FUNCTION_HOLOMORPHIC = prove
  (`!t w. norm w < &1 ==> moebius_function t w holomorphic_on ball(Cx(&0),&1)`,
   let LEMMA_1 = prove
    (`!a b:complex. norm a < &1 /\ norm b < &1 ==> ~(Cx(&1) - a * b = Cx(&0))`,
     GEN_TAC THEN GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [COMPLEX_SUB_0] THEN
     SUBGOAL_THEN `~(norm (Cx(&1)) = norm (a * b))`
       (fun th -> MESON_TAC[th]) THEN
     REWRITE_TAC [COMPLEX_NORM_NUM; COMPLEX_NORM_MUL] THEN
     MATCH_MP_TAC (REAL_ARITH `!x y. y < x ==> ~(x = y)`) THEN
     ASM_CASES_TAC `b = Cx(&0)` THEN
     ASM_REWRITE_TAC [COMPLEX_NORM_NUM; REAL_MUL_RZERO; REAL_LT_01] THEN
     MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `&1 * norm (b:complex)` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC [COMPLEX_NORM_NZ];
      ASM_REWRITE_TAC [REAL_MUL_LID]]) in
   REPEAT STRIP_TAC THEN
   SUBST1_TAC (GSYM (ISPEC `moebius_function t w` ETA_AX)) THEN
   REWRITE_TAC [moebius_function] THEN
   MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN  CONJ_TAC THENL
   [MATCH_MP_TAC (REWRITE_RULE [o_DEF] HOLOMORPHIC_ON_COMPOSE_GEN) THEN
    EXISTS_TAC `(:complex)` THEN REWRITE_TAC [HOLOMORPHIC_ON_CEXP; IN_UNIV] THEN
    SIMP_TAC [HOLOMORPHIC_ON_MUL; HOLOMORPHIC_ON_CONST];
    MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN
    SIMP_TAC[HOLOMORPHIC_ON_SUB; HOLOMORPHIC_ON_CONST;
             HOLOMORPHIC_ON_ID; HOLOMORPHIC_ON_MUL] THEN
    ASM_SIMP_TAC[COMPLEX_IN_BALL_0; LEMMA_1; COMPLEX_NORM_CNJ]]);;

let MOEBIUS_FUNCTION_COMPOSE = prove
 (`!w1 w2 z.
     -- w1 = w2  /\ norm w1 < &1 /\ norm z < &1
     ==> moebius_function (&0) w1 (moebius_function (&0) w2 z) = z`,
  let LEMMA_1 = prove
   (`!a b:complex. norm a < &1 /\ norm b < &1
                   ==> ~(Cx(&1) - a * b = Cx(&0))`,
    GEN_TAC THEN GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [COMPLEX_SUB_0] THEN
    SUBGOAL_THEN `~(norm (Cx(&1)) = norm (a * b))`
      (fun th -> MESON_TAC[th]) THEN
    REWRITE_TAC [COMPLEX_NORM_NUM; COMPLEX_NORM_MUL] THEN
    MATCH_MP_TAC (REAL_ARITH `!x y. y < x ==> ~(x = y)`) THEN
    ASM_CASES_TAC `b = Cx(&0)` THEN
    ASM_REWRITE_TAC [COMPLEX_NORM_NUM; REAL_MUL_RZERO; REAL_LT_01] THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `&1 * norm (b:complex)` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC [COMPLEX_NORM_NZ];
     ASM_REWRITE_TAC [REAL_MUL_LID]]) in
  let LEMMA_1_ALT = prove
    (`!a b:complex. norm a < &1 /\ norm b < &1
                    ==> ~(Cx(&1) + a * b = Cx(&0))`,
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     SUBST1_TAC (COMPLEX_RING `a : complex = -- (-- a)`) THEN
     ABBREV_TAC `u : complex= -- a` THEN
     REWRITE_TAC [COMPLEX_MUL_LNEG; GSYM complex_sub] THEN
     MATCH_MP_TAC LEMMA_1 THEN EXPAND_TAC "u" THEN
     ASM_REWRITE_TAC[NORM_NEG]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `norm (w2:complex) < &1` ASSUME_TAC THENL
   [EXPAND_TAC "w2" THEN ASM_REWRITE_TAC [NORM_NEG]; ALL_TAC] THEN
  REWRITE_TAC [moebius_function; COMPLEX_MUL_RZERO;
               CEXP_0; COMPLEX_MUL_LID] THEN
  MATCH_MP_TAC (COMPLEX_FIELD
     `!a b c. ~(b = Cx(&0)) /\ a = b * c ==> a / b = c`) THEN
  CONJ_TAC THENL
   [ALL_TAC; MP_TAC (SPECL [`cnj w2`;`z:complex`] LEMMA_1) THEN
    ASM_REWRITE_TAC [COMPLEX_NORM_CNJ] THEN EXPAND_TAC "w2" THEN
    REWRITE_TAC [CNJ_NEG] THEN CONV_TAC COMPLEX_FIELD] THEN
  MATCH_MP_TAC (COMPLEX_FIELD
      `!a b c d. ~(d = Cx(&0)) /\ ~(d * a - b * c  = Cx(&0))
                 ==> ~(a - b * c / d  = Cx(&0))`) THEN
  ASM_SIMP_TAC [LEMMA_1; COMPLEX_NORM_CNJ] THEN
  ASM_REWRITE_TAC [COMPLEX_MUL_RID] THEN
  SUBGOAL_THEN
      `Cx(&1) - cnj w2 * z - cnj w1 * (z - w2) =
       Cx(&1) + cnj w1 * w2` SUBST1_TAC THENL
   [EXPAND_TAC "w2" THEN REWRITE_TAC [CNJ_NEG] THEN CONV_TAC COMPLEX_RING;
    ASM_SIMP_TAC [LEMMA_1_ALT; COMPLEX_NORM_CNJ]]);;

let BALL_BIHOLOMORPHISM_EXISTS = prove
 (`!a. a IN ball(Cx(&0),&1)
       ==> ?f g. f(a) = Cx(&0) /\
                 f holomorphic_on ball (Cx(&0),&1) /\
                 (!z. z IN ball (Cx(&0),&1) ==> f z IN ball (Cx(&0),&1)) /\
                 g holomorphic_on ball (Cx(&0),&1) /\
                 (!z. z IN ball (Cx(&0),&1) ==> g z IN ball (Cx(&0),&1)) /\
                 (!z. z IN ball (Cx(&0),&1) ==> f (g z) = z) /\
                 (!z. z IN ball (Cx(&0),&1) ==> g (f z) = z)`,
  REWRITE_TAC[COMPLEX_IN_BALL_0] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `moebius_function (&0) a` THEN
  EXISTS_TAC `moebius_function (&0) (--a)` THEN
  ASM_SIMP_TAC[COMPLEX_IN_BALL_0; MOEBIUS_FUNCTION_COMPOSE; COMPLEX_NEG_NEG;
               NORM_NEG] THEN
  ASM_SIMP_TAC[MOEBIUS_FUNCTION_NORM_LT_1; NORM_NEG;
               MOEBIUS_FUNCTION_HOLOMORPHIC; MOEBIUS_FUNCTION_EQ_ZERO]);;

let BALL_BIHOLOMORPHISM_MOEBIUS_FUNCTION = prove
  (`!f g.
      f holomorphic_on ball (Cx(&0),&1) /\
      (!z. z IN ball (Cx(&0),&1) ==> f z IN ball (Cx(&0),&1)) /\
      g holomorphic_on ball (Cx(&0),&1) /\
      (!z. z IN ball (Cx(&0),&1) ==> g z IN ball (Cx(&0),&1)) /\
      (!z. z IN ball (Cx(&0),&1) ==> f (g z) = z) /\
      (!z. z IN ball (Cx(&0),&1) ==> g (f z) = z)
      ==> ?t w. w IN ball (Cx(&0),&1) /\
                (!z. z IN ball (Cx(&0),&1) ==> f z = moebius_function t w z)`,
   let LEMMA_1 = prove
     (`!a b:complex. norm a < &1 /\ norm b < &1
                     ==> ~(Cx(&1) - a * b = Cx(&0))`,
      GEN_TAC THEN GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [COMPLEX_SUB_0] THEN
      SUBGOAL_THEN `~(norm (Cx(&1)) = norm (a * b))`
        (fun th -> MESON_TAC[th]) THEN
      REWRITE_TAC [COMPLEX_NORM_NUM; COMPLEX_NORM_MUL] THEN
      MATCH_MP_TAC (REAL_ARITH `!x y. y < x ==> ~(x = y)`) THEN
      ASM_CASES_TAC `b = Cx(&0)` THEN
      ASM_REWRITE_TAC [COMPLEX_NORM_NUM; REAL_MUL_RZERO; REAL_LT_01] THEN
      MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `&1 * norm (b:complex)` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC [COMPLEX_NORM_NZ];
       ASM_REWRITE_TAC [REAL_MUL_LID]]) in
   let LEMMA_2 = prove
     (`!t w s z. norm w < &1 /\ norm z < &1
                 ==> moebius_function t w (cexp (ii * Cx s) * z) =
                     moebius_function (t + s) (cexp (-- (ii * Cx s)) * w) z`,
      REPEAT STRIP_TAC THEN
      REWRITE_TAC[moebius_function; CX_ADD; COMPLEX_ADD_LDISTRIB; CEXP_ADD;
                  GSYM COMPLEX_MUL_ASSOC; COMPLEX_EQ_MUL_LCANCEL; CEXP_NZ;
               CNJ_MUL] THEN
      MATCH_MP_TAC (COMPLEX_FIELD
        `!a b c d e. ~(b = Cx(&0)) /\ ~(e = Cx(&0)) /\ e * a = b * c * d
                     ==> a / b = c * d / e`) THEN CONJ_TAC THENL
      [MATCH_MP_TAC LEMMA_1 THEN
       ASM_REWRITE_TAC [COMPLEX_NORM_CNJ; COMPLEX_NORM_MUL; NORM_CEXP_II;
                        REAL_MUL_LID];
       ALL_TAC] THEN
      CONJ_TAC THENL
      [REWRITE_TAC [COMPLEX_MUL_ASSOC] THEN MATCH_MP_TAC LEMMA_1 THEN
       ASM_REWRITE_TAC [COMPLEX_NORM_MUL; COMPLEX_NORM_CNJ; COMPLEX_NEG_RMUL;
                        GSYM CX_NEG; NORM_CEXP_II; REAL_MUL_LID];
       REWRITE_TAC [CNJ_CEXP; CNJ_NEG; CNJ_MUL; CNJ_II; CNJ_CX;
                    COMPLEX_MUL_LNEG; COMPLEX_NEG_NEG; CEXP_NEG] THEN
       ABBREV_TAC `a = cexp (ii * Cx s)` THEN
       SUBGOAL_THEN `inv a * a = Cx(&1)` MP_TAC THENL
       [ALL_TAC; CONV_TAC COMPLEX_RING] THEN
       MATCH_MP_TAC COMPLEX_MUL_LINV THEN EXPAND_TAC "a" THEN
       REWRITE_TAC [CEXP_NZ]]) in
   REWRITE_TAC [COMPLEX_IN_BALL_0] THEN REPEAT STRIP_TAC THEN
   ABBREV_TAC `w:complex = f (Cx(&0))` THEN
   SUBGOAL_THEN `norm(w:complex) < &1` ASSUME_TAC THENL
   [ASM_MESON_TAC [COMPLEX_NORM_NUM; REAL_LT_01]; ALL_TAC] THEN
   SUBGOAL_THEN
    `?t. !z. z IN ball (Cx(&0),&1)
             ==> moebius_function (&0) w (f z) = cexp (ii * Cx t) * z`
    STRIP_ASSUME_TAC THENL
   [ALL_TAC;
    EXISTS_TAC `t:real` THEN EXISTS_TAC `-- (cexp(-- (ii * Cx t)) * w)` THEN
    ASM_REWRITE_TAC [NORM_NEG; COMPLEX_NORM_MUL; COMPLEX_NEG_RMUL;
                     GSYM CX_NEG; NORM_CEXP_II; REAL_MUL_LID] THEN
    GEN_TAC THEN DISCH_TAC THEN EQ_TRANS_TAC
      `moebius_function (&0) (--w)
         (moebius_function (&0) w (f (z:complex)))` THENL
    [MATCH_MP_TAC EQ_SYM THEN MATCH_MP_TAC MOEBIUS_FUNCTION_COMPOSE THEN
     ASM_SIMP_TAC [COMPLEX_NEG_NEG; NORM_NEG];
     ASM_SIMP_TAC[COMPLEX_IN_BALL_0] THEN ASM_SIMP_TAC[LEMMA_2; NORM_NEG] THEN
     REWRITE_TAC [REAL_ADD_LID; CX_NEG; COMPLEX_MUL_RNEG]]] THEN
   MATCH_MP_TAC SECOND_CARTAN_THM_DIM_1 THEN EXISTS_TAC
     `\z. g (moebius_function (&0) (--w) z) : complex` THEN
   REWRITE_TAC [COMPLEX_IN_BALL_0] THEN REWRITE_TAC [REAL_LT_01] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC (REWRITE_RULE [o_DEF] HOLOMORPHIC_ON_COMPOSE_GEN) THEN
    EXISTS_TAC `ball(Cx(&0),&1)` THEN
    ASM_SIMP_TAC [ETA_AX; MOEBIUS_FUNCTION_HOLOMORPHIC; COMPLEX_IN_BALL_0];
    ALL_TAC] THEN CONJ_TAC THENL [ASM_SIMP_TAC [MOEBIUS_FUNCTION_NORM_LT_1];
    ALL_TAC] THEN
   CONJ_TAC THENL [ASM_REWRITE_TAC [MOEBIUS_FUNCTION_EQ_ZERO]; ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC (REWRITE_RULE [o_DEF] HOLOMORPHIC_ON_COMPOSE_GEN) THEN
    EXISTS_TAC `ball(Cx(&0),&1)` THEN
    ASM_SIMP_TAC [COMPLEX_IN_BALL_0; MOEBIUS_FUNCTION_NORM_LT_1;
                  NORM_NEG] THEN
    ASM_SIMP_TAC [ETA_AX; MOEBIUS_FUNCTION_HOLOMORPHIC; NORM_NEG];
    ALL_TAC] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC [MOEBIUS_FUNCTION_NORM_LT_1; NORM_NEG]; ALL_TAC] THEN
   CONJ_TAC THENL
   [ASM_REWRITE_TAC [MOEBIUS_FUNCTION_OF_ZERO; COMPLEX_MUL_RZERO; CEXP_0;
                     GSYM COMPLEX_NEG_LMUL; COMPLEX_MUL_LID;
                      COMPLEX_NEG_NEG] THEN
    ASM_MESON_TAC [COMPLEX_NORM_0; REAL_LT_01];
    ALL_TAC] THEN CONJ_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC [REWRITE_RULE [COMPLEX_NEG_NEG; NORM_NEG]
         (SPECL [`--w:complex`;`w:complex`] MOEBIUS_FUNCTION_COMPOSE)]] THEN
    REPEAT STRIP_TAC THEN SUBGOAL_THEN
     `f (g (moebius_function (&0) (--w) z) : complex) =
      (moebius_function (&0) (--w) z)`
     SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC [MOEBIUS_FUNCTION_NORM_LT_1; NORM_NEG];
    MATCH_MP_TAC MOEBIUS_FUNCTION_COMPOSE THEN ASM_REWRITE_TAC []]);;

(* ------------------------------------------------------------------------- *)
(* Some simple but useful cases of Hurwitz's theorem.                        *)
(* ------------------------------------------------------------------------- *)

let HURWITZ_NO_ZEROS = prove
 (`!f:num->complex->complex g s.
        open s /\ connected s /\
        (!n. (f n) holomorphic_on s) /\ g holomorphic_on s /\
        (!k e. compact k /\ k SUBSET s /\ &0 < e
               ==> ?N. !n x. n >= N /\ x IN k ==> norm(f n x - g x) < e) /\
        ~(?c. !z. z IN s ==> g z = c) /\
        (!n z. z IN s ==> ~(f n z = Cx(&0)))
        ==> (!z. z IN s ==> ~(g z = Cx(&0)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `z0:complex` THEN
  REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`g:complex->complex`; `s:complex->bool`; `z0:complex`]
   HOLOMORPHIC_FACTOR_ZERO_NONCONSTANT) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`h:complex->complex`; `r:real`; `m:num`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL
   [`sequentially`; `\n:num z. complex_derivative (f n) z / f n z`;
    `\z. complex_derivative g z / g z`;  `z0:complex`; `r / &2`]
   PATH_INTEGRAL_UNIFORM_LIMIT_CIRCLEPATH) THEN
  ASM_REWRITE_TAC[REAL_HALF; TRIVIAL_LIMIT_SEQUENTIALLY; NOT_IMP] THEN
  SUBGOAL_THEN
   `!n:num. ((\z. complex_derivative (f n) z / f n z)
             has_path_integral (Cx(&0))) (circlepath(z0,r / &2))`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN MATCH_MP_TAC CAUCHY_THEOREM_DISC_SIMPLE THEN
    MAP_EVERY EXISTS_TAC [`z0:complex`; `r:real`] THEN
    ASM_SIMP_TAC[VALID_PATH_CIRCLEPATH; PATHSTART_CIRCLEPATH;
                 PATHFINISH_CIRCLEPATH; PATH_IMAGE_CIRCLEPATH;
                 REAL_HALF; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[SUBSET; IN_BALL; ONCE_REWRITE_RULE[DIST_SYM] dist] THEN
    ASM_SIMP_TAC[IN_ELIM_THM; REAL_ARITH `&0 < r ==> r / &2 < r`] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC HOLOMORPHIC_COMPLEX_DERIVATIVE THEN
      REWRITE_TAC[OPEN_BALL];
      REWRITE_TAC[ETA_AX];
      ASM_MESON_TAC[SUBSET]] THEN
    ASM_MESON_TAC[HOLOMORPHIC_ON_SUBSET];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
    REWRITE_TAC[path_integrable_on] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC UNIFORM_LIM_COMPLEX_DIV THEN
    REWRITE_TAC[LEFT_EXISTS_AND_THM; CONJ_ASSOC] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; GSYM CONJ_ASSOC] THEN
    REWRITE_TAC[LEFT_EXISTS_AND_THM] THEN
    ASM_SIMP_TAC[PATH_IMAGE_CIRCLEPATH; REAL_HALF; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPEC `IMAGE (complex_derivative g) {w | norm(w - z0) = r / &2}`
        COMPACT_IMP_BOUNDED) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
        REWRITE_TAC[COMPACT_SPHERE; o_DEF] THEN
        MATCH_MP_TAC HOLOMORPHIC_ON_IMP_CONTINUOUS_ON THEN
        MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
        EXISTS_TAC `s:complex->bool` THEN
        ASM_SIMP_TAC[HOLOMORPHIC_COMPLEX_DERIVATIVE] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
          SUBSET_TRANS)) THEN
        REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM] THEN
        UNDISCH_TAC `&0 < r` THEN CONV_TAC NORM_ARITH;
        REWRITE_TAC[bounded; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
        MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
        MATCH_MP_TAC ALWAYS_EVENTUALLY THEN ASM_SIMP_TAC[]];
      MP_TAC(ISPEC `IMAGE (norm o (g:complex->complex))
          {w | norm(w - z0) = r / &2}`
          COMPACT_ATTAINS_INF) THEN
      REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE; IMAGE_EQ_EMPTY] THEN
      REWRITE_TAC[GSYM IMAGE_o; FORALL_IN_GSPEC; EXISTS_IN_GSPEC; o_THM] THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
          REWRITE_TAC[COMPACT_SPHERE; o_DEF] THEN
          MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
          MATCH_MP_TAC HOLOMORPHIC_ON_IMP_CONTINUOUS_ON THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            HOLOMORPHIC_ON_SUBSET)) THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
            SUBSET_TRANS)) THEN
          REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM] THEN
          UNDISCH_TAC `&0 < r` THEN CONV_TAC NORM_ARITH;
          REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
          EXISTS_TAC `z0 + Cx(r / &2)` THEN
          REWRITE_TAC[VECTOR_ARITH `(a + b) - a:real^N = b`] THEN
          REWRITE_TAC[COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC];
        DISCH_THEN(X_CHOOSE_THEN `ww:complex` MP_TAC) THEN
        STRIP_TAC THEN EXISTS_TAC `norm((g:complex->complex) ww)` THEN
        ASM_SIMP_TAC[ALWAYS_EVENTUALLY; COMPLEX_NORM_NZ] THEN
        DISCH_THEN(ASSUME_TAC o REWRITE_RULE[COMPLEX_NORM_ZERO]) THEN
        UNDISCH_TAC `!w. w IN ball(z0,r) ==> g w = (w - z0) pow m * h w` THEN
        DISCH_THEN(MP_TAC o SPEC `ww:complex`) THEN
        CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
        ASM_SIMP_TAC[COMPLEX_ENTIRE; COMPLEX_POW_EQ_0] THEN
        REWRITE_TAC[IN_BALL; GSYM COMPLEX_NORM_ZERO] THEN
        ASM_REWRITE_TAC[ONCE_REWRITE_RULE[DIST_SYM] dist] THEN
        ASM_REAL_ARITH_TAC];
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o SPECL
       [`cball(z0:complex,&3 * r / &4)`; `r / &4 * e / &2`]) THEN
      REWRITE_TAC[COMPACT_CBALL] THEN ANTS_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
          SUBSET_TRANS)) THEN
        REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL; IN_ELIM_THM] THEN
        UNDISCH_TAC `&0 < r` THEN CONV_TAC NORM_ARITH;
        REWRITE_TAC[GE; EVENTUALLY_SEQUENTIALLY; IN_CBALL; dist] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
        DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
      X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
      MP_TAC(ISPECL
       [`\z. (f:num->complex->complex) n z - g z`;
        `w:complex`; `Cx(&0)`; `r / &4`; `r / &4 * e / &2`; `1`]
        CAUCHY_HIGHER_COMPLEX_DERIVATIVE_BOUND) THEN
      REWRITE_TAC[HIGHER_COMPLEX_DERIVATIVE_1; COMPLEX_IN_BALL_0] THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV] THEN
        REPEAT CONJ_TAC THENL
         [ALL_TAC;
          MATCH_MP_TAC HOLOMORPHIC_ON_IMP_CONTINUOUS_ON;
          X_GEN_TAC `y:complex` THEN REWRITE_TAC[IN_BALL] THEN
          DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          MAP_EVERY UNDISCH_TAC
           [`norm(w - z0:complex) = r / &2`; `dist(w:complex,y) < r / &4`] THEN
          CONV_TAC NORM_ARITH] THEN
        (MATCH_MP_TAC HOLOMORPHIC_ON_SUB THEN
         CONJ_TAC THEN MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
         EXISTS_TAC `s:complex->bool` THEN ASM_REWRITE_TAC[ETA_AX] THEN
         FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
          SUBSET_TRANS)) THEN
         REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL; IN_ELIM_THM] THEN
         UNDISCH_TAC `norm(w - z0:complex) = r / &2` THEN
         UNDISCH_TAC `&0 < r` THEN CONV_TAC NORM_ARITH);
        CONV_TAC NUM_REDUCE_CONV THEN
        ASM_SIMP_TAC[REAL_FIELD
         `&0 < r /\ &0 < e
          ==> &1 * (r / &4 * e / &2) / (r / &4) pow 1 = e / &2`] THEN
        MATCH_MP_TAC(NORM_ARITH
         `x = y /\ &0 < e ==> norm(x) <= e / &2 ==> norm(y) < e`) THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC COMPLEX_DERIVATIVE_SUB THEN CONJ_TAC THEN
        MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT THEN
        EXISTS_TAC `s:complex->bool` THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
        ASM_REWRITE_TAC[IN_BALL; ONCE_REWRITE_RULE[DIST_SYM] dist] THEN
        ASM_REAL_ARITH_TAC];
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`{w:complex | norm(w - z0) = r / &2}`; `e:real`]) THEN
      ASM_REWRITE_TAC[GE; COMPACT_SPHERE; IN_ELIM_THM] THEN
      ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
          SUBSET_TRANS)) THEN
      REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM] THEN
      UNDISCH_TAC `&0 < r` THEN CONV_TAC NORM_ARITH];
    FIRST_ASSUM(ASSUME_TAC o GEN `n:num` o MATCH_MP PATH_INTEGRAL_UNIQUE o
        SPEC `n:num`) THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    ASM_REWRITE_TAC[LIM_CONST_EQ; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    MATCH_MP_TAC(COMPLEX_RING
     `!q r. p = q /\ q = r /\ ~(r = Cx(&0)) ==> ~(Cx(&0) = p)`) THEN
    MAP_EVERY EXISTS_TAC
     [`path_integral (circlepath(z0,r / &2))
                     (\z. Cx(&m) / (z - z0) +
                          complex_derivative h z / h z)`;
      `Cx(&2) * Cx pi * ii * Cx(&m)`] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PATH_INTEGRAL_EQ THEN X_GEN_TAC `w:complex` THEN
      ASM_SIMP_TAC[PATH_IMAGE_CIRCLEPATH; IN_ELIM_THM; REAL_HALF;
                   REAL_LT_IMP_LE] THEN
      ASM_CASES_TAC `w:complex = z0` THEN
      ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THENL
       [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      SUBGOAL_THEN `w IN ball(z0:complex,r)` ASSUME_TAC THENL
       [REWRITE_TAC[IN_BALL] THEN
        MAP_EVERY UNDISCH_TAC [`norm (w - z0) = r / &2`; `&0 < r`] THEN
        CONV_TAC NORM_ARITH;
        ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN
      ASM_SIMP_TAC[COMPLEX_ENTIRE; COMPLEX_POW_EQ_0; COMPLEX_SUB_0;
            COMPLEX_FIELD `~(y = Cx(&0)) ==> (x / y = w <=> x = y * w)`] THEN
      ASM_SIMP_TAC[COMPLEX_FIELD
       `~(h = Cx(&0)) ==> (m * h) * (x + y / h) = m * y + m * h * x`] THEN
      MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
      MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
      EXISTS_TAC `\w:complex. (w - z0) pow m * h w` THEN
      EXISTS_TAC `ball(z0:complex,r)` THEN ASM_SIMP_TAC[OPEN_BALL] THEN
      SUBGOAL_THEN
       `(w - z0) pow m * h w * Cx(&m) / (w - z0) =
        (Cx(&m) * (w - z0) pow (m - 1)) * h w`
      SUBST1_TAC THENL
       [MATCH_MP_TAC(COMPLEX_FIELD
         `w * mm = z /\ ~(w = Cx(&0))
          ==> z * h * m / w = (m * mm) * h`) THEN
        ASM_REWRITE_TAC[COMPLEX_SUB_0; GSYM(CONJUNCT2 complex_pow)] THEN
        AP_TERM_TAC THEN ASM_ARITH_TAC;
        MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_MUL_AT THEN CONJ_TAC THENL
         [COMPLEX_DIFF_TAC THEN CONV_TAC COMPLEX_RING;
          REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
          ASM_MESON_TAC[HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT; OPEN_BALL]]];
      GEN_REWRITE_TAC RAND_CONV [GSYM COMPLEX_ADD_RID] THEN
      MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
      MATCH_MP_TAC HAS_PATH_INTEGRAL_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC CAUCHY_INTEGRAL_CIRCLEPATH_SIMPLE THEN
        ASM_REWRITE_TAC[CENTRE_IN_BALL; REAL_HALF; HOLOMORPHIC_ON_CONST];
        MATCH_MP_TAC CAUCHY_THEOREM_DISC_SIMPLE THEN
        MAP_EVERY EXISTS_TAC [`z0:complex`; `r:real`] THEN
        ASM_SIMP_TAC[VALID_PATH_CIRCLEPATH; PATHSTART_CIRCLEPATH;
                     PATHFINISH_CIRCLEPATH; PATH_IMAGE_CIRCLEPATH;
                     REAL_HALF; REAL_LT_IMP_LE] THEN
        REWRITE_TAC[SUBSET; IN_BALL; ONCE_REWRITE_RULE[DIST_SYM] dist] THEN
        ASM_SIMP_TAC[IN_ELIM_THM; REAL_ARITH `&0 < r ==> r / &2 < r`] THEN
        MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN ASM_REWRITE_TAC[ETA_AX] THEN
        MATCH_MP_TAC HOLOMORPHIC_COMPLEX_DERIVATIVE THEN
        ASM_REWRITE_TAC[OPEN_BALL]];
      REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ; PI_NZ; II_NZ; REAL_OF_NUM_EQ] THEN
      ASM_SIMP_TAC[LE_1; ARITH_EQ] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL]]]);;

let HURWITZ_INJECTIVE = prove
 (`!f:num->complex->complex g s.
    open s /\ connected s /\
    (!n. (f n) holomorphic_on s) /\ g holomorphic_on s /\
    (!k e. compact k /\ k SUBSET s /\ &0 < e
           ==> ?N. !n x. n >= N /\ x IN k ==> norm(f n x - g x) < e) /\
    ~(?c. !z. z IN s ==> g z = c) /\
    (!n w z. w IN s /\ z IN s /\ f n w = f n z ==> w = z)
    ==> (!w z. w IN s /\ z IN s /\ g w = g z ==> w = z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`z1:complex`; `z2:complex`] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
  DISCH_THEN(MP_TAC o SPEC `(g:complex->complex) z2`) THEN
  REWRITE_TAC[] THEN X_GEN_TAC `z0:complex` THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REPEAT DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MESON[]
   `(!x y. x IN s /\ y IN s /\ g x = g y ==> x = y) <=>
    (!x y. x IN s /\ y IN s ==> (g x = g y <=> x = y))`]) THEN
  MP_TAC(ISPECL
   [`\z. (g:complex->complex) z - g z1`; `s:complex->bool`;
    `z2:complex`; `z0:complex`]
        ISOLATED_ZEROS) THEN
  ASM_SIMP_TAC[COMPLEX_SUB_0; HOLOMORPHIC_ON_SUB; HOLOMORPHIC_ON_ID;
               HOLOMORPHIC_ON_CONST] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`\n z. (f:num->complex->complex) n z - f n z1`;
    `\z. (g:complex->complex) z - g z1`; `s DELETE (z1:complex)`]
        HURWITZ_NO_ZEROS) THEN
  REWRITE_TAC[NOT_IMP; COMPLEX_SUB_0] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[OPEN_DELETE];
    ASM_SIMP_TAC[CONNECTED_OPEN_DELETE; DIMINDEX_2; LE_REFL];
    GEN_TAC THEN MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
    EXISTS_TAC `s:complex->bool` THEN
    ASM_SIMP_TAC[HOLOMORPHIC_ON_SUB; ETA_AX; HOLOMORPHIC_ON_CONST] THEN
    SET_TAC[];
    MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
    EXISTS_TAC `s:complex->bool` THEN
    ASM_SIMP_TAC[HOLOMORPHIC_ON_SUB; ETA_AX; HOLOMORPHIC_ON_CONST] THEN
    SET_TAC[];
    MAP_EVERY X_GEN_TAC [`k:complex->bool`; `e:real`] THEN STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP (SET_RULE
     `k SUBSET s DELETE z ==> k SUBSET s`)) THEN
    FIRST_X_ASSUM(fun th ->
     MP_TAC(SPECL [`k:complex->bool`; `e / &2`] th) THEN
     MP_TAC(SPECL [`{z1:complex}`; `e / &2`] th)) THEN
    ASM_REWRITE_TAC[COMPACT_SING; SING_SUBSET; REAL_HALF] THEN
    SIMP_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; IN_SING; FORALL_UNWIND_THM2] THEN
    REWRITE_TAC[IMP_IMP; RIGHT_IMP_FORALL_THM] THEN DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_TAC `N1:num`) (X_CHOOSE_TAC `N2:num`)) THEN
    EXISTS_TAC `MAX N1 N2` THEN REPEAT STRIP_TAC THEN
    UNDISCH_THEN `(g:complex->complex) z1 = g z2` (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(x1 - x2) < e / &2 /\ norm(y1 - y2) < e / &2
      ==> norm(x1 - y1 - (x2 - y2)) < e`) THEN
    ASM_MESON_TAC[ARITH_RULE `x >= MAX m n <=> x >= m /\ x >= n`];
    REWRITE_TAC[IN_DELETE; COMPLEX_EQ_SUB_RADD] THEN DISCH_THEN(CHOOSE_THEN
     (fun th -> MAP_EVERY (MP_TAC o C SPEC th)
                 [`z0:complex`; `z1:complex`; `z2:complex`])) THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[IN_DELETE] THEN ASM_MESON_TAC[];
    REWRITE_TAC[IN_DELETE] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A big chain of equivalents of simple connectedness for an open set.       *)
(* ------------------------------------------------------------------------- *)

let [SIMPLY_CONNECTED_EQ_WINDING_NUMBER_ZERO;
     SIMPLY_CONNECTED_EQ_PATH_INTEGRAL_ZERO;
     SIMPLY_CONNECTED_EQ_GLOBAL_PRIMITIVE;
     SIMPLY_CONNECTED_EQ_HOLOMORPHIC_LOG;
     SIMPLY_CONNECTED_EQ_HOLOMORPHIC_SQRT;
     SIMPLY_CONNECTED_EQ_INJECTIVE_HOLOMORPHIC_SQRT;
     SIMPLY_CONNECTED_EQ_BIHOLOMORPHIC_TO_DISC;
     SIMPLY_CONNECTED_EQ_HOMEOMORPHIC_TO_DISC] =
 (CONJUNCTS o prove)
 (`(!s. open s
        ==> (simply_connected s <=>
             connected s /\
             !g z. path g /\ path_image g SUBSET s /\
                   pathfinish g = pathstart g /\ ~(z IN s)
                   ==> winding_number(g,z) = Cx(&0))) /\
   (!s. open s
        ==> (simply_connected s <=>
             connected s /\
             !g f. valid_path g /\ path_image g SUBSET s /\
                   pathfinish g = pathstart g /\ f holomorphic_on s
                 ==> (f has_path_integral Cx(&0)) g)) /\
   (!s. open s
        ==> (simply_connected s <=>
             connected s /\
             !f. f holomorphic_on s
                 ==> ?h. !z. z IN s
                             ==> (h has_complex_derivative f(z)) (at z))) /\
   (!s. open s
        ==> (simply_connected s <=>
             connected s /\
             !f. f holomorphic_on s /\ (!z. z IN s ==> ~(f z = Cx(&0)))
                 ==> ?g. g holomorphic_on s /\
                         !z. z IN s ==> f z = cexp(g z))) /\
   (!s. open s
        ==> (simply_connected s <=>
             connected s /\
             !f. f holomorphic_on s /\ (!z. z IN s ==> ~(f z = Cx(&0)))
                 ==> ?g. g holomorphic_on s /\
                         !z. z IN s ==> f z = g z pow 2)) /\
   (!s. open s
        ==> (simply_connected s <=>
             connected s /\
             !f. f holomorphic_on s /\ (!z. z IN s ==> ~(f z = Cx(&0))) /\
                 (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
                 ==> ?g. g holomorphic_on s /\
                         !z. z IN s ==> f z = g z pow 2)) /\
   (!s. open s
        ==> (simply_connected s <=>
             s = {} \/ s = (:complex) \/
             ?f g. f holomorphic_on s /\ g holomorphic_on ball(Cx(&0),&1) /\
                   (!z. z IN s ==> f(z) IN ball(Cx(&0),&1) /\ g(f z) = z) /\
                   (!z. z IN ball(Cx(&0),&1) ==> g(z) IN s /\ f(g z) = z))) /\
   (!s. open s
        ==> (simply_connected(s:complex->bool) <=>
             s = {} \/ s homeomorphic ball(Cx(&0),&1)))`,
  REWRITE_TAC[AND_FORALL_THM; TAUT
   `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  X_GEN_TAC `s:complex->bool` THEN DISCH_TAC THEN MATCH_MP_TAC(TAUT
   `(p0 ==> p1) /\ (p1 ==> p2) /\ (p2 ==> p3) /\ (p3 ==> p4) /\
    (p4 ==> p5) /\ (p5 ==> p6) /\ (p6 ==> p7) /\ (p7 ==> p8) /\ (p8 ==> p0)
    ==> (p0 <=> p1) /\ (p0 <=> p2) /\
        (p0 <=> p3) /\ (p0 <=> p4) /\
        (p0 <=> p5) /\ (p0 <=> p6) /\ (p0 <=> p7) /\ (p0 <=> p8)`) THEN
  REPEAT CONJ_TAC THENL
   [SIMP_TAC[SIMPLY_CONNECTED_IMP_CONNECTED] THEN
    MESON_TAC[SIMPLY_CONNECTED_IMP_WINDING_NUMBER_ZERO];

    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CAUCHY_THEOREM_GLOBAL THEN
    EXISTS_TAC `s:complex->bool` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[VALID_PATH_IMP_PATH];

    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `f:complex->complex` THEN
    ASM_CASES_TAC `s:complex->bool = {}` THENL
     [ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN ASM_MESON_TAC[]; DISCH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `a:complex`) THEN EXISTS_TAC
     `\z. path_integral
           (@g. vector_polynomial_function g /\ path_image g SUBSET s /\
                pathstart g = a /\ pathfinish g = z)
           f` THEN
    X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
    DISCH_THEN(MP_TAC o SPEC `x:complex`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[has_complex_derivative] THEN
    REWRITE_TAC[has_derivative_at; LINEAR_COMPLEX_MUL] THEN
    MATCH_MP_TAC LIM_TRANSFORM THEN
    EXISTS_TAC `\y. inv(norm(y - x)) % (path_integral(linepath(x,y)) f -
                     f x * (y - x))` THEN
    REWRITE_TAC[VECTOR_ARITH
     `i % (x - a) - i % (y - (z + a)) = i % (x + z - y)`] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LIM_EVENTUALLY THEN REWRITE_TAC[EVENTUALLY_AT] THEN
      EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `y:complex` THEN STRIP_TAC THEN
      REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ2_TAC THEN MP_TAC(ISPEC
        `s:complex->bool` CONNECTED_OPEN_VECTOR_POLYNOMIAL_CONNECTED) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `a:complex`) THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(y:complex) IN s` ASSUME_TAC THENL
       [ASM_MESON_TAC[SUBSET; IN_CBALL; REAL_LT_IMP_LE; DIST_SYM];
        ALL_TAC] THEN
      DISCH_THEN(fun th ->
        MP_TAC(SPEC `y:complex` th) THEN MP_TAC(SPEC `x:complex` th)) THEN
      ASM_REWRITE_TAC[] THEN MAP_EVERY ABBREV_TAC
       [`g1 = @g. vector_polynomial_function g /\ path_image g SUBSET s /\
                  pathstart g = (a:complex) /\ pathfinish g = x`;
        `g2 = @g. vector_polynomial_function g /\ path_image g SUBSET s /\
                  pathstart g = (a:complex) /\ pathfinish g = y`] THEN
      DISCH_THEN(MP_TAC o SELECT_RULE) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN DISCH_THEN(MP_TAC o SELECT_RULE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`g1 ++ linepath (x:complex,y) ++ reversepath g2`;
        `f:complex->complex`]) THEN
      ASM_REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHFINISH_REVERSEPATH;
                      PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
      SUBGOAL_THEN `segment[x:complex,y] SUBSET s` ASSUME_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x:complex,d)` THEN
        ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
        MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_CBALL] THEN
        REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
        ASM_SIMP_TAC[IN_CBALL; DIST_REFL] THEN
        ASM_MESON_TAC[REAL_LT_IMP_LE; DIST_SYM];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `f path_integrable_on g1 /\ f path_integrable_on g2 /\
        f path_integrable_on linepath(x,y)`
      STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THEN
        MATCH_MP_TAC PATH_INTEGRABLE_HOLOMORPHIC_SIMPLE THEN
        EXISTS_TAC `s:complex->bool` THEN
        ASM_SIMP_TAC[VALID_PATH_VECTOR_POLYNOMIAL_FUNCTION] THEN
        ASM_REWRITE_TAC[VALID_PATH_LINEPATH; PATH_IMAGE_LINEPATH];
        ALL_TAC] THEN
      ANTS_TAC THENL
       [ALL_TAC; DISCH_THEN(MP_TAC o MATCH_MP PATH_INTEGRAL_UNIQUE)] THEN
      ASM_SIMP_TAC[VALID_PATH_JOIN_EQ; PATHSTART_JOIN; PATHFINISH_JOIN;
                   PATHFINISH_REVERSEPATH; PATHSTART_LINEPATH;
                   PATHFINISH_LINEPATH; VALID_PATH_VECTOR_POLYNOMIAL_FUNCTION;
                   PATH_IMAGE_JOIN; PATH_IMAGE_LINEPATH;
                   PATH_IMAGE_REVERSEPATH; PATHSTART_REVERSEPATH;
                   VALID_PATH_LINEPATH; VALID_PATH_REVERSEPATH; UNION_SUBSET;
                   PATH_INTEGRAL_JOIN; PATH_INTEGRABLE_JOIN;
                   PATH_INTEGRABLE_REVERSEPATH; PATH_INTEGRAL_REVERSEPATH] THEN
      REWRITE_TAC[COMPLEX_VEC_0] THEN CONV_TAC COMPLEX_RING;
      REWRITE_TAC[LIM_AT] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(f:complex->complex) continuous at x` MP_TAC THENL
       [ASM_MESON_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON;
                      CONTINUOUS_ON_EQ_CONTINUOUS_AT];
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
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `s:complex->bool` THEN CONJ_TAC THENL
         [ASM_MESON_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON;
                        CONTINUOUS_ON_EQ_CONTINUOUS_AT];
          MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC `ball(x:complex,d2)` THEN CONJ_TAC THENL
           [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
            MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_BALL] THEN
            REWRITE_TAC[SUBSET; IN_BALL; IN_INSERT; NOT_IN_EMPTY; dist] THEN
            REPEAT STRIP_TAC THEN
            ASM_REWRITE_TAC[dist; NORM_0; VECTOR_SUB_REFL] THEN
            ASM_MESON_TAC[NORM_SUB];
            ASM_REWRITE_TAC[SUBSET; dist; IN_BALL]]];
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
      X_GEN_TAC `w:complex` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[REAL_LET_TRANS; SEGMENT_BOUND]];

    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `f:complex->complex` THEN
    ASM_CASES_TAC `s:complex->bool = {}` THENL
     [ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN ASM_MESON_TAC[]; STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `\z. complex_derivative f z / f z`) THEN
    ASM_SIMP_TAC[HOLOMORPHIC_COMPLEX_DERIVATIVE;
                 HOLOMORPHIC_ON_DIV; ETA_AX] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:complex->complex` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`\z:complex. cexp(g z) / f z`; `s:complex->bool`]
        HAS_COMPLEX_DERIVATIVE_ZERO_CONNECTED_CONSTANT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `Cx(&0) = ((complex_derivative f z / f z * cexp (g z)) * f z -
                  cexp (g z) * complex_derivative f z) / f z pow 2`
      SUBST1_TAC THENL
       [ASM_SIMP_TAC[COMPLEX_FIELD
         `~(z = Cx(&0)) ==> (d / z * e) * z = e * d`] THEN
        SIMPLE_COMPLEX_ARITH_TAC;
        MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DIV_AT THEN
        ASM_SIMP_TAC[] THEN CONJ_TAC THENL
         [GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM o_DEF] THEN
          ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
          MATCH_MP_TAC COMPLEX_DIFF_CHAIN_AT THEN
          ASM_SIMP_TAC[HAS_COMPLEX_DERIVATIVE_CEXP];
          ASM_MESON_TAC[HOLOMORPHIC_ON_OPEN; complex_differentiable;
                        HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE]]];
      DISCH_THEN(X_CHOOSE_THEN `c:complex` MP_TAC) THEN
      ASM_CASES_TAC `c = Cx(&0)` THENL
       [ASM_SIMP_TAC[CEXP_NZ; COMPLEX_FIELD
         `~(x = Cx(&0)) /\ ~(y = Cx(&0)) ==> ~(x / y = Cx(&0))`] THEN
        ASM_MESON_TAC[];
      ASM_SIMP_TAC[COMPLEX_FIELD
       `~(y = Cx(&0)) /\ ~(z = Cx(&0))
        ==> (x / y = z <=> y = inv(z) * x)`] THEN
      DISCH_TAC THEN EXISTS_TAC `\z:complex. clog(inv c) + g z` THEN
      ASM_SIMP_TAC[CEXP_CLOG; CEXP_ADD; COMPLEX_INV_EQ_0] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_ADD THEN
      REWRITE_TAC[HOLOMORPHIC_ON_CONST] THEN
      ASM_MESON_TAC[HOLOMORPHIC_ON_OPEN]]];

    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `f:complex->complex` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `f:complex->complex`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:complex->complex` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\z:complex. cexp(g z / Cx(&2))` THEN
    ASM_SIMP_TAC[GSYM CEXP_N; COMPLEX_RING `Cx(&2) * z / Cx(&2) = z`] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN
    REWRITE_TAC[HOLOMORPHIC_ON_CEXP] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN
    ASM_SIMP_TAC[HOLOMORPHIC_ON_CONST] THEN
    CONV_TAC COMPLEX_RING;

    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_FORALL THEN MESON_TAC[];

    POP_ASSUM MP_TAC THEN SPEC_TAC(`s:complex->bool`,`s:complex->bool`) THEN
    REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC; FORALL_AND_THM] THEN
    SUBGOAL_THEN
     `!s:complex->bool.
          open s /\ connected s /\ Cx(&0) IN s /\ s SUBSET ball(Cx(&0),&1) /\
          (!f. f holomorphic_on s /\ (!z. z IN s ==> ~(f z = Cx(&0))) /\
               (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
               ==> ?g. g holomorphic_on s /\ (!z. z IN s ==> f z = g z pow 2))
          ==> ?f g. f holomorphic_on s /\
                    g holomorphic_on ball(Cx(&0),&1) /\
                    (!z. z IN s ==> f z IN ball(Cx(&0),&1) /\ g(f z) = z) /\
                    (!z. z IN ball(Cx(&0),&1) ==> g z IN s /\ f(g z) = z)`
    ASSUME_TAC THENL
     [ALL_TAC;
      REPEAT STRIP_TAC THEN
      ASM_CASES_TAC `s:complex->bool = {}` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `s = (:complex)` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `?a b:complex. a IN s /\ ~(b IN s)` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN
       `?f. f holomorphic_on s /\
            f(a) = Cx(&0) /\
            IMAGE f s SUBSET ball(Cx(&0),&1) /\
            (!w z. w IN s /\ z IN s /\ f w = f z ==> w = z)`
      MP_TAC THENL
       [FIRST_X_ASSUM(K ALL_TAC o SPEC `(:complex)`) THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `\z:complex. z - b`) THEN ANTS_TAC THENL
         [SIMP_TAC[HOLOMORPHIC_ON_SUB; HOLOMORPHIC_ON_CONST; HOLOMORPHIC_ON_ID;
                   COMPLEX_RING `x - b:complex = y - b <=> x = y`] THEN
          ASM_MESON_TAC[COMPLEX_SUB_0];
         ALL_TAC] THEN
        REWRITE_TAC[COMPLEX_EQ_SUB_RADD] THEN
        DISCH_THEN(X_CHOOSE_THEN `g:complex->complex` STRIP_ASSUME_TAC) THEN
        MP_TAC(ISPECL [`s:complex->bool`; `g:complex->complex`]
          OPEN_MAPPING_THM) THEN ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
        DISCH_THEN(MP_TAC o SPEC `a:complex`) THEN ASM_REWRITE_TAC[SUBSET] THEN
        DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN ANTS_TAC THENL
         [SUBGOAL_THEN `a IN ball(a,d) /\ (a + Cx(d / &2)) IN ball(a,d) /\
                        ~(a + Cx(d / &2) = a)`
          MP_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
          ASM_REWRITE_TAC[CENTRE_IN_BALL;
                          COMPLEX_EQ_ADD_LCANCEL_0; CX_INJ] THEN
          REWRITE_TAC[IN_BALL; NORM_ARITH `dist(a,a + d) = norm d`] THEN
          REWRITE_TAC[COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPEC `ball(a:complex,d)`) THEN
        ASM_REWRITE_TAC[OPEN_BALL] THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
        DISCH_THEN(MP_TAC o SPEC `(g:complex->complex) a`) THEN
        ASM_SIMP_TAC[FUN_IN_IMAGE; CENTRE_IN_BALL] THEN
        DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `!z:complex. z IN s ==> ~(g(z) IN ball(--(g a),r))`
        MP_TAC THENL
         [REWRITE_TAC[IN_BALL] THEN X_GEN_TAC `z:complex` THEN
          REPEAT DISCH_TAC THEN
          FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
          DISCH_THEN(MP_TAC o SPEC `--((g:complex->complex) z)`) THEN
          ASM_REWRITE_TAC[IN_BALL; NORM_ARITH `dist(w,--z) = dist(--w,z)`] THEN
          REWRITE_TAC[IN_IMAGE; NOT_EXISTS_THM] THEN X_GEN_TAC `w:complex` THEN
          ASM_CASES_TAC `w:complex = z` THENL
           [ASM_REWRITE_TAC[COMPLEX_RING `--z = z <=> z = Cx(&0)`] THEN
            ASM_MESON_TAC[COMPLEX_RING `Cx(&0) pow 2 + b = b`];
            ASM_MESON_TAC[COMPLEX_RING `(--z:complex) pow 2 = z pow 2`]];
          REWRITE_TAC[IN_BALL; NORM_ARITH `dist(--a,b) = norm(b + a)`] THEN
          ASM_CASES_TAC `!z:complex. z IN s ==> ~(g z + g a = Cx(&0))` THENL
           [REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC;
            ASM_MESON_TAC[COMPLEX_NORM_0]] THEN
          EXISTS_TAC `\z:complex.
            Cx(r / &3) / (g z + g a) - Cx(r / &3) / (g a + g a)` THEN
          REWRITE_TAC[COMPLEX_SUB_REFL] THEN CONJ_TAC THENL
           [MATCH_MP_TAC HOLOMORPHIC_ON_SUB THEN
            REWRITE_TAC[HOLOMORPHIC_ON_CONST] THEN
            MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN
            ASM_SIMP_TAC[HOLOMORPHIC_ON_ADD; HOLOMORPHIC_ON_CONST; ETA_AX];
            ASM_SIMP_TAC[IMP_CONJ; CX_INJ; REAL_LT_IMP_NZ;
             REAL_ARITH `&0 < r ==> ~(r / &3 = &0)`;
             COMPLEX_FIELD
             `~(a = Cx(&0)) /\ ~(x + k = Cx(&0)) /\ ~(y + k = Cx(&0))
              ==> (a / (x + k) - c = a / (y + k) - c <=> x = y)`] THEN
            CONJ_TAC THENL [REWRITE_TAC[dist]; ASM_MESON_TAC[]] THEN
            REWRITE_TAC[FORALL_IN_IMAGE; COMPLEX_SUB_LZERO; NORM_NEG] THEN
            X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
            MATCH_MP_TAC(NORM_ARITH
             `norm(x) <= &1 / &3 /\ norm(y) <= &1 / &3
              ==> norm(x - y) < &1`) THEN
            REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_DIV] THEN
            ASM_SIMP_TAC[real_abs; REAL_LT_IMP_LE; REAL_POS] THEN
            REWRITE_TAC[REAL_ARITH
             `r / &3 / x <= &1 / &3 <=> r / x <= &1`] THEN
            ASM_SIMP_TAC[REAL_LE_LDIV_EQ; NORM_POS_LT; COMPLEX_NORM_NZ] THEN
            ASM_SIMP_TAC[REAL_MUL_LID]]];
        REWRITE_TAC[MESON[]
         `(!x y. P x /\ P y /\ f x = f y ==> x = y) <=>
          (!x y. P x /\ P y ==> (f x = f y <=> x = y))`] THEN
        DISCH_THEN(X_CHOOSE_THEN `h:complex->complex` STRIP_ASSUME_TAC) THEN
        MP_TAC(ISPECL [`h:complex->complex`; `s:complex->bool`]
            HOLOMORPHIC_ON_INVERSE) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
         (X_CHOOSE_THEN `k:complex->complex` STRIP_ASSUME_TAC)) THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (h:complex->complex) s`) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
            ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON];
            ASM SET_TAC[];
            REWRITE_TAC[FORALL_IN_IMAGE]] THEN
          X_GEN_TAC `f:complex->complex` THEN STRIP_TAC THEN
          FIRST_X_ASSUM(MP_TAC o SPEC
           `(f:complex->complex) o (h:complex->complex)`) THEN
          ANTS_TAC THENL
           [CONJ_TAC THENL
             [ASM_MESON_TAC[HOLOMORPHIC_ON_COMPOSE]; ALL_TAC] THEN
            ASM_REWRITE_TAC[o_THM] THEN ASM SET_TAC[];
            ALL_TAC] THEN
          REWRITE_TAC[o_THM] THEN
          DISCH_THEN(X_CHOOSE_THEN `g:complex->complex` STRIP_ASSUME_TAC) THEN
          EXISTS_TAC `(g:complex->complex) o (k:complex->complex)` THEN
          ASM_SIMP_TAC[o_THM] THEN MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN
          ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
           (REWRITE_RULE[IMP_CONJ] HOLOMORPHIC_ON_SUBSET)) THEN ASM SET_TAC[];
          ALL_TAC] THEN
        REWRITE_TAC[FORALL_IN_IMAGE] THEN
        DISCH_THEN(X_CHOOSE_THEN `f:complex->complex`
          (X_CHOOSE_THEN `g:complex->complex` STRIP_ASSUME_TAC)) THEN
        EXISTS_TAC `(f:complex->complex) o (h:complex->complex)` THEN
        EXISTS_TAC `(k:complex->complex) o (g:complex->complex)` THEN
        ASM_SIMP_TAC[o_THM; HOLOMORPHIC_ON_COMPOSE] THEN CONJ_TAC THENL
         [MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE; ASM SET_TAC[]] THEN
        ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
           (REWRITE_RULE[IMP_CONJ] HOLOMORPHIC_ON_SUBSET)) THEN
        ASM SET_TAC[]]] THEN
    X_GEN_TAC `s:complex->bool` THEN STRIP_TAC THEN
    ABBREV_TAC
     `ff = { h | h holomorphic_on s /\
                 IMAGE h s SUBSET ball(Cx(&0),&1) /\
                 h(Cx(&0)) = Cx(&0) /\
                 (!x y. x IN s /\ y IN s ==> (h x = h y <=> x = y))}` THEN
    SUBGOAL_THEN `(\z:complex. z) IN ff` MP_TAC THENL
     [EXPAND_TAC "ff" THEN REWRITE_TAC[IN_ELIM_THM; IMAGE_ID] THEN
      ASM_REWRITE_TAC[HOLOMORPHIC_ON_ID];
      ASM_CASES_TAC `ff:(complex->complex)->bool = {}` THEN
      ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN DISCH_TAC] THEN
    SUBGOAL_THEN `!h. h IN ff ==> h holomorphic_on s` ASSUME_TAC THENL
     [EXPAND_TAC "ff" THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    SUBGOAL_THEN
     `?f:complex->complex.
          f IN ff /\
          (!h. h IN ff
               ==> norm(complex_derivative h (Cx(&0)))
                   <= norm(complex_derivative f (Cx(&0))))`
    MP_TAC THENL
     [MP_TAC(ISPEC
       `{ norm(complex_derivative h (Cx(&0))) | h IN ff}` SUP) THEN
      ANTS_TAC THENL
       [ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
        ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
        FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
        DISCH_THEN(MP_TAC o SPEC `Cx(&0)`) THEN
        ASM_REWRITE_TAC[SUBSET; IN_BALL; COMPLEX_SUB_LZERO;
                        dist; NORM_NEG] THEN
        DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `inv(r):real` THEN X_GEN_TAC `f:complex->complex` THEN
        EXPAND_TAC "ff" THEN
        REWRITE_TAC[IN_ELIM_THM; FORALL_IN_IMAGE; SUBSET] THEN
        ASM_REWRITE_TAC[SUBSET; IN_BALL; COMPLEX_SUB_LZERO;
                        dist; NORM_NEG] THEN
        STRIP_TAC THEN
        MP_TAC(ISPEC `\z. (f:complex->complex) (Cx(r) * z)`
          SCHWARZ_LEMMA) THEN
        ASM_REWRITE_TAC[COMPLEX_MUL_RZERO] THEN
        SUBGOAL_THEN
         `!z. z IN ball(Cx(&0),&1)
              ==> ((\z. f (Cx r * z)) has_complex_derivative
                   complex_derivative f (Cx(r) * z) * Cx(r)) (at z)`
         (LABEL_TAC "*")
        THENL
         [REPEAT STRIP_TAC THEN MATCH_MP_TAC
           (REWRITE_RULE[o_DEF] COMPLEX_DIFF_CHAIN_AT) THEN
          CONJ_TAC THENL
           [COMPLEX_DIFF_TAC THEN REWRITE_TAC[COMPLEX_MUL_RID];
            REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE]] THEN
          MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT THEN
          EXISTS_TAC `s:complex->bool` THEN ASM_REWRITE_TAC[] THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN
          REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
          ASM_SIMP_TAC[real_abs; REAL_LT_IMP_LE] THEN
          GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
          ASM_SIMP_TAC[GSYM COMPLEX_IN_BALL_0; REAL_LT_LMUL_EQ];
          ALL_TAC] THEN
        ANTS_TAC THENL
         [CONJ_TAC THENL
           [REWRITE_TAC[holomorphic_on] THEN
            ASM_MESON_TAC[HAS_COMPLEX_DERIVATIVE_AT_WITHIN];
            REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
            FIRST_X_ASSUM MATCH_MP_TAC THEN
            REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
            ASM_SIMP_TAC[real_abs; REAL_LT_IMP_LE] THEN
            GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
            ASM_SIMP_TAC[GSYM COMPLEX_IN_BALL_0; REAL_LT_LMUL_EQ]];
          REMOVE_THEN "*" (MP_TAC o SPEC `Cx(&0)`) THEN
          REWRITE_TAC[CENTRE_IN_BALL; REAL_LT_01] THEN
          DISCH_THEN(SUBST1_TAC o
            MATCH_MP HAS_COMPLEX_DERIVATIVE_DERIVATIVE) THEN
          DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
          REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_NORM_MUL] THEN
          ASM_SIMP_TAC[COMPLEX_NORM_CX; real_abs; REAL_LT_IMP_LE] THEN
          ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; real_div; REAL_MUL_LID]];
        ALL_TAC] THEN
      ABBREV_TAC
       `l = sup { norm(complex_derivative h (Cx(&0))) | h IN ff}` THEN
      REWRITE_TAC[FORALL_IN_GSPEC] THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `?f. (!n. (f n) IN ff) /\
            ((\n. Cx(norm(complex_derivative (f n) (Cx(&0))))) --> Cx(l))
            sequentially`
      STRIP_ASSUME_TAC THENL
       [SUBGOAL_THEN
         `!n. ?f. f IN ff /\
                  abs(norm(complex_derivative f (Cx (&0))) - l) < inv(&n + &1)`
        MP_TAC THENL
         [X_GEN_TAC `n:num` THEN
          FIRST_ASSUM(MP_TAC o SPEC `l - inv(&n + &1)` o CONJUNCT2) THEN
          REWRITE_TAC[REAL_ARITH `l <= l - i <=> ~(&0 < i)`; REAL_LT_INV_EQ;
             REAL_ARITH `&0 < &n + &1`; NOT_FORALL_THM; NOT_IMP] THEN
          MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:complex->complex` THEN
          ASM_CASES_TAC `(f:complex->complex) IN ff` THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
           `n <= l ==> ~(n <= l - e) ==> abs(n - l) < e`) THEN
          ASM_SIMP_TAC[];
          REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM] THEN
          MATCH_MP_TAC MONO_EXISTS THEN
          X_GEN_TAC `f:num->complex->complex` THEN
          STRIP_TAC THEN ASM_REWRITE_TAC[LIM_SEQUENTIALLY] THEN
          X_GEN_TAC `e:real` THEN
          DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [REAL_ARCH_INV]) THEN
          MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN STRIP_TAC THEN
          X_GEN_TAC `m:num` THEN DISCH_TAC THEN REWRITE_TAC[dist] THEN
          MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `inv(&m + &1)` THEN
          ASM_REWRITE_TAC[COMPLEX_NORM_CX; GSYM CX_SUB] THEN
          MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `inv(&N)` THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
          ASM_REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_ADD] THEN ASM_ARITH_TAC];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`f:num->complex->complex`; `ff:(complex->complex)->bool`;
                     `s:complex->bool`] MONTEL) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [EXPAND_TAC "ff" THEN SIMP_TAC[IN_ELIM_THM] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL; COMPLEX_SUB_LZERO;
                    dist; NORM_NEG] THEN
        MESON_TAC[REAL_LT_IMP_LE];
        ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:complex->complex` THEN
      DISCH_THEN(X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN
       `g complex_differentiable (at(Cx(&0))) /\
        norm(complex_derivative g (Cx(&0))) = l`
      STRIP_ASSUME_TAC THENL
       [MP_TAC(ISPECL [`(f:num->complex->complex) o (r:num->num)`;
                       `(\n:num z. complex_derivative (f n) z) o (r:num->num)`;
                       `g:complex->complex`; `s:complex->bool`]
                    HAS_COMPLEX_DERIVATIVE_UNIFORM_SEQUENCE) THEN
        ASM_REWRITE_TAC[o_THM] THEN ANTS_TAC THENL
         [CONJ_TAC THENL
           [REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
            REPEAT STRIP_TAC THEN
            MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT THEN
            EXISTS_TAC `s:complex->bool` THEN ASM_SIMP_TAC[];
            ALL_TAC] THEN
          X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
          FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
          DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
          STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:real` THEN
          DISCH_TAC THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
          FIRST_X_ASSUM(MP_TAC o SPECL [`cball(z:complex,d)`; `e:real`]) THEN
          ASM_REWRITE_TAC[COMPACT_CBALL; GE] THEN
          MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[];
          DISCH_THEN(X_CHOOSE_THEN `g':complex->complex` MP_TAC) THEN
          DISCH_THEN(MP_TAC o SPEC `Cx(&0)`) THEN
          ASM_REWRITE_TAC[IMP_CONJ_ALT] THEN
          DISCH_THEN(MP_TAC o ISPEC `\z:complex. Cx(norm z)` o MATCH_MP
           (REWRITE_RULE[IMP_CONJ_ALT] LIM_CONTINUOUS_FUNCTION)) THEN
          REWRITE_TAC[CONTINUOUS_AT_CX_NORM] THEN DISCH_TAC THEN DISCH_TAC THEN
          CONJ_TAC THENL [ASM_MESON_TAC[complex_differentiable]; ALL_TAC] THEN
          GEN_REWRITE_TAC I [GSYM CX_INJ] THEN
          FIRST_ASSUM(SUBST1_TAC o
            MATCH_MP HAS_COMPLEX_DERIVATIVE_DERIVATIVE) THEN
          MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN EXISTS_TAC
           `\n. Cx(norm(complex_derivative(f((r:num->num) n)) (Cx (&0))))` THEN
          ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN MP_TAC(ISPECL
           [`\n:num. Cx(norm(complex_derivative (f n) (Cx (&0))))`;
            `r:num->num`; `Cx l`] LIM_SUBSEQUENCE) THEN
          ASM_REWRITE_TAC[o_DEF]];
        ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN
      SUBGOAL_THEN `~(?c. !z. z IN s ==> (g:complex->complex) z = c)`
      ASSUME_TAC THENL
       [DISCH_THEN(X_CHOOSE_TAC `c:complex`) THEN
        SUBGOAL_THEN `complex_derivative g (Cx(&0)) = Cx(&0)` MP_TAC THENL
         [MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
          MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
          MAP_EVERY EXISTS_TAC
           [`(\z. c):complex->complex`; `s:complex->bool`] THEN
          ASM_REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_CONST] THEN ASM_MESON_TAC[];
          DISCH_THEN(MP_TAC o AP_TERM `norm:complex->real`) THEN
          ASM_REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
          DISCH_THEN SUBST_ALL_TAC THEN
          FIRST_ASSUM(MP_TAC o SPEC `\z:complex. z` o CONJUNCT1) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          REWRITE_TAC[COMPLEX_DERIVATIVE_ID; COMPLEX_NORM_CX] THEN
          REAL_ARITH_TAC];
        ALL_TAC] THEN
      EXPAND_TAC "ff" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; COMPLEX_IN_BALL_0] THEN
        SUBGOAL_THEN `!z. z IN s ==> norm((g:complex->complex) z) <= &1`
        ASSUME_TAC THENL
         [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
          MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
          EXISTS_TAC `\n:num. (f:num->complex->complex) (r n) z` THEN
          ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
          MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
          SUBGOAL_THEN
           `(f:num->complex->complex) (r(n:num)) IN ff`
          MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          EXPAND_TAC "ff" THEN REWRITE_TAC[IN_ELIM_THM] THEN
          ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; COMPLEX_IN_BALL_0;
                       REAL_LT_IMP_LE];
          X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
          ASM_SIMP_TAC[REAL_LT_LE] THEN DISCH_TAC THEN MP_TAC(ISPECL
           [`g:complex->complex`; `s:complex->bool`; `s:complex->bool`;
            `z:complex`] MAXIMUM_MODULUS_PRINCIPLE) THEN
          ASM_REWRITE_TAC[SUBSET_REFL]];
        MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
        EXISTS_TAC `\n:num. (f:num->complex->complex) (r n) (Cx(&0))` THEN
        ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
        MATCH_MP_TAC LIM_EVENTUALLY THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
        X_GEN_TAC `n:num` THEN
        SUBGOAL_THEN `(f:num->complex->complex) (r(n:num)) IN ff`
        MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        EXPAND_TAC "ff" THEN SIMP_TAC[IN_ELIM_THM];
        MATCH_MP_TAC(REWRITE_RULE
         [MESON[] `(!x y. P x /\ P y /\ f x = f y ==> x = y) <=>
                   (!x y. P x /\ P y ==> (f x = f y <=> x = y))`]
         HURWITZ_INJECTIVE) THEN
        EXISTS_TAC `(f:num->complex->complex) o (r:num->num)` THEN
        ASM_SIMP_TAC[o_THM] THEN X_GEN_TAC `n:num` THEN
        SUBGOAL_THEN `(f:num->complex->complex) (r(n:num)) IN ff`
        MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        EXPAND_TAC "ff" THEN SIMP_TAC[IN_ELIM_THM]];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:complex->complex` THEN
    STRIP_TAC THEN
    MP_TAC(SPECL [`f:complex->complex`; `s:complex->bool`]
          HOLOMORPHIC_ON_INVERSE) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `(f:complex->complex) IN ff` THEN EXPAND_TAC "ff" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:complex->complex` THEN
    ASM_CASES_TAC `IMAGE (f:complex->complex) s = ball(Cx(&0),&1)` THENL
     [ASM_SIMP_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN
    UNDISCH_TAC `~(IMAGE (f:complex->complex) s = ball(Cx(&0),&1))` THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [UNDISCH_TAC `(f:complex->complex) IN ff` THEN EXPAND_TAC "ff" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; COMPLEX_IN_BALL_0] THEN
    X_GEN_TAC `a:complex` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_IMAGE; MESON[]
      `(?x. a = f x /\ x IN s) <=> ~(!x. x IN s ==> ~(f x = a))`] THEN
    DISCH_TAC THEN
    MP_TAC(ISPEC `a:complex` BALL_BIHOLOMORPHISM_EXISTS) THEN
    ASM_REWRITE_TAC[COMPLEX_IN_BALL_0; NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`t:complex->complex`; `t':complex->complex`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `!z. z IN s ==> norm((f:complex->complex) z) < &1`
    ASSUME_TAC THENL
     [UNDISCH_TAC `(f:complex->complex) IN ff` THEN EXPAND_TAC "ff" THEN
      SIMP_TAC[IN_ELIM_THM; SUBSET; FORALL_IN_IMAGE; COMPLEX_IN_BALL_0];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?sq. sq holomorphic_on (IMAGE (t o f) s) /\
           !z. z IN s
               ==> sq((t:complex->complex) ((f:complex->complex) z)) pow 2 =
                   t(f z)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC
       `!f. f holomorphic_on s /\ (!z. z IN s ==> ~(f z = Cx (&0))) /\
            (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
            ==> ?g. g holomorphic_on s /\
                    (!z. z IN s ==> f z = g z pow 2)` THEN
      DISCH_THEN(MP_TAC o SPEC
       `(t:complex->complex) o (f:complex->complex)`) THEN
      ASM_REWRITE_TAC[FORALL_IN_IMAGE; o_THM] THEN ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN ASM_SIMP_TAC[] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
           (REWRITE_RULE[IMP_CONJ] HOLOMORPHIC_ON_SUBSET)) THEN
          UNDISCH_TAC `(f:complex->complex) IN ff` THEN EXPAND_TAC "ff" THEN
          REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
          UNDISCH_TAC `(f:complex->complex) IN ff` THEN EXPAND_TAC "ff" THEN
          REWRITE_TAC[IN_ELIM_THM; SUBSET; FORALL_IN_IMAGE] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; COMPLEX_IN_BALL_0]) THEN
          REWRITE_TAC[COMPLEX_IN_BALL_0] THEN STRIP_TAC THEN
          GEN_TAC THEN DISCH_TAC THEN
          DISCH_THEN(MP_TAC o AP_TERM `t':complex->complex`) THEN
          ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
          UNDISCH_TAC `(f:complex->complex) IN ff` THEN EXPAND_TAC "ff" THEN
          REWRITE_TAC[IN_ELIM_THM] THEN
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; COMPLEX_IN_BALL_0] THEN
          REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
          REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN ASM_MESON_TAC[]];
        DISCH_THEN(X_CHOOSE_THEN `q:complex->complex` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `(q:complex->complex) o (g:complex->complex) o
                    (t':complex->complex)` THEN
        ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
         [MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN CONJ_TAC THENL
           [MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN CONJ_TAC;
            ALL_TAC] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
           (REWRITE_RULE[IMP_CONJ] HOLOMORPHIC_ON_SUBSET)) THEN
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; COMPLEX_IN_BALL_0; o_THM] THENL
           [ASM_MESON_TAC[]; ASM SET_TAC[]; ASM_MESON_TAC[]];
          X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
          MATCH_MP_TAC EQ_TRANS THEN
          EXISTS_TAC `(q:complex->complex) z pow 2` THEN
          CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
          AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
          UNDISCH_TAC `(f:complex->complex) IN ff` THEN EXPAND_TAC "ff" THEN
          REWRITE_TAC[IN_ELIM_THM; SUBSET; FORALL_IN_IMAGE] THEN
          REWRITE_TAC[COMPLEX_IN_BALL_0] THEN ASM_MESON_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!z. z IN s
          ==> norm((sq:complex->complex)
                   ((t:complex->complex)((f:complex->complex) z))) < &1`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ABS_NORM] THEN
      REWRITE_TAC[GSYM ABS_SQUARE_LT_1; GSYM COMPLEX_NORM_POW] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC
     `(sq:complex->complex)
      ((t:complex->complex)((f:complex->complex) (Cx(&0))))`
      BALL_BIHOLOMORPHISM_EXISTS) THEN
    ASM_SIMP_TAC[COMPLEX_IN_BALL_0; NOT_IMP; NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`r:complex->complex`; `r':complex->complex`] THEN
    STRIP_TAC THEN UNDISCH_TAC
     `!h. h IN ff
          ==> norm(complex_derivative h (Cx (&0))) <=
              norm(complex_derivative f (Cx (&0)))` THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC
     `(r:complex->complex) o (sq:complex->complex) o
      (t:complex->complex) o (f:complex->complex)` th) THEN
     MP_TAC(SPEC `\z:complex. z` th)) THEN
    ASM_REWRITE_TAC[COMPLEX_DERIVATIVE_ID; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
    DISCH_TAC THEN REWRITE_TAC[NOT_IMP; REAL_NOT_LE] THEN
    EXPAND_TAC "ff" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN REPEAT CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
           (REWRITE_RULE[IMP_CONJ] HOLOMORPHIC_ON_SUBSET)) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM; COMPLEX_IN_BALL_0] THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM; COMPLEX_IN_BALL_0] THEN
      ASM_SIMP_TAC[];
      ASM_SIMP_TAC[o_THM];
      MAP_EVERY X_GEN_TAC [`w:complex`; `z:complex`] THEN STRIP_TAC THEN
      EQ_TAC THEN SIMP_TAC[] THEN
      DISCH_THEN(MP_TAC o AP_TERM `r':complex->complex`) THEN
      ASM_SIMP_TAC[o_THM] THEN
      DISCH_THEN(MP_TAC o AP_TERM `\z:complex. z pow 2`) THEN
      ASM_SIMP_TAC[] THEN
      DISCH_THEN(MP_TAC o AP_TERM `t':complex->complex`) THEN
      ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
      STRIP_TAC] THEN
    MP_TAC(ISPEC
     `(t':complex->complex) o (\z. z pow 2) o (r':complex->complex)`
     SCHWARZ_LEMMA) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REPEAT(MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN CONJ_TAC) THEN
        SIMP_TAC[HOLOMORPHIC_ON_POW; HOLOMORPHIC_ON_ID] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
           (REWRITE_RULE[IMP_CONJ] HOLOMORPHIC_ON_SUBSET)) THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM; COMPLEX_IN_BALL_0] THEN
        ASM_SIMP_TAC[COMPLEX_NORM_POW; ABS_SQUARE_LT_1; REAL_ABS_NORM];
        ASM_SIMP_TAC[COMPLEX_NORM_POW; ABS_SQUARE_LT_1; REAL_ABS_NORM; o_THM];
        UNDISCH_THEN `(r:complex->complex) ((sq:complex->complex)
                      ((t:complex->complex) (f(Cx(&0))))) = Cx (&0)`
         (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
        ASM_SIMP_TAC[o_THM] THEN
        UNDISCH_TAC `(f:complex->complex) IN ff` THEN EXPAND_TAC "ff" THEN
        SIMP_TAC[IN_ELIM_THM]];
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN MATCH_MP_TAC
       (TAUT `~r /\ (p /\ ~q ==> s) ==> p /\ (q' \/ q ==> r) ==> s`) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `c:complex` THEN
        ASM_CASES_TAC `c = Cx(&0)` THEN
        ASM_SIMP_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM; REAL_OF_NUM_EQ; ARITH] THEN
        DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
        DISCH_THEN(fun th ->
          MP_TAC(ISPEC `(r:complex->complex) (--(Cx(&1) / Cx(&2)))` th) THEN
          MP_TAC(ISPEC `(r:complex->complex) (Cx(&1) / Cx(&2))` th)) THEN
        MATCH_MP_TAC(TAUT `(p1 /\ p2) /\ (q1 /\ q2 ==> r)
                           ==> (p1 ==> q1) ==> (p2 ==> q2) ==> r`) THEN
        CONJ_TAC THENL
         [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; NORM_NEG] THEN
          REAL_ARITH_TAC;
          ALL_TAC] THEN
        MATCH_MP_TAC(MESON[]
         `~(b1 = b2) /\ a1 = a2 ==> (a1 = b1 /\ a2 = b2 ==> F)`) THEN
        CONJ_TAC THENL
         [ASM_REWRITE_TAC[COMPLEX_EQ_MUL_LCANCEL] THEN
          DISCH_THEN(MP_TAC o AP_TERM `r':complex->complex`) THEN
          FIRST_ASSUM(fun th ->
            W(MP_TAC o PART_MATCH (lhand o rand) th o
               lhand o lhand o snd)) THEN
          REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; NORM_NEG] THEN
          CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
          MATCH_MP_TAC(COMPLEX_RING
           `x = --(Cx(&1) / Cx(&2)) ==> ~(Cx(&1) / Cx(&2) = x)`) THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN
          REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; NORM_NEG] THEN
          CONV_TAC REAL_RAT_REDUCE_CONV;
          REWRITE_TAC[o_DEF] THEN AP_TERM_TAC THEN
          MATCH_MP_TAC(COMPLEX_RING
           `x = Cx(&1) / Cx(&2) /\ y = --(Cx(&1) / Cx(&2))
            ==> x pow 2 = y pow 2`) THEN
          CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; NORM_NEG] THEN
          CONV_TAC REAL_RAT_REDUCE_CONV];
        REWRITE_TAC[GSYM REAL_LT_LE] THEN DISCH_TAC THEN
        UNDISCH_TAC `&1 <= norm (complex_derivative f (Cx (&0)))` THEN
        SUBGOAL_THEN
         `complex_derivative f (Cx (&0)) =
          complex_derivative (t' o (\z:complex. z pow 2) o r') (Cx(&0)) *
          complex_derivative
            (r o (sq:complex->complex) o (t:complex->complex) o f) (Cx(&0))`
         (fun th -> REWRITE_TAC[th; COMPLEX_NORM_MUL])
        THENL
         [ALL_TAC;
          REWRITE_TAC[REAL_ARITH `a * b < b <=> &0 < (&1 - a) * b`] THEN
          DISCH_THEN(MP_TAC o MATCH_MP
           (REAL_ARITH `&1 <= x ==> ~(x = &0)`)) THEN
          SIMP_TAC[REAL_ENTIRE; NORM_EQ_0; GSYM NORM_POS_LT; DE_MORGAN_THM] THEN
          ASM_SIMP_TAC[REAL_LT_MUL_EQ] THEN ASM_REAL_ARITH_TAC] THEN
        MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
        MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
        EXISTS_TAC `((t':complex->complex) o
                     (\z:complex. z pow 2) o (r':complex->complex)) o
                    ((r:complex->complex) o (sq:complex->complex) o
                     (t:complex->complex) o (f:complex->complex))` THEN
        EXISTS_TAC `s:complex->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC COMPLEX_DIFF_CHAIN_AT THEN
        ASM_REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
        CONJ_TAC THEN MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT THENL
         [EXISTS_TAC `s:complex->bool` THEN ASM_REWRITE_TAC[];
          EXISTS_TAC `ball(Cx(&0),&1)` THEN
          ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL; REAL_LT_01] THEN
          REPEAT(MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN CONJ_TAC) THEN
          SIMP_TAC[HOLOMORPHIC_ON_POW; HOLOMORPHIC_ON_ID] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
           (REWRITE_RULE[IMP_CONJ] HOLOMORPHIC_ON_SUBSET)) THEN
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM; COMPLEX_IN_BALL_0] THEN
          ASM_SIMP_TAC[COMPLEX_NORM_POW; ABS_SQUARE_LT_1; REAL_ABS_NORM]]]];
    ASM_CASES_TAC `s:complex->bool = {}` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `s = (:complex)` THEN ASM_REWRITE_TAC[] THENL
     [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
      MATCH_MP_TAC HOMEOMORPHIC_BALL_UNIV THEN REWRITE_TAC[REAL_LT_01];
      REWRITE_TAC[HOMEOMORPHIC_MINIMAL] THEN
      REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
      MESON_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON]];
    STRIP_TAC THEN ASM_REWRITE_TAC[SIMPLY_CONNECTED_EMPTY] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_SIMPLY_CONNECTED_EQ) THEN
    SIMP_TAC[CONVEX_IMP_SIMPLY_CONNECTED; CONVEX_BALL]]);;

(* ------------------------------------------------------------------------- *)
(* A further chain of equivalents about components of the complement of a    *)
(* simply connected set (following 1.35 in Burckel's book).                  *)
(* ------------------------------------------------------------------------- *)

let [SIMPLY_CONNECTED_EQ_FRONTIER_PROPERTIES;
     SIMPLY_CONNECTED_EQ_UNBOUNDED_COMPLEMENT_COMPONENTS;
     SIMPLY_CONNECTED_EQ_EMPTY_INSIDE] = (CONJUNCTS o prove)
 (`(!s:complex->bool.
        open s
        ==> (simply_connected s <=>
             connected s /\
             if bounded s then connected(frontier s)
             else !c. c IN components(frontier s) ==> ~bounded c)) /\
   (!s. open s
        ==> (simply_connected s <=>
             connected s /\
             !c. c IN components ((:complex) DIFF s) ==> ~bounded c)) /\
   (!s:complex->bool.
        open s ==> (simply_connected s <=> connected s /\ inside s = {}))`,
  REWRITE_TAC[AND_FORALL_THM] THEN X_GEN_TAC `s:complex->bool` THEN
  ASM_CASES_TAC `open(s:complex->bool)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT
   `(q3 ==> p) /\ (q2 ==> q3) /\ (q1 ==> q2) /\ (p ==> q1)
    ==> (p <=> q1) /\ (p <=> q2) /\ (p <=> q3)`) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[INSIDE_OUTSIDE] THEN
    REWRITE_TAC[SET_RULE `UNIV DIFF (s UNION t) = {} <=>
                          !x. ~(x IN s) ==> x IN t`] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[SIMPLY_CONNECTED_EQ_WINDING_NUMBER_ZERO] THEN
    GEN_TAC THEN X_GEN_TAC `z:complex` THEN STRIP_TAC THEN
    MATCH_MP_TAC WINDING_NUMBER_ZERO_IN_OUTSIDE THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OUTSIDE_MONO) THEN ASM SET_TAC[];
    REWRITE_TAC[components; FORALL_IN_GSPEC; inside] THEN SET_TAC[];
    ASM_CASES_TAC `connected(s:complex->bool)` THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THENL
     [DISCH_TAC THEN
      REWRITE_TAC[components; FORALL_IN_GSPEC; IN_DIFF; IN_UNIV] THEN
      ASM_CASES_TAC `s:complex->bool = {}` THEN
      ASM_SIMP_TAC[DIFF_EMPTY; CONNECTED_COMPONENT_EQ_SELF;
                   CONNECTED_UNIV; IN_UNIV; NOT_BOUNDED_UNIV] THEN
      ASM_CASES_TAC `s = (:complex)` THENL
       [ASM_MESON_TAC[NOT_BOUNDED_UNIV]; ALL_TAC] THEN
      X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP OUTSIDE_BOUNDED_NONEMPTY) THEN
      REWRITE_TAC[outside; GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:complex` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN
       `connected_component ((:complex) DIFF s) w =
        connected_component ((:complex) DIFF s) z`
       (fun th -> ASM_REWRITE_TAC[th]) THEN
      MATCH_MP_TAC JOINABLE_CONNECTED_COMPONENT_EQ THEN
      EXISTS_TAC `frontier s :complex->bool` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[frontier] THEN MATCH_MP_TAC(SET_RULE
         `i = s ==> s' DIFF i SUBSET UNIV DIFF s`) THEN
        ASM_REWRITE_TAC[INTERIOR_EQ];
        ALL_TAC] THEN
      ONCE_REWRITE_TAC[GSYM FRONTIER_COMPLEMENT] THEN CONJ_TAC THEN
      MATCH_MP_TAC(SET_RULE
       `frontier c SUBSET c /\ frontier c SUBSET f /\ ~(frontier c = {})
        ==> ~(c INTER f = {})`) THEN
      REWRITE_TAC[FRONTIER_OF_CONNECTED_COMPONENT_SUBSET] THEN
      ASM_REWRITE_TAC[FRONTIER_EQ_EMPTY; CONNECTED_COMPONENT_EQ_EMPTY;
                      IN_DIFF; IN_UNIV; CONNECTED_COMPONENT_EQ_UNIV;
                      SET_RULE `UNIV DIFF s = UNIV <=> s = {}`] THEN
      REWRITE_TAC[frontier] THEN MATCH_MP_TAC(SET_RULE
       `c = s ==> c DIFF i SUBSET s`) THEN
      ASM_REWRITE_TAC[CLOSURE_EQ] THEN
      MATCH_MP_TAC CLOSED_CONNECTED_COMPONENT THEN
      ASM_REWRITE_TAC[GSYM OPEN_CLOSED];
      DISCH_TAC THEN REWRITE_TAC[components; FORALL_IN_GSPEC] THEN
      X_GEN_TAC `w:complex` THEN REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN
       `?z:complex. z IN frontier s /\
                    z IN connected_component ((:real^2) DIFF s) w`
      STRIP_ASSUME_TAC THENL
       [ONCE_REWRITE_TAC[GSYM FRONTIER_COMPLEMENT] THEN
        MATCH_MP_TAC(SET_RULE
         `frontier c SUBSET c /\ frontier c SUBSET f /\ ~(frontier c = {})
          ==> ?z. z IN f /\ z IN c`) THEN
        ASM_REWRITE_TAC[FRONTIER_OF_CONNECTED_COMPONENT_SUBSET] THEN
        CONJ_TAC THENL
         [REWRITE_TAC[frontier] THEN MATCH_MP_TAC(SET_RULE
           `c = s ==> c DIFF i SUBSET s`) THEN
          ASM_REWRITE_TAC[CLOSURE_EQ] THEN
          MATCH_MP_TAC CLOSED_CONNECTED_COMPONENT THEN
          ASM_REWRITE_TAC[GSYM OPEN_CLOSED];
          ASM_REWRITE_TAC[FRONTIER_EQ_EMPTY; CONNECTED_COMPONENT_EQ_EMPTY;
                          CONNECTED_COMPONENT_EQ_UNIV; IN_DIFF; IN_UNIV] THEN
          REWRITE_TAC[SET_RULE `UNIV DIFF s = UNIV <=> s = {}`] THEN
          ASM_MESON_TAC[BOUNDED_EMPTY]];
        FIRST_X_ASSUM(MP_TAC o SPEC
         `connected_component (frontier s) (z:complex)`) THEN
        REWRITE_TAC[components; IN_ELIM_THM] THEN
        ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[CONTRAPOS_THM]] THEN
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] BOUNDED_SUBSET) THEN
        SUBGOAL_THEN
         `connected_component ((:complex) DIFF s) w =
          connected_component ((:complex) DIFF s) z`
        SUBST1_TAC THENL
         [ASM_MESON_TAC[CONNECTED_COMPONENT_EQ];
          MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
          ASM_REWRITE_TAC[IN; CONNECTED_COMPONENT_REFL_EQ] THEN
          REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT] THEN
          MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC `frontier s :complex->bool` THEN
          REWRITE_TAC[CONNECTED_COMPONENT_SUBSET] THEN
          REWRITE_TAC[frontier] THEN MATCH_MP_TAC(SET_RULE
            `i = s ==> s' DIFF i SUBSET UNIV DIFF s`) THEN
          ASM_REWRITE_TAC[INTERIOR_EQ]]]];
    ALL_TAC] THEN
  DISCH_THEN(fun th ->
   ASSUME_TAC(MATCH_MP SIMPLY_CONNECTED_IMP_CONNECTED th) THEN MP_TAC th) THEN
  ASM_SIMP_TAC[SIMPLY_CONNECTED_EQ_HOMEOMORPHIC_TO_DISC] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[BOUNDED_EMPTY; FRONTIER_EMPTY; CONNECTED_EMPTY] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; homeomorphism] THEN
  MAP_EVERY X_GEN_TAC [`g:real^2->real^2`; `f:real^2->real^2`] THEN
  STRIP_TAC THEN MAP_EVERY ABBREV_TAC
   [`D = \n. ball(vec 0:real^2,&1 - inv(&n + &2))`;
    `A = \n. {z:real^2 | &1 - inv(&n + &2) < norm z /\ norm z < &1}`;
    `X = \n:num. closure(IMAGE (f:real^2->real^2) (A n))`] THEN
  SUBGOAL_THEN
   `frontier s = INTERS {X n:real^2->bool | n IN (:num)}`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[frontier; INTERIOR_OPEN; INTERS_GSPEC; IN_UNIV] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `x:real^2` THEN
      STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `n:num` THEN
      UNDISCH_TAC `(x:real^2) IN closure s` THEN
      SUBGOAL_THEN
       `s = IMAGE (f:real^2->real^2) (closure (D(n:num))) UNION IMAGE f (A n)`
      SUBST1_TAC THENL
       [EXPAND_TAC "s" THEN MATCH_MP_TAC(SET_RULE
         `t UNION u = s /\ (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
          ==> IMAGE f s = IMAGE f t UNION IMAGE f u`) THEN
        CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
        MAP_EVERY EXPAND_TAC ["A"; "D"] THEN
        SIMP_TAC[CLOSURE_BALL; REAL_SUB_LT; REAL_INV_LT_1;
                 REAL_ARITH `&1 < &n + &2`] THEN
        REWRITE_TAC[EXTENSION; IN_UNION; COMPLEX_IN_BALL_0; IN_CBALL_0;
                   IN_ELIM_THM] THEN GEN_TAC THEN
        MATCH_MP_TAC(REAL_ARITH
         `&0 < e /\ e <= &1
          ==> (x <= &1 - e \/ &1 - e < x /\ x < &1 <=> x < &1)`) THEN
        SIMP_TAC[REAL_LT_INV_EQ; REAL_INV_LE_1; REAL_ARITH `&1 <= &n + &2`;
                 REAL_ARITH `&0 < &n + &2`];
        EXPAND_TAC "X" THEN REWRITE_TAC[CLOSURE_UNION] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `~(x IN s) ==> t SUBSET s ==> x IN t UNION u ==> x IN u`)) THEN
        EXPAND_TAC "D" THEN
        SIMP_TAC[CLOSURE_BALL; REAL_SUB_LT; REAL_INV_LT_1;
                 REAL_ARITH `&1 < &n + &2`; COMPACT_CBALL] THEN
        MATCH_MP_TAC(SET_RULE
         `closure s = s /\ s SUBSET t ==> closure s SUBSET t`) THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CLOSURE_CLOSED THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
          MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
          REWRITE_TAC[COMPACT_CBALL] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP(REWRITE_RULE[IMP_CONJ]
            CONTINUOUS_ON_SUBSET));
          EXPAND_TAC "s" THEN MATCH_MP_TAC IMAGE_SUBSET] THEN
        REWRITE_TAC[SUBSET; COMPLEX_IN_BALL_0; IN_CBALL_0] THEN GEN_TAC THEN
        MATCH_MP_TAC(REAL_ARITH `&0 < x ==> a <= &1 - x ==> a < &1`) THEN
        REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC];
      MATCH_MP_TAC(SET_RULE
       `s SUBSET t /\ s INTER u = {} ==> s SUBSET t DIFF u`) THEN
      CONJ_TAC THENL
       [EXPAND_TAC "X" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        X_GEN_TAC `x:real^2` THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN
        SPEC_TAC(`x:real^2`,`x:real^2`) THEN REWRITE_TAC[GSYM SUBSET] THEN
        MATCH_MP_TAC SUBSET_CLOSURE THEN EXPAND_TAC "s" THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN EXPAND_TAC "A" THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM; COMPLEX_IN_BALL_0] THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
        MAP_EVERY EXPAND_TAC ["s"; "X"] THEN
        REWRITE_TAC[TAUT `~(a /\ b) <=> b ==> ~a`; FORALL_IN_IMAGE] THEN
        X_GEN_TAC `x:real^2` THEN REWRITE_TAC[COMPLEX_IN_BALL_0] THEN
        DISCH_TAC THEN MP_TAC(SPEC `&1 - norm(x:real^2)` REAL_ARCH_INV) THEN
        ASM_REWRITE_TAC[REAL_SUB_LT; NOT_FORALL_THM] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
        MATCH_MP_TAC(SET_RULE
         `!s. y IN s /\ (s INTER t = {}) ==> ~(y IN t)`) THEN
        EXISTS_TAC `IMAGE (f:real^2->real^2) (D(n:num))` THEN CONJ_TAC THENL
         [MATCH_MP_TAC FUN_IN_IMAGE THEN EXPAND_TAC "D" THEN
          REWRITE_TAC[IN_BALL_0] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
           (REAL_ARITH `n < &1 - x ==> m < n ==> x < &1 - m`)) THEN
          MATCH_MP_TAC REAL_LT_INV2 THEN
          ASM_SIMP_TAC[REAL_OF_NUM_LT; LE_1] THEN REAL_ARITH_TAC;
          SUBGOAL_THEN `open(IMAGE (f:real^2->real^2) (D(n:num)))` MP_TAC THENL
           [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN
            SUBGOAL_THEN `(D:num->real^2->bool) n SUBSET ball(Cx(&0),&1)`
            ASSUME_TAC THENL
             [EXPAND_TAC "D" THEN REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
              MATCH_MP_TAC SUBSET_BALL THEN
              REWRITE_TAC[REAL_ARITH `&1 - x <= &1 <=> &0 <= x`] THEN
              REWRITE_TAC[REAL_LE_INV_EQ] THEN REAL_ARITH_TAC;
              REPEAT CONJ_TAC THENL
               [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
                EXPAND_TAC "D" THEN REWRITE_TAC[OPEN_BALL];
                ASM SET_TAC[]]];
            SIMP_TAC[OPEN_INTER_CLOSURE_EQ_EMPTY] THEN DISCH_TAC THEN
            MATCH_MP_TAC(SET_RULE
             `!u. (!x y. x IN u /\ y IN u /\ f x = f y ==> x = y) /\
                  s UNION t SUBSET u /\ s INTER t = {}
                  ==> IMAGE f s INTER IMAGE f t = {}`) THEN
            EXISTS_TAC `ball(Cx(&0),&1)` THEN
            CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
            MAP_EVERY EXPAND_TAC ["D"; "A"] THEN
            REWRITE_TAC[COMPLEX_IN_BALL_0; IN_BALL_0; SUBSET; NOT_IN_EMPTY;
              IN_UNION; IN_ELIM_THM; IN_INTER; EXTENSION] THEN
            CONJ_TAC THENL [GEN_TAC; REAL_ARITH_TAC] THEN
            MATCH_MP_TAC(REAL_ARITH
             `&0 < e ==> x < &1 - e \/ &1 - e < x /\ x < &1 ==> x < &1`) THEN
            REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC]]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. closed((X:num->complex->bool) n)` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN REWRITE_TAC[CLOSED_CLOSURE]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. connected((X:num->complex->bool) n)` ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN EXPAND_TAC "X" THEN
    MATCH_MP_TAC CONNECTED_CLOSURE THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    EXPAND_TAC "A" THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP(REWRITE_RULE[IMP_CONJ]
            CONTINUOUS_ON_SUBSET)) THEN
      SIMP_TAC[SUBSET; COMPLEX_IN_BALL_0; IN_ELIM_THM];
      ONCE_REWRITE_TAC[NORM_ARITH `norm z = norm(z - vec 0)`] THEN
      SIMP_TAC[CONNECTED_ANNULUS; DIMINDEX_2; LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. ((X:num->complex->bool) n) SUBSET closure s`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "X" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_CLOSURE THEN EXPAND_TAC "s" THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN  EXPAND_TAC "A" THEN
    SIMP_TAC[SUBSET; COMPLEX_IN_BALL_0; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m n. m <= n ==> (X:num->complex->bool) n SUBSET X m`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
    EXPAND_TAC "X" THEN MATCH_MP_TAC SUBSET_CLOSURE THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN EXPAND_TAC "A" THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
     `n <= m ==> &1 - n < x /\ x < &1 ==> &1 - m < x /\ x < &1`) THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[REAL_LE_RADD; REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC CONNECTED_NEST THEN
    ASM_REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN
    ASM_MESON_TAC[BOUNDED_SUBSET; BOUNDED_CLOSURE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. ~(bounded((X:num->complex->bool) n))` ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    UNDISCH_TAC `~bounded(s:complex->bool)` THEN EXPAND_TAC "s" THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC
      `IMAGE (f:complex->complex)
             (cball(Cx(&0),&1 - inv(&n + &2)) UNION A n)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IMAGE_UNION; BOUNDED_UNION] THEN CONJ_TAC THENL
       [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
        MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN SIMP_TAC[COMPACT_CBALL] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP(REWRITE_RULE[IMP_CONJ]
            CONTINUOUS_ON_SUBSET)) THEN
        SIMP_TAC[SUBSET; COMPLEX_IN_CBALL_0; COMPLEX_IN_BALL_0] THEN
        GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH
         `&0 < e ==> x <= &1 - e ==> x < &1`) THEN
        ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP(REWRITE_RULE[IMP_CONJ]
              BOUNDED_SUBSET)) THEN EXPAND_TAC "X" THEN
        REWRITE_TAC[CLOSURE_SUBSET]];
      MATCH_MP_TAC IMAGE_SUBSET THEN EXPAND_TAC "A" THEN
      REWRITE_TAC[SUBSET; IN_UNION; COMPLEX_IN_BALL_0; COMPLEX_IN_CBALL_0;
                  IN_ELIM_THM] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `c:complex->bool` THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `closed(INTERS {X n:complex->bool | n IN (:num)})`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[CLOSED_INTERS; FORALL_IN_GSPEC]; ALL_TAC] THEN
  SUBGOAL_THEN `closed(c:complex->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[CLOSED_COMPONENTS]; ALL_TAC] THEN
  SUBGOAL_THEN `compact(c:complex->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?k:complex->bool.
        c SUBSET k /\ compact k /\
        k SUBSET INTERS {X n | n IN (:num)} /\
        closed(INTERS {X n | n IN (:num)} DIFF k)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL[`INTERS {X n:complex->bool | n IN (:num)}`;`c:complex->bool`]
        SURA_BURA_CLOSED) THEN
    ASM_REWRITE_TAC[OPEN_IN_CLOSED_IN_EQ; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    MATCH_MP_TAC(MESON[]
     `~(c = i {}) /\ (~(f = {}) ==> P)
      ==> c = i f ==> P`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[INTERS_0] THEN ASM_MESON_TAC[NOT_BOUNDED_UNIV];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `k:complex->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_MESON_TAC[CLOSED_IN_CLOSED_TRANS]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:complex->bool`;
                 `INTERS {X n:complex->bool | n IN (:num)} DIFF k`]
        SEPARATION_NORMAL_COMPACT) THEN
  ASM_SIMP_TAC[NOT_EXISTS_THM; SET_RULE `k INTER (s DIFF k) = {}`] THEN
  MAP_EVERY X_GEN_TAC [`v:complex->bool`; `v':complex->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `v INTER (INTERS {X n:complex->bool | n IN (:num)} DIFF k) = {}`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`closure(v) DIFF v:complex->bool`;
    `{X n INTER closure(v:complex->bool) | n IN (:num)}`]
   COMPACT_IMP_FIP) THEN
  ASM_SIMP_TAC[COMPACT_DIFF; FORALL_IN_GSPEC; CLOSED_INTER; CLOSED_CLOSURE;
               NOT_IMP] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN
     `INTERS {X n INTER closure v :complex->bool | n IN (:num)} =
      INTERS {X n | n IN (:num)} INTER closure v`
    SUBST1_TAC THENL
     [REWRITE_TAC[INTERS_GSPEC; EXTENSION; IN_ELIM_THM; IN_INTER; IN_UNIV] THEN
      MESON_TAC[];
      MP_TAC(ISPECL [`v':complex->bool`; `v:complex->bool`]
        OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
  REWRITE_TAC[FINITE_SUBSET_IMAGE; SUBSET_UNIV; LEFT_IMP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2] THEN
  X_GEN_TAC `i:num->bool` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `\n:num. n` o MATCH_MP UPPER_BOUND_FINITE_SET) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `i:num->bool = {}` THENL
   [ASM_REWRITE_TAC[IMAGE_CLAUSES; INTERS_0; INTER_UNIV] THEN
    MP_TAC(ISPEC `v:complex->bool` FRONTIER_EQ_EMPTY) THEN
    ASM_SIMP_TAC[frontier; INTERIOR_OPEN] THEN DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_NONEMPTY) THEN
      ASM SET_TAC[];
      ASM_MESON_TAC[CLOSURE_UNIV; COMPACT_IMP_BOUNDED; NOT_BOUNDED_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?n:num. n IN i /\ !m. m IN i ==> m <= n`
   (X_CHOOSE_TAC `p:num`) THENL
   [MAP_EVERY UNDISCH_TAC [`~(i:num->bool = {})`; `FINITE(i:num->bool)`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN SPEC_TAC(`i:num->bool`,`i:num->bool`) THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC[EXISTS_IN_INSERT; FORALL_IN_INSERT; NOT_INSERT_EMPTY] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `i:num->bool`] THEN
    ASM_CASES_TAC `i:num->bool = {}` THEN
    ASM_REWRITE_TAC[LE_REFL; NOT_IN_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC o CONJUNCT1) THEN
    DISJ_CASES_TAC(ARITH_RULE `n:num <= p \/ p <= n`) THEN
    ASM_MESON_TAC[LE_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `INTERS (IMAGE (\n:num. X n INTER closure v) i):complex->bool =
    X p INTER closure v`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; INTERS_IMAGE; IN_ELIM_THM; IN_INTER] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP (SET_RULE
    `(c DIFF v) INTER (x INTER c) = {} ==> x INTER c SUBSET v`)) THEN
  SUBGOAL_THEN `connected((X:num->complex->bool) p)` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[CONNECTED_CLOPEN] THEN
  DISCH_THEN(MP_TAC o SPEC `(X:num->complex->bool) p INTER closure v`) THEN
  REWRITE_TAC[NOT_IMP; DE_MORGAN_THM] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(X:num->complex->bool) p INTER closure v = X p INTER v`
    SUBST1_TAC THENL
     [MP_TAC(ISPEC `v:complex->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[];
      MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN REWRITE_TAC[CLOSED_CLOSURE];
    MATCH_MP_TAC(SET_RULE `!k. k SUBSET s /\ ~(k = {}) ==> ~(s = {})`) THEN
    EXISTS_TAC `k:complex->bool` THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `v:complex->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[];
      FIRST_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_NONEMPTY) THEN
      ASM SET_TAC[]];
    DISCH_THEN(MP_TAC o AP_TERM `bounded:(complex->bool)->bool`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `closure v:complex->bool` THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Yet another set of equivalences based on *continuous* logs and sqrts.     *)
(* ------------------------------------------------------------------------- *)

let SIMPLY_CONNECTED_EQ_CONTINUOUS_LOG,SIMPLY_CONNECTED_EQ_CONTINUOUS_SQRT =
  (CONJ_PAIR o prove)
 (`(!s. open s
        ==> (simply_connected s <=>
             connected s /\
             !f. f continuous_on s /\ (!z:complex. z IN s ==> ~(f z = Cx(&0)))
                 ==> ?g. g continuous_on s /\
                         !z. z IN s ==> f z = cexp(g z))) /\
   (!s. open s
        ==> (simply_connected s <=>
             connected s /\
             !f. f continuous_on s /\ (!z:complex. z IN s ==> ~(f z = Cx(&0)))
                 ==> ?g. g continuous_on s /\
                         !z. z IN s ==> f z = g z pow 2))`,
  REWRITE_TAC[AND_FORALL_THM] THEN X_GEN_TAC `s:complex->bool` THEN
  ASM_CASES_TAC `open(s:complex->bool)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `connected(s:complex->bool)` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; ASM_MESON_TAC[SIMPLY_CONNECTED_IMP_CONNECTED]] THEN
  MATCH_MP_TAC(TAUT
   `(p ==> q) /\ (q ==> r) /\ (r ==> p) ==> (p <=> q) /\ (p <=> r)`) THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[SIMPLY_CONNECTED_EQ_HOMEOMORPHIC_TO_DISC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[CONTINUOUS_ON_EMPTY; NOT_IN_EMPTY] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
    REWRITE_TAC[homeomorphism; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`k:complex->complex`; `h:complex->complex`] THEN
    STRIP_TAC THEN X_GEN_TAC `f:complex->complex` THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`(f:complex->complex) o (h:complex->complex)`; `Cx(&0)`; `&1`]
        CONTINUOUS_LOGARITHM_ON_BALL) THEN
    ASM_REWRITE_TAC[o_THM] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      DISCH_THEN(X_CHOOSE_THEN `g:complex->complex` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(g:complex->complex) o (k:complex->complex)` THEN
      REWRITE_TAC[o_THM] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]];
    DISCH_TAC THEN X_GEN_TAC `f:complex->complex` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `f:complex->complex`) THEN ASM_SIMP_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:complex->complex` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\z:complex. cexp(g z / Cx(&2))` THEN
    ASM_SIMP_TAC[GSYM CEXP_N; COMPLEX_RING `Cx(&2) * z / Cx(&2) = z`] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    REWRITE_TAC[CONTINUOUS_ON_CEXP] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_DIV THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_CONST] THEN
    CONV_TAC COMPLEX_RING;
    DISCH_TAC THEN ASM_SIMP_TAC[SIMPLY_CONNECTED_EQ_HOLOMORPHIC_SQRT] THEN
    X_GEN_TAC `f:complex->complex` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `f:complex->complex`) THEN
    ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:complex->complex` THEN
    STRIP_TAC THEN ASM_SIMP_TAC[HOLOMORPHIC_ON_OPEN] THEN
    X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((g:complex->complex) z = Cx(&0))` ASSUME_TAC THENL
     [ASM_MESON_TAC[COMPLEX_RING `Cx(&0) pow 2 = Cx(&0)`]; ALL_TAC] THEN
    EXISTS_TAC `complex_derivative f z / (Cx(&2) * g z)` THEN
    REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_AT] THEN
    MATCH_MP_TAC LIM_TRANSFORM_WITHIN_OPEN THEN
    EXISTS_TAC `\x:complex. (f(x) - f(z)) / (x - z) / (g(x) + g(z))` THEN
    SUBGOAL_THEN
      `?d. &0 < d /\
           !w:complex. w IN s /\ w IN ball(z,d) ==> ~(g w + g z = Cx(&0))`
    STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC `z:complex` o
      GEN_REWRITE_RULE I [continuous_on]) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `norm((g:complex->complex) z)`) THEN
      ASM_REWRITE_TAC[COMPLEX_NORM_NZ] THEN MATCH_MP_TAC MONO_EXISTS THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN
      REWRITE_TAC[IN_BALL; GSYM COMPLEX_VEC_0] THEN
      MESON_TAC[NORM_ARITH `dist(z,x) < norm z ==> ~(x + z = vec 0)`];
      ALL_TAC] THEN
    EXISTS_TAC `ball(z:complex,d) INTER s` THEN
    ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL] THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL];
      ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC(COMPLEX_FIELD
       `~(x = z) /\ ~(gx + gz = Cx(&0))
        ==> (gx pow 2 - gz pow 2) / (x - z) / (gx + gz) =
             (gx - gz) / (x - z)`) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC LIM_COMPLEX_DIV THEN
      ASM_REWRITE_TAC[COMPLEX_ENTIRE; GSYM HAS_COMPLEX_DERIVATIVE_AT] THEN
      REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE; CX_INJ] THEN
      REWRITE_TAC[COMPLEX_MUL_2; REAL_OF_NUM_EQ; ARITH_EQ] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT]; ALL_TAC] THEN
      MATCH_MP_TAC LIM_ADD THEN REWRITE_TAC[LIM_CONST; GSYM CONTINUOUS_AT] THEN
      ASM_MESON_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON;
                    CONTINUOUS_ON_INTERIOR; INTERIOR_OPEN]]]);;

(* ------------------------------------------------------------------------- *)
(* A per-function version for continuous logs, a kind of monodromy.          *)
(* ------------------------------------------------------------------------- *)

let WINDING_NUMBER_COMPOSE_CEXP = prove
 (`!p. path p
       ==> winding_number(cexp o p,Cx(&0)) =
           Cx(&1) / (Cx(&2) * Cx pi * ii) * (pathfinish p - pathstart p)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?e. &0 < e /\
       !t:real^1. t IN interval[vec 0,vec 1] ==> e <= norm(cexp(p t))`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `setdist({Cx(&0)},path_image (cexp o p))` THEN
    REWRITE_TAC[SETDIST_POS_LE; REAL_ARITH
     `&0 < x <=> &0 <= x /\ ~(x = &0)`] THEN
    ASM_SIMP_TAC[PATH_CONTINUOUS_IMAGE; CONTINUOUS_ON_CEXP; CLOSED_SING;
     SETDIST_EQ_0_CLOSED_COMPACT; COMPACT_PATH_IMAGE; PATH_IMAGE_NONEMPTY] THEN
    REWRITE_TAC[NOT_INSERT_EMPTY; path_image; IMAGE_o] THEN CONJ_TAC THENL
     [MP_TAC CEXP_NZ THEN SET_TAC[]; REPEAT STRIP_TAC] THEN
    ONCE_REWRITE_TAC[GSYM NORM_NEG] THEN
    REWRITE_TAC[COMPLEX_RING `--x = Cx(&0) - x`] THEN
    REWRITE_TAC[GSYM dist] THEN MATCH_MP_TAC SETDIST_LE_DIST THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`path_image(p:real^1->complex)`; `Cx(&0)`]
        BOUNDED_SUBSET_CBALL) THEN
  ASM_SIMP_TAC[BOUNDED_PATH_IMAGE; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `B:real` THEN REWRITE_TAC[SUBSET; COMPLEX_IN_CBALL_0] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`cexp`; `cball(Cx(&0),B + &1)`]
        COMPACT_UNIFORMLY_CONTINUOUS) THEN
  REWRITE_TAC[CONTINUOUS_ON_CEXP; COMPACT_CBALL] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[COMPLEX_IN_CBALL_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`p:real^1->complex`; `min (&1) d`]
      PATH_APPROX_VECTOR_POLYNOMIAL_FUNCTION) THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g:real^1->complex` THEN STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `winding_number(cexp o g,Cx(&0))` THEN CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC WINDING_NUMBER_NEARBY_PATHS_EQ THEN
    ASM_SIMP_TAC[PATH_CONTINUOUS_IMAGE; CONTINUOUS_ON_CEXP;
                 PATH_VECTOR_POLYNOMIAL_FUNCTION] THEN
    ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[COMPLEX_SUB_RZERO; o_THM] THEN
    REWRITE_TAC[GSYM dist] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `e:real` THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[dist] THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(g - p) < &1 /\ norm(p) <= B
      ==> norm(p) <= B + &1 /\ norm(g) <= B + &1`) THEN
    ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[path_image] THEN ASM SET_TAC[];
    W(MP_TAC o
      PART_MATCH (lhs o rand) WINDING_NUMBER_VALID_PATH o lhs o snd) THEN
    REWRITE_TAC[PATH_INTEGRAL_INTEGRAL; COMPLEX_SUB_RZERO] THEN ANTS_TAC THENL
     [REWRITE_TAC[path_image; IN_IMAGE; o_THM; CEXP_NZ] THEN
      REWRITE_TAC[valid_path] THEN
      MATCH_MP_TAC DIFFERENTIABLE_ON_IMP_PIECEWISE_DIFFERENTIABLE THEN
      MATCH_MP_TAC DIFFERENTIABLE_ON_COMPOSE THEN
      REWRITE_TAC[differentiable_on] THEN REPEAT STRIP_TAC THENL
       [MATCH_MP_TAC DIFFERENTIABLE_AT_WITHIN THEN
        REWRITE_TAC[differentiable] THEN
        ASM_MESON_TAC[has_vector_derivative;
                        HAS_VECTOR_DERIVATIVE_VECTOR_POLYNOMIAL_FUNCTION];
        GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
        MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_IMP_DIFFERENTIABLE THEN
        COMPLEX_DIFFERENTIABLE_TAC];
      DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `integral (interval [vec 0,vec 1])
                    (\x. vector_derivative (g:real^1->complex) (at x))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
        REWRITE_TAC[o_THM] THEN MATCH_MP_TAC(COMPLEX_FIELD
         `~(e = Cx(&0)) /\ v' = e * v ==> Cx(&1) / e * v' = v`) THEN
        REWRITE_TAC[CEXP_NZ] THEN
        MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_UNIQUE_AT THEN
        MP_TAC(ISPECL [`g:real^1->complex`; `cexp`;
         `\h. drop h % vector_derivative (g:real^1->complex) (at t)`;
         `\w. cexp(g(t:real^1)) * w`; `t:real^1`]
        DIFF_CHAIN_AT) THEN
        REWRITE_TAC[GSYM has_vector_derivative; GSYM has_complex_derivative;
                    GSYM VECTOR_DERIVATIVE_WORKS;
                    HAS_COMPLEX_DERIVATIVE_CEXP; differentiable] THEN
        ANTS_TAC THENL
         [ASM_MESON_TAC[HAS_VECTOR_DERIVATIVE_VECTOR_POLYNOMIAL_FUNCTION;
                        has_vector_derivative];
          REWRITE_TAC[has_vector_derivative; o_DEF] THEN
          MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
          REWRITE_TAC[FUN_EQ_THM; COMPLEX_CMUL] THEN
          CONV_TAC COMPLEX_RING];
        MP_TAC(ISPECL [`g:real^1->complex`;
                        `\x. vector_derivative (g:real^1->complex) (at x)`;
                       `vec 0:real^1`; `vec 1:real^1`]
          FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
        ASM_REWRITE_TAC[DROP_VEC; REAL_POS] THEN ANTS_TAC THENL
         [REPEAT STRIP_TAC THEN
          MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
          REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS] THEN
          REWRITE_TAC[differentiable] THEN
          ASM_MESON_TAC[has_vector_derivative;
                        HAS_VECTOR_DERIVATIVE_VECTOR_POLYNOMIAL_FUNCTION];
          DISCH_THEN(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
          RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
          ASM_REWRITE_TAC[pathstart; pathfinish]]]]]);;

let MONODROMY_CONTINUOUS_LOG = prove
 (`!f:complex->complex s.
        open s /\ f continuous_on s /\
        (!z. z IN s ==> ~(f z = Cx(&0)))
        ==> ((!p. path p /\ path_image p SUBSET s /\
                  pathfinish p = pathstart p
                  ==> winding_number(f o p,Cx(&0)) = Cx(&0)) <=>
             (?g. g continuous_on s /\ !z. z IN s ==> f(z) = cexp(g z)))`,
  let lemma = prove
   (`!f g s p.
           f continuous_on s /\ g continuous_on s /\
           (!z:complex. z IN s ==> f(z) = cexp(g z)) /\
           path p /\ path_image p SUBSET s
           ==> winding_number(f o p,Cx(&0)) =
               Cx(&1) / (Cx(&2) * Cx pi * ii) *
               (pathfinish(g o p) - pathstart(g o p))`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `winding_number(cexp o g o (p:real^1->complex),Cx(&0))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC WINDING_NUMBER_NEARBY_PATHS_EQ THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
        REWRITE_TAC[CONTINUOUS_ON_CEXP] THEN
        MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
        ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
        MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
        ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
        REWRITE_TAC[PATHSTART_COMPOSE] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_MESON_TAC[SUBSET; PATHSTART_IN_PATH_IMAGE];
        REWRITE_TAC[PATHFINISH_COMPOSE] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_MESON_TAC[SUBSET; PATHFINISH_IN_PATH_IMAGE];
        GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[o_THM; COMPLEX_SUB_RZERO] THEN
        MATCH_MP_TAC(NORM_ARITH
         `x = y /\ ~(z = vec 0) ==> norm(x - y) < norm z`) THEN
        REWRITE_TAC[COMPLEX_VEC_0; CEXP_NZ] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_MESON_TAC[SUBSET; path_image; IN_IMAGE]];
      MATCH_MP_TAC WINDING_NUMBER_COMPOSE_CEXP THEN
      ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN
      MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]]) in
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC;
    DISCH_THEN(X_CHOOSE_THEN `g:complex->complex` STRIP_ASSUME_TAC) THEN
    X_GEN_TAC `p:real^1->complex` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`f:complex->complex`; `g:complex->complex`;
                   `s:complex->bool`; `p:real^1->complex`]
        lemma) THEN
    ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN
    REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_MUL_RZERO]] THEN
  DISCH_TAC THEN
  EXISTS_TAC `\z. let c = connected_component s (z:complex) in
                  let z0 = (@) c in
                  let p = @p. path p /\ path_image p SUBSET c /\
                              pathstart p = z0 /\ pathfinish p = z in
                  Cx(&2) * Cx(pi) * ii * winding_number(f o p,Cx(&0)) +
                  clog(f z0)` THEN

  CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `z:complex` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    REPEAT LET_TAC THEN
    SUBGOAL_THEN `(z:complex) IN c` ASSUME_TAC THENL
     [ASM_MESON_TAC[CONNECTED_COMPONENT_REFL; IN]; ALL_TAC] THEN
    SUBGOAL_THEN `(z0:complex) IN c` ASSUME_TAC THENL
     [EXPAND_TAC "z0" THEN REWRITE_TAC[IN] THEN MATCH_MP_TAC SELECT_AX THEN
      ASM_MESON_TAC[IN];
      ALL_TAC] THEN
    SUBGOAL_THEN `(c:complex->bool) SUBSET s` ASSUME_TAC THENL
     [ASM_MESON_TAC[CONNECTED_COMPONENT_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `connected(c:complex->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[CONNECTED_CONNECTED_COMPONENT]; ALL_TAC] THEN
    SUBGOAL_THEN `open(c:complex->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_CONNECTED_COMPONENT]; ALL_TAC] THEN
    SUBGOAL_THEN `path_connected(c:complex->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[CONNECTED_OPEN_PATH_CONNECTED]; ALL_TAC] THEN
    SUBGOAL_THEN
     `path p /\ path_image p SUBSET c /\
      pathstart p = z0 /\ pathfinish p = (z:complex)`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "p" THEN CONV_TAC SELECT_CONV THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[path_connected]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(f:complex->complex) o (p:real^1->complex)`; `Cx(&0)`]
      WINDING_NUMBER_AHLFORS_FULL) THEN
    REWRITE_TAC[CEXP_ADD] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
        ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
        REWRITE_TAC[path_image; IMAGE_o] THEN
        REWRITE_TAC[GSYM path_image] THEN ASM SET_TAC[]];
      ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN
      REWRITE_TAC[COMPLEX_SUB_RZERO] THEN DISCH_THEN SUBST1_TAC THEN
      AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CEXP_CLOG THEN
      ASM SET_TAC[]]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPONENTS THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `c:complex->bool` THEN DISCH_TAC THEN
  ABBREV_TAC `z0:complex = (@) c` THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  ABBREV_TAC
   `g = \z. let p = @p. path p /\ path_image p SUBSET c /\
                        pathstart p = z0 /\ pathfinish p = z in
            Cx(&2) * Cx(pi) * ii * winding_number(f o p,Cx(&0)) +
            clog(f(z0:complex))` THEN
  EXISTS_TAC `g:complex->complex` THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN EXPAND_TAC "g" THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN EXPAND_TAC "z0" THEN
    SUBGOAL_THEN `connected_component s (z:complex) = c`
     (fun th -> REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_COMPONENTS]) THEN
    ASM_MESON_TAC[CONNECTED_COMPONENT_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z0:complex) IN c` ASSUME_TAC THENL
   [EXPAND_TAC "z0" THEN REWRITE_TAC[IN] THEN MATCH_MP_TAC SELECT_AX THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_NONEMPTY) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:complex->bool) SUBSET s` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `connected(c:complex->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED]; ALL_TAC] THEN
  SUBGOAL_THEN `open(c:complex->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_COMPONENTS]; ALL_TAC] THEN
  SUBGOAL_THEN `path_connected(c:complex->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONNECTED_OPEN_PATH_CONNECTED]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN c
        ==> ?p. path (p:real^1->complex) /\ path_image p SUBSET c /\
                pathstart p = z0 /\ pathfinish p = x /\
                g(x) = Cx(&2) * Cx pi * ii * winding_number(f o p,Cx(&0)) +
                       clog (f z0)`
   (LABEL_TAC "*")
  THENL
   [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN EXPAND_TAC "g" THEN
    ABBREV_TAC `p = @p. path p /\ path_image p SUBSET c /\
                        pathstart p = z0 /\ pathfinish p = (z:complex)` THEN
    EXISTS_TAC `p:real^1->complex` THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN
    EXPAND_TAC "p" THEN CONV_TAC SELECT_CONV THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [path_connected]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `z:complex` o GEN_REWRITE_RULE I
   [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `e:real` THEN
  STRIP_TAC THEN
  MP_TAC(SPEC `ball(z:complex,e)` SIMPLY_CONNECTED_EQ_CONTINUOUS_LOG) THEN
  SIMP_TAC[OPEN_BALL; CONVEX_BALL; CONVEX_IMP_SIMPLY_CONNECTED] THEN
  DISCH_THEN(MP_TAC o SPEC `f:complex->complex` o CONJUNCT2) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET];
    DISCH_THEN(X_CHOOSE_THEN `l:complex->complex` STRIP_ASSUME_TAC)] THEN
  REWRITE_TAC[CONTINUOUS_AT] THEN ONCE_REWRITE_TAC[LIM_NULL] THEN
  MATCH_MP_TAC LIM_TRANSFORM_AT THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN EXISTS_TAC
   `\w. Cx (&2) * Cx pi * ii *
        winding_number((f:complex->complex) o linepath(z,w),Cx(&0))` THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `w:complex` THEN STRIP_TAC THEN REMOVE_THEN "*"
     (fun th -> MP_TAC(SPEC `w:complex` th) THEN
                MP_TAC(SPEC `z:complex` th)) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `p:real^1->complex` THEN STRIP_TAC THEN
    ANTS_TAC THENL [ASM_MESON_TAC[SUBSET; IN_BALL; DIST_SYM]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^1->complex` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(COMPLEX_RING
     `(z + x) - y = Cx(&0)
      ==> a * b * c * x = (a * b * c * y + l) - (a * b * c * z + l)`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
     `p ++ linepath(z:complex,w) ++ reversepath q`) THEN
    ASM_SIMP_TAC[PATHSTART_JOIN; PATHFINISH_JOIN;
                 PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                 PATH_JOIN_EQ; PATH_LINEPATH; PATH_REVERSEPATH;
                 PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_JOIN] THEN
    ASM_REWRITE_TAC[UNION_SUBSET; PATH_IMAGE_REVERSEPATH] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `c:complex->bool` THEN
      ASM_REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(z:complex,e)` THEN
      ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
      ASM_REWRITE_TAC[INSERT_SUBSET; CENTRE_IN_BALL; EMPTY_SUBSET] THEN
      ASM_REWRITE_TAC[IN_BALL; CONVEX_BALL];
      DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
      REWRITE_TAC[PATH_COMPOSE_JOIN; PATH_COMPOSE_REVERSEPATH] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) WINDING_NUMBER_JOIN o
        rand o snd) THEN
      ANTS_TAC THENL
       [ALL_TAC;
        DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[VECTOR_SUB; GSYM VECTOR_ADD_ASSOC] THEN
        AP_TERM_TAC THEN
        W(MP_TAC o PART_MATCH (lhand o rand) WINDING_NUMBER_JOIN o
          rand o snd) THEN
        ANTS_TAC THENL
         [ALL_TAC;
          DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
          MATCH_MP_TAC(GSYM WINDING_NUMBER_REVERSEPATH)]] THEN
      ASM_SIMP_TAC[PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                 PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_REVERSEPATH;
                 PATHSTART_JOIN; PATHFINISH_JOIN; PATH_REVERSEPATH;
                 PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_JOIN;
                 PATH_IMAGE_JOIN; IN_UNION; DE_MORGAN_THM] THEN
      REWRITE_TAC[PATH_IMAGE_COMPOSE; SET_RULE
       `~(z IN IMAGE f s) <=> !x. x IN s ==> ~(f x = z)`] THEN
      REPEAT CONJ_TAC THEN
      ((MATCH_MP_TAC PATH_CONTINUOUS_IMAGE)
       ORELSE
       (X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC)) THEN
      ASM_REWRITE_TAC[PATH_LINEPATH] THEN
      TRY(FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            CONTINUOUS_ON_SUBSET)) THEN
          REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:complex` THEN STRIP_TAC) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
      TRY(FIRST_X_ASSUM(fun th ->
            MATCH_MP_TAC(GEN_REWRITE_RULE I [SUBSET] th) THEN
            FIRST_X_ASSUM ACCEPT_TAC)) THEN
      UNDISCH_TAC `(x:complex) IN path_image(linepath(z,w))` THEN
      SPEC_TAC(`x:complex`,`x:complex`) THEN
      REWRITE_TAC[GSYM SUBSET; PATH_IMAGE_LINEPATH; SEGMENT_CONVEX_HULL] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(z:complex,e)` THEN
      ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
      ASM_REWRITE_TAC[INSERT_SUBSET; CENTRE_IN_BALL; EMPTY_SUBSET] THEN
      ASM_REWRITE_TAC[IN_BALL; CONVEX_BALL]];
    MATCH_MP_TAC LIM_TRANSFORM THEN
    EXISTS_TAC `\w. Cx(&2) * Cx pi * ii *
                    Cx(&1) / (Cx(&2) * Cx pi * ii) *
                    (pathfinish(l o linepath(z:complex,w)) -
                     pathstart (l o linepath(z,w)))` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LIM_EVENTUALLY THEN REWRITE_TAC[EVENTUALLY_AT] THEN
      EXISTS_TAC `e:real` THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:complex` THEN STRIP_TAC THEN
      REWRITE_TAC[VECTOR_ARITH `x - y = vec 0 <=> y = x`] THEN
      REPLICATE_TAC 3 AP_TERM_TAC THEN MATCH_MP_TAC lemma THEN
      EXISTS_TAC `ball(z:complex,e)` THEN ASM_REWRITE_TAC[PATH_LINEPATH] THEN
      CONJ_TAC THENL[ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET]; ALL_TAC] THEN
      REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_CONVEX_HULL] THEN
      MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_BALL] THEN
      ASM_REWRITE_TAC[INSERT_SUBSET; CENTRE_IN_BALL; EMPTY_SUBSET] THEN
      ASM_REWRITE_TAC[IN_BALL];
      REWRITE_TAC[COMPLEX_VEC_0] THEN
      REPEAT(MATCH_MP_TAC LIM_NULL_COMPLEX_LMUL) THEN
      REWRITE_TAC[PATHSTART_COMPOSE; PATHSTART_LINEPATH;
                  PATHFINISH_COMPOSE; PATHFINISH_LINEPATH] THEN
      REWRITE_TAC[GSYM COMPLEX_VEC_0; GSYM LIM_NULL; GSYM CONTINUOUS_AT] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_BALL;
                    CENTRE_IN_BALL]]]);;

(* ------------------------------------------------------------------------- *)
(* The winding number defines a continuous logarithm for the path itself.    *)
(* ------------------------------------------------------------------------- *)

let WINDING_NUMBER_AS_CONTINUOUS_LOGARITHM = prove
 (`!p z.
      path p /\ ~(z IN path_image p)
      ==> ?q. path q /\
              pathfinish q - pathstart q =
              Cx(&2) * Cx pi * ii * winding_number(p,z) /\
              !t. t IN interval[vec 0,vec 1] ==> p(t) = z + cexp(q t)`,
  REPEAT STRIP_TAC THEN EXISTS_TAC
  `\t:real^1. Cx(&2) * Cx pi * ii * winding_number(subpath (vec 0) t p,z) +
              clog(pathstart p - z)` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[path] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    REPEAT(MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
           REWRITE_TAC[CONTINUOUS_ON_CONST]) THEN
    REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((p:real^1->complex) t = z)` ASSUME_TAC THENL
     [ASM_MESON_TAC[path_image; IN_IMAGE]; ALL_TAC] THEN
    MP_TAC(SPEC `ball((p:real^1->complex) t,norm(p t - z))`
      SIMPLY_CONNECTED_EQ_CONTINUOUS_LOG) THEN
    SIMP_TAC[OPEN_BALL; CONVEX_BALL; CONVEX_IMP_SIMPLY_CONNECTED] THEN
    DISCH_THEN(MP_TAC o SPEC `\w:complex. w - z` o CONJUNCT2) THEN
    SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST] THEN
    REWRITE_TAC[COMPLEX_SUB_0] THEN ANTS_TAC THENL
     [GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
      SIMP_TAC[IN_BALL; dist; REAL_LT_REFL];
      DISCH_THEN(X_CHOOSE_THEN `l:complex->complex` STRIP_ASSUME_TAC)] THEN
    ONCE_REWRITE_TAC[WINDING_NUMBER_OFFSET] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [path]) THEN
    GEN_REWRITE_TAC LAND_CONV [continuous_on] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real^1`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `norm((p:real^1->complex) t - z)`) THEN
    ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[GSYM IN_BALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[CONTINUOUS_WITHIN] THEN ONCE_REWRITE_TAC[LIM_NULL] THEN
    MATCH_MP_TAC LIM_TRANSFORM_WITHIN THEN EXISTS_TAC
     `\u. Cx(&1) / (Cx(&2) * Cx pi * ii) *
          (pathfinish((l:complex->complex) o subpath t u p) -
           pathstart(l o subpath t u p))` THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `u:real^1` THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `path_image(subpath t u p) SUBSET ball(p t:complex,norm (p t - z))`
      ASSUME_TAC THENL
       [REWRITE_TAC[PATH_IMAGE_SUBPATH_GEN] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
        SUBGOAL_THEN
         `segment[t,u] SUBSET interval[vec 0,vec 1] /\
          segment[t,u] SUBSET ball(t:real^1,d)`
        MP_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
        CONJ_TAC THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
        MATCH_MP_TAC HULL_MINIMAL THEN
        REWRITE_TAC[CONVEX_BALL; CONVEX_INTERVAL] THEN
        ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; CENTRE_IN_BALL] THEN
        ASM_REWRITE_TAC[ONCE_REWRITE_RULE[DIST_SYM] IN_BALL];
        ALL_TAC] THEN
      W(MP_TAC o PART_MATCH (rand o rand) WINDING_NUMBER_COMPOSE_CEXP o
        lhand o snd) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_SIMP_TAC[PATH_SUBPATH] THEN
        ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
        DISCH_THEN(SUBST1_TAC o SYM)] THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `winding_number((\w. subpath t u p w - z),Cx(&0))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC WINDING_NUMBER_EQUAL THEN
        REWRITE_TAC[o_THM; GSYM path_image; SET_RULE
         `(!x. x IN s ==> cexp(l(subpath t u p x)) = subpath t u p x - z) <=>
          (!y. y IN IMAGE (subpath t u p) s ==> cexp(l y) = y - z)`] THEN
        ASM SET_TAC[];
        ONCE_REWRITE_TAC[GSYM WINDING_NUMBER_OFFSET] THEN
        REWRITE_TAC[ETA_AX] THEN
        MP_TAC(ISPECL [`p:real^1->complex`; `vec 0:real^1`; `t:real^1`;
                       `u:real^1`; `z:complex`]
          WINDING_NUMBER_SUBPATH_COMBINE) THEN
        ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN
        CONV_TAC COMPLEX_RING];
      REWRITE_TAC[COMPLEX_VEC_0] THEN MATCH_MP_TAC LIM_NULL_COMPLEX_LMUL THEN
      REWRITE_TAC[PATHSTART_COMPOSE; PATHSTART_SUBPATH;
                  PATHFINISH_COMPOSE; PATHFINISH_SUBPATH] THEN
      REWRITE_TAC[GSYM COMPLEX_VEC_0; GSYM LIM_NULL] THEN
      REWRITE_TAC[GSYM CONTINUOUS_WITHIN] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_WITHIN_COMPOSE THEN CONJ_TAC THENL
       [ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; path];
        MATCH_MP_TAC CONTINUOUS_AT_WITHIN THEN
        UNDISCH_TAC `(l:complex->complex) continuous_on
                     ball(p(t:real^1),norm(p t - z))` THEN
        SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_BALL] THEN
        DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[CENTRE_IN_BALL] THEN
        ASM_REWRITE_TAC[VECTOR_SUB_EQ; NORM_POS_LT]]];
    REWRITE_TAC[pathstart; pathfinish; SUBPATH_REFL; SUBPATH_TRIVIAL] THEN
    MATCH_MP_TAC(COMPLEX_FIELD
     `w' = Cx(&0)
      ==> (a * b * c * w + l) - (a * b * c * w' + l) = a * b * c * w`) THEN
    MATCH_MP_TAC WINDING_NUMBER_TRIVIAL THEN
    MP_TAC(ISPEC `p:real^1->complex` PATHSTART_IN_PATH_IMAGE) THEN
    REWRITE_TAC[pathstart] THEN ASM_MESON_TAC[];
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`subpath (vec 0) t (p:real^1->complex)`; `z:complex`]
        WINDING_NUMBER_AHLFORS_FULL) THEN
    REWRITE_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
    ASM_SIMP_TAC[ENDS_IN_UNIT_INTERVAL; PATH_SUBPATH; CEXP_ADD;
      REWRITE_RULE[SET_RULE `s SUBSET t <=> !x. ~(x IN t) ==> ~(x IN s)`]
                  PATH_IMAGE_SUBPATH_SUBSET] THEN
    MATCH_MP_TAC(COMPLEX_RING
     `t:complex = s ==> p - z = e * s ==> p = z + e * t`) THEN
    REWRITE_TAC[pathstart] THEN MATCH_MP_TAC CEXP_CLOG THEN
    REWRITE_TAC[COMPLEX_SUB_0] THEN
    ASM_MESON_TAC[pathstart; PATHSTART_IN_PATH_IMAGE]]);;

let WINDING_NUMBER_HOMOTOPIC_LOOPS_EQ = prove
 (`!p q z.
        path p /\ pathfinish p = pathstart p /\ ~(z IN path_image p) /\
        path q /\ pathfinish q = pathstart q /\ ~(z IN path_image q)
        ==> (winding_number(p,z) = winding_number(q,z) <=>
             homotopic_loops ((:complex) DELETE z) p q)`,
  let lemma = prove
   (`!p z. path p /\ ~(z IN path_image p) /\
           winding_number(p,z) = Cx(&0)
           ==> ?a. homotopic_loops ((:complex) DELETE z) p (\t. a)`,
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`p:real^1->complex`; `z:complex`]
          WINDING_NUMBER_AS_CONTINUOUS_LOGARITHM) THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_ADD_LID; COMPLEX_SUB_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^1->complex` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `z + Cx(&1)` THEN
    MP_TAC(ISPECL [`\r:real^1->complex. pathfinish r = pathstart r`;
                   `q:real^1->complex`; `\t:real^1. Cx(&0)`;
                   `\w. z + cexp w`;
                   `interval[vec 0:real^1,vec 1]`; `(:complex)`;
                   `(:complex) DELETE z`]
     HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT) THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_CEXP; CONTINUOUS_ON_ADD; CONTINUOUS_ON_CONST;
                 CEXP_0; homotopic_loops; o_DEF] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[CEXP_NZ; COMPLEX_EQ_ADD_LCANCEL_0; SET_RULE
       `IMAGE f UNIV SUBSET UNIV DELETE z <=> !x. ~(f x = z)`] THEN
      MATCH_MP_TAC HOMOTOPIC_WITH_MONO THEN
      EXISTS_TAC `\r:real^1->complex. pathfinish r = pathstart r` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM homotopic_loops] THEN
        MATCH_MP_TAC HOMOTOPIC_LOOPS_LINEAR THEN
        ASM_REWRITE_TAC[SUBSET_UNIV] THEN
        REWRITE_TAC[path; pathstart; pathfinish; CONTINUOUS_ON_CONST];
        SIMP_TAC[pathstart; pathfinish]];
      MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_EQ) THEN
     ASM_SIMP_TAC[o_THM; pathstart; pathfinish; ENDS_IN_UNIT_INTERVAL]])
  and tac =
    ASM_SIMP_TAC[PATH_REVERSEPATH; PATHSTART_REVERSEPATH; PATHSTART_JOIN;
                 PATH_LINEPATH; PATHFINISH_REVERSEPATH; PATHSTART_LINEPATH;
                 PATHFINISH_LINEPATH; WINDING_NUMBER_JOIN;
                 PATH_IMAGE_REVERSEPATH; PATH_IMAGE_JOIN; IN_UNION;
                 PATHFINISH_JOIN; PATH_JOIN; WINDING_NUMBER_REVERSEPATH;
                 SET_RULE `s SUBSET UNIV DELETE z <=> ~(z IN s)`] in
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  REWRITE_TAC[WINDING_NUMBER_HOMOTOPIC_LOOPS] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(pathstart p:complex = z) /\ ~(pathstart q = z)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:complex)`; `z:complex`]
        PATH_CONNECTED_OPEN_DELETE) THEN
  REWRITE_TAC[OPEN_UNIV; CONNECTED_UNIV; DIMINDEX_2; LE_REFL] THEN
  REWRITE_TAC[path_connected] THEN DISCH_THEN(MP_TAC o SPECL
   [`pathstart p:complex`; `pathstart q:complex`]) THEN
  ASM_REWRITE_TAC[IN_UNIV; IN_DELETE; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:real^1->complex` THEN
  REWRITE_TAC[SET_RULE `s SUBSET UNIV DELETE z <=> ~(z IN s)`] THEN
  STRIP_TAC THEN SUBGOAL_THEN `~(pathstart r:complex = z)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN EXISTS_TAC
   `reversepath(r ++ reversepath q ++ reversepath r):real^1->complex` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[REVERSEPATH_JOINPATHS; REVERSEPATH_REVERSEPATH;
                 PATHSTART_JOIN; PATHFINISH_JOIN;
                 PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH] THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `r ++ q ++ reversepath r:real^1->complex` THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS THEN tac THEN
      ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
      MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN tac;
      MATCH_MP_TAC HOMOTOPIC_LOOPS_CONJUGATE THEN tac]] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS THEN tac THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC
   `linepath(pathstart(reversepath(r ++ reversepath q ++ reversepath r)),
             pathstart(reversepath(r ++ reversepath q ++ reversepath r))) ++
    reversepath(r ++ reversepath q ++ reversepath r)
    :real^1->complex` THEN
  CONJ_TAC THENL [tac; MATCH_MP_TAC HOMOTOPIC_PATHS_LID THEN tac] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC
   `p ++ linepath(pathstart(r ++ reversepath q ++ reversepath r),
                  pathstart(r ++ reversepath q ++ reversepath r))
    :real^1->complex` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
    tac THEN SUBST1_TAC(SYM(ASSUME `pathfinish p:complex = pathstart p`)) THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_RID THEN tac;
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC
   `p ++ (r ++ reversepath q ++ reversepath r) ++
         reversepath(r ++ reversepath q ++ reversepath r):real^1->complex` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    REWRITE_TAC[HOMOTOPIC_PATHS_REFL] THEN
    CONJ_TAC THENL [tac; ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; tac] THEN
    ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_RINV THEN tac;
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC
   `(p ++ (r ++ reversepath q ++ reversepath r)) ++
         reversepath(r ++ reversepath q ++ reversepath r):real^1->complex` THEN
  CONJ_TAC THENL [MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN tac; ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[HOMOTOPIC_PATHS_REFL] THEN tac] THEN
  MP_TAC(SPECL
   [`(p ++ r ++ reversepath q ++ reversepath r):real^1->complex`;
    `z:complex`] lemma) THEN
  tac THEN REWRITE_TAC[COMPLEX_RING `q + r + --q + --r = Cx(&0)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `aa:complex` MP_TAC) THEN
  REWRITE_TAC[GSYM LINEPATH_REFL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_PATHS_NULL) THEN
  tac);;

(* ------------------------------------------------------------------------- *)
(* A few simple corollaries from the various equivalences.                   *)
(* ------------------------------------------------------------------------- *)

let SIMPLY_CONNECTED_INSIDE_SIMPLE_PATH = prove
 (`!p:real^1->real^2.
     simple_path p ==> simply_connected(inside(path_image p))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SIMPLE_PATH_IMP_PATH) THEN
  ASM_SIMP_TAC[SIMPLY_CONNECTED_EQ_EMPTY_INSIDE;
               OPEN_INSIDE; CLOSED_PATH_IMAGE; INSIDE_INSIDE_EQ_EMPTY;
               CONNECTED_PATH_IMAGE] THEN
  ASM_CASES_TAC `pathstart(p):real^2 = pathfinish p` THEN
  ASM_SIMP_TAC[JORDAN_INSIDE_OUTSIDE; INSIDE_ARC_EMPTY; ARC_SIMPLE_PATH] THEN
  REWRITE_TAC[CONNECTED_EMPTY]);;

let SIMPLY_CONNECTED_INTER = prove
 (`!s t:real^2->bool.
        open s /\ open t /\ simply_connected s /\ simply_connected t /\
        connected (s INTER t)
        ==> simply_connected (s INTER t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  SIMP_TAC[SIMPLY_CONNECTED_EQ_WINDING_NUMBER_ZERO; OPEN_INTER] THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Pick out the Riemann Mapping Theorem from the earlier chain.              *)
(* ------------------------------------------------------------------------- *)

let RIEMANN_MAPPING_THEOREM = prove
 (`!s. open s /\ simply_connected s <=>
       s = {} \/
       s = (:real^2) \/
       ?f g. f holomorphic_on s /\
             g holomorphic_on ball(Cx(&0),&1) /\
             (!z. z IN s ==> f z IN ball(Cx(&0),&1) /\ g(f z) = z) /\
             (!z. z IN ball(Cx(&0),&1) ==> g z IN s /\ f(g z) = z)`,
  GEN_TAC THEN MATCH_MP_TAC(TAUT
   `(a ==> (b <=> c)) /\ (c ==> a) ==> (a /\ b <=> c)`) THEN
  REWRITE_TAC[SIMPLY_CONNECTED_EQ_BIHOLOMORPHIC_TO_DISC] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[OPEN_EMPTY; OPEN_UNIV] THEN
  SUBGOAL_THEN `s = IMAGE (g:complex->complex) (ball(Cx(&0),&1))`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN
  ASM_SIMP_TAC[OPEN_BALL; HOLOMORPHIC_ON_IMP_CONTINUOUS_ON] THEN
  ASM_MESON_TAC[]);;
