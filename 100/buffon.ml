(* ========================================================================= *)
(* Buffon's needle problem -- short and long needle cases.                   *)
(*                                                                           *)
(* A needle of length l is dropped uniformly at random on a floor ruled      *)
(* with parallel lines at distance d apart. The needle's position is         *)
(* described by two independent uniform random variables:                    *)
(*   X ~ Uniform(0, d/2)   (distance from center to nearest line)            *)
(*   Theta ~ Uniform(0, pi) (angle of the needle)                            *)
(* The needle crosses a line iff X <= (l/2) * sin(Theta).                    *)
(*                                                                           *)
(* We first prove a unified general theorem for any l, d > 0, expressing     *)
(* the crossing probability as an integral involving min(d/2, (l/2)*sin).    *)
(* The short and long needle formulas are then derived as special cases:     *)
(*                                                                           *)
(*   Short needle (l <= d):                                                  *)
(*     P(crossing) = 2l / (pi * d)                                           *)
(*                                                                           *)
(*   Long needle (d <= l):                                                   *)
(*     P(crossing) = (2 / (pi * d)) * (l - sqrt(l^2 - d^2) + d * acs(d/l))   *)
(*                                                                           *)
(* Main results:                                                             *)
(*   BUFFON_GENERAL     -- unified integral form for any l, d > 0            *)
(*   BUFFON_SHORT       -- P = 2l/(pi*d) when l <= d                         *)
(*   BUFFON_LONG        -- long needle formula when d <= l                   *)
(* ========================================================================= *)

needs "Probability/measure.ml";;
needs "Probability/random_variables.ml";;
needs "Probability/independence.ml";;
needs "Probability/expectation.ml";;

prioritize_real();;

(* ===================================================================== *)
(* Uniform distribution on an interval                                   *)
(* ===================================================================== *)

let uniform_rv = new_definition
  `uniform_rv (p:A prob_space) (X:A->real) (a:real) (b:real) <=>
   random_variable p X /\
   a < b /\
   !t. distribution_fn p X t =
     if t < a then &0
     else if b <= t then &1
     else (t - a) / (b - a)`;;

(* ===================================================================== *)
(* Basic properties of uniform distributions                             *)
(* ===================================================================== *)

let UNIFORM_RV_IMP_RV = prove
  (`!p:A prob_space X a b. uniform_rv p X a b ==> random_variable p X`,
   REWRITE_TAC[uniform_rv] THEN MESON_TAC[]);;

let UNIFORM_RV_BOUNDS = prove
  (`!p:A prob_space X a b. uniform_rv p X a b ==> a < b`,
   REWRITE_TAC[uniform_rv] THEN MESON_TAC[]);;

(* CDF value in the middle range *)
let UNIFORM_RV_CDF_MID = prove
  (`!p:A prob_space X a b t.
      uniform_rv p X a b /\ a <= t /\ t < b
      ==> distribution_fn p X t = (t - a) / (b - a)`,
   REWRITE_TAC[uniform_rv] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN
   COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REFL_TAC);;

(* CDF value at or above b *)
let UNIFORM_RV_CDF_HIGH = prove
  (`!p:A prob_space X a b t.
      uniform_rv p X a b /\ b <= t
      ==> distribution_fn p X t = &1`,
   REWRITE_TAC[uniform_rv] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN
   COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

(* CDF value below a *)
let UNIFORM_RV_CDF_LOW = prove
  (`!p:A prob_space X a b t.
      uniform_rv p X a b /\ t < a
      ==> distribution_fn p X t = &0`,
   REWRITE_TAC[uniform_rv] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN
   COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

(* CDF at zero for Uniform(0, b) *)
let UNIFORM_RV_CDF_ZERO = prove
  (`!p:A prob_space X b t.
      uniform_rv p X (&0) b /\ &0 <= t /\ t < b
      ==> distribution_fn p X t = t / b`,
   REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `&0`; `b:real`; `t:real`]
     UNIFORM_RV_CDF_MID) THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL
   [ASM_MESON_TAC[UNIFORM_RV_BOUNDS]; ALL_TAC] THEN
   SIMP_TAC[REAL_SUB_RZERO]);;

(* CDF for Uniform(0, b) at any c in [0, b], including the right endpoint *)
let UNIFORM_ZERO_CDF_RANGE = prove
  (`!p:A prob_space X b c. uniform_rv p X (&0) b /\ &0 <= c /\ c <= b
   ==> distribution_fn p X c = c / b`,
   REPEAT STRIP_TAC THEN
   ASM_CASES_TAC `c < b:real` THENL
   [ASM_MESON_TAC[UNIFORM_RV_CDF_ZERO]; ALL_TAC] THEN
   SUBGOAL_THEN `c = b:real` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL
   [ASM_MESON_TAC[UNIFORM_RV_BOUNDS]; ALL_TAC] THEN
   SUBGOAL_THEN `b / b = &1` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[REAL_DIV_REFL; REAL_ARITH `&0 < b ==> ~(b = &0)`];
    ALL_TAC] THEN
   MATCH_MP_TAC UNIFORM_RV_CDF_HIGH THEN
   EXISTS_TAC `&0:real` THEN EXISTS_TAC `b:real` THEN
   ASM_REWRITE_TAC[REAL_LE_REFL]);;

(* ===================================================================== *)
(* The integral of sin from 0 to pi                                      *)
(* ===================================================================== *)

(* The key integral: integral of sin from 0 to pi equals 2 *)
let HAS_REAL_INTEGRAL_SIN_0_PI = prove
  (`(sin has_real_integral (&2)) (real_interval [&0, pi])`,
   SUBGOAL_THEN `&2 = --(cos pi) - (--(cos(&0)))` SUBST1_TAC THENL
   [REWRITE_TAC[COS_0; COS_PI] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS THEN
   CONJ_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
   MP_TAC(SPEC `x:real` HAS_REAL_DERIVATIVE_COS) THEN
   DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_DERIVATIVE_NEG) THEN
   REWRITE_TAC[REAL_NEG_NEG]);;

(* Scaled version: integral of c * sin from 0 to pi equals 2 * c *)
let HAS_REAL_INTEGRAL_CMUL_SIN_0_PI = prove
  (`!c. ((\t. c * sin t) has_real_integral (&2 * c))
        (real_interval [&0, pi])`,
   GEN_TAC THEN
   MP_TAC HAS_REAL_INTEGRAL_SIN_0_PI THEN
   DISCH_THEN(MP_TAC o SPEC `c:real` o MATCH_MP HAS_REAL_INTEGRAL_LMUL) THEN
   REWRITE_TAC[REAL_MUL_SYM]);;

(* ===================================================================== *)
(* Helper lemmas for the bridge proof                                    *)
(* ===================================================================== *)

(* Lipschitz bound for sin: |sin(b) - sin(a)| <= |b - a| *)
let SIN_LIPSCHITZ = prove
  (`!a b. abs(sin b - sin a) <= abs(b - a)`,
   REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real = b` THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0; REAL_LE_REFL]; ALL_TAC] THEN
   ASM_CASES_TAC `a:real < b` THENL
   [MP_TAC(ISPECL [`sin`; `cos`; `a:real`; `b:real`] REAL_MVT_VERY_SIMPLE) THEN
    ANTS_TAC THENL
    [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
     REWRITE_TAC[HAS_REAL_DERIVATIVE_SIN]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[REAL_ABS_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
    [MP_TAC(SPEC `x:real` COS_BOUND) THEN REAL_ARITH_TAC;
     REAL_ARITH_TAC];
    (* b < a case: symmetry *)
    ONCE_REWRITE_TAC[REAL_ARITH `abs(x - y) = abs(y - x)`] THEN
    MP_TAC(ISPECL [`sin`; `cos`; `b:real`; `a:real`] REAL_MVT_VERY_SIMPLE) THEN
    ANTS_TAC THENL
    [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
     REWRITE_TAC[HAS_REAL_DERIVATIVE_SIN]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[REAL_ABS_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
    [MP_TAC(SPEC `x:real` COS_BOUND) THEN REAL_ARITH_TAC;
     REAL_ARITH_TAC]]);;

(* Epsilon-to-equality *)
let REAL_EQ_EPSILON = prove
  (`!x y:real. (!e. &0 < e ==> abs(x - y) < e) ==> x = y`,
   REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH
     `~(&0 < abs(x - y)) ==> x = y`) THEN
   DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `abs(x - y:real)`) THEN
   ASM_REWRITE_TAC[REAL_LT_REFL]);;

(* Sandwich bound: both in [L,U] implies |a-b| <= U-L *)
let SANDWICH_ABS_BOUND = prove
  (`!a b l r. l <= a /\ a <= r /\ l <= b /\ b <= r
              ==> abs(a - b) <= r - l`,
   REAL_ARITH_TAC);;

(* ===================================================================== *)
(* Independence and probability machinery                                *)
(* ===================================================================== *)

(* The joint CDF formula for independent RVs (from indep_rv definition) *)
let INDEP_JOINT_CDF = prove
  (`!p:A prob_space X Y a b.
      indep_rv p X Y
      ==> prob p {x | x IN prob_carrier p /\ X x <= a /\ Y x <= b} =
          distribution_fn p X a * distribution_fn p Y b`,
   REWRITE_TAC[indep_rv; distribution_fn] THEN MESON_TAC[]);;

(* Probability of a set difference when one is a subset *)
let PROB_SUBSET_DIFF = prove
  (`!p:A prob_space a b.
      a IN prob_events p /\ b IN prob_events p /\ b SUBSET a
      ==> prob p (a DIFF b) = prob p a - prob p b`,
   REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `a:A->bool`; `b:A->bool`] PROB_DIFF) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   AP_TERM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]);;

(* Rectangle probability for independent RVs *)
let INDEP_RECT_PROB = prove
  (`!p:A prob_space X Theta c a' b'.
      indep_rv p X Theta /\ a' <= b'
      ==> prob p {x | x IN prob_carrier p /\ X x <= c /\
                      a' < Theta x /\ Theta x <= b'} =
          distribution_fn p X c *
          (distribution_fn p Theta b' - distribution_fn p Theta a')`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `random_variable p (X:A->real) /\ random_variable p (Theta:A->real)`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[indep_rv]; ALL_TAC] THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ X x <= c /\ a' < Theta x /\ Theta x <= b'} =
      {x | x IN prob_carrier p /\ X x <= c /\ Theta x <= b'} DIFF
      {x | x IN prob_carrier p /\ X x <= c /\ Theta x <= a'}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM; GSYM REAL_NOT_LE;
                DE_MORGAN_THM] THEN
    GEN_TAC THEN ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN
     `!t. {x:A | x IN prob_carrier p /\ X x <= c /\ Theta x <= t} =
          {x | x IN prob_carrier p /\ X x <= c} INTER
          {x | x IN prob_carrier p /\ Theta x <= t}`
     ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ X x <= c /\ Theta x <= b'} IN prob_events p /\
      {x | x IN prob_carrier p /\ X x <= c /\ Theta x <= a'} IN prob_events p`
     STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN
    ASM_SIMP_TAC[DIST_FN_IN_EVENTS];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ X x <= c /\ Theta x <= a'} SUBSET
      {x | x IN prob_carrier p /\ X x <= c /\ Theta x <= b'}`
     ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN
     `!t. prob p ({x:A | x IN prob_carrier p /\ X x <= c} INTER
                  {x | x IN prob_carrier p /\ Theta x <= t}) =
          distribution_fn p X c * distribution_fn p Theta t`
     ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\ X x <= c} INTER
       {x | x IN prob_carrier p /\ Theta x <= t} =
       {x | x IN prob_carrier p /\ X x <= c /\ Theta x <= t}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN MESON_TAC[];
     ASM_SIMP_TAC[INDEP_JOINT_CDF]];
    ALL_TAC] THEN
   ASM_SIMP_TAC[PROB_SUBSET_DIFF] THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Rectangle probability for specific uniform distributions *)
let UNIFORM_RECT_PROB = prove
  (`!p:A prob_space X Theta d c a' b'.
       uniform_rv p X (&0) (d / &2) /\
       uniform_rv p Theta (&0) pi /\
       indep_rv p X Theta /\
       &0 <= c /\ c <= d / &2 /\
       &0 <= a' /\ a' <= b' /\ b' <= pi
       ==> prob p {x | x IN prob_carrier p /\ X x <= c /\
                       a' < Theta x /\ Theta x <= b'} =
           c / (d / &2) * ((b' - a') / pi)`,
   REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `Theta:A->real`;
                   `c:real`; `a':real`; `b':real`] INDEP_RECT_PROB) THEN
   ASM_SIMP_TAC[REAL_LE_TRANS] THEN DISCH_THEN SUBST1_TAC THEN
   SUBGOAL_THEN `distribution_fn p (X:A->real) c = c / (d / &2)`
     SUBST1_TAC THENL
   [MATCH_MP_TAC UNIFORM_ZERO_CDF_RANGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `distribution_fn p (Theta:A->real) b' = b' / pi` SUBST1_TAC THENL
   [MATCH_MP_TAC UNIFORM_ZERO_CDF_RANGE THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `distribution_fn p (Theta:A->real) a' = a' / pi` SUBST1_TAC THENL
   [MATCH_MP_TAC UNIFORM_ZERO_CDF_RANGE THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `~(pi = &0)` ASSUME_TAC THENL
   [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_FIELD `~(p = &0) ==> b / p - a / p = (b - a) / p`]);;

(* Finite additivity for pairwise disjoint indexed events *)
let PROB_FINITE_ADDITIVE = prove
  (`!p:A prob_space A.
      !n. (!k. k <= n ==> A k IN prob_events p) /\
          (!i j. i <= n /\ j <= n /\ ~(i = j) ==> DISJOINT (A i) (A j))
          ==> prob p (UNIONS (IMAGE A (0..n))) =
              sum (0..n) (\k. prob p (A k))`,
   GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [STRIP_TAC THEN
    REWRITE_TAC[NUMSEG_SING; IMAGE_CLAUSES; UNIONS_1; SUM_SING_NUMSEG];
    ALL_TAC] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `0..SUC n = (0..n) UNION {SUC n}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_NUMSEG; IN_SING] THEN ARITH_TAC;
    ALL_TAC] THEN
   REWRITE_TAC[IMAGE_UNION; IMAGE_CLAUSES; UNIONS_UNION; UNIONS_1] THEN
   SUBGOAL_THEN `DISJOINT (UNIONS (IMAGE (A:num->A->bool) (0..n))) (A (SUC n))`
     ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY;
                IN_UNIONS; EXISTS_IN_IMAGE; IN_NUMSEG] THEN
    X_GEN_TAC `w:A` THEN
    REWRITE_TAC[TAUT `~(a /\ b) <=> a ==> ~b`] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `SUC n`]) THEN
    ASM_REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `w:A`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `UNIONS (IMAGE (A:num->A->bool) (0..n)) IN prob_events p`
     ASSUME_TAC THENL
   [MATCH_MP_TAC PROB_FINITE_UNION_IN_EVENTS THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_NUMSEG] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `(A:num->A->bool) (SUC n) IN prob_events p` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN ARITH_TAC;
    ALL_TAC] THEN
   MP_TAC(ISPECL [`\k. prob p ((A:num->A->bool) k)`; `0..n`; `{SUC n}`]
     SUM_UNION) THEN
   SIMP_TAC[FINITE_NUMSEG; FINITE_SING; SUM_SING] THEN
   ANTS_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_NUMSEG; IN_SING;
                NOT_IN_EMPTY] THEN ARITH_TAC;
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`;
                   `UNIONS (IMAGE (A:num->A->bool) (0..n))`;
                   `(A:num->A->bool) (SUC n)`] PROB_ADDITIVE) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* Paired Skolemization *)
let SKOLEM_PAIR = prove
  (`(!x:A. ?a:B b:C. P x a b) <=> (?f g. !x. P x (f x) (g x))`,
   EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `!x:A. ?(p:B#C). P x (FST p) (SND p)` MP_TAC THENL
    [GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
     STRIP_TAC THEN EXISTS_TAC `(a:B),(b:C)` THEN
     ASM_REWRITE_TAC[FST; SND]; ALL_TAC] THEN
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `h:A->B#C`) THEN
    EXISTS_TAC `(\x. FST((h:A->B#C) x))` THEN
    EXISTS_TAC `(\x. SND((h:A->B#C) x))` THEN
    GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
    SIMP_TAC[];
    STRIP_TAC THEN GEN_TAC THEN
    EXISTS_TAC `(f:A->B) x` THEN EXISTS_TAC `(g:A->C) x` THEN
    ASM_REWRITE_TAC[]]);;

(* ===================================================================== *)
(* Generalized Buffon's needle (short and long needle cases)             *)
(*                                                                       *)
(* For arbitrary l, d > 0, the crossing probability equals               *)
(*   (2 / (pi * d)) * integral_0^pi min(d/2, l/2 * sin(t)) dt            *)
(*                                                                       *)
(* When l <= d this gives 2l/(pi*d) (short needle).                      *)
(* When d <= l this gives (2/(pi*d))*(l - sqrt(l^2-d^2) + d*acs(d/l))    *)
(* (long needle, Laplace 1812).                                          *)
(* ===================================================================== *)

(* ----- Helper lemmas for min-clipped sin function ----- *)

(* Lipschitz property of min with a constant: min is a contraction *)
let MIN_CONTRACTION = prove
  (`!c x y. x <= y ==> min c y - min c x <= y - x`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[real_min] THEN
   REPEAT COND_CASES_TAC THEN
   ASM_REAL_ARITH_TAC);;

(* Absolute Lipschitz form *)
let MIN_ABS_LIPSCHITZ = prove
  (`!c x y. abs(min c x - min c y) <= abs(x - y)`,
   REPEAT GEN_TAC THEN
   DISJ_CASES_TAC(REAL_ARITH `x <= y \/ y <= x`) THENL
   [MP_TAC(SPECL [`c:real`; `x:real`; `y:real`] MIN_CONTRACTION) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`c:real`; `x:real`] REAL_MIN_MIN) THEN
    REAL_ARITH_TAC;
    MP_TAC(SPECL [`c:real`; `y:real`; `x:real`] MIN_CONTRACTION) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`c:real`; `y:real`] REAL_MIN_MIN) THEN
    REAL_ARITH_TAC]);;

(* Oscillation bound for min(d/2, l/2 * sin) on [a,b] within [0,pi] *)
let MIN_SIN_OSCILLATION = prove
  (`!l d a b. &0 < l /\ &0 < d /\ a <= b /\ &0 <= a /\ b <= pi
    ==> ?m M. (!t. t IN real_interval[a,b]
                 ==> m <= min (d / &2) (l / &2 * sin t) /\
                     min (d / &2) (l / &2 * sin t) <= M) /\
              M - m <= l / &2 * (b - a) /\
              &0 <= m /\ m <= d / &2 /\ M <= d / &2`,
   REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`\t. min (d / &2) (l / &2 * sin t)`;
                   `real_interval[a:real,b]`]
     REAL_CONTINUOUS_ATTAINS_SUP) THEN
   REWRITE_TAC[real_compact; IMAGE_LIFT_REAL_INTERVAL; COMPACT_INTERVAL] THEN
   ASM_REWRITE_TAC[REAL_INTERVAL_NE_EMPTY] THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_MIN THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_SIN];
    ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `t_max:real` STRIP_ASSUME_TAC) THEN
   MP_TAC(ISPECL [`\t. min (d / &2) (l / &2 * sin t)`;
                   `real_interval[a:real,b]`]
     REAL_CONTINUOUS_ATTAINS_INF) THEN
   REWRITE_TAC[real_compact; IMAGE_LIFT_REAL_INTERVAL; COMPACT_INTERVAL] THEN
   ASM_REWRITE_TAC[REAL_INTERVAL_NE_EMPTY] THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_MIN THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_SIN];
    ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `t_min:real` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `min (d / &2) (l / &2 * sin t_min)` THEN
   EXISTS_TAC `min (d / &2) (l / &2 * sin t_max)` THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    (* oscillation bound *)
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(min (d / &2) (l / &2 * sin t_max) -
                    min (d / &2) (l / &2 * sin t_min))` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(l / &2 * sin t_max - l / &2 * sin t_min)` THEN
    CONJ_TAC THENL
    [REWRITE_TAC[MIN_ABS_LIPSCHITZ]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(l / &2) * abs(t_max - t_min)` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS; SIN_LIPSCHITZ];
     ALL_TAC] THEN
    SUBGOAL_THEN `abs(l / &2) = l / &2` SUBST1_TAC THENL
    [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> abs x = x`) THEN ASM_REAL_ARITH_TAC;
     ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `t_min IN real_interval[a,b]` THEN
    UNDISCH_TAC `t_max IN real_interval[a,b]` THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    (* 0 <= m *)
    REWRITE_TAC[REAL_LE_MIN] THEN CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SIN_POS_PI_LE THEN
    UNDISCH_TAC `t_min IN real_interval[a,b]` THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    (* m <= d/2 *)
    REWRITE_TAC[REAL_MIN_LE] THEN DISJ1_TAC THEN REAL_ARITH_TAC;
    (* M <= d/2 *)
    REWRITE_TAC[REAL_MIN_LE] THEN DISJ1_TAC THEN REAL_ARITH_TAC]);;

(* Custom tactic for PROB_SUBADDITIVE that handles alpha-equivalence.
   MATCH_MP_TAC fails when the LHS and RHS sets come from different term
   parsings (same set expressions but different bound variable names).
   This tactic extracts the union from the goal's LHS, instantiates
   PROB_SUBADDITIVE with those exact terms, and uses AP_TERM/ALPHA to
   bridge any alpha-equivalence gap on the RHS. *)
let SUBADDITIVE_TAC : tactic =
  fun (asl, w) ->
    let lhs = lhand w in
    let prob_p = rator lhs in
    let union_set = rand lhs in
    let a_set = lhand union_set in
    let b_set = rand union_set in
    let p_tm = rand prob_p in
    let ith = ISPECL [p_tm; a_set; b_set] PROB_SUBADDITIVE in
    let ant = fst(dest_imp(concl ith)) in
    null_meta, [asl, ant], fun i [pth] ->
      let ith' = INSTANTIATE_ALL i ith in
      let th = MP ith' pth in
      if concl th = w then th
      else
        let rhs_eq = ALPHA (rand(concl th)) (rand w) in
        EQ_MP (AP_TERM (rator(concl th)) rhs_eq) th;;

(* Tactic to rewrite "prob p S = &0" when S is alpha-equivalent to an
   assumption's argument. Handles alpha-equiv bound variable mismatch.
   Goal should be of the form: ... + prob p S <= ...
   where an assumption has |- prob p S' = &0 with S aconv S'. *)
let PROB_ZERO_TAC : tactic =
  fun (asl, w) ->
    let prob_y = rand(lhand w) in
    let target_eq = mk_eq(prob_y, `&0`) in
    let (_, asm_th) = find (fun (_, th) ->
      try let l,r = dest_eq(concl th) in
          aconv l prob_y && r = `&0`
      with _ -> false) asl in
    let bridge =
      if concl asm_th = target_eq then asm_th
      else EQ_MP (ALPHA (concl asm_th) target_eq) asm_th in
    (SUBST1_TAC bridge THEN REWRITE_TAC[REAL_ADD_RID]) (asl, w);;

(* ------------------------------------------------------------------------- *)
(* General core bound: Riemann sum approach with min clipping                *)
(* ------------------------------------------------------------------------- *)

let BUFFON_GENERAL_CORE_BOUND = prove
  (`!p:A prob_space X Theta l d.
      &0 < l /\ &0 < d /\
      uniform_rv p X (&0) (d / &2) /\
      uniform_rv p Theta (&0) pi /\
      indep_rv p X Theta
      ==> !N. 1 <= N
          ==> abs(prob p {x:A | x IN prob_carrier p /\
                     X x <= l / &2 * sin(Theta x)} -
                  &2 / (d * pi) *
                  real_integral (real_interval [&0,pi])
                    (\t. min (d / &2) (l / &2 * sin t)))
              <= l * pi / (d * &N)`,
   REPEAT STRIP_TAC THEN
   (* Basic positivity facts *)
   SUBGOAL_THEN `&0 < pi` ASSUME_TAC THENL [REWRITE_TAC[PI_POS]; ALL_TAC] THEN
   SUBGOAL_THEN `&0 < &N` ASSUME_TAC THENL
   [UNDISCH_TAC `1 <= N` THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `~(&N = &0)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `~(d = &0)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `~(pi = &0)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `random_variable p (X:A->real)` ASSUME_TAC THENL
   [ASM_MESON_TAC[UNIFORM_RV_IMP_RV]; ALL_TAC] THEN
   SUBGOAL_THEN `random_variable p (Theta:A->real)` ASSUME_TAC THENL
   [ASM_MESON_TAC[UNIFORM_RV_IMP_RV]; ALL_TAC] THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ X x <= (l / &2) * sin(Theta x)}
        IN prob_events p` ASSUME_TAC THENL
   [MATCH_MP_TAC RV_LEVEL_LE_RV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN
    MATCH_MP_TAC RANDOM_VARIABLE_SIN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* Skolemize: get m, M bounding min(d/2, l/2*sin) on each subinterval *)
   SUBGOAL_THEN
     `?m M. !k. (k:num) < N ==>
        (!t. &k * pi / &N <= t /\ t <= &(k+1) * pi / &N ==>
             (m:num->real) k <= min (d / &2) (l / &2 * sin t) /\
             min (d / &2) (l / &2 * sin t) <= M k) /\
        M k - m k <= l / &2 * pi / &N /\
        &0 <= m k /\ m k <= d / &2 /\ M k <= d / &2`
     STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
      `!k. ?a b. (k:num) < N ==>
         (!t. &k * pi / &N <= t /\ t <= &(k+1) * pi / &N ==>
              a <= min (d / &2) (l / &2 * sin t) /\
              min (d / &2) (l / &2 * sin t) <= b) /\
         b - a <= l / &2 * pi / &N /\
         &0 <= a /\ a <= d / &2 /\ b <= d / &2`
      MP_TAC THENL
    [X_GEN_TAC `k:num` THEN ASM_CASES_TAC `(k:num) < N` THENL
     [SUBGOAL_THEN `&k * pi / &N <= &(k+1) * pi / &N` ASSUME_TAC THENL
      [REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
       MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
        [REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC; ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= &k * pi / &N` ASSUME_TAC THENL
      [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
       MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&(k+1) * pi / &N <= pi` ASSUME_TAC THENL
      [SUBGOAL_THEN `&(k+1) * pi / &N = &(k+1) / &N * pi`
         SUBST1_TAC THENL
       [REWRITE_TAC[real_div; REAL_MUL_AC]; ALL_TAC] THEN
       GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
       MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
        REWRITE_TAC[REAL_MUL_LID; REAL_OF_NUM_LE] THEN
        UNDISCH_TAC `(k:num) < N` THEN ARITH_TAC;
        ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
      MP_TAC(ISPECL [`l:real`; `d:real`; `&k * pi / &N`; `&(k+1) * pi / &N`]
        MIN_SIN_OSCILLATION) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `m0:real` (X_CHOOSE_THEN `M0:real`
        STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `m0:real` THEN EXISTS_TAC `M0:real` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
      [REPEAT STRIP_TAC THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN
       REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
       MATCH_MP_TAC REAL_LE_TRANS THEN
       EXISTS_TAC `l / &2 * (&(k + 1) * pi / &N - &k * pi / &N)` THEN
       ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
       CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `a:real = b ==> a <= b`) THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC]];
      EXISTS_TAC `&0` THEN EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[]];
     REWRITE_TAC[SKOLEM_PAIR]];
    ALL_TAC] THEN
   (* Useful subinterval facts *)
   SUBGOAL_THEN `!k. k < N ==> &k * pi / &N <= &(k+1) * pi / &N`
     ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
      ASM_REAL_ARITH_TAC];
     MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
   SUBGOAL_THEN `!k:num. k < N ==> &(k+1) * pi / &N - &k * pi / &N = pi / &N`
     ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `!k:num. k < N ==> &0 <= &k * pi / &N` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
   SUBGOAL_THEN `!k:num. k < N ==> &(k+1) * pi / &N <= pi` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&(k+1) * pi / &N = &(k+1) / &N * pi`
      SUBST1_TAC THENL
    [REWRITE_TAC[real_div; REAL_MUL_AC]; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
    [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
     REWRITE_TAC[REAL_MUL_LID; REAL_OF_NUM_LE] THEN
     UNDISCH_TAC `(k:num) < N` THEN ARITH_TAC;
     ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
   (* min(d/2, l/2*sin) is integrable on [0, pi] *)
   SUBGOAL_THEN `(\t. min (d / &2) (l / &2 * sin t))
     real_integrable_on real_interval[&0, pi]` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_MIN THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_SIN];
    ALL_TAC] THEN
   (* Per-subinterval integral lower bound *)
   SUBGOAL_THEN
     `!k. k < N ==>
       (m:num->real) k * pi / &N <=
       real_integral (real_interval [&k * pi / &N, &(k+1) * pi / &N])
         (\t. min (d / &2) (l / &2 * sin t))`
     ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
      `(m:num->real) k * pi / &N =
       m k * (&(k+1) * pi / &N - &k * pi / &N)` SUBST1_TAC THENL
    [AP_TERM_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`\t:real. (m:num->real) k`;
      `\t. min (d / &2) (l / &2 * sin t)`;
      `real_interval [&k * pi / &N, &(k+1) * pi / &N]`;
      `(m:num->real) k * (&(k+1) * pi / &N - &k * pi / &N)`;
      `real_integral (real_interval [&k * pi / &N, &(k+1) * pi / &N])
         (\t. min (d / &2) (l / &2 * sin t))`]
      HAS_REAL_INTEGRAL_LE) THEN
    ANTS_TAC THENL
    [CONJ_TAC THENL
     [REWRITE_TAC[] THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_CONST THEN
      ASM_SIMP_TAC[];
      CONJ_TAC THENL
      [MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
       MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
       MATCH_MP_TAC REAL_CONTINUOUS_ON_MIN THEN
       REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
       MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
       REWRITE_TAC[REAL_CONTINUOUS_ON_SIN];
       REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o
         check (fun th -> free_in `(m:num->real)` (concl th) &&
                          free_in `(M:num->real)` (concl th))) THEN
       ASM_REWRITE_TAC[] THEN
       DISCH_THEN(MP_TAC o CONJUNCT1) THEN
       DISCH_THEN(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN
       SIMP_TAC[]]];
     SIMP_TAC[]];
    ALL_TAC] THEN
   (* Per-subinterval integral upper bound *)
   SUBGOAL_THEN
     `!k. k < N ==>
       real_integral (real_interval [&k * pi / &N, &(k+1) * pi / &N])
         (\t. min (d / &2) (l / &2 * sin t)) <=
       (M:num->real) k * pi / &N`
     ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
      `(M:num->real) k * pi / &N =
       M k * (&(k+1) * pi / &N - &k * pi / &N)` SUBST1_TAC THENL
    [AP_TERM_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`\t. min (d / &2) (l / &2 * sin t)`;
      `\t:real. (M:num->real) k`;
      `real_interval [&k * pi / &N, &(k+1) * pi / &N]`;
      `real_integral (real_interval [&k * pi / &N, &(k+1) * pi / &N])
         (\t. min (d / &2) (l / &2 * sin t))`;
      `(M:num->real) k * (&(k+1) * pi / &N - &k * pi / &N)`]
      HAS_REAL_INTEGRAL_LE) THEN
    ANTS_TAC THENL
    [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
      MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_MIN THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_SIN];
      CONJ_TAC THENL
      [REWRITE_TAC[] THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_CONST THEN
       ASM_SIMP_TAC[];
       REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o
         check (fun th -> free_in `(m:num->real)` (concl th) &&
                          free_in `(M:num->real)` (concl th))) THEN
       ASM_REWRITE_TAC[] THEN
       DISCH_THEN(MP_TAC o CONJUNCT1) THEN
       DISCH_THEN(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN
       SIMP_TAC[]]];
     SIMP_TAC[]];
    ALL_TAC] THEN
   (* Integral splitting: sum of subinterval integrals = full integral *)
   SUBGOAL_THEN
     `!n. SUC n <= N ==>
       sum(0..n) (\k. real_integral
         (real_interval [&k * pi / &N, &(k+1) * pi / &N])
           (\t. min (d / &2) (l / &2 * sin t))) =
       real_integral (real_interval [&0, &(SUC n) * pi / &N])
         (\t. min (d / &2) (l / &2 * sin t))`
     ASSUME_TAC THENL
   [INDUCT_TAC THENL
    [(* base: n = 0 *)
     DISCH_TAC THEN REWRITE_TAC[SUM_SING_NUMSEG] THEN
     REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID; ARITH_RULE `0 + 1 = 1`] THEN
     CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_MUL_LID];
     (* step: n -> SUC n *)
     DISCH_TAC THEN
     SUBGOAL_THEN `SUC n <= N` ASSUME_TAC THENL
     [UNDISCH_TAC `SUC(SUC n) <= N` THEN ARITH_TAC; ALL_TAC] THEN
     FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
     ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
     REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN `SUC n + 1 = SUC(SUC n)` SUBST1_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
     MP_TAC(ISPECL [`\t. min (d / &2) (l / &2 * sin t)`;
       `&0`; `&(SUC(SUC n)) * pi / &N`; `&(SUC n) * pi / &N`]
       REAL_INTEGRAL_COMBINE) THEN
     ANTS_TAC THENL
     [CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
       MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
       CONJ_TAC THENL
       [REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
        [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
         [REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC; ASM_REAL_ARITH_TAC];
         MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_MIN THEN
        REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
        REWRITE_TAC[REAL_CONTINUOUS_ON_SIN]]];
      SIMP_TAC[]]];
    ALL_TAC] THEN
   (* Now assemble the sandwich *)
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `sum(0..N-1) (\k. &2 / (d * &N) * (M:num->real) k) -
               sum(0..N-1) (\k. &2 / (d * &N) * m k)` THEN
   CONJ_TAC THENL
   [(* |P(C) - I| <= U - L: sandwich *)
    MATCH_MP_TAC SANDWICH_ABS_BOUND THEN
    (* L <= P(C) *)
    CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `prob p (UNIONS (IMAGE (\k.
       {x:A | x IN prob_carrier p /\ X x <= (m:num->real) k /\
              &k * pi / &N < Theta x /\ Theta x <= &(k+1) * pi / &N})
       (0..N-1)))` THEN
     CONJ_TAC THENL
     [(* sum P(A_k) = P(UNIONS A_k) *)
      SUBGOAL_THEN
        `!k. k <= N - 1 ==>
          prob p {x:A | x IN prob_carrier p /\ X x <= (m:num->real) k /\
            &k * pi / &N < Theta x /\ Theta x <= &(k+1) * pi / &N} =
          &2 / (d * &N) * m k`
        ASSUME_TAC THENL
      [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
       SUBGOAL_THEN `(k:num) < N` ASSUME_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `1 <= N /\ k <= N - 1 ==> k < N`) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
       MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `Theta:A->real`;
         `d:real`; `(m:num->real) k`;
         `&k * pi / &N`; `&(k+1) * pi / &N`] UNIFORM_RECT_PROB) THEN
       ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
        [ASM_MESON_TAC[];
         ASM_MESON_TAC[];
         ASM_SIMP_TAC[REAL_LT_IMP_LE];
         ASM_SIMP_TAC[];
         ASM_SIMP_TAC[REAL_LT_IMP_LE]];
        DISCH_THEN SUBST1_TAC THEN
        SUBGOAL_THEN `&(k+1) * pi / &N - &k * pi / &N = pi / &N`
          SUBST1_TAC THENL
        [REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
         ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_FIELD
          `~(d = &0) /\ ~(pi = &0) /\ ~(&N = &0) ==>
           mk / (d / &2) * (pi / &N) / pi = &2 / (d * &N) * mk`]];
       ALL_TAC] THEN
      (* A_k events are measurable *)
      SUBGOAL_THEN
        `!k. k <= N - 1 ==>
          {x:A | x IN prob_carrier p /\ X x <= (m:num->real) k /\
            &k * pi / &N < Theta x /\ Theta x <= &(k+1) * pi / &N}
          IN prob_events p`
        ASSUME_TAC THENL
      [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
       SUBGOAL_THEN
         `{x:A | x IN prob_carrier p /\ X x <= (m:num->real) k /\
           &k * pi / &N < Theta x /\ Theta x <= &(k+1) * pi / &N} =
          {x | x IN prob_carrier p /\ X x <= m k /\
               Theta x <= &(k+1) * pi / &N} DIFF
          {x | x IN prob_carrier p /\ X x <= m k /\
               Theta x <= &k * pi / &N}`
         SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM; GSYM REAL_NOT_LE;
                     DE_MORGAN_THM] THEN
        GEN_TAC THEN ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC PROB_DIFF_IN_EVENTS THEN CONJ_TAC THEN
        (SUBGOAL_THEN
          `!t. {x:A | x IN prob_carrier p /\ X x <= (m:num->real) k /\ Theta x <= t} =
           {x | x IN prob_carrier p /\ X x <= m k} INTER
           {x | x IN prob_carrier p /\ Theta x <= t}`
          (fun th -> ONCE_REWRITE_TAC[th]) THENL
        [GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN MESON_TAC[];
         MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN
         ASM_SIMP_TAC[DIST_FN_IN_EVENTS]])];
       ALL_TAC] THEN
      (* A_k pairwise disjoint *)
      SUBGOAL_THEN
        `!i j. i <= N - 1 /\ j <= N - 1 /\ ~(i = j) ==>
          DISJOINT
            ({x:A | x IN prob_carrier p /\ X x <= (m:num->real) i /\
              &i * pi / &N < Theta x /\ Theta x <= &(i+1) * pi / &N})
            ({x | x IN prob_carrier p /\ X x <= m j /\
              &j * pi / &N < Theta x /\ Theta x <= &(j+1) * pi / &N})`
        ASSUME_TAC THENL
      [REPEAT STRIP_TAC THEN
       REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_ELIM_THM] THEN
       X_GEN_TAC `w:A` THEN
       ASM_CASES_TAC `(w:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
       STRIP_TAC THEN
       SUBGOAL_THEN `&i * pi / &N < &(j+1) * pi / &N /\
                      &j * pi / &N < &(i+1) * pi / &N` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
       SUBGOAL_THEN `~(i:num = j)` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
       REWRITE_TAC[REAL_ARITH `a * x / y < b * x / y <=> (a - b) * x / y < &0`;
                    REAL_ARITH `c * x / y < d * x / y <=> (c - d) * x / y < &0`] THEN
       DISCH_TAC THEN
       ASM_CASES_TAC `i:num < j` THENL
       [SUBGOAL_THEN `&(i+1) <= &j` MP_TAC THENL
        [REWRITE_TAC[REAL_OF_NUM_LE] THEN
         UNDISCH_TAC `i:num < j` THEN ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
        DISCH_TAC THEN
        DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) MP_TAC) THEN
        REWRITE_TAC[REAL_NOT_LT] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
        [ASM_REAL_ARITH_TAC;
         MATCH_MP_TAC REAL_LT_IMP_LE THEN
         MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]];
        SUBGOAL_THEN `&(j+1) <= &i` MP_TAC THENL
        [REWRITE_TAC[REAL_OF_NUM_LE] THEN
         UNDISCH_TAC `~(i:num < j)` THEN
         UNDISCH_TAC `~(i:num = j)` THEN ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
        DISCH_TAC THEN
        DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (K ALL_TAC)) THEN
        REWRITE_TAC[REAL_NOT_LT] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
        [ASM_REAL_ARITH_TAC;
         MATCH_MP_TAC REAL_LT_IMP_LE THEN
         MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]]];
       ALL_TAC] THEN
      MP_TAC(ISPECL [`p:A prob_space`;
        `\k. {x:A | x IN prob_carrier p /\ X x <= (m:num->real) k /\
          &k * pi / &N < Theta x /\ Theta x <= &(k+1) * pi / &N}`;
        `N - 1`] PROB_FINITE_ADDITIVE) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `a:real = b ==> a <= b`) THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[];
      (* P(UNIONS A_k) <= P(crossing) *)
      SUBGOAL_THEN
        `!k. k <= N - 1 ==>
          {x:A | x IN prob_carrier p /\ X x <= (m:num->real) k /\
            &k * pi / &N < Theta x /\ Theta x <= &(k+1) * pi / &N}
          IN prob_events p`
        ASSUME_TAC THENL
      [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
       SUBGOAL_THEN
         `{x:A | x IN prob_carrier p /\ X x <= (m:num->real) k /\
           &k * pi / &N < Theta x /\ Theta x <= &(k+1) * pi / &N} =
          {x | x IN prob_carrier p /\ X x <= m k /\
               Theta x <= &(k+1) * pi / &N} DIFF
          {x | x IN prob_carrier p /\ X x <= m k /\
               Theta x <= &k * pi / &N}`
         SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM; GSYM REAL_NOT_LE;
                     DE_MORGAN_THM] THEN
        GEN_TAC THEN ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC PROB_DIFF_IN_EVENTS THEN CONJ_TAC THEN
        (SUBGOAL_THEN
          `!t. {x:A | x IN prob_carrier p /\ X x <= (m:num->real) k /\ Theta x <= t} =
           {x | x IN prob_carrier p /\ X x <= m k} INTER
           {x | x IN prob_carrier p /\ Theta x <= t}`
          (fun th -> ONCE_REWRITE_TAC[th]) THENL
        [GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN MESON_TAC[];
         MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN
         ASM_SIMP_TAC[DIST_FN_IN_EVENTS]])];
       ALL_TAC] THEN
      MATCH_MP_TAC PROB_MONO THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
      [MATCH_MP_TAC PROB_FINITE_UNION_IN_EVENTS THEN
       SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG] THEN
       REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_NUMSEG] THEN
       REPEAT STRIP_TAC THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `x:num` o check
         (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "prob_events")) (concl th))) THEN
       ASM_REWRITE_TAC[];
       REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE; IN_NUMSEG; IN_ELIM_THM] THEN
       X_GEN_TAC `w:A` THEN
       DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
       ASM_REWRITE_TAC[] THEN
       (* m(k) <= min(d/2, l/2*sin(Theta(w))) <= l/2*sin(Theta(w)) *)
       MATCH_MP_TAC REAL_LE_TRANS THEN
       EXISTS_TAC `(m:num->real) k` THEN ASM_REWRITE_TAC[] THEN
       MATCH_MP_TAC REAL_LE_TRANS THEN
       EXISTS_TAC `min (d / &2) (l / &2 * sin(Theta(w:A)))` THEN
       CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o
          check (fun th -> free_in `(m:num->real)` (concl th) &&
                           free_in `(M:num->real)` (concl th))) THEN
        ANTS_TAC THENL
        [UNDISCH_TAC `k <= N - 1` THEN UNDISCH_TAC `1 <= N` THEN ARITH_TAC;
         ALL_TAC] THEN
        DISCH_THEN(MP_TAC o CONJUNCT1) THEN
        DISCH_THEN(MP_TAC o SPEC `Theta(w:A):real`) THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_MIN_LE] THEN DISJ2_TAC THEN REAL_ARITH_TAC]]];
     (* P(crossing) <= U *)
     CONJ_TAC THENL
     [(* Upper bound: P(crossing) <= sum P(B_k) *)
      (* B_k events are measurable *)
      SUBGOAL_THEN
        `!k. k <= N - 1 ==>
          {x:A | x IN prob_carrier p /\ X x <= (M:num->real) k /\
            &k * pi / &N < Theta x /\ Theta x <= &(k+1) * pi / &N}
          IN prob_events p`
        ASSUME_TAC THENL
      [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
       SUBGOAL_THEN
         `{x:A | x IN prob_carrier p /\ X x <= (M:num->real) k /\
           &k * pi / &N < Theta x /\ Theta x <= &(k+1) * pi / &N} =
          {x | x IN prob_carrier p /\ X x <= M k /\
               Theta x <= &(k+1) * pi / &N} DIFF
          {x | x IN prob_carrier p /\ X x <= M k /\
               Theta x <= &k * pi / &N}`
         SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM; GSYM REAL_NOT_LE;
                     DE_MORGAN_THM] THEN
        GEN_TAC THEN ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC PROB_DIFF_IN_EVENTS THEN CONJ_TAC THEN
        (SUBGOAL_THEN
          `!t. {x:A | x IN prob_carrier p /\ X x <= (M:num->real) k /\ Theta x <= t} =
           {x | x IN prob_carrier p /\ X x <= M k} INTER
           {x | x IN prob_carrier p /\ Theta x <= t}`
          (fun th -> ONCE_REWRITE_TAC[th]) THENL
        [GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN MESON_TAC[];
         MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN
         ASM_SIMP_TAC[DIST_FN_IN_EVENTS]])];
       ALL_TAC] THEN
      (* UNIONS B_k is measurable *)
      SUBGOAL_THEN
        `UNIONS (IMAGE (\k.
          {x:A | x IN prob_carrier p /\ X x <= (M:num->real) k /\
           &k * pi / &N < Theta x /\ Theta x <= &(k+1) * pi / &N})
          (0..N-1)) IN prob_events p`
        ASSUME_TAC THENL
      [MATCH_MP_TAC PROB_FINITE_UNION_IN_EVENTS THEN
       SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG] THEN
       REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_NUMSEG] THEN
       ASM_MESON_TAC[];
       ALL_TAC] THEN
      (* B_k pairwise disjoint *)
      SUBGOAL_THEN
        `!i j. i <= N - 1 /\ j <= N - 1 /\ ~(i = j) ==>
          DISJOINT
            ({x:A | x IN prob_carrier p /\ X x <= (M:num->real) i /\
              &i * pi / &N < Theta x /\ Theta x <= &(i+1) * pi / &N})
            ({x | x IN prob_carrier p /\ X x <= M j /\
              &j * pi / &N < Theta x /\ Theta x <= &(j+1) * pi / &N})`
        ASSUME_TAC THENL
      [REPEAT STRIP_TAC THEN
       REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_ELIM_THM] THEN
       X_GEN_TAC `w:A` THEN
       ASM_CASES_TAC `(w:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
       STRIP_TAC THEN
       SUBGOAL_THEN `&i * pi / &N < &(j+1) * pi / &N /\
                      &j * pi / &N < &(i+1) * pi / &N` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
       SUBGOAL_THEN `~(i:num = j)` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
       REWRITE_TAC[REAL_ARITH `a * x / y < b * x / y <=> (a - b) * x / y < &0`;
                    REAL_ARITH `c * x / y < d * x / y <=> (c - d) * x / y < &0`] THEN
       DISCH_TAC THEN
       ASM_CASES_TAC `i:num < j` THENL
       [SUBGOAL_THEN `&(i+1) <= &j` MP_TAC THENL
        [REWRITE_TAC[REAL_OF_NUM_LE] THEN
         UNDISCH_TAC `i:num < j` THEN ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
        DISCH_TAC THEN
        DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) MP_TAC) THEN
        REWRITE_TAC[REAL_NOT_LT] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
        [ASM_REAL_ARITH_TAC;
         MATCH_MP_TAC REAL_LT_IMP_LE THEN
         MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]];
        SUBGOAL_THEN `&(j+1) <= &i` MP_TAC THENL
        [REWRITE_TAC[REAL_OF_NUM_LE] THEN
         UNDISCH_TAC `~(i:num < j)` THEN
         UNDISCH_TAC `~(i:num = j)` THEN ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
        DISCH_TAC THEN
        DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (K ALL_TAC)) THEN
        REWRITE_TAC[REAL_NOT_LT] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
        [ASM_REAL_ARITH_TAC;
         MATCH_MP_TAC REAL_LT_IMP_LE THEN
         MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]]];
       ALL_TAC] THEN
      (* P(B_k) = 2/(d*N) * M(k) *)
      SUBGOAL_THEN
        `!k. k <= N - 1 ==>
          prob p {x:A | x IN prob_carrier p /\ X x <= (M:num->real) k /\
            &k * pi / &N < Theta x /\ Theta x <= &(k+1) * pi / &N} =
          &2 / (d * &N) * M k`
        ASSUME_TAC THENL
      [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
       SUBGOAL_THEN `(k:num) < N` ASSUME_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `1 <= N /\ k <= N - 1 ==> k < N`) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
       (* Derive M k <= d/2 and &0 <= M k from Skolem bound *)
       SUBGOAL_THEN `(M:num->real) k <= d / &2` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
       SUBGOAL_THEN `&0 <= (M:num->real) k` ASSUME_TAC THENL
       [SUBGOAL_THEN `(m:num->real) k <= (M:num->real) k` MP_TAC THENL
        [FIRST_ASSUM(MP_TAC o SPEC `k:num` o
           check (fun th -> free_in `(m:num->real)` (concl th) &&
                            free_in `(M:num->real)` (concl th) &&
                            is_forall (concl th))) THEN
         REWRITE_TAC[ASSUME `(k:num) < N`] THEN
         DISCH_THEN(MP_TAC o CONJUNCT1) THEN
         DISCH_THEN(MP_TAC o SPEC `&k * pi / &N`) THEN
         ANTS_TAC THENL
         [CONJ_TAC THENL [REAL_ARITH_TAC; ASM_SIMP_TAC[]]; ALL_TAC] THEN
         REAL_ARITH_TAC;
         ALL_TAC] THEN
        SUBGOAL_THEN `&0 <= (m:num->real) k` MP_TAC THENL
        [ASM_MESON_TAC[]; ALL_TAC] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
       MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `Theta:A->real`;
         `d:real`; `(M:num->real) k`;
         `&k * pi / &N`; `&(k+1) * pi / &N`] UNIFORM_RECT_PROB) THEN
       ASM_REWRITE_TAC[] THEN
       ANTS_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_IMP_LE];
        DISCH_THEN SUBST1_TAC THEN
        SUBGOAL_THEN `&(k+1) * pi / &N - &k * pi / &N = pi / &N`
          SUBST1_TAC THENL
        [REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
         ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_FIELD
          `~(d = &0) /\ ~(pi = &0) /\ ~(&N = &0) ==>
           mk / (d / &2) * (pi / &N) / pi = &2 / (d * &N) * mk`]];
       ALL_TAC] THEN
      (* P(UNIONS B_k) = sum P(B_k) *)
      SUBGOAL_THEN
        `prob p (UNIONS (IMAGE (\k.
          {x:A | x IN prob_carrier p /\ X x <= (M:num->real) k /\
           &k * pi / &N < Theta x /\ Theta x <= &(k+1) * pi / &N})
          (0..N-1))) =
         sum(0..N-1) (\k. &2 / (d * &N) * (M:num->real) k)`
        ASSUME_TAC THENL
      [MP_TAC(ISPECL [`p:A prob_space`;
        `\k. {x:A | x IN prob_carrier p /\ X x <= (M:num->real) k /\
          &k * pi / &N < Theta x /\ Theta x <= &(k+1) * pi / &N}`;
        `N - 1`] PROB_FINITE_ADDITIVE) THEN
       ASM_REWRITE_TAC[] THEN
       DISCH_THEN SUBST1_TAC THEN
       MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
       REWRITE_TAC[] THEN ASM_SIMP_TAC[];
       ALL_TAC] THEN
      (* P(crossing) <= P(UNIONS B_k): containment via null sets *)
      (* P(Theta <= 0) = 0 *)
      SUBGOAL_THEN `prob p {x:A | x IN prob_carrier p /\ Theta x <= &0} = &0`
        ASSUME_TAC THENL
      [SUBGOAL_THEN `prob p {x:A | x IN prob_carrier p /\ Theta x <= &0} =
                      distribution_fn p (Theta:A->real) (&0)` SUBST1_TAC THENL
       [REWRITE_TAC[distribution_fn]; ALL_TAC] THEN
       MP_TAC(ISPECL [`p:A prob_space`; `Theta:A->real`; `pi`; `&0`]
         UNIFORM_ZERO_CDF_RANGE) THEN
       ASM_REWRITE_TAC[REAL_LE_REFL] THEN
       ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
       SIMP_TAC[real_div; REAL_MUL_LZERO];
       ALL_TAC] THEN

      (* P(Theta > pi) = 0 *)
      SUBGOAL_THEN
        `prob p (prob_carrier p DIFF
          {x:A | x IN prob_carrier p /\ Theta x <= pi}) = &0`
        ASSUME_TAC THENL
      [MP_TAC(ISPECL [`p:A prob_space`;
                        `{x:A | x IN prob_carrier p /\ Theta x <= pi}`]
         PROB_COMPL) THEN
       ANTS_TAC THENL [ASM_SIMP_TAC[DIST_FN_IN_EVENTS]; ALL_TAC] THEN
       DISCH_THEN SUBST1_TAC THEN
       SUBGOAL_THEN `prob p {x:A | x IN prob_carrier p /\ Theta x <= pi} = &1`
         (fun th -> REWRITE_TAC[th] THEN REAL_ARITH_TAC) THEN
       SUBGOAL_THEN `prob p {x:A | x IN prob_carrier p /\ Theta x <= pi} =
                      distribution_fn p (Theta:A->real) pi` SUBST1_TAC THENL
       [REWRITE_TAC[distribution_fn]; ALL_TAC] THEN
       MATCH_MP_TAC UNIFORM_RV_CDF_HIGH THEN
       EXISTS_TAC `&0` THEN EXISTS_TAC `pi` THEN
       ASM_REWRITE_TAC[REAL_LE_REFL];
       ALL_TAC] THEN

      (* P(X > d/2) = 0 -- NEW for general case *)
      SUBGOAL_THEN
        `prob p (prob_carrier p DIFF
          {x:A | x IN prob_carrier p /\ X x <= d / &2}) = &0`
        ASSUME_TAC THENL
      [MP_TAC(ISPECL [`p:A prob_space`;
                        `{x:A | x IN prob_carrier p /\ X x <= d / &2}`]
         PROB_COMPL) THEN
       ANTS_TAC THENL [ASM_SIMP_TAC[DIST_FN_IN_EVENTS]; ALL_TAC] THEN
       DISCH_THEN SUBST1_TAC THEN
       SUBGOAL_THEN `prob p {x:A | x IN prob_carrier p /\ X x <= d / &2} = &1`
         (fun th -> REWRITE_TAC[th] THEN REAL_ARITH_TAC) THEN
       SUBGOAL_THEN `prob p {x:A | x IN prob_carrier p /\ X x <= d / &2} =
                      distribution_fn p (X:A->real) (d / &2)` SUBST1_TAC THENL
       [REWRITE_TAC[distribution_fn]; ALL_TAC] THEN
       MATCH_MP_TAC UNIFORM_RV_CDF_HIGH THEN
       EXISTS_TAC `&0` THEN EXISTS_TAC `d / &2` THEN
       ASM_REWRITE_TAC[REAL_LE_REFL];
       ALL_TAC] THEN
      TRANS_TAC REAL_LE_TRANS `prob p (UNIONS (IMAGE (\k.
        {x:A | x IN prob_carrier p /\ X x <= (M:num->real) k /\
               &k * pi / &N < Theta x /\ Theta x <= &(k+1) * pi / &N})
        (0..N-1)) UNION
        {x:A | x IN prob_carrier p /\ Theta x <= &0} UNION
        (prob_carrier p DIFF
          {x:A | x IN prob_carrier p /\ Theta x <= pi}) UNION
        (prob_carrier p DIFF
          {x:A | x IN prob_carrier p /\ X x <= d / &2}))` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC PROB_MONO THEN ASM_REWRITE_TAC[] THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC PROB_UNION_IN_EVENTS THEN CONJ_TAC THENL
        [FIRST_X_ASSUM ACCEPT_TAC;
         MATCH_MP_TAC PROB_UNION_IN_EVENTS THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[DIST_FN_IN_EVENTS];
          MATCH_MP_TAC PROB_UNION_IN_EVENTS THEN CONJ_TAC THENL
          [ASM_SIMP_TAC[PROB_COMPL_IN_EVENTS; DIST_FN_IN_EVENTS];
           ASM_SIMP_TAC[PROB_COMPL_IN_EVENTS; DIST_FN_IN_EVENTS]]]];
        REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS; EXISTS_IN_IMAGE;
                     IN_NUMSEG; IN_ELIM_THM; IN_DIFF] THEN
        X_GEN_TAC `w:A` THEN STRIP_TAC THEN
        ASM_CASES_TAC `Theta(w:A) <= &0` THENL
        [DISJ2_TAC THEN DISJ1_TAC THEN
         ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_CASES_TAC `Theta(w:A) <= pi` THENL
        [ALL_TAC;
         DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
         ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC] THEN
        ASM_CASES_TAC `(X:A->real) w <= d / &2` THENL
        [ALL_TAC;
         DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
         ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC] THEN
        DISJ1_TAC THEN
        SUBGOAL_THEN `&0 < Theta(w:A)` ASSUME_TAC THENL
        [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        (* Find strip k via WOP *)
        SUBGOAL_THEN `?k. k < N /\ &k * pi / &N < Theta(w:A) /\
                          Theta w <= &(k+1) * pi / &N`
          STRIP_ASSUME_TAC THENL
        [SUBGOAL_THEN `?k. k < N /\ Theta(w:A) <= &(k+1) * pi / &N`
           STRIP_ASSUME_TAC THENL
         [EXISTS_TAC `N - 1` THEN CONJ_TAC THENL
          [UNDISCH_TAC `1 <= N` THEN ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `&(N - 1 + 1) = &N` SUBST1_TAC THENL
          [AP_TERM_TAC THEN UNDISCH_TAC `1 <= N` THEN ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[REAL_FIELD `~(&N = &0) ==> &N * pi / &N = pi`];
          ALL_TAC] THEN
         MP_TAC(BETA_RULE(fst(EQ_IMP_RULE(ISPEC
           `\k. k < N /\ Theta(w:A) <= &(k+1) * pi / &N` num_WOP)))) THEN
         ANTS_TAC THENL
         [EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
         DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
         EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN
         ASM_CASES_TAC `j = 0` THENL
         [ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
          ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> &0 / n < t`]; ALL_TAC] THEN
         FIRST_X_ASSUM(MP_TAC o SPEC `j - 1`) THEN
         ASM_REWRITE_TAC[DE_MORGAN_THM] THEN
         ANTS_TAC THENL
         [UNDISCH_TAC `~(j = 0)` THEN ARITH_TAC; ALL_TAC] THEN
         DISCH_THEN DISJ_CASES_TAC THENL
         [SUBGOAL_THEN `j - 1 < N`
           (fun th -> UNDISCH_TAC `~(j - 1 < N)` THEN REWRITE_TAC[th]) THEN
          UNDISCH_TAC `(j:num) < N` THEN UNDISCH_TAC `~(j = 0)` THEN
          ARITH_TAC;
          ALL_TAC] THEN
         SUBGOAL_THEN `&(j - 1 + 1) = &j:real` SUBST_ALL_TAC THENL
         [AP_TERM_TAC THEN UNDISCH_TAC `~(j = 0)` THEN ARITH_TAC;
          ALL_TAC] THEN
         ASM_REAL_ARITH_TAC;
         ALL_TAC] THEN
        EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
        [UNDISCH_TAC `(k:num) < N` THEN UNDISCH_TAC `1 <= N` THEN ARITH_TAC;
         ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN
        (* X(w) <= M(k): since X(w) <= d/2 and X(w) <= l/2*sin(Theta(w)) <= l/2*M_sin *)
        (* Actually: X(w) <= min(d/2, l/2*sin(Theta(w))) <= M(k) *)
        TRANS_TAC REAL_LE_TRANS `min (d / &2) (l / &2 * sin(Theta(w:A)))` THEN
        CONJ_TAC THENL
        [REWRITE_TAC[REAL_LE_MIN] THEN ASM_REWRITE_TAC[];
         FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o
           check (fun th -> free_in `(m:num->real)` (concl th) &&
                            free_in `(M:num->real)` (concl th))) THEN
         ASM_REWRITE_TAC[] THEN
         DISCH_THEN(MP_TAC o CONJUNCT1) THEN
         DISCH_THEN(MP_TAC o SPEC `Theta(w:A):real`) THEN
         ASM_REAL_ARITH_TAC]];
       (* Bound P(crossing UNION ...) <= P(UNIONS B_k) + 0 + 0 + 0 *)
       TRANS_TAC REAL_LE_TRANS `prob p (UNIONS (IMAGE (\k.
         {x:A | x IN prob_carrier p /\ X x <= (M:num->real) k /\
                &k * pi / &N < Theta x /\ Theta x <= &(k+1) * pi / &N})
         (0..N-1)) UNION
         {x:A | x IN prob_carrier p /\ Theta x <= &0} UNION
         (prob_carrier p DIFF
           {x:A | x IN prob_carrier p /\ Theta x <= pi})) +
         prob p (prob_carrier p DIFF
           {x:A | x IN prob_carrier p /\ X x <= d / &2})` THEN
       CONJ_TAC THENL
       [REWRITE_TAC[GSYM UNION_ASSOC] THEN
        SUBADDITIVE_TAC THEN
        ASM_SIMP_TAC[PROB_UNION_IN_EVENTS; PROB_COMPL_IN_EVENTS;
                      DIST_FN_IN_EVENTS];
        PROB_ZERO_TAC THEN
        TRANS_TAC REAL_LE_TRANS `prob p (UNIONS (IMAGE (\k.
          {x:A | x IN prob_carrier p /\ X x <= (M:num->real) k /\
                 &k * pi / &N < Theta x /\ Theta x <= &(k+1) * pi / &N})
          (0..N-1)) UNION
          {x:A | x IN prob_carrier p /\ Theta x <= &0}) +
          prob p (prob_carrier p DIFF
            {x:A | x IN prob_carrier p /\ Theta x <= pi})` THEN
        CONJ_TAC THENL
        [REWRITE_TAC[GSYM UNION_ASSOC] THEN
         SUBADDITIVE_TAC THEN
         ASM_SIMP_TAC[PROB_UNION_IN_EVENTS; PROB_COMPL_IN_EVENTS;
                       DIST_FN_IN_EVENTS];
         PROB_ZERO_TAC THEN
         TRANS_TAC REAL_LE_TRANS `prob p (UNIONS (IMAGE (\k.
           {x:A | x IN prob_carrier p /\ X x <= (M:num->real) k /\
                  &k * pi / &N < Theta x /\ Theta x <= &(k+1) * pi / &N})
           (0..N-1))) +
           prob p {x:A | x IN prob_carrier p /\ Theta x <= &0}` THEN
         CONJ_TAC THENL
         [SUBADDITIVE_TAC THEN
          ASM_SIMP_TAC[DIST_FN_IN_EVENTS];
          PROB_ZERO_TAC THEN
          FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
          REWRITE_TAC[REAL_LE_REFL]]]]];
      (* L <= I /\ I <= U *)
      ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
      [(* L <= I: sum m(k)*2/(d*N) <= 2/(d*pi) * integral *)
       REWRITE_TAC[SUM_LMUL] THEN
       SUBGOAL_THEN `&0 < &2 / d` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
        REAL_ARITH_TAC; ALL_TAC] THEN
       ASM_SIMP_TAC[REAL_FIELD `~(d = &0) /\ ~(&N = &0) ==>
         &2 / (d * &N) * s = (&2 / d) * (s / &N)`;
         REAL_FIELD `~(d = &0) /\ ~(pi = &0) ==>
         &2 / (d * pi) * i = (&2 / d) * (i / pi)`] THEN
       ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
       REWRITE_TAC[real_div; GSYM SUM_RMUL] THEN
       TRANS_TAC REAL_LE_TRANS `sum(0..N-1)
         (\k. real_integral (real_interval [&k * pi / &N, &(k+1) * pi / &N])
                (\t. min (d * inv(&2)) ((l * inv(&2)) * sin t)) * inv pi)` THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
        BETA_TAC THEN
        SUBGOAL_THEN `(m:num->real) k * inv(&N) =
          (m k * pi * inv(&N)) * inv pi` SUBST1_TAC THENL
        [UNDISCH_TAC `~(pi = &0)` THEN UNDISCH_TAC `~(&N = &0)` THEN
         CONV_TAC REAL_FIELD; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
        [REWRITE_TAC[GSYM real_div] THEN
         FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check
           (fun th -> free_in `real_integral` (concl th) &&
                      free_in `(m:num->real)` (concl th) &&
                      not (free_in `(M:num->real)` (concl th)))) THEN
         ANTS_TAC THENL
         [UNDISCH_TAC `k <= N - 1` THEN UNDISCH_TAC `1 <= N` THEN ARITH_TAC;
          SIMP_TAC[]];
         MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC];
        REWRITE_TAC[SUM_RMUL] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
        [MATCH_MP_TAC(REAL_ARITH `a:real = b ==> a <= b`) THEN
         REWRITE_TAC[GSYM real_div] THEN
         SUBGOAL_THEN `SUC(N - 1) = N` ASSUME_TAC THENL
         [UNDISCH_TAC `1 <= N` THEN ARITH_TAC; ALL_TAC] THEN
         FIRST_X_ASSUM(MP_TAC o SPEC `N - 1` o check
           (fun th -> free_in `SUC` (concl th))) THEN
         ASM_REWRITE_TAC[LE_REFL] THEN
         DISCH_THEN SUBST1_TAC THEN
         ASM_SIMP_TAC[REAL_FIELD `~(&N = &0) ==> &N * pi / &N = pi`];
         MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC]];
       (* I <= U: 2/(d*pi) * integral <= sum M(k)*2/(d*N) *)
       REWRITE_TAC[SUM_LMUL] THEN
       SUBGOAL_THEN `&0 < &2 / d` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
        REAL_ARITH_TAC; ALL_TAC] THEN
       ASM_SIMP_TAC[REAL_FIELD `~(d = &0) /\ ~(&N = &0) ==>
         &2 / (d * &N) * s = (&2 / d) * (s / &N)`;
         REAL_FIELD `~(d = &0) /\ ~(pi = &0) ==>
         &2 / (d * pi) * i = (&2 / d) * (i / pi)`] THEN
       ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
       REWRITE_TAC[real_div; GSYM SUM_RMUL] THEN
       TRANS_TAC REAL_LE_TRANS `sum(0..N-1)
         (\k. real_integral (real_interval [&k * pi / &N, &(k+1) * pi / &N])
                (\t. min (d * inv(&2)) ((l * inv(&2)) * sin t)) * inv pi)` THEN
       CONJ_TAC THENL
       [REWRITE_TAC[SUM_RMUL] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
        [MATCH_MP_TAC(REAL_ARITH `a = b ==> b <= a`) THEN
         REWRITE_TAC[GSYM real_div] THEN
         SUBGOAL_THEN `SUC(N - 1) = N` ASSUME_TAC THENL
         [UNDISCH_TAC `1 <= N` THEN ARITH_TAC; ALL_TAC] THEN
         FIRST_X_ASSUM(MP_TAC o SPEC `N - 1` o check
           (fun th -> free_in `SUC` (concl th))) THEN
         ASM_REWRITE_TAC[LE_REFL] THEN
         DISCH_THEN SUBST1_TAC THEN
         ASM_SIMP_TAC[REAL_FIELD `~(&N = &0) ==> &N * pi / &N = pi`];
         MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
        BETA_TAC THEN
        SUBGOAL_THEN `(M:num->real) k * inv(&N) =
          (M k * pi * inv(&N)) * inv pi` SUBST1_TAC THENL
        [UNDISCH_TAC `~(pi = &0)` THEN UNDISCH_TAC `~(&N = &0)` THEN
         CONV_TAC REAL_FIELD; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
        [REWRITE_TAC[GSYM real_div] THEN
         FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check
           (fun th -> free_in `real_integral` (concl th) &&
                      free_in `(M:num->real)` (concl th))) THEN
         ANTS_TAC THENL
         [UNDISCH_TAC `k <= N - 1` THEN UNDISCH_TAC `1 <= N` THEN ARITH_TAC;
          SIMP_TAC[]];
         MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC]]]]];
     (* Gap bound: U - L <= l*pi/(d*N) *)
     REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN
     REWRITE_TAC[REAL_ARITH `a * b - a * c = a * (b - c)`] THEN
     REWRITE_TAC[SUM_LMUL] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `&2 / (d * &N) * sum(0..N-1) (\k. l / &2 * pi / &N)` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
       [REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_SIMP_TAC[REAL_LT_MUL]];
       MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o
         check (fun th -> free_in `(m:num->real)` (concl th) &&
                          free_in `(M:num->real)` (concl th))) THEN
       ANTS_TAC THENL
       [UNDISCH_TAC `k <= N - 1` THEN UNDISCH_TAC `1 <= N` THEN ARITH_TAC;
        SIMP_TAC[]]];
      REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0] THEN
      SUBGOAL_THEN `N - 1 + 1 = N` SUBST1_TAC THENL
      [UNDISCH_TAC `1 <= N` THEN ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `a:real = b ==> a <= b`) THEN
      UNDISCH_TAC `~(&N = &0)` THEN UNDISCH_TAC `~(d = &0)` THEN
      CONV_TAC REAL_FIELD]]);;

(* ===================================================================== *)
(* BUFFON_GENERAL_BRIDGE: crossing probability = integral formula        *)
(* (epsilon-delta from core bound, no l <= d hypothesis)                 *)
(* ===================================================================== *)

let BUFFON_GENERAL_BRIDGE = prove
  (`!p:A prob_space X Theta l d.
      &0 < l /\ &0 < d /\
      uniform_rv p X (&0) (d / &2) /\
      uniform_rv p Theta (&0) pi /\
      indep_rv p X Theta
      ==> prob p {x | x IN prob_carrier p /\ X x <= (l / &2) * sin(Theta x)} =
          (&2 / (d * pi)) *
          real_integral (real_interval [&0, pi])
            (\t. min (d / &2) (l / &2 * sin t))`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC REAL_EQ_EPSILON THEN
   X_GEN_TAC `e:real` THEN DISCH_TAC THEN
   SUBGOAL_THEN `&0 < pi` ASSUME_TAC THENL [REWRITE_TAC[PI_POS]; ALL_TAC] THEN
   SUBGOAL_THEN `&0 < d * pi` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
   SUBGOAL_THEN `~(d = &0)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `~(pi = &0)` ASSUME_TAC THENL
   [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `~(d * pi = &0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_ENTIRE]; ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `Theta:A->real`;
                   `l:real`; `d:real`] BUFFON_GENERAL_CORE_BOUND) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   MP_TAC(SPEC `l * pi / (d * e)` REAL_ARCH_LT) THEN
   DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
   SUBGOAL_THEN `1 <= N` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= N <=> ~(N = 0)`] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `l * pi / (d * e) < &0` THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> x < &0 ==> F`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_MUL];
    ALL_TAC] THEN
   SUBGOAL_THEN `&0 < &N` ASSUME_TAC THENL
   [UNDISCH_TAC `1 <= N` THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `&0 < d * &N` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `l * pi / (d * &N)` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `&0 < d * e` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
   SUBGOAL_THEN `l * pi / (d * &N) = (l * pi) / (d * &N)` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
   SUBGOAL_THEN `(l * pi) / (d * e) < &N` MP_TAC THENL
   [UNDISCH_TAC `l * pi / (d * e) < &N` THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
   REWRITE_TAC[REAL_MUL_AC]);;

(* ===================================================================== *)
(* BUFFON_GENERAL: unified integral form (commuted coefficient)          *)
(* ===================================================================== *)

let BUFFON_GENERAL = prove
  (`!p:A prob_space X Theta l d.
      &0 < l /\ &0 < d /\
      uniform_rv p X (&0) (d / &2) /\
      uniform_rv p Theta (&0) pi /\
      indep_rv p X Theta
      ==> prob p {x | x IN prob_carrier p /\ X x <= (l / &2) * sin(Theta x)} =
          (&2 / (pi * d)) *
          real_integral (real_interval [&0, pi])
            (\t. min (d / &2) (l / &2 * sin t))`,
   REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `Theta:A->real`;
                   `l:real`; `d:real`] BUFFON_GENERAL_BRIDGE) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC[REAL_MUL_AC]);;

(* ===================================================================== *)
(* Short needle integral: when l <= d, min(d/2, l/2*sin t) = l/2*sin t  *)
(* ===================================================================== *)

let MIN_SIN_INTEGRAL_SHORT = prove
  (`!l d. &0 < l /\ &0 < d /\ l <= d
      ==> real_integral (real_interval [&0, pi])
            (\t. min (d / &2) (l / &2 * sin t)) = l`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN
     `!t. t IN real_interval [&0, pi]
       ==> min (d / &2) (l / &2 * sin t) = l / &2 * sin t`
     ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    REWRITE_TAC[real_min] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `l / &2 * sin t <= d / &2` MP_TAC THENL
    [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `l / &2 * &1` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
      [ASM_REAL_ARITH_TAC; MP_TAC(SPEC `t:real` SIN_BOUNDS) THEN REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
     ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `real_integral (real_interval [&0, pi])
        (\t. min (d / &2) (l / &2 * sin t)) =
      real_integral (real_interval [&0, pi])
        (\t. l / &2 * sin t)`
     SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
   MP_TAC(SPEC `l / &2` HAS_REAL_INTEGRAL_CMUL_SIN_0_PI) THEN
   DISCH_THEN(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
   ASM_REAL_ARITH_TAC);;

(* ===================================================================== *)
(* BUFFON_SHORT: re-derive the short needle formula from general         *)
(* ===================================================================== *)

let BUFFON_SHORT = prove
  (`!p:A prob_space X Theta l d.
      &0 < l /\ l <= d /\ &0 < d /\
      uniform_rv p X (&0) (d / &2) /\
      uniform_rv p Theta (&0) pi /\
      indep_rv p X Theta
      ==> prob p {x | x IN prob_carrier p /\ X x <= (l / &2) * sin(Theta x)} =
          (&2 * l) / (pi * d)`,
   REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `Theta:A->real`;
                   `l:real`; `d:real`] BUFFON_GENERAL) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   MP_TAC(SPECL [`l:real`; `d:real`] MIN_SIN_INTEGRAL_SHORT) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   SUBGOAL_THEN `~(d = &0) /\ ~(pi = &0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC; MP_TAC PI_POS THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
   CONV_TAC REAL_FIELD);;

(* ===================================================================== *)
(* Long needle integral evaluation: when d <= l,                         *)
(*   integral_0^pi min(d/2, l/2 * sin t) dt                             *)
(*     = l - sqrt(l^2 - d^2) + d * acs(d/l)                             *)
(* ===================================================================== *)

(* Helper: sin(pi - x) = sin(x) *)
let SIN_PI_SUB = prove
  (`!x. sin(pi - x) = sin(x)`,
   GEN_TAC THEN REWRITE_TAC[SIN_SUB; SIN_PI; COS_PI] THEN REAL_ARITH_TAC);;

(* Helper: cos(pi - x) = --(cos x) *)
let COS_PI_SUB = prove
  (`!x. cos(pi - x) = --(cos(x))`,
   GEN_TAC THEN REWRITE_TAC[COS_SUB; COS_PI; SIN_PI] THEN REAL_ARITH_TAC);;

(* Helper: integral of sin over [a,b] = cos(a) - cos(b) via FTC *)
let HAS_REAL_INTEGRAL_SIN = prove
  (`!a b. a <= b
     ==> (sin has_real_integral (cos(a) - cos(b))) (real_interval [a, b])`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `cos a - cos b = (--(cos b)) - (--(cos a))` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS THEN
   ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
   MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
   MP_TAC(SPEC `x:real` HAS_REAL_DERIVATIVE_COS) THEN
   DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_DERIVATIVE_NEG) THEN
   REWRITE_TAC[REAL_NEG_NEG]);;

(* Helper: integral of c*sin over [a,b] = c*(cos(a) - cos(b)) *)
let HAS_REAL_INTEGRAL_CMUL_SIN = prove
  (`!c a b. a <= b
     ==> ((\t. c * sin t) has_real_integral (c * (cos a - cos b)))
          (real_interval [a, b])`,
   REPEAT STRIP_TAC THEN
   MP_TAC(SPECL [`a:real`; `b:real`] HAS_REAL_INTEGRAL_SIN) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPEC `c:real` o MATCH_MP HAS_REAL_INTEGRAL_LMUL) THEN
   REWRITE_TAC[]);;

let MIN_SIN_INTEGRAL_LONG = prove
  (`!l d. &0 < l /\ &0 < d /\ d <= l
      ==> real_integral (real_interval [&0, pi])
            (\t. min (d / &2) (l / &2 * sin t)) =
          l - sqrt(l pow 2 - d pow 2) + d * acs(d / l)`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `&0 < pi` ASSUME_TAC THENL [REWRITE_TAC[PI_POS]; ALL_TAC] THEN
   SUBGOAL_THEN `~(l = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   (* Let alpha = asn(d/l) *)
   ABBREV_TAC `alpha = asn(d / l)` THEN
   (* Establish d/l in [-1,1] *)
   SUBGOAL_THEN `&0 < d / l /\ d / l <= &1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `-- &1 <= d / l /\ d / l <= &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   (* Key properties of alpha *)
   SUBGOAL_THEN `sin(alpha) = d / l` ASSUME_TAC THENL
   [EXPAND_TAC "alpha" THEN ASM_SIMP_TAC[SIN_ASN]; ALL_TAC] THEN
   SUBGOAL_THEN `cos(alpha) = sqrt(&1 - (d / l) pow 2)` ASSUME_TAC THENL
   [EXPAND_TAC "alpha" THEN ASM_SIMP_TAC[COS_ASN]; ALL_TAC] THEN
   SUBGOAL_THEN `--(pi / &2) <= alpha /\ alpha <= pi / &2`
     STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "alpha" THEN ASM_SIMP_TAC[ASN_BOUNDS]; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= alpha` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `sin alpha <= sin (&0)` MP_TAC THENL
    [MATCH_MP_TAC SIN_MONO_LE THEN
     UNDISCH_TAC `alpha < &0` THEN
     UNDISCH_TAC `--(pi / &2) <= alpha` THEN
     MP_TAC PI_POS THEN REAL_ARITH_TAC;
     ASM_REWRITE_TAC[SIN_0] THEN
     UNDISCH_TAC `&0 < d / l` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
   SUBGOAL_THEN `alpha <= pi` ASSUME_TAC THENL
   [UNDISCH_TAC `alpha <= pi / &2` THEN
    UNDISCH_TAC `&0 < pi` THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `pi - alpha <= pi` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 <= alpha` THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `alpha <= pi - alpha` ASSUME_TAC THENL
   [UNDISCH_TAC `alpha <= pi / &2` THEN
    UNDISCH_TAC `&0 < pi` THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= pi - alpha` ASSUME_TAC THENL
   [UNDISCH_TAC `alpha <= pi` THEN REAL_ARITH_TAC; ALL_TAC] THEN
   (* The function is continuous hence integrable *)
   SUBGOAL_THEN `(\t. min (d / &2) (l / &2 * sin t))
     real_integrable_on real_interval [&0, pi]` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_MIN THEN CONJ_TAC THENL
    [REWRITE_TAC[REAL_CONTINUOUS_ON_CONST]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_SIN];
    ALL_TAC] THEN
   (* Split at alpha *)
   MP_TAC(ISPECL [`\t. min (d / &2) (l / &2 * sin t)`;
                   `&0`; `pi`; `alpha:real`]
     REAL_INTEGRAL_COMBINE) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [UNDISCH_TAC `&0 <= alpha` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
    [UNDISCH_TAC `alpha <= pi` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
   (* Split at pi - alpha *)
   MP_TAC(ISPECL [`\t. min (d / &2) (l / &2 * sin t)`;
                   `alpha:real`; `pi`; `pi - alpha`]
     REAL_INTEGRAL_COMBINE) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [UNDISCH_TAC `alpha <= pi - alpha` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
    [UNDISCH_TAC `pi - alpha <= pi` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `pi`] THEN
    ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
    UNDISCH_TAC `&0 <= alpha` THEN UNDISCH_TAC `pi - alpha <= pi` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
   (* On [0, alpha]: min = l/2 * sin t *)
   SUBGOAL_THEN
     `real_integral (real_interval [&0, alpha])
        (\t. min (d / &2) (l / &2 * sin t)) =
      real_integral (real_interval [&0, alpha])
        (\t. l / &2 * sin t)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN
    X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    REWRITE_TAC[real_min] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `l / &2 * sin t <= d / &2` MP_TAC THENL
    [SUBGOAL_THEN `sin t <= sin alpha` MP_TAC THENL
     [MATCH_MP_TAC SIN_MONO_LE THEN
      UNDISCH_TAC `&0 <= t` THEN UNDISCH_TAC `t <= alpha` THEN
      UNDISCH_TAC `alpha <= pi / &2` THEN
      MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
     SUBGOAL_THEN `l / &2 * (d / l) = d / &2`
       (SUBST1_TAC o GSYM) THENL
     [UNDISCH_TAC `~(l = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
     MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [UNDISCH_TAC `&0 < l` THEN REAL_ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC];
     UNDISCH_TAC `d / &2 <= l / &2 * sin t` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
   (* On [alpha, pi - alpha]: min = d/2 *)
   SUBGOAL_THEN
     `real_integral (real_interval [alpha, pi - alpha])
        (\t. min (d / &2) (l / &2 * sin t)) =
      real_integral (real_interval [alpha, pi - alpha])
        (\t. d / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN
    X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    REWRITE_TAC[real_min] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `~(d / &2 <= l / &2 * sin t)` THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    SUBGOAL_THEN `sin alpha <= sin t` MP_TAC THENL
    [SUBGOAL_THEN `t <= pi - alpha ==> sin alpha <= sin t` MP_TAC THENL
     [DISCH_TAC THEN
      DISJ_CASES_TAC(SPECL [`t:real`; `pi / &2`] REAL_LE_TOTAL) THENL
      [MATCH_MP_TAC SIN_MONO_LE THEN
       UNDISCH_TAC `&0 <= alpha` THEN UNDISCH_TAC `alpha <= t` THEN
       UNDISCH_TAC `t <= pi / &2` THEN
       MP_TAC PI_POS THEN REAL_ARITH_TAC;
       SUBGOAL_THEN `sin alpha <= sin(pi - t)` MP_TAC THENL
       [MATCH_MP_TAC SIN_MONO_LE THEN
        UNDISCH_TAC `&0 <= alpha` THEN UNDISCH_TAC `t <= pi - alpha` THEN
        UNDISCH_TAC `pi / &2 <= t` THEN
        MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
       REWRITE_TAC[SIN_PI_SUB] THEN REAL_ARITH_TAC];
      ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `d / &2 = l / &2 * (d / l)` SUBST1_TAC THENL
    [UNDISCH_TAC `~(l = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [UNDISCH_TAC `&0 < l` THEN REAL_ARITH_TAC;
     FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
   (* On [pi - alpha, pi]: min = l/2 * sin t (by symmetry) *)
   SUBGOAL_THEN
     `real_integral (real_interval [pi - alpha, pi])
        (\t. min (d / &2) (l / &2 * sin t)) =
      real_integral (real_interval [pi - alpha, pi])
        (\t. l / &2 * sin t)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN
    X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    REWRITE_TAC[real_min] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `l / &2 * sin t <= d / &2` MP_TAC THENL
    [SUBGOAL_THEN `sin t <= sin alpha` MP_TAC THENL
     [SUBGOAL_THEN `sin(pi - t) <= sin alpha` MP_TAC THENL
      [MATCH_MP_TAC SIN_MONO_LE THEN
       UNDISCH_TAC `pi - alpha <= t` THEN UNDISCH_TAC `t <= pi` THEN
       UNDISCH_TAC `alpha <= pi / &2` THEN
       MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[SIN_PI_SUB];
      ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
     SUBGOAL_THEN `l / &2 * (d / l) = d / &2`
       (SUBST1_TAC o GSYM) THENL
     [UNDISCH_TAC `~(l = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
     MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [UNDISCH_TAC `&0 < l` THEN REAL_ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC];
     UNDISCH_TAC `d / &2 <= l / &2 * sin t` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
   (* Compute piece 1: integral_0^alpha (l/2 * sin t) = l/2 * (1 - cos alpha) *)
   SUBGOAL_THEN
     `real_integral (real_interval [&0, alpha])
        (\t. l / &2 * sin t) = l / &2 * (&1 - cos alpha)`
     ASSUME_TAC THENL
   [MP_TAC(SPECL [`l / &2`; `&0`; `alpha:real`] HAS_REAL_INTEGRAL_CMUL_SIN) THEN
    ANTS_TAC THENL [UNDISCH_TAC `&0 <= alpha` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[COS_0] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
   (* Compute piece 2: integral_alpha^{pi-alpha} (d/2) = d/2 * (pi - 2*alpha) *)
   SUBGOAL_THEN
     `real_integral (real_interval [alpha, pi - alpha])
        (\t. d / &2) = d / &2 * (pi - &2 * alpha)`
     ASSUME_TAC THENL
   [MP_TAC(SPECL [`alpha:real`; `pi - alpha`; `d / &2`]
      HAS_REAL_INTEGRAL_CONST) THEN
    ANTS_TAC THENL
    [UNDISCH_TAC `alpha <= pi - alpha` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
   (* Compute piece 3: integral_{pi-alpha}^pi (l/2*sin t) = l/2*(1-cos alpha) *)
   SUBGOAL_THEN
     `real_integral (real_interval [pi - alpha, pi])
        (\t. l / &2 * sin t) = l / &2 * (&1 - cos alpha)`
     ASSUME_TAC THENL
   [MP_TAC(SPECL [`l / &2`; `pi - alpha`; `pi`] HAS_REAL_INTEGRAL_CMUL_SIN) THEN
    ANTS_TAC THENL
    [UNDISCH_TAC `pi - alpha <= pi` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[COS_PI_SUB; COS_PI] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
   (* Assemble the three pieces *)
   ASM_REWRITE_TAC[] THEN
   (* Use ASN_PLUS_ACS: alpha + acs(d/l) = pi/2 so pi - 2*alpha = 2*acs(d/l) *)
   SUBGOAL_THEN `pi - &2 * alpha = &2 * acs(d / l)` ASSUME_TAC THENL
   [EXPAND_TAC "alpha" THEN
    MP_TAC(SPEC `d / l` ASN_PLUS_ACS) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   (* Use cos(alpha) = sqrt(1 - (d/l)^2) *)
   (* Simplify sqrt(1 - (d/l)^2) = sqrt(l^2 - d^2) / l *)
   SUBGOAL_THEN `sqrt(&1 - (d / l) pow 2) = sqrt(l pow 2 - d pow 2) / l`
     ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 - (d / l) pow 2 = (l pow 2 - d pow 2) / l pow 2`
      SUBST1_TAC THENL
    [UNDISCH_TAC `~(l = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_DIV; REAL_POW_LE; REAL_LT_IMP_LE] THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE];
    ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `~(l = &0)` THEN CONV_TAC REAL_FIELD);;

(* ===================================================================== *)
(* BUFFON_LONG: long needle formula from general                         *)
(* ===================================================================== *)

let BUFFON_LONG = prove
  (`!p:A prob_space X Theta l d.
      &0 < l /\ &0 < d /\ d <= l /\
      uniform_rv p X (&0) (d / &2) /\
      uniform_rv p Theta (&0) pi /\
      indep_rv p X Theta
      ==> prob p {x | x IN prob_carrier p /\ X x <= (l / &2) * sin(Theta x)} =
          (&2 / (pi * d)) *
          (l - sqrt(l pow 2 - d pow 2) + d * acs(d / l))`,
   REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `Theta:A->real`;
                   `l:real`; `d:real`] BUFFON_GENERAL) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   MP_TAC(SPECL [`l:real`; `d:real`] MIN_SIN_INTEGRAL_LONG) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC[]);;
