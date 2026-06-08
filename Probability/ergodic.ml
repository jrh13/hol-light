(* ========================================================================= *)
(* Ergodic theory: Birkhoff's Ergodic Theorem (Wiedijk #66).                 *)
(*                                                                           *)
(* Follows Williams "Probability with Martingales" Chapter 12.               *)
(* Uses the maximal ergodic lemma (Garsia's proof) approach.                 *)
(* ========================================================================= *)

needs "Probability/clt.ml";;

(* ------------------------------------------------------------------------- *)
(* Function iteration: ITER is already in the checkpoint.                    *)
(* We prove additional properties needed for ergodic theory.                 *)
(* ------------------------------------------------------------------------- *)

let ITER_ADD = prove
 (`!f:A->A m n x. ITER (m + n) f x = ITER m f (ITER n f x)`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; ITER]);;

let ITER_1 = prove
 (`!f:A->A x. ITER 1 f x = f x`,
  REWRITE_TAC[num_CONV `1`; ITER]);;

let REAL_LE_EPSILON = prove
 (`!x y:real. (!e. &0 < e ==> x <= y + e) ==> x <= y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(x - y) / &2`) THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Measure-preserving transformations                                        *)
(* Note: we use "tt" instead of "T" since T is the boolean true in HOL.      *)
(* ------------------------------------------------------------------------- *)

let measure_preserving = new_definition
  `measure_preserving (p:A prob_space) (tt:A->A) <=>
   (!x. x IN prob_carrier p ==> tt x IN prob_carrier p) /\
   (!A. A IN prob_events p ==>
        {x | x IN prob_carrier p /\ tt x IN A} IN prob_events p) /\
   (!A. A IN prob_events p ==>
        prob p {x | x IN prob_carrier p /\ tt x IN A} = prob p A)`;;

(* ------------------------------------------------------------------------- *)
(* Ergodicity: invariant events are trivial                                  *)
(* ------------------------------------------------------------------------- *)

let invariant_event = new_definition
  `invariant_event (p:A prob_space) (tt:A->A) (A:A->bool) <=>
   A IN prob_events p /\
   {x | x IN prob_carrier p /\ tt x IN A} = A`;;

let ergodic = new_definition
  `ergodic (p:A prob_space) (tt:A->A) <=>
   measure_preserving p tt /\
   (!A. invariant_event p tt A ==> prob p A = &0 \/ prob p A = &1)`;;

(* ------------------------------------------------------------------------- *)
(* Basic properties of measure-preserving maps                               *)
(* ------------------------------------------------------------------------- *)

let MEASURE_PRESERVING_CARRIER = prove
 (`!p:A prob_space tt. measure_preserving p tt
    ==> (!x. x IN prob_carrier p ==> tt x IN prob_carrier p)`,
  REWRITE_TAC[measure_preserving] THEN MESON_TAC[]);;

let MEASURE_PRESERVING_EVENTS = prove
 (`!p:A prob_space tt A. measure_preserving p tt /\ A IN prob_events p
    ==> {x | x IN prob_carrier p /\ tt x IN A} IN prob_events p`,
  REWRITE_TAC[measure_preserving] THEN MESON_TAC[]);;

let MEASURE_PRESERVING_PROB = prove
 (`!p:A prob_space tt A. measure_preserving p tt /\ A IN prob_events p
    ==> prob p {x | x IN prob_carrier p /\ tt x IN A} = prob p A`,
  REWRITE_TAC[measure_preserving] THEN MESON_TAC[]);;

(* ITER n tt is measure-preserving *)
let MEASURE_PRESERVING_ITER = prove
 (`!p:A prob_space tt n. measure_preserving p tt
    ==> measure_preserving p (ITER n tt)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [DISCH_TAC THEN REWRITE_TAC[ITER; measure_preserving] THEN
   SUBGOAL_THEN `!A:A->bool. A IN prob_events p ==>
     {x | x IN prob_carrier p /\ x IN A} = A` (fun th -> SIMP_TAC[th]) THEN
   REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
   X_GEN_TAC `x:A` THEN EQ_TAC THENL
   [MESON_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`p:A prob_space`; `A:A->bool`] PROB_EVENT_SUBSET) THEN
    ASM_REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[]];
   DISCH_TAC THEN
   SUBGOAL_THEN `measure_preserving (p:A prob_space) (ITER n tt)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[measure_preserving; ITER] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(ITER n (tt:A->A) x) IN prob_carrier p` ASSUME_TAC THENL
    [MP_TAC(SPECL [`p:A prob_space`; `ITER n (tt:A->A)`] MEASURE_PRESERVING_CARRIER) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
     MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`] MEASURE_PRESERVING_CARRIER) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `A:A->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ tt (ITER n tt x) IN A} =
      {x | x IN prob_carrier p /\ ITER n tt x IN
        {y | y IN prob_carrier p /\ tt y IN A}}` SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`p:A prob_space`; `ITER n (tt:A->A)`]
        MEASURE_PRESERVING_CARRIER) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
      ASM_REWRITE_TAC[];
      MESON_TAC[]];
     MP_TAC(SPECL [`p:A prob_space`; `ITER n (tt:A->A)`;
       `{y:A | y IN prob_carrier p /\ tt y IN (A:A->bool)}`]
       MEASURE_PRESERVING_EVENTS) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
     MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`; `A:A->bool`]
       MEASURE_PRESERVING_EVENTS) THEN
     ASM_REWRITE_TAC[]];
    X_GEN_TAC `A:A->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ tt (ITER n tt x) IN A} =
      {x | x IN prob_carrier p /\ ITER n tt x IN
        {y | y IN prob_carrier p /\ tt y IN A}}` SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`p:A prob_space`; `ITER n (tt:A->A)`]
        MEASURE_PRESERVING_CARRIER) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
      ASM_REWRITE_TAC[];
      MESON_TAC[]];
     SUBGOAL_THEN `{y:A | y IN prob_carrier p /\ tt y IN (A:A->bool)}
       IN prob_events p` ASSUME_TAC THENL
     [MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`; `A:A->bool`]
        MEASURE_PRESERVING_EVENTS) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
     MP_TAC(SPECL [`p:A prob_space`; `ITER n (tt:A->A)`;
       `{y:A | y IN prob_carrier p /\ tt y IN (A:A->bool)}`]
       MEASURE_PRESERVING_PROB) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
     MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`; `A:A->bool`]
       MEASURE_PRESERVING_PROB) THEN
     ASM_REWRITE_TAC[]]]]);;

(* Composition with tt preserves random variable property *)
let RANDOM_VARIABLE_COMP_MP = prove
 (`!p:A prob_space tt X. measure_preserving p tt /\ random_variable p X
    ==> random_variable p (\x. X(tt x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[random_variable] THEN
  X_GEN_TAC `a:real` THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ X((tt:A->A) x) <= a} =
     {x | x IN prob_carrier p /\
          tt x IN {y | y IN prob_carrier p /\ X y <= a}}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
   EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `measure_preserving (p:A prob_space) (tt:A->A)` THEN
    REWRITE_TAC[measure_preserving] THEN STRIP_TAC THEN
    ASM_MESON_TAC[];
    MESON_TAC[]];
   MATCH_MP_TAC MEASURE_PRESERVING_EVENTS THEN ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `random_variable (p:A prob_space) (X:A->real)` THEN
   REWRITE_TAC[random_variable] THEN
   DISCH_THEN(MP_TAC o SPEC `a:real`) THEN REWRITE_TAC[]]);;


(* Composition with ITER n tt preserves random variable property *)
let RANDOM_VARIABLE_ITER_COMP_MP = prove
 (`!p:A prob_space tt X n. measure_preserving p tt /\ random_variable p X
    ==> random_variable p (\x. X(ITER n tt x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:A prob_space`; `ITER n (tt:A->A)`; `X:A->real`]
    RANDOM_VARIABLE_COMP_MP) THEN
  ANTS_TAC THENL
  [ASM_SIMP_TAC[MEASURE_PRESERVING_ITER]; REWRITE_TAC[]]);;

(* {h < v} is an event for random variables *)
let RV_STRICT_INEQ_EVENT = prove
 (`!p:A prob_space h v. random_variable p h
    ==> {x | x IN prob_carrier p /\ h x < v} IN prob_events p`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`prob_events (p:A prob_space)`;
   `{t:A->bool | ?n:num. t = {y:A | y IN prob_carrier p /\
      (h:A->real) y <= v - inv(&n + &1)}}`]
   SIGMA_ALGEBRA_UNION_COUNTABLE) THEN
  ANTS_TAC THENL
  [REWRITE_TAC[PROB_SPACE_SIGMA_ALGEBRA] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `random_variable (p:A prob_space) (h:A->real)` THEN
    REWRITE_TAC[random_variable] THEN
    DISCH_THEN(MP_TAC o SPEC `v - inv(&n + &1)`) THEN REWRITE_TAC[];
    MATCH_MP_TAC COUNTABLE_SUBSET THEN
    EXISTS_TAC `IMAGE (\n:num. {y:A | y IN prob_carrier p /\
      (h:A->real) y <= v - inv(&n + &1)}) (:num)` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[NUM_COUNTABLE];
     REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE; IN_UNIV] THEN
     GEN_TAC THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
     EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]]];
   SUBGOAL_THEN
    `UNIONS {t:A->bool | ?n:num. t = {y | y IN prob_carrier p /\
       (h:A->real) y <= v - inv (&n + &1)}} =
     {x:A | x IN prob_carrier p /\ h x < v}` (fun th -> REWRITE_TAC[th]) THEN
   MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS] THEN X_GEN_TAC `y:A` THEN
    DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(t:A->bool) IN {t | ?n:num. t = {y:A | y IN prob_carrier p /\
      (h:A->real) y <= v - inv(&n + &1)}}` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
    UNDISCH_TAC `(y:A) IN (t:A->bool)` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `&m + &1` REAL_LT_INV) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `y:A` THEN STRIP_TAC THEN
    MP_TAC(SPEC `v - (h:A->real) y` REAL_ARCH_INV_SUC) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
    EXISTS_TAC `{y':A | y' IN prob_carrier p /\
      (h:A->real) y' <= v - inv(&m + &1)}` THEN
    CONJ_TAC THENL
    [EXISTS_TAC `m:num` THEN REFL_TAC;
     REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
     ASM_REAL_ARITH_TAC]]]);;

(* Level sets of random variables are events *)
let RV_LEVEL_SET_EVENT = prove
 (`!p:A prob_space h v. random_variable p h
    ==> {x | x IN prob_carrier p /\ h x = v} IN prob_events p`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ (h:A->real) x = v} =
    {x | x IN prob_carrier p /\ h x <= v} DIFF
    {x | x IN prob_carrier p /\ h x < v}` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN X_GEN_TAC `y:A` THEN
   ASM_CASES_TAC `(y:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
   REAL_ARITH_TAC;
   MATCH_MP_TAC PROB_DIFF_IN_EVENTS THEN CONJ_TAC THENL
   [UNDISCH_TAC `random_variable (p:A prob_space) (h:A->real)` THEN
    REWRITE_TAC[random_variable] THEN MESON_TAC[];
    MATCH_MP_TAC RV_STRICT_INEQ_EVENT THEN ASM_REWRITE_TAC[]]]);;

(* Simple expectation is preserved under composition with measure-preserving map *)
let SIMPLE_EXPECTATION_COMP_PRESERVED = prove
 (`!p:A prob_space tt h. measure_preserving p tt /\ simple_rv p h
    ==> simple_expectation p (\x. h(tt x)) = simple_expectation p h`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simple_expectation] THEN
  SUBGOAL_THEN
    `!v:real. prob p {x:A | x IN prob_carrier p /\ (h:A->real)((tt:A->A) x) = v} =
              prob p {x | x IN prob_carrier p /\ h x = v}` ASSUME_TAC THENL
  [X_GEN_TAC `v:real` THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ (h:A->real)((tt:A->A) x) = v} =
     {x | x IN prob_carrier p /\ tt x IN {y | y IN prob_carrier p /\ h y = v}}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN EQ_TAC THENL
    [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`] MEASURE_PRESERVING_CARRIER) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
     ASM_REWRITE_TAC[];
     MESON_TAC[]];
    MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`;
      `{y:A | y IN prob_carrier p /\ (h:A->real) y = v}`]
      MEASURE_PRESERVING_PROB) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
    [MATCH_MP_TAC RV_LEVEL_SET_EVENT THEN ASM_MESON_TAC[simple_rv];
     DISCH_THEN(fun th -> REWRITE_TAC[th])]];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[SET_RULE `{v:real | v IN s} = s`] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN CONJ_TAC THENL
  [REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `v:real` THEN
   DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `(tt:A->A) x` THEN ASM_REWRITE_TAC[] THEN
   MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`] MEASURE_PRESERVING_CARRIER) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[] THEN X_GEN_TAC `v:real` THEN STRIP_TAC THEN
   SUBGOAL_THEN `prob p {x:A | x IN prob_carrier p /\ (h:A->real) x = v} = &0`
     (fun th -> REWRITE_TAC[th; REAL_MUL_RZERO]) THEN
   SUBGOAL_THEN
     `prob p {x:A | x IN prob_carrier p /\ (h:A->real)((tt:A->A) x) = v} = &0`
     MP_TAC THENL
   [SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\ (h:A->real)((tt:A->A) x) = v} = {}`
      (fun th -> REWRITE_TAC[th; PROB_EMPTY]) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:A` THEN
    UNDISCH_TAC `~(v IN IMAGE (\x:A. (h:A->real)(tt x)) (prob_carrier p))` THEN
    REWRITE_TAC[IN_IMAGE; CONTRAPOS_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (fun th -> EXISTS_TAC `x:A` THEN
      REWRITE_TAC[th] THEN ASM_REWRITE_TAC[]));
    ASM_MESON_TAC[]]]);;

(* Composition with tt preserves simple_rv *)
let SIMPLE_RV_COMP_MP = prove
 (`!p:A prob_space tt h. measure_preserving p tt /\ simple_rv p h
    ==> simple_rv p (\x. h(tt x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simple_rv] THEN CONJ_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_COMP_MP THEN ASM_MESON_TAC[simple_rv];
   ALL_TAC] THEN
  SUBGOAL_THEN `{(\x:A. (h:A->real)(tt x)) x | x IN prob_carrier p} SUBSET
    {h x | x IN prob_carrier p}` MP_TAC THENL
  [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `v:real` THEN
   DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `(tt:A->A) x` THEN ASM_REWRITE_TAC[] THEN
   MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`] MEASURE_PRESERVING_CARRIER) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
   DISCH_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
   EXISTS_TAC `{(h:A->real) x | x IN prob_carrier p}` THEN
   ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[simple_rv]]);;

(* nn_expectation preserved under composition with tt (bounded case) *)
let NN_EXPECTATION_COMP_PRESERVED_BOUNDED = prove
 (`!p:A prob_space tt f B.
    measure_preserving p tt /\
    random_variable p f /\
    (!x. x IN prob_carrier p ==> &0 <= f x) /\
    (!x. x IN prob_carrier p ==> f x <= B)
    ==> nn_expectation p (\x. f(tt x)) = nn_expectation p f`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `fn = \n:num. nonneg_simple_fn_approx (p:A prob_space) (f:A->real) n` THEN
  SUBGOAL_THEN `!n:num. simple_rv p ((fn:num->A->real) n)` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "fn" THEN
   MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_SIMPLE_RV THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n:num. simple_rv p (\x:A. (fn:num->A->real) n (tt x))` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] SIMPLE_RV_COMP_MP) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `((\n. simple_expectation p ((fn:num->A->real) n)) ---> nn_expectation p f) sequentially` ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_MCT_NN_EXPECTATION THEN ASM_REWRITE_TAC[] THEN
   REPEAT CONJ_TAC THENL
   [GEN_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    EXPAND_TAC "fn" THEN REWRITE_TAC[NONNEG_SIMPLE_FN_APPROX_NONNEG];
    GEN_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXPAND_TAC "fn" THEN
    MP_TAC(SPECL [`p:A prob_space`; `f:A->real`; `n:num`; `SUC n`]
      NONNEG_SIMPLE_FN_APPROX_MONO) THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
    ASM_SIMP_TAC[LE_REFL; ARITH_RULE `n <= SUC n`];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXPAND_TAC "fn" THEN
    MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_CONVERGES THEN ASM_SIMP_TAC[];
    EXISTS_TAC `B:real` THEN ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `((\n. simple_expectation p (\x:A. (fn:num->A->real) n (tt x))) ---> nn_expectation p (\x. (f:A->real)(tt x))) sequentially` ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_MCT_NN_EXPECTATION THEN ASM_REWRITE_TAC[] THEN
   REPEAT CONJ_TAC THENL
   [GEN_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    EXPAND_TAC "fn" THEN REWRITE_TAC[NONNEG_SIMPLE_FN_APPROX_NONNEG];
    GEN_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXPAND_TAC "fn" THEN
    MP_TAC(SPECL [`p:A prob_space`; `f:A->real`; `n:num`; `SUC n`]
      NONNEG_SIMPLE_FN_APPROX_MONO) THEN
    DISCH_THEN(MP_TAC o SPEC `(tt:A->A) x`) THEN
    SUBGOAL_THEN `(tt:A->A) x IN prob_carrier p` ASSUME_TAC THENL
    [MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`] MEASURE_PRESERVING_CARRIER) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
     ASM_SIMP_TAC[ARITH_RULE `n <= SUC n`]];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXPAND_TAC "fn" THEN
    SUBGOAL_THEN `(tt:A->A) x IN prob_carrier p` ASSUME_TAC THENL
    [MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`] MEASURE_PRESERVING_CARRIER) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_CONVERGES THEN ASM_SIMP_TAC[]];
    EXISTS_TAC `B:real` THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[MEASURE_PRESERVING_CARRIER]];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n:num. simple_expectation p (\x:A. (fn:num->A->real) n (tt x)) = simple_expectation p (fn n)` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC SIMPLE_EXPECTATION_COMP_PRESERVED THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `((\n:num. simple_expectation p ((fn:num->A->real) n)) ---> nn_expectation p (\x:A. (f:A->real)(tt x))) sequentially` MP_TAC THENL
  [SUBGOAL_THEN `(\n:num. simple_expectation p ((fn:num->A->real) n)) = (\n. simple_expectation p (\x:A. fn n (tt x)))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN CONV_TAC SYM_CONV THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]];
   DISCH_TAC THEN
   MP_TAC(ISPECL [`sequentially`; `\n:num. simple_expectation (p:A prob_space) ((fn:num->A->real) n)`; `nn_expectation (p:A prob_space) (\x:A. (f:A->real)(tt x))`; `nn_expectation (p:A prob_space) (f:A->real)`] REALLIM_UNIQUE) THEN
   REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
   DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* nn_expectation preserved under composition with tt (general nonneg case) *)
let NN_EXPECTATION_COMP_PRESERVED = prove
 (`!p:A prob_space tt f.
    measure_preserving p tt /\
    random_variable p f /\
    (!x. x IN prob_carrier p ==> &0 <= f x) /\
    integrable p f
    ==> nn_expectation p (\x. f(tt x)) = nn_expectation p f`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Xn = \n:num. (\x:A. min ((f:A->real) x) (&n))` THEN
  SUBGOAL_THEN `!n:num. integrable p ((Xn:num->A->real) n)` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "Xn" THEN
   MATCH_MP_TAC INTEGRABLE_MIN THEN ASM_REWRITE_TAC[INTEGRABLE_CONST];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n:num x:A. x IN prob_carrier p ==> &0 <= (Xn:num->A->real) n x` ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "Xn" THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= y ==> &0 <= min x y`) THEN
   ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `!n:num x:A. x IN prob_carrier p ==> (Xn:num->A->real) n x <= Xn (SUC n) x` ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "Xn" THEN
   MATCH_MP_TAC(REAL_ARITH `a <= b ==> min x a <= min x b`) THEN
   REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN prob_carrier p ==> ((\n. (Xn:num->A->real) n x) ---> (f:A->real) x) sequentially` ASSUME_TAC THENL
  [X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXPAND_TAC "Xn" THEN
   REWRITE_TAC[tendsto_real; EVENTUALLY_SEQUENTIALLY] THEN
   X_GEN_TAC `e:real` THEN DISCH_TAC THEN
   MP_TAC(ISPEC `(f:A->real) x` REAL_ARCH_SIMPLE) THEN
   DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
   EXISTS_TAC `N:num` THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
   SUBGOAL_THEN `min ((f:A->real) x) (&m) = f x` SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= n ==> min x n = x`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `((\n:num. nn_expectation p ((Xn:num->A->real) n)) ---> nn_expectation p (f:A->real)) sequentially` ASSUME_TAC THENL
  [MP_TAC(SPECL [`p:A prob_space`; `Xn:num->A->real`; `f:A->real`] MCT_NN_EXPECTATION) THEN
   ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MP_TAC(SPECL [`p:A prob_space`; `f:A->real`] NN_EXPECTATION_INTEGRABLE_BOUND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `Bf:real`) THEN
    EXISTS_TAC `Bf:real` THEN GEN_TAC THEN
    MP_TAC(SPECL [`p:A prob_space`; `(Xn:num->A->real) n`; `f:A->real`] NN_EXPECTATION_MONO) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXPAND_TAC "Xn" THEN REAL_ARITH_TAC;
     DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `nn_expectation (p:A prob_space) (f:A->real)` THEN
     ASM_REWRITE_TAC[]];
    REWRITE_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n:num. nn_expectation p (\x:A. (Xn:num->A->real) n (tt x)) = nn_expectation p (Xn n)` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC NN_EXPECTATION_COMP_PRESERVED_BOUNDED THEN
   EXISTS_TAC `&n` THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL [ASM_MESON_TAC[integrable]; ALL_TAC] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXPAND_TAC "Xn" THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `!n:num. integrable p (\x:A. (Xn:num->A->real) n (tt x))` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
   EXISTS_TAC `&n` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(\x:A. (Xn:num->A->real) n (tt x)) = (\x. min ((f:A->real)(tt x)) (&n))` SUBST1_TAC THENL
    [EXPAND_TAC "Xn" THEN REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
    REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN
    MATCH_MP_TAC RANDOM_VARIABLE_COMP_MP THEN ASM_MESON_TAC[integrable];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXPAND_TAC "Xn" THEN
    SUBGOAL_THEN `(tt:A->A) x IN prob_carrier p` ASSUME_TAC THENL
    [MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`] MEASURE_PRESERVING_CARRIER) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
     MP_TAC(REAL_ARITH `&0 <= (f:A->real)((tt:A->A) x) ==> abs(min (f(tt x)) (&n)) <= &n`) THEN
     ASM_SIMP_TAC[]]];
   ALL_TAC] THEN
  SUBGOAL_THEN `((\n:num. nn_expectation p (\x:A. (Xn:num->A->real) n (tt x))) ---> nn_expectation p (\x. (f:A->real)(tt x))) sequentially` ASSUME_TAC THENL
  [MP_TAC(SPECL [`p:A prob_space`; `\n:num. (\x:A. (Xn:num->A->real) n (tt x))`; `\x:A. (f:A->real)(tt x)`] MCT_NN_EXPECTATION) THEN
   REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [GEN_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
     SUBGOAL_THEN `(tt:A->A) x IN prob_carrier p` MP_TAC THENL
     [MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`] MEASURE_PRESERVING_CARRIER) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
     GEN_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
     SUBGOAL_THEN `(tt:A->A) x IN prob_carrier p` MP_TAC THENL
     [MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`] MEASURE_PRESERVING_CARRIER) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN
     SUBGOAL_THEN `(tt:A->A) x IN prob_carrier p` MP_TAC THENL
     [MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`] MEASURE_PRESERVING_CARRIER) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN
      UNDISCH_TAC `!x:A. x IN prob_carrier p ==> ((\n. (Xn:num->A->real) n x) ---> (f:A->real) x) sequentially` THEN
      DISCH_THEN(MP_TAC o SPEC `(tt:A->A) x`) THEN ASM_REWRITE_TAC[]];
     MP_TAC(SPECL [`p:A prob_space`; `f:A->real`] NN_EXPECTATION_INTEGRABLE_BOUND) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `Bf:real`) THEN
     EXISTS_TAC `Bf:real` THEN GEN_TAC THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `nn_expectation (p:A prob_space) ((Xn:num->A->real) n)` THEN
     CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `nn_expectation (p:A prob_space) (f:A->real)` THEN
     ASM_REWRITE_TAC[] THEN
     MP_TAC(SPECL [`p:A prob_space`; `(Xn:num->A->real) n`; `f:A->real`] NN_EXPECTATION_MONO) THEN
     ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXPAND_TAC "Xn" THEN REAL_ARITH_TAC;
      REWRITE_TAC[]]];
    REWRITE_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `(\n:num. nn_expectation p (\x:A. (Xn:num->A->real) n (tt x))) = (\n. nn_expectation p (Xn n))` ASSUME_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MP_TAC(ISPECL [`sequentially`; `\n:num. nn_expectation (p:A prob_space) ((Xn:num->A->real) n)`; `nn_expectation (p:A prob_space) (\x:A. (f:A->real)(tt x))`; `nn_expectation (p:A prob_space) (f:A->real)`] REALLIM_UNIQUE) THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

(* Integrability preserved under composition with tt *)
let INTEGRABLE_COMP_MP = prove
 (`!p:A prob_space tt f.
    measure_preserving p tt /\ integrable p f
    ==> integrable p (\x. f(tt x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[integrable] THEN CONJ_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_COMP_MP THEN ASM_MESON_TAC[integrable];
   ALL_TAC] THEN
  UNDISCH_TAC `integrable (p:A prob_space) (f:A->real)` THEN
  GEN_REWRITE_TAC LAND_CONV [integrable] THEN STRIP_TAC THEN
  EXISTS_TAC `B:real` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?M. &0 <= M /\ !x:A. x IN prob_carrier p ==> (g:A->real) x <= M` (X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC) THENL
  [UNDISCH_TAC `simple_rv (p:A prob_space) (g:A->real)` THEN
   REWRITE_TAC[simple_rv] THEN STRIP_TAC THEN
   ASM_CASES_TAC `prob_carrier (p:A prob_space) = {}` THENL
   [EXISTS_TAC `&0` THEN REWRITE_TAC[REAL_LE_REFL] THEN
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY];
    ALL_TAC] THEN
   SUBGOAL_THEN `~({(g:A->real) x | x IN prob_carrier p} = {})` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; NOT_FORALL_THM] THEN
    UNDISCH_TAC `~(prob_carrier (p:A prob_space) = {})` THEN
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; NOT_FORALL_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `z:A`) THEN EXISTS_TAC `(g:A->real) z` THEN
    EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   EXISTS_TAC `sup {(g:A->real) x | x IN prob_carrier p}` THEN
   MP_TAC(ISPEC `{(g:A->real) x | x IN prob_carrier p}` SUP_FINITE) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `sup {(g:A->real) x | x IN prob_carrier p} IN {g x | x IN prob_carrier p}` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(g:A->real) x`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    ANTS_TAC THENL [EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]];
   ALL_TAC] THEN
  SUBGOAL_THEN `simple_expectation p (g:A->real) <= nn_expectation p (\x:A. min (abs((f:A->real)(tt x))) M)` ASSUME_TAC THENL
  [SUBGOAL_THEN `simple_rv (p:A prob_space) (g:A->real) /\
    (!x:A. x IN prob_carrier p ==> &0 <= g x) /\
    (!x. x IN prob_carrier p ==> g x <= min (abs((f:A->real)((tt:A->A) x))) M) /\
    (?B'. !x. x IN prob_carrier p ==> min (abs (f(tt x))) M <= B')` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
     REWRITE_TAC[REAL_LE_MIN] THEN ASM_SIMP_TAC[];
     EXISTS_TAC `M:real` THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
     REAL_ARITH_TAC];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `g:A->real`; `\x:A. min (abs((f:A->real)((tt:A->A) x))) M`] BOUNDED_NN_EXPECTATION_GE_SIMPLE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `nn_expectation p (\x:A. min (abs((f:A->real)(tt x))) M) = nn_expectation p (\x. min (abs(f x)) M)` ASSUME_TAC THENL
  [SUBGOAL_THEN `(\x:A. min (abs((f:A->real)((tt:A->A) x))) M) = (\x. (\y. min (abs(f y)) M)(tt x))` SUBST1_TAC THENL
   [REWRITE_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC NN_EXPECTATION_COMP_PRESERVED_BOUNDED THEN
   EXISTS_TAC `M:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN
    MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN ASM_REWRITE_TAC[];
    CONJ_TAC THENL
    [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
     MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= min a b`) THEN
     ASM_REWRITE_TAC[REAL_ABS_POS];
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN REAL_ARITH_TAC]];
   ALL_TAC] THEN
  SUBGOAL_THEN `nn_expectation p (\x:A. min (abs((f:A->real) x)) M) <= B` MP_TAC THENL
  [MP_TAC(SPECL [`p:A prob_space`; `\x:A. min (abs((f:A->real) x)) M`; `B:real`] NN_EXPECTATION_LE_FROM_SIMPLE) THEN
   REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= min a b`) THEN
    ASM_REWRITE_TAC[REAL_ABS_POS];
    X_GEN_TAC `h:A->real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `h:A->real`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `min (abs((f:A->real) x)) M` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; REAL_ARITH_TAC]];
   ASM_REAL_ARITH_TAC]);;

(* Expectation is preserved under composition with tt *)
let EXPECTATION_COMP_PRESERVED = prove
 (`!p:A prob_space tt f. measure_preserving p tt /\ integrable p f
    ==> integrable p (\x. f(tt x)) /\
        expectation p (\x. f(tt x)) = expectation p f`,
  REPEAT STRIP_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_COMP_MP THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[expectation] THEN
  SUBGOAL_THEN `nn_expectation p (\x:A. max ((f:A->real)(tt x)) (&0)) = nn_expectation p (\x. max (f x) (&0))` ASSUME_TAC THENL
  [SUBGOAL_THEN `(\x:A. max ((f:A->real)((tt:A->A) x)) (&0)) = (\x. (\y. max (f y) (&0))(tt x))` SUBST1_TAC THENL
   [REWRITE_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC NN_EXPECTATION_COMP_PRESERVED THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN
    ASM_MESON_TAC[integrable];
    CONJ_TAC THENL
    [X_GEN_TAC `x:A` THEN DISCH_TAC THEN REAL_ARITH_TAC;
     MATCH_MP_TAC INTEGRABLE_POS_PART THEN ASM_REWRITE_TAC[]]];
   ALL_TAC] THEN
  SUBGOAL_THEN `nn_expectation p (\x:A. max (--((f:A->real)(tt x))) (&0)) = nn_expectation p (\x. max (--f x) (&0))` ASSUME_TAC THENL
  [SUBGOAL_THEN `(\x:A. max (--((f:A->real)((tt:A->A) x))) (&0)) = (\x. (\y. max (--f y) (&0))(tt x))` SUBST1_TAC THENL
   [REWRITE_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC NN_EXPECTATION_COMP_PRESERVED THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN
    MATCH_MP_TAC RANDOM_VARIABLE_NEG THEN ASM_MESON_TAC[integrable];
    CONJ_TAC THENL
    [X_GEN_TAC `x:A` THEN DISCH_TAC THEN REAL_ARITH_TAC;
     MATCH_MP_TAC INTEGRABLE_NEG_PART THEN ASM_REWRITE_TAC[]]];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* Expectation is preserved under composition with ITER n tt *)
let EXPECTATION_ITER_COMP_PRESERVED = prove
 (`!p:A prob_space tt f n. measure_preserving p tt /\ integrable p f
    ==> integrable p (\x. f(ITER n tt x)) /\
        expectation p (\x. f(ITER n tt x)) = expectation p f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:A prob_space`; `ITER n (tt:A->A)`; `f:A->real`]
    EXPECTATION_COMP_PRESERVED) THEN
  ANTS_TAC THENL
  [ASM_SIMP_TAC[MEASURE_PRESERVING_ITER]; REWRITE_TAC[]]);;

(* Ergodic sum is integrable *)
let ERGODIC_SUM_INTEGRABLE = prove
 (`!p:A prob_space tt f n. measure_preserving p tt /\ integrable p f
    ==> integrable p (\x. sum(0..n) (\k. f(ITER k tt x)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_SUM THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `i:num`]
    EXPECTATION_ITER_COMP_PRESERVED) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* Expectation of ergodic sum *)
let ERGODIC_SUM_EXPECTATION = prove
 (`!p:A prob_space tt f n. measure_preserving p tt /\ integrable p f
    ==> expectation p (\x. sum(0..n) (\k. f(ITER k tt x))) =
        &(SUC n) * expectation p f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:A prob_space`; `\k:num. (\x:A. (f:A->real)(ITER k tt x))`;
    `n:num`] EXPECTATION_SUM) THEN
  ANTS_TAC THENL
  [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `i:num`]
     EXPECTATION_ITER_COMP_PRESERVED) THEN
   ASM_REWRITE_TAC[] THEN MESON_TAC[];
   REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   SUBGOAL_THEN `(\i:num. expectation p (\x:A. (f:A->real)(ITER i tt x))) =
     (\i. expectation p f)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
    MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `i:num`]
      EXPECTATION_ITER_COMP_PRESERVED) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0; ADD1] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC]]]);;

(* Ergodic average is integrable *)
let ERGODIC_AVG_INTEGRABLE = prove
 (`!p:A prob_space tt f n. measure_preserving p tt /\ integrable p f
    ==> integrable p (\x. inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
  MATCH_MP_TAC ERGODIC_SUM_INTEGRABLE THEN ASM_REWRITE_TAC[]);;

(* Expectation of ergodic average equals expectation of f *)
let ERGODIC_AVG_EXPECTATION = prove
 (`!p:A prob_space tt f n. measure_preserving p tt /\ integrable p f
    ==> expectation p (\x. inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x))) =
        expectation p f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `integrable p (\x:A. sum (0..n) (\k. (f:A->real) (ITER k tt x)))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC ERGODIC_SUM_INTEGRABLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`p:A prob_space`; `inv(&(SUC n))`;
    `\x:A. sum (0..n) (\k. (f:A->real) (ITER k tt x))`] EXPECTATION_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `n:num`]
    ERGODIC_SUM_EXPECTATION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  MP_TAC(SPEC `&(SUC n)` REAL_MUL_LINV) THEN
  REWRITE_TAC[REAL_OF_NUM_EQ; NOT_SUC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th; REAL_MUL_LID]));;

(* Invariant events form a sub-sigma-algebra *)
let INVARIANT_EVENTS_SUB_SIGMA_ALGEBRA = prove
 (`!p:A prob_space tt. measure_preserving p tt
    ==> sub_sigma_algebra p {A | invariant_event p tt A}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS {A:A->bool | invariant_event p tt A} = prob_carrier p` ASSUME_TAC THENL
  [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:A` THEN DISCH_THEN(X_CHOOSE_THEN `A:A->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `invariant_event (p:A prob_space) (tt:A->A) (A:A->bool)` THEN
    REWRITE_TAC[invariant_event] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`p:A prob_space`; `A:A->bool`] PROB_EVENT_SUBSET) THEN
    ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    EXISTS_TAC `prob_carrier (p:A prob_space)` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[invariant_event; PROB_CARRIER_IN_EVENTS] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `y:A` THEN EQ_TAC THENL
    [MESON_TAC[];
     DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
     MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`] MEASURE_PRESERVING_CARRIER) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
   ALL_TAC] THEN
  REWRITE_TAC[sub_sigma_algebra] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [ALL_TAC;
   REWRITE_TAC[SUBSET; IN_ELIM_THM; invariant_event] THEN MESON_TAC[]] THEN
  REWRITE_TAC[sigma_algebra; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
  [REWRITE_TAC[invariant_event; PROB_CARRIER_IN_EVENTS] THEN
   REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `y:A` THEN EQ_TAC THENL
   [MESON_TAC[];
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`] MEASURE_PRESERVING_CARRIER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
   X_GEN_TAC `a:A->bool` THEN REWRITE_TAC[invariant_event] THEN STRIP_TAC THEN
   CONJ_TAC THENL
   [REWRITE_TAC[prob_carrier] THEN MATCH_MP_TAC SIGMA_ALGEBRA_COMPL THEN
    REWRITE_TAC[PROB_SPACE_SIGMA_ALGEBRA; GSYM prob_carrier] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF] THEN X_GEN_TAC `x:A` THEN
    MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`] MEASURE_PRESERVING_CARRIER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `!y:A. y IN prob_carrier p /\ (tt:A->A) y IN a <=> y IN a`
      ASSUME_TAC THENL
    [GEN_TAC THEN
     UNDISCH_TAC `{x:A | x IN prob_carrier p /\ tt x IN a} = a` THEN
     REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[];
     EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]]];
   X_GEN_TAC `s:(A->bool)->bool` THEN STRIP_TAC THEN
   REWRITE_TAC[invariant_event] THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`prob_events (p:A prob_space)`; `s:(A->bool)->bool`] SIGMA_ALGEBRA_UNION_COUNTABLE) THEN
    ASM_REWRITE_TAC[PROB_SPACE_SIGMA_ALGEBRA] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `(s:(A->bool)->bool) SUBSET {A | invariant_event p tt A}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; invariant_event] THEN MESON_TAC[];
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIONS] THEN X_GEN_TAC `x:A` THEN
    EQ_TAC THENL
    [STRIP_TAC THEN
     SUBGOAL_THEN `invariant_event (p:A prob_space) (tt:A->A) (t:A->bool)` MP_TAC THENL
     [UNDISCH_TAC `(s:(A->bool)->bool) SUBSET {A | invariant_event p tt A}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[invariant_event] THEN STRIP_TAC THEN
      EXISTS_TAC `t:A->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `{x:A | x IN prob_carrier p /\ tt x IN t} = t` THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]];
     STRIP_TAC THEN
     SUBGOAL_THEN `invariant_event (p:A prob_space) (tt:A->A) (t:A->bool)` MP_TAC THENL
     [UNDISCH_TAC `(s:(A->bool)->bool) SUBSET {A | invariant_event p tt A}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[invariant_event] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(x:A) IN prob_carrier p` ASSUME_TAC THENL
      [MP_TAC(SPECL [`p:A prob_space`; `t:A->bool`] PROB_EVENT_SUBSET) THEN
       ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
       ASM_REWRITE_TAC[] THEN
       EXISTS_TAC `t:A->bool` THEN ASM_REWRITE_TAC[] THEN
       UNDISCH_TAC `{x:A | x IN prob_carrier p /\ (tt:A->A) x IN t} = t` THEN
       REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
       DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]]]]]]);;

(* ------------------------------------------------------------------------- *)
(* Maximal Ergodic Lemma (Garsia's proof)                                    *)
(*                                                                           *)
(* Key idea: Define M_n(x) = max(0, S_1(f)(x), ..., S_n(f)(x)).             *)
(* On A_n = {M_n > 0}: f(x) >= M_n(x) - M_n(T(x)).                         *)
(* Integrating: int_An f >= int_Omega M_n - int_Omega M_n(T) = 0.           *)
(* ------------------------------------------------------------------------- *)

(* The running max of partial sums: max(0, S_1, S_2, ..., S_{n+1}) *)
let ergodic_maxsum = define
  `(ergodic_maxsum (f:A->real) (tt:A->A) 0 x = max (f x) (&0)) /\
   (ergodic_maxsum f tt (SUC n) x =
      max (ergodic_maxsum f tt n x)
          (sum(0..SUC n) (\k. f(ITER k tt x))))`;;

(* M_n is non-negative *)
let ERGODIC_MAXSUM_POS = prove
 (`!f:A->real tt n x. &0 <= ergodic_maxsum f tt n x`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [REWRITE_TAC[ergodic_maxsum] THEN REAL_ARITH_TAC;
   GEN_TAC THEN REWRITE_TAC[ergodic_maxsum] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN REAL_ARITH_TAC]);;

(* Sum shift: relates sum at x to sum at (tt x) *)
let ERGODIC_SUM_SHIFT = prove
 (`!f:A->real tt n x.
    sum(0..SUC n) (\k. f(ITER k tt x)) =
    f(x) + sum(0..n) (\k. f(ITER k tt (tt x)))`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`\k. (f:A->real)(ITER k tt x)`; `0`; `SUC n`] SUM_CLAUSES_LEFT) THEN
  REWRITE_TAC[LE_0; ITER; ADD_CLAUSES] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `sum (1..SUC n) (\k. (f:A->real) (ITER k tt x)) =
    sum(0..n) (\k. f(ITER (k + 1) tt x))` SUBST1_TAC THENL
  [MP_TAC(SPECL [`1`; `\k. (f:A->real)(ITER k tt x)`; `0`; `n:num`] SUM_OFFSET) THEN
   REWRITE_TAC[ADD_CLAUSES; ADD1];
   MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
   REWRITE_TAC[] THEN AP_TERM_TAC THEN
   MP_TAC(SPECL [`tt:A->A`; `k:num`; `1`; `x:A`] ITER_ADD) THEN
   REWRITE_TAC[ITER_1] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
   REWRITE_TAC[ARITH_RULE `k + 1 = SUC k`; ITER]]);;

(* Monotonicity of ergodic_maxsum *)
let ERGODIC_MAXSUM_MONO = prove
 (`!f:A->real tt n x. ergodic_maxsum f tt n x <= ergodic_maxsum f tt (SUC n) x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ergodic_maxsum] THEN REAL_ARITH_TAC);;

(* ergodic_maxsum >= each partial sum *)
let ERGODIC_MAXSUM_GE_SUM = prove
 (`!f:A->real tt n x.
    sum(0..n) (\k. f(ITER k tt x)) <= ergodic_maxsum f tt n x`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [REWRITE_TAC[ergodic_maxsum; SUM_SING_NUMSEG; ITER] THEN REAL_ARITH_TAC;
   GEN_TAC THEN REWRITE_TAC[ergodic_maxsum] THEN REAL_ARITH_TAC]);;

(* Key pointwise inequality: f(x) >= M_n(x) - M_n(T(x)) when M_n(x) > 0 *)
let ERGODIC_MAXSUM_KEY_INEQ = prove
 (`!f:A->real tt n x.
    ergodic_maxsum f tt n x > &0
    ==> f x >= ergodic_maxsum f tt n x - ergodic_maxsum f tt n (tt x)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [REWRITE_TAC[ergodic_maxsum; ITER] THEN REAL_ARITH_TAC;
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   SUBGOAL_THEN `ergodic_maxsum (f:A->real) tt (SUC n) x =
     max (ergodic_maxsum f tt n x)
         (sum(0..SUC n) (\k. f(ITER k tt x)))` ASSUME_TAC THENL
   [REWRITE_TAC[ergodic_maxsum]; ALL_TAC] THEN
   SUBGOAL_THEN `ergodic_maxsum (f:A->real) tt (SUC n) (tt x) =
     max (ergodic_maxsum f tt n (tt x))
         (sum(0..SUC n) (\k. f(ITER k tt (tt x))))` ASSUME_TAC THENL
   [REWRITE_TAC[ergodic_maxsum]; ALL_TAC] THEN
   SUBGOAL_THEN `sum(0..SUC n) (\k. (f:A->real)(ITER k tt x)) =
     f x + sum(0..n) (\k. f(ITER k tt (tt x)))` ASSUME_TAC THENL
   [REWRITE_TAC[ERGODIC_SUM_SHIFT]; ALL_TAC] THEN
   SUBGOAL_THEN `sum(0..n) (\k. (f:A->real)(ITER k tt (tt x))) <=
     ergodic_maxsum f tt n (tt x)` ASSUME_TAC THENL
   [REWRITE_TAC[ERGODIC_MAXSUM_GE_SUM]; ALL_TAC] THEN
   SUBGOAL_THEN `ergodic_maxsum (f:A->real) tt n (tt x) <=
     ergodic_maxsum f tt (SUC n) (tt x)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_CASES_TAC `ergodic_maxsum (f:A->real) tt n x >=
     sum(0..SUC n) (\k. f(ITER k tt x))` THENL
   [SUBGOAL_THEN `ergodic_maxsum (f:A->real) tt (SUC n) x =
      ergodic_maxsum f tt n x` ASSUME_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `ergodic_maxsum (f:A->real) tt n x > &0` ASSUME_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `ergodic_maxsum (f:A->real) tt (SUC n) x =
      sum(0..SUC n) (\k. f(ITER k tt x))` ASSUME_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC]]);;

(* ergodic_maxsum is a random variable *)
let ERGODIC_MAXSUM_RV = prove
 (`!p:A prob_space tt f n.
    measure_preserving p tt /\ integrable p f
    ==> random_variable p (ergodic_maxsum f tt n)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [STRIP_TAC THEN
   SUBGOAL_THEN `ergodic_maxsum (f:A->real) tt 0 = (\x. max (f x) (&0))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; ergodic_maxsum]; ALL_TAC] THEN
   MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN
   REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN
   ASM_MESON_TAC[integrable];
   STRIP_TAC THEN
   SUBGOAL_THEN `random_variable (p:A prob_space) (ergodic_maxsum (f:A->real) tt n)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `ergodic_maxsum (f:A->real) tt (SUC n) =
     (\x. max (ergodic_maxsum f tt n x) (sum(0..SUC n) (\k. f(ITER k tt x))))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; ergodic_maxsum]; ALL_TAC] THEN
   MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN CONJ_TAC THENL
   [REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`p:A prob_space`; `\i:num. (\x:A. (f:A->real)(ITER i tt x))`; `SUC n`] RANDOM_VARIABLE_SUM) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC RANDOM_VARIABLE_ITER_COMP_MP THEN
    ASM_MESON_TAC[integrable]]]);;

(* ergodic_maxsum is integrable *)
let ERGODIC_MAXSUM_INTEGRABLE = prove
 (`!p:A prob_space tt f n.
    measure_preserving p tt /\ integrable p f
    ==> integrable p (ergodic_maxsum f tt n)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [STRIP_TAC THEN
   SUBGOAL_THEN `ergodic_maxsum (f:A->real) tt 0 = (\x. max (f x) (&0))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; ergodic_maxsum]; ALL_TAC] THEN
   MATCH_MP_TAC INTEGRABLE_MAX THEN ASM_REWRITE_TAC[INTEGRABLE_CONST];
   STRIP_TAC THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (ergodic_maxsum (f:A->real) tt n)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `ergodic_maxsum (f:A->real) tt (SUC n) =
     (\x. max (ergodic_maxsum f tt n x) (sum(0..SUC n) (\k. f(ITER k tt x))))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; ergodic_maxsum]; ALL_TAC] THEN
   MATCH_MP_TAC INTEGRABLE_MAX THEN CONJ_TAC THENL
   [REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ERGODIC_SUM_INTEGRABLE THEN ASM_REWRITE_TAC[]]]);;

(* The set {M_n > 0} is a measurable event *)
let ERGODIC_MAXSUM_POS_EVENT = prove
 (`!p:A prob_space tt f n.
    measure_preserving p tt /\ integrable p f
    ==> {x | x IN prob_carrier p /\ ergodic_maxsum f tt n x > &0} IN prob_events p`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `random_variable (p:A prob_space) (ergodic_maxsum (f:A->real) tt n)` ASSUME_TAC THENL
  [MATCH_MP_TAC ERGODIC_MAXSUM_RV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ ergodic_maxsum (f:A->real) tt n x > &0} =
    prob_carrier p DIFF {x | x IN prob_carrier p /\ ergodic_maxsum f tt n x <= &0}` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
   ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   REWRITE_TAC[prob_carrier] THEN MATCH_MP_TAC SIGMA_ALGEBRA_COMPL THEN
   REWRITE_TAC[PROB_SPACE_SIGMA_ALGEBRA] THEN
   UNDISCH_TAC `random_variable (p:A prob_space) (ergodic_maxsum (f:A->real) tt n)` THEN
   REWRITE_TAC[random_variable] THEN DISCH_THEN(MP_TAC o SPEC `&0`) THEN
   REWRITE_TAC[GSYM prob_carrier]]);;

(* The maximal ergodic lemma *)
let MAXIMAL_ERGODIC_LEMMA = prove
 (`!p:A prob_space tt f n.
    measure_preserving p tt /\ integrable p f
    ==> &0 <= expectation p
               (\x. f x * indicator_fn
                 {x | x IN prob_carrier p /\
                      ergodic_maxsum f tt n x > &0} x)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `A = {x:A | x IN prob_carrier p /\ ergodic_maxsum (f:A->real) tt n x > &0}` THEN
  SUBGOAL_THEN `A IN prob_events (p:A prob_space)` ASSUME_TAC THENL
  [EXPAND_TAC "A" THEN MATCH_MP_TAC ERGODIC_MAXSUM_POS_EVENT THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (ergodic_maxsum (f:A->real) tt n)` ASSUME_TAC THENL
  [MATCH_MP_TAC ERGODIC_MAXSUM_INTEGRABLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x. ergodic_maxsum (f:A->real) tt n (tt x))` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_COMP_MP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x. (f:A->real) x * indicator_fn A x)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN prob_carrier p ==>
    ergodic_maxsum (f:A->real) tt n x - ergodic_maxsum f tt n (tt x) <=
    f x * indicator_fn A x` ASSUME_TAC THENL
  [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   ASM_CASES_TAC `ergodic_maxsum (f:A->real) tt n x > &0` THENL
   [SUBGOAL_THEN `(x:A) IN A` ASSUME_TAC THENL
    [EXPAND_TAC "A" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN `indicator_fn (A:A->bool) x = &1` SUBST1_TAC THENL
    [REWRITE_TAC[indicator_fn] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_RID] THEN
    MP_TAC(SPECL [`f:A->real`; `tt:A->A`; `n:num`; `x:A`] ERGODIC_MAXSUM_KEY_INEQ) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `ergodic_maxsum (f:A->real) tt n x = &0` ASSUME_TAC THENL
    [MP_TAC(SPECL [`f:A->real`; `tt:A->A`; `n:num`; `x:A`] ERGODIC_MAXSUM_POS) THEN
     ASM_REAL_ARITH_TAC;
     ALL_TAC] THEN
    SUBGOAL_THEN `~((x:A) IN A)` ASSUME_TAC THENL
    [EXPAND_TAC "A" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
     ALL_TAC] THEN
    SUBGOAL_THEN `indicator_fn (A:A->bool) x = &0` SUBST1_TAC THENL
    [REWRITE_TAC[indicator_fn] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_RZERO] THEN
    ASM_REWRITE_TAC[REAL_SUB_LZERO] THEN
    MP_TAC(SPECL [`f:A->real`; `tt:A->A`; `n:num`; `(tt:A->A) x`] ERGODIC_MAXSUM_POS) THEN
    REAL_ARITH_TAC];
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `expectation (p:A prob_space) (\x. ergodic_maxsum (f:A->real) tt n x - ergodic_maxsum f tt n (tt x))` THEN
  CONJ_TAC THENL
  [SUBGOAL_THEN `expectation (p:A prob_space) (\x. ergodic_maxsum (f:A->real) tt n x - ergodic_maxsum f tt n (tt x)) =
    expectation p (ergodic_maxsum f tt n) - expectation p (\x. ergodic_maxsum f tt n (tt x))` SUBST1_TAC THENL
   [MP_TAC(SPECL [`p:A prob_space`; `ergodic_maxsum (f:A->real) tt n`; `\x:A. ergodic_maxsum (f:A->real) tt n (tt x)`] EXPECTATION_SUB) THEN
    ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
   SUBGOAL_THEN `expectation (p:A prob_space) (\x. ergodic_maxsum (f:A->real) tt n (tt x)) =
     expectation p (ergodic_maxsum f tt n)` SUBST1_TAC THENL
   [MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`; `ergodic_maxsum (f:A->real) tt n`] EXPECTATION_COMP_PRESERVED) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    REAL_ARITH_TAC];
   MATCH_MP_TAC EXPECTATION_MONO THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX]]);;

(* Infinite-horizon maximal ergodic inequality:                              *)
(* E[f * 1_{exists n. M_n > 0}] >= 0                                        *)
(* Uses DOMINATED_CONVERGENCE to pass from finite to infinite horizon        *)
let MAXIMAL_ERGODIC_INFINITE = prove
 (`!p:A prob_space tt f.
    measure_preserving p tt /\ integrable p f
    ==> &0 <= expectation p
               (\x. f x * indicator_fn
                 {x | x IN prob_carrier p /\
                      ?n. ergodic_maxsum f tt n x > &0} x)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Ainf = {x:A | x IN prob_carrier p /\ ?n. ergodic_maxsum (f:A->real) tt n x > &0}` THEN
  SUBGOAL_THEN `(Ainf:A->bool) IN prob_events p` ASSUME_TAC THENL
  [SUBGOAL_THEN `Ainf = UNIONS {({x:A | x IN prob_carrier p /\ ergodic_maxsum (f:A->real) tt n x > &0}) | n IN (:num)}`
    SUBST1_TAC THENL
   [EXPAND_TAC "Ainf" THEN SET_TAC[];
    MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN
    GEN_TAC THEN MATCH_MP_TAC ERGODIC_MAXSUM_POS_EVENT THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`;
                `(\n:num. (\x:A. (f:A->real) x * indicator_fn {x | x IN prob_carrier p /\ ergodic_maxsum f tt n x > &0} x))`;
                `(\x:A. (f:A->real) x * indicator_fn (Ainf:A->bool) x)`;
                `(\x:A. abs((f:A->real) x))`] DOMINATED_CONVERGENCE) THEN
  ANTS_TAC THENL
  [BETA_TAC THEN CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ERGODIC_MAXSUM_POS_EVENT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ABS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
   ASM_CASES_TAC `(x:A) IN Ainf` THENL
   [SUBGOAL_THEN `?n0. ergodic_maxsum (f:A->real) tt n0 x > &0` STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `(x:A) IN Ainf` THEN EXPAND_TAC "Ainf" THEN
     REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
     ALL_TAC] THEN
    EXISTS_TAC `n0:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `ergodic_maxsum (f:A->real) tt n x > &0` ASSUME_TAC THENL
    [SUBGOAL_THEN `ergodic_maxsum (f:A->real) tt n0 x <= ergodic_maxsum f tt n x` MP_TAC THENL
     [MP_TAC(ISPECL [`\m n:num. ergodic_maxsum (f:A->real) tt m x <= ergodic_maxsum f tt n x`] TRANSITIVE_STEPWISE_LE) THEN
      BETA_TAC THEN
      ANTS_TAC THENL
      [REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
        GEN_TAC THEN REWRITE_TAC[ERGODIC_MAXSUM_MONO]];
       DISCH_THEN(MP_TAC o SPECL [`n0:num`; `n:num`]) THEN ASM_REWRITE_TAC[]];
      UNDISCH_TAC `ergodic_maxsum (f:A->real) tt n0 x > &0` THEN REAL_ARITH_TAC];
     SUBGOAL_THEN `indicator_fn {x:A | x IN prob_carrier p /\ ergodic_maxsum (f:A->real) tt n x > &0} x = &1` SUBST1_TAC THENL
     [REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
      COND_CASES_TAC THENL [REFL_TAC; ASM_MESON_TAC[]];
      ALL_TAC] THEN
     SUBGOAL_THEN `indicator_fn (Ainf:A->bool) (x:A) = &1` SUBST1_TAC THENL
     [REWRITE_TAC[indicator_fn] THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC]];
    EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((x:A) IN {x | x IN prob_carrier p /\ ergodic_maxsum (f:A->real) tt n x > &0})` ASSUME_TAC THENL
    [REWRITE_TAC[IN_ELIM_THM] THEN
     UNDISCH_TAC `~((x:A) IN Ainf)` THEN EXPAND_TAC "Ainf" THEN
     REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
     SUBGOAL_THEN `indicator_fn {x:A | x IN prob_carrier p /\ ergodic_maxsum (f:A->real) tt n x > &0} x = &0` SUBST1_TAC THENL
     [REWRITE_TAC[indicator_fn] THEN
      COND_CASES_TAC THENL [ASM_MESON_TAC[]; REFL_TAC];
      ALL_TAC] THEN
     SUBGOAL_THEN `indicator_fn (Ainf:A->bool) (x:A) = &0` SUBST1_TAC THENL
     [REWRITE_TAC[indicator_fn] THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC]]];
   ALL_TAC] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LBOUND) THEN
  EXISTS_TAC `\n:num. expectation (p:A prob_space) (\x:A. (f:A->real) x *
    indicator_fn {x | x IN prob_carrier p /\ ergodic_maxsum f tt n x > &0} x)` THEN
  CONJ_TAC THENL
  [UNDISCH_TAC `((\n.
            expectation (p:A prob_space)
            ((\n x.
                  (f:A->real) x *
                  indicator_fn
                  {x | x IN prob_carrier p /\ ergodic_maxsum f tt n x > &0}
                  x)
            n)) --->
       expectation p (\x. f x * indicator_fn (Ainf:A->bool) x))
      sequentially` THEN
   BETA_TAC THEN REWRITE_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC MAXIMAL_ERGODIC_LEMMA THEN ASM_REWRITE_TAC[]);;

(* Iterates stay in an invariant set *)
let ITER_IN_INVARIANT = prove
 (`!p:A prob_space tt (A:A->bool) x k.
    measure_preserving p tt /\ invariant_event p tt A /\ x IN A
    ==> ITER k tt x IN A`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SPEC_TAC(`k:num`, `k:num`) THEN INDUCT_TAC THENL
  [REWRITE_TAC[ITER] THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[ITER] THEN
   UNDISCH_TAC `invariant_event (p:A prob_space) (tt:A->A) (A:A->bool)` THEN
   REWRITE_TAC[invariant_event] THEN STRIP_TAC THEN
   UNDISCH_TAC `{x:A | x IN prob_carrier p /\ tt x IN A} = A` THEN
   REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
   DISCH_THEN(MP_TAC o SPEC `ITER k (tt:A->A) x`) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_MESON_TAC[]]);;

(* MEL restricted to an invariant set:
   If A is T-invariant and on A the partial sums of f are eventually positive,
   then E[f * 1_A] >= 0 *)
let MEL_INVARIANT_SET = prove
 (`!p:A prob_space tt f (A:A->bool).
    measure_preserving p tt /\ integrable p f /\
    A IN prob_events p /\ invariant_event p tt A /\
    (!x. x IN A ==> ?n. sum(0..n) (\k. f(ITER k tt x)) > &0)
    ==> &0 <= expectation p (\x. f x * indicator_fn A x)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `g = \x:A. (f:A->real) x * indicator_fn (A:A->bool) x` THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (g:A->real)` ASSUME_TAC THENL
  [EXPAND_TAC "g" THEN MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!y:A. (g:A->real) y *
    indicator_fn {x:A | x IN prob_carrier p /\ (?n. ergodic_maxsum g tt n x > &0)} y = g y` ASSUME_TAC THENL
  [X_GEN_TAC `y:A` THEN
   REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
   COND_CASES_TAC THENL [REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
   REWRITE_TAC[REAL_MUL_RZERO] THEN EXPAND_TAC "g" THEN BETA_TAC THEN
   SUBGOAL_THEN `~((y:A) IN A)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~((y:A) IN prob_carrier p /\ (?n. ergodic_maxsum (g:A->real) tt n y > &0))` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
    [MP_TAC(SPECL [`p:A prob_space`; `A:A->bool`] PROB_EVENT_SUBSET) THEN
     ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
     UNDISCH_TAC `!x:A. x IN A ==> (?n. sum (0..n) (\k. (f:A->real) (ITER k tt x)) > &0)` THEN
     DISCH_THEN(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[] THEN
     DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `n:num` THEN
     SUBGOAL_THEN `sum(0..n) (\k. (g:A->real)(ITER k tt y)) = sum(0..n) (\k. (f:A->real)(ITER k tt y))` ASSUME_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      EXPAND_TAC "g" THEN BETA_TAC THEN
      SUBGOAL_THEN `indicator_fn (A:A->bool) (ITER k (tt:A->A) y) = &1` SUBST1_TAC THENL
      [REWRITE_TAC[indicator_fn] THEN
       SUBGOAL_THEN `ITER k (tt:A->A) y IN A` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `A:A->bool`; `y:A`; `k:num`] ITER_IN_INVARIANT) THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
       REWRITE_TAC[REAL_MUL_RID]];
      MP_TAC(ISPECL [`g:A->real`; `tt:A->A`; `n:num`; `y:A`] ERGODIC_MAXSUM_GE_SUM) THEN
      ASM_REAL_ARITH_TAC]];
    REWRITE_TAC[indicator_fn] THEN ASM_REWRITE_TAC[REAL_MUL_RZERO]];
   ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `g:A->real`] MAXIMAL_ERGODIC_INFINITE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\x:A. (g:A->real) x *
    indicator_fn {x | x IN prob_carrier p /\ (?n. ergodic_maxsum g tt n x > &0)} x) = g`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[ETA_AX]]);;

(* Helper: real_limsup > b implies existence of a term > b (bounded case) *)
let REAL_LIMSUP_GT_EXISTS_BOUNDED = prove
 (`!s:num->real b c B. (!n. c <= s n) /\ (!n. s n <= B) /\
    real_limsup s > b ==> ?n. s n > b`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[TAUT `(p /\ q /\ r ==> s) <=> (p /\ q ==> r ==> s)`] THEN
  STRIP_TAC THEN
  ONCE_REWRITE_TAC[TAUT `p ==> q <=> ~q ==> ~p`] THEN
  REWRITE_TAC[NOT_EXISTS_THM; real_gt; REAL_NOT_LT] THEN
  DISCH_TAC THEN REWRITE_TAC[real_limsup] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sup {(s:num->real) k | k >= 0}` THEN CONJ_TAC THENL
  [MATCH_MP_TAC INF_LE_ELEMENT THEN CONJ_TAC THENL
   [EXISTS_TAC `c:real` THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`{(s:num->real) k | k >= n}`; `c:real`; `B:real`; `(s:num->real) n`]
      REAL_LE_SUP) THEN
    ANTS_TAC THENL
    [REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [EXISTS_TAC `n:num` THEN REWRITE_TAC[GE; LE_REFL];
      CONJ_TAC THENL [ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]];
     ASM_REAL_ARITH_TAC];
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN EXISTS_TAC `0` THEN REFL_TAC];
   MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `(s:num->real) 0` THEN EXISTS_TAC `0` THEN REWRITE_TAC[GE; LE_REFL];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* Helper: real_liminf < a implies existence of a term < a (bounded case) *)
let REAL_LIMINF_LT_EXISTS_BOUNDED = prove
 (`!s:num->real a c B. (!n. c <= s n) /\ (!n. s n <= B) /\
    real_liminf s < a ==> ?n. s n < a`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[TAUT `(p /\ q /\ r ==> s) <=> (p /\ q ==> r ==> s)`] THEN
  STRIP_TAC THEN
  ONCE_REWRITE_TAC[TAUT `p ==> q <=> ~q ==> ~p`] THEN
  REWRITE_TAC[NOT_EXISTS_THM; REAL_NOT_LT] THEN
  DISCH_TAC THEN REWRITE_TAC[real_liminf] THEN
  MP_TAC(ISPECL [`{inf {(s:num->real) k | k >= n} | n IN (:num)}`; `a:real`; `B:real`;
                  `inf {(s:num->real) k | k >= 0}`] REAL_LE_SUP) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN EXISTS_TAC `0` THEN REFL_TAC;
    CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `(s:num->real) 0` THEN EXISTS_TAC `0` THEN REWRITE_TAC[GE; LE_REFL];
      REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]];
     REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(s:num->real) n` THEN CONJ_TAC THENL
     [MATCH_MP_TAC INF_LE_ELEMENT THEN CONJ_TAC THENL
      [EXISTS_TAC `c:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
       REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
       REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `n:num` THEN REWRITE_TAC[GE; LE_REFL]];
      ASM_REWRITE_TAC[]]]];
   SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Birkhoff's Ergodic Theorem: almost sure convergence of ergodic averages   *)
(* ------------------------------------------------------------------------- *)

(* Helper: average > b implies sum of (f-b) > 0 *)
let AVG_GT_IMP_SUM_POS = prove
 (`!f:A->real tt (x:A) b n.
    inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x)) > b
    ==> sum(0..n) (\k. f(ITER k tt x) - b) > &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_gt] THEN DISCH_TAC THEN
  REWRITE_TAC[SUM_SUB_NUMSEG; SUM_CONST_NUMSEG; SUB_0; ADD1] THEN
  REWRITE_TAC[GSYM ADD1] THEN
  ABBREV_TAC `S = sum(0..n) (\k. (f:A->real)(ITER k tt x))` THEN
  SUBGOAL_THEN `&0 < &(SUC n)` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(&(SUC n) = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&(SUC n) * b < S` MP_TAC THENL
  [MP_TAC(SPECL [`b:real`; `inv(&(SUC n)) * S`; `&(SUC n)`] REAL_LT_LMUL_EQ) THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[REAL_MUL_ASSOC] THEN
   ASM_SIMP_TAC[REAL_MUL_RINV] THEN
   REWRITE_TAC[REAL_MUL_LID] THEN SIMP_TAC[];
   ASM_REAL_ARITH_TAC]);;

(* Helper: average < a implies sum of (a-f) > 0 *)
let AVG_LT_IMP_SUM_POS = prove
 (`!f:A->real tt (x:A) a n.
    inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x)) < a
    ==> sum(0..n) (\k. a - f(ITER k tt x)) > &0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[real_gt] THEN
  REWRITE_TAC[SUM_SUB_NUMSEG; SUM_CONST_NUMSEG; SUB_0; ADD1] THEN
  REWRITE_TAC[GSYM ADD1] THEN
  ABBREV_TAC `S = sum(0..n) (\k. (f:A->real)(ITER k tt x))` THEN
  SUBGOAL_THEN `&0 < &(SUC n)` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(&(SUC n) = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `S < &(SUC n) * a` MP_TAC THENL
  [MP_TAC(SPECL [`inv(&(SUC n)) * S`; `a:real`; `&(SUC n)`] REAL_LT_LMUL_EQ) THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[REAL_MUL_ASSOC] THEN
   ASM_SIMP_TAC[REAL_MUL_RINV] THEN
   REWRITE_TAC[REAL_MUL_LID] THEN SIMP_TAC[];
   ASM_REAL_ARITH_TAC]);;

(* Helper: ergodic averages are bounded by C when f is bounded by C *)
let ERGODIC_AVG_BOUNDED = prove
 (`!p:A prob_space tt f C n x.
    measure_preserving p tt /\
    (!x. x IN prob_carrier p ==> abs(f x) <= C) /\
    x IN prob_carrier p
    ==> abs(inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x))) <= C`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NUM] THEN
  SUBGOAL_THEN `!k:num. ITER k (tt:A->A) x IN prob_carrier p` ASSUME_TAC THENL
  [GEN_TAC THEN
   SUBGOAL_THEN `measure_preserving (p:A prob_space) (ITER k tt)` MP_TAC THENL
   [MATCH_MP_TAC MEASURE_PRESERVING_ITER THEN ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o MATCH_MP MEASURE_PRESERVING_CARRIER) THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `~(&(SUC n) = &0)` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_OF_NUM_EQ; NOT_SUC]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(&(SUC n)) * (&(SUC n) * C)` THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `sum(0..n) (\k. abs((f:A->real)(ITER k tt x)))` THEN CONJ_TAC THENL
   [REWRITE_TAC[SUM_ABS_NUMSEG];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..n) (\k:num. C:real)` THEN CONJ_TAC THENL
    [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN REWRITE_TAC[] THEN
     DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0; ADD1] THEN REAL_ARITH_TAC]];
   ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_MUL_LID; REAL_LE_REFL]]);;

(* Telescoping identity: avg_n(tt x) - avg_n(x) = inv(n+1) * (f(T^{n+1}x) - f(x)) *)
let AVG_SHIFT_DIFF = prove
 (`!f:A->real tt (x:A) n.
   inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt (tt x))) -
   inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x)) =
   inv(&(SUC n)) * (f(ITER (SUC n) tt x) - f(x))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `!k. (f:A->real)(ITER k tt (tt x)) = f(ITER (SUC k) tt x)`
    (fun th -> REWRITE_TAC[th]) THENL
  [GEN_TAC THEN AP_TERM_TAC THEN
   MP_TAC(SPECL [`tt:A->A`; `k:num`; `1`; `x:A`] ITER_ADD) THEN
   REWRITE_TAC[ITER_1; ADD_SYM; GSYM ADD1] THEN SIMP_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN
  SPEC_TAC(`n:num`, `n:num`) THEN INDUCT_TAC THENL
  [REWRITE_TAC[SUM_SING_NUMSEG; ITER; GSYM ADD1] THEN REAL_ARITH_TAC;
   REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[ITER] THEN REAL_ARITH_TAC]);;

(* Measurability of the oscillation set *)
let ERGODIC_OSCILLATION_MEASURABLE = prove
 (`!p:A prob_space tt f a b C.
    measure_preserving p tt /\ integrable p f /\ a < b /\
    (!x. x IN prob_carrier p ==> abs(f x) <= C)
    ==> {x | x IN prob_carrier p /\
                    real_liminf (\n. inv(&(SUC n)) *
                      sum(0..n) (\k. f(ITER k tt x))) < a /\
                    real_limsup (\n. inv(&(SUC n)) *
                      sum(0..n) (\k. f(ITER k tt x))) > b} IN prob_events p`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `random_variable (p:A prob_space)
    (\x. real_limsup (\n. inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x))))`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`;
    `\n (x:A). inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x))`;
    `\x:A. C:real`] RANDOM_VARIABLE_REAL_LIMSUP_DOMINATED) THEN
   BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
    MATCH_MP_TAC ERGODIC_AVG_INTEGRABLE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[RANDOM_VARIABLE_CONST];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`;
                   `n:num`; `x:A`] ERGODIC_AVG_BOUNDED) THEN
    ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
    real_limsup (\n. inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x))) > b} IN
    prob_events p` ASSUME_TAC THENL
  [REWRITE_TAC[real_gt] THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
     b < real_limsup (\n. inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x)))} =
     prob_carrier p DIFF {x | x IN prob_carrier p /\
       real_limsup (\n. inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x))) <= b}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN GEN_TAC THEN
    ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[prob_carrier] THEN
   MATCH_MP_TAC SIGMA_ALGEBRA_COMPL THEN REWRITE_TAC[PROB_SPACE_SIGMA_ALGEBRA] THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `\x:A. real_limsup (\n. inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x)))`;
     `b:real`] RV_LE_EVENT) THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[GSYM prob_carrier];
   ALL_TAC] THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
    real_liminf (\n. inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x))) < a} IN
    prob_events p` ASSUME_TAC THENL
  [SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
     real_liminf (\n. inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x))) < a} =
     {x | x IN prob_carrier p /\
       real_liminf (\n. inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x)) + C) < a + C}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
    ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `real_liminf (\n. inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x))) =
      real_liminf (\n. inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x)) + C) - C`
      (fun th -> REWRITE_TAC[th] THEN REAL_ARITH_TAC) THEN
    MP_TAC(ISPECL [`\n. inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x)) + C`;
                   `&0`; `&2 * C`; `C:real`] REAL_LIMINF_SUB_CONST) THEN BETA_TAC THEN
    SUBGOAL_THEN `(\n. (inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x)) + C) - C) =
      (\n. inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x)))`
      (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THEN GEN_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`;
                   `n:num`; `x:A`] ERGODIC_AVG_BOUNDED) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `\x:A. real_liminf (\n. inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x)) + C)`;
     `a + C:real`] RV_STRICT_INEQ_EVENT) THEN
   ANTS_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`;
     `\n (x:A). inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x)) + C`;
     `&2 * C`] RANDOM_VARIABLE_REAL_LIMINF) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
    [GEN_TAC THEN
     SUBGOAL_THEN `(\x:A. inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x)) + C) =
       (\x. (\x. inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x))) x + (\x. C) x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN BETA_TAC THEN REFL_TAC;
      MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN CONJ_TAC THENL
      [MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
       MATCH_MP_TAC ERGODIC_AVG_INTEGRABLE THEN ASM_REWRITE_TAC[];
       REWRITE_TAC[RANDOM_VARIABLE_CONST]]];
     REPEAT STRIP_TAC THEN
     MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`;
                    `n:num`; `x:A`] ERGODIC_AVG_BOUNDED) THEN
     ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
     REPEAT STRIP_TAC THEN
     MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`;
                    `n:num`; `x:A`] ERGODIC_AVG_BOUNDED) THEN
     ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
    real_liminf (\n. inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x))) < a /\
    real_limsup (\n. inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x))) > b} =
    {x | x IN prob_carrier p /\
      real_liminf (\n. inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x))) < a} INTER
    {x | x IN prob_carrier p /\
      real_limsup (\n. inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x))) > b}` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SIGMA_ALGEBRA_INTER THEN ASM_REWRITE_TAC[PROB_SPACE_SIGMA_ALGEBRA]);;

(* Helper: Archimedean bound for c*inv(SUC N) *)
let ARCHIMEDEAN_INV_BOUND = prove
 (`!c eps. &0 <= c /\ &0 < eps ==> ?N. c * inv(&(SUC N)) < eps`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `c = &0` THENL
  [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `eps:real` REAL_ARCH) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `c:real`) THEN
  DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
  SUBGOAL_THEN `0 < m` ASSUME_TAC THENL
  [ASM_CASES_TAC `m = 0` THENL
   [UNDISCH_TAC `c < &m * eps` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
    ASM_REAL_ARITH_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
  EXISTS_TAC `m - 1` THEN
  SUBGOAL_THEN `SUC(m - 1) = m` SUBST1_TAC THENL
  [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `&m` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
   SUBGOAL_THEN `&m * c * inv(&m) = c` SUBST1_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_OF_NUM_EQ;
      ARITH_RULE `0 < m ==> ~(m = 0)`] THEN
    REWRITE_TAC[REAL_MUL_RID];
    ASM_REWRITE_TAC[]]]);;

(* Helper: inf perturbation bound *)
let INF_PERTURB_BOUND = prove
 (`!s t lb ub c N.
  (!n. lb <= s n) /\ (!n. s n <= ub) /\
  (!n. lb <= t n) /\ (!n. t n <= ub) /\
  (!n. abs(s n - t n) <= c * inv(&(SUC n))) /\ &0 <= c
  ==> inf {t k | k >= N} - c * inv(&(SUC N)) <= inf {s k | k >= N}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
  [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
   MESON_TAC[GE; LE_REFL];
   REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `y:real` THEN
   DISCH_THEN(X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
   SUBGOAL_THEN `inf {(t:num->real) k | k >= N} <= t k` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`{(t:num->real) k | k >= N}`; `(t:num->real) k`] INF_LE_ELEMENT) THEN
    ANTS_TAC THENL
    [CONJ_TAC THENL
     [EXISTS_TAC `lb:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]];
     REWRITE_TAC[]];
    ALL_TAC] THEN
   MP_TAC(SPEC `k:num` (ASSUME `!n. abs((s:num->real) n - t n) <= c * inv(&(SUC n))`)) THEN
   SUBGOAL_THEN `c * inv(&(SUC k)) <= c * inv(&(SUC N))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE; LT_0; LE_SUC] THEN
    ASM_MESON_TAC[GE];
    ABBREV_TAC `inft:real = inf {(t:num->real) k | k >= N}` THEN
    ASM_REAL_ARITH_TAC]]);;

(* Helper: inf over larger range is monotone *)
let INF_SUBSET_LE = prove
 (`!s lb ub M N. (!n. lb <= s n) /\ (!n. s n <= ub) /\ M <= N
  ==> inf {s k | k >= M} <= inf {(s:num->real) k | k >= N}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `inf {(s:num->real) k | k >= M}`
    (INST [`{(s:num->real) k | k >= N}`, `s:real->bool`] REAL_LE_INF)) THEN
  MATCH_MP_TAC(TAUT `a ==> (a ==> b) ==> b`) THEN CONJ_TAC THENL
  [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
   MESON_TAC[GE; LE_REFL];
   REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   MP_TAC(ISPECL [`{(s:num->real) k | k >= M}`; `(s:num->real) k`] INF_LE_ELEMENT) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [EXISTS_TAC `lb:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
     REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
     REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `k:num` THEN
     ASM_REWRITE_TAC[GE] THEN ASM_ARITH_TAC];
    REWRITE_TAC[]]]);;

(* Helper: sup perturbation bound *)
let SUP_PERTURB_BOUND = prove
 (`!s t lb ub c N.
  (!n. lb <= s n) /\ (!n. s n <= ub) /\
  (!n. lb <= t n) /\ (!n. t n <= ub) /\
  (!n. abs(s n - t n) <= c * inv(&(SUC n))) /\ &0 <= c
  ==> sup {s k | k >= N} <= sup {t k | k >= N} + c * inv(&(SUC N))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `S' = sup {(t:num->real) k | k >= N}` THEN
  MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
  [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
   MESON_TAC[GE; LE_REFL]; ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `y:real` THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  SUBGOAL_THEN `(s:num->real) k <= t k + c * inv(&(SUC N))` ASSUME_TAC THENL
  [MP_TAC(SPEC `k:num` (ASSUME `!n. abs((s:num->real) n - t n) <= c * inv(&(SUC n))`)) THEN
   MATCH_MP_TAC(REAL_ARITH `b <= d ==> abs(a - c) <= b ==> a <= c + d`) THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LE_INV2 THEN
   REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE; LT_0; LE_SUC] THEN
   ASM_MESON_TAC[GE]; ALL_TAC] THEN
  SUBGOAL_THEN `(t:num->real) k <= S'` ASSUME_TAC THENL
  [EXPAND_TAC "S'" THEN
   MP_TAC(ISPECL [`{(t:num->real) k | k >= N}`; `(t:num->real) k`] ELEMENT_LE_SUP) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [EXISTS_TAC `ub:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
     REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
     REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[]]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Helper: sup over subset is monotone decreasing *)
let SUP_SUBSET_GE = prove
 (`!s lb ub M N. (!n. lb <= s n) /\ (!n. s n <= ub) /\ M <= N
  ==> sup {s k | k >= N} <= sup {(s:num->real) k | k >= M}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_SUP_LE_SUBSET THEN CONJ_TAC THENL
  [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
   MESON_TAC[GE; LE_REFL]; ALL_TAC] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[GE] THEN ASM_ARITH_TAC;
   EXISTS_TAC `ub:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
   REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]]);;

(* Helper: real_limsup s <= sup{s k|k>=N} *)
let REAL_LIMSUP_LE_SUP' = prove
 (`!s lb ub N. (!n. lb <= s n) /\ (!n. s n <= ub)
  ==> real_limsup s <= sup {(s:num->real) k | k >= N}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_limsup] THEN
  MATCH_MP_TAC INF_LE_ELEMENT THEN CONJ_TAC THENL
  [EXISTS_TAC `lb:real` THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
   X_GEN_TAC `y:real` THEN DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
   MP_TAC(ISPECL [`{(s:num->real) k | k >= m}`; `lb:real`; `ub:real`]
     REAL_SUP_BOUNDS) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
     MESON_TAC[GE; LE_REFL];
     REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
     ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    SIMP_TAC[]];
   REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN EXISTS_TAC `N:num` THEN REFL_TAC]);;

(* Bounded sequences differing by O(1/n) have equal liminf *)
let REAL_LIMINF_LE_PERTURB = prove
 (`!s t lb ub c.
  (!n. lb <= s n) /\ (!n. s n <= ub) /\
  (!n. lb <= t n) /\ (!n. t n <= ub) /\
  (!n. abs(s n - t n) <= c * inv(&(SUC n))) /\ &0 <= c
  ==> real_liminf t <= real_liminf s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_EPSILON THEN
  X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `eps:real`] ARCHIMEDEAN_INV_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN
  REWRITE_TAC[real_liminf] THEN
  MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
  [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; IN_UNIV] THEN
   EXISTS_TAC `inf {(t:num->real) k | k >= 0}` THEN
   EXISTS_TAC `0` THEN REFL_TAC; ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
  X_GEN_TAC `x:real` THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` SUBST1_TAC) THEN
  MP_TAC(INST [
    `inf {(t:num->real) k | k >= N + N0}`, `q:real`;
    `inf {(s:num->real) k | k >= N + N0}`, `r:real`;
    `c * inv(&(SUC(N + N0)))`, `u:real`;
    `c * inv(&(SUC N0))`, `v:real`;
    `inf {(t:num->real) k | k >= N}`, `p:real`;
    `sup {inf {(s:num->real) k | k >= n} | n | T}`, `w:real`;
    `eps:real`, `z:real`]
    (REAL_ARITH `p <= q /\ q - u <= r /\ r <= w /\ u <= v /\ v < z
      ==> p <= w + z`)) THEN
  ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC INF_SUBSET_LE THEN
   EXISTS_TAC `lb:real` THEN EXISTS_TAC `ub:real` THEN
   ASM_REWRITE_TAC[LE_ADD];
   MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] INF_PERTURB_BOUND) THEN
   EXISTS_TAC `lb:real` THEN EXISTS_TAC `ub:real` THEN ASM_REWRITE_TAC[];
   SUBGOAL_THEN `inf {(s:num->real) k | k >= N + N0} IN
     {inf {s k | k >= n} | n | T}` ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `N + N0:num` THEN REFL_TAC;
    ALL_TAC] THEN
   MP_TAC(ISPECL [`{inf {(s:num->real) k | k >= n} | n | T}`;
     `inf {(s:num->real) k | k >= N + N0}`] ELEMENT_LE_SUP) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [EXISTS_TAC `ub:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
     X_GEN_TAC `y:real` THEN DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
     MP_TAC(ISPECL [`{(s:num->real) k | k >= m}`; `(s:num->real) m`]
       INF_LE_ELEMENT) THEN
     ANTS_TAC THENL
     [CONJ_TAC THENL
      [EXISTS_TAC `lb:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
       REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
       REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `m:num` THEN
       REWRITE_TAC[GE; LE_REFL]];
      ASM_MESON_TAC[REAL_LE_TRANS]];
     ASM_REWRITE_TAC[]];
    REWRITE_TAC[]];
   MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LE_INV2 THEN
   REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE; LT_0] THEN
   REWRITE_TAC[LE_SUC; LE_ADDR];
   ASM_REWRITE_TAC[]]);;

(* Bounded sequences differing by O(1/n) have equal liminf *)
let REAL_LIMINF_PERTURB_NULL = prove
 (`!s t lb ub c.
  (!n. lb <= s n) /\ (!n. s n <= ub) /\
  (!n. lb <= t n) /\ (!n. t n <= ub) /\
  (!n. abs(s n - t n) <= c * inv(&(SUC n))) /\ &0 <= c
  ==> real_liminf s = real_liminf t`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b /\ b <= a ==> a = b`) THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LIMINF_LE_PERTURB THEN
   MAP_EVERY EXISTS_TAC [`lb:real`; `ub:real`; `c:real`] THEN
   ASM_REWRITE_TAC[] THEN
   GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `abs(a - b) <= c ==> abs(b - a) <= c`) THEN
   ASM_REWRITE_TAC[];
   MATCH_MP_TAC REAL_LIMINF_LE_PERTURB THEN
   MAP_EVERY EXISTS_TAC [`lb:real`; `ub:real`; `c:real`] THEN
   ASM_REWRITE_TAC[]]);;

(* Bounded sequences differing by O(1/n) have equal limsup *)
let REAL_LIMSUP_LE_PERTURB = prove
 (`!s t lb ub c.
  (!n. lb <= s n) /\ (!n. s n <= ub) /\
  (!n. lb <= t n) /\ (!n. t n <= ub) /\
  (!n. abs(s n - t n) <= c * inv(&(SUC n))) /\ &0 <= c
  ==> real_limsup s <= real_limsup t`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_EPSILON THEN X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `eps / &2`] ARCHIMEDEAN_INV_BOUND) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN
  SUBGOAL_THEN `!m. lb <= sup {(t:num->real) k | k >= m}` ASSUME_TAC THENL
  [GEN_TAC THEN
   MP_TAC(ISPECL [`{(t:num->real) k | k >= m}`; `lb:real`; `ub:real`]
     REAL_SUP_BOUNDS) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
     MESON_TAC[GE; LE_REFL];
     REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
     ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    SIMP_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `?N1:num. sup {(t:num->real) k | k >= N1} < real_limsup t + eps / &2`
    (X_CHOOSE_TAC `N1:num`) THENL
  [REWRITE_TAC[real_limsup] THEN
   MP_TAC(ISPECL [`{sup {(t:num->real) k | k >= n} | n IN (:num)}`;
     `inf {sup {(t:num->real) k | k >= n} | n IN (:num)} + eps / &2`]
     INF_APPROACH) THEN
   ANTS_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; IN_UNIV] THEN
    REPEAT CONJ_TAC THENL
    [MESON_TAC[];
     EXISTS_TAC `lb:real` THEN X_GEN_TAC `y:real` THEN
     DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[REAL_LT_ADDR] THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `m:num`) ASSUME_TAC) THEN
    EXISTS_TAC `m:num` THEN ASM_MESON_TAC[]]; ALL_TAC] THEN
  ABBREV_TAC `N = N0 + N1:num` THEN
  MP_TAC(ISPECL [`s:num->real`; `lb:real`; `ub:real`; `N:num`] REAL_LIMSUP_LE_SUP') THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:num->real`; `t:num->real`; `lb:real`; `ub:real`; `c:real`; `N:num`]
    SUP_PERTURB_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t:num->real`; `lb:real`; `ub:real`; `N1:num`; `N:num`]
    SUP_SUBSET_GE) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [EXPAND_TAC "N" THEN ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  SUBGOAL_THEN `c * inv(&(SUC N)) <= c * inv(&(SUC N0))` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LE_INV2 THEN
   REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE; LT_0; LE_SUC] THEN
   EXPAND_TAC "N" THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `ls = real_limsup (s:num->real)` THEN
  ABBREV_TAC `lt = real_limsup (t:num->real)` THEN
  ABBREV_TAC `ss = sup {(s:num->real) k | k >= N}` THEN
  ABBREV_TAC `st = sup {(t:num->real) k | k >= N}` THEN
  ABBREV_TAC `st1 = sup {(t:num->real) k | k >= N1}` THEN
  ABBREV_TAC `d = c * inv(&(SUC N))` THEN
  ABBREV_TAC `d0 = c * inv(&(SUC N0))` THEN
  ASM_REAL_ARITH_TAC);;

(* Bounded sequences differing by O(1/n) have equal limsup *)
let REAL_LIMSUP_PERTURB_NULL = prove
 (`!s t lb ub c.
  (!n. lb <= s n) /\ (!n. s n <= ub) /\
  (!n. lb <= t n) /\ (!n. t n <= ub) /\
  (!n. abs(s n - t n) <= c * inv(&(SUC n))) /\ &0 <= c
  ==> real_limsup s = real_limsup t`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b /\ b <= a ==> a = b`) THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LIMSUP_LE_PERTURB THEN
   MAP_EVERY EXISTS_TAC [`lb:real`; `ub:real`; `c:real`] THEN
   ASM_REWRITE_TAC[];
   MATCH_MP_TAC REAL_LIMSUP_LE_PERTURB THEN
   MAP_EVERY EXISTS_TAC [`lb:real`; `ub:real`; `c:real`] THEN
   ASM_REWRITE_TAC[] THEN
   GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `abs(a - b) <= c ==> abs(b - a) <= c`) THEN
   ASM_REWRITE_TAC[]]);;

(* Helper: establish ergodic avg difference bound uniformly *)
let ERGODIC_AVG_DIFF_BOUND = prove
 (`!p:A prob_space tt f C x n. measure_preserving p tt /\
  (!x. x IN prob_carrier p ==> abs(f x) <= C) /\ &0 <= C /\
  x IN prob_carrier p
  ==> abs(inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt (tt x))) -
          inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x))) <=
      (&2 * C) * inv(&(SUC n))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->real`; `tt:A->A`; `x:A`; `n:num`] AVG_SHIFT_DIFF) THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NUM] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(&(SUC n)) * (&2 * C)` THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
   MATCH_MP_TAC(REAL_ARITH `abs a <= C /\ abs b <= C ==> abs(a - b) <= &2 * C`) THEN
   CONJ_TAC THENL
   [SUBGOAL_THEN `ITER (SUC n) (tt:A->A) x IN prob_carrier p` ASSUME_TAC THENL
    [MP_TAC(SPEC `SUC n` (MATCH_MP MEASURE_PRESERVING_ITER
       (ASSUME `measure_preserving (p:A prob_space) tt`))) THEN
     DISCH_THEN(MP_TAC o MATCH_MP MEASURE_PRESERVING_CARRIER) THEN
     ASM SET_TAC[];
     ASM_SIMP_TAC[]];
    ASM_SIMP_TAC[]];
   REWRITE_TAC[REAL_MUL_AC] THEN REAL_ARITH_TAC]);;

(* Ergodic averages shifted by T have same limsup *)
let ERGODIC_LIMSUP_SHIFT = prove
 (`!p:A prob_space tt f C. measure_preserving p tt /\
  (!x. x IN prob_carrier p ==> abs(f x) <= C) /\ &0 <= C
  ==> !x. x IN prob_carrier p ==>
    real_limsup (\n. inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt (tt x)))) =
    real_limsup (\n. inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
  [MP_TAC(ISPECL [`\n:num. inv(&(SUC n)) * sum(0..n)
     (\k. (f:A->real)(ITER k (tt:A->A) (tt (x:A))))`;
    `\n:num. inv(&(SUC n)) * sum(0..n)
     (\k. (f:A->real)(ITER k (tt:A->A) (x:A)))`;
    `--C:real`; `C:real`; `&2 * C`] REAL_LIMSUP_LE_PERTURB) THEN
   BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
   REPEAT CONJ_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`;
      `n:num`; `tt (x:A):A`] ERGODIC_AVG_BOUNDED) THEN
    ASM_SIMP_TAC[MEASURE_PRESERVING_CARRIER] THEN REAL_ARITH_TAC;
    GEN_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`;
      `n:num`; `tt (x:A):A`] ERGODIC_AVG_BOUNDED) THEN
    ASM_SIMP_TAC[MEASURE_PRESERVING_CARRIER] THEN REAL_ARITH_TAC;
    GEN_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`;
      `n:num`; `x:A`] ERGODIC_AVG_BOUNDED) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    GEN_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`;
      `n:num`; `x:A`] ERGODIC_AVG_BOUNDED) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    GEN_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`;
      `x:A`; `n:num`] ERGODIC_AVG_DIFF_BOUND) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC];
   MP_TAC(ISPECL [`\n:num. inv(&(SUC n)) * sum(0..n)
     (\k. (f:A->real)(ITER k (tt:A->A) (x:A)))`;
    `\n:num. inv(&(SUC n)) * sum(0..n)
     (\k. (f:A->real)(ITER k (tt:A->A) (tt (x:A))))`;
    `--C:real`; `C:real`; `&2 * C`] REAL_LIMSUP_LE_PERTURB) THEN
   BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
   REPEAT CONJ_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`;
      `n:num`; `x:A`] ERGODIC_AVG_BOUNDED) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    GEN_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`;
      `n:num`; `x:A`] ERGODIC_AVG_BOUNDED) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    GEN_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`;
      `n:num`; `tt (x:A):A`] ERGODIC_AVG_BOUNDED) THEN
    ASM_SIMP_TAC[MEASURE_PRESERVING_CARRIER] THEN REAL_ARITH_TAC;
    GEN_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`;
      `n:num`; `tt (x:A):A`] ERGODIC_AVG_BOUNDED) THEN
    ASM_SIMP_TAC[MEASURE_PRESERVING_CARRIER] THEN REAL_ARITH_TAC;
    GEN_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`;
      `x:A`; `n:num`] ERGODIC_AVG_DIFF_BOUND) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]]);;

(* Ergodic averages shifted by T have same liminf *)
let ERGODIC_LIMINF_SHIFT = prove
 (`!p:A prob_space tt f C. measure_preserving p tt /\
  (!x. x IN prob_carrier p ==> abs(f x) <= C) /\ &0 <= C
  ==> !x. x IN prob_carrier p ==>
    real_liminf (\n. inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt (tt x)))) =
    real_liminf (\n. inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
  [MP_TAC(ISPECL [`\n:num. inv(&(SUC n)) * sum(0..n)
     (\k. (f:A->real)(ITER k (tt:A->A) (x:A)))`;
    `\n:num. inv(&(SUC n)) * sum(0..n)
     (\k. (f:A->real)(ITER k (tt:A->A) (tt (x:A))))`;
    `--C:real`; `C:real`; `&2 * C`] REAL_LIMINF_LE_PERTURB) THEN
   BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
   REPEAT CONJ_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`;
      `n:num`; `x:A`] ERGODIC_AVG_BOUNDED) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    GEN_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`;
      `n:num`; `x:A`] ERGODIC_AVG_BOUNDED) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    GEN_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`;
      `n:num`; `tt (x:A):A`] ERGODIC_AVG_BOUNDED) THEN
    ASM_SIMP_TAC[MEASURE_PRESERVING_CARRIER] THEN REAL_ARITH_TAC;
    GEN_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`;
      `n:num`; `tt (x:A):A`] ERGODIC_AVG_BOUNDED) THEN
    ASM_SIMP_TAC[MEASURE_PRESERVING_CARRIER] THEN REAL_ARITH_TAC;
    GEN_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`;
      `x:A`; `n:num`] ERGODIC_AVG_DIFF_BOUND) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC];
   MP_TAC(ISPECL [`\n:num. inv(&(SUC n)) * sum(0..n)
     (\k. (f:A->real)(ITER k (tt:A->A) (tt (x:A))))`;
    `\n:num. inv(&(SUC n)) * sum(0..n)
     (\k. (f:A->real)(ITER k (tt:A->A) (x:A)))`;
    `--C:real`; `C:real`; `&2 * C`] REAL_LIMINF_LE_PERTURB) THEN
   BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
   REPEAT CONJ_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`;
      `n:num`; `tt (x:A):A`] ERGODIC_AVG_BOUNDED) THEN
    ASM_SIMP_TAC[MEASURE_PRESERVING_CARRIER] THEN REAL_ARITH_TAC;
    GEN_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`;
      `n:num`; `tt (x:A):A`] ERGODIC_AVG_BOUNDED) THEN
    ASM_SIMP_TAC[MEASURE_PRESERVING_CARRIER] THEN REAL_ARITH_TAC;
    GEN_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`;
      `n:num`; `x:A`] ERGODIC_AVG_BOUNDED) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    GEN_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`;
      `n:num`; `x:A`] ERGODIC_AVG_BOUNDED) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    GEN_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`;
      `x:A`; `n:num`] ERGODIC_AVG_DIFF_BOUND) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]]);;

(* T-invariance of the oscillation set *)
let ERGODIC_OSCILLATION_INVARIANT = prove
 (`!p:A prob_space tt f C a b.
  measure_preserving p tt /\ integrable p f /\
  (!x. x IN prob_carrier p ==> abs(f x) <= C) /\ a < b
  ==> invariant_event p tt {x | x IN prob_carrier p /\
    real_liminf (\n. inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x))) < a /\
    real_limsup (\n. inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x))) > b}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= C` ASSUME_TAC THENL
  [MP_TAC(SPEC `p:A prob_space` PROB_CARRIER_NONEMPTY) THEN
   REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
   DISCH_THEN(X_CHOOSE_TAC `z:A`) THEN
   SUBGOAL_THEN `abs((f:A->real) z) <= C` MP_TAC THENL
   [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
   ALL_TAC] THEN
  REWRITE_TAC[invariant_event] THEN CONJ_TAC THENL
  [MATCH_MP_TAC ERGODIC_OSCILLATION_MEASURABLE THEN
   EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
  EQ_TAC THENL
  [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`]
     ERGODIC_LIMSUP_SHIFT) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(SUBST1_TAC o SYM) THEN
   MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`]
     ERGODIC_LIMINF_SHIFT) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL
   [ASM_SIMP_TAC[MEASURE_PRESERVING_CARRIER]; ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`]
     ERGODIC_LIMSUP_SHIFT) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`]
     ERGODIC_LIMINF_SHIFT) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

(* The set where liminf < a < b < limsup has probability zero (bounded case) *)
let ERGODIC_OSCILLATION_NULL = prove
 (`!p:A prob_space tt f a b C.
    measure_preserving p tt /\ integrable p f /\ a < b /\
    (!x. x IN prob_carrier p ==> abs(f x) <= C)
    ==> prob p {x | x IN prob_carrier p /\
                    real_liminf (\n. inv(&(SUC n)) *
                      sum(0..n) (\k. f(ITER k tt x))) < a /\
                    real_limsup (\n. inv(&(SUC n)) *
                      sum(0..n) (\k. f(ITER k tt x))) > b} = &0`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `O_ab = {x:A | x IN prob_carrier p /\
    real_liminf (\n. inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x))) < a /\
    real_limsup (\n. inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x))) > b}` THEN
  (* O_ab is an event *)
  SUBGOAL_THEN `(O_ab:A->bool) IN prob_events p` ASSUME_TAC THENL
  [EXPAND_TAC "O_ab" THEN
   MATCH_MP_TAC ERGODIC_OSCILLATION_MEASURABLE THEN
   EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* O_ab is T-invariant *)
  SUBGOAL_THEN `invariant_event (p:A prob_space) (tt:A->A) (O_ab:A->bool)` ASSUME_TAC THENL
  [EXPAND_TAC "O_ab" THEN
   MATCH_MP_TAC ERGODIC_OSCILLATION_INVARIANT THEN
   EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Averages are bounded by C for x in prob_carrier *)
  SUBGOAL_THEN `!x:A n. x IN prob_carrier p ==>
    abs(inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x))) <= C` ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `!k:num. ITER k (tt:A->A) x IN prob_carrier p` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(SPEC `k:num` (MATCH_MP MEASURE_PRESERVING_ITER (ASSUME `measure_preserving (p:A prob_space) tt`))) THEN
    DISCH_THEN(MP_TAC o MATCH_MP MEASURE_PRESERVING_CARRIER) THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `!k:num. abs((f:A->real)(ITER k tt x)) <= C` ASSUME_TAC THENL
   [GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NUM] THEN
   SUBGOAL_THEN `~(&(SUC n) = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ; NOT_SUC]; ALL_TAC] THEN
   SUBGOAL_THEN `abs(sum(0..n) (\k. (f:A->real)(ITER k tt x))) <= &(SUC n) * C` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..n) (\k:num. C:real)` THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `sum(0..n) (\k. abs((f:A->real)(ITER k tt x)))` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUM_ABS_NUMSEG];
      MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_REWRITE_TAC[]];
     REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0; ADD1] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `inv(&(SUC n)) * (&(SUC n) * C)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS]; ASM_REWRITE_TAC[]];
    ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_MUL_LID; REAL_LE_REFL]];
   ALL_TAC] THEN
  (* On O_ab, limsup > b implies partial sums of (f-b) eventually positive *)
  SUBGOAL_THEN `!x:A. x IN O_ab ==>
    ?n. sum(0..n) (\k. ((f:A->real)(ITER k tt x) - b)) > &0` ASSUME_TAC THENL
  [X_GEN_TAC `x:A` THEN EXPAND_TAC "O_ab" THEN
   REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
   SUBGOAL_THEN `!n. --(C:real) <= inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x))` ASSUME_TAC THENL
   [GEN_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `n:num`]) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `!n. inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x)) <= C` ASSUME_TAC THENL
   [GEN_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `n:num`]) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
   MP_TAC(SPECL [`\n. inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x))`; `b:real`; `--C:real`; `C:real`]
     REAL_LIMSUP_GT_EXISTS_BOUNDED) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN EXISTS_TAC `m:num` THEN
   MATCH_MP_TAC(SPEC_ALL AVG_GT_IMP_SUM_POS) THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* On O_ab, liminf < a implies partial sums of (a-f) eventually positive *)
  SUBGOAL_THEN `!x:A. x IN O_ab ==>
    ?n. sum(0..n) (\k. (a - (f:A->real)(ITER k tt x))) > &0` ASSUME_TAC THENL
  [X_GEN_TAC `x:A` THEN EXPAND_TAC "O_ab" THEN
   REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
   SUBGOAL_THEN `!n. --(C:real) <= inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x))` ASSUME_TAC THENL
   [GEN_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `n:num`]) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `!n. inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x)) <= C` ASSUME_TAC THENL
   [GEN_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `n:num`]) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
   MP_TAC(SPECL [`\n. inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x))`; `a:real`; `--C:real`; `C:real`]
     REAL_LIMINF_LT_EXISTS_BOUNDED) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN EXISTS_TAC `m:num` THEN
   MATCH_MP_TAC(SPEC_ALL AVG_LT_IMP_SUM_POS) THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* f - b is integrable *)
  SUBGOAL_THEN `integrable (p:A prob_space) (\x. (f:A->real) x - b)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[INTEGRABLE_CONST];
   ALL_TAC] THEN
  (* a - f is integrable *)
  SUBGOAL_THEN `integrable (p:A prob_space) (\x. a - (f:A->real) x)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[INTEGRABLE_CONST];
   ALL_TAC] THEN
  (* Apply MEL_INVARIANT_SET to (f-b): E[(f-b) * 1_O] >= 0 *)
  SUBGOAL_THEN `&0 <= expectation (p:A prob_space) (\x. ((f:A->real) x - b) * indicator_fn O_ab x)` ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `\x:A. (f:A->real) x - b`; `O_ab:A->bool`] MEL_INVARIANT_SET) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `n:num` THEN
   BETA_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Apply MEL_INVARIANT_SET to (a-f): E[(a-f) * 1_O] >= 0 *)
  SUBGOAL_THEN `&0 <= expectation (p:A prob_space) (\x. (a - (f:A->real) x) * indicator_fn O_ab x)` ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `\x:A. a - (f:A->real) x`; `O_ab:A->bool`] MEL_INVARIANT_SET) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `n:num` THEN
   BETA_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Combine: E[(f-b)*1_O] >= 0 and E[(a-f)*1_O] >= 0 *)
  (* means (a-b)*P(O) >= 0, and since a < b, P(O) = 0 *)
  SUBGOAL_THEN `expectation (p:A prob_space) (\x. ((f:A->real) x - b) * indicator_fn O_ab x) +
    expectation p (\x. (a - f x) * indicator_fn O_ab x) =
    (a - b) * prob p O_ab` ASSUME_TAC THENL
  [SUBGOAL_THEN `expectation (p:A prob_space) (\x. ((f:A->real) x - b) * indicator_fn (O_ab:A->bool) x) +
    expectation p (\x. (a - f x) * indicator_fn O_ab x) =
    expectation p (\x. ((f x - b) * indicator_fn O_ab x + (a - f x) * indicator_fn O_ab x))` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXPECTATION_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `(\x:A. ((f:A->real) x - b) * indicator_fn (O_ab:A->bool) x +
     (a - f x) * indicator_fn O_ab x) = (\x. (a - b) * indicator_fn O_ab x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   MP_TAC(SPECL [`p:A prob_space`; `a - b:real`; `indicator_fn (O_ab:A->bool)`] EXPECTATION_CMUL) THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC EXPECTATION_INDICATOR THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[];
   SUBGOAL_THEN `(a - b) * prob (p:A prob_space) O_ab >= &0` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 <= expectation (p:A prob_space) (\x. ((f:A->real) x - b) * indicator_fn O_ab x)` THEN
    UNDISCH_TAC `&0 <= expectation (p:A prob_space) (\x. (a - (f:A->real) x) * indicator_fn O_ab x)` THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `&0 <= prob (p:A prob_space) O_ab` ASSUME_TAC THENL
    [MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[];
     ASM_CASES_TAC `prob (p:A prob_space) O_ab = &0` THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `&0 < prob (p:A prob_space) O_ab` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `(a - b) * prob (p:A prob_space) O_ab < &0` MP_TAC THENL
     [REWRITE_TAC[REAL_ARITH `x * y < &0 <=> &0 < (--x) * y`] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC]]]]);;

(* Key analysis lemma: bounded sequence with limsup = liminf converges *)
let BOUNDED_LIMSUP_LIMINF_CONVERGE = prove
 (`!s:num->real C.
    (!n. abs(s n) <= C) /\ real_limsup s = real_liminf s
    ==> (s ---> real_limsup s) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `L = real_limsup s` THEN
  SUBGOAL_THEN `!n:num. (s:num->real) n <= sup {s k | k >= n}` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
   [EXISTS_TAC `C:real` THEN REWRITE_TAC[IN_ELIM_THM; GE] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `k:num` (ASSUME `!n. abs((s:num->real) n) <= C`)) THEN REAL_ARITH_TAC;
    REWRITE_TAC[IN_ELIM_THM; GE] THEN EXISTS_TAC `n:num` THEN REWRITE_TAC[LE_REFL]];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n:num. inf {(s:num->real) k | k >= n} <= s n` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC INF_LE_ELEMENT THEN CONJ_TAC THENL
   [EXISTS_TAC `--C:real` THEN REWRITE_TAC[IN_ELIM_THM; GE] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `k:num` (ASSUME `!n. abs((s:num->real) n) <= C`)) THEN REAL_ARITH_TAC;
    REWRITE_TAC[IN_ELIM_THM; GE] THEN EXISTS_TAC `n:num` THEN REWRITE_TAC[LE_REFL]];
   ALL_TAC] THEN
  SUBGOAL_THEN `!m n:num. m <= n ==> sup {(s:num->real) k | k >= n} <= sup {s k | k >= m}` ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SUP_LE_SUBSET THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; GE] THEN
    EXISTS_TAC `(s:num->real) n` THEN EXISTS_TAC `n:num` THEN REWRITE_TAC[LE_REFL];
    CONJ_TAC THENL
    [REWRITE_TAC[SUBSET; IN_ELIM_THM; GE] THEN
     REPEAT STRIP_TAC THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
     EXISTS_TAC `C:real` THEN REWRITE_TAC[IN_ELIM_THM; GE] THEN
     REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     MP_TAC(SPEC `k:num` (ASSUME `!n. abs((s:num->real) n) <= C`)) THEN REAL_ARITH_TAC]];
   ALL_TAC] THEN
  SUBGOAL_THEN `!m n:num. m <= n ==> inf {(s:num->real) k | k >= m} <= inf {s k | k >= n}` ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_INF_SUBSET THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; GE] THEN
    EXISTS_TAC `(s:num->real) n` THEN EXISTS_TAC `n:num` THEN REWRITE_TAC[LE_REFL];
    CONJ_TAC THENL
    [REWRITE_TAC[SUBSET; IN_ELIM_THM; GE] THEN
     REPEAT STRIP_TAC THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
     EXISTS_TAC `--C:real` THEN REWRITE_TAC[IN_ELIM_THM; GE] THEN
     REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     MP_TAC(SPEC `k:num` (ASSUME `!n. abs((s:num->real) n) <= C`)) THEN REAL_ARITH_TAC]];
   ALL_TAC] THEN
  SUBGOAL_THEN `?N1:num. sup {(s:num->real) k | k >= N1} < L + e` STRIP_ASSUME_TAC THENL
  [MP_TAC(SPECL [`{sup {(s:num->real) k | k >= n} | n IN (:num)}`; `L + e:real`] INF_APPROACH) THEN
   SUBGOAL_THEN `inf {sup {(s:num->real) k | k >= n} | n IN (:num)} = L`
     (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[real_limsup]; ALL_TAC] THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; IN_UNIV] THEN
     EXISTS_TAC `sup {(s:num->real) k | k >= 0}` THEN EXISTS_TAC `0` THEN REFL_TAC;
     CONJ_TAC THENL
     [EXISTS_TAC `--C:real` THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
      X_GEN_TAC `x:real` THEN DISCH_THEN(X_CHOOSE_THEN `p:num` SUBST1_TAC) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(s:num->real) p` THEN CONJ_TAC THENL
      [MP_TAC(SPEC `p:num` (ASSUME `!n. abs((s:num->real) n) <= C`)) THEN REAL_ARITH_TAC;
       MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
       [EXISTS_TAC `C:real` THEN REWRITE_TAC[IN_ELIM_THM; GE] THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(SPEC `k:num` (ASSUME `!n. abs((s:num->real) n) <= C`)) THEN REAL_ARITH_TAC;
        REWRITE_TAC[IN_ELIM_THM; GE] THEN EXISTS_TAC `p:num` THEN REWRITE_TAC[LE_REFL]]];
      ASM_REAL_ARITH_TAC]];
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `?N2:num. L - e < inf {(s:num->real) k | k >= N2}` STRIP_ASSUME_TAC THENL
  [MP_TAC(SPECL [`{inf {(s:num->real) k | k >= n} | n IN (:num)}`; `L - e:real`] SUP_APPROACH) THEN
   SUBGOAL_THEN `sup {inf {(s:num->real) k | k >= n} | n IN (:num)} = L`
     (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `L = real_liminf s` THEN REWRITE_TAC[real_liminf] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[SYM th]); ALL_TAC] THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; IN_UNIV] THEN
     EXISTS_TAC `inf {(s:num->real) k | k >= 0}` THEN EXISTS_TAC `0` THEN REFL_TAC;
     CONJ_TAC THENL
     [EXISTS_TAC `C:real` THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
      X_GEN_TAC `x:real` THEN DISCH_THEN(X_CHOOSE_THEN `p:num` SUBST1_TAC) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(s:num->real) p` THEN CONJ_TAC THENL
      [MATCH_MP_TAC INF_LE_ELEMENT THEN CONJ_TAC THENL
       [EXISTS_TAC `--C:real` THEN REWRITE_TAC[IN_ELIM_THM; GE] THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(SPEC `k:num` (ASSUME `!n. abs((s:num->real) n) <= C`)) THEN REAL_ARITH_TAC;
        REWRITE_TAC[IN_ELIM_THM; GE] THEN EXISTS_TAC `p:num` THEN REWRITE_TAC[LE_REFL]];
       MP_TAC(SPEC `p:num` (ASSUME `!n. abs((s:num->real) n) <= C`)) THEN REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC]];
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[]];
   ALL_TAC] THEN
  EXISTS_TAC `MAX N1 N2` THEN X_GEN_TAC `q:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `N1 <= q /\ N2 <= (q:num)` STRIP_ASSUME_TAC THENL
  [POP_ASSUM MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sup {(s:num->real) k | k >= q} <= sup {s k | k >= N1}` ASSUME_TAC THENL
  [MP_TAC(SPECL [`N1:num`; `q:num`]
    (ASSUME `!m n:num. m <= n ==> sup {(s:num->real) k | k >= n} <= sup {s k | k >= m}`)) THEN
   ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `inf {(s:num->real) k | k >= N2} <= inf {s k | k >= q}` ASSUME_TAC THENL
  [MP_TAC(SPECL [`N2:num`; `q:num`]
    (ASSUME `!m n:num. m <= n ==> inf {(s:num->real) k | k >= m} <= inf {s k | k >= n}`)) THEN
   ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `L - e < (s:num->real) q` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inf {(s:num->real) k | k >= q}` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inf {(s:num->real) k | k >= N2}` THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:num->real) q < L + e` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sup {(s:num->real) k | k >= N1}` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sup {(s:num->real) k | k >= q}` THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Bounded sequences: liminf <= limsup *)
let REAL_LIMINF_LE_LIMSUP_ABS = prove
 (`!s:num->real C. (!n. abs(s n) <= C)
   ==> real_liminf s <= real_limsup s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_limsup; real_liminf] THEN
  MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
  [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; IN_UNIV] THEN
   MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
  X_GEN_TAC `x:real` THEN DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
  MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
  [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; IN_UNIV] THEN
   MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
  X_GEN_TAC `y:real` THEN DISCH_THEN(X_CHOOSE_THEN `p:num` SUBST1_TAC) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(s:num->real)(MAX m p)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC INF_LE_ELEMENT THEN CONJ_TAC THENL
   [EXISTS_TAC `--C:real` THEN REWRITE_TAC[IN_ELIM_THM; GE] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `k:num` (ASSUME `!n. abs((s:num->real) n) <= C`)) THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[IN_ELIM_THM; GE] THEN EXISTS_TAC `MAX m p` THEN
    REWRITE_TAC[MAX] THEN ARITH_TAC];
   MP_TAC(ISPECL [`{(s:num->real) k | k >= p}`; `(s:num->real)(MAX m p)`;
                   `C:real`; `(s:num->real)(MAX m p)`] REAL_LE_SUP) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [REWRITE_TAC[IN_ELIM_THM; GE] THEN EXISTS_TAC `MAX m p` THEN
     REWRITE_TAC[MAX] THEN ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM; GE] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `k:num` (ASSUME `!n. abs((s:num->real) n) <= C`)) THEN
    REAL_ARITH_TAC;
    REAL_ARITH_TAC]]);;

(* Birkhoff for bounded f: almost sure convergence *)
let BIRKHOFF_ERGODIC_THEOREM_BOUNDED = prove
 (`!p:A prob_space tt f C.
    measure_preserving p tt /\ integrable p f /\
    (!x. x IN prob_carrier p ==> abs(f x) <= C)
    ==> almost_surely p
          {x | ?L. ((\n. inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x)))
                    ---> L) sequentially}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[almost_surely] THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
     ~(x IN {x | ?L. ((\n. inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x))) ---> L) sequentially})} =
   {x | x IN prob_carrier p /\
     ~(?L. ((\n. inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x))) ---> L) sequentially)}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `COUNTABLE {(a:real,b:real) | rational a /\ rational b /\ a < b} /\
    ~({(a:real,b:real) | rational a /\ rational b /\ a < b} = {})`
    STRIP_ASSUME_TAC THENL
  [CONJ_TAC THENL
   [MATCH_MP_TAC COUNTABLE_SUBSET THEN
    EXISTS_TAC `rational CROSS (rational:real->bool)` THEN
    SIMP_TAC[COUNTABLE_CROSS; COUNTABLE_RATIONAL] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; CROSS; FORALL_PAIR_THM; IN] THEN
    MESON_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; EXISTS_PAIR_THM] THEN
    MAP_EVERY EXISTS_TAC [`&0`; `&1`; `&0`; `&1`] THEN
    REWRITE_TAC[PAIR_EQ; RATIONAL_CLOSED] THEN CONV_TAC REAL_RAT_REDUCE_CONV];
   ALL_TAC] THEN
  SUBGOAL_THEN `?g:num->real#real.
    {(a,b) | rational a /\ rational b /\ a < b} = IMAGE g (:num)`
    STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC COUNTABLE_AS_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n:num. rational(FST((g:num->real#real) n)) /\
    rational(SND(g n)) /\ FST(g n) < SND(g n)` ASSUME_TAC THENL
  [GEN_TAC THEN
   SUBGOAL_THEN `(g:num->real#real) n IN
     {(a,b) | rational a /\ rational b /\ a < b}` MP_TAC THENL
   [UNDISCH_TAC `{a:real,b | rational a /\ rational b /\ a < b} =
      IMAGE (g:num->real#real) (:num)` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN MESON_TAC[]; ALL_TAC] THEN
   SPEC_TAC(`(g:num->real#real) n`, `p':real#real`) THEN
   REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM; FST; SND; PAIR_EQ] THEN
   MESON_TAC[];
   ALL_TAC] THEN
  EXISTS_TAC `UNIONS {(\n. {x:A | x IN prob_carrier p /\
    real_liminf (\m. inv(&(SUC m)) * sum(0..m) (\k. (f:A->real)(ITER k tt x))) < FST((g:num->real#real) n) /\
    real_limsup (\m. inv(&(SUC m)) * sum(0..m) (\k. f(ITER k tt x))) > SND(g n)}) n | n IN (:num)}` THEN
  REWRITE_TAC[BETA_THM] THEN CONJ_TAC THENL
  [(* null_event of the countable union *)
   MATCH_MP_TAC NULL_EVENT_COUNTABLE_UNION THEN GEN_TAC THEN
   REWRITE_TAC[null_event] THEN CONJ_TAC THENL
   [MATCH_MP_TAC ERGODIC_OSCILLATION_MEASURABLE THEN
    EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`;
                   `FST((g:num->real#real) n)`; `SND((g:num->real#real) n)`; `C:real`]
      ERGODIC_OSCILLATION_NULL) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[]]];
   ALL_TAC] THEN
  (* subset: non-convergence set is in the union *)
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIONS; IN_UNIV] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  ABBREV_TAC `s = (\m. inv(&(SUC m)) * sum(0..m) (\k. (f:A->real)(ITER k tt x)))` THEN
  SUBGOAL_THEN `!n:num. abs((s:num->real) n) <= C` ASSUME_TAC THENL
  [EXPAND_TAC "s" THEN REWRITE_TAC[] THEN GEN_TAC THEN
   SUBGOAL_THEN `!k:num. ITER k (tt:A->A) x IN prob_carrier p` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(SPEC `k:num` (MATCH_MP MEASURE_PRESERVING_ITER
      (ASSUME `measure_preserving (p:A prob_space) tt`))) THEN
    DISCH_THEN(MP_TAC o MATCH_MP MEASURE_PRESERVING_CARRIER) THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `!k:num. abs((f:A->real)(ITER k tt x)) <= C` ASSUME_TAC THENL
   [GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NUM] THEN
   SUBGOAL_THEN `~(&(SUC n) = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ; NOT_SUC]; ALL_TAC] THEN
   SUBGOAL_THEN `abs(sum(0..n) (\k. (f:A->real)(ITER k tt x))) <= &(SUC n) * C` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..n) (\k:num. C:real)` THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `sum(0..n) (\k. abs((f:A->real)(ITER k tt x)))` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUM_ABS_NUMSEG]; MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_REWRITE_TAC[]];
     REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0; ADD1] THEN REAL_ARITH_TAC]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `inv(&(SUC n)) * (&(SUC n) * C)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS]; ASM_REWRITE_TAC[]];
    ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_MUL_LID; REAL_LE_REFL]];
   ALL_TAC] THEN
  SUBGOAL_THEN `~(real_limsup s = real_liminf s)` ASSUME_TAC THENL
  [DISCH_TAC THEN UNDISCH_TAC `~(?L:real. (s ---> L) sequentially)` THEN
   REWRITE_TAC[] THEN EXISTS_TAC `real_limsup s` THEN
   MATCH_MP_TAC BOUNDED_LIMSUP_LIMINF_CONVERGE THEN
   EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `real_liminf s < real_limsup s` ASSUME_TAC THENL
  [MP_TAC(SPECL [`s:num->real`; `C:real`] REAL_LIMINF_LE_LIMSUP_ABS) THEN
   ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  MP_TAC(SPECL [`real_liminf s`; `real_limsup s`] RATIONAL_BETWEEN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`q1:real`; `real_limsup s`] RATIONAL_BETWEEN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?nn:num. (g:num->real#real) nn = (q1,q2)` STRIP_ASSUME_TAC THENL
  [SUBGOAL_THEN `(q1:real,q2:real) IN IMAGE (g:num->real#real) (:num)` MP_TAC THENL
   [UNDISCH_TAC `{a,b | rational a /\ rational b /\ a < b} = IMAGE (g:num->real#real) (:num)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN
    MAP_EVERY EXISTS_TAC [`q1:real`; `q2:real`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN MESON_TAC[]];
   ALL_TAC] THEN
  EXISTS_TAC `{x:A | x IN prob_carrier p /\
    real_liminf (\m. inv(&(SUC m)) * sum(0..m) (\k. (f:A->real)(ITER k tt x))) < FST((g:num->real#real) nn) /\
    real_limsup (\m. inv(&(SUC m)) * sum(0..m) (\k. f(ITER k tt x))) > SND(g nn)}` THEN
  CONJ_TAC THENL
  [EXISTS_TAC `nn:num` THEN REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[FST; SND] THEN
  REWRITE_TAC[real_gt] THEN ASM_REWRITE_TAC[]);;

(* Wiener's maximal ergodic inequality:
   For f >= 0 integrable, P(sup_n avg_n(f) > lambda) <= E[f]/lambda.
   Stated using ergodic_maxsum: {exists n. M_n(f-lam) > 0} = {sup avg(f) > lam} *)
let WIENER_MAXIMAL_INEQUALITY = prove
 (`!p:A prob_space tt (f:A->real) lam.
    measure_preserving p tt /\ integrable p f /\
    (!x. x IN prob_carrier p ==> &0 <= f x) /\ &0 < lam
    ==> prob p {x | x IN prob_carrier p /\
          (?n. ergodic_maxsum (\x. f x - lam) tt n x > &0)}
        <= inv(lam) * expectation p f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x. (f:A->real) x - lam)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC] THEN
  ABBREV_TAC `A = {x:A | x IN prob_carrier p /\
    (?n. ergodic_maxsum (\x. (f:A->real) x - lam) tt n x > &0)}` THEN
  SUBGOAL_THEN `(A:A->bool) IN prob_events p` ASSUME_TAC THENL
  [EXPAND_TAC "A" THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
     (?n. ergodic_maxsum (\x. (f:A->real) x - lam) tt n x > &0)} =
     UNIONS {({x:A | x IN prob_carrier p /\
       ergodic_maxsum (\x. f x - lam) tt n x > &0}) | n IN (:num)}`
     SUBST1_TAC THENL
   [SET_TAC[];
    MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN
    GEN_TAC THEN MATCH_MP_TAC ERGODIC_MAXSUM_POS_EVENT THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* Apply maximal ergodic lemma: E[(f-lam)*1_A] >= 0 *)
  SUBGOAL_THEN `&0 <= expectation (p:A prob_space)
    (\x. ((f:A->real) x - lam) * indicator_fn A x)` ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `\x:A. (f:A->real) x - lam`]
    MAXIMAL_ERGODIC_INFINITE) THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
     (?n. ergodic_maxsum (\x. (f:A->real) x - lam) tt n x > &0)} = A`
     (fun th -> REWRITE_TAC[th]) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Chain: lam * P(A) <= E[f*1_A] <= E[f], so P(A) <= E[f]/lam *)
  SUBGOAL_THEN `lam * prob (p:A prob_space) A <= expectation p (f:A->real)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `expectation (p:A prob_space)
     (\x. (f:A->real) x * indicator_fn A x)` THEN
   CONJ_TAC THENL
   [SUBGOAL_THEN `expectation (p:A prob_space)
      (\x. ((f:A->real) x - lam) * indicator_fn A x) =
      expectation p (\x. f x * indicator_fn A x) - lam * prob p A`
      ASSUME_TAC THENL
    [SUBGOAL_THEN `(\x:A. ((f:A->real) x - lam) * indicator_fn (A:A->bool) x) =
       (\x. f x * indicator_fn A x - lam * indicator_fn A x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `integrable (p:A prob_space)
       (\x. (f:A->real) x * indicator_fn (A:A->bool) x)` ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
     SUBGOAL_THEN `integrable (p:A prob_space)
       (\x. lam * indicator_fn (A:A->bool) x)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`p:A prob_space`; `lam:real`; `indicator_fn (A:A->bool)`]
        INTEGRABLE_CMUL) THEN
      ASM_SIMP_TAC[INTEGRABLE_INDICATOR; ETA_AX]; ALL_TAC] THEN
     ASM_SIMP_TAC[EXPECTATION_SUB] THEN AP_TERM_TAC THEN
     MP_TAC(ISPECL [`p:A prob_space`; `lam:real`; `indicator_fn (A:A->bool)`]
       EXPECTATION_CMUL) THEN
     ASM_SIMP_TAC[INTEGRABLE_INDICATOR; ETA_AX] THEN
     DISCH_THEN SUBST1_TAC THEN
     AP_TERM_TAC THEN MATCH_MP_TAC EXPECTATION_INDICATOR THEN ASM_REWRITE_TAC[];
     ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC EXPECTATION_MONO THEN
    ASM_SIMP_TAC[INTEGRABLE_MUL_INDICATOR_FN] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THENL
    [REWRITE_TAC[REAL_MUL_RID; REAL_LE_REFL];
     REWRITE_TAC[REAL_MUL_RZERO] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC[]]];
   ALL_TAC] THEN
  (* Final: from lam * P(A) <= E[f], derive P(A) <= inv(lam) * E[f] *)
  SUBGOAL_THEN `&0 <= prob (p:A prob_space) A` ASSUME_TAC THENL
  [MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= expectation (p:A prob_space) (f:A->real)` ASSUME_TAC THENL
  [MATCH_MP_TAC EXPECTATION_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `inv lam * expectation (p:A prob_space) (f:A->real) =
    expectation p f / lam` SUBST1_TAC THENL
  [REWRITE_TAC[real_div]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

(* Truncation of f at level M is integrable *)
let ERGODIC_TRUNCATION_INTEGRABLE = prove
 (`!p:A prob_space (f:A->real) M.
    integrable p f ==> integrable p (\x. max (-- &M) (min (&M) (f x)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:A. max (-- &M) (min (&M) ((f:A->real) x))) =
    (\x. max ((\x. -- &M) x) (min ((\x. &M) x) (f x)))` SUBST1_TAC THENL
  [REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC INTEGRABLE_MAX THEN CONJ_TAC THENL
  [REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC] THEN
  MATCH_MP_TAC INTEGRABLE_MIN THEN ASM_REWRITE_TAC[INTEGRABLE_CONST]);;

(* |f - truncation| <= |f| *)
let ERGODIC_TRUNCATION_ABS_BOUND = prove
 (`!f:A->real x M. abs(f x - max (-- &M) (min (&M) (f x))) <= abs(f x)`,
  REPEAT GEN_TAC THEN REAL_ARITH_TAC);;

(* |f - truncation| converges to 0 pointwise *)
let ERGODIC_TRUNCATION_POINTWISE = prove
 (`!f:A->real x. ((\M. f x - max(-- &M) (min (&M) (f x))) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `abs((f:A->real) x)` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  X_GEN_TAC `M:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs((f:A->real) x) <= &M` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N:real` THEN
   ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `max (-- &M) (min (&M) ((f:A->real) x)) = f x` SUBST1_TAC THENL
  [POP_ASSUM MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* E[|f - f_M|] -> 0 using Dominated Convergence *)
let ERGODIC_TRUNCATION_L1 = prove
 (`!p:A prob_space (f:A->real).
    integrable p f
    ==> ((\M. expectation p (\x. abs(f x - max (-- &M) (min (&M) (f x)))))
         ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `\M (x:A). abs((f:A->real) x - max (-- &M) (min (&M) (f x)))`;
    `\x:A. &0:real`;
    `\x:A. abs((f:A->real) x)`] DOMINATED_CONVERGENCE) THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THENL
   [GEN_TAC THEN BETA_TAC THEN MATCH_MP_TAC INTEGRABLE_ABS THEN
    MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ERGODIC_TRUNCATION_INTEGRABLE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC INTEGRABLE_ABS THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[REAL_ABS_ABS] THEN
    REWRITE_TAC[ERGODIC_TRUNCATION_ABS_BOUND];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`sequentially`; `\M:num. (f:A->real) x - max(-- &M) (min (&M) (f x))`; `&0`] REALLIM_ABS) THEN
    REWRITE_TAC[REAL_ABS_NUM] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[ERGODIC_TRUNCATION_POINTWISE]];
   DISCH_THEN(MP_TAC o CONJUNCT2) THEN BETA_TAC THEN
   SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. &0) = &0` SUBST1_TAC THENL
   [REWRITE_TAC[EXPECTATION_CONST; REAL_MUL_RZERO];
    REWRITE_TAC[]]]);;

(* Helper: if average of |f| at orbit point exceeds lam, maxsum is positive *)
let AVG_GT_IMP_MAXSUM_POS = prove
 (`!f:A->real tt x q lam.
    inv(&(SUC q)) * sum(0..q) (\j. abs(f(ITER j tt x))) > lam /\ &0 < lam
    ==> ergodic_maxsum (\y. abs(f y) - lam) tt q x > &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(SUC q)` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_OF_NUM_LT; LT_0]; ALL_TAC] THEN
  SUBGOAL_THEN `~(&(SUC q) = &0)` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_OF_NUM_EQ; NOT_SUC]; ALL_TAC] THEN
  SUBGOAL_THEN `&(SUC q) * lam < sum(0..q) (\j. abs((f:A->real)(ITER j tt x)))` ASSUME_TAC THENL
  [SUBGOAL_THEN `lam < inv(&(SUC q)) * sum(0..q) (\j. abs((f:A->real)(ITER j tt x)))` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`&(SUC q)`; `lam:real`;
     `inv(&(SUC q)) * sum(0..q) (\j. abs((f:A->real)(ITER j tt x)))`] REAL_LT_LMUL) THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `&(SUC q) * (inv(&(SUC q)) * sum(0..q) (\j. abs((f:A->real)(ITER j tt x)))) =
     sum(0..q) (\j. abs(f(ITER j tt x)))` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_LID];
    SIMP_TAC[]];
   ALL_TAC] THEN
  REWRITE_TAC[real_gt] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `sum(0..q) (\j. (\y:A. abs((f:A->real) y) - lam)(ITER j tt x))` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[] THEN
   REWRITE_TAC[SUM_SUB_NUMSEG; SUM_CONST_NUMSEG; SUB_0] THEN
   UNDISCH_TAC `&(SUC q) * lam < sum (0..q) (\j. abs ((f:A->real) (ITER j tt x)))` THEN
   REWRITE_TAC[ADD1] THEN REAL_ARITH_TAC;
   REWRITE_TAC[ERGODIC_MAXSUM_GE_SUM]]);;

(* Key containment: if Cesaro averages oscillate by > inv(k) infinitely often,
   then either avg(f_M) doesn't converge or avg(|f-f_M|) > inv(4k) somewhere.
   This is the corrected containment using oscillation level. *)
let BIRKHOFF_OSCILLATION_CONTAINMENT = prove
 (`!p:A prob_space tt (f:A->real) M k.
    measure_preserving p tt /\ integrable p f /\ ~(k = 0)
    ==> {x | x IN prob_carrier p /\
             (!N. ?m n. N <= m /\ N <= n /\
               abs(inv(&(SUC m)) * sum(0..m) (\j. f(ITER j tt x)) -
                   inv(&(SUC n)) * sum(0..n) (\j. f(ITER j tt x))) > inv(&k))}
        SUBSET
        {x | x IN prob_carrier p /\
             ~(?L. ((\n. inv(&(SUC n)) * sum(0..n)
               (\j. max (-- &M) (min (&M) (f(ITER j tt x))))) ---> L) sequentially)}
        UNION
        {x | x IN prob_carrier p /\
             (?n. ergodic_maxsum
               (\x. abs(f x - max (-- &M) (min (&M) (f x))) - inv(&(4 * k)))
               tt n x > &0)}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `?L. ((\n. inv(&(SUC n)) * sum(0..n)
    (\j. max (-- &(M:num)) (min (&M) ((f:A->real)(ITER j tt x))))) ---> L) sequentially` THENL
  [DISJ2_TAC THEN FIRST_X_ASSUM(X_CHOOSE_TAC `L:real`) THEN
   UNDISCH_TAC `((\n. inv (&(SUC n)) *
     sum (0..n) (\j. max (-- &(M:num)) (min (&M) ((f:A->real) (ITER j tt x))))) ---> L)
     sequentially` THEN
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   DISCH_THEN(MP_TAC o SPEC `inv(&(4 * k))`) THEN
   ANTS_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ; REAL_OF_NUM_LT] THEN
    UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN
   UNDISCH_TAC `!N. ?m n. N <= m /\ N <= n /\
     abs(inv(&(SUC m)) * sum(0..m) (\j. (f:A->real)(ITER j tt x)) -
         inv(&(SUC n)) * sum(0..n) (\j. f(ITER j tt x))) > inv(&k)` THEN
   DISCH_THEN(MP_TAC o SPEC `N0:num`) THEN STRIP_TAC THEN
   SUBGOAL_THEN `abs(inv(&(SUC m)) * sum(0..m) (\j. max (-- &(M:num)) (min (&M) ((f:A->real)(ITER j tt x)))) - L) < inv(&(4 * k))` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `abs(inv(&(SUC n)) * sum(0..n) (\j. max (-- &(M:num)) (min (&M) ((f:A->real)(ITER j tt x)))) - L) < inv(&(4 * k))` ASSUME_TAC THENL
   [UNDISCH_TAC `!n. N0 <= n ==> abs(inv(&(SUC n)) * sum(0..n) (\j. max (-- &(M:num)) (min (&M) ((f:A->real)(ITER j tt x)))) - L) < inv(&(4 * k))` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   (* Key: avg(|f-f_M|) > inv(4k) at m or n via triangle inequality *)
   SUBGOAL_THEN `inv(&(SUC m)) * sum(0..m) (\j. abs((f:A->real)(ITER j tt x) - max (-- &(M:num))(min (&M)(f(ITER j tt x))))) > inv(&(4 * k)) \/
     inv(&(SUC n)) * sum(0..n) (\j. abs((f:A->real)(ITER j tt x) - max (-- &M)(min (&M)(f(ITER j tt x))))) > inv(&(4 * k))` MP_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p /\ ~q ==> F) ==> p \/ q`) THEN
    REWRITE_TAC[real_gt; REAL_NOT_LT] THEN STRIP_TAC THEN
    SUBGOAL_THEN `abs(inv(&(SUC m)) * sum(0..m) (\j. (f:A->real)(ITER j tt x) - max (-- &(M:num))(min (&M)(f(ITER j tt x))))) <= inv(&(4 * k))` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `inv(&(SUC m)) * sum(0..m) (\j. abs((f:A->real)(ITER j tt x) - max (-- &M)(min (&M)(f(ITER j tt x)))))` THEN
     ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NUM] THEN
     MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
     REWRITE_TAC[SUM_ABS_NUMSEG]; ALL_TAC] THEN
    SUBGOAL_THEN `abs(inv(&(SUC n)) * sum(0..n) (\j. (f:A->real)(ITER j tt x) - max (-- &(M:num))(min (&M)(f(ITER j tt x))))) <= inv(&(4 * k))` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `inv(&(SUC n)) * sum(0..n) (\j. abs((f:A->real)(ITER j tt x) - max (-- &M)(min (&M)(f(ITER j tt x)))))` THEN
     ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NUM] THEN
     MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
     REWRITE_TAC[SUM_ABS_NUMSEG]; ALL_TAC] THEN
    SUBGOAL_THEN `!q. inv(&(SUC q)) * sum(0..q) (\j. (f:A->real)(ITER j tt x)) =
      inv(&(SUC q)) * sum(0..q) (\j. max (-- &(M:num))(min (&M)(f(ITER j tt x)))) +
      inv(&(SUC q)) * sum(0..q) (\j. f(ITER j tt x) - max (-- &M)(min (&M)(f(ITER j tt x))))` ASSUME_TAC THENL
    [GEN_TAC THEN REWRITE_TAC[GSYM REAL_ADD_LDISTRIB; GSYM SUM_ADD_NUMSEG] THEN
     AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
     REPEAT STRIP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `abs(inv(&(SUC m)) * sum(0..m) (\j. (f:A->real)(ITER j tt x)) -
      inv(&(SUC n)) * sum(0..n) (\j. f(ITER j tt x))) > inv(&k)` THEN
    REWRITE_TAC[real_gt; REAL_NOT_LT] THEN
    FIRST_X_ASSUM(fun th -> PURE_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(inv(&(SUC m)) * sum(0..m) (\j. max (-- &(M:num))(min (&M)((f:A->real)(ITER j tt x)))) - L) +
      abs(L - inv(&(SUC n)) * sum(0..n) (\j. max (-- &M)(min (&M)(f(ITER j tt x))))) +
      abs(inv(&(SUC m)) * sum(0..m) (\j. f(ITER j tt x) - max (-- &M)(min (&M)(f(ITER j tt x))))) +
      abs(inv(&(SUC n)) * sum(0..n) (\j. f(ITER j tt x) - max (-- &M)(min (&M)(f(ITER j tt x)))))` THEN
    CONJ_TAC THENL
    [REAL_ARITH_TAC;
     SUBGOAL_THEN `~(&k = &0)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     SUBGOAL_THEN `inv(&k) = inv(&(4*k)) + inv(&(4*k)) + inv(&(4*k)) + inv(&(4*k))` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
      MATCH_MP_TAC(REAL_FIELD `~(k = &0) ==> inv(k) = inv(&4 * k) + inv(&4 * k) + inv(&4 * k) + inv(&4 * k)`) THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
     MATCH_MP_TAC(REAL_ARITH `a < e /\ b < e /\ c <= e /\ d <= e ==> a + b + c + d <= e + e + e + e`) THEN
     ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `abs(inv(&(SUC n)) * sum(0..n) (\j. max (-- &M) (min (&M) ((f:A->real)(ITER j tt x)))) - L) < inv(&(4*k))` THEN
     REAL_ARITH_TAC]; ALL_TAC] THEN
   SUBGOAL_THEN `&0 < inv(&(4 * k))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ; REAL_OF_NUM_LT] THEN
    UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; ALL_TAC] THEN
   STRIP_TAC THENL
   [EXISTS_TAC `m:num` THEN
    MATCH_MP_TAC(REWRITE_RULE[](ISPEC `\x:A. (f:A->real) x - max (-- &(M:num))(min (&M)(f x))` AVG_GT_IMP_MAXSUM_POS)) THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `n:num` THEN
    MATCH_MP_TAC(REWRITE_RULE[](ISPEC `\x:A. (f:A->real) x - max (-- &(M:num))(min (&M)(f x))` AVG_GT_IMP_MAXSUM_POS)) THEN
    ASM_REWRITE_TAC[]];
   DISJ1_TAC THEN ASM_REWRITE_TAC[]]);;

(* If a real sequence doesn't converge, it oscillates at some level inv(SUC k) *)
let NOT_CONVERGENT_OSCILLATION = prove
 (`!s:num->real. ~(?L. (s ---> L) sequentially)
    ==> ?k. !N. ?m n. N <= m /\ N <= n /\ abs(s m - s n) > inv(&(SUC k))`,
  GEN_TAC THEN
  MATCH_MP_TAC(TAUT `(~q ==> ~p) ==> (p ==> q)`) THEN
  REWRITE_TAC[NOT_EXISTS_THM; NOT_FORALL_THM; NOT_IMP] THEN
  REWRITE_TAC[REAL_NOT_LT; real_gt; DE_MORGAN_THM] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(cauchy:((num->real^1)->bool)) (\n. lift(s n))` MP_TAC THENL
  [REWRITE_TAC[cauchy; GE; DIST_LIFT] THEN
   X_GEN_TAC `e:real` THEN DISCH_TAC THEN
   MP_TAC(SPEC `e:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
   DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&(SUC k))` THEN
   CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `n:num`]) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&k)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC];
   ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `?l:real^1. ((\n. lift(s n)) --> l) sequentially` MP_TAC THENL
  [REWRITE_TAC[CONVERGENT_EQ_CAUCHY] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `l:real^1`) THEN EXISTS_TAC `drop l` THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  UNDISCH_TAC `((\n. lift((s:num->real) n)) --> l:real^1) sequentially` THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN
  MATCH_MP_TAC(TAUT `(a <=> b) ==> (a ==> b)`) THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  AP_TERM_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV) [GSYM LIFT_DROP] THEN
  REWRITE_TAC[DIST_LIFT]);;

(* BIRKHOFF'S ERGODIC THEOREM: S_n(f)/n converges almost surely *)
let BIRKHOFF_ERGODIC_THEOREM = prove
 (`!p:A prob_space tt f.
    measure_preserving p tt /\ integrable p f
    ==> almost_surely p
          {x | ?L. ((\n. inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x)))
                    ---> L) sequentially}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[almost_surely] THEN
  (* For each M, bounded Birkhoff gives null event for f_M *)
  SUBGOAL_THEN `!M:num. ?NM:A->bool. null_event (p:A prob_space) NM /\
    {x:A | x IN prob_carrier p /\
      ~(?L. ((\n. inv(&(SUC n)) * sum(0..n)
        (\k. max (-- &M) (min (&M) ((f:A->real)(ITER k tt x))))) ---> L) sequentially)}
    SUBSET NM` ASSUME_TAC THENL
  [GEN_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`;
     `\x:A. max (-- &M) (min (&M) ((f:A->real) x))`; `&M:real`]
     BIRKHOFF_ERGODIC_THEOREM_BOUNDED) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [MATCH_MP_TAC ERGODIC_TRUNCATION_INTEGRABLE THEN ASM_REWRITE_TAC[];
     REPEAT STRIP_TAC THEN REAL_ARITH_TAC];
    REWRITE_TAC[almost_surely] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `N:A->bool` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
   ALL_TAC] THEN
  (* For each M and k, Wiener gives prob bound on remainder *)
  SUBGOAL_THEN `!M k. prob (p:A prob_space)
    {x:A | x IN prob_carrier p /\
      (?n. ergodic_maxsum (\x. abs((f:A->real) x - max (-- &M) (min (&M) (f x))) -
        inv(&(SUC k))) tt n x > &0)}
    <= &(SUC k) * expectation p (\x. abs(f x - max (-- &M) (min (&M) (f x))))`
    ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`;
     `\x:A. abs((f:A->real) x - max (-- &M) (min (&M) (f x)))`;
     `inv(&(SUC k))`] WIENER_MAXIMAL_INEQUALITY) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_ABS THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ERGODIC_TRUNCATION_INTEGRABLE THEN
     ASM_REWRITE_TAC[];
     REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_POS];
     REWRITE_TAC[REAL_LT_INV_EQ; REAL_OF_NUM_LT; LT_0]];
    REWRITE_TAC[REAL_INV_INV]];
   ALL_TAC] THEN
  (* E[|f - f_M|] -> 0 *)
  MP_TAC(ISPECL [`p:A prob_space`; `f:A->real`] ERGODIC_TRUNCATION_L1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* Skolemize and establish helper facts *)
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_TAC `NM:num->A->bool`) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN `!M:num k:num. integrable (p:A prob_space)
    (\x:A. abs((f:A->real) x - max (-- &M) (min (&M) (f x))) - inv(&(4 * SUC k)))`
    ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
   REWRITE_TAC[INTEGRABLE_CONST] THEN
   MATCH_MP_TAC INTEGRABLE_ABS THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
   ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ERGODIC_TRUNCATION_INTEGRABLE THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!M:num k:num.
    {x:A | x IN prob_carrier p /\
      (?n. ergodic_maxsum (\x. abs((f:A->real) x - max (-- &M) (min (&M) (f x))) -
        inv(&(4 * SUC k))) tt n x > &0)} IN prob_events (p:A prob_space)`
    ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
     (?n:num. ergodic_maxsum (\x. abs((f:A->real) x - max (-- &M) (min (&M) (f x))) -
       inv(&(4 * SUC k))) tt n x > &0)} =
     UNIONS (IMAGE (\n:num. {x:A | x IN prob_carrier p /\
       ergodic_maxsum (\x. abs(f x - max (-- &M) (min (&M) (f x))) -
         inv(&(4 * SUC k))) tt n x > &0}) (:num))` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIONS; EXISTS_IN_IMAGE; IN_UNIV] THEN
    MESON_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC PROB_COUNTABLE_UNION_IN_EVENTS THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN GEN_TAC THEN
    MATCH_MP_TAC ERGODIC_MAXSUM_POS_EVENT THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[NUM_COUNTABLE]];
   ALL_TAC] THEN
  SUBGOAL_THEN `!M:num k:num. prob (p:A prob_space)
    {x:A | x IN prob_carrier p /\
      (?n. ergodic_maxsum (\x. abs((f:A->real) x - max (-- &M) (min (&M) (f x))) -
        inv(&(4 * SUC k))) tt n x > &0)}
    <= &(4 * SUC k) * expectation p (\x. abs(f x - max (-- &M) (min (&M) (f x))))`
    ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN
   SUBGOAL_THEN `4 * SUC k = SUC(4 * k + 3)` SUBST1_TAC THENL
   [ARITH_TAC; ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `!M:num k:num. (NM:num->A->bool) M UNION
    {x:A | x IN prob_carrier p /\
      (?n. ergodic_maxsum (\x. abs((f:A->real) x - max (-- &M) (min (&M) (f x))) -
        inv(&(4 * SUC k))) tt n x > &0)} IN prob_events (p:A prob_space)`
    ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN MATCH_MP_TAC PROB_UNION_IN_EVENTS THEN
   ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[null_event];
   ALL_TAC] THEN
  (* Each INTERS over M is a null event *)
  SUBGOAL_THEN `!k:num. null_event (p:A prob_space)
    (INTERS (IMAGE (\M:num. (NM:num->A->bool) M UNION
      {x:A | x IN prob_carrier p /\
        (?n. ergodic_maxsum (\x. abs((f:A->real) x - max (-- &M) (min (&M) (f x))) -
          inv(&(4 * SUC k))) tt n x > &0)}) (:num)))` ASSUME_TAC THENL
  [X_GEN_TAC `k:num` THEN REWRITE_TAC[null_event] THEN
   SUBGOAL_THEN `INTERS (IMAGE (\M:num. (NM:num->A->bool) M UNION
     {x:A | x IN prob_carrier p /\
       (?n. ergodic_maxsum (\x. abs((f:A->real) x - max (-- &M) (min (&M) (f x))) -
         inv(&(4 * SUC k))) tt n x > &0)}) (:num)) IN prob_events (p:A prob_space)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC PROB_COUNTABLE_INTERS_IN_EVENTS THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY; UNIV_NOT_EMPTY] THEN CONJ_TAC THENL
    [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[NUM_COUNTABLE]];
    ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN
   CONJ_TAC THENL [MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_EPSILON THEN REWRITE_TAC[REAL_ADD_LID] THEN
   X_GEN_TAC `e:real` THEN DISCH_TAC THEN
   UNDISCH_TAC `((\M. expectation (p:A prob_space) (\x. abs ((f:A->real) x - max (-- &M) (min (&M) (f x))))) ---> &0) sequentially` THEN
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   DISCH_THEN(MP_TAC o SPEC `e / &(4 * SUC k)`) THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC;
    ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `M0:num` (MP_TAC o SPEC `M0:num`)) THEN
   REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `prob (p:A prob_space)
     ((NM:num->A->bool) M0 UNION
      {x:A | x IN prob_carrier p /\
        (?n. ergodic_maxsum (\x. abs((f:A->real) x - max (-- &M0) (min (&M0) (f x))) -
          inv(&(4 * SUC k))) tt n x > &0)})` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC PROB_MONO THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_INTERS; FORALL_IN_IMAGE; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `prob (p:A prob_space) ((NM:num->A->bool) M0) +
     prob p {x:A | x IN prob_carrier p /\
       (?n. ergodic_maxsum (\x. abs((f:A->real) x - max (-- &M0) (min (&M0) (f x))) -
         inv(&(4 * SUC k))) tt n x > &0)}` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC PROB_SUBADDITIVE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[null_event]; ALL_TAC] THEN
   SUBGOAL_THEN `prob (p:A prob_space) ((NM:num->A->bool) M0) = &0` SUBST1_TAC THENL
   [ASM_MESON_TAC[null_event]; ALL_TAC] THEN
   REWRITE_TAC[REAL_ADD_LID] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `&(4 * SUC k) * expectation (p:A prob_space) (\x. abs((f:A->real) x - max (-- &M0) (min (&M0) (f x))))` THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LT_IMP_LE THEN
   SUBGOAL_THEN `e = &(4 * SUC k) * (e / &(4 * SUC k))` SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_FIELD `~(c = &0) ==> e = c * (e / c)`) THEN
    REWRITE_TAC[REAL_OF_NUM_EQ] THEN ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LT_LMUL THEN
   CONJ_TAC THENL [REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= expectation (p:A prob_space) (\x. abs((f:A->real) x - max (-- &M0) (min (&M0) (f x))))` ASSUME_TAC THENL
   [MATCH_MP_TAC EXPECTATION_POS THEN CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_ABS THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ERGODIC_TRUNCATION_INTEGRABLE THEN
     ASM_REWRITE_TAC[];
     REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_POS]]; ALL_TAC] THEN
   UNDISCH_TAC `abs(expectation (p:A prob_space) (\x. abs((f:A->real) x - max (-- &M0) (min (&M0) (f x)))) - &0) < e / &(4 * SUC k)` THEN
   ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Provide the witness: countable union of null events *)
  EXISTS_TAC `UNIONS {INTERS (IMAGE (\M:num. (NM:num->A->bool) M UNION
    {x:A | x IN prob_carrier p /\
      (?n. ergodic_maxsum (\x. abs((f:A->real) x - max (-- &M) (min (&M) (f x))) -
        inv(&(4 * SUC k))) tt n x > &0)}) (:num)) | k IN (:num)}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC NULL_EVENT_COUNTABLE_UNION THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* SUBSET: non-convergent points are in the witness *)
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  MP_TAC(SPEC `\n:num. inv(&(SUC n)) * sum(0..n) (\j. (f:A->real)(ITER j tt x))`
    NOT_CONVERGENT_OSCILLATION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  EXISTS_TAC `k:num` THEN
  REWRITE_TAC[IN_INTERS; FORALL_IN_IMAGE; IN_UNIV] THEN
  X_GEN_TAC `M:num` THEN
  MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `M:num`; `SUC k`]
    BIRKHOFF_OSCILLATION_CONTAINMENT) THEN
  ASM_REWRITE_TAC[NOT_SUC] THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL
  [REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
   UNDISCH_TAC `!M:num. null_event (p:A prob_space) ((NM:num->A->bool) M) /\
     {x:A | x IN prob_carrier p /\
       ~(?L. ((\n. inv(&(SUC n)) * sum(0..n)
         (\k. max (-- &M) (min (&M) ((f:A->real) (ITER k tt x))))) ---> L) sequentially)} SUBSET NM M` THEN
   DISCH_THEN(MP_TAC o SPEC `M:num`) THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN DISJ2_TAC THEN
   ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]
  );;

(* The limit is T-invariant: if averages converge to L then they also
   converge to L when started from tt(x) *)
let BIRKHOFF_LIMIT_INVARIANT = prove
 (`!p:A prob_space tt f x L.
    measure_preserving p tt /\ integrable p f /\
    x IN prob_carrier p /\
    ((\n. inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x))) ---> L)
      sequentially
    ==> ((\n. inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt (tt x)))) ---> L)
          sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  UNDISCH_TAC `((\n. inv (&(SUC n)) * sum (0..n) (\k. (f:A->real) (ITER k tt x))) ---> L) sequentially` THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `e / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `&1`) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N3:num`) THEN
  ABBREV_TAC `C = abs(L) + abs((f:A->real) x) + &1` THEN
  SUBGOAL_THEN `&0 < C` ASSUME_TAC THENL
  [EXPAND_TAC "C" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `e / (&2 * C)` REAL_ARCH_INV) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `MAX N1 (MAX N2 N3)` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `N1 <= n /\ N2 <= n /\ N3 <= (n:num)` STRIP_ASSUME_TAC THENL
  [POP_ASSUM MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sum(0..n) (\k. (f:A->real)(ITER k tt (tt x))) =
    sum(0..SUC n) (\k. f(ITER k tt x)) - f x` SUBST1_TAC THENL
  [MP_TAC(SPECL [`f:A->real`; `tt:A->A`; `n:num`; `x:A`] ERGODIC_SUM_SHIFT) THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `a = inv(&(SUC(SUC n))) * sum(0..SUC n) (\k. (f:A->real)(ITER k tt x))` THEN
  SUBGOAL_THEN `abs(a - L) < e / &2` ASSUME_TAC THENL
  [EXPAND_TAC "a" THEN
   UNDISCH_TAC `!n. N1 <= n ==> abs(inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x)) - L) < e / &2` THEN
   DISCH_THEN(MP_TAC o SPEC `SUC n`) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(a - L) < &1` ASSUME_TAC THENL
  [EXPAND_TAC "a" THEN
   UNDISCH_TAC `!n. N3 <= n ==> abs(inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x)) - L) < &1` THEN
   DISCH_THEN(MP_TAC o SPEC `SUC n`) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(a - (f:A->real) x) < C` ASSUME_TAC THENL
  [UNDISCH_TAC `abs(a - L) < &1` THEN
   UNDISCH_TAC `abs L + abs((f:A->real) x) + &1 = C` THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv(&(SUC n)) < e / (&2 * C)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N2)` THEN
   ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
   REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
   UNDISCH_TAC `~(N2 = 0)` THEN UNDISCH_TAC `N2 <= (n:num)` THEN
   ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `~(&(SUC n) = &0)` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_OF_NUM_EQ; NOT_SUC]; ALL_TAC] THEN
  SUBGOAL_THEN `~(&(SUC(SUC n)) = &0)` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_OF_NUM_EQ; NOT_SUC]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(&(SUC n)) * (sum(0..SUC n) (\k. (f:A->real)(ITER k tt x)) - f x) - L =
    (a - L) + inv(&(SUC n)) * (a - f x)` SUBST1_TAC THENL
  [EXPAND_TAC "a" THEN
   ABBREV_TAC `S = sum(0..SUC n) (\k. (f:A->real)(ITER k tt x))` THEN
   MATCH_MP_TAC(REAL_FIELD
    `~(a = &0) /\ ~(b = &0) /\ b = a + &1
     ==> inv(a) * (S - fx) - L = (inv(b) * S - L) + inv(a) * (inv(b) * S - fx)`) THEN
   ASM_REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `abs(inv(&(SUC n)) * (a - (f:A->real) x)) < e / &2` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NUM] THEN
   SUBGOAL_THEN `e / &2 = e / (&2 * C) * C` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_INV_MUL; GSYM REAL_MUL_ASSOC] THEN
    SUBGOAL_THEN `inv(C) * C = &1` SUBST1_TAC THENL
    [MATCH_MP_TAC REAL_MUL_LINV THEN
     UNDISCH_TAC `&0 < C` THEN REAL_ARITH_TAC;
     REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LT_MUL2 THEN
    REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS; REAL_ABS_POS] THEN
    UNDISCH_TAC `inv(&(SUC n)) < e / (&2 * C)` THEN
    UNDISCH_TAC `abs(a - (f:A->real) x) < C` THEN
    REAL_ARITH_TAC];
   ALL_TAC] THEN
  UNDISCH_TAC `abs(a - L) < e / &2` THEN
  UNDISCH_TAC `abs(inv(&(SUC n)) * (a - (f:A->real) x)) < e / &2` THEN
  REAL_ARITH_TAC);;

(* Under ergodicity: prob({limsup > c}) = 0 for c > E[f] (bounded case) *)
let ERGODIC_LIMSUP_NULL = prove
 (`!p:A prob_space tt f C c.
    ergodic p tt /\ integrable p f /\
    (!x. x IN prob_carrier p ==> abs(f x) <= C) /\
    c > expectation p f
    ==> prob p {x | x IN prob_carrier p /\
      real_limsup (\n. inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x))) > c} = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `measure_preserving (p:A prob_space) (tt:A->A)` ASSUME_TAC THENL
  [UNDISCH_TAC `ergodic (p:A prob_space) (tt:A->A)` THEN
   REWRITE_TAC[ergodic] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C` ASSUME_TAC THENL
  [MP_TAC(SPEC `p:A prob_space` PROB_CARRIER_NONEMPTY) THEN
   REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
   DISCH_THEN(X_CHOOSE_TAC `z:A`) THEN
   SUBGOAL_THEN `abs((f:A->real) z) <= C` MP_TAC THENL
   [ASM_SIMP_TAC[]; REAL_ARITH_TAC]; ALL_TAC] THEN
  ABBREV_TAC `A = {x:A | x IN prob_carrier p /\
    real_limsup (\n. inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x))) > c}` THEN
  (* A is in prob_events *)
  SUBGOAL_THEN `(A:A->bool) IN prob_events p` ASSUME_TAC THENL
  [EXPAND_TAC "A" THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
     real_limsup (\n. inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x))) > c} =
     prob_carrier p DIFF {x | x IN prob_carrier p /\
       real_limsup (\n. inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x))) <= c}`
     (fun th -> REWRITE_TAC[th]) THENL
   [SET_TAC[real_gt; REAL_NOT_LE]; ALL_TAC] THEN
   MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] SIGMA_ALGEBRA_DIFF) THEN
   CONJ_TAC THENL [REWRITE_TAC[PROB_SPACE_SIGMA_ALGEBRA]; ALL_TAC] THEN
   CONJ_TAC THENL [REWRITE_TAC[PROB_CARRIER_IN_EVENTS]; ALL_TAC] THEN
   MATCH_MP_TAC RV_LE_EVENT THEN
   MP_TAC(CONV_RULE(DEPTH_CONV BETA_CONV) (ISPECL [`p:A prob_space`;
     `\n (x:A). inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x))`;
     `\x:A. C:real`] RANDOM_VARIABLE_REAL_LIMSUP_DOMINATED)) THEN
   DISCH_THEN MATCH_MP_TAC THEN
   CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
    MATCH_MP_TAC ERGODIC_AVG_INTEGRABLE THEN ASM_REWRITE_TAC[];
    CONJ_TAC THENL
    [REWRITE_TAC[RANDOM_VARIABLE_CONST];
     REPEAT STRIP_TAC THEN
     MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`;
       `n:num`; `x:A`] ERGODIC_AVG_BOUNDED) THEN
     ASM_REWRITE_TAC[]]]; ALL_TAC] THEN
  (* A is T-invariant *)
  SUBGOAL_THEN `invariant_event (p:A prob_space) (tt:A->A) (A:A->bool)` ASSUME_TAC THENL
  [EXPAND_TAC "A" THEN REWRITE_TAC[invariant_event] THEN
   CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`]
      ERGODIC_LIMSUP_SHIFT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [ASM_MESON_TAC[MEASURE_PRESERVING_CARRIER]; ALL_TAC] THEN
    MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`]
      ERGODIC_LIMSUP_SHIFT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  (* By ergodicity: prob A = 0 or 1 *)
  SUBGOAL_THEN `prob (p:A prob_space) A = &0 \/ prob p A = &1` ASSUME_TAC THENL
  [UNDISCH_TAC `ergodic (p:A prob_space) (tt:A->A)` THEN REWRITE_TAC[ergodic] THEN
   STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Show prob A = 1 leads to contradiction via MEL *)
  FIRST_X_ASSUM DISJ_CASES_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* MEL gives E[(f-c)*1_A] >= 0 *)
  SUBGOAL_THEN `&0 <= expectation (p:A prob_space) (\x. ((f:A->real) x - c) * indicator_fn A x)`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`;
     `\x:A. (f:A->real) x - c`; `A:A->bool`] MEL_INVARIANT_SET) THEN
   ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC] THEN
    X_GEN_TAC `x:A` THEN EXPAND_TAC "A" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN
    MP_TAC(SPECL [`\n. inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x))`;
      `c:real`; `--C:real`; `C:real`] REAL_LIMSUP_GT_EXISTS_BOUNDED) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN GEN_TAC THEN
     MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`;
       `n:num`; `x:A`] ERGODIC_AVG_BOUNDED) THEN ASM_REWRITE_TAC[] THEN
     REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN EXISTS_TAC `m:num` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC AVG_GT_IMP_SUM_POS THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[BETA_RULE th]);
    REWRITE_TAC[]]; ALL_TAC] THEN
  (* E[(f-c)*1_A] = E[f] - c when prob A = 1 *)
  (* Split: E[(f-c)*1_A] = E[(f-c)*1_carrier] - E[(f-c)*1_{carrier\A}] *)
  (* The latter is 0 since prob(carrier\A) = 0 and f-c is bounded *)
  SUBGOAL_THEN `prob (p:A prob_space) (prob_carrier p DIFF A) = &0` ASSUME_TAC THENL
  [MP_TAC(SPECL [`p:A prob_space`; `A:A->bool`] PROB_COMPL) THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `prob_carrier (p:A prob_space) DIFF A IN prob_events p` ASSUME_TAC THENL
  [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] SIGMA_ALGEBRA_DIFF) THEN
   REWRITE_TAC[PROB_SPACE_SIGMA_ALGEBRA; PROB_CARRIER_IN_EVENTS] THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* E[(f-c)*1_A] + E[(f-c)*1_{carrier\A}] = E[f-c] = E[f] - c *)
  SUBGOAL_THEN `expectation (p:A prob_space) (\x. ((f:A->real) x - c) * indicator_fn A x) +
    expectation p (\x. (f x - c) * indicator_fn (prob_carrier p DIFF A) x) =
    expectation p f - c` ASSUME_TAC THENL
  [SUBGOAL_THEN `expectation (p:A prob_space) (\x. ((f:A->real) x - c) * indicator_fn (A:A->bool) x) +
    expectation p (\x. (f x - c) * indicator_fn (prob_carrier p DIFF A) x) =
    expectation p (\x. (f x - c) * indicator_fn A x + (f x - c) * indicator_fn (prob_carrier p DIFF A) x)`
    SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXPECTATION_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC] THEN
   SUBGOAL_THEN `(\x:A. ((f:A->real) x - c) * indicator_fn (A:A->bool) x +
     (f x - c) * indicator_fn (prob_carrier p DIFF A) x) =
     (\x. (f x - c) * indicator_fn (prob_carrier p) x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; indicator_fn; IN_DIFF] THEN X_GEN_TAC `y:A` THEN
    SUBGOAL_THEN `(A:A->bool) SUBSET prob_carrier p` ASSUME_TAC THENL
    [EXPAND_TAC "A" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
     GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `(y:A) IN A` THEN ASM_CASES_TAC `(y:A) IN prob_carrier p` THEN
    ASM_REWRITE_TAC[] THEN
    TRY(UNDISCH_TAC `(A:A->bool) SUBSET prob_carrier p` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `y:A`) THEN
        ASM_REWRITE_TAC[]) THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(CONV_RULE(DEPTH_CONV BETA_CONV)
     (SPECL [`p:A prob_space`; `\x:A. (f:A->real) x - c`]
       EXPECTATION_CARRIER_INDICATOR)) THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC(CONV_RULE(DEPTH_CONV BETA_CONV)
     (SPECL [`p:A prob_space`; `f:A->real`; `\x:A. c:real`] EXPECTATION_SUB)) THEN
   ASM_REWRITE_TAC[INTEGRABLE_CONST] THEN DISCH_THEN SUBST1_TAC THEN
   MP_TAC(SPECL [`p:A prob_space`; `c:real`] EXPECTATION_CONST) THEN
   DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* E[(f-c)*1_{carrier\A}] has absolute value bounded by (C+|c|)*prob(carrier\A) = 0 *)
  SUBGOAL_THEN `abs(expectation (p:A prob_space) (\x. ((f:A->real) x - c) *
    indicator_fn (prob_carrier p DIFF A) x)) <= (C + abs c) * prob p (prob_carrier p DIFF A)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `expectation (p:A prob_space)
     (\x. abs(((f:A->real) x - c) * indicator_fn (prob_carrier p DIFF A) x))` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC EXPECTATION_ABS_BOUND THEN
    MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `expectation (p:A prob_space)
     (\x:A. (C + abs c) * indicator_fn (prob_carrier p DIFF A) x)` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC EXPECTATION_MONO THEN CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_ABS THEN
     MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_CMUL THEN REWRITE_TAC[ETA_AX] THEN
     MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN BETA_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL; indicator_fn] THEN COND_CASES_TAC THENL
    [REWRITE_TAC[REAL_ABS_NUM; REAL_MUL_RID] THEN
     MATCH_MP_TAC(REAL_ARITH `abs(f) <= C ==> abs(f - c) <= C + abs c`) THEN
     ASM_SIMP_TAC[];
     REWRITE_TAC[REAL_ABS_NUM; REAL_MUL_RZERO; REAL_LE_REFL]];
    MP_TAC(SPECL [`p:A prob_space`; `C + abs c`;
      `indicator_fn (prob_carrier (p:A prob_space) DIFF A)`] EXPECTATION_CMUL) THEN
    ANTS_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPECL [`p:A prob_space`; `prob_carrier (p:A prob_space) DIFF A`]
      EXPECTATION_INDICATOR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_LE_REFL]]; ALL_TAC] THEN
  (* Derive contradiction: E[f] - c >= 0 but c > E[f] *)
  SUBGOAL_THEN `expectation (p:A prob_space) (\x. ((f:A->real) x - c) * indicator_fn (prob_carrier p DIFF A) x) = &0` ASSUME_TAC THENL
  [MATCH_MP_TAC(REAL_ARITH `abs x <= &0 ==> x = &0`) THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `(C + abs c) * prob (p:A prob_space) (prob_carrier p DIFF A)` THEN
   ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (\x. ((f:A->real) x - c) * indicator_fn A x) = expectation p f - c` ASSUME_TAC THENL
  [UNDISCH_TAC `expectation (p:A prob_space) (\x. ((f:A->real) x - c) * indicator_fn A x) +
    expectation p (\x. (f x - c) * indicator_fn (prob_carrier p DIFF A) x) =
    expectation p f - c` THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&0 <= expectation (p:A prob_space) (\x. ((f:A->real) x - c) * indicator_fn A x)` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `c > expectation (p:A prob_space) (f:A->real)` THEN
  REAL_ARITH_TAC);;


(* real_limsup of negation = negation of real_liminf (bounded case) *)
let REAL_LIMSUP_NEG = prove
 (`!(f:num->real) C. (!n. abs(f n) <= C)
   ==> real_limsup (\n. --(f n)) = --(real_liminf f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_limsup; real_liminf] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  SUBGOAL_THEN
    `!m:num. sup {--((f:num->real) k) | k >= m} = --(inf {f k | k >= m})`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC SUP_UNIQUE THEN X_GEN_TAC `c:real` THEN
   EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `--c <= inf {(f:num->real) k | k >= m}` MP_TAC THENL
    [MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `(f:num->real) m` THEN EXISTS_TAC `m:num` THEN
      REWRITE_TAC[GE; LE_REFL]; ALL_TAC] THEN
     REWRITE_TAC[IN_ELIM_THM; GE] THEN
     X_GEN_TAC `y:real` THEN
     DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
     ASM_REWRITE_TAC[] THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `--((f:num->real) j)`) THEN
     ANTS_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM; GE] THEN EXISTS_TAC `j:num` THEN
      ASM_REWRITE_TAC[]; REAL_ARITH_TAC]; ALL_TAC] THEN
    MESON_TAC[REAL_ARITH `!a c. --c <= a ==> --a <= c`];
    DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM; GE] THEN
    X_GEN_TAC `y:real` THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `inf {(f:num->real) k | k >= m} <= f j` MP_TAC THENL
    [MATCH_MP_TAC INF_LE_ELEMENT THEN CONJ_TAC THENL
     [EXISTS_TAC `--C:real` THEN REWRITE_TAC[IN_ELIM_THM; GE] THEN
      X_GEN_TAC `z:real` THEN
      DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN REAL_ARITH_TAC;
      REWRITE_TAC[IN_ELIM_THM; GE] THEN EXISTS_TAC `j:num` THEN
      ASM_REWRITE_TAC[]]; ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `--inf {(f:num->real) k | k >= m}` THEN
    ASM_REWRITE_TAC[REAL_LE_NEG2]]; ALL_TAC] THEN
  SUBGOAL_THEN
    `{sup {--((f:num->real) k) | k >= n} | n IN (:num)} =
     {--(inf {f k | k >= n}) | n IN (:num)}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIV] THEN GEN_TAC THEN
   EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
   EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MATCH_MP_TAC INF_UNIQUE THEN X_GEN_TAC `c:real` THEN EQ_TAC THENL
  [REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN DISCH_TAC THEN
   ONCE_REWRITE_TAC[REAL_ARITH `c <= --a <=> a <= --c`] THEN
   MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; IN_UNIV] THEN
    EXISTS_TAC `inf {(f:num->real) k | k >= 0}` THEN
    EXISTS_TAC `0` THEN REFL_TAC; ALL_TAC] THEN
   REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
   X_GEN_TAC `y:real` THEN
   DISCH_THEN(X_CHOOSE_THEN `p:num` SUBST1_TAC) THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `--(inf {(f:num->real) k | k >= p})`) THEN
   ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN EXISTS_TAC `p:num` THEN
    REFL_TAC;
    MESON_TAC[REAL_ARITH `!a c. c <= --a ==> a <= --c`]];
   DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
   X_GEN_TAC `y:real` THEN
   DISCH_THEN(X_CHOOSE_THEN `p:num` SUBST1_TAC) THEN
   SUBGOAL_THEN `inf {(f:num->real) k | k >= p} <=
     sup {inf {f k | k >= n} | n IN (:num)}` MP_TAC THENL
   [MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
    [EXISTS_TAC `C:real` THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
     X_GEN_TAC `z:real` THEN
     DISCH_THEN(X_CHOOSE_THEN `q:num` SUBST1_TAC) THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(f:num->real) q` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC INF_LE_ELEMENT THEN CONJ_TAC THENL
      [EXISTS_TAC `--C:real` THEN REWRITE_TAC[IN_ELIM_THM; GE] THEN
       X_GEN_TAC `w:real` THEN
       DISCH_THEN(X_CHOOSE_THEN `r:num` STRIP_ASSUME_TAC) THEN
       ASM_REWRITE_TAC[] THEN
       MP_TAC(SPEC `r:num` (ASSUME `!n. abs((f:num->real) n) <= C`)) THEN
       REAL_ARITH_TAC;
       REWRITE_TAC[IN_ELIM_THM; GE] THEN EXISTS_TAC `q:num` THEN
       REWRITE_TAC[LE_REFL]];
      MP_TAC(SPEC `q:num` (ASSUME `!n. abs((f:num->real) n) <= C`)) THEN
      REAL_ARITH_TAC];
     REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN EXISTS_TAC `p:num` THEN
     REFL_TAC]; ALL_TAC] THEN
   DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `--sup {inf {(f:num->real) k | k >= n} | n IN (:num)}` THEN
   ASM_REWRITE_TAC[REAL_LE_NEG2]]);;

(* Under ergodicity: prob({liminf < c}) = 0 for c < E[f] (bounded case) *)
let ERGODIC_LIMINF_NULL = prove
 (`!p:A prob_space tt f C c.
    ergodic p tt /\ integrable p f /\
    (!x. x IN prob_carrier p ==> abs(f x) <= C) /\
    c < expectation p f
    ==> prob p {x | x IN prob_carrier p /\
      real_liminf (\n. inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x))) < c} = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `prob (p:A prob_space) {x | x IN prob_carrier p /\
    real_limsup (\n. inv(&(SUC n)) * sum(0..n) (\k. --((f:A->real)(ITER k tt x)))) > --c} = &0`
    MP_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `\x:A. --((f:A->real) x)`;
     `C:real`; `--c:real`] ERGODIC_LIMSUP_NULL) THEN
   REWRITE_TAC[REAL_ABS_NEG] THEN DISCH_THEN MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_NEG THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[real_gt] THEN
    SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. --((f:A->real) x)) =
      --(expectation p f)` SUBST1_TAC THENL
    [MATCH_MP_TAC EXPECTATION_NEG THEN
     MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
     ASM_REAL_ARITH_TAC]];
   ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> a = &0 ==> b = &0`) THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `x:A` THEN
  ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\n. inv(&(SUC n)) * sum(0..n) (\k. --((f:A->real)(ITER k tt x)))) =
    (\n. --(inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x))))`
    (fun th -> REWRITE_TAC[th]) THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
   REWRITE_TAC[GSYM REAL_MUL_RNEG; GSYM SUM_NEG; REAL_NEG_NEG]; ALL_TAC] THEN
  SUBGOAL_THEN `real_limsup (\n. --(inv(&(SUC n)) * sum(0..n)
    (\k. (f:A->real)(ITER k tt x)))) =
    --(real_liminf (\n. inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x))))`
    (fun th -> REWRITE_TAC[th]) THENL
  [MP_TAC(ISPECL [`\n:num. inv(&(SUC n)) * sum(0..n)
      (\k. (f:A->real)(ITER k tt x))`; `C:real`] REAL_LIMSUP_NEG) THEN
   REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
   X_GEN_TAC `nn:num` THEN
   MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`;
     `nn:num`; `x:A`] ERGODIC_AVG_BOUNDED) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [UNDISCH_TAC `ergodic (p:A prob_space) (tt:A->A)` THEN
     REWRITE_TAC[ergodic] THEN MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    SIMP_TAC[]]; ALL_TAC] THEN
  REWRITE_TAC[real_gt; REAL_LT_NEG2]);;

(* The bounded ergodic case: averages converge to E[f] a.s. *)
let BIRKHOFF_ERGODIC_BOUNDED = prove
 (`!p:A prob_space tt f C.
    ergodic p tt /\ integrable p f /\
    (!x. x IN prob_carrier p ==> abs(f x) <= C)
    ==> almost_surely p
          {x | ((\n. inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x)))
                ---> expectation p f) sequentially}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `measure_preserving (p:A prob_space) (tt:A->A)` ASSUME_TAC THENL
  [UNDISCH_TAC `ergodic (p:A prob_space) (tt:A->A)` THEN
   REWRITE_TAC[ergodic] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C` ASSUME_TAC THENL
  [MP_TAC(SPEC `p:A prob_space` PROB_CARRIER_NONEMPTY) THEN
   REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
   DISCH_THEN(X_CHOOSE_TAC `z:A`) THEN
   SUBGOAL_THEN `abs((f:A->real) z) <= C` MP_TAC THENL
   [ASM_SIMP_TAC[]; REAL_ARITH_TAC]; ALL_TAC] THEN
  ABBREV_TAC `E = expectation (p:A prob_space) (f:A->real)` THEN
  (* Limsup of averages is a random variable *)
  SUBGOAL_THEN `random_variable (p:A prob_space)
    (\x. real_limsup (\m. inv(&(SUC m)) * sum(0..m) (\k. (f:A->real)(ITER k tt x))))`
    ASSUME_TAC THENL
  [MP_TAC(CONV_RULE(DEPTH_CONV BETA_CONV) (ISPECL [`p:A prob_space`;
     `\n (x:A). inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x))`;
     `\x:A. C:real`] RANDOM_VARIABLE_REAL_LIMSUP_DOMINATED)) THEN
   DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
    MATCH_MP_TAC ERGODIC_AVG_INTEGRABLE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[RANDOM_VARIABLE_CONST];
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`;
                   `m:num`; `x:A`] ERGODIC_AVG_BOUNDED) THEN
    ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  (* Limsup > c sets are in prob_events for any c *)
  SUBGOAL_THEN `!c. {x:A | x IN prob_carrier p /\
    real_limsup (\m. inv(&(SUC m)) * sum(0..m) (\k. (f:A->real)(ITER k tt x))) > c}
    IN prob_events p` ASSUME_TAC THENL
  [GEN_TAC THEN REWRITE_TAC[real_gt] THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
     c < real_limsup (\m. inv(&(SUC m)) * sum(0..m) (\k. (f:A->real)(ITER k tt x)))} =
     prob_carrier p DIFF {x | x IN prob_carrier p /\
       real_limsup (\m. inv(&(SUC m)) * sum(0..m) (\k. f(ITER k tt x))) <= c}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN
    MESON_TAC[REAL_NOT_LE]; ALL_TAC] THEN
   REWRITE_TAC[prob_carrier] THEN
   MATCH_MP_TAC SIGMA_ALGEBRA_COMPL THEN REWRITE_TAC[PROB_SPACE_SIGMA_ALGEBRA] THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `\x:A. real_limsup (\m. inv(&(SUC m)) * sum(0..m) (\k. (f:A->real)(ITER k tt x)))`;
     `c:real`] RV_LE_EVENT) THEN
   ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM prob_carrier]; ALL_TAC] THEN
  (* Liminf < c sets are in prob_events for any c *)
  SUBGOAL_THEN `!c. {x:A | x IN prob_carrier p /\
    real_liminf (\m. inv(&(SUC m)) * sum(0..m) (\k. (f:A->real)(ITER k tt x))) < c}
    IN prob_events p` ASSUME_TAC THENL
  [GEN_TAC THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
     real_liminf (\m. inv(&(SUC m)) * sum(0..m) (\k. (f:A->real)(ITER k tt x))) < c} =
     {x | x IN prob_carrier p /\
       real_limsup (\m. --(inv(&(SUC m)) * sum(0..m) (\k. (f:A->real)(ITER k tt x)))) > --c}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
    ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `real_liminf (\m. inv(&(SUC m)) * sum(0..m)
      (\k. (f:A->real)(ITER k tt x))) =
      --(real_limsup (\m. --(inv(&(SUC m)) * sum(0..m)
        (\k. f(ITER k tt x)))))` SUBST1_TAC THENL
    [MP_TAC(SPECL [`\m:num. inv(&(SUC m)) * sum(0..m)
       (\k. (f:A->real)(ITER k tt x))`; `C:real`] REAL_LIMSUP_NEG) THEN
     ANTS_TAC THENL
     [GEN_TAC THEN MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`;
        `C:real`; `n:num`; `x:A`] ERGODIC_AVG_BOUNDED) THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     MESON_TAC[REAL_NEG_NEG]; ALL_TAC] THEN
    REWRITE_TAC[real_gt] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[real_gt] THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
     --c < real_limsup (\m. --(inv(&(SUC m)) * sum(0..m)
       (\k. (f:A->real)(ITER k tt x))))} =
     prob_carrier p DIFF {x | x IN prob_carrier p /\
       real_limsup (\m. --(inv(&(SUC m)) * sum(0..m)
         (\k. (f:A->real)(ITER k tt x)))) <= --c}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN
    MESON_TAC[REAL_NOT_LE]; ALL_TAC] THEN
   REWRITE_TAC[prob_carrier] THEN
   MATCH_MP_TAC SIGMA_ALGEBRA_COMPL THEN REWRITE_TAC[PROB_SPACE_SIGMA_ALGEBRA] THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `\x:A. real_limsup (\m. --(inv(&(SUC m)) * sum(0..m)
       (\k. (f:A->real)(ITER k tt x))))`;
     `--c:real`] RV_LE_EVENT) THEN
   ANTS_TAC THENL
   [MP_TAC(CONV_RULE(DEPTH_CONV BETA_CONV) (ISPECL [`p:A prob_space`;
      `\n (x:A). --(inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x)))`;
      `\x:A. C:real`] RANDOM_VARIABLE_REAL_LIMSUP_DOMINATED)) THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_NEG THEN
     MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
     MATCH_MP_TAC ERGODIC_AVG_INTEGRABLE THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[RANDOM_VARIABLE_CONST];
     REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_NEG] THEN
     MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `C:real`;
                    `m:num`; `x:A`] ERGODIC_AVG_BOUNDED) THEN
     ASM_REWRITE_TAC[]]; ALL_TAC] THEN
   REWRITE_TAC[GSYM prob_carrier]; ALL_TAC] THEN
  (* Null events for limsup > E + inv(SUC n) *)
  SUBGOAL_THEN `!n. null_event (p:A prob_space) {x | x IN prob_carrier p /\
    real_limsup (\m. inv(&(SUC m)) * sum(0..m) (\k. (f:A->real)(ITER k tt x))) >
      E + inv(&(SUC n))}` ASSUME_TAC THENL
  [GEN_TAC THEN REWRITE_TAC[null_event] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   EXPAND_TAC "E" THEN MATCH_MP_TAC ERGODIC_LIMSUP_NULL THEN
   EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[real_gt] THEN
   MATCH_MP_TAC(REAL_ARITH `&0 < i ==> e < e + i`) THEN
   REWRITE_TAC[REAL_LT_INV_EQ; REAL_OF_NUM_LT; LT_0]; ALL_TAC] THEN
  (* Null events for liminf < E - inv(SUC n) *)
  SUBGOAL_THEN `!n. null_event (p:A prob_space) {x | x IN prob_carrier p /\
    real_liminf (\m. inv(&(SUC m)) * sum(0..m) (\k. (f:A->real)(ITER k tt x))) <
      E - inv(&(SUC n))}` ASSUME_TAC THENL
  [GEN_TAC THEN REWRITE_TAC[null_event] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   EXPAND_TAC "E" THEN MATCH_MP_TAC ERGODIC_LIMINF_NULL THEN
   EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC(REAL_ARITH `&0 < i ==> e - i < e`) THEN
   REWRITE_TAC[REAL_LT_INV_EQ; REAL_OF_NUM_LT; LT_0]; ALL_TAC] THEN
  (* Construct the null set *)
  REWRITE_TAC[almost_surely] THEN
  EXISTS_TAC `UNIONS {(\n. {x:A | x IN prob_carrier p /\
    real_limsup (\m. inv(&(SUC m)) * sum(0..m) (\k. (f:A->real)(ITER k tt x))) >
      E + inv(&(SUC n))}) n | n IN (:num)}
    UNION
    UNIONS {(\n. {x:A | x IN prob_carrier p /\
    real_liminf (\m. inv(&(SUC m)) * sum(0..m) (\k. (f:A->real)(ITER k tt x))) <
      E - inv(&(SUC n))}) n | n IN (:num)}` THEN
  CONJ_TAC THENL
  [(* null_event of the union *)
   MATCH_MP_TAC NULL_EVENT_UNION THEN CONJ_TAC THEN
   MATCH_MP_TAC NULL_EVENT_COUNTABLE_UNION THEN
   GEN_TAC THEN REWRITE_TAC[BETA_THM] THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Subset: non-convergence implies membership *)
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION; IN_UNIONS; IN_UNIV] THEN
  X_GEN_TAC `x:A` THEN
  REWRITE_TAC[NOT_EXISTS_THM; DE_MORGAN_THM] THEN
  STRIP_TAC THEN
  (* Averages are bounded *)
  SUBGOAL_THEN `!m. abs(inv(&(SUC m)) * sum(0..m)
    (\k. (f:A->real)(ITER k tt x))) <= C` ASSUME_TAC THENL
  [GEN_TAC THEN MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`;
     `C:real`; `m:num`; `x:A`] ERGODIC_AVG_BOUNDED) THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `s = (\m. inv(&(SUC m)) * sum(0..m)
    (\k. (f:A->real)(ITER k tt x)))` THEN
  (* If limsup <= E and liminf >= E then convergence to E *)
  SUBGOAL_THEN `real_limsup s > E \/ real_liminf (s:num->real) < E`
    ASSUME_TAC THENL
  [MATCH_MP_TAC(TAUT `(~a /\ ~b ==> F) ==> a \/ b`) THEN
   REWRITE_TAC[real_gt; REAL_NOT_LT] THEN STRIP_TAC THEN
   SUBGOAL_THEN `real_limsup s = real_liminf (s:num->real)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
    [UNDISCH_TAC `real_limsup (s:num->real) <= E` THEN
     UNDISCH_TAC `E <= real_liminf (s:num->real)` THEN REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_LIMINF_LE_LIMSUP_ABS THEN
     EXISTS_TAC `C:real` THEN
     EXPAND_TAC "s" THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
   SUBGOAL_THEN `real_limsup (s:num->real) = E` ASSUME_TAC THENL
   [UNDISCH_TAC `real_limsup (s:num->real) <= E` THEN
    UNDISCH_TAC `E <= real_liminf (s:num->real)` THEN
    UNDISCH_TAC `real_limsup s = real_liminf (s:num->real)` THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`s:num->real`; `C:real`] BOUNDED_LIMSUP_LIMINF_CONVERGE) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [EXPAND_TAC "s" THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[]]; ALL_TAC] THEN
   UNDISCH_TAC `real_limsup (s:num->real) = E` THEN
   DISCH_THEN SUBST1_TAC THEN
   UNDISCH_TAC `~((s:num->real) ---> E) sequentially` THEN
   REWRITE_TAC[]; ALL_TAC] THEN
  (* Use archimedean property to find the witnessing n *)
  FIRST_X_ASSUM DISJ_CASES_TAC THENL
  [DISJ1_TAC THEN
   UNDISCH_TAC `real_limsup (s:num->real) > E` THEN
   REWRITE_TAC[real_gt] THEN DISCH_TAC THEN
   MP_TAC(SPEC `real_limsup s - E:real` REAL_ARCH_INV) THEN
   DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
   ANTS_TAC THENL
   [UNDISCH_TAC `E < real_limsup (s:num->real)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `{x:A | x IN prob_carrier p /\
     real_limsup (\m. inv(&(SUC m)) * sum(0..m) (\k. (f:A->real)(ITER k tt x))) >
       E + inv(&(SUC k))}` THEN
   CONJ_TAC THENL
   [EXISTS_TAC `k:num` THEN REWRITE_TAC[BETA_THM; real_gt]; ALL_TAC] THEN
   REWRITE_TAC[IN_ELIM_THM; real_gt] THEN
   CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `inv(&(SUC k)) <= inv(&k:real)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
   UNDISCH_TAC `inv(&k) < real_limsup (s:num->real) - E` THEN
   EXPAND_TAC "s" THEN REAL_ARITH_TAC;
   DISJ2_TAC THEN
   UNDISCH_TAC `real_liminf (s:num->real) < E` THEN DISCH_TAC THEN
   MP_TAC(SPEC `E - real_liminf (s:num->real)` REAL_ARCH_INV) THEN
   DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
   ANTS_TAC THENL
   [UNDISCH_TAC `real_liminf (s:num->real) < E` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `{x:A | x IN prob_carrier p /\
     real_liminf (\m. inv(&(SUC m)) * sum(0..m) (\k. (f:A->real)(ITER k tt x))) <
       E - inv(&(SUC k))}` THEN
   CONJ_TAC THENL
   [EXISTS_TAC `k:num` THEN REWRITE_TAC[BETA_THM]; ALL_TAC] THEN
   REWRITE_TAC[IN_ELIM_THM] THEN
   CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `inv(&(SUC k)) <= inv(&k:real)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
   UNDISCH_TAC `inv(&k) < E - real_liminf (s:num->real)` THEN
   EXPAND_TAC "s" THEN REAL_ARITH_TAC]);;

(* The ergodic case: if tt is ergodic, the limit is E[f] a.s.
   Proof: combine BIRKHOFF_ERGODIC_THEOREM (convergence), BIRKHOFF_ERGODIC_BOUNDED
   (bounded limit identification), and WIENER_MAXIMAL_INEQUALITY (error control). *)
let BIRKHOFF_ERGODIC = prove
 (`!p:A prob_space tt f.
    ergodic p tt /\ integrable p f
    ==> almost_surely p
          {x | ((\n. inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x)))
                ---> expectation p f) sequentially}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `measure_preserving (p:A prob_space) (tt:A->A)` ASSUME_TAC THENL
  [UNDISCH_TAC `ergodic (p:A prob_space) (tt:A->A)` THEN
   REWRITE_TAC[ergodic] THEN MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[almost_surely] THEN
  (* Step 1: Get null event from BIRKHOFF_ERGODIC_THEOREM *)
  MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`]
    BIRKHOFF_ERGODIC_THEOREM) THEN
  ASM_REWRITE_TAC[almost_surely] THEN
  DISCH_THEN(X_CHOOSE_THEN `N_f:A->bool` STRIP_ASSUME_TAC) THEN
  (* Step 2: Get null events from BIRKHOFF_ERGODIC_BOUNDED for each M *)
  SUBGOAL_THEN `!M:num. ?NM:A->bool. null_event (p:A prob_space) NM /\
    {x:A | x IN prob_carrier p /\
      ~(((\n. inv(&(SUC n)) * sum(0..n)
        (\k. max (-- &M) (min (&M) ((f:A->real)(ITER k tt x))))) --->
        expectation p (\y. max (-- &M) (min (&M) (f y)))) sequentially)}
    SUBSET NM` ASSUME_TAC THENL
  [GEN_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`;
     `\x:A. max (-- &M) (min (&M) ((f:A->real) x))`; `&M:real`]
     BIRKHOFF_ERGODIC_BOUNDED) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [MATCH_MP_TAC ERGODIC_TRUNCATION_INTEGRABLE THEN ASM_REWRITE_TAC[];
     REPEAT STRIP_TAC THEN REAL_ARITH_TAC];
    REWRITE_TAC[almost_surely] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `N:A->bool` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
   ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_TAC `NM:num->A->bool`) THEN
  (* Step 3: Wiener bound on events *)
  SUBGOAL_THEN `!M:num k:num. prob (p:A prob_space)
    {x:A | x IN prob_carrier p /\
      (?n. ergodic_maxsum (\x. abs((f:A->real) x - max (-- &M) (min (&M) (f x))) -
        inv(&(SUC k))) tt n x > &0)}
    <= &(SUC k) * expectation p (\x. abs(f x - max (-- &M) (min (&M) (f x))))`
    ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`;
     `\x:A. abs((f:A->real) x - max (-- &M) (min (&M) (f x)))`;
     `inv(&(SUC k))`] WIENER_MAXIMAL_INEQUALITY) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_ABS THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ERGODIC_TRUNCATION_INTEGRABLE THEN
     ASM_REWRITE_TAC[];
     REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_POS];
     REWRITE_TAC[REAL_LT_INV_EQ; REAL_OF_NUM_LT; LT_0]];
    REWRITE_TAC[REAL_INV_INV]];
   ALL_TAC] THEN
  (* Step 4: Events membership for Wiener sets *)
  SUBGOAL_THEN `!M:num k:num.
    {x:A | x IN prob_carrier p /\
      (?n. ergodic_maxsum (\x. abs((f:A->real) x - max (-- &M) (min (&M) (f x))) -
        inv(&(SUC k))) tt n x > &0)} IN prob_events (p:A prob_space)`
    ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
     (?n:num. ergodic_maxsum (\x. abs((f:A->real) x - max (-- &M) (min (&M) (f x))) -
       inv(&(SUC k))) tt n x > &0)} =
     UNIONS (IMAGE (\n:num. {x:A | x IN prob_carrier p /\
       ergodic_maxsum (\x. abs(f x - max (-- &M) (min (&M) (f x))) -
         inv(&(SUC k))) tt n x > &0}) (:num))` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIONS; EXISTS_IN_IMAGE; IN_UNIV] THEN
    MESON_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC PROB_COUNTABLE_UNION_IN_EVENTS THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `nn:num` THEN
    MATCH_MP_TAC ERGODIC_MAXSUM_POS_EVENT THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC INTEGRABLE_SUB THEN REWRITE_TAC[INTEGRABLE_CONST] THEN
    MATCH_MP_TAC INTEGRABLE_ABS THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ERGODIC_TRUNCATION_INTEGRABLE THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[NUM_COUNTABLE]];
   ALL_TAC] THEN
  (* Step 5: Events membership for NM(M) UNION W(M,k) *)
  SUBGOAL_THEN `!M:num k:num. (NM:num->A->bool) M UNION
    {x:A | x IN prob_carrier p /\
      (?n. ergodic_maxsum (\x. abs((f:A->real) x - max (-- &M) (min (&M) (f x))) -
        inv(&(SUC k))) tt n x > &0)} IN prob_events (p:A prob_space)`
    ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN MATCH_MP_TAC PROB_UNION_IN_EVENTS THEN
   ASM_REWRITE_TAC[] THEN
   FIRST_ASSUM(MP_TAC o CONJUNCT1 o SPEC `M:num`) THEN
   REWRITE_TAC[null_event] THEN MESON_TAC[];
   ALL_TAC] THEN
  (* Step 6: E[|f - f_M|] --> 0 *)
  MP_TAC(ISPECL [`p:A prob_space`; `f:A->real`] ERGODIC_TRUNCATION_L1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* Step 7: Extract M0(k) from convergence *)
  SUBGOAL_THEN `!k:num. ?N0:num. !M. M >= N0 ==>
    abs(expectation (p:A prob_space)
      (\x. abs((f:A->real) x - max (-- &M) (min (&M) (f x)))) - &0) <
      inv(&(2 * SUC k))` ASSUME_TAC THENL
  [GEN_TAC THEN
   UNDISCH_TAC `((\M. expectation (p:A prob_space)
     (\x. abs((f:A->real) x - max (-- &M) (min (&M) (f x))))) ---> &0) sequentially` THEN
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   DISCH_THEN(MP_TAC o SPEC `inv(&(2 * SUC k))`) THEN
   REWRITE_TAC[REAL_LT_INV_EQ; REAL_OF_NUM_LT] THEN
   ANTS_TAC THENL
   [ARITH_TAC;
    DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN EXISTS_TAC `N0:num` THEN
    REWRITE_TAC[GE] THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_TAC `M0:num->num`) THEN
  (* Step 8: For each k, the INTERS is null *)
  SUBGOAL_THEN `!k:num. null_event (p:A prob_space)
    (INTERS (IMAGE (\j:num. (NM:num->A->bool) (j + M0 k) UNION
      {x:A | x IN prob_carrier p /\
        (?n. ergodic_maxsum (\x. abs((f:A->real) x - max (-- &(j + M0 k))
          (min (&(j + M0 k)) (f x))) - inv(&(2 * SUC k))) tt n x > &0)})
      (:num)))` ASSUME_TAC THENL
  [X_GEN_TAC `k:num` THEN REWRITE_TAC[null_event] THEN
   SUBGOAL_THEN `INTERS (IMAGE (\j:num. (NM:num->A->bool) (j + M0 k) UNION
     {x:A | x IN prob_carrier p /\
       (?n. ergodic_maxsum (\x. abs((f:A->real) x - max (-- &(j + M0 k))
         (min (&(j + M0 k)) (f x))) - inv(&(2 * SUC k))) tt n x > &0)})
     (:num)) IN prob_events (p:A prob_space)` ASSUME_TAC THENL
   [MATCH_MP_TAC PROB_COUNTABLE_INTERS_IN_EVENTS THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY; UNIV_NOT_EMPTY] THEN CONJ_TAC THENL
    [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN
     SUBGOAL_THEN `2 * SUC k = SUC(2 * k + 1)` SUBST1_TAC THENL
     [ARITH_TAC; ASM_REWRITE_TAC[]];
     MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[NUM_COUNTABLE]];
    ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN
   CONJ_TAC THENL [MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_EPSILON THEN REWRITE_TAC[REAL_ADD_LID] THEN
   X_GEN_TAC `e:real` THEN DISCH_TAC THEN
   (* Choose M large enough that (2*SUC k)*E[|f-f_M|] < e *)
   UNDISCH_TAC `((\M. expectation (p:A prob_space)
     (\x. abs((f:A->real) x - max (-- &M) (min (&M) (f x))))) ---> &0) sequentially` THEN
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   DISCH_THEN(MP_TAC o SPEC `e / &(2 * SUC k)`) THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC;
    ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `M1:num` (MP_TAC o SPEC `M1 + M0 (k:num):num`)) THEN
   REWRITE_TAC[GE; LE_ADD] THEN DISCH_TAC THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `prob (p:A prob_space)
     ((NM:num->A->bool) (M1 + M0 (k:num)) UNION
      {x:A | x IN prob_carrier p /\
        (?n. ergodic_maxsum (\x. abs((f:A->real) x - max (-- &(M1 + M0 k))
          (min (&(M1 + M0 k)) (f x))) - inv(&(2 * SUC k))) tt n x > &0)})` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC PROB_MONO THEN CONJ_TAC THENL
    [ASM_REWRITE_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
    [SUBGOAL_THEN `2 * SUC k = SUC(2 * k + 1)` SUBST1_TAC THENL
     [ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_INTERS; FORALL_IN_IMAGE; IN_UNIV] THEN
    X_GEN_TAC `y:A` THEN DISCH_THEN(MP_TAC o SPEC `M1:num`) THEN REWRITE_TAC[];
    ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `prob (p:A prob_space) ((NM:num->A->bool) (M1 + M0 (k:num))) +
     prob p {x:A | x IN prob_carrier p /\
       (?n. ergodic_maxsum (\x. abs((f:A->real) x - max (-- &(M1 + M0 k))
         (min (&(M1 + M0 k)) (f x))) - inv(&(2 * SUC k))) tt n x > &0)}` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC PROB_SUBADDITIVE THEN CONJ_TAC THENL
    [FIRST_ASSUM(MP_TAC o CONJUNCT1 o SPEC `M1 + M0 (k:num):num`) THEN
     REWRITE_TAC[null_event] THEN MESON_TAC[];
     SUBGOAL_THEN `2 * SUC k = SUC(2 * k + 1)` SUBST1_TAC THENL
     [ARITH_TAC; ASM_REWRITE_TAC[]]]; ALL_TAC] THEN
   SUBGOAL_THEN `prob (p:A prob_space) ((NM:num->A->bool) (M1 + M0 (k:num))) = &0`
     SUBST1_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o SPEC `M1 + M0 (k:num):num`) THEN
    REWRITE_TAC[null_event] THEN MESON_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[REAL_ADD_LID] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `&(2 * SUC k) * expectation (p:A prob_space)
     (\x. abs((f:A->real) x - max (-- &(M1 + M0 k)) (min (&(M1 + M0 k)) (f x))))` THEN
   CONJ_TAC THENL
   [SUBGOAL_THEN `2 * SUC k = SUC(2 * k + 1)` SUBST1_TAC THENL
    [ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LT_IMP_LE THEN
   SUBGOAL_THEN `e = &(2 * SUC k) * (e / &(2 * SUC k))` SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_FIELD `~(c = &0) ==> e = c * (e / c)`) THEN
    REWRITE_TAC[REAL_OF_NUM_EQ] THEN ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LT_LMUL THEN
   CONJ_TAC THENL [REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= expectation (p:A prob_space)
     (\x. abs((f:A->real) x - max (-- &(M1 + (M0:num->num) k)) (min (&(M1 + M0 k)) (f x))))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC EXPECTATION_POS THEN CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_ABS THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ERGODIC_TRUNCATION_INTEGRABLE THEN
     ASM_REWRITE_TAC[];
     REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_POS]]; ALL_TAC] THEN
   UNDISCH_TAC `abs(expectation (p:A prob_space)
     (\x. abs((f:A->real) x - max (-- &(M1 + M0 k)) (min (&(M1 + M0 k)) (f x)))) - &0) <
     e / &(2 * SUC k)` THEN
   ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Step 9: Build the total null event *)
  EXISTS_TAC `(N_f:A->bool) UNION UNIONS {INTERS (IMAGE (\j:num.
    (NM:num->A->bool) (j + M0 k) UNION
    {x:A | x IN prob_carrier p /\
      (?n. ergodic_maxsum (\x. abs((f:A->real) x - max (-- &(j + M0 k))
        (min (&(j + M0 k)) (f x))) - inv(&(2 * SUC k))) tt n x > &0)})
    (:num)) | k IN (:num)}` THEN
  CONJ_TAC THENL
  [(* Show it's null *)
   MATCH_MP_TAC NULL_EVENT_UNION THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC NULL_EVENT_COUNTABLE_UNION THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 10: Show the subset inclusion *)
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION; IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  (* Case 1: avg(f) doesn't converge *)
  ASM_CASES_TAC `?L:real. ((\n. inv(&(SUC n)) * sum(0..n)
    (\k. (f:A->real)(ITER k tt x))) ---> L) sequentially` THENL
  [ALL_TAC;
   DISJ1_TAC THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
   REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[]
  ] THEN
  (* avg(f) converges to some L *)
  FIRST_X_ASSUM(X_CHOOSE_TAC `L:real`) THEN
  (* Case 2: L = E[f] - nothing to prove *)
  ASM_CASES_TAC `L = expectation (p:A prob_space) (f:A->real)` THENL
  [UNDISCH_TAC `((\n. inv (&(SUC n)) * sum (0..n)
    (\k. (f:A->real) (ITER k tt x))) ---> L) sequentially` THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Case 3: L != E[f] - show x is in the Wiener null event *)
  DISJ2_TAC THEN
  (* Get k such that |L - E[f]| > inv(SUC k) *)
  SUBGOAL_THEN `&0 < abs(L - expectation (p:A prob_space) (f:A->real))` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_ABS_NZ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `abs(L - expectation (p:A prob_space) (f:A->real))` REAL_ARCH_INV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `K:num` THEN
  (* Show x is in INTERS: for all j, x in NM(j+M0 K) UNION W(j+M0 K, 2*SUC K) *)
  REWRITE_TAC[IN_INTERS; FORALL_IN_IMAGE; IN_UNIV] THEN
  X_GEN_TAC `j:num` THEN
  ABBREV_TAC `M = (j:num) + (M0:num->num) (K:num)` THEN
  (* Either avg(f_M) doesn't converge to E[f_M] or we use Wiener *)
  ASM_CASES_TAC `((\n. inv(&(SUC n)) * sum(0..n)
    (\k. max (-- &M) (min (&M) ((f:A->real)(ITER k tt x))))) --->
    expectation p (\y. max (-- &M) (min (&M) (f y)))) sequentially` THENL
  [ALL_TAC;
   (* avg(f_M) doesn't converge to E[f_M]: x in NM M *)
   REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
   FIRST_ASSUM(MP_TAC o CONJUNCT2 o SPEC `M:num`) THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[]
  ] THEN
  (* avg(f_M) --> E[f_M] at x. Show x in W(M, 2*SUC K). *)
  REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN DISJ2_TAC THEN
  ASM_REWRITE_TAC[] THEN
  (* Key: |L - E[f_M]| > inv(2*SUC K), so some avg(|f-f_M|) > inv(2*SUC K) *)
  (* First show |E[f_M] - E[f]| < inv(2*SUC K) since M >= M0(K) *)
  SUBGOAL_THEN `abs(expectation (p:A prob_space)
    (\x. abs((f:A->real) x - max (-- &M) (min (&M) (f x)))) - &0) <
    inv(&(2 * SUC K))` ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPECL [`K:num`; `M:num`]) THEN
   EXPAND_TAC "M" THEN REWRITE_TAC[GE; ONCE_REWRITE_RULE[ADD_SYM] LE_ADD];
   ALL_TAC] THEN
  (* |E[f_M] - E[f]| <= E[|f - f_M|] < inv(2*SUC K) *)
  SUBGOAL_THEN `abs(expectation (p:A prob_space) (\y. max (-- &M) (min (&M) ((f:A->real) y))) -
    expectation p f) < inv(&(2 * SUC K))` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `expectation (p:A prob_space)
     (\x. abs((f:A->real) x - max (-- &M) (min (&M) (f x))))` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(expectation (p:A prob_space)
      (\x. (f:A->real) x - max (-- &M) (min (&M) (f x))))` THEN
    CONJ_TAC THENL
    [MP_TAC(SPECL [`p:A prob_space`; `f:A->real`;
       `\x:A. max (-- &M) (min (&M) ((f:A->real) x))`] EXPECTATION_SUB) THEN
     ASM_REWRITE_TAC[] THEN
     ANTS_TAC THENL
     [MATCH_MP_TAC ERGODIC_TRUNCATION_INTEGRABLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
     REWRITE_TAC[REAL_ABS_SUB; REAL_LE_REFL];
     MATCH_MP_TAC EXPECTATION_ABS_BOUND THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ERGODIC_TRUNCATION_INTEGRABLE THEN
     ASM_REWRITE_TAC[]];
    UNDISCH_TAC `abs(expectation (p:A prob_space)
      (\x. abs((f:A->real) x - max (-- &M) (min (&M) (f x)))) - &0) <
      inv(&(2 * SUC K))` THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* Therefore |L - E[f_M]| > inv(2*SUC K) *)
  SUBGOAL_THEN `inv(&(2 * SUC K)) < abs(L - expectation (p:A prob_space)
    (\y. max (-- &M) (min (&M) ((f:A->real) y))))` ASSUME_TAC THENL
  [SUBGOAL_THEN `inv(&(2 * SUC K)) + inv(&(2 * SUC K)) <= inv(&(K:num))`
     ASSUME_TAC THENL
   [SUBGOAL_THEN `inv(&(2 * SUC K)) + inv(&(2 * SUC K)) = inv(&(SUC K))`
      SUBST1_TAC THENL
    [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; REAL_INV_MUL] THEN
     REWRITE_TAC[REAL_ARITH `i2 * is + i2 * is = (&2 * i2) * is`] THEN
     SIMP_TAC[REAL_MUL_RINV; REAL_OF_NUM_EQ; ARITH_RULE `~(2 = 0)`] THEN
     REWRITE_TAC[REAL_MUL_LID]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `~(K = 0)` THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `abs(L - expectation (p:A prob_space) (f:A->real)) <=
     abs(L - expectation p (\y:A. max (-- &M) (min (&M) ((f:A->real) y)))) +
     abs(expectation p (\y. max (-- &M) (min (&M) (f y))) - expectation p f)`
     ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `inv(&(2 * SUC K)) < inv(&(K:num))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV2 THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    UNDISCH_TAC `~(K = 0)` THEN ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* avg(f-f_M)(n) --> L - E[f_M] *)
  SUBGOAL_THEN `((\n. inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x)) -
    inv(&(SUC n)) * sum(0..n) (\k. max (-- &M) (min (&M) (f(ITER k tt x))))) --->
    L - expectation (p:A prob_space) (\y. max (-- &M) (min (&M) (f y)))) sequentially`
    ASSUME_TAC THENL
  [MATCH_MP_TAC REALLIM_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* From convergence and |limit| > inv(2*SUC K): exists n with |avg(f-f_M)(n)| > inv(2*SUC K) *)
  SUBGOAL_THEN `?n0:num. abs(inv(&(SUC n0)) * sum(0..n0) (\k. (f:A->real)(ITER k tt x)) -
    inv(&(SUC n0)) * sum(0..n0) (\k. max (-- &M) (min (&M) (f(ITER k tt x))))) >
    inv(&(2 * SUC K))` ASSUME_TAC THENL
  [UNDISCH_TAC `((\n. inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x)) -
    inv(&(SUC n)) * sum(0..n) (\k. max (-- &M) (min (&M) (f(ITER k tt x))))) --->
    L - expectation (p:A prob_space) (\y. max (-- &M) (min (&M) ((f:A->real) y)))) sequentially` THEN
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   DISCH_THEN(MP_TAC o SPEC `abs(L - expectation (p:A prob_space)
     (\y. max (-- &M) (min (&M) ((f:A->real) y)))) - inv(&(2 * SUC K))`) THEN
   ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_TAC `n0:num`) THEN EXISTS_TAC `n0:num` THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `n0:num`) THEN REWRITE_TAC[LE_REFL] THEN
   REWRITE_TAC[real_gt] THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `n0:num`) THEN
  (* |avg(f-f_M)(n0)| > inv(2*SUC K) implies avg(|f-f_M|)(n0) > inv(2*SUC K) *)
  (* by triangle inequality for sums *)
  EXISTS_TAC `n0:num` THEN
  (* Need: ergodic_maxsum(|f-f_M| - inv(2*SUC K)) tt n0 x > 0 *)
  (* This follows from: sum(0..n0)(|f-f_M|(T^k x) - inv(2*SUC K)) > 0 *)
  (* which follows from: sum(0..n0)|f-f_M|(T^k x) > (n0+1)*inv(2*SUC K) *)
  (* which follows from: avg(|f-f_M|)(n0) > inv(2*SUC K) *)
  (* which follows from: |avg(f-f_M)(n0)| > inv(2*SUC K) + triangle ineq *)
  REWRITE_TAC[real_gt] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `sum(0..n0) (\k. (\x. abs((f:A->real) x -
    max (-- &M) (min (&M) (f x))) - inv(&(2 * SUC K))) (ITER k tt x))` THEN
  CONJ_TAC THENL
  [ALL_TAC; REWRITE_TAC[ERGODIC_MAXSUM_GE_SUM]] THEN
  REWRITE_TAC[] THEN
  REWRITE_TAC[SUM_SUB_NUMSEG; SUM_CONST_NUMSEG; SUB_0] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; ADD1] THEN
  SUBGOAL_THEN `(&n0 + &1) * inv(&(2 * SUC K)) <
    sum(0..n0) (\k. abs((f:A->real)(ITER k tt x) -
      max (-- &M) (min (&M) (f(ITER k tt x)))))` MP_TAC THENL
  [MATCH_MP_TAC REAL_LTE_TRANS THEN
   EXISTS_TAC `abs(sum(0..n0) (\k. (f:A->real)(ITER k tt x) -
     max (-- &M) (min (&M) (f(ITER k tt x)))))` THEN
   CONJ_TAC THENL
   [UNDISCH_TAC `abs
       (inv (&(SUC n0)) * sum (0..n0) (\k. (f:A->real) (ITER k tt x)) -
        inv (&(SUC n0)) *
        sum (0..n0) (\k. max (-- &M) (min (&M) (f (ITER k tt x))))) >
       inv (&(2 * SUC K))` THEN
    REWRITE_TAC[real_gt; GSYM REAL_SUB_LDISTRIB; GSYM SUM_SUB_NUMSEG] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NUM] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&(SUC n0) * inv(&(2 * SUC K)) < &(SUC n0) *
      (inv(&(SUC n0)) * abs(sum(0..n0) (\k. (f:A->real)(ITER k tt x) -
        max (-- &M) (min (&M) (f(ITER k tt x))))))` MP_TAC THENL
    [MATCH_MP_TAC REAL_LT_LMUL THEN
     REWRITE_TAC[REAL_OF_NUM_LT; LT_0] THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[REAL_MUL_ASSOC] THEN
     SIMP_TAC[REAL_MUL_RINV; REAL_OF_NUM_EQ; NOT_SUC] THEN
     REWRITE_TAC[REAL_MUL_LID; GSYM REAL_OF_NUM_SUC]];
    REWRITE_TAC[real_ge; SUM_ABS_NUMSEG]];
   SUBGOAL_THEN `&(2 * SUC K) = &(2 * (K + 1))` (fun th ->
     REWRITE_TAC[th] THEN REAL_ARITH_TAC) THEN
   REWRITE_TAC[ADD1]]);;


(* ========================================================================= *)
(* L1 convergence of Birkhoff averages (Mean Ergodic Theorem)                *)
(* ========================================================================= *)

(* Helper: for bounded f, Birkhoff averages converge in L1 via DCT *)
let BIRKHOFF_ERGODIC_BOUNDED_L1 = prove
 (`!p:A prob_space tt f B.
    ergodic p tt /\ integrable p f /\
    (!x. x IN prob_carrier p ==> abs(f x) <= B)
    ==> ((\n. expectation p (\x. abs(inv(&(SUC n)) *
            sum(0..n) (\k. f(ITER k tt x)) - expectation p f))) ---> &0)
         sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `measure_preserving (p:A prob_space) (tt:A->A)` ASSUME_TAC THENL
  [UNDISCH_TAC `ergodic (p:A prob_space) (tt:A->A)` THEN
   REWRITE_TAC[ergodic] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!k:num. integrable (p:A prob_space) (\x. (f:A->real)(ITER k tt x))`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `k:num`]
     EXPECTATION_ITER_COMP_PRESERVED) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Use DOMINATED_CONVERGENCE_AE on |A_n(f) - E[f]| -> 0 *)
  MP_TAC(ISPECL [
    `p:A prob_space`;
    `\n (x:A). abs(inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x)) - expectation p f)`;
    `\x:A. &0`;
    `\x:A. B + abs(expectation (p:A prob_space) (f:A->real))`]
    DOMINATED_CONVERGENCE_AE) THEN
  REWRITE_TAC[EXPECTATION_CONST; REAL_MUL_RZERO] THEN
  ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  REPEAT CONJ_TAC THENL
  [(* Integrability of |A_n(f) - E[f]| *)
   GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_ABS THEN
   MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CMUL THEN MATCH_MP_TAC INTEGRABLE_SUM THEN
    GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[INTEGRABLE_CONST]];
   (* Integrability of B + |E[f]| *)
   REWRITE_TAC[INTEGRABLE_CONST];
   (* Bound: |abs(A_n(f)(x) - E[f])| <= B + |E[f]| *)
   GEN_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
   REWRITE_TAC[REAL_ABS_ABS] THEN
   MATCH_MP_TAC(REAL_ARITH `abs a <= B ==> abs(a - b) <= B + abs b`) THEN
   REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NUM] THEN
   SUBGOAL_THEN `!k:num. ITER k (tt:A->A) x IN prob_carrier p` ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `measure_preserving (p:A prob_space) (ITER k (tt:A->A))` MP_TAC THENL
    [MATCH_MP_TAC MEASURE_PRESERVING_ITER THEN ASM_REWRITE_TAC[];
     DISCH_THEN(MP_TAC o MATCH_MP MEASURE_PRESERVING_CARRIER) THEN
     DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `inv(&(SUC n)) * sum(0..n) (\k:num. B)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_INV THEN REAL_ARITH_TAC;
     MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
     X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[]];
    REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; ADD1] THEN
    SUBGOAL_THEN `inv(&n + &1) * ((&n + &1) * B) = B` (fun th ->
      REWRITE_TAC[th; REAL_LE_REFL]) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    SIMP_TAC[REAL_MUL_LINV; REAL_ARITH `~(&n + &1 = &0)`; REAL_MUL_LID]];
   (* random_variable p (\x. 0) *)
   REWRITE_TAC[RANDOM_VARIABLE_CONST];
   (* |0| <= B + |E[f]| *)
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= B ==> abs(&0) <= B + abs(e)`) THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((f:A->real) x)` THEN
   REWRITE_TAC[REAL_ABS_POS] THEN ASM_SIMP_TAC[];
   (* a.s. convergence: |A_n(f)(x) - E[f]| -> 0 follows from A_n(f) -> E[f] *)
   MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`] BIRKHOFF_ERGODIC) THEN
   ASM_REWRITE_TAC[almost_surely] THEN
   DISCH_THEN(X_CHOOSE_THEN `N:A->bool` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `N:A->bool` THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC SUBSET_TRANS THEN
   EXISTS_TAC `{x:A | x IN prob_carrier p /\
     ~(x IN {x | ((\n. inv (&(SUC n)) * sum (0..n)
       (\k. (f:A->real) (ITER k tt x))) ---> expectation p f)
       sequentially})}` THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
   X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `~((\n.
     abs(inv (&(SUC n)) * sum (0..n) (\k. (f:A->real) (ITER k tt x)) -
       expectation p f)) ---> &0) sequentially` THEN
   REWRITE_TAC[CONTRAPOS_THM; REALLIM_SEQUENTIALLY] THEN
   DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `NN:num` THEN
   DISCH_TAC THEN X_GEN_TAC `nn:num` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `nn:num`) THEN ASM_REWRITE_TAC[] THEN
   REAL_ARITH_TAC]);;


(* Main L1 ergodic theorem *)
let BIRKHOFF_ERGODIC_L1 = prove
 (`!p:A prob_space tt f.
    ergodic p tt /\ integrable p f
    ==> ((\n. expectation p (\x. abs(inv(&(SUC n)) *
            sum(0..n) (\k. f(ITER k tt x)) - expectation p f))) ---> &0)
         sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `measure_preserving (p:A prob_space) (tt:A->A)` ASSUME_TAC THENL
  [UNDISCH_TAC `ergodic (p:A prob_space) (tt:A->A)` THEN
   REWRITE_TAC[ergodic] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!k:num. integrable (p:A prob_space) (\x. (f:A->real)(ITER k tt x))`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `k:num`]
     EXPECTATION_ITER_COMP_PRESERVED) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  (* Get M such that E[|f - f_M|] < e/3 *)
  MP_TAC(ISPECL [`p:A prob_space`; `f:A->real`] ERGODIC_TRUNCATION_L1) THEN
  ASM_REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `M0:num` (LABEL_TAC "TRUNC")) THEN
  ABBREV_TAC `M = SUC M0` THEN
  (* E[|f - fM|] < e/3 *)
  SUBGOAL_THEN `abs(expectation (p:A prob_space)
    (\x:A. abs((f:A->real) x - max (-- &M) (min (&M) (f x))))) < e / &3`
    (LABEL_TAC "TRUNC_BOUND") THENL
  [REMOVE_THEN "TRUNC" MATCH_MP_TAC THEN
   EXPAND_TAC "M" THEN ARITH_TAC; ALL_TAC] THEN
  (* Get N such that E[|A_n(fM) - E[fM]|] < e/3 for n >= N *)
  SUBGOAL_THEN `integrable (p:A prob_space)
    (\x:A. max (-- &M) (min (&M) ((f:A->real) x)))` (LABEL_TAC "INT_FM") THENL
  [MATCH_MP_TAC ERGODIC_TRUNCATION_INTEGRABLE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`;
    `\x:A. max (-- &M) (min (&M) ((f:A->real) x))`; `&M`]
    BIRKHOFF_ERGODIC_BOUNDED_L1) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "BOUNDED_CONV")) THEN
  (* Witness: N *)
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  (* Strip outer abs: abs(E[|...|]) < e follows from 0 <= E[|...|] < e *)
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x < e ==> abs x < e`) THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC EXPECTATION_POS THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ABS THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_CMUL THEN MATCH_MP_TAC INTEGRABLE_SUM THEN
     X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
     ASM_REWRITE_TAC[];
     REWRITE_TAC[INTEGRABLE_CONST]];
    GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC]; ALL_TAC] THEN
  (* E[|A_n(f) - E[f]|] < e via triangle inequality decomposition *)
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `expectation (p:A prob_space) (\x:A.
    abs(inv(&(SUC n)) * sum(0..n)
      (\k. (f:A->real)(ITER k tt x) - max (-- &M) (min (&M) (f(ITER k tt x))))) +
    abs(inv(&(SUC n)) * sum(0..n)
      (\k. max (-- &M) (min (&M) ((f:A->real)(ITER k tt x)))) -
      expectation p (\y. max (-- &M) (min (&M) (f y)))) +
    abs(expectation p (\y:A. max (-- &M) (min (&M) ((f:A->real) y))) -
        expectation p f))` THEN
  CONJ_TAC THENL
  [(* E[|stuff|] <= E[|A|+|B|+|C|] via EXPECTATION_MONO + pointwise triangle *)
   MATCH_MP_TAC EXPECTATION_MONO THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ABS THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_CMUL THEN MATCH_MP_TAC INTEGRABLE_SUM THEN
     X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
     ASM_REWRITE_TAC[];
     REWRITE_TAC[INTEGRABLE_CONST]]; ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_ABS THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
     MATCH_MP_TAC INTEGRABLE_SUM THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
     REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`;
        `\x:A. max (-- &M) (min (&M) ((f:A->real) x))`; `k:num`]
        EXPECTATION_ITER_COMP_PRESERVED) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]];
     MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_ABS THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC INTEGRABLE_CMUL THEN MATCH_MP_TAC INTEGRABLE_SUM THEN
       X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
       MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`;
         `\x:A. max (-- &M) (min (&M) ((f:A->real) x))`; `k:num`]
         EXPECTATION_ITER_COMP_PRESERVED) THEN
       ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
       REWRITE_TAC[INTEGRABLE_CONST]];
      REWRITE_TAC[INTEGRABLE_CONST]]]; ALL_TAC] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
   MATCH_MP_TAC(REAL_ARITH
     `a = b + c + d ==> abs a <= abs b + abs c + abs d`) THEN
   REWRITE_TAC[SUM_SUB_NUMSEG; REAL_SUB_LDISTRIB] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Split E[|A|+|B|+|C|] into E[|A|] + E[|B|] + |C| via linearity *)
  SUBGOAL_THEN
    `expectation (p:A prob_space) (\x:A.
      abs(inv(&(SUC n)) * sum(0..n)
        (\k. (f:A->real)(ITER k tt x) - max (-- &M) (min (&M) (f(ITER k tt x))))) +
      abs(inv(&(SUC n)) * sum(0..n)
        (\k. max (-- &M) (min (&M) (f(ITER k tt x)))) -
        expectation p (\y. max (-- &M) (min (&M) (f y)))) +
      abs(expectation p (\y. max (-- &M) (min (&M) (f y))) - expectation p f)) =
    expectation p (\x. abs(inv(&(SUC n)) * sum(0..n)
      (\k. f(ITER k tt x) - max (-- &M) (min (&M) (f(ITER k tt x)))))) +
    expectation p (\x. abs(inv(&(SUC n)) * sum(0..n)
      (\k. max (-- &M) (min (&M) (f(ITER k tt x)))) -
      expectation p (\y. max (-- &M) (min (&M) (f y))))) +
    abs(expectation p (\y. max (-- &M) (min (&M) (f y))) - expectation p f)`
    SUBST1_TAC THENL
  [(* Linearity via EXPECTATION_ADD twice + EXPECTATION_CONST *)
   MP_TAC(ISPECL [`p:A prob_space`;
     `\x:A. abs(inv(&(SUC n)) * sum(0..n)
       (\k. (f:A->real)(ITER k tt x) - max (-- &M) (min (&M) (f(ITER k tt x)))))`;
     `\x:A. abs(inv(&(SUC n)) * sum(0..n)
       (\k. max (-- &M) (min (&M) ((f:A->real)(ITER k tt x)))) -
       expectation p (\y. max (-- &M) (min (&M) (f y)))) +
     abs(expectation (p:A prob_space) (\y. max (-- &M) (min (&M) ((f:A->real) y))) -
         expectation p f)`]
     EXPECTATION_ADD) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_ABS THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
     MATCH_MP_TAC INTEGRABLE_SUM THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
     REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`;
        `\x:A. max (-- &M) (min (&M) ((f:A->real) x))`; `k:num`]
        EXPECTATION_ITER_COMP_PRESERVED) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]];
     MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_ABS THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC INTEGRABLE_CMUL THEN MATCH_MP_TAC INTEGRABLE_SUM THEN
       X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
       MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`;
         `\x:A. max (-- &M) (min (&M) ((f:A->real) x))`; `k:num`]
         EXPECTATION_ITER_COMP_PRESERVED) THEN
       ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
       REWRITE_TAC[INTEGRABLE_CONST]];
      REWRITE_TAC[INTEGRABLE_CONST]]]; ALL_TAC] THEN
   REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `\x:A. abs(inv(&(SUC n)) * sum(0..n)
       (\k. max (-- &M) (min (&M) ((f:A->real)(ITER k tt x)))) -
       expectation p (\y. max (-- &M) (min (&M) (f y))))`;
     `\x:A. abs(expectation (p:A prob_space)
       (\y. max (-- &M) (min (&M) ((f:A->real) y))) - expectation p f)`]
     EXPECTATION_ADD) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_ABS THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_CMUL THEN MATCH_MP_TAC INTEGRABLE_SUM THEN
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`;
        `\x:A. max (-- &M) (min (&M) ((f:A->real) x))`; `k:num`]
        EXPECTATION_ITER_COMP_PRESERVED) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[INTEGRABLE_CONST]];
     REWRITE_TAC[INTEGRABLE_CONST]]; ALL_TAC] THEN
   REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC[EXPECTATION_CONST];
   ALL_TAC] THEN
  (* Now bound E[|A|] + E[|B|] + |C| < e *)
  MATCH_MP_TAC(REAL_ARITH
    `a < e / &3 /\ b < e / &3 /\ c < e / &3 /\ &0 < e
     ==> a + b + c < e`) THEN
  CONJ_TAC THENL
  [(* Term 1: E[|A_n(f - fM)|] <= E[|f - fM|] < e/3 *)
   MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `expectation (p:A prob_space)
     (\x:A. abs((f:A->real) x - max (-- &M) (min (&M) (f x))))` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `expectation (p:A prob_space) (\x:A.
      inv(&(SUC n)) * sum(0..n)
        (\k. abs((f:A->real)(ITER k tt x) -
          max (-- &M) (min (&M) (f(ITER k tt x))))))` THEN
    CONJ_TAC THENL
    [(* |inv*sum(diff)| <= inv*sum(|diff|) *)
     MATCH_MP_TAC EXPECTATION_MONO THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_ABS THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
      MATCH_MP_TAC INTEGRABLE_SUM THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
      [ASM_REWRITE_TAC[];
       MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`;
         `\x:A. max (-- &M) (min (&M) ((f:A->real) x))`; `k:num`]
         EXPECTATION_ITER_COMP_PRESERVED) THEN
       ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]];
      CONJ_TAC THENL
      [MATCH_MP_TAC INTEGRABLE_CMUL THEN MATCH_MP_TAC INTEGRABLE_SUM THEN
       X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
       MATCH_MP_TAC INTEGRABLE_ABS THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
       CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`;
          `\x:A. max (-- &M) (min (&M) ((f:A->real) x))`; `k:num`]
          EXPECTATION_ITER_COMP_PRESERVED) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]];
       GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[] THEN
       REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NUM] THEN
       MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV THEN REAL_ARITH_TAC;
        REWRITE_TAC[SUM_ABS_NUMSEG]]]];
     (* E[inv*sum(|f-fM| o T^k)] = E[|f-fM|] by measure-preserving *)
     SUBGOAL_THEN
       `!m. expectation (p:A prob_space) (\x:A. sum(0..m)
         (\k. abs((f:A->real)(ITER k tt x) -
           max (-- &M) (min (&M) (f(ITER k tt x)))))) =
         &(SUC m) * expectation p (\x. abs(f x - max (-- &M) (min (&M) (f x))))`
       ASSUME_TAC THENL
     [INDUCT_TAC THENL
      [REWRITE_TAC[SUM_SING_NUMSEG; ITER; ARITH_RULE `SUC 0 = 1`; REAL_MUL_LID];
       REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
       MP_TAC(ISPECL [`p:A prob_space`;
         `\x:A. sum(0..m) (\k. abs((f:A->real)(ITER k tt x) -
           max (-- &M) (min (&M) (f(ITER k tt x)))))`;
         `\x:A. abs((f:A->real)(ITER (SUC m) tt x) -
           max (-- &M) (min (&M) (f(ITER (SUC m) tt x))))`]
         EXPECTATION_ADD) THEN
       ANTS_TAC THENL
       [CONJ_TAC THENL
        [MATCH_MP_TAC INTEGRABLE_SUM THEN X_GEN_TAC `k:num` THEN
         DISCH_TAC THEN REWRITE_TAC[] THEN
         MATCH_MP_TAC INTEGRABLE_ABS THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
         CONJ_TAC THENL
         [ASM_REWRITE_TAC[];
          MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`;
            `\x:A. max (-- &M) (min (&M) ((f:A->real) x))`; `k:num`]
            EXPECTATION_ITER_COMP_PRESERVED) THEN
          ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]];
         MATCH_MP_TAC INTEGRABLE_ABS THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
         CONJ_TAC THENL
         [ASM_REWRITE_TAC[];
          MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`;
            `\x:A. max (-- &M) (min (&M) ((f:A->real) x))`; `SUC m`]
            EXPECTATION_ITER_COMP_PRESERVED) THEN
          ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]]];
        ALL_TAC] THEN
       REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
       ASM_REWRITE_TAC[] THEN
       MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`;
         `\x:A. abs((f:A->real) x - max (-- &M) (min (&M) (f x)))`; `SUC m`]
         EXPECTATION_ITER_COMP_PRESERVED) THEN
       ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_ABS THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
        ASM_REWRITE_TAC[];
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC]];
      ALL_TAC] THEN
     MP_TAC(ISPECL [`p:A prob_space`; `inv(&(SUC n))`;
       `\x:A. sum(0..n) (\k. abs((f:A->real)(ITER k tt x) -
         max (-- &M) (min (&M) (f(ITER k tt x)))))`]
       EXPECTATION_CMUL) THEN
     (ANTS_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_SUM THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_ABS THEN
      MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
      [ASM_REWRITE_TAC[];
       MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`;
         `\x:A. max (-- &M) (min (&M) ((f:A->real) x))`; `k:num`]
         EXPECTATION_ITER_COMP_PRESERVED) THEN
       ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]]; ALL_TAC]) THEN
     REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
     DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC[REAL_MUL_ASSOC] THEN
     SIMP_TAC[REAL_MUL_LINV; REAL_OF_NUM_EQ; NOT_SUC;
              REAL_MUL_LID; REAL_LE_REFL]];
    MATCH_MP_TAC(REAL_ARITH `abs x < e ==> x < e`) THEN ASM_REWRITE_TAC[]];
   CONJ_TAC THENL
   [(* Term 2: E[|A_n(fM) - E[fM]|] < e/3 by BOUNDED_CONV *)
    MATCH_MP_TAC(REAL_ARITH `abs x < e ==> x < e`) THEN
    REMOVE_THEN "BOUNDED_CONV" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    CONJ_TAC THENL
    [(* Term 3: |E[fM] - E[f]| < e/3 *)
     MATCH_MP_TAC REAL_LET_TRANS THEN
     EXISTS_TAC `expectation (p:A prob_space)
       (\x:A. abs((f:A->real) x - max (-- &M) (min (&M) (f x))))` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `abs(expectation (p:A prob_space)
        (\x:A. max (-- &M) (min (&M) ((f:A->real) x)) - f x))` THEN
      CONJ_TAC THENL
      [SUBGOAL_THEN `expectation (p:A prob_space)
         (\y:A. max (-- &M) (min (&M) ((f:A->real) y))) - expectation p f =
         expectation p (\x. max (-- &M) (min (&M) (f x)) - f x)` SUBST1_TAC THENL
       [MATCH_MP_TAC(GSYM EXPECTATION_SUB) THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[REAL_LE_REFL]];
       MATCH_MP_TAC REAL_LE_TRANS THEN
       EXISTS_TAC `expectation (p:A prob_space)
         (\x:A. abs(max (-- &M) (min (&M) ((f:A->real) x)) - f x))` THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC EXPECTATION_ABS_BOUND THEN
        MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC EXPECTATION_MONO THEN CONJ_TAC THENL
        [MATCH_MP_TAC INTEGRABLE_ABS THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
         ASM_REWRITE_TAC[];
         CONJ_TAC THENL
         [MATCH_MP_TAC INTEGRABLE_ABS THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
          ASM_REWRITE_TAC[];
          GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC]]]];
      MATCH_MP_TAC(REAL_ARITH `abs x < e ==> x < e`) THEN
      ASM_REWRITE_TAC[]];
     (* &0 < e *)
     ASM_REWRITE_TAC[]]]]);;

(* ======================================================================== *)
(* SLLN for stationary ergodic sequences via Birkhoff                       *)
(* ======================================================================== *)

(* If X_n = X_0 o T^n for an ergodic T, then SLLN holds (a.s. version) *)
let IID_SLLN_VIA_BIRKHOFF = prove
 (`!p:A prob_space tt (X:num->A->real) mu.
    ergodic p tt /\
    integrable p (X 0) /\
    (!n x. x IN prob_carrier p ==> X n x = X 0 (ITER n tt x)) /\
    expectation p (X 0) = mu
    ==> almost_surely p
          {x | ((\n. inv(&(SUC n)) * sum(0..n) (\i. X i x)) ---> mu)
               sequentially}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC `{x:A | ((\n. inv(&(SUC n)) * sum(0..n)
    (\k. (X:num->A->real) 0 (ITER k tt x))) ---> mu) sequentially}` THEN
  CONJ_TAC THENL
  [SUBGOAL_THEN `mu = expectation (p:A prob_space) ((X:num->A->real) 0)`
     SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC BIRKHOFF_ERGODIC THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   SUBGOAL_THEN `!n. sum(0..n) (\i. (X:num->A->real) i (x:A)) =
     sum(0..n) (\k. X 0 (ITER k (tt:A->A) x))`
     (fun th -> REWRITE_TAC[th]) THEN
   GEN_TAC THEN MATCH_MP_TAC SUM_EQ THEN
   X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_NUMSEG] THEN DISCH_TAC THEN
   CONV_TAC SYM_CONV THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `x:A`]) THEN
   ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

(* L1 version: E[|A_n(X) - mu|] -> 0 *)
let IID_SLLN_L1_VIA_BIRKHOFF = prove
 (`!p:A prob_space tt (X:num->A->real) mu.
    ergodic p tt /\
    integrable p (X 0) /\
    (!n x. x IN prob_carrier p ==> X n x = X 0 (ITER n tt x)) /\
    expectation p (X 0) = mu
    ==> ((\n. expectation p (\x. abs(inv(&(SUC n)) *
            sum(0..n) (\i. X i x) - mu))) ---> &0)
         sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `!n. expectation (p:A prob_space) (\x. abs(inv(&(SUC n)) *
       sum(0..n) (\i. (X:num->A->real) i x) - mu)) =
     expectation p (\x. abs(inv(&(SUC n)) *
       sum(0..n) (\k. X 0 (ITER k (tt:A->A) x)) - mu))`
    (fun th -> REWRITE_TAC[th]) THENL
  [GEN_TAC THEN MATCH_MP_TAC EXPECTATION_EXT THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
   AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
   MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:num` THEN
   REWRITE_TAC[IN_NUMSEG] THEN DISCH_TAC THEN
   CONV_TAC SYM_CONV THEN FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `x:A`]) THEN
   ASM_REWRITE_TAC[] THEN SIMP_TAC[];
   SUBGOAL_THEN `mu = expectation (p:A prob_space) ((X:num->A->real) 0)`
     SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC BIRKHOFF_ERGODIC_L1 THEN ASM_REWRITE_TAC[]]);;

(* ======================================================================== *)
(* Mean Ergodic Theorem (von Neumann): L2 convergence of ergodic averages   *)
(* ======================================================================== *)

(* Helper: bounded integrable function has integrable square *)
let INTEGRABLE_BOUNDED_POW2 = prove
 (`!p:A prob_space (g:A->real) C.
    integrable p g /\ (!x. x IN prob_carrier p ==> abs(g x) <= C)
    ==> integrable p (\x. g x pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC INTEGRABLE_DOMINATED THEN
  EXISTS_TAC `\x:A. abs((C:real) * C)` THEN REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
   MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[INTEGRABLE_CONST];
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
   REWRITE_TAC[REAL_POW_2; REAL_ABS_MUL] THEN
   REWRITE_TAC[REAL_ABS_ABS] THEN
   MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C:real` THEN
   ASM_SIMP_TAC[REAL_ABS_LE]]);;

(* Mean Ergodic Theorem: bounded case *)
let MEAN_ERGODIC_BOUNDED = prove
 (`!p:A prob_space tt f M.
    ergodic p tt /\
    integrable p f /\
    (!x. x IN prob_carrier p ==> abs(f x) <= M)
    ==> ((\n. expectation p (\x. (inv(&(SUC n)) *
            sum(0..n) (\k. f(ITER k tt x)) - expectation p f) pow 2)) ---> &0)
         sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `mu = expectation (p:A prob_space) (f:A->real)` THEN
  SUBGOAL_THEN `measure_preserving (p:A prob_space) (tt:A->A)` ASSUME_TAC THENL
  [UNDISCH_TAC `ergodic (p:A prob_space) (tt:A->A)` THEN
   REWRITE_TAC[ergodic] THEN MESON_TAC[]; ALL_TAC] THEN
  (* Key: |avg - mu| <= 2M, so (avg-mu)^2 <= 2M * |avg-mu| *)
  SUBGOAL_THEN `!n x. x IN prob_carrier (p:A prob_space)
    ==> abs(inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x)) - mu)
        <= &2 * M` (LABEL_TAC "AVG_BOUND") THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC(REAL_ARITH `abs a <= M /\ abs b <= M ==> abs(a - b) <= &2 * M`) THEN
   CONJ_TAC THENL
   [MP_TAC(SPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `M:real`; `n:num`; `x:A`]
     ERGODIC_AVG_BOUNDED) THEN ASM_REWRITE_TAC[];
    EXPAND_TAC "mu" THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `expectation (p:A prob_space) (\x:A. abs((f:A->real) x))` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC EXPECTATION_ABS_BOUND THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `expectation (p:A prob_space) (\x:A. M:real)` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC EXPECTATION_MONO THEN
      ASM_REWRITE_TAC[INTEGRABLE_CONST] THEN
      MATCH_MP_TAC INTEGRABLE_ABS THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[EXPECTATION_CONST] THEN REAL_ARITH_TAC]]];
   ALL_TAC] THEN
  (* Integrable avg - mu *)
  SUBGOAL_THEN `!n. integrable (p:A prob_space)
    (\x:A. inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x)) - mu)`
    (LABEL_TAC "INT_DIFF") THENL
  [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
   REWRITE_TAC[INTEGRABLE_CONST] THEN
   MATCH_MP_TAC ERGODIC_AVG_INTEGRABLE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Integrable (avg - mu)^2 *)
  SUBGOAL_THEN `!n. integrable (p:A prob_space)
    (\x:A. (inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x)) - mu) pow 2)`
    (LABEL_TAC "INT_SQ") THENL
  [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_BOUNDED_POW2 THEN
   EXISTS_TAC `&2 * M` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  (* Use comparison: 0 <= E[(avg-mu)^2] <= 2M * E[|avg-mu|] --> 0 *)
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n:num. (&2 * M) * expectation (p:A prob_space)
    (\x:A. abs(inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x)) - mu))` THEN
  CONJ_TAC THENL
  [(* Eventually: |E[(avg-mu)^2]| <= 2M * E[|avg-mu|] *)
   REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
   X_GEN_TAC `n:num` THEN DISCH_TAC THEN BETA_TAC THEN
   (* E[(avg-mu)^2] >= 0, so abs(E[...]) = E[...] *)
   MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a <= b ==> abs a <= b`) THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC EXPECTATION_POS THEN CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN REWRITE_TAC[REAL_LE_POW_2]];
    (* E[(avg-mu)^2] <= E[2M * |avg-mu|] = 2M * E[|avg-mu|] *)
    SUBGOAL_THEN `(&2 * M) * expectation (p:A prob_space)
      (\x:A. abs(inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x)) - mu)) =
      expectation p (\x. (&2 * M) * abs(inv(&(SUC n)) * sum(0..n)
        (\k. f(ITER k tt x)) - mu))` SUBST1_TAC THENL
    [MATCH_MP_TAC(GSYM EXPECTATION_CMUL) THEN
     MATCH_MP_TAC INTEGRABLE_ABS THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC EXPECTATION_MONO THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC INTEGRABLE_CMUL THEN
      MATCH_MP_TAC INTEGRABLE_ABS THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
      REWRITE_TAC[REAL_POW_2] THEN
      (* a*a <= 2M * |a| when |a| <= 2M, i.e. |a|*|a| <= 2M*|a| *)
      MATCH_MP_TAC(REAL_ARITH
        `abs a * abs a <= c * abs a ==> a * a <= c * abs a`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      ASM_SIMP_TAC[]]]];
   (* 2M * E[|avg-mu|] --> 0 *)
   SUBGOAL_THEN
     `(\n:num. (&2 * M) * expectation (p:A prob_space)
       (\x:A. abs(inv(&(SUC n)) * sum(0..n)
         (\k. (f:A->real)(ITER k tt x)) - mu))) =
      (\n. (&2 * M) * (\n. expectation p
       (\x. abs(inv(&(SUC n)) * sum(0..n)
         (\k. f(ITER k tt x)) - mu))) n)` SUBST1_TAC THENL
   [REWRITE_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC REALLIM_NULL_LMUL THEN
   EXPAND_TAC "mu" THEN
   MATCH_MP_TAC BIRKHOFF_ERGODIC_L1 THEN ASM_REWRITE_TAC[]]);;

(* Cauchy-Schwarz for finite sums: (sum a)^2 <= (n+1) * sum(a^2) *)
let SUM_SQUARE_CAUCHY_SCHWARZ = prove
 (`!f:num->real n. (sum(0..n) f) pow 2 <= &(SUC n) * sum(0..n) (\i. f i pow 2)`,
  GEN_TAC THEN INDUCT_TAC THENL
  [REWRITE_TAC[SUM_SING_NUMSEG] THEN BETA_TAC THEN
   REWRITE_TAC[ARITH_RULE `SUC 0 = 1`; REAL_MUL_LID; REAL_LE_REFL];
   REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN BETA_TAC THEN
   ABBREV_TAC `S = sum(0..n) (f:num->real)` THEN
   ABBREV_TAC `Q = sum(0..n) (\i. (f:num->real) i pow 2)` THEN
   ABBREV_TAC `a = (f:num->real)(SUC n)` THEN
   REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
   MATCH_MP_TAC(REAL_ARITH
     `S pow 2 <= (&n + &1) * Q /\
      &0 <= Q - &2 * a * S + (&n + &1) * a pow 2
      ==> (S + a) pow 2 <= ((&n + &1) + &1) * (Q + a pow 2)`) THEN
   CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_SUC];
    EXPAND_TAC "Q" THEN EXPAND_TAC "S" THEN EXPAND_TAC "a" THEN
    SUBGOAL_THEN `sum(0..n) (\i. (f:num->real) i pow 2) -
      &2 * f(SUC n) * sum(0..n) f + (&n + &1) * f(SUC n) pow 2 =
      sum(0..n) (\i. (f i - f(SUC n)) pow 2)` SUBST1_TAC THENL
    [REWRITE_TAC[REAL_POW_2] THEN
     REWRITE_TAC[REAL_ARITH `(a - b) * (a - b) = a * a - &2 * b * a + b * b`] THEN
     REWRITE_TAC[SUM_ADD_NUMSEG; SUM_SUB_NUMSEG; SUM_LMUL; SUM_RMUL] THEN
     REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0] THEN
     REWRITE_TAC[REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
     MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
     GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN REWRITE_TAC[REAL_LE_POW_2]]]]);;

(* Variance bound for ergodic averages:
   E[(A_n(f) - E[f])^2] <= E[f^2] *)
let ERGODIC_AVG_VARIANCE_BOUND = prove
 (`!p:A prob_space tt f.
    measure_preserving p tt /\ integrable p f /\ integrable p (\x. f x pow 2)
    ==> !n. expectation p
      (\x. (inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x)) - expectation p f) pow 2)
      <= expectation p (\x. f x pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `mu = expectation (p:A prob_space) (f:A->real)` THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. ((f:A->real) x - mu) pow 2)`
    (LABEL_TAC "INT_SQ") THENL
  [REWRITE_TAC[REAL_POW_2;
     REAL_ARITH `(a - b) * (a - b) = a * a - &2 * b * a + b * b`] THEN
   MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
    [ASM_REWRITE_TAC[GSYM REAL_POW_2];
     MATCH_MP_TAC INTEGRABLE_CMUL THEN
     MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[INTEGRABLE_CONST]];
   ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN
  (* Integrability of inv(n+1)*sum((f_k-mu)^2) *)
  SUBGOAL_THEN `integrable (p:A prob_space)
    (\x:A. inv(&(SUC n)) * sum(0..n)
      (\k. ((f:A->real)(ITER k tt x) - mu) pow 2))`
    (LABEL_TAC "INT_AVG") THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`;
     `\x:A. ((f:A->real) x - mu) pow 2`; `n:num`] ERGODIC_AVG_INTEGRABLE) THEN
   ASM_REWRITE_TAC[] THEN REWRITE_TAC[];
   ALL_TAC] THEN
  (* Pointwise Cauchy-Schwarz bound *)
  SUBGOAL_THEN `!x:A.
    (inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x)) - mu) pow 2 <=
    inv(&(SUC n)) * sum(0..n) (\k. (f(ITER k tt x) - mu) pow 2)`
    (LABEL_TAC "PW_BOUND") THENL
  [X_GEN_TAC `x:A` THEN
   MP_TAC(ISPECL [`\k. (f:A->real)(ITER k (tt:A->A) x) - mu`; `n:num`]
     SUM_SQUARE_CAUCHY_SCHWARZ) THEN
   BETA_TAC THEN
   ABBREV_TAC `S = sum(0..n) (\k. (f:A->real)(ITER k (tt:A->A) x) - mu)` THEN
   ABBREV_TAC `Q = sum(0..n) (\k. ((f:A->real)(ITER k (tt:A->A) x) - mu) pow 2)` THEN
   SUBGOAL_THEN `sum(0..n) (\k. (f:A->real)(ITER k (tt:A->A) x)) = S + &(SUC n) * mu`
     SUBST1_TAC THENL
   [EXPAND_TAC "S" THEN ONCE_REWRITE_TAC[real_sub] THEN
    REWRITE_TAC[SUM_ADD_NUMSEG; SUM_CONST_NUMSEG; SUB_0; GSYM ADD1;
                SUM_NEG; REAL_NEG_NEG] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `inv(&(SUC n)) * (S + &(SUC n) * mu) - mu = inv(&(SUC n)) * S`
     SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_MUL_ASSOC] THEN
    SIMP_TAC[REAL_MUL_LINV; REAL_OF_NUM_EQ; NOT_SUC; REAL_MUL_LID] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
   DISCH_TAC THEN
   REWRITE_TAC[REAL_POW_MUL; REAL_POW_2] THEN
   REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `inv(&(SUC n)) * &(SUC n) * Q` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_INV THEN REWRITE_TAC[REAL_POS];
     ASM_REWRITE_TAC[GSYM REAL_POW_2]];
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    SIMP_TAC[REAL_MUL_LINV; REAL_OF_NUM_EQ; NOT_SUC; REAL_MUL_LID;
             REAL_LE_REFL]];
   ALL_TAC] THEN
  (* Integrability of (A_n-mu)^2 via domination *)
  SUBGOAL_THEN `integrable (p:A prob_space)
    (\x:A. (inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x)) - mu) pow 2)`
    (LABEL_TAC "INT_LHS") THENL
  [MATCH_MP_TAC INTEGRABLE_DOMINATED THEN
   EXISTS_TAC `\x:A. inv(&(SUC n)) * sum(0..n)
     (\k. ((f:A->real)(ITER k tt x) - mu) pow 2)` THEN
   REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
    MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
     MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `n:num`]
       ERGODIC_AVG_INTEGRABLE) THEN
     ASM_REWRITE_TAC[] THEN REWRITE_TAC[];
     REWRITE_TAC[RANDOM_VARIABLE_CONST]];
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a <= b ==> abs a <= abs b`) THEN
    CONJ_TAC THENL
    [REWRITE_TAC[REAL_LE_POW_2];
     FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN REWRITE_TAC[]]];
   ALL_TAC] THEN
  (* Main: E[(A_n-mu)^2] <= E[(f-mu)^2] <= E[f^2] *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `expectation (p:A prob_space) (\x:A. ((f:A->real) x - mu) pow 2)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `expectation (p:A prob_space)
     (\x:A. inv(&(SUC n)) * sum(0..n)
       (\k. ((f:A->real)(ITER k tt x) - mu) pow 2))` THEN
   CONJ_TAC THENL
   [(* E[(A_n-mu)^2] <= E[inv(n+1)*sum((f_k-mu)^2)] by EXPECTATION_MONO *)
    MP_TAC(ISPECL [`p:A prob_space`;
      `\x:A. (inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x)) - mu) pow 2`;
      `\x:A. inv(&(SUC n)) * sum(0..n) (\k. ((f:A->real)(ITER k tt x) - mu) pow 2)`]
      EXPECTATION_MONO) THEN
    BETA_TAC THEN ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
     SIMP_TAC[]];
    (* E[inv(n+1)*sum((f_k-mu)^2)] = E[(f-mu)^2] by ERGODIC_AVG_EXPECTATION *)
    SUBGOAL_THEN `expectation (p:A prob_space)
      (\x:A. inv(&(SUC n)) * sum(0..n)
        (\k. ((f:A->real)(ITER k tt x) - mu) pow 2)) =
      expectation p (\x. (f x - mu) pow 2)`
      (fun th -> REWRITE_TAC[th; REAL_LE_REFL]) THEN
    MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`;
      `\x:A. ((f:A->real) x - mu) pow 2`; `n:num`]
      ERGODIC_AVG_EXPECTATION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th])];
   (* E[(f-mu)^2] <= E[f^2] since E[(f-mu)^2] = E[f^2] - mu^2 *)
   SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. ((f:A->real) x - mu) pow 2) =
     expectation p (\x. f x pow 2) - mu pow 2` SUBST1_TAC THENL
   [SUBGOAL_THEN `(\x:A. ((f:A->real) x - mu) pow 2) =
     (\x. f x pow 2 + ((-- &2 * mu) * f x + mu pow 2))` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM; REAL_POW_2] THEN REAL_ARITH_TAC;
     ASM_SIMP_TAC[EXPECTATION_ADD; INTEGRABLE_ADD; INTEGRABLE_CMUL;
                  INTEGRABLE_CONST; GSYM REAL_POW_2] THEN
     ASM_SIMP_TAC[EXPECTATION_ADD; INTEGRABLE_CMUL; INTEGRABLE_CONST] THEN
     ASM_SIMP_TAC[EXPECTATION_CMUL; EXPECTATION_CONST] THEN
     EXPAND_TAC "mu" THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC];
    REWRITE_TAC[REAL_POW_2] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= m * m ==> a - m * m <= a`) THEN
    REWRITE_TAC[REAL_LE_SQUARE]]]);;

(* ------------------------------------------------------------------------- *)
(* L2 convergence of truncation: E[(f - trunc_M(f))^2] -> 0 as M -> infty.  *)
(* ------------------------------------------------------------------------- *)

let TRUNCATION_L2_CONVERGENCE = prove
 (`!p:A prob_space (f:A->real).
     integrable p f /\ integrable p (\x. f x pow 2)
     ==> ((\M. expectation p (\x. (f x - max (-- &M) (min (&M) (f x))) pow 2))
          ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `\M (x:A). ((f:A->real) x - max (-- &M) (min (&M) (f x))) pow 2`;
    `\x:A. &0:real`;
    `\x:A. (f:A->real) x pow 2`] DOMINATED_CONVERGENCE) THEN
  ANTS_TAC THENL
  [BETA_TAC THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_DOMINATED THEN
    EXISTS_TAC `\x:A. (f:A->real) x pow 2` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
     MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
      MATCH_MP_TAC ERGODIC_TRUNCATION_INTEGRABLE THEN ASM_REWRITE_TAC[]];
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN
     SUBGOAL_THEN `(f:A->real) x pow 2 = abs(f x) pow 2`
       SUBST1_TAC THENL [REWRITE_TAC[REAL_POW2_ABS]; ALL_TAC] THEN
     REWRITE_TAC[REAL_ABS_POW] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
     REWRITE_TAC[REAL_ABS_POS; REAL_ABS_ABS; ERGODIC_TRUNCATION_ABS_BOUND]];
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(f:A->real) x pow 2 = abs(f x) pow 2`
      SUBST1_TAC THENL [REWRITE_TAC[REAL_POW2_ABS]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_POW] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    REWRITE_TAC[REAL_ABS_POS; REAL_ABS_ABS; ERGODIC_TRUNCATION_ABS_BOUND];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 = &0 pow 2` SUBST1_TAC THENL
    [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    MATCH_MP_TAC REALLIM_POW THEN
    REWRITE_TAC[ERGODIC_TRUNCATION_POINTWISE]];
   DISCH_THEN(MP_TAC o CONJUNCT2) THEN BETA_TAC THEN
   SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. &0) = &0`
     (fun th -> REWRITE_TAC[th; INTEGRABLE_CONST]) THEN
   REWRITE_TAC[EXPECTATION_CONST; REAL_MUL_RZERO]]);;

(* ------------------------------------------------------------------------- *)
(* Integrability of (A_n(f) - E[f])^2 for square-integrable f.              *)
(* ------------------------------------------------------------------------- *)

let ERGODIC_AVG_INTEGRABLE_POW2 = prove
 (`!p:A prob_space (tt:A->A) (f:A->real) n.
     measure_preserving p tt /\
     integrable p f /\ integrable p (\x. f x pow 2)
     ==> integrable p
       (\x. (inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x)) -
             expectation p f) pow 2)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `mu = expectation (p:A prob_space) (f:A->real)` THEN
  SUBGOAL_THEN `integrable (p:A prob_space)
    (\x:A. inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x)))`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `f:A->real`; `n:num`]
    ERGODIC_AVG_INTEGRABLE) THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space)
    (\x:A. inv(&(SUC n)) * sum(0..n) (\k. ((f:A->real)(ITER k tt x) - mu) pow 2))`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`;
    `\x:A. ((f:A->real) x - mu) pow 2`; `n:num`] ERGODIC_AVG_INTEGRABLE) THEN
   ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [SUBGOAL_THEN `(\x:A. ((f:A->real) x - mu) pow 2) =
     (\x. f x pow 2 + ((-- &2 * mu) * f x + mu pow 2))` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM; REAL_POW_2] THEN REAL_ARITH_TAC;
     ASM_SIMP_TAC[INTEGRABLE_ADD; INTEGRABLE_CMUL; INTEGRABLE_CONST]];
    SIMP_TAC[]];
   ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `\x:A. (inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x)) - mu) pow 2`;
    `\x:A. inv(&(SUC n)) * sum(0..n) (\k. ((f:A->real)(ITER k tt x) - mu) pow 2)`]
    INTEGRABLE_DOMINATED) THEN BETA_TAC THEN ANTS_TAC THENL
  [CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
    MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
    MP_TAC(ISPECL [`p:A prob_space`;
      `\x:A. inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x))`;
      `(\x:A. mu):A->real`] INTEGRABLE_SUB) THEN
    ASM_REWRITE_TAC[INTEGRABLE_CONST] THEN BETA_TAC THEN SIMP_TAC[];
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ABS_POW] THEN
    SUBGOAL_THEN `abs(inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x)) -
      mu) pow 2 =
      (inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x)) - mu) pow 2`
      SUBST1_TAC THENL [REWRITE_TAC[REAL_POW2_ABS]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= b /\ a <= b ==> a <= abs b`) THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
      GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_LE_POW_2]];
     ALL_TAC] THEN
    SUBGOAL_THEN `inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x)) -
      mu = inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x) - mu)`
      SUBST1_TAC THENL
    [REWRITE_TAC[SUM_SUB_NUMSEG] THEN
     REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0; ADD1] THEN
     REWRITE_TAC[REAL_SUB_LDISTRIB] THEN
     ONCE_REWRITE_TAC[REAL_MUL_ASSOC] THEN
     SIMP_TAC[REAL_MUL_LINV; REAL_OF_NUM_EQ;
              ARITH_RULE `~(n + 1 = 0)`] THEN
     REWRITE_TAC[REAL_MUL_LID];
     ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_MUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(&(SUC n)) pow 2 *
      (&(SUC n) * sum(0..n) (\k. ((f:A->real)(ITER k tt x) - mu) pow 2))` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_POW_2];
      MP_TAC(ISPECL [`\k. (f:A->real)(ITER k (tt:A->A) x) - mu`;
        `n:num`] SUM_SQUARE_CAUCHY_SCHWARZ) THEN SIMP_TAC[]];
     ONCE_REWRITE_TAC[REAL_MUL_ASSOC] THEN
     SUBGOAL_THEN `inv(&(SUC n)) pow 2 * &(SUC n) = inv(&(SUC n))`
       SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
      SIMP_TAC[REAL_MUL_LINV; REAL_OF_NUM_EQ; NOT_SUC; REAL_MUL_RID];
      REWRITE_TAC[REAL_LE_REFL]]]];
   SIMP_TAC[]]);;

(* Helper: (a+b)^2 <= 2*a^2 + 2*b^2 *)
let SQ_SUM_BOUND = prove
 (`!a b. (a + b) pow 2 <= &2 * a pow 2 + &2 * b pow 2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN
  MP_TAC(SPEC `a - b:real` REAL_LE_SQUARE) THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Mean Ergodic Theorem (von Neumann): L2 convergence of ergodic averages.   *)
(* For ergodic T and square-integrable f,                                    *)
(*   E[(A_n(f) - E[f])^2] -> 0 as n -> infinity.                            *)
(* ------------------------------------------------------------------------- *)

let MEAN_ERGODIC_THEOREM = prove
 (`!p:A prob_space (tt:A->A) (f:A->real).
     ergodic p tt /\ integrable p f /\ integrable p (\x. f x pow 2)
     ==> ((\n. expectation p
       (\x. (inv(&(SUC n)) * sum(0..n) (\k. f(ITER k tt x)) -
             expectation p f) pow 2)) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `measure_preserving (p:A prob_space) (tt:A->A)` ASSUME_TAC THENL
  [ASM_MESON_TAC[ergodic]; ALL_TAC] THEN
  ABBREV_TAC `mu = expectation (p:A prob_space) (f:A->real)` THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN
  DISCH_TAC THEN
  (* Use truncation approximation: find M with E[(f-g_M)^2] < e/4 *)
  MP_TAC(ISPECL [`p:A prob_space`; `f:A->real`] TRUNCATION_L2_CONVERGENCE) THEN
  ASM_REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &4`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
  (* Use MEAN_ERGODIC_BOUNDED for g_M to find N *)
  MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`;
    `\x:A. max (-- &M) (min (&M) ((f:A->real) x))`; `&M`]
    MEAN_ERGODIC_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [MATCH_MP_TAC ERGODIC_TRUNCATION_INTEGRABLE THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &4`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  (* Abbreviate g = trunc_M(f) and h = f - g *)
  ABBREV_TAC `g = \x:A. max (-- &M) (min (&M) ((f:A->real) x))` THEN
  ABBREV_TAC `h = \x:A. (f:A->real) x - (g:A->real) x` THEN
  (* Establish integrability of g and g^2 *)
  SUBGOAL_THEN `integrable (p:A prob_space) (g:A->real)` ASSUME_TAC THENL
  [EXPAND_TAC "g" THEN MATCH_MP_TAC ERGODIC_TRUNCATION_INTEGRABLE THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. (g:A->real) x pow 2)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_BOUNDED_POW2 THEN EXISTS_TAC `&M` THEN
   ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN
   EXPAND_TAC "g" THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Establish integrability of h and h^2 *)
  SUBGOAL_THEN `integrable (p:A prob_space) (h:A->real)` ASSUME_TAC THENL
  [EXPAND_TAC "h" THEN MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. (h:A->real) x pow 2)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_DOMINATED THEN
   EXISTS_TAC `\x:A. (f:A->real) x pow 2` THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
    MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:A->real) x pow 2 = abs(f x) pow 2`
      SUBST1_TAC THENL [REWRITE_TAC[REAL_POW2_ABS]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_POW] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    REWRITE_TAC[REAL_ABS_POS; REAL_ABS_ABS] THEN
    EXPAND_TAC "h" THEN EXPAND_TAC "g" THEN
    REWRITE_TAC[ERGODIC_TRUNCATION_ABS_BOUND]];
   ALL_TAC] THEN
  (* Key bound: E[(A_n(h) - E[h])^2] < e/4 *)
  SUBGOAL_THEN
    `expectation (p:A prob_space)
      (\x:A. (inv(&(SUC n)) * sum(0..n) (\k. (h:A->real)(ITER k tt x)) -
              expectation p h) pow 2) < e / &4` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `expectation (p:A prob_space) (\x:A. (h:A->real) x pow 2)` THEN
   CONJ_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `tt:A->A`; `h:A->real`]
     ERGODIC_AVG_VARIANCE_BOUND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[];
    (* E[h^2] = E[(f-g)^2] < e/4 from truncation bound *)
    SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. (h:A->real) x pow 2) =
      expectation p (\x. ((f:A->real) x - max (-- &M) (min (&M) (f x))) pow 2)`
      SUBST1_TAC THENL
    [AP_TERM_TAC THEN EXPAND_TAC "h" THEN EXPAND_TAC "g" THEN REWRITE_TAC[];
     SUBGOAL_THEN `&0 <= expectation (p:A prob_space)
       (\x:A. ((f:A->real) x - max (-- &M) (min (&M) (f x))) pow 2)` MP_TAC THENL
     [MATCH_MP_TAC EXPECTATION_POS THEN CONJ_TAC THENL
      [UNDISCH_TAC `integrable (p:A prob_space) (\x:A. (h:A->real) x pow 2)` THEN
       SUBGOAL_THEN `(\x:A. (h:A->real) x pow 2) =
         (\x. ((f:A->real) x - max (-- &M) (min (&M) (f x))) pow 2)` SUBST1_TAC
         THENL [EXPAND_TAC "h" THEN EXPAND_TAC "g" THEN REWRITE_TAC[];
                SIMP_TAC[]];
       GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_LE_POW_2]];
      FIRST_X_ASSUM(fun th ->
       if free_in `N:num` (concl th) then failwith ""
       else MP_TAC(SPEC `M:num` th)) THEN
      REWRITE_TAC[LE_REFL] THEN REAL_ARITH_TAC]]];
   ALL_TAC] THEN
  (* Key bound: E[(A_n(g) - E[g])^2] < e/4 from BOUNDED_CONV *)
  SUBGOAL_THEN
    `expectation (p:A prob_space)
      (\x:A. (inv(&(SUC n)) * sum(0..n) (\k. (g:A->real)(ITER k tt x)) -
              expectation p g) pow 2) < e / &4` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= expectation (p:A prob_space)
      (\x:A. (inv(&(SUC n)) * sum(0..n) (\k. (g:A->real)(ITER k tt x)) -
              expectation p g) pow 2)` MP_TAC THENL
   [MATCH_MP_TAC EXPECTATION_POS THEN CONJ_TAC THENL
    [MATCH_MP_TAC ERGODIC_AVG_INTEGRABLE_POW2 THEN ASM_REWRITE_TAC[];
     GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_LE_POW_2]];
    SUBGOAL_THEN `abs(expectation (p:A prob_space)
      (\x:A. (inv(&(SUC n)) *
        sum(0..n) (\k. max (-- &M) (min (&M) ((f:A->real)(ITER k tt x)))) -
        expectation p g) pow 2)) < e / &4` MP_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[];
     SUBGOAL_THEN `(\x:A. (inv(&(SUC n)) *
       sum(0..n) (\k. max (-- &M) (min (&M) ((f:A->real)(ITER k tt x)))) -
       expectation p g) pow 2) =
       (\x. (inv(&(SUC n)) * sum(0..n) (\k. (g:A->real)(ITER k tt x)) -
             expectation p g) pow 2)` SUBST1_TAC THENL
     [EXPAND_TAC "g" THEN REWRITE_TAC[]; REAL_ARITH_TAC]]];
   ALL_TAC] THEN
  (* Non-negativity of the LHS expectation *)
  SUBGOAL_THEN `&0 <= expectation (p:A prob_space)
    (\x:A. (inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x)) - mu) pow 2)`
    MP_TAC THENL
  [MATCH_MP_TAC EXPECTATION_POS THEN CONJ_TAC THENL
   [EXPAND_TAC "mu" THEN MATCH_MP_TAC ERGODIC_AVG_INTEGRABLE_POW2 THEN
    ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_LE_POW_2]];
   DISCH_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a < e ==> abs a < e`) THEN
  ASM_REWRITE_TAC[] THEN
  (* Main bound: E[(A_n(f)-mu)^2] < e by splitting *)
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `expectation (p:A prob_space)
    (\x:A. &2 * (inv(&(SUC n)) * sum(0..n) (\k. (h:A->real)(ITER k tt x)) -
            expectation p h) pow 2 +
      &2 * (inv(&(SUC n)) * sum(0..n) (\k. (g:A->real)(ITER k tt x)) -
            expectation p g) pow 2)` THEN
  CONJ_TAC THENL
  [(* Pointwise bound via EXPECTATION_MONO *)
   MATCH_MP_TAC EXPECTATION_MONO THEN CONJ_TAC THENL
   [EXPAND_TAC "mu" THEN MATCH_MP_TAC ERGODIC_AVG_INTEGRABLE_POW2 THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC INTEGRABLE_CMUL THEN
    MATCH_MP_TAC ERGODIC_AVG_INTEGRABLE_POW2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
   (* (A_n(f)-mu)^2 <= 2*(A_n(h)-E[h])^2 + 2*(A_n(g)-E[g])^2 *)
   (* Key: A_n(f) - mu = (A_n(h) - E[h]) + (A_n(g) - E[g]) *)
   SUBGOAL_THEN `inv(&(SUC n)) * sum(0..n) (\k. (f:A->real)(ITER k tt x)) - mu =
     (inv(&(SUC n)) * sum(0..n) (\k. (h:A->real)(ITER k tt x)) - expectation p h) +
     (inv(&(SUC n)) * sum(0..n) (\k. (g:A->real)(ITER k tt x)) - expectation p g)`
     SUBST1_TAC THENL
   [SUBGOAL_THEN `!k. (f:A->real)(ITER k (tt:A->A) x) =
     (h:A->real)(ITER k tt x) + (g:A->real)(ITER k tt x)` (fun th ->
       REWRITE_TAC[th]) THENL
    [GEN_TAC THEN EXPAND_TAC "h" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUM_ADD_NUMSEG; REAL_ADD_LDISTRIB] THEN
    SUBGOAL_THEN `mu = expectation (p:A prob_space) (h:A->real) +
      expectation p (g:A->real)` SUBST1_TAC THENL
    [EXPAND_TAC "mu" THEN
     SUBGOAL_THEN `(f:A->real) = (\x:A. h x + g x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN EXPAND_TAC "h" THEN
      REAL_ARITH_TAC;
      ASM_SIMP_TAC[EXPECTATION_ADD]];
     REAL_ARITH_TAC];
    (* (a+b)^2 <= 2*a^2 + 2*b^2 *)
    REWRITE_TAC[SQ_SUM_BOUND]];
   (* Linearity: E[2*a^2 + 2*b^2] = 2*E[a^2] + 2*E[b^2] *)
   SUBGOAL_THEN `integrable (p:A prob_space)
     (\x:A. (inv(&(SUC n)) * sum(0..n) (\k. (h:A->real)(ITER k tt x)) -
             expectation p h) pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC ERGODIC_AVG_INTEGRABLE_POW2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space)
     (\x:A. (inv(&(SUC n)) * sum(0..n) (\k. (g:A->real)(ITER k tt x)) -
             expectation p g) pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC ERGODIC_AVG_INTEGRABLE_POW2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   ASM_SIMP_TAC[EXPECTATION_ADD; INTEGRABLE_CMUL; EXPECTATION_CMUL] THEN
   MATCH_MP_TAC(REAL_ARITH
     `a < e / &4 /\ b < e / &4 ==> &2 * a + &2 * b < e`) THEN
   ASM_REWRITE_TAC[]])
