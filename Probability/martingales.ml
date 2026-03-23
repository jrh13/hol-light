(* ========================================================================= *)
(* Martingale theory: sub-sigma-algebras, filtrations, stopping times,       *)
(* optional stopping, and Doob's maximal inequality.                         *)
(*                                                                           *)
(* Follows Williams "Probability with Martingales" Chapters 8-10.            *)
(* Includes sub-sigma-algebras, conditional expectation for simple RVs,      *)
(* filtrations, martingale definitions, Doob's optional stopping theorem     *)
(* (Fair Games Theorem), submartingale inequalities, and Doob's maximal      *)
(* inequality (both bounded and general versions).                           *)
(* ========================================================================= *)

needs "Probability/expectation.ml";;

(* ========================================================================= *)
(* Sub-sigma-algebras and Conditional Expectation                            *)
(* Following Williams Chapters 8-9                                           *)
(* ========================================================================= *)

(* A sub-sigma-algebra G of a probability space p is a sigma-algebra that
   is contained in the event algebra and has the same carrier *)
let sub_sigma_algebra = new_definition
  `sub_sigma_algebra (p:A prob_space) (G:(A->bool)->bool) <=>
   sigma_algebra G /\
   G SUBSET prob_events p /\
   UNIONS G = prob_carrier p`;;



let SUB_SIGMA_ALGEBRA_CARRIER_IN = prove
 (`!p:A prob_space G.
     sub_sigma_algebra p G ==> prob_carrier p IN G`,
  MESON_TAC[sub_sigma_algebra; SIGMA_ALGEBRA_CARRIER]);;



(* Sub-sigma-algebra events are prob events *)
let SUB_SIGMA_ALGEBRA_IN_EVENTS = prove
 (`!p:A prob_space G a.
     sub_sigma_algebra p G /\ a IN G ==> a IN prob_events p`,
  REWRITE_TAC[sub_sigma_algebra] THEN SET_TAC[]);;

(* G-measurability: X is measurable w.r.t. a sub-sigma-algebra G *)
let measurable_wrt = new_definition
  `measurable_wrt (p:A prob_space) (G:(A->bool)->bool) (X:A->real) <=>
   !v. {x | x IN prob_carrier p /\ X x <= v} IN G`;;

(* G-measurable implies random_variable *)
let MEASURABLE_WRT_IMP_RV = prove
 (`!p:A prob_space G X.
     sub_sigma_algebra p G /\ measurable_wrt p G X
     ==> random_variable p X`,
  REWRITE_TAC[measurable_wrt; random_variable; sub_sigma_algebra] THEN
  SET_TAC[]);;

(* random_variable iff measurable w.r.t. full event algebra *)
let MEASURABLE_WRT_EVENTS = prove
 (`!p:A prob_space X.
     measurable_wrt p (prob_events p) X <=> random_variable p X`,
  REWRITE_TAC[measurable_wrt; random_variable]);;

(* Constant is measurable w.r.t. any sub-sigma-algebra *)
let MEASURABLE_WRT_CONST = prove
 (`!p:A prob_space G c.
     sub_sigma_algebra p G ==> measurable_wrt p G (\x. c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[measurable_wrt] THEN
  X_GEN_TAC `v:real` THEN
  ASM_CASES_TAC `c <= v` THENL
  [SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ c <= v} = prob_carrier p`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[sub_sigma_algebra; SIGMA_ALGEBRA_CARRIER]];
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ c <= v} = {}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN ASM_REAL_ARITH_TAC;
    ASM_MESON_TAC[sub_sigma_algebra; SIGMA_ALGEBRA_EMPTY]]]);;


(* G-measurable simple RV: simple_rv w.r.t. sub-sigma-algebra *)
let simple_rv_wrt = new_definition
  `simple_rv_wrt (p:A prob_space) (G:(A->bool)->bool) (X:A->real) <=>
   measurable_wrt p G X /\
   FINITE {X x | x IN prob_carrier p}`;;


(* simple_rv_wrt implies simple_rv *)
let SIMPLE_RV_WRT_IMP_SIMPLE_RV = prove
 (`!p:A prob_space G X.
     sub_sigma_algebra p G /\ simple_rv_wrt p G X ==> simple_rv p X`,
  REWRITE_TAC[simple_rv_wrt; simple_rv] THEN
  MESON_TAC[MEASURABLE_WRT_IMP_RV]);;

(* Sub-sigma-algebra closure under inter and union *)
let SUB_SIGMA_ALGEBRA_INTER = prove
 (`!p:A prob_space G a b.
     sub_sigma_algebra p G /\ a IN G /\ b IN G ==> a INTER b IN G`,
  MESON_TAC[sub_sigma_algebra; SIGMA_ALGEBRA_INTER]);;

let SUB_SIGMA_ALGEBRA_UNION = prove
 (`!p:A prob_space G a b.
     sub_sigma_algebra p G /\ a IN G /\ b IN G ==> a UNION b IN G`,
  MESON_TAC[sub_sigma_algebra; SIGMA_ALGEBRA_UNION]);;

let SUB_SIGMA_ALGEBRA_DIFF = prove
 (`!p:A prob_space G a b.
     sub_sigma_algebra p G /\ a IN G /\ b IN G ==> a DIFF b IN G`,
  MESON_TAC[sub_sigma_algebra; SIGMA_ALGEBRA_DIFF]);;

let SUB_SIGMA_ALGEBRA_COMPL = prove
 (`!p:A prob_space G a.
     sub_sigma_algebra p G /\ a IN G ==> (prob_carrier p DIFF a) IN G`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `prob_carrier (p:A prob_space) = UNIONS G` SUBST1_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  ASM_MESON_TAC[sub_sigma_algebra; SIGMA_ALGEBRA_COMPL]);;

(* ========================================================================= *)
(* Filtrations and Martingales                                               *)
(* ========================================================================= *)

(* A filtration is an increasing sequence of sub-sigma-algebras *)
let filtration = new_definition
  `filtration (p:A prob_space) (FF:num->(A->bool)->bool) <=>
   (!n. sub_sigma_algebra p (FF n)) /\
   (!m n. m <= n ==> FF m SUBSET FF n)`;;

(* A process X is adapted to a filtration FF if X_n is FF_n-measurable *)
let adapted = new_definition
  `adapted (p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real) <=>
   !n. measurable_wrt p (FF n) (X n)`;;

(* A process X is a simple adapted process *)
let simple_adapted = new_definition
  `simple_adapted (p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real) <=>
   adapted p FF X /\
   (!n. FINITE {X n x | x IN prob_carrier p})`;;

(* Natural filtration generated by a sequence of random variables *)
let natural_filtration = new_definition
  `natural_filtration (p:A prob_space) (X:num->A->real) (n:num) =
   sigma_generated (prob_carrier p)
     (UNIONS (IMAGE (\k. {{x | x IN prob_carrier p /\ X k x <= v} | v IN (:real)}) (0..n)))`;;

(* A martingale w.r.t. filtration FF *)
let martingale = new_definition
  `martingale (p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real) <=>
   filtration p FF /\
   simple_adapted p FF X /\
   (!n. simple_rv p (X n)) /\
   (!n a. a IN FF n
     ==> simple_expectation p (\x. X (SUC n) x * indicator_fn a x) =
         simple_expectation p (\x. X n x * indicator_fn a x))`;;

(* A submartingale w.r.t. filtration FF *)
let submartingale = new_definition
  `submartingale (p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real) <=>
   filtration p FF /\
   simple_adapted p FF X /\
   (!n. simple_rv p (X n)) /\
   (!n a. a IN FF n
     ==> simple_expectation p (\x. X n x * indicator_fn a x) <=
         simple_expectation p (\x. X (SUC n) x * indicator_fn a x))`;;

(* A supermartingale w.r.t. filtration FF *)
let supermartingale = new_definition
  `supermartingale (p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real) <=>
   filtration p FF /\
   simple_adapted p FF X /\
   (!n. simple_rv p (X n)) /\
   (!n a. a IN FF n
     ==> simple_expectation p (\x. X (SUC n) x * indicator_fn a x) <=
         simple_expectation p (\x. X n x * indicator_fn a x))`;;

(* Every martingale is both a sub- and super-martingale *)
let MARTINGALE_IMP_SUBMARTINGALE = prove
 (`!p:A prob_space FF X.
     martingale p FF X ==> submartingale p FF X`,
  REWRITE_TAC[martingale; submartingale] THEN
  MESON_TAC[REAL_LE_REFL]);;

let MARTINGALE_IMP_SUPERMARTINGALE = prove
 (`!p:A prob_space FF X.
     martingale p FF X ==> supermartingale p FF X`,
  REWRITE_TAC[martingale; supermartingale] THEN
  MESON_TAC[REAL_LE_REFL]);;

(* X is a martingale iff it is both sub- and super-martingale *)
let MARTINGALE_SUB_SUPER = prove
 (`!p:A prob_space FF X.
     martingale p FF X <=>
     submartingale p FF X /\ supermartingale p FF X`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [MESON_TAC[MARTINGALE_IMP_SUBMARTINGALE; MARTINGALE_IMP_SUPERMARTINGALE];
   REWRITE_TAC[submartingale; supermartingale; martingale] THEN
   MESON_TAC[REAL_LE_ANTISYM]]);;


let FILTRATION_MONO = prove
 (`!p:A prob_space FF m n.
     filtration p FF /\ m <= n ==> FF m SUBSET FF n`,
  SIMP_TAC[filtration]);;

(* Constant sequence is a martingale *)
let MARTINGALE_CONST = prove
 (`!p:A prob_space FF c.
     filtration p FF
     ==> martingale p FF (\n x. c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[martingale] THEN
  TRY BETA_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [REWRITE_TAC[simple_adapted; adapted] THEN
   TRY BETA_TAC THEN CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC MEASURABLE_WRT_CONST THEN
    ASM_MESON_TAC[filtration];
    SUBGOAL_THEN `{(c:real) | x | x IN prob_carrier (p:A prob_space)} SUBSET {c}`
      (fun th -> MESON_TAC[th; FINITE_SUBSET; FINITE_SING]) THEN
    SET_TAC[]];
   REWRITE_TAC[SIMPLE_RV_CONST]]);;


(* Stopping time definition *)
let stopping_time = new_definition
  `stopping_time (p:A prob_space) (FF:num->(A->bool)->bool) (tau:A->num) <=>
   !n. {x | x IN prob_carrier p /\ tau x <= n} IN FF n`;;

(* Bounded stopping time *)
let bounded_stopping_time = new_definition
  `bounded_stopping_time (p:A prob_space) (FF:num->(A->bool)->bool) (tau:A->num) (N:num) <=>
   stopping_time p FF tau /\
   (!x. x IN prob_carrier p ==> tau x <= N)`;;

(* E[X_n] = E[X_0] for martingales *)
let MARTINGALE_EXPECTATION_CONST = prove
 (`!p:A prob_space FF X.
     martingale p FF X
     ==> !n. simple_expectation p (X n) = simple_expectation p (X 0)`,
  REWRITE_TAC[martingale] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
    `simple_expectation p ((X:num->A->real) (SUC n)) =
     simple_expectation p (X n)` (fun th -> ASM_REWRITE_TAC[th]) THEN
  ONCE_REWRITE_TAC[GSYM SIMPLE_EXPECTATION_MUL_INDICATOR_CARRIER] THEN
  SUBGOAL_THEN `prob_carrier (p:A prob_space) IN FF (n:num)` ASSUME_TAC THENL
  [ASM_MESON_TAC[filtration; SUB_SIGMA_ALGEBRA_CARRIER_IN]; ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

(* E[X_n] <= E[X_{n+1}] for submartingales *)
let SUBMARTINGALE_EXPECTATION_MONO = prove
 (`!p:A prob_space FF X.
     submartingale p FF X
     ==> !n. simple_expectation p (X n) <= simple_expectation p (X (SUC n))`,
  REWRITE_TAC[submartingale] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM SIMPLE_EXPECTATION_MUL_INDICATOR_CARRIER] THEN
  SUBGOAL_THEN `prob_carrier (p:A prob_space) IN FF (n:num)` ASSUME_TAC THENL
  [ASM_MESON_TAC[filtration; SUB_SIGMA_ALGEBRA_CARRIER_IN]; ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

(* E[X_{n+1}] <= E[X_n] for supermartingales *)
let SUPERMARTINGALE_EXPECTATION_MONO = prove
 (`!p:A prob_space FF X.
     supermartingale p FF X
     ==> !n. simple_expectation p (X (SUC n)) <= simple_expectation p (X n)`,
  REWRITE_TAC[supermartingale] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM SIMPLE_EXPECTATION_MUL_INDICATOR_CARRIER] THEN
  SUBGOAL_THEN `prob_carrier (p:A prob_space) IN FF (n:num)` ASSUME_TAC THENL
  [ASM_MESON_TAC[filtration; SUB_SIGMA_ALGEBRA_CARRIER_IN]; ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

(* E[X_0] <= E[X_n] for submartingales (by induction) *)
let SUBMARTINGALE_EXPECTATION_INCREASING = prove
 (`!p:A prob_space FF X.
     submartingale p FF X
     ==> !m n. m <= n ==> simple_expectation p (X m) <= simple_expectation p (X n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?k. n = m + k:num` CHOOSE_TAC THENL
  [EXISTS_TAC `n - m:num` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC (`k:num`, `j:num`) THEN INDUCT_TAC THENL
  [REWRITE_TAC[ADD_CLAUSES] THEN REAL_ARITH_TAC;
   REWRITE_TAC[ADD_CLAUSES] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `simple_expectation p ((X:num->A->real) (m + j))` THEN
   CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MP_TAC (SPEC `m + j:num` (MATCH_MP SUBMARTINGALE_EXPECTATION_MONO
      (ASSUME `submartingale (p:A prob_space) FF (X:num->A->real)`))) THEN
    SIMP_TAC[]]]);;

(* E[X_n] <= E[X_0] for supermartingales (by induction) *)
let SUPERMARTINGALE_EXPECTATION_DECREASING = prove
 (`!p:A prob_space FF X.
     supermartingale p FF X
     ==> !m n. m <= n ==> simple_expectation p (X n) <= simple_expectation p (X m)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?k. n = m + k:num` CHOOSE_TAC THENL
  [EXISTS_TAC `n - m:num` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC (`k:num`, `j:num`) THEN INDUCT_TAC THENL
  [REWRITE_TAC[ADD_CLAUSES] THEN REAL_ARITH_TAC;
   REWRITE_TAC[ADD_CLAUSES] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `simple_expectation p ((X:num->A->real) (m + j))` THEN
   CONJ_TAC THENL
   [MP_TAC (SPEC `m + j:num` (MATCH_MP SUPERMARTINGALE_EXPECTATION_MONO
      (ASSUME `supermartingale (p:A prob_space) FF (X:num->A->real)`))) THEN
    SIMP_TAC[];
    ASM_REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* Conditional Expectation for Simple RVs                                    *)
(* ========================================================================= *)

(* Conditional expectation of X given sub-sigma-algebra G:
   The unique G-measurable simple RV Y such that for all A in G,
   E[Y * 1_A] = E[X * 1_A].
   We define it constructively for simple RVs. *)

(* First: a key property - martingale condition restated *)
let MARTINGALE_COND_EXP = prove
 (`!p:A prob_space FF X.
     martingale p FF X
     ==> !n a. a IN FF n
         ==> simple_expectation p (\x. X (SUC n) x * indicator_fn a x) =
             simple_expectation p (\x. X n x * indicator_fn a x)`,
  REWRITE_TAC[martingale] THEN MESON_TAC[]);;

(* Martingale transform: if X is a martingale and H is predictable & bounded,
   then (H . X)_n = sum_{i=0}^{n-1} H_i * (X_{i+1} - X_i) is a martingale.
   For simple setup, we define the transform directly. *)

(* Martingale transform definition *)
let martingale_transform = new_definition
  `martingale_transform (H:num->A->real) (X:num->A->real) (n:num) (x:A) =
   sum(0..n-1) (\i. H i x * (X (i + 1) x - X i x))`;;

(* Predictable process: H_n is FF_{n-1}-measurable for n >= 1,
   and H_0 is FF_0-measurable *)
let predictable = new_definition
  `predictable (p:A prob_space) (FF:num->(A->bool)->bool) (H:num->A->real) <=>
   simple_rv_wrt p (FF 0) (H 0) /\
   (!n. simple_rv_wrt p (FF n) (H (SUC n)))`;;

(* Stopped process *)
let stopped_process = new_definition
  `stopped_process (X:num->A->real) (tau:A->num) (n:num) (x:A) =
   X (MIN n (tau x)) x`;;

(* ========================================================================= *)
(* Doob's Optional Stopping Theorem (bounded case)                           *)
(* ========================================================================= *)

(* Key theorem: For a martingale X and bounded stopping times sigma <= tau <= N,
   E[X_tau] = E[X_sigma] = E[X_0].
   The simplest case: E[X_{tau /\ n}] = E[X_0] for all n.

   Proof approach: X^tau_n = X_0 + sum_{i=0}^{n-1} 1_{tau > i} * (X_{i+1} - X_i)
   The indicator 1_{tau > i} is FF_i-measurable (since {tau > i} = Omega \ {tau <= i}
   and {tau <= i} IN FF_i by the stopping time property).
   So X^tau is a martingale transform, and E[X^tau_n] = E[X_0]. *)

(* First: indicator of {tau > n} is FF_n-measurable *)
let STOPPING_TIME_INDICATOR_PREDICTABLE = prove
 (`!p:A prob_space FF tau.
     stopping_time p FF tau /\ filtration p FF
     ==> !n. {x | x IN prob_carrier p /\ tau x > n} IN FF n`,
  REWRITE_TAC[stopping_time; filtration] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_TAC THEN
  SUBGOAL_THEN
    `prob_carrier (p:A prob_space) DIFF
     {x | x IN prob_carrier p /\ (tau:A->num) x <= n} IN
     (FF:num->(A->bool)->bool) n` MP_TAC THENL
  [MATCH_MP_TAC SUB_SIGMA_ALGEBRA_COMPL THEN
   ASM_REWRITE_TAC[];
   MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN
   X_GEN_TAC `y:A` THEN
   ASM_CASES_TAC `(y:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
   ARITH_TAC]);;

(* Base case for stopped process *)
let STOPPED_PROCESS_ZERO = prove
 (`!X:num->A->real tau x. stopped_process X tau 0 x = X 0 x`,
  REWRITE_TAC[stopped_process; MIN; LE_0]);;

(* One-step increment of the stopped process *)
let STOPPED_PROCESS_INCREMENT = prove
 (`!X:num->A->real tau n x.
     stopped_process X tau (SUC n) x - stopped_process X tau n x =
     if tau x > n then X (SUC n) x - X n x else &0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[stopped_process] THEN
  ASM_CASES_TAC `(tau:A->num) x > n` THENL
  [ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `MIN (SUC n) ((tau:A->num) x) = SUC n` SUBST1_TAC THENL
   [REWRITE_TAC[MIN] THEN ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `MIN n ((tau:A->num) x) = n` SUBST1_TAC THENL
   [REWRITE_TAC[MIN] THEN ASM_ARITH_TAC; ALL_TAC] THEN
   REAL_ARITH_TAC;
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `MIN (SUC n) ((tau:A->num) x) = (tau:A->num) x` SUBST1_TAC THENL
   [REWRITE_TAC[MIN] THEN ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `MIN n ((tau:A->num) x) = (tau:A->num) x` SUBST1_TAC THENL
   [REWRITE_TAC[MIN] THEN ASM_ARITH_TAC; ALL_TAC] THEN
   REAL_ARITH_TAC]);;

(* Indicator of {tau > n} is a simple_rv when tau is a stopping time *)
let SIMPLE_RV_STOPPING_TIME_INDICATOR = prove
 (`!p:A prob_space FF tau.
     stopping_time p FF tau /\ filtration p FF
     ==> !n. simple_rv p
              (indicator_fn {x | x IN prob_carrier p /\ tau x > n})`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
  SUBGOAL_THEN
    `{x | x IN prob_carrier (p:A prob_space) /\ (tau:A->num) x > n} IN
     prob_events p`
    (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN
    `{x | x IN prob_carrier (p:A prob_space) /\ (tau:A->num) x > n} IN
     (FF:num->(A->bool)->bool) n` MP_TAC THENL
  [ASM_SIMP_TAC[STOPPING_TIME_INDICATOR_PREDICTABLE];
   DISCH_TAC THEN
   SUBGOAL_THEN `sub_sigma_algebra (p:A prob_space) ((FF:num->(A->bool)->bool) n)`
     MP_TAC THENL
   [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
   REWRITE_TAC[sub_sigma_algebra] THEN
   ASM SET_TAC[]]);;

(* simple_rv is preserved under extensional equality on carrier *)
let SIMPLE_RV_EXT = prove
 (`!p:A prob_space f g.
     (!x. x IN prob_carrier p ==> f x = g x) /\ simple_rv p g
     ==> simple_rv p f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simple_rv; random_variable] THEN
  STRIP_TAC THEN CONJ_TAC THENL
  [X_GEN_TAC `a:real` THEN
   SUBGOAL_THEN `{x | x IN prob_carrier (p:A prob_space) /\ (f:A->real) x <= a} =
     {x | x IN prob_carrier p /\ (g:A->real) x <= a}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[]];
   SUBGOAL_THEN `{(f:A->real) x | x IN prob_carrier (p:A prob_space)} =
     {(g:A->real) x | x IN prob_carrier p}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[]]]);;

(* The stopped process is a simple_rv at every time step *)
let SIMPLE_RV_STOPPED_PROCESS = prove
 (`!p:A prob_space FF X tau.
     (!n. simple_rv p (X n)) /\ stopping_time p FF tau /\ filtration p FF
     ==> !n. simple_rv p (stopped_process X tau n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  INDUCT_TAC THENL
  [(* Base: stopped_process X tau 0 = X 0 *)
   SUBGOAL_THEN `stopped_process (X:num->A->real) (tau:A->num) 0 = X 0`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; STOPPED_PROCESS_ZERO]; ASM_REWRITE_TAC[]];
   (* Inductive step: use extensionality on carrier *)
   MATCH_MP_TAC SIMPLE_RV_EXT THEN
   EXISTS_TAC `\x:A. stopped_process (X:num->A->real) (tau:A->num) n x +
     ((X (SUC n) x - X n x) *
      indicator_fn {y | y IN prob_carrier (p:A prob_space) /\ tau y > n} x)` THEN
   CONJ_TAC THENL
   [(* Pointwise identity on carrier *)
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(SPECL [`(X:num->A->real)`; `(tau:A->num)`; `n:num`; `x:A`]
      STOPPED_PROCESS_INCREMENT) THEN
    REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    (* simple_rv for the sum *)
    MATCH_MP_TAC SIMPLE_RV_ADD THEN REWRITE_TAC[ETA_AX] THEN
    CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC SIMPLE_RV_SUB THEN REWRITE_TAC[ETA_AX] THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[SIMPLE_RV_STOPPING_TIME_INDICATOR]]]]]);;


(* Doob's Optional Stopping Theorem (bounded case),
   also known as the "Fair Games Theorem" (Williams, Ch.10):
   For a martingale X and bounded stopping time tau,
   E[X^tau_n] = E[X_0] for all n. *)
let DOOB_OPTIONAL_STOPPING_BOUNDED = prove
 (`!p:A prob_space FF X tau N.
     martingale p FF X /\ bounded_stopping_time p FF tau N
     ==> !n. simple_expectation p (stopped_process X tau n) =
             simple_expectation p (X 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Extract key properties from martingale *)
  SUBGOAL_THEN `filtration (p:A prob_space) (FF:num->(A->bool)->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[martingale]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. simple_rv (p:A prob_space) ((X:num->A->real) n)`
    ASSUME_TAC THENL [ASM_MESON_TAC[martingale]; ALL_TAC] THEN
  SUBGOAL_THEN
    `!n a. a IN (FF:num->(A->bool)->bool) n
     ==> simple_expectation (p:A prob_space)
           (\x. (X:num->A->real) (SUC n) x * indicator_fn a x) =
         simple_expectation p (\x. X n x * indicator_fn a x)`
    ASSUME_TAC THENL [ASM_MESON_TAC[martingale]; ALL_TAC] THEN
  SUBGOAL_THEN `stopping_time (p:A prob_space) FF (tau:A->num)` ASSUME_TAC THENL
  [ASM_MESON_TAC[bounded_stopping_time]; ALL_TAC] THEN
  INDUCT_TAC THENL
  [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; STOPPED_PROCESS_ZERO];
   (* Inductive step: E[X^tau_{SUC n}] = E[X^tau_n] = E[X_0] *)
   ASM_REWRITE_TAC[] THEN
   (* Establish {tau > n} IN FF n *)
   SUBGOAL_THEN
     `{x | x IN prob_carrier (p:A prob_space) /\ (tau:A->num) x > n} IN
      (FF:num->(A->bool)->bool) n`
     ASSUME_TAC THENL
   [ASM_SIMP_TAC[STOPPING_TIME_INDICATOR_PREDICTABLE]; ALL_TAC] THEN
   (* Apply the martingale property: E[X_{n+1} * 1_{tau>n}] = E[X_n * 1_{tau>n}] *)
   SUBGOAL_THEN
     `simple_expectation (p:A prob_space)
       (\x. (X:num->A->real) (SUC n) x *
            indicator_fn {y | y IN prob_carrier p /\ (tau:A->num) y > n} x) =
      simple_expectation p
       (\x. X n x * indicator_fn {y | y IN prob_carrier p /\ tau y > n} x)`
     ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
   (* Show (X_{n+1} - X_n) * 1_{tau>n} has zero expectation.
      Uses: (a - b) * c = a * c - b * c pointwise, E[SUB] = E[] - E[],
      and martingale property for {tau > n} IN FF n. *)
   SUBGOAL_THEN
     `simple_expectation (p:A prob_space) (\x. (X (SUC n) x - X n x) *
        indicator_fn {y | y IN prob_carrier p /\ (tau:A->num) y > n} x) = &0`
     ASSUME_TAC THENL
   [(* Prove E[(X_{n+1} - X_n) * 1_{tau>n}] = 0 *)
    (* Rewrite (a-b)*c as a*c - b*c pointwise *)
    SUBGOAL_THEN
      `simple_expectation (p:A prob_space)
        (\x. ((X:num->A->real) (SUC n) x - X n x) *
           indicator_fn {y | y IN prob_carrier p /\ (tau:A->num) y > n} x) =
       simple_expectation p
        (\x. X (SUC n) x *
           indicator_fn {y | y IN prob_carrier p /\ tau y > n} x -
           X n x * indicator_fn {y | y IN prob_carrier p /\ tau y > n} x)`
      SUBST1_TAC THENL
    [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
     SPEC_TAC (`indicator_fn {y | y IN prob_carrier (p:A prob_space) /\
       (tau:A->num) y > n} (x:A)`, `c:real`) THEN
     REAL_ARITH_TAC; ALL_TAC] THEN
    (* Establish simple_rv for products *)
    SUBGOAL_THEN `simple_rv (p:A prob_space)
      (\x. (X:num->A->real) (SUC n) x *
           indicator_fn {y | y IN prob_carrier p /\ (tau:A->num) y > n} x)`
      ASSUME_TAC THENL
    [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
     CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_MESON_TAC[SIMPLE_RV_STOPPING_TIME_INDICATOR]]; ALL_TAC] THEN
    SUBGOAL_THEN `simple_rv (p:A prob_space)
      (\x. (X:num->A->real) n x *
           indicator_fn {y | y IN prob_carrier p /\ (tau:A->num) y > n} x)`
      ASSUME_TAC THENL
    [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
     CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_MESON_TAC[SIMPLE_RV_STOPPING_TIME_INDICATOR]]; ALL_TAC] THEN
    (* Apply SIMPLE_EXPECTATION_SUB *)
    SUBGOAL_THEN
      `simple_expectation (p:A prob_space)
        (\x. (X:num->A->real) (SUC n) x *
           indicator_fn {y | y IN prob_carrier p /\ (tau:A->num) y > n} x -
           X n x * indicator_fn {y | y IN prob_carrier p /\ tau y > n} x) =
       simple_expectation p
        (\x. X (SUC n) x *
           indicator_fn {y | y IN prob_carrier p /\ tau y > n} x) -
       simple_expectation p
        (\x. X n x *
           indicator_fn {y | y IN prob_carrier p /\ tau y > n} x)`
      SUBST1_TAC THENL
    [MATCH_MP_TAC SIMPLE_EXPECTATION_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL];
    (* Now combine: E[X^tau_{SUC n}] = E[X^tau_n] + 0 = E[X^tau_n] *)
    (* E[X^tau_{SUC n}] = E[X^tau_n + increment] = E[X^tau_n] + E[increment] *)
    SUBGOAL_THEN
      `simple_expectation (p:A prob_space)
        (stopped_process (X:num->A->real) (tau:A->num) (SUC n)) =
       simple_expectation p (stopped_process X tau n) +
       simple_expectation p (\x. (X (SUC n) x - X n x) *
         indicator_fn {y | y IN prob_carrier p /\ tau y > n} x)`
      SUBST1_TAC THENL
    [(* Prove E[X^tau_{n+1}] = E[X^tau_n] + E[increment] *)
     (* Step 1: Rewrite via pointwise identity on carrier *)
     SUBGOAL_THEN
       `simple_expectation (p:A prob_space)
         (stopped_process (X:num->A->real) (tau:A->num) (SUC n)) =
        simple_expectation p (\x. stopped_process X tau n x +
          (X (SUC n) x - X n x) *
          indicator_fn {y | y IN prob_carrier p /\ tau y > n} x)`
       SUBST1_TAC THENL
     [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
      MP_TAC(SPECL [`(X:num->A->real)`; `(tau:A->num)`; `n:num`; `x:A`]
        STOPPED_PROCESS_INCREMENT) THEN
      REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
     (* Step 2: Apply SIMPLE_EXPECTATION_ADD *)
     MP_TAC(BETA_RULE(ISPECL [`p:A prob_space`;
       `stopped_process (X:num->A->real) (tau:A->num) n`;
       `\x:A. ((X:num->A->real) (SUC n) x - X n x) *
         indicator_fn {y | y IN prob_carrier (p:A prob_space) /\
           (tau:A->num) y > n} x`]
       SIMPLE_EXPECTATION_ADD)) THEN
     ANTS_TAC THENL
     [CONJ_TAC THENL
      [ASM_MESON_TAC[SIMPLE_RV_STOPPED_PROCESS];
       MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC SIMPLE_RV_SUB THEN REWRITE_TAC[ETA_AX] THEN
        ASM_REWRITE_TAC[];
        ASM_MESON_TAC[SIMPLE_RV_STOPPING_TIME_INDICATOR]]];
      SIMP_TAC[]];
     ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]]]);;

(* ========================================================================= *)
(* Submartingale inequalities                                                *)
(* ========================================================================= *)


(* Submartingale optional stopping: lower bound.
   For a submartingale, E[X_0] <= E[X^tau_n] for all n. *)
let SUBMARTINGALE_OPTIONAL_STOPPING_GE = prove
 (`!p:A prob_space FF X tau N.
     submartingale p FF X /\ bounded_stopping_time p FF tau N
     ==> !n. simple_expectation p (X 0) <=
             simple_expectation p (stopped_process X tau n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Extract key properties from submartingale *)
  SUBGOAL_THEN `filtration (p:A prob_space) (FF:num->(A->bool)->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. simple_rv (p:A prob_space) ((X:num->A->real) n)`
    ASSUME_TAC THENL [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `stopping_time (p:A prob_space) FF (tau:A->num)` ASSUME_TAC THENL
  [ASM_MESON_TAC[bounded_stopping_time]; ALL_TAC] THEN
  INDUCT_TAC THENL
  [(* Base case: E[X_0] <= E[X^tau_0], both sides are equal *)
   SUBGOAL_THEN `simple_expectation (p:A prob_space)
     (stopped_process (X:num->A->real) (tau:A->num) 0) =
     simple_expectation p (X 0)`
     (fun th -> REWRITE_TAC[th; REAL_LE_REFL]) THEN
   AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; STOPPED_PROCESS_ZERO];
   (* Inductive step: E[X_0] <= E[X^tau_n] <= E[X^tau_{SUC n}] *)
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `simple_expectation (p:A prob_space)
     (stopped_process (X:num->A->real) (tau:A->num) n)` THEN
   CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    (* Show E[X^tau_n] <= E[X^tau_{SUC n}] *)
    (* Step 1: Decompose E[X^tau_{SUC n}] = E[X^tau_n] + E[increment] *)
    SUBGOAL_THEN
      `simple_expectation (p:A prob_space)
        (stopped_process (X:num->A->real) (tau:A->num) (SUC n)) =
       simple_expectation p (stopped_process X tau n) +
       simple_expectation p (\x. (X (SUC n) x - X n x) *
         indicator_fn {y | y IN prob_carrier p /\ tau y > n} x)`
      SUBST1_TAC THENL
    [(* Pointwise identity on carrier *)
     SUBGOAL_THEN
       `simple_expectation (p:A prob_space)
         (stopped_process (X:num->A->real) (tau:A->num) (SUC n)) =
        simple_expectation p (\x. stopped_process X tau n x +
          (X (SUC n) x - X n x) *
          indicator_fn {y | y IN prob_carrier p /\ tau y > n} x)`
       SUBST1_TAC THENL
     [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
      MP_TAC(SPECL [`(X:num->A->real)`; `(tau:A->num)`; `n:num`; `x:A`]
        STOPPED_PROCESS_INCREMENT) THEN
      REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
     (* Apply SIMPLE_EXPECTATION_ADD *)
     MP_TAC(BETA_RULE(ISPECL [`p:A prob_space`;
       `stopped_process (X:num->A->real) (tau:A->num) n`;
       `\x:A. ((X:num->A->real) (SUC n) x - X n x) *
         indicator_fn {y | y IN prob_carrier (p:A prob_space) /\
           (tau:A->num) y > n} x`]
       SIMPLE_EXPECTATION_ADD)) THEN
     ANTS_TAC THENL
     [CONJ_TAC THENL
      [ASM_MESON_TAC[SIMPLE_RV_STOPPED_PROCESS];
       MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC SIMPLE_RV_SUB THEN REWRITE_TAC[ETA_AX] THEN
        ASM_REWRITE_TAC[];
        ASM_MESON_TAC[SIMPLE_RV_STOPPING_TIME_INDICATOR]]];
      SIMP_TAC[]];
     (* Step 2: Show E[increment] >= 0, i.e. &0 <= E[(X_{n+1}-X_n)*1_{tau>n}] *)
     MATCH_MP_TAC(REAL_ARITH `&0 <= c ==> a <= a + c`) THEN
     (* Prove E[increment] >= 0 using submartingale property *)
     (* Step A: Rewrite (a-b)*c as a*c - b*c pointwise *)
     SUBGOAL_THEN
       `simple_expectation (p:A prob_space)
         (\x. ((X:num->A->real) (SUC n) x - X n x) *
            indicator_fn {y | y IN prob_carrier p /\ (tau:A->num) y > n} x) =
        simple_expectation p
         (\x. X (SUC n) x *
            indicator_fn {y | y IN prob_carrier p /\ tau y > n} x -
            X n x * indicator_fn {y | y IN prob_carrier p /\ tau y > n} x)`
       SUBST1_TAC THENL
     [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
      SPEC_TAC (`indicator_fn {y | y IN prob_carrier (p:A prob_space) /\
        (tau:A->num) y > n} (x:A)`, `c:real`) THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
     (* Establish simple_rv for products *)
     SUBGOAL_THEN `simple_rv (p:A prob_space)
       (\x. (X:num->A->real) (SUC n) x *
            indicator_fn {y | y IN prob_carrier p /\ (tau:A->num) y > n} x)`
       ASSUME_TAC THENL
     [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
      CONJ_TAC THENL
      [ASM_REWRITE_TAC[];
       ASM_MESON_TAC[SIMPLE_RV_STOPPING_TIME_INDICATOR]]; ALL_TAC] THEN
     SUBGOAL_THEN `simple_rv (p:A prob_space)
       (\x. (X:num->A->real) n x *
            indicator_fn {y | y IN prob_carrier p /\ (tau:A->num) y > n} x)`
       ASSUME_TAC THENL
     [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
      CONJ_TAC THENL
      [ASM_REWRITE_TAC[];
       ASM_MESON_TAC[SIMPLE_RV_STOPPING_TIME_INDICATOR]]; ALL_TAC] THEN
     (* Step B: Apply SIMPLE_EXPECTATION_SUB *)
     SUBGOAL_THEN
       `simple_expectation (p:A prob_space)
         (\x. (X:num->A->real) (SUC n) x *
            indicator_fn {y | y IN prob_carrier p /\ (tau:A->num) y > n} x -
            X n x * indicator_fn {y | y IN prob_carrier p /\ tau y > n} x) =
        simple_expectation p
         (\x. X (SUC n) x *
            indicator_fn {y | y IN prob_carrier p /\ tau y > n} x) -
        simple_expectation p
         (\x. X n x *
            indicator_fn {y | y IN prob_carrier p /\ tau y > n} x)`
       SUBST1_TAC THENL
     [MATCH_MP_TAC SIMPLE_EXPECTATION_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     (* Step C: &0 <= E[a*c] - E[b*c] iff E[b*c] <= E[a*c] *)
     REWRITE_TAC[REAL_SUB_LE] THEN
     SUBGOAL_THEN
       `{x | x IN prob_carrier (p:A prob_space) /\ (tau:A->num) x > n} IN
        (FF:num->(A->bool)->bool) n`
       ASSUME_TAC THENL
     [ASM_SIMP_TAC[STOPPING_TIME_INDICATOR_PREDICTABLE]; ALL_TAC] THEN
     (* Extract one-step submartingale inequality and apply *)
     SUBGOAL_THEN
       `!n' (a:A->bool). a IN (FF:num->(A->bool)->bool) n' ==>
        simple_expectation (p:A prob_space)
          (\x. (X:num->A->real) n' x * indicator_fn a x) <=
        simple_expectation p (\x. X (SUC n') x * indicator_fn a x)`
       ASSUME_TAC THENL
     [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]]);;
(* Supermartingale optional stopping: upper bound.
   For a supermartingale, E[X^tau_n] <= E[X_0] for all n. *)
let SUPERMARTINGALE_OPTIONAL_STOPPING_LE = prove
 (`!p:A prob_space FF X tau N.
     supermartingale p FF X /\ bounded_stopping_time p FF tau N
     ==> !n. simple_expectation p (stopped_process X tau n) <=
             simple_expectation p (X 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Extract key properties from supermartingale *)
  SUBGOAL_THEN `filtration (p:A prob_space) (FF:num->(A->bool)->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[supermartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. simple_rv (p:A prob_space) ((X:num->A->real) n)`
    ASSUME_TAC THENL [ASM_MESON_TAC[supermartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `stopping_time (p:A prob_space) FF (tau:A->num)` ASSUME_TAC THENL
  [ASM_MESON_TAC[bounded_stopping_time]; ALL_TAC] THEN
  INDUCT_TAC THENL
  [(* Base case: E[X^tau_0] <= E[X_0], both sides are equal *)
   SUBGOAL_THEN `simple_expectation (p:A prob_space)
     (stopped_process (X:num->A->real) (tau:A->num) 0) =
     simple_expectation p (X 0)`
     (fun th -> REWRITE_TAC[th; REAL_LE_REFL]) THEN
   AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; STOPPED_PROCESS_ZERO];
   (* Inductive step: E[X^tau_{SUC n}] <= E[X^tau_n] <= E[X_0] *)
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `simple_expectation (p:A prob_space)
     (stopped_process (X:num->A->real) (tau:A->num) n)` THEN
   CONJ_TAC THENL
   [(* Show E[X^tau_{SUC n}] <= E[X^tau_n] *)
    (* Decompose: E[X^tau_{SUC n}] = E[X^tau_n] + E[increment] *)
    SUBGOAL_THEN
      `simple_expectation (p:A prob_space)
        (stopped_process (X:num->A->real) (tau:A->num) (SUC n)) =
       simple_expectation p (stopped_process X tau n) +
       simple_expectation p (\x. (X (SUC n) x - X n x) *
         indicator_fn {y | y IN prob_carrier p /\ tau y > n} x)`
      SUBST1_TAC THENL
    [(* Pointwise identity on carrier *)
     SUBGOAL_THEN
       `simple_expectation (p:A prob_space)
         (stopped_process (X:num->A->real) (tau:A->num) (SUC n)) =
        simple_expectation p (\x. stopped_process X tau n x +
          (X (SUC n) x - X n x) *
          indicator_fn {y | y IN prob_carrier p /\ tau y > n} x)`
       SUBST1_TAC THENL
     [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
      MP_TAC(SPECL [`(X:num->A->real)`; `(tau:A->num)`; `n:num`; `x:A`]
        STOPPED_PROCESS_INCREMENT) THEN
      REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
     MP_TAC(BETA_RULE(ISPECL [`p:A prob_space`;
       `stopped_process (X:num->A->real) (tau:A->num) n`;
       `\x:A. ((X:num->A->real) (SUC n) x - X n x) *
         indicator_fn {y | y IN prob_carrier (p:A prob_space) /\
           (tau:A->num) y > n} x`]
       SIMPLE_EXPECTATION_ADD)) THEN
     ANTS_TAC THENL
     [CONJ_TAC THENL
      [ASM_MESON_TAC[SIMPLE_RV_STOPPED_PROCESS];
       MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC SIMPLE_RV_SUB THEN REWRITE_TAC[ETA_AX] THEN
        ASM_REWRITE_TAC[];
        ASM_MESON_TAC[SIMPLE_RV_STOPPING_TIME_INDICATOR]]];
      SIMP_TAC[]];
     (* Show E[increment] <= 0, i.e. E[(X_{n+1}-X_n)*1_{tau>n}] <= 0 *)
     MATCH_MP_TAC(REAL_ARITH `c <= &0 ==> a + c <= a`) THEN
     (* Rewrite (a-b)*c as a*c - b*c *)
     SUBGOAL_THEN
       `simple_expectation (p:A prob_space)
         (\x. ((X:num->A->real) (SUC n) x - X n x) *
            indicator_fn {y | y IN prob_carrier p /\ (tau:A->num) y > n} x) =
        simple_expectation p
         (\x. X (SUC n) x *
            indicator_fn {y | y IN prob_carrier p /\ tau y > n} x -
            X n x * indicator_fn {y | y IN prob_carrier p /\ tau y > n} x)`
       SUBST1_TAC THENL
     [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
      SPEC_TAC (`indicator_fn {y | y IN prob_carrier (p:A prob_space) /\
        (tau:A->num) y > n} (x:A)`, `c:real`) THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `simple_rv (p:A prob_space)
       (\x. (X:num->A->real) (SUC n) x *
            indicator_fn {y | y IN prob_carrier p /\ (tau:A->num) y > n} x)`
       ASSUME_TAC THENL
     [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
      CONJ_TAC THENL
      [ASM_REWRITE_TAC[];
       ASM_MESON_TAC[SIMPLE_RV_STOPPING_TIME_INDICATOR]]; ALL_TAC] THEN
     SUBGOAL_THEN `simple_rv (p:A prob_space)
       (\x. (X:num->A->real) n x *
            indicator_fn {y | y IN prob_carrier p /\ (tau:A->num) y > n} x)`
       ASSUME_TAC THENL
     [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
      CONJ_TAC THENL
      [ASM_REWRITE_TAC[];
       ASM_MESON_TAC[SIMPLE_RV_STOPPING_TIME_INDICATOR]]; ALL_TAC] THEN
     SUBGOAL_THEN
       `simple_expectation (p:A prob_space)
         (\x. (X:num->A->real) (SUC n) x *
            indicator_fn {y | y IN prob_carrier p /\ (tau:A->num) y > n} x -
            X n x * indicator_fn {y | y IN prob_carrier p /\ tau y > n} x) =
        simple_expectation p
         (\x. X (SUC n) x *
            indicator_fn {y | y IN prob_carrier p /\ tau y > n} x) -
        simple_expectation p
         (\x. X n x *
            indicator_fn {y | y IN prob_carrier p /\ tau y > n} x)`
       SUBST1_TAC THENL
     [MATCH_MP_TAC SIMPLE_EXPECTATION_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     (* E[X_{n+1}*1_{tau>n}] - E[X_n*1_{tau>n}] <= 0,
        i.e. E[X_{n+1}*1_{tau>n}] <= E[X_n*1_{tau>n}] *)
     REWRITE_TAC[REAL_ARITH `a - b <= &0 <=> a <= b`] THEN
     SUBGOAL_THEN
       `{x | x IN prob_carrier (p:A prob_space) /\ (tau:A->num) x > n} IN
        (FF:num->(A->bool)->bool) n`
       ASSUME_TAC THENL
     [ASM_SIMP_TAC[STOPPING_TIME_INDICATOR_PREDICTABLE]; ALL_TAC] THEN
     SUBGOAL_THEN
       `!n' (a:A->bool). a IN (FF:num->(A->bool)->bool) n' ==>
        simple_expectation (p:A prob_space)
          (\x. (X:num->A->real) (SUC n') x * indicator_fn a x) <=
        simple_expectation p (\x. X n' x * indicator_fn a x)`
       ASSUME_TAC THENL
     [ASM_MESON_TAC[supermartingale]; ALL_TAC] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    (* IH: E[X^tau_n] <= E[X_0] *)
    ASM_REWRITE_TAC[]]]);;

(* Measurability transfers to a larger sub-sigma-algebra *)
let MEASURABLE_WRT_MONO = prove
 (`!p:A prob_space G1 G2 X.
     measurable_wrt p G1 X /\ G1 SUBSET G2
     ==> measurable_wrt p G2 X`,
  REWRITE_TAC[measurable_wrt] THEN SET_TAC[]);;

(* If-then-else preserves measurability *)
let MEASURABLE_WRT_IF = prove
 (`!p:A prob_space G (s:A->bool) f g.
     sub_sigma_algebra p G /\ s IN G /\
     measurable_wrt p G f /\ measurable_wrt p G g
     ==> measurable_wrt p G (\x. if x IN s then f x else g x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[measurable_wrt] THEN
  X_GEN_TAC `v:real` THEN TRY BETA_TAC THEN
  (* Rewrite the level set as a union *)
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ (if x IN s then f x else g x) <= v} =
     (s INTER {x | x IN prob_carrier p /\ (f:A->real) x <= v}) UNION
     ((prob_carrier p DIFF s) INTER
      {x | x IN prob_carrier p /\ (g:A->real) x <= v})`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_DIFF; IN_ELIM_THM] THEN
   X_GEN_TAC `x:A` THEN
   ASM_CASES_TAC `(x:A) IN s` THEN ASM_REWRITE_TAC[] THEN
   ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MATCH_MP_TAC SUB_SIGMA_ALGEBRA_UNION THEN
  EXISTS_TAC `p:A prob_space` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SUB_SIGMA_ALGEBRA_INTER THEN
   EXISTS_TAC `p:A prob_space` THEN ASM_REWRITE_TAC[] THEN
   ASM_MESON_TAC[measurable_wrt];
   MATCH_MP_TAC SUB_SIGMA_ALGEBRA_INTER THEN
   EXISTS_TAC `p:A prob_space` THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC SUB_SIGMA_ALGEBRA_COMPL THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[measurable_wrt]]]);;

(* Indicator function of intersection = product of indicators *)
let INDICATOR_FN_INTER = prove
 (`!a b (x:A). indicator_fn (a INTER b) x =
                indicator_fn a x * indicator_fn b x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[indicator_fn; IN_INTER] THEN
  ASM_CASES_TAC `(x:A) IN a` THEN ASM_CASES_TAC `(x:A) IN b` THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Functions equal on carrier have same measurability *)
let MEASURABLE_WRT_EQ_ON_CARRIER = prove
 (`!p:A prob_space G f g.
     measurable_wrt p G g /\
     (!x. x IN prob_carrier p ==> f x = g x)
     ==> measurable_wrt p G f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[measurable_wrt] THEN
  X_GEN_TAC `v:real` THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ f x <= v} =
     {x | x IN prob_carrier p /\ (g:A->real) x <= v}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
   GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[measurable_wrt]);;

(* Stopped process is measurable w.r.t. the filtration *)
let STOPPED_PROCESS_MEASURABLE_WRT = prove
 (`!p:A prob_space FF X tau.
     adapted p FF X /\ stopping_time p FF tau /\ filtration p FF
     ==> !n. measurable_wrt p (FF n) (stopped_process X tau n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
  [(* Base: stopped_process X tau 0 = X 0 as functions *)
   SUBGOAL_THEN
     `stopped_process (X:num->A->real) (tau:A->num) 0 = X 0`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; STOPPED_PROCESS_ZERO]; ALL_TAC] THEN
   ASM_MESON_TAC[adapted];
   (* Step: use if-then-else decomposition *)
   MATCH_MP_TAC MEASURABLE_WRT_EQ_ON_CARRIER THEN
   EXISTS_TAC `\x:A. if x IN {y | y IN prob_carrier p /\ (tau:A->num) y > n}
     then (X:num->A->real) (SUC n) x
     else stopped_process X tau n x` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_WRT_IF THEN
    SUBGOAL_THEN `sub_sigma_algebra (p:A prob_space) (FF (SUC n):(A->bool)->bool)`
      ASSUME_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [(* {tau > n} IN FF (SUC n): it's in FF n, and FF n SUBSET FF (SUC n) *)
     SUBGOAL_THEN
       `{y:A | y IN prob_carrier p /\ (tau:A->num) y > n} IN
        (FF:num->(A->bool)->bool) n` ASSUME_TAC THENL
     [ASM_SIMP_TAC[STOPPING_TIME_INDICATOR_PREDICTABLE]; ALL_TAC] THEN
     UNDISCH_TAC
       `{y:A | y IN prob_carrier p /\ (tau:A->num) y > n} IN
        (FF:num->(A->bool)->bool) n` THEN
     SUBGOAL_THEN `(FF:num->(A->bool)->bool) n SUBSET FF (SUC n)`
       MP_TAC THENL
     [SUBGOAL_THEN `n <= SUC n` MP_TAC THENL
      [ARITH_TAC; ASM_MESON_TAC[filtration]]; ALL_TAC] THEN
     REWRITE_TAC[SUBSET] THEN
     MESON_TAC[];
     (* X (SUC n) measurable w.r.t. FF (SUC n) *)
     CONV_TAC(RAND_CONV ETA_CONV) THEN
     UNDISCH_TAC
       `adapted (p:A prob_space) (FF:num->(A->bool)->bool)
        (X:num->A->real)` THEN
     REWRITE_TAC[adapted] THEN
     DISCH_THEN(ACCEPT_TAC o SPEC `SUC n`);
     (* stopped_process X tau n measurable w.r.t. FF (SUC n) *)
     CONV_TAC(RAND_CONV ETA_CONV) THEN
     MATCH_MP_TAC MEASURABLE_WRT_MONO THEN
     EXISTS_TAC `(FF:num->(A->bool)->bool) n` THEN
     ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `filtration (p:A prob_space) (FF:num->(A->bool)->bool)` THEN
     REWRITE_TAC[filtration] THEN
     DISCH_THEN(MP_TAC o CONJUNCT2) THEN
     DISCH_THEN(MP_TAC o SPECL [`n:num`; `SUC n`]) THEN
     DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC];
    (* Pointwise equality on carrier *)
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
    REWRITE_TAC[stopped_process; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(tau:A->num) x > n` THEN ASM_REWRITE_TAC[] THENL
    [SUBGOAL_THEN `MIN (SUC n) ((tau:A->num) x) = SUC n` SUBST1_TAC THENL
     [REWRITE_TAC[MIN] THEN ASM_ARITH_TAC; REFL_TAC];
     SUBGOAL_THEN `MIN (SUC n) ((tau:A->num) x) = MIN n (tau x)` SUBST1_TAC THENL
     [REWRITE_TAC[MIN] THEN ASM_ARITH_TAC; REFL_TAC]]]]);;

(* Stopped process of a simple adapted process is simple adapted *)
let SIMPLE_ADAPTED_STOPPED_PROCESS = prove
 (`!p:A prob_space FF X tau.
     simple_adapted p FF X /\ stopping_time p FF tau /\ filtration p FF
     ==> simple_adapted p FF (stopped_process X tau)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* First establish that all X n are simple_rv *)
  SUBGOAL_THEN `!n. simple_rv (p:A prob_space) ((X:num->A->real) n)`
    ASSUME_TAC THENL
  [GEN_TAC THEN REWRITE_TAC[simple_rv] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_WRT_IMP_RV THEN
    EXISTS_TAC `(FF:num->(A->bool)->bool) n` THEN
    CONJ_TAC THENL
    [ASM_MESON_TAC[filtration]; ASM_MESON_TAC[simple_adapted; adapted]];
    ASM_MESON_TAC[simple_adapted]]; ALL_TAC] THEN
  (* Establish stopped process is simple_rv *)
  SUBGOAL_THEN `!n. simple_rv (p:A prob_space)
    (stopped_process (X:num->A->real) (tau:A->num) n)` ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_STOPPED_PROCESS THEN
   EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[simple_adapted] THEN CONJ_TAC THENL
  [(* adapted *)
   REWRITE_TAC[adapted] THEN
   MATCH_MP_TAC STOPPED_PROCESS_MEASURABLE_WRT THEN
   CONJ_TAC THENL [ASM_MESON_TAC[simple_adapted; adapted]; ALL_TAC] THEN
   ASM_REWRITE_TAC[];
   (* FINITE range *)
   GEN_TAC THEN
   UNDISCH_TAC `!n. simple_rv (p:A prob_space)
     (stopped_process (X:num->A->real) (tau:A->num) n)` THEN
   DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
   REWRITE_TAC[simple_rv] THEN MESON_TAC[]]);;

(* Stopped process of a submartingale is a submartingale *)
let SUBMARTINGALE_STOPPED_PROCESS = prove
 (`!p:A prob_space FF X tau N.
     submartingale p FF X /\ bounded_stopping_time p FF tau N
     ==> submartingale p FF (stopped_process X tau)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Extract key properties *)
  SUBGOAL_THEN `filtration (p:A prob_space) (FF:num->(A->bool)->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_adapted (p:A prob_space) FF (X:num->A->real)`
    ASSUME_TAC THENL [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. simple_rv (p:A prob_space) ((X:num->A->real) n)`
    ASSUME_TAC THENL [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `stopping_time (p:A prob_space) FF (tau:A->num)`
    ASSUME_TAC THENL [ASM_MESON_TAC[bounded_stopping_time]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_adapted (p:A prob_space) FF
    (stopped_process (X:num->A->real) (tau:A->num))` ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_ADAPTED_STOPPED_PROCESS THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. simple_rv (p:A prob_space)
    (stopped_process (X:num->A->real) (tau:A->num) n)` ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_STOPPED_PROCESS THEN
   EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[submartingale] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  (* Need: E[X^tau_n * 1_a] <= E[X^tau_{SUC n} * 1_a] for a IN FF n *)
  (* Step 1: Establish {tau > n} IN FF n *)
  SUBGOAL_THEN
    `{y:A | y IN prob_carrier p /\ (tau:A->num) y > n} IN
     (FF:num->(A->bool)->bool) n`
    ASSUME_TAC THENL
  [ASM_SIMP_TAC[STOPPING_TIME_INDICATOR_PREDICTABLE]; ALL_TAC] THEN
  (* Step 2: Establish a INTER {tau > n} IN FF n *)
  SUBGOAL_THEN `sub_sigma_algebra (p:A prob_space)
    ((FF:num->(A->bool)->bool) n)` ASSUME_TAC THENL
  [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
  ABBREV_TAC `B = (a:A->bool) INTER
    {y | y IN prob_carrier (p:A prob_space) /\ (tau:A->num) y > n}` THEN
  SUBGOAL_THEN `(B:A->bool) IN (FF:num->(A->bool)->bool) n` ASSUME_TAC THENL
  [EXPAND_TAC "B" THEN MATCH_MP_TAC SUB_SIGMA_ALGEBRA_INTER THEN
   EXISTS_TAC `p:A prob_space` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Step 3: Show E[X^tau_{SUC n} * 1_a] = E[X^tau_n * 1_a] +
     E[(X(SUC n) - X n) * 1_B] *)
  (* First, the pointwise identity on carrier *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
      (\x. stopped_process (X:num->A->real) (tau:A->num) (SUC n) x *
           indicator_fn (a:A->bool) x) =
     simple_expectation p
      (\x. stopped_process X tau n x * indicator_fn a x) +
     simple_expectation p
      (\x. (X (SUC n) x - X n x) * indicator_fn B x)`
    SUBST1_TAC THENL
  [(* Show pointwise then use SIMPLE_EXPECTATION_ADD *)
   SUBGOAL_THEN
     `simple_expectation (p:A prob_space)
       (\x. stopped_process (X:num->A->real) (tau:A->num) (SUC n) x *
            indicator_fn (a:A->bool) x) =
      simple_expectation p
       (\x. stopped_process X tau n x * indicator_fn a x +
            (X (SUC n) x - X n x) * indicator_fn (B:A->bool) x)`
     SUBST1_TAC THENL
   [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(SPECL [`(X:num->A->real)`; `(tau:A->num)`; `n:num`; `x:A`]
      STOPPED_PROCESS_INCREMENT) THEN
    EXPAND_TAC "B" THEN
    REWRITE_TAC[indicator_fn; IN_INTER; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
   (* Apply SIMPLE_EXPECTATION_ADD *)
   MP_TAC(BETA_RULE(ISPECL [`p:A prob_space`;
     `\x:A. stopped_process (X:num->A->real) (tau:A->num) n x *
            indicator_fn (a:A->bool) x`;
     `\x:A. ((X:num->A->real) (SUC n) x - X n x) *
            indicator_fn (B:A->bool) x`]
     SIMPLE_EXPECTATION_ADD)) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
     CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
      MATCH_MP_TAC SUB_SIGMA_ALGEBRA_IN_EVENTS THEN
      EXISTS_TAC `(FF:num->(A->bool)->bool) n` THEN ASM_REWRITE_TAC[]];
     MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC SIMPLE_RV_SUB THEN REWRITE_TAC[ETA_AX] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
      MATCH_MP_TAC SUB_SIGMA_ALGEBRA_IN_EVENTS THEN
      EXISTS_TAC `(FF:num->(A->bool)->bool) n` THEN ASM_REWRITE_TAC[]]];
    SIMP_TAC[]];
   ALL_TAC] THEN
  (* Step 4: Show E[(X(SUC n) - X n) * 1_B] >= 0 *)
  MATCH_MP_TAC(REAL_ARITH `&0 <= c ==> a <= a + c`) THEN
  (* Rewrite (a-b)*c as a*c - b*c pointwise *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
      (\x. ((X:num->A->real) (SUC n) x - X n x) *
           indicator_fn (B:A->bool) x) =
     simple_expectation p (\x. X (SUC n) x * indicator_fn B x -
                                X n x * indicator_fn B x)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
   SPEC_TAC (`indicator_fn (B:A->bool) (x:A)`, `c:real`) THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  (* Establish simple_rv for products *)
  SUBGOAL_THEN `simple_rv (p:A prob_space)
    (\x. (X:num->A->real) (SUC n) x * indicator_fn (B:A->bool) x)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
   CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
    MATCH_MP_TAC SUB_SIGMA_ALGEBRA_IN_EVENTS THEN
    EXISTS_TAC `(FF:num->(A->bool)->bool) n` THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space)
    (\x. (X:num->A->real) n x * indicator_fn (B:A->bool) x)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
   CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
    MATCH_MP_TAC SUB_SIGMA_ALGEBRA_IN_EVENTS THEN
    EXISTS_TAC `(FF:num->(A->bool)->bool) n` THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* Apply SIMPLE_EXPECTATION_SUB *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
      (\x. (X:num->A->real) (SUC n) x * indicator_fn (B:A->bool) x -
           X n x * indicator_fn B x) =
     simple_expectation p (\x. X (SUC n) x * indicator_fn B x) -
     simple_expectation p (\x. X n x * indicator_fn B x)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_LE] THEN
  (* Apply the submartingale property to B IN FF n *)
  SUBGOAL_THEN
    `!n' (s:A->bool). s IN (FF:num->(A->bool)->bool) n' ==>
     simple_expectation (p:A prob_space)
       (\x. (X:num->A->real) n' x * indicator_fn s x) <=
     simple_expectation p (\x. X (SUC n') x * indicator_fn s x)`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Stopped process of a supermartingale is a supermartingale *)
let SUPERMARTINGALE_STOPPED_PROCESS = prove
 (`!p:A prob_space FF X tau N.
     supermartingale p FF X /\ bounded_stopping_time p FF tau N
     ==> supermartingale p FF (stopped_process X tau)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `filtration (p:A prob_space) (FF:num->(A->bool)->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[supermartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_adapted (p:A prob_space) FF (X:num->A->real)`
    ASSUME_TAC THENL [ASM_MESON_TAC[supermartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. simple_rv (p:A prob_space) ((X:num->A->real) n)`
    ASSUME_TAC THENL [ASM_MESON_TAC[supermartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `stopping_time (p:A prob_space) FF (tau:A->num)`
    ASSUME_TAC THENL [ASM_MESON_TAC[bounded_stopping_time]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_adapted (p:A prob_space) FF
    (stopped_process (X:num->A->real) (tau:A->num))` ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_ADAPTED_STOPPED_PROCESS THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. simple_rv (p:A prob_space)
    (stopped_process (X:num->A->real) (tau:A->num) n)` ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_STOPPED_PROCESS THEN
   EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[supermartingale] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `{y:A | y IN prob_carrier p /\ (tau:A->num) y > n} IN
     (FF:num->(A->bool)->bool) n`
    ASSUME_TAC THENL
  [ASM_SIMP_TAC[STOPPING_TIME_INDICATOR_PREDICTABLE]; ALL_TAC] THEN
  SUBGOAL_THEN `sub_sigma_algebra (p:A prob_space)
    ((FF:num->(A->bool)->bool) n)` ASSUME_TAC THENL
  [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
  ABBREV_TAC `B = (a:A->bool) INTER
    {y | y IN prob_carrier (p:A prob_space) /\ (tau:A->num) y > n}` THEN
  SUBGOAL_THEN `(B:A->bool) IN (FF:num->(A->bool)->bool) n` ASSUME_TAC THENL
  [EXPAND_TAC "B" THEN MATCH_MP_TAC SUB_SIGMA_ALGEBRA_INTER THEN
   EXISTS_TAC `p:A prob_space` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Decompose: E[X^tau_{SUC n} * 1_a] = E[X^tau_n * 1_a] +
     E[(X(SUC n) - X n) * 1_B] *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
      (\x. stopped_process (X:num->A->real) (tau:A->num) (SUC n) x *
           indicator_fn (a:A->bool) x) =
     simple_expectation p
      (\x. stopped_process X tau n x * indicator_fn a x) +
     simple_expectation p
      (\x. (X (SUC n) x - X n x) * indicator_fn B x)`
    SUBST1_TAC THENL
  [SUBGOAL_THEN
     `simple_expectation (p:A prob_space)
       (\x. stopped_process (X:num->A->real) (tau:A->num) (SUC n) x *
            indicator_fn (a:A->bool) x) =
      simple_expectation p
       (\x. stopped_process X tau n x * indicator_fn a x +
            (X (SUC n) x - X n x) * indicator_fn (B:A->bool) x)`
     SUBST1_TAC THENL
   [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(SPECL [`(X:num->A->real)`; `(tau:A->num)`; `n:num`; `x:A`]
      STOPPED_PROCESS_INCREMENT) THEN
    EXPAND_TAC "B" THEN
    REWRITE_TAC[indicator_fn; IN_INTER; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(BETA_RULE(ISPECL [`p:A prob_space`;
     `\x:A. stopped_process (X:num->A->real) (tau:A->num) n x *
            indicator_fn (a:A->bool) x`;
     `\x:A. ((X:num->A->real) (SUC n) x - X n x) *
            indicator_fn (B:A->bool) x`]
     SIMPLE_EXPECTATION_ADD)) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
     CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
      MATCH_MP_TAC SUB_SIGMA_ALGEBRA_IN_EVENTS THEN
      EXISTS_TAC `(FF:num->(A->bool)->bool) n` THEN ASM_REWRITE_TAC[]];
     MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC SIMPLE_RV_SUB THEN REWRITE_TAC[ETA_AX] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
      MATCH_MP_TAC SUB_SIGMA_ALGEBRA_IN_EVENTS THEN
      EXISTS_TAC `(FF:num->(A->bool)->bool) n` THEN ASM_REWRITE_TAC[]]];
    SIMP_TAC[]];
   ALL_TAC] THEN
  (* For supermartingale: need E[(X(SUC n) - X n) * 1_B] <= 0 *)
  MATCH_MP_TAC(REAL_ARITH `c <= &0 ==> a + c <= a`) THEN
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
      (\x. ((X:num->A->real) (SUC n) x - X n x) *
           indicator_fn (B:A->bool) x) =
     simple_expectation p (\x. X (SUC n) x * indicator_fn B x -
                                X n x * indicator_fn B x)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
   SPEC_TAC (`indicator_fn (B:A->bool) (x:A)`, `c:real`) THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space)
    (\x. (X:num->A->real) (SUC n) x * indicator_fn (B:A->bool) x)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
   CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
    MATCH_MP_TAC SUB_SIGMA_ALGEBRA_IN_EVENTS THEN
    EXISTS_TAC `(FF:num->(A->bool)->bool) n` THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space)
    (\x. (X:num->A->real) n x * indicator_fn (B:A->bool) x)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
   CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
    MATCH_MP_TAC SUB_SIGMA_ALGEBRA_IN_EVENTS THEN
    EXISTS_TAC `(FF:num->(A->bool)->bool) n` THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
      (\x. (X:num->A->real) (SUC n) x * indicator_fn (B:A->bool) x -
           X n x * indicator_fn B x) =
     simple_expectation p (\x. X (SUC n) x * indicator_fn B x) -
     simple_expectation p (\x. X n x * indicator_fn B x)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `a - b <= &0 <=> a <= b`] THEN
  SUBGOAL_THEN
    `!n' (s:A->bool). s IN (FF:num->(A->bool)->bool) n' ==>
     simple_expectation (p:A prob_space)
       (\x. (X:num->A->real) (SUC n') x * indicator_fn s x) <=
     simple_expectation p (\x. X n' x * indicator_fn s x)`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[supermartingale]; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Stopped process of a martingale is a martingale *)
let MARTINGALE_STOPPED_PROCESS = prove
 (`!p:A prob_space FF X tau N.
     martingale p FF X /\ bounded_stopping_time p FF tau N
     ==> martingale p FF (stopped_process X tau)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MARTINGALE_SUB_SUPER] THEN CONJ_TAC THENL
  [MATCH_MP_TAC SUBMARTINGALE_STOPPED_PROCESS THEN
   EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[] THEN
   ASM_MESON_TAC[MARTINGALE_IMP_SUBMARTINGALE];
   MATCH_MP_TAC SUPERMARTINGALE_STOPPED_PROCESS THEN
   EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[] THEN
   ASM_MESON_TAC[MARTINGALE_IMP_SUPERMARTINGALE]]);;

(* Localized submartingale increasing: E[X_m * 1_a] <= E[X_n * 1_a]
   for a IN FF m and m <= n *)
let SUBMARTINGALE_LOCALIZED_INCREASING = prove
 (`!p:A prob_space FF X m n a.
     submartingale p FF X /\ a IN FF m /\ m <= n
     ==> simple_expectation p (\x. X m x * indicator_fn a x) <=
         simple_expectation p (\x. X n x * indicator_fn a x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?k. n = m + k:num` CHOOSE_TAC THENL
  [EXISTS_TAC `n - m:num` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC (`k:num`, `j:num`) THEN INDUCT_TAC THENL
  [REWRITE_TAC[ADD_CLAUSES] THEN REAL_ARITH_TAC;
   REWRITE_TAC[ADD_CLAUSES] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `simple_expectation (p:A prob_space)
     (\x. (X:num->A->real) (m + j) x * indicator_fn (a:A->bool) x)` THEN
   CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    (* Need: E[X(m+j) * 1_a] <= E[X(SUC(m+j)) * 1_a] *)
    (* From submartingale: need a IN FF (m+j) *)
    SUBGOAL_THEN `(a:A->bool) IN (FF:num->(A->bool)->bool) (m + j)`
      (fun th -> MP_TAC th) THENL
    [SUBGOAL_THEN `(FF:num->(A->bool)->bool) m SUBSET FF (m + j)`
       MP_TAC THENL
     [UNDISCH_TAC `submartingale (p:A prob_space) FF (X:num->A->real)` THEN
      REWRITE_TAC[submartingale; filtration] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      DISCH_THEN(MP_TAC o SPECL [`m:num`; `m + j:num`]) THEN
      DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
     UNDISCH_TAC `(a:A->bool) IN (FF:num->(A->bool)->bool) m` THEN
     REWRITE_TAC[SUBSET] THEN MESON_TAC[];
     ALL_TAC] THEN
    DISCH_TAC THEN
    UNDISCH_TAC `submartingale (p:A prob_space) FF (X:num->A->real)` THEN
    REWRITE_TAC[submartingale] THEN
    DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
    DISCH_THEN(MP_TAC o SPECL [`m + j:num`; `a:A->bool`]) THEN
    ASM_REWRITE_TAC[]]]);;

(* Running maximum of a process *)
let running_max = define
  `(running_max (X:num->A->real) 0 x = X 0 x) /\
   (running_max X (SUC n) x = real_max (running_max X n x) (X (SUC n) x))`;;


(* Helper: real_max a b >= c iff a >= c or b >= c *)
let REAL_MAX_GE = prove
 (`!a b c:real. real_max a b >= c <=> a >= c \/ b >= c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_max; real_ge] THEN
  COND_CASES_TAC THEN
  ASM_MESON_TAC[REAL_LE_TRANS; REAL_NOT_LE; REAL_LT_IMP_LE]);;


(* Level set {X >= c} is in sub-sigma-algebra when X is measurable_wrt *)
let MEASURABLE_WRT_GE = prove
 (`!p:A prob_space G X c.
     sub_sigma_algebra p G /\ measurable_wrt p G X
     ==> {x | x IN prob_carrier p /\ X x >= c} IN G`,
  REPEAT STRIP_TAC THEN
  (* {X >= c} = UNIONS G DIFF {X < c} *)
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ X x >= c} =
     UNIONS G DIFF {x | x IN prob_carrier p /\ X x < c}`
    SUBST1_TAC THENL
  [SUBGOAL_THEN `UNIONS (G:(A->bool)->bool) = prob_carrier p` SUBST1_TAC THENL
   [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
   REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN
   X_GEN_TAC `z:A` THEN
   ASM_CASES_TAC `(z:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  MATCH_MP_TAC SIGMA_ALGEBRA_COMPL THEN
  CONJ_TAC THENL [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  (* {X < c} = countable union of {X <= c - inv(n+1)} *)
  REWRITE_TAC[ISPECL [`X:A->real`; `c:real`; `prob_carrier (p:A prob_space)`]
    OPEN_HALFLINE_AS_UNION] THEN
  MATCH_MP_TAC SIGMA_ALGEBRA_UNION_COUNTABLE THEN
  CONJ_TAC THENL [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIV] THEN
   X_GEN_TAC `s:A->bool` THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
   ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `measurable_wrt (p:A prob_space) G X` THEN
   REWRITE_TAC[measurable_wrt] THEN
   DISCH_THEN(MP_TAC o SPEC `c - inv(&n + &1)`) THEN
   MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[EXTENSION; IN_ELIM_THM];
   REWRITE_TAC[SIMPLE_IMAGE] THEN
   MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[NUM_COUNTABLE]]);;

(* {running_max X n >= c} is in FF n for adapted X *)
let RUNNING_MAX_EXCEEDS_IN_FILTRATION = prove
 (`!p:A prob_space FF X c n.
     filtration p FF /\ adapted p FF X
     ==> {x | x IN prob_carrier p /\ running_max X n x >= c} IN FF n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SPEC_TAC(`n:num`, `n:num`) THEN
  INDUCT_TAC THENL
  [REWRITE_TAC[running_max] THEN MATCH_MP_TAC MEASURABLE_WRT_GE THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC[filtration];
    REWRITE_TAC[ETA_AX] THEN
    UNDISCH_TAC `adapted (p:A prob_space) FF X` THEN
    REWRITE_TAC[adapted] THEN DISCH_THEN(fun th -> REWRITE_TAC[th])];
   (* SUC case *)
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ running_max X (SUC n) x >= c} =
      {x | x IN prob_carrier p /\ running_max X n x >= c} UNION
      {x | x IN prob_carrier p /\ X (SUC n) x >= c}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; running_max; REAL_MAX_GE] THEN
    MESON_TAC[];
    ALL_TAC] THEN
   MATCH_MP_TAC SIGMA_ALGEBRA_UNION THEN
   CONJ_TAC THENL [ASM_MESON_TAC[filtration; sub_sigma_algebra]; ALL_TAC] THEN
   CONJ_TAC THENL
   [SUBGOAL_THEN `(FF:num->(A->bool)->bool) n SUBSET FF (SUC n)` MP_TAC THENL
    [ASM_MESON_TAC[filtration; LE; LE_REFL]; ALL_TAC] THEN
    ASM SET_TAC[];
    MATCH_MP_TAC MEASURABLE_WRT_GE THEN
    CONJ_TAC THENL
    [ASM_MESON_TAC[filtration];
     REWRITE_TAC[ETA_AX] THEN
     UNDISCH_TAC `adapted (p:A prob_space) FF X` THEN
     REWRITE_TAC[adapted] THEN DISCH_THEN(fun th -> REWRITE_TAC[th])]]]);;


(* Indicator of disjoint union decomposes as sum *)
let INDICATOR_FN_DISJOINT_UNION = prove
 (`!a b (x:A). DISJOINT a b
     ==> indicator_fn (a UNION b) x = indicator_fn a x + indicator_fn b x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DISJOINT; indicator_fn; IN_UNION; IN_INTER;
    EXTENSION; NOT_IN_EMPTY] THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `(x:A) IN a` THEN ASM_CASES_TAC `(x:A) IN b` THEN
  ASM_REWRITE_TAC[] THEN TRY REAL_ARITH_TAC THEN
  ASM_MESON_TAC[]);;



(* Doob's maximal inequality - strong form *)
(* c * P(max_{k<=n} X_k >= c) <= E[X_n * 1_{max_{k<=n} X_k >= c}] *)
let DOOB_MAXIMAL_INEQUALITY_STRONG = prove
 (`!p:A prob_space FF X c n.
     submartingale p FF X /\ &0 < c /\
     (!m x. x IN prob_carrier p ==> &0 <= X m x)
     ==> c * prob p {x | x IN prob_carrier p /\ running_max X n x >= c} <=
         simple_expectation p
           (\x. X n x * indicator_fn
                  {y | y IN prob_carrier p /\ running_max X n y >= c} x)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `filtration (p:A prob_space) FF` ASSUME_TAC THENL
  [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `adapted (p:A prob_space) FF X` ASSUME_TAC THENL
  [ASM_MESON_TAC[submartingale; simple_adapted]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. simple_rv (p:A prob_space) ((X:num->A->real) n)`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  INDUCT_TAC THENL
  [REWRITE_TAC[running_max] THEN
   SUBGOAL_THEN
     `{y:A | y IN prob_carrier p /\ X 0 y >= c} IN prob_events p`
     ASSUME_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_GE THEN REWRITE_TAC[ETA_AX] THEN
    FIRST_ASSUM(fun th -> ACCEPT_TAC(CONJUNCT1(REWRITE_RULE[simple_rv](SPEC `0` th))));
    ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `simple_expectation (p:A prob_space)
     (\x. c * indicator_fn {y | y IN prob_carrier p /\ X 0 y >= c} x)` THEN
   CONJ_TAC THENL
   [SUBGOAL_THEN
      `simple_expectation (p:A prob_space)
         (\x. c * indicator_fn {y | y IN prob_carrier p /\ X 0 y >= c} x) =
       c * prob p {y | y IN prob_carrier p /\ X 0 y >= c}`
      SUBST1_TAC THENL
    [SUBGOAL_THEN
       `simple_expectation (p:A prob_space)
          (\x. c * indicator_fn {y | y IN prob_carrier p /\ X 0 y >= c} x) =
        c * simple_expectation p
              (indicator_fn {y | y IN prob_carrier p /\ X 0 y >= c})`
       SUBST1_TAC THENL
     [MATCH_MP_TAC SIMPLE_EXPECTATION_CMUL THEN
      MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     AP_TERM_TAC THEN MATCH_MP_TAC SIMPLE_EXPECTATION_INDICATOR THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    REWRITE_TAC[REAL_LE_REFL];
    MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
     CONJ_TAC THENL
     [REWRITE_TAC[SIMPLE_RV_CONST]; MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
     CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN BETA_TAC THEN
    REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
   ABBREV_TAC
     `A_n = {x:A | x IN prob_carrier p /\ running_max X n x >= c}` THEN
   ABBREV_TAC
     `B = {x:A | x IN prob_carrier p /\ X (SUC n) x >= c} DIFF A_n` THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ running_max X (SUC n) x >= c} =
      A_n UNION B`
     SUBST1_TAC THENL
   [EXPAND_TAC "B" THEN EXPAND_TAC "A_n" THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:A` THEN
    REWRITE_TAC[IN_UNION; IN_DIFF; IN_ELIM_THM;
                running_max; REAL_MAX_GE] THEN
    ASM_CASES_TAC `(z:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `running_max (X:num->A->real) n z >= c` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `DISJOINT (A_n:A->bool) B` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN SET_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `(A_n:A->bool) IN FF (n:num)` ASSUME_TAC THENL
   [EXPAND_TAC "A_n" THEN MATCH_MP_TAC RUNNING_MAX_EXCEEDS_IN_FILTRATION THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `(A_n:A->bool) IN prob_events p` ASSUME_TAC THENL
   [ASM_MESON_TAC[filtration; sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
   SUBGOAL_THEN `(B:A->bool) IN prob_events p` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN MATCH_MP_TAC PROB_DIFF_IN_EVENTS THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RANDOM_VARIABLE_GE THEN REWRITE_TAC[ETA_AX] THEN
    FIRST_ASSUM(fun th -> ACCEPT_TAC(CONJUNCT1(REWRITE_RULE[simple_rv](SPEC `SUC n` th))));
    ALL_TAC] THEN
   SUBGOAL_THEN
     `prob (p:A prob_space) (A_n UNION B) = prob p A_n + prob p B`
     SUBST1_TAC THENL
   [MATCH_MP_TAC PROB_ADDITIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN
     `simple_expectation (p:A prob_space)
        (\x. X (SUC n) x * indicator_fn (A_n UNION B) x) =
      simple_expectation p (\x. X (SUC n) x * indicator_fn A_n x) +
      simple_expectation p (\x. X (SUC n) x * indicator_fn B x)`
     SUBST1_TAC THENL
   [SUBGOAL_THEN
      `simple_expectation (p:A prob_space)
         (\x. X (SUC n) x * indicator_fn (A_n UNION B) x) =
       simple_expectation p
         (\x. X (SUC n) x * indicator_fn A_n x +
              X (SUC n) x * indicator_fn B x)`
      SUBST1_TAC THENL
    [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
     X_GEN_TAC `y:A` THEN DISCH_TAC THEN BETA_TAC THEN
     REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN
     AP_TERM_TAC THEN MATCH_MP_TAC INDICATOR_FN_DISJOINT_UNION THEN
     ASM_REWRITE_TAC[];
     MATCH_MP_TAC SIMPLE_EXPECTATION_ADD THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
      CONJ_TAC THENL
      [ASM_REWRITE_TAC[]; MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
      CONJ_TAC THENL
      [ASM_REWRITE_TAC[]; MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[]]]];
    ALL_TAC] THEN
   REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
   SUBGOAL_THEN
     `c * prob (p:A prob_space) (A_n:A->bool) <=
      simple_expectation p (\x. (X:num->A->real) (SUC n) x * indicator_fn A_n x)`
     ASSUME_TAC THENL
   [SUBGOAL_THEN
      `simple_expectation (p:A prob_space)
         (\x. (X:num->A->real) n x * indicator_fn A_n x) <=
       simple_expectation p
         (\x. X (SUC n) x * indicator_fn A_n x)`
      ASSUME_TAC THENL
    [MATCH_MP_TAC SUBMARTINGALE_LOCALIZED_INCREASING THEN
     EXISTS_TAC `(FF:num->(A->bool)->bool)` THEN
     ASM_REWRITE_TAC[ARITH_RULE `n <= SUC n`];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `c * prob (p:A prob_space) A_n <=
       simple_expectation p (\x. (X:num->A->real) n x * indicator_fn A_n x)`
      ASSUME_TAC THENL
    [FIRST_ASSUM ACCEPT_TAC;
     ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN
     `c * prob (p:A prob_space) (B:A->bool) <=
      simple_expectation p (\x. (X:num->A->real) (SUC n) x * indicator_fn B x)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `simple_expectation (p:A prob_space)
      (\x. c * indicator_fn B x)` THEN
    CONJ_TAC THENL
    [SUBGOAL_THEN
       `simple_expectation (p:A prob_space)
          (\x. c * indicator_fn B x) = c * prob p B`
       SUBST1_TAC THENL
     [SUBGOAL_THEN
        `simple_expectation (p:A prob_space) (\x. c * indicator_fn B x) =
         c * simple_expectation p (indicator_fn B)` SUBST1_TAC THENL
      [MATCH_MP_TAC SIMPLE_EXPECTATION_CMUL THEN
       MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC SIMPLE_EXPECTATION_INDICATOR THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
     REWRITE_TAC[REAL_LE_REFL];
     MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
      CONJ_TAC THENL
      [REWRITE_TAC[SIMPLE_RV_CONST];
       MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
      CONJ_TAC THENL
      [ASM_REWRITE_TAC[];
       MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
     X_GEN_TAC `y:A` THEN DISCH_TAC THEN BETA_TAC THEN
     REWRITE_TAC[indicator_fn] THEN
     COND_CASES_TAC THEN REWRITE_TAC[] THENL
     [REWRITE_TAC[REAL_MUL_RID] THEN
      UNDISCH_TAC `(y:A) IN B` THEN EXPAND_TAC "B" THEN
      REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
      REWRITE_TAC[real_ge] THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC]];
    ALL_TAC] THEN
   ASM_REAL_ARITH_TAC]);;

(* Doob's maximal inequality *)
let DOOB_MAXIMAL_INEQUALITY = prove
 (`!p:A prob_space FF X c n.
     submartingale p FF X /\ &0 < c /\
     (!m x. x IN prob_carrier p ==> &0 <= X m x)
     ==> c * prob p {x | x IN prob_carrier p /\ running_max X n x >= c}
         <= simple_expectation p (X n)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `simple_expectation (p:A prob_space)
    (\x. X n x * indicator_fn
           {y | y IN prob_carrier p /\ running_max X n y >= c} x)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC DOOB_MAXIMAL_INEQUALITY_STRONG THEN
   EXISTS_TAC `(FF:num->(A->bool)->bool)` THEN ASM_REWRITE_TAC[];
   (* E[X n * 1_A] <= E[X n] since X n >= 0 and 1_A <= 1 *)
   MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
   SUBGOAL_THEN `!n. simple_rv (p:A prob_space) ((X:num->A->real) n)`
     ASSUME_TAC THENL
   [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
    CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
     SUBGOAL_THEN
       `{y:A | y IN prob_carrier p /\ running_max X n y >= c} IN
        (FF:num->(A->bool)->bool) n`
       MP_TAC THENL
     [MATCH_MP_TAC RUNNING_MAX_EXCEEDS_IN_FILTRATION THEN
      ASM_MESON_TAC[submartingale; simple_adapted];
      ASM_MESON_TAC[submartingale; simple_adapted; filtration;
                    sub_sigma_algebra; SUBSET]]]; ALL_TAC] THEN
   CONJ_TAC THENL [REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   X_GEN_TAC `y:A` THEN DISCH_TAC THEN BETA_TAC THEN
   REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
   COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO] THENL
   [REWRITE_TAC[REAL_LE_REFL];
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `y:A`]) THEN
    ASM_REWRITE_TAC[]]])


(* ------------------------------------------------------------------------- *)
(* Generalized Doob theorems using general (integrable) expectation          *)
(* ------------------------------------------------------------------------- *)

(* Fair Games Theorem (Doob Optional Stopping) with general expectation *)
let DOOB_OPTIONAL_STOPPING_GENERAL = prove
 (`!p:A prob_space FF X tau N.
    martingale p FF X /\ bounded_stopping_time p FF tau N
    ==> !n. expectation p (stopped_process X tau n) = expectation p (X 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                 `X:num->A->real`; `tau:A->num`; `N:num`]
    DOOB_OPTIONAL_STOPPING_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (stopped_process X tau n) /\
                simple_rv p (X 0)` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                   `X:num->A->real`; `tau:A->num`]
     SIMPLE_RV_STOPPED_PROCESS) THEN
    ANTS_TAC THENL
    [CONJ_TAC THENL
     [ASM_MESON_TAC[martingale]; ALL_TAC] THEN
     CONJ_TAC THENL
     [ASM_MESON_TAC[bounded_stopping_time]; ALL_TAC] THEN
     ASM_MESON_TAC[martingale];
     SIMP_TAC[]];
    ASM_MESON_TAC[martingale]];
   ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM EXPECTATION_SIMPLE_AGREE]);;

(* Doob Maximal Inequality with general expectation *)
let DOOB_MAXIMAL_INEQUALITY_GENERAL = prove
 (`!p:A prob_space FF X c n.
    submartingale p FF X /\
    &0 < c /\
    (!m x. x IN prob_carrier p ==> &0 <= X m x)
    ==> c * prob p {x | x IN prob_carrier p /\ running_max X n x >= c} <=
        expectation p (X n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `expectation (p:A prob_space) ((X:num->A->real) n) =
                simple_expectation p (X n)` SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN
   ASM_MESON_TAC[submartingale];
   MATCH_MP_TAC DOOB_MAXIMAL_INEQUALITY THEN
   EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[]]);;
