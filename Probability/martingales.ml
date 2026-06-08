(* ========================================================================= *)
(* Martingale theory: sub-sigma-algebras, filtrations, stopping times,       *)
(* optional stopping, and Doob's maximal inequality.                         *)
(*                                                                           *)
(* Follows Williams "Probability with Martingales" Chapters 8-10.            *)
(* Includes sub-sigma-algebras, conditional expectation for simple RVs,      *)
(* filtrations, simple_martingale definitions, Doob's optional stopping theorem     *)
(* (Fair Games Theorem), simple_submartingale inequalities, and Doob's maximal      *)
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

(* A simple_martingale w.r.t. filtration FF *)
let simple_martingale = new_definition
  `simple_martingale (p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real) <=>
   filtration p FF /\
   simple_adapted p FF X /\
   (!n. simple_rv p (X n)) /\
   (!n a. a IN FF n
     ==> simple_expectation p (\x. X (SUC n) x * indicator_fn a x) =
         simple_expectation p (\x. X n x * indicator_fn a x))`;;

(* A simple_submartingale w.r.t. filtration FF *)
let simple_submartingale = new_definition
  `simple_submartingale (p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real) <=>
   filtration p FF /\
   simple_adapted p FF X /\
   (!n. simple_rv p (X n)) /\
   (!n a. a IN FF n
     ==> simple_expectation p (\x. X n x * indicator_fn a x) <=
         simple_expectation p (\x. X (SUC n) x * indicator_fn a x))`;;

(* A simple_supermartingale w.r.t. filtration FF *)
let simple_supermartingale = new_definition
  `simple_supermartingale (p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real) <=>
   filtration p FF /\
   simple_adapted p FF X /\
   (!n. simple_rv p (X n)) /\
   (!n a. a IN FF n
     ==> simple_expectation p (\x. X (SUC n) x * indicator_fn a x) <=
         simple_expectation p (\x. X n x * indicator_fn a x))`;;

(* Every simple_martingale is both a sub- and super-simple_martingale *)
let SIMPLE_MARTINGALE_IMP_SUBMARTINGALE = prove
 (`!p:A prob_space FF X.
     simple_martingale p FF X ==> simple_submartingale p FF X`,
  REWRITE_TAC[simple_martingale; simple_submartingale] THEN
  MESON_TAC[REAL_LE_REFL]);;

let SIMPLE_MARTINGALE_IMP_SUPERMARTINGALE = prove
 (`!p:A prob_space FF X.
     simple_martingale p FF X ==> simple_supermartingale p FF X`,
  REWRITE_TAC[simple_martingale; simple_supermartingale] THEN
  MESON_TAC[REAL_LE_REFL]);;

(* X is a simple_martingale iff it is both sub- and super-simple_martingale *)
let SIMPLE_MARTINGALE_SUB_SUPER = prove
 (`!p:A prob_space FF X.
     simple_martingale p FF X <=>
     simple_submartingale p FF X /\ simple_supermartingale p FF X`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [MESON_TAC[SIMPLE_MARTINGALE_IMP_SUBMARTINGALE; SIMPLE_MARTINGALE_IMP_SUPERMARTINGALE];
   REWRITE_TAC[simple_submartingale; simple_supermartingale; simple_martingale] THEN
   MESON_TAC[REAL_LE_ANTISYM]]);;


let FILTRATION_MONO = prove
 (`!p:A prob_space FF m n.
     filtration p FF /\ m <= n ==> FF m SUBSET FF n`,
  SIMP_TAC[filtration]);;

(* Constant sequence is a simple_martingale *)
let SIMPLE_MARTINGALE_CONST = prove
 (`!p:A prob_space FF c.
     filtration p FF
     ==> simple_martingale p FF (\n x. c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simple_martingale] THEN
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
let SIMPLE_MARTINGALE_EXPECTATION_CONST = prove
 (`!p:A prob_space FF X.
     simple_martingale p FF X
     ==> !n. simple_expectation p (X n) = simple_expectation p (X 0)`,
  REWRITE_TAC[simple_martingale] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
    `simple_expectation p ((X:num->A->real) (SUC n)) =
     simple_expectation p (X n)` (fun th -> ASM_REWRITE_TAC[th]) THEN
  ONCE_REWRITE_TAC[GSYM SIMPLE_EXPECTATION_MUL_INDICATOR_CARRIER] THEN
  SUBGOAL_THEN `prob_carrier (p:A prob_space) IN FF (n:num)` ASSUME_TAC THENL
  [ASM_MESON_TAC[filtration; SUB_SIGMA_ALGEBRA_CARRIER_IN]; ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

(* E[X_n] <= E[X_{n+1}] for submartingales *)
let SIMPLE_SUBMARTINGALE_EXPECTATION_MONO = prove
 (`!p:A prob_space FF X.
     simple_submartingale p FF X
     ==> !n. simple_expectation p (X n) <= simple_expectation p (X (SUC n))`,
  REWRITE_TAC[simple_submartingale] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM SIMPLE_EXPECTATION_MUL_INDICATOR_CARRIER] THEN
  SUBGOAL_THEN `prob_carrier (p:A prob_space) IN FF (n:num)` ASSUME_TAC THENL
  [ASM_MESON_TAC[filtration; SUB_SIGMA_ALGEBRA_CARRIER_IN]; ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

(* E[X_{n+1}] <= E[X_n] for supermartingales *)
let SIMPLE_SUPERMARTINGALE_EXPECTATION_MONO = prove
 (`!p:A prob_space FF X.
     simple_supermartingale p FF X
     ==> !n. simple_expectation p (X (SUC n)) <= simple_expectation p (X n)`,
  REWRITE_TAC[simple_supermartingale] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM SIMPLE_EXPECTATION_MUL_INDICATOR_CARRIER] THEN
  SUBGOAL_THEN `prob_carrier (p:A prob_space) IN FF (n:num)` ASSUME_TAC THENL
  [ASM_MESON_TAC[filtration; SUB_SIGMA_ALGEBRA_CARRIER_IN]; ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

(* E[X_0] <= E[X_n] for submartingales (by induction) *)
let SIMPLE_SUBMARTINGALE_EXPECTATION_INCREASING = prove
 (`!p:A prob_space FF X.
     simple_submartingale p FF X
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
    MP_TAC (SPEC `m + j:num` (MATCH_MP SIMPLE_SUBMARTINGALE_EXPECTATION_MONO
      (ASSUME `simple_submartingale (p:A prob_space) FF (X:num->A->real)`))) THEN
    SIMP_TAC[]]]);;

(* E[X_n] <= E[X_0] for supermartingales (by induction) *)
let SIMPLE_SUPERMARTINGALE_EXPECTATION_DECREASING = prove
 (`!p:A prob_space FF X.
     simple_supermartingale p FF X
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
   [MP_TAC (SPEC `m + j:num` (MATCH_MP SIMPLE_SUPERMARTINGALE_EXPECTATION_MONO
      (ASSUME `simple_supermartingale (p:A prob_space) FF (X:num->A->real)`))) THEN
    SIMP_TAC[];
    ASM_REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* Conditional Expectation for Simple RVs                                    *)
(* ========================================================================= *)

(* Conditional expectation of X given sub-sigma-algebra G:
   The unique G-measurable simple RV Y such that for all A in G,
   E[Y * 1_A] = E[X * 1_A].
   We define it constructively for simple RVs. *)

(* First: a key property - simple_martingale condition restated *)
let SIMPLE_MARTINGALE_COND_EXP = prove
 (`!p:A prob_space FF X.
     simple_martingale p FF X
     ==> !n a. a IN FF n
         ==> simple_expectation p (\x. X (SUC n) x * indicator_fn a x) =
             simple_expectation p (\x. X n x * indicator_fn a x)`,
  REWRITE_TAC[simple_martingale] THEN MESON_TAC[]);;

(* Martingale transform: if X is a simple_martingale and H is predictable & bounded,
   then (H . X)_n = sum_{i=0}^{n-1} H_i * (X_{i+1} - X_i) is a simple_martingale.
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

(* Key theorem: For a simple_martingale X and bounded stopping times sigma <= tau <= N,
   E[X_tau] = E[X_sigma] = E[X_0].
   The simplest case: E[X_{tau /\ n}] = E[X_0] for all n.

   Proof approach: X^tau_n = X_0 + sum_{i=0}^{n-1} 1_{tau > i} * (X_{i+1} - X_i)
   The indicator 1_{tau > i} is FF_i-measurable (since {tau > i} = Omega \ {tau <= i}
   and {tau <= i} IN FF_i by the stopping time property).
   So X^tau is a simple_martingale transform, and E[X^tau_n] = E[X_0]. *)

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
   SET_TAC[NOT_LE; GT]]);;

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
   For a simple_martingale X and bounded stopping time tau,
   E[X^tau_n] = E[X_0] for all n. *)
let SIMPLE_DOOB_OPTIONAL_STOPPING_BOUNDED = prove
 (`!p:A prob_space FF X tau N.
     simple_martingale p FF X /\ bounded_stopping_time p FF tau N
     ==> !n. simple_expectation p (stopped_process X tau n) =
             simple_expectation p (X 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Extract key properties from simple_martingale *)
  SUBGOAL_THEN `filtration (p:A prob_space) (FF:num->(A->bool)->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_martingale]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. simple_rv (p:A prob_space) ((X:num->A->real) n)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_martingale]; ALL_TAC] THEN
  SUBGOAL_THEN
    `!n a. a IN (FF:num->(A->bool)->bool) n
     ==> simple_expectation (p:A prob_space)
           (\x. (X:num->A->real) (SUC n) x * indicator_fn a x) =
         simple_expectation p (\x. X n x * indicator_fn a x)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_martingale]; ALL_TAC] THEN
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
   (* Apply the simple_martingale property: E[X_{n+1} * 1_{tau>n}] = E[X_n * 1_{tau>n}] *)
   SUBGOAL_THEN
     `simple_expectation (p:A prob_space)
       (\x. (X:num->A->real) (SUC n) x *
            indicator_fn {y | y IN prob_carrier p /\ (tau:A->num) y > n} x) =
      simple_expectation p
       (\x. X n x * indicator_fn {y | y IN prob_carrier p /\ tau y > n} x)`
     ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
   (* Show (X_{n+1} - X_n) * 1_{tau>n} has zero expectation.
      Uses: (a - b) * c = a * c - b * c pointwise, E[SUB] = E[] - E[],
      and simple_martingale property for {tau > n} IN FF n. *)
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
   For a simple_submartingale, E[X_0] <= E[X^tau_n] for all n. *)
let SIMPLE_SUBMARTINGALE_OPTIONAL_STOPPING_GE = prove
 (`!p:A prob_space FF X tau N.
     simple_submartingale p FF X /\ bounded_stopping_time p FF tau N
     ==> !n. simple_expectation p (X 0) <=
             simple_expectation p (stopped_process X tau n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Extract key properties from simple_submartingale *)
  SUBGOAL_THEN `filtration (p:A prob_space) (FF:num->(A->bool)->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. simple_rv (p:A prob_space) ((X:num->A->real) n)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
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
     (* Prove E[increment] >= 0 using simple_submartingale property *)
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
     (* Extract one-step simple_submartingale inequality and apply *)
     SUBGOAL_THEN
       `!n' (a:A->bool). a IN (FF:num->(A->bool)->bool) n' ==>
        simple_expectation (p:A prob_space)
          (\x. (X:num->A->real) n' x * indicator_fn a x) <=
        simple_expectation p (\x. X (SUC n') x * indicator_fn a x)`
       ASSUME_TAC THENL
     [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]]);;
(* Supermartingale optional stopping: upper bound.
   For a simple_supermartingale, E[X^tau_n] <= E[X_0] for all n. *)
let SIMPLE_SUPERMARTINGALE_OPTIONAL_STOPPING_LE = prove
 (`!p:A prob_space FF X tau N.
     simple_supermartingale p FF X /\ bounded_stopping_time p FF tau N
     ==> !n. simple_expectation p (stopped_process X tau n) <=
             simple_expectation p (X 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Extract key properties from simple_supermartingale *)
  SUBGOAL_THEN `filtration (p:A prob_space) (FF:num->(A->bool)->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_supermartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. simple_rv (p:A prob_space) ((X:num->A->real) n)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_supermartingale]; ALL_TAC] THEN
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
     [ASM_MESON_TAC[simple_supermartingale]; ALL_TAC] THEN
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

(* Stopped process of a simple_submartingale is a simple_submartingale *)
let SIMPLE_SUBMARTINGALE_STOPPED_PROCESS = prove
 (`!p:A prob_space FF X tau N.
     simple_submartingale p FF X /\ bounded_stopping_time p FF tau N
     ==> simple_submartingale p FF (stopped_process X tau)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Extract key properties *)
  SUBGOAL_THEN `filtration (p:A prob_space) (FF:num->(A->bool)->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_adapted (p:A prob_space) FF (X:num->A->real)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. simple_rv (p:A prob_space) ((X:num->A->real) n)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
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
  REWRITE_TAC[simple_submartingale] THEN
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
  (* Apply the simple_submartingale property to B IN FF n *)
  SUBGOAL_THEN
    `!n' (s:A->bool). s IN (FF:num->(A->bool)->bool) n' ==>
     simple_expectation (p:A prob_space)
       (\x. (X:num->A->real) n' x * indicator_fn s x) <=
     simple_expectation p (\x. X (SUC n') x * indicator_fn s x)`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Stopped process of a simple_supermartingale is a simple_supermartingale *)
let SIMPLE_SUPERMARTINGALE_STOPPED_PROCESS = prove
 (`!p:A prob_space FF X tau N.
     simple_supermartingale p FF X /\ bounded_stopping_time p FF tau N
     ==> simple_supermartingale p FF (stopped_process X tau)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `filtration (p:A prob_space) (FF:num->(A->bool)->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_supermartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_adapted (p:A prob_space) FF (X:num->A->real)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_supermartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. simple_rv (p:A prob_space) ((X:num->A->real) n)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_supermartingale]; ALL_TAC] THEN
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
  REWRITE_TAC[simple_supermartingale] THEN
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
  (* For simple_supermartingale: need E[(X(SUC n) - X n) * 1_B] <= 0 *)
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
  [ASM_MESON_TAC[simple_supermartingale]; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Stopped process of a simple_martingale is a simple_martingale *)
let SIMPLE_MARTINGALE_STOPPED_PROCESS = prove
 (`!p:A prob_space FF X tau N.
     simple_martingale p FF X /\ bounded_stopping_time p FF tau N
     ==> simple_martingale p FF (stopped_process X tau)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[SIMPLE_MARTINGALE_SUB_SUPER] THEN CONJ_TAC THENL
  [MATCH_MP_TAC SIMPLE_SUBMARTINGALE_STOPPED_PROCESS THEN
   EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[] THEN
   ASM_MESON_TAC[SIMPLE_MARTINGALE_IMP_SUBMARTINGALE];
   MATCH_MP_TAC SIMPLE_SUPERMARTINGALE_STOPPED_PROCESS THEN
   EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[] THEN
   ASM_MESON_TAC[SIMPLE_MARTINGALE_IMP_SUPERMARTINGALE]]);;

(* Localized simple_submartingale increasing: E[X_m * 1_a] <= E[X_n * 1_a]
   for a IN FF m and m <= n *)
let SIMPLE_SUBMARTINGALE_LOCALIZED_INCREASING = prove
 (`!p:A prob_space FF X m n a.
     simple_submartingale p FF X /\ a IN FF m /\ m <= n
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
    (* From simple_submartingale: need a IN FF (m+j) *)
    SUBGOAL_THEN `(a:A->bool) IN (FF:num->(A->bool)->bool) (m + j)`
      (fun th -> MP_TAC th) THENL
    [SUBGOAL_THEN `(FF:num->(A->bool)->bool) m SUBSET FF (m + j)`
       MP_TAC THENL
     [UNDISCH_TAC `simple_submartingale (p:A prob_space) FF (X:num->A->real)` THEN
      REWRITE_TAC[simple_submartingale; filtration] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      DISCH_THEN(MP_TAC o SPECL [`m:num`; `m + j:num`]) THEN
      DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
     UNDISCH_TAC `(a:A->bool) IN (FF:num->(A->bool)->bool) m` THEN
     REWRITE_TAC[SUBSET] THEN MESON_TAC[];
     ALL_TAC] THEN
    DISCH_TAC THEN
    UNDISCH_TAC `simple_submartingale (p:A prob_space) FF (X:num->A->real)` THEN
    REWRITE_TAC[simple_submartingale] THEN
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
   SET_TAC[REAL_ARITH `!x c:real. x >= c <=> ~(x < c)`];
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
let SIMPLE_DOOB_MAXIMAL_INEQUALITY_STRONG = prove
 (`!p:A prob_space FF X c n.
     simple_submartingale p FF X /\ &0 < c /\
     (!m x. x IN prob_carrier p ==> &0 <= X m x)
     ==> c * prob p {x | x IN prob_carrier p /\ running_max X n x >= c} <=
         simple_expectation p
           (\x. X n x * indicator_fn
                  {y | y IN prob_carrier p /\ running_max X n y >= c} x)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `filtration (p:A prob_space) FF` ASSUME_TAC THENL
  [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `adapted (p:A prob_space) FF X` ASSUME_TAC THENL
  [ASM_MESON_TAC[simple_submartingale; simple_adapted]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. simple_rv (p:A prob_space) ((X:num->A->real) n)`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  INDUCT_TAC THENL
  [REWRITE_TAC[running_max] THEN
   SUBGOAL_THEN
     `{y:A | y IN prob_carrier p /\ X 0 y >= c} IN prob_events p`
     ASSUME_TAC THENL
   [MATCH_MP_TAC RV_PREIMAGE_GE THEN REWRITE_TAC[ETA_AX] THEN
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
    MATCH_MP_TAC RV_PREIMAGE_GE THEN REWRITE_TAC[ETA_AX] THEN
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
    [MATCH_MP_TAC SIMPLE_SUBMARTINGALE_LOCALIZED_INCREASING THEN
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
     simple_submartingale p FF X /\ &0 < c /\
     (!m x. x IN prob_carrier p ==> &0 <= X m x)
     ==> c * prob p {x | x IN prob_carrier p /\ running_max X n x >= c}
         <= simple_expectation p (X n)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `simple_expectation (p:A prob_space)
    (\x. X n x * indicator_fn
           {y | y IN prob_carrier p /\ running_max X n y >= c} x)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SIMPLE_DOOB_MAXIMAL_INEQUALITY_STRONG THEN
   EXISTS_TAC `(FF:num->(A->bool)->bool)` THEN ASM_REWRITE_TAC[];
   (* E[X n * 1_A] <= E[X n] since X n >= 0 and 1_A <= 1 *)
   MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
   SUBGOAL_THEN `!n. simple_rv (p:A prob_space) ((X:num->A->real) n)`
     ASSUME_TAC THENL
   [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
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
      ASM_MESON_TAC[simple_submartingale; simple_adapted];
      ASM_MESON_TAC[simple_submartingale; simple_adapted; filtration;
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
let SIMPLE_DOOB_OPTIONAL_STOPPING = prove
 (`!p:A prob_space FF X tau N.
    simple_martingale p FF X /\ bounded_stopping_time p FF tau N
    ==> !n. expectation p (stopped_process X tau n) = expectation p (X 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                 `X:num->A->real`; `tau:A->num`; `N:num`]
    SIMPLE_DOOB_OPTIONAL_STOPPING_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (stopped_process X tau n) /\
                simple_rv p (X 0)` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                   `X:num->A->real`; `tau:A->num`]
     SIMPLE_RV_STOPPED_PROCESS) THEN
    ANTS_TAC THENL
    [CONJ_TAC THENL
     [ASM_MESON_TAC[simple_martingale]; ALL_TAC] THEN
     CONJ_TAC THENL
     [ASM_MESON_TAC[bounded_stopping_time]; ALL_TAC] THEN
     ASM_MESON_TAC[simple_martingale];
     SIMP_TAC[]];
    ASM_MESON_TAC[simple_martingale]];
   ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM EXPECTATION_SIMPLE_AGREE]);;

(* Doob Maximal Inequality with general expectation *)
let DOOB_MAXIMAL_INEQUALITY_GENERAL = prove
 (`!p:A prob_space FF X c n.
    simple_submartingale p FF X /\
    &0 < c /\
    (!m x. x IN prob_carrier p ==> &0 <= X m x)
    ==> c * prob p {x | x IN prob_carrier p /\ running_max X n x >= c} <=
        expectation p (X n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `expectation (p:A prob_space) ((X:num->A->real) n) =
                simple_expectation p (X n)` SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN
   ASM_MESON_TAC[simple_submartingale];
   MATCH_MP_TAC DOOB_MAXIMAL_INEQUALITY THEN
   EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[]]);;

(* ================================================================== *)
(* Wald's Equation: E[S_tau] = mu * E[SUC(tau)]                       *)
(* For bounded stopping times with i.i.d.-like conditional mean       *)
(* ================================================================== *)

(* {tau > n} is in FF n *)
let STOPPING_TIME_GT_IN_FF = prove
 (`!p:A prob_space FF (tau:A->num) n.
     filtration p FF /\ stopping_time p FF tau
     ==> {x | x IN prob_carrier p /\ tau x > n} IN FF n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sub_sigma_algebra (p:A prob_space) ((FF:num->(A->bool)->bool) n)` ASSUME_TAC THENL
  [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ (tau:A->num) x <= n} IN (FF:num->(A->bool)->bool) n` ASSUME_TAC THENL
  [ASM_MESON_TAC[stopping_time]; ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS ((FF:num->(A->bool)->bool) n) DIFF {x:A | x IN prob_carrier p /\ (tau:A->num) x <= n} IN FF n` MP_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra; sigma_algebra]; ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS ((FF:num->(A->bool)->bool) n) = prob_carrier (p:A prob_space)` SUBST1_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `a = b ==> a ==> b`) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SET_TAC[NOT_LE; GT]);;

(* Transfer simple_rv via equality on carrier *)
let SIMPLE_RV_EQ_ON_CARRIER = prove
 (`!p:A prob_space f g.
     simple_rv p g /\ (!x. x IN prob_carrier p ==> f x = g x)
     ==> simple_rv p f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simple_rv] THEN CONJ_TAC THENL
  [REWRITE_TAC[random_variable] THEN X_GEN_TAC `v:real` THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ f x <= v} = {x | x IN prob_carrier p /\ g x <= v}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[simple_rv; random_variable]];
   SUBGOAL_THEN `{f x:real | x:A IN prob_carrier p} = {g x | x IN prob_carrier p}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN EXISTS_TAC `x':A` THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[simple_rv]]]);;

(* Pointwise identity: sum up to random index = sum with indicators *)
let SUM_RANDOM_INDEX = prove
 (`!f (tau:B->num) M (x:B).
     tau x <= M
     ==> sum(0..tau x) (\i. f i) =
         sum(0..M) (\i. f i * (if i <= tau x then &1 else &0))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `0..M = (0..(tau (x:B))) UNION (((tau x) + 1)..M)` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_UNION; IN_NUMSEG] THEN X_GEN_TAC `i:num` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (0..tau (x:B)) ((tau x + 1)..M)` ASSUME_TAC THENL
  [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_NUMSEG; NOT_IN_EMPTY] THEN X_GEN_TAC `i:num` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_UNION; FINITE_NUMSEG] THEN
  SUBGOAL_THEN `sum (0..tau (x:B)) (\i. f i * (if i <= tau x then &1 else &0)) = sum (0..tau x) (\i. f i)` SUBST1_TAC THENL
  [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
   SUBGOAL_THEN `x':num <= tau (x:B)` (fun th -> REWRITE_TAC[th; REAL_MUL_RID]) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sum ((tau (x:B) + 1)..M) (\i. f i * (if i <= tau x then &1 else &0)) = &0` SUBST1_TAC THENL
  [MATCH_MP_TAC SUM_EQ_0 THEN REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
   SUBGOAL_THEN `~(x':num <= tau (x:B))` (fun th -> REWRITE_TAC[th; REAL_MUL_RZERO]) THEN ASM_ARITH_TAC;
   REAL_ARITH_TAC]);;

(* {i <= tau} is in prob_events *)
let STOPPING_TIME_GE_EVENT = prove
 (`!p:A prob_space FF (tau:A->num) i.
     filtration p FF /\ stopping_time p FF tau
     ==> {x | x IN prob_carrier p /\ i <= tau x} IN prob_events p`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [STRIP_TAC THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ 0 <= tau x} = prob_carrier p` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; LE_0]; ALL_TAC] THEN REWRITE_TAC[PROB_CARRIER_IN_EVENTS];
   STRIP_TAC THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ SUC i <= tau x} = {x | x IN prob_carrier p /\ tau x > i}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
    ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[GT] THEN ARITH_TAC; ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`; `tau:A->num`; `i:num`] STOPPING_TIME_GT_IN_FF) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_MESON_TAC[filtration; sub_sigma_algebra; SUBSET]]);;

(* {SUC n <= tau} is in FF n *)
let STOPPING_TIME_SUC_GE_IN_FF = prove
 (`!p:A prob_space FF (tau:A->num) n.
     filtration p FF /\ stopping_time p FF tau
     ==> {x | x IN prob_carrier p /\ SUC n <= tau x} IN FF n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ SUC n <= tau x} = {x | x IN prob_carrier p /\ tau x > n}` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
   ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[GT] THEN ARITH_TAC;
   MATCH_MP_TAC STOPPING_TIME_GT_IN_FF THEN ASM_REWRITE_TAC[]]);;

(* E[X_i * 1_{i<=tau}] = mu * P(i <= tau) *)
let WALD_TERM_EXPECTATION = prove
 (`!p:A prob_space FF (X:num->A->real) (tau:A->num) (M:num) (mu:real) i.
     filtration p FF /\
     (!n. n <= M ==> simple_rv p (X n)) /\
     (!n. n <= M ==> simple_expectation p (X n) = mu) /\
     (!n. n <= M ==> !a. a IN FF n ==>
       simple_expectation p (\x. X (SUC n) x * indicator_fn a x) = mu * prob p a) /\
     bounded_stopping_time p FF tau M /\
     i <= M
     ==> simple_expectation p
           (\x. X i x * indicator_fn {y | y IN prob_carrier p /\ i <= tau y} x) =
         mu * prob p {y | y IN prob_carrier p /\ i <= tau y}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `stopping_time (p:A prob_space) FF (tau:A->num)` ASSUME_TAC THENL
  [ASM_MESON_TAC[bounded_stopping_time]; ALL_TAC] THEN
  ASM_CASES_TAC `?n. i = SUC n` THENL
  [FIRST_X_ASSUM(X_CHOOSE_TAC `n:num`) THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `n:num <= M` ASSUME_TAC THENL
   [UNDISCH_TAC `(i:num) <= M` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `{y:A | y IN prob_carrier p /\ SUC n <= (tau:A->num) y} IN (FF:num->(A->bool)->bool) n` ASSUME_TAC THENL
   [MATCH_MP_TAC STOPPING_TIME_SUC_GE_IN_FF THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_MESON_TAC[];
   SUBGOAL_THEN `i = 0` SUBST_ALL_TAC THENL [ASM_MESON_TAC[num_CASES]; ALL_TAC] THEN
   SUBGOAL_THEN `!x:A. x IN prob_carrier p ==>
     (X:num->A->real) 0 x * indicator_fn {y | y IN prob_carrier p /\ 0 <= (tau:A->num) y} x = X 0 x` ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[indicator_fn; IN_ELIM_THM; LE_0] THEN
    ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
   SUBGOAL_THEN `simple_expectation (p:A prob_space) (\x. (X:num->A->real) 0 x *
     indicator_fn {y | y IN prob_carrier p /\ 0 <= tau y} x) = simple_expectation p (X 0)` SUBST1_TAC THENL
   [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN ASM_SIMP_TAC[ETA_AX]; ALL_TAC] THEN
   SUBGOAL_THEN `prob (p:A prob_space) {y | y IN prob_carrier p /\ 0 <= (tau:A->num) y} = &1` SUBST1_TAC THENL
   [SUBGOAL_THEN `{y:A | y IN prob_carrier p /\ 0 <= (tau:A->num) y} = prob_carrier p` SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM; LE_0]; ALL_TAC] THEN REWRITE_TAC[PROB_SPACE]; ALL_TAC] THEN
   REWRITE_TAC[REAL_MUL_RID; ETA_AX] THEN ASM_MESON_TAC[LE_0]]);;

(* Sum of indicators = SUC(tau) *)
let INDICATOR_SUM_STOPPING_TIME = prove
 (`!p:A prob_space (tau:A->num) M x.
     x IN prob_carrier p /\ tau x <= M
     ==> sum(0..M) (\i. indicator_fn {y | y IN prob_carrier p /\ i <= tau y} x) = &(SUC(tau x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `0..M = (0..tau (x:A)) UNION ((tau x + 1)..M)` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_UNION; IN_NUMSEG] THEN X_GEN_TAC `i:num` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (0..tau (x:A)) ((tau x + 1)..M)` ASSUME_TAC THENL
  [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_NUMSEG; NOT_IN_EMPTY] THEN X_GEN_TAC `i:num` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_UNION; FINITE_NUMSEG] THEN
  SUBGOAL_THEN `sum (0..tau (x:A)) (\i. indicator_fn {y:A | y IN prob_carrier p /\ i <= (tau:A->num) y} x) = sum (0..tau x) (\i. &1)` SUBST1_TAC THENL
  [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
   REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
   ASM_CASES_TAC `(x:A) IN prob_carrier p` THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
   ASM_REWRITE_TAC[] THEN
   COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sum ((tau (x:A) + 1)..M) (\i. indicator_fn {y:A | y IN prob_carrier p /\ i <= (tau:A->num) y} x) = &0` SUBST1_TAC THENL
  [MATCH_MP_TAC SUM_EQ_0 THEN REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
   REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
   COND_CASES_TAC THEN REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o CONJUNCT2) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RID; SUM_CONST_NUMSEG; SUB_0] THEN
  REWRITE_TAC[REAL_MUL_RID; GSYM REAL_OF_NUM_SUC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC);;

(* Wald's Equation *)
let WALD_EQUATION = prove
 (`!p:A prob_space FF (X:num->A->real) (tau:A->num) (M:num) (mu:real).
     filtration p FF /\
     (!n. n <= M ==> simple_rv p (X n)) /\
     (!n. n <= M ==> simple_expectation p (X n) = mu) /\
     (!n. n <= M ==> !a. a IN FF n ==>
       simple_expectation p (\x. X (SUC n) x * indicator_fn a x) =
       mu * prob p a) /\
     bounded_stopping_time p FF tau M
     ==> simple_expectation p (\x. sum(0..tau x) (\i. X i x)) =
         mu * simple_expectation p (\x. &(SUC(tau x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `stopping_time (p:A prob_space) FF (tau:A->num) /\ (!x. x IN prob_carrier p ==> tau x <= M)` STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `bounded_stopping_time (p:A prob_space) FF (tau:A->num) M` THEN REWRITE_TAC[bounded_stopping_time]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. {y:A | y IN prob_carrier p /\ i <= (tau:A->num) y} IN prob_events p` ASSUME_TAC THENL
  [GEN_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`; `tau:A->num`; `i:num`] STOPPING_TIME_GE_EVENT) THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. i <= M ==> simple_rv (p:A prob_space) (\x. (X:num->A->real) i x * indicator_fn {y | y IN prob_carrier p /\ i <= (tau:A->num) y} x)` ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) i`; `indicator_fn {y:A | y IN prob_carrier p /\ i <= (tau:A->num) y}`] SIMPLE_RV_MUL) THEN
   REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
   CONJ_TAC THENL [ASM_SIMP_TAC[]; MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN prob_carrier p ==>
    sum(0..tau x) (\i. (X:num->A->real) i x) =
    sum(0..M) (\i. X i x * indicator_fn {y | y IN prob_carrier p /\ i <= (tau:A->num) y} x)` ASSUME_TAC THENL
  [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   SUBGOAL_THEN `(tau:A->num) x <= M` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
   MP_TAC(ISPECL [`\i. (X:num->A->real) i x`; `tau:A->num`; `M:num`; `x:A`] SUM_RANDOM_INDEX) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
   MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_NUMSEG] THEN
   REPEAT STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Rewrite LHS *)
  SUBGOAL_THEN `simple_expectation (p:A prob_space) (\x. sum(0..tau x) (\i. (X:num->A->real) i x)) =
    simple_expectation p (\x. sum(0..M) (\i. X i x * indicator_fn {y | y IN prob_carrier p /\ i <= (tau:A->num) y} x))` SUBST1_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  (* Apply linearity of expectation *)
  SUBGOAL_THEN `simple_expectation (p:A prob_space) (\x. sum(0..M) (\i. (X:num->A->real) i x * indicator_fn {y | y IN prob_carrier p /\ i <= (tau:A->num) y} x)) =
    sum(0..M) (\i. simple_expectation p (\x. X i x * indicator_fn {y | y IN prob_carrier p /\ i <= tau y} x))` SUBST1_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`;
     `\i (x:A). (X:num->A->real) i x * indicator_fn {y | y IN prob_carrier p /\ i <= (tau:A->num) y} x`;
     `M:num`] SIMPLE_EXPECTATION_SUM_NUMSEG) THEN
   REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Apply WALD_TERM_EXPECTATION to each term *)
  SUBGOAL_THEN `!i. i <= M ==> simple_expectation (p:A prob_space)
    (\x. (X:num->A->real) i x * indicator_fn {y | y IN prob_carrier p /\ i <= (tau:A->num) y} x) =
    mu * prob p {y | y IN prob_carrier p /\ i <= tau y}` ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`; `X:num->A->real`; `tau:A->num`; `M:num`; `mu:real`; `i:num`] WALD_TERM_EXPECTATION) THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Rewrite each term *)
  SUBGOAL_THEN `sum(0..M) (\i. simple_expectation (p:A prob_space) (\x. (X:num->A->real) i x * indicator_fn {y | y IN prob_carrier p /\ i <= (tau:A->num) y} x)) =
    sum(0..M) (\i. mu * prob p {y | y IN prob_carrier p /\ i <= tau y})` SUBST1_TAC THENL
  [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  (* Factor out mu *)
  REWRITE_TAC[SUM_LMUL] THEN AP_TERM_TAC THEN
  (* Rewrite prob as expectation of indicator *)
  SUBGOAL_THEN `sum(0..M) (\i. prob (p:A prob_space) {y | y IN prob_carrier p /\ i <= (tau:A->num) y}) =
    sum(0..M) (\i. simple_expectation p (indicator_fn {y | y IN prob_carrier p /\ i <= tau y}))` SUBST1_TAC THENL
  [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
   BETA_TAC THEN CONV_TAC SYM_CONV THEN
   MATCH_MP_TAC SIMPLE_EXPECTATION_INDICATOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Use linearity in reverse: sum of E[ind_i] = E[sum of ind_i] *)
  CONV_TAC SYM_CONV THEN
  SUBGOAL_THEN `simple_expectation (p:A prob_space) (\x. &(SUC((tau:A->num) x))) =
    simple_expectation p (\x. sum(0..M) (\i. indicator_fn {y | y IN prob_carrier p /\ i <= tau y} x))` SUBST1_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   CONV_TAC SYM_CONV THEN
   MP_TAC(ISPECL [`p:A prob_space`; `tau:A->num`; `M:num`; `x:A`] INDICATOR_SUM_STOPPING_TIME) THEN
   ASM_SIMP_TAC[]; ALL_TAC] THEN
  (* Apply linearity *)
  MP_TAC(ISPECL [`p:A prob_space`;
    `\i (x:A). indicator_fn {y:A | y IN prob_carrier p /\ i <= (tau:A->num) y} x`;
    `M:num`] SIMPLE_EXPECTATION_SUM_NUMSEG) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC SIMPLE_RV_EQ_ON_CARRIER THEN
   EXISTS_TAC `indicator_fn {y:A | y IN prob_carrier p /\ i <= (tau:A->num) y}` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[]]; ALL_TAC] THEN
  REWRITE_TAC[ETA_AX]);;

(* ========================================================================= *)
(* BACKWARD (REVERSED) SIMPLE_MARTINGALES                                           *)
(* A backward simple_martingale uses a decreasing filtration FF_n >= FF_{n+1}       *)
(* with E[X_n | FF_{n+1}] = X_{n+1}.                                        *)
(* ========================================================================= *)

let decreasing_filtration = new_definition
  `decreasing_filtration (p:A prob_space) (FF:num->(A->bool)->bool) <=>
   (!n. sub_sigma_algebra p (FF n)) /\
   (!m n. m <= n ==> FF n SUBSET FF m)`;;

let simple_backward_martingale = new_definition
  `simple_backward_martingale (p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real) <=>
   decreasing_filtration p FF /\
   simple_adapted p FF X /\
   (!n. simple_rv p (X n)) /\
   (!n a. a IN FF (SUC n) ==>
     simple_expectation p (\x. X n x * indicator_fn a x) =
     simple_expectation p (\x. X (SUC n) x * indicator_fn a x))`;;

(* ========================================================================= *)
(* GENERAL (INTEGRABLE) MARTINGALE DEFINITIONS                                *)
(* These use integrable + expectation instead of simple_rv + simple_expectation *)
(* Every simple_martingale is a martingale (bridge lemmas below).              *)
(* ========================================================================= *)

let martingale = new_definition
  `martingale (p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real) <=>
   filtration p FF /\
   adapted p FF X /\
   (!n. integrable p (X n)) /\
   (!n a. a IN FF n
     ==> expectation p (\x. X (SUC n) x * indicator_fn a x) =
         expectation p (\x. X n x * indicator_fn a x))`;;

let submartingale = new_definition
  `submartingale (p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real) <=>
   filtration p FF /\
   adapted p FF X /\
   (!n. integrable p (X n)) /\
   (!n a. a IN FF n
     ==> expectation p (\x. X n x * indicator_fn a x) <=
         expectation p (\x. X (SUC n) x * indicator_fn a x))`;;

let supermartingale = new_definition
  `supermartingale (p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real) <=>
   filtration p FF /\
   adapted p FF X /\
   (!n. integrable p (X n)) /\
   (!n a. a IN FF n
     ==> expectation p (\x. X (SUC n) x * indicator_fn a x) <=
         expectation p (\x. X n x * indicator_fn a x))`;;

let backward_martingale = new_definition
  `backward_martingale (p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real) <=>
   decreasing_filtration p FF /\
   adapted p FF X /\
   (!n. integrable p (X n)) /\
   (!n a. a IN FF (SUC n) ==>
     expectation p (\x. X n x * indicator_fn a x) =
     expectation p (\x. X (SUC n) x * indicator_fn a x))`;;

(* --- Infrastructure lemma --- *)

let EXPECTATION_CARRIER_INDICATOR = prove
 (`!p:A prob_space f. integrable p f
   ==> expectation p (\x. f x * indicator_fn (prob_carrier p) x) =
       expectation p f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[expectation] THEN
  SUBGOAL_THEN `nn_expectation (p:A prob_space)
    (\x. max (f x * indicator_fn (prob_carrier p) x) (&0)) =
    nn_expectation p (\x. max (f x) (&0))` SUBST1_TAC THENL
  [MATCH_MP_TAC NN_EXPECTATION_EXT THEN GEN_TAC THEN DISCH_TAC THEN
   REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
   ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
  SUBGOAL_THEN `nn_expectation (p:A prob_space)
    (\x. max (--(f x * indicator_fn (prob_carrier p) x)) (&0)) =
    nn_expectation p (\x. max (--f x) (&0))` SUBST1_TAC THENL
  [MATCH_MP_TAC NN_EXPECTATION_EXT THEN GEN_TAC THEN DISCH_TAC THEN
   REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
   ASM_REWRITE_TAC[REAL_MUL_RID]; REWRITE_TAC[]]);;

(* --- Bridge lemmas: simple => general --- *)

let SIMPLE_IMP_MARTINGALE = prove
 (`!p:A prob_space FF X. simple_martingale p FF X ==> martingale p FF X`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[simple_martingale; martingale; simple_adapted] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_SIMPLE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a:A->bool) IN prob_events p` ASSUME_TAC THENL
  [MATCH_MP_TAC SUB_SIGMA_ALGEBRA_IN_EVENTS THEN
   EXISTS_TAC `(FF:num->(A->bool)->bool) n` THEN ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `filtration (p:A prob_space) FF` THEN
   REWRITE_TAC[filtration] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space)
    (\x. (X:num->A->real) (SUC n) x * indicator_fn (a:A->bool) x) /\
    simple_rv p (\x. X n x * indicator_fn a x)` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC SIMPLE_RV_MUL THEN
   REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[SIMPLE_RV_INDICATOR];
   ASM_SIMP_TAC[EXPECTATION_SIMPLE_AGREE]]);;

let SIMPLE_IMP_SUBMARTINGALE = prove
 (`!p:A prob_space FF X. simple_submartingale p FF X ==> submartingale p FF X`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[simple_submartingale; submartingale; simple_adapted] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_SIMPLE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a:A->bool) IN prob_events p` ASSUME_TAC THENL
  [MATCH_MP_TAC SUB_SIGMA_ALGEBRA_IN_EVENTS THEN
   EXISTS_TAC `(FF:num->(A->bool)->bool) n` THEN ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `filtration (p:A prob_space) FF` THEN
   REWRITE_TAC[filtration] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space)
    (\x. (X:num->A->real) (SUC n) x * indicator_fn (a:A->bool) x) /\
    simple_rv p (\x. X n x * indicator_fn a x)` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC SIMPLE_RV_MUL THEN
   REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[SIMPLE_RV_INDICATOR];
   ASM_SIMP_TAC[EXPECTATION_SIMPLE_AGREE]]);;

let SIMPLE_IMP_SUPERMARTINGALE = prove
 (`!p:A prob_space FF X. simple_supermartingale p FF X ==> supermartingale p FF X`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[simple_supermartingale; supermartingale; simple_adapted] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_SIMPLE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a:A->bool) IN prob_events p` ASSUME_TAC THENL
  [MATCH_MP_TAC SUB_SIGMA_ALGEBRA_IN_EVENTS THEN
   EXISTS_TAC `(FF:num->(A->bool)->bool) n` THEN ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `filtration (p:A prob_space) FF` THEN
   REWRITE_TAC[filtration] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space)
    (\x. (X:num->A->real) (SUC n) x * indicator_fn (a:A->bool) x) /\
    simple_rv p (\x. X n x * indicator_fn a x)` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC SIMPLE_RV_MUL THEN
   REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[SIMPLE_RV_INDICATOR];
   ASM_SIMP_TAC[EXPECTATION_SIMPLE_AGREE]]);;

let SIMPLE_IMP_BACKWARD_MARTINGALE = prove
 (`!p:A prob_space FF X.
     simple_backward_martingale p FF X ==> backward_martingale p FF X`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[simple_backward_martingale; backward_martingale; simple_adapted] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_SIMPLE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a:A->bool) IN prob_events p` ASSUME_TAC THENL
  [MATCH_MP_TAC SUB_SIGMA_ALGEBRA_IN_EVENTS THEN
   EXISTS_TAC `(FF:num->(A->bool)->bool) (SUC n)` THEN ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `decreasing_filtration (p:A prob_space) FF` THEN
   REWRITE_TAC[decreasing_filtration] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space)
    (\x. (X:num->A->real) (SUC n) x * indicator_fn (a:A->bool) x) /\
    simple_rv p (\x. X n x * indicator_fn a x)` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC SIMPLE_RV_MUL THEN
   REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[SIMPLE_RV_INDICATOR];
   ASM_SIMP_TAC[EXPECTATION_SIMPLE_AGREE]]);;

(* --- Structural relationships --- *)

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

let MARTINGALE_SUB_SUPER = prove
 (`!p:A prob_space FF X.
     martingale p FF X <=>
     submartingale p FF X /\ supermartingale p FF X`,
  REWRITE_TAC[martingale; submartingale; supermartingale] THEN
  MESON_TAC[REAL_LE_ANTISYM; REAL_LE_REFL]);;

(* --- Expectation monotonicity/constancy --- *)

let SUBMARTINGALE_EXPECTATION_MONO = prove
 (`!p:A prob_space FF X. submartingale p FF X
     ==> !n. expectation p (X n) <= expectation p (X (SUC n))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[submartingale] THEN STRIP_TAC THEN
  GEN_TAC THEN
  SUBGOAL_THEN `prob_carrier (p:A prob_space) IN FF (n:num)` ASSUME_TAC THENL
  [UNDISCH_TAC `filtration (p:A prob_space) FF` THEN
   REWRITE_TAC[filtration; sub_sigma_algebra; sigma_algebra] THEN
   MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `prob_carrier (p:A prob_space)`]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `expectation (p:A prob_space)
    (\x. (X:num->A->real) n x * indicator_fn (prob_carrier p) x) =
    expectation p (X n)` SUBST1_TAC THENL
  [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC EXPECTATION_CARRIER_INDICATOR THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `expectation (p:A prob_space)
    (\x. (X:num->A->real) (SUC n) x * indicator_fn (prob_carrier p) x) =
    expectation p (X (SUC n))` SUBST1_TAC THENL
  [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC EXPECTATION_CARRIER_INDICATOR THEN
   ASM_REWRITE_TAC[]; REAL_ARITH_TAC]);;

let SUBMARTINGALE_EXPECTATION_INCREASING = prove
 (`!p:A prob_space FF X. submartingale p FF X
     ==> !m n. m <= n ==> expectation p (X m) <= expectation p (X n)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SUBMARTINGALE_EXPECTATION_MONO) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `?k. n = m + k:num` (CHOOSE_THEN SUBST_ALL_TAC) THENL
  [EXISTS_TAC `n - m:num` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `m:num <= m + k` THEN DISCH_THEN(K ALL_TAC) THEN
  SPEC_TAC(`k:num`,`k:num`) THEN INDUCT_TAC THENL
  [REWRITE_TAC[ADD_CLAUSES; REAL_LE_REFL];
   REWRITE_TAC[ADD_CLAUSES] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `expectation (p:A prob_space) ((X:num->A->real) (m + k))` THEN
   ASM_MESON_TAC[]]);;

let SUPERMARTINGALE_EXPECTATION_MONO = prove
 (`!p:A prob_space FF X. supermartingale p FF X
     ==> !n. expectation p (X (SUC n)) <= expectation p (X n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[supermartingale] THEN STRIP_TAC THEN
  GEN_TAC THEN
  SUBGOAL_THEN `prob_carrier (p:A prob_space) IN FF (n:num)` ASSUME_TAC THENL
  [UNDISCH_TAC `filtration (p:A prob_space) FF` THEN
   REWRITE_TAC[filtration; sub_sigma_algebra; sigma_algebra] THEN
   MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `prob_carrier (p:A prob_space)`]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `expectation (p:A prob_space)
    (\x. (X:num->A->real) n x * indicator_fn (prob_carrier p) x) =
    expectation p (X n)` SUBST1_TAC THENL
  [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC EXPECTATION_CARRIER_INDICATOR THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `expectation (p:A prob_space)
    (\x. (X:num->A->real) (SUC n) x * indicator_fn (prob_carrier p) x) =
    expectation p (X (SUC n))` SUBST1_TAC THENL
  [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC EXPECTATION_CARRIER_INDICATOR THEN
   ASM_REWRITE_TAC[]; REAL_ARITH_TAC]);;

let SUPERMARTINGALE_EXPECTATION_DECREASING = prove
 (`!p:A prob_space FF X. supermartingale p FF X
     ==> !m n. m <= n ==> expectation p (X n) <= expectation p (X m)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SUPERMARTINGALE_EXPECTATION_MONO) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `?k. n = m + k:num` (CHOOSE_THEN SUBST_ALL_TAC) THENL
  [EXISTS_TAC `n - m:num` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `m:num <= m + k` THEN DISCH_THEN(K ALL_TAC) THEN
  SPEC_TAC(`k:num`,`k:num`) THEN INDUCT_TAC THENL
  [REWRITE_TAC[ADD_CLAUSES; REAL_LE_REFL];
   REWRITE_TAC[ADD_CLAUSES] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `expectation (p:A prob_space) ((X:num->A->real) (m + k))` THEN
   ASM_MESON_TAC[]]);;

let MARTINGALE_EXPECTATION_CONST = prove
 (`!p:A prob_space FF X. martingale p FF X
     ==> !m n. expectation p (X m) = expectation p (X n)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MARTINGALE_IMP_SUBMARTINGALE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUBMARTINGALE_EXPECTATION_INCREASING) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MARTINGALE_IMP_SUPERMARTINGALE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUPERMARTINGALE_EXPECTATION_DECREASING) THEN
  DISCH_TAC THEN DISCH_TAC THEN
  DISJ_CASES_TAC(SPECL [`m:num`; `n:num`] LE_CASES) THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN ASM_MESON_TAC[]);;

(* --- Constant process is a martingale --- *)

let MARTINGALE_CONST = prove
 (`!p:A prob_space FF c. filtration p FF
     ==> martingale p FF (\n x. c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SIMPLE_IMP_MARTINGALE THEN
  ASM_SIMP_TAC[SIMPLE_MARTINGALE_CONST]);;

(* ================================================================== *)
(* Optional stopping theorems for general martingales                 *)
(* ================================================================== *)

(* EXPECTATION_EXT: defined in expectation.ml *)

(* --- Measurability of stopped process --- *)

let RANDOM_VARIABLE_STOPPED_PROCESS = prove
 (`!p:A prob_space FF X tau n.
    adapted p FF X /\ filtration p FF /\ stopping_time p FF tau
    ==> random_variable p (stopped_process X tau n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SPEC_TAC(`n:num`, `n:num`) THEN INDUCT_TAC THENL
  [REWRITE_TAC[random_variable; stopped_process; MIN; LE_0] THEN
   GEN_TAC THEN
   UNDISCH_TAC `adapted (p:A prob_space) FF (X:num->A->real)` THEN
   REWRITE_TAC[adapted; measurable_wrt] THEN
   DISCH_THEN(MP_TAC o SPEC `0`) THEN
   DISCH_THEN(MP_TAC o SPEC `a:real`) THEN
   UNDISCH_TAC `filtration (p:A prob_space) FF` THEN
   REWRITE_TAC[filtration; sub_sigma_algebra] THEN SET_TAC[];
   REWRITE_TAC[random_variable] THEN X_GEN_TAC `v:real` THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ stopped_process (X:num->A->real) (tau:A->num) (SUC n) x <= v} =
      ({x | x IN prob_carrier p /\ tau x > n} INTER
       {x | x IN prob_carrier p /\ X (SUC n) x <= v}) UNION
      ({x | x IN prob_carrier p /\ tau x <= n} INTER
       {x | x IN prob_carrier p /\ stopped_process X tau n x <= v})`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_UNION] THEN
    X_GEN_TAC `x:A` THEN
    ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[stopped_process] THEN
    ASM_CASES_TAC `(tau:A->num) x > n` THENL
    [ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN `MIN (SUC n) ((tau:A->num) x) = SUC n` SUBST1_TAC THENL
     [REWRITE_TAC[MIN] THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
     ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN `MIN (SUC n) ((tau:A->num) x) = tau x` SUBST1_TAC THENL
     [REWRITE_TAC[MIN] THEN ASM_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `MIN n ((tau:A->num) x) = tau x` SUBST1_TAC THENL
     [REWRITE_TAC[MIN] THEN ASM_ARITH_TAC; ASM_ARITH_TAC]];
    ALL_TAC] THEN
   MATCH_MP_TAC PROB_UNION_IN_EVENTS THEN CONJ_TAC THEN
   MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`; `tau:A->num`; `n:num`]
      STOPPING_TIME_GT_IN_FF) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_MESON_TAC[filtration; sub_sigma_algebra; SUBSET];
    UNDISCH_TAC `adapted (p:A prob_space) FF (X:num->A->real)` THEN
    REWRITE_TAC[adapted; measurable_wrt] THEN
    DISCH_THEN(MP_TAC o SPEC `SUC n`) THEN DISCH_THEN(MP_TAC o SPEC `v:real`) THEN
    UNDISCH_TAC `filtration (p:A prob_space) FF` THEN
    REWRITE_TAC[filtration; sub_sigma_algebra] THEN SET_TAC[];
    UNDISCH_TAC `stopping_time (p:A prob_space) FF tau` THEN
    REWRITE_TAC[stopping_time] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
    UNDISCH_TAC `filtration (p:A prob_space) FF` THEN
    REWRITE_TAC[filtration; sub_sigma_algebra] THEN SET_TAC[];
    UNDISCH_TAC `random_variable (p:A prob_space) (stopped_process (X:num->A->real) (tau:A->num) n)` THEN
    REWRITE_TAC[random_variable] THEN DISCH_THEN(MP_TAC o SPEC `v:real`) THEN
    REWRITE_TAC[]]]);;

(* --- Integrability of stopped process --- *)

let INTEGRABLE_STOPPED_PROCESS = prove
 (`!p:A prob_space FF X tau N n.
    adapted p FF X /\ filtration p FF /\
    bounded_stopping_time p FF tau N /\
    (!k. integrable p (X k))
    ==> integrable p (stopped_process X tau n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `stopping_time (p:A prob_space) FF (tau:A->num)` ASSUME_TAC THENL
  [ASM_MESON_TAC[bounded_stopping_time]; ALL_TAC] THEN
  SPEC_TAC(`n:num`, `n:num`) THEN INDUCT_TAC THENL
  [SUBGOAL_THEN `stopped_process (X:num->A->real) (tau:A->num) 0 = X 0`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; STOPPED_PROCESS_ZERO]; ASM_REWRITE_TAC[]];
   MATCH_MP_TAC INTEGRABLE_DOMINATED THEN
   EXISTS_TAC `\x:A. abs((X:num->A->real) (SUC n) x) + abs(stopped_process X (tau:A->num) n x)` THEN
   REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_STOPPED_PROCESS THEN
    EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC INTEGRABLE_ABS THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    REWRITE_TAC[stopped_process] THEN
    ASM_CASES_TAC `(tau:A->num) x > n` THENL
    [SUBGOAL_THEN `MIN (SUC n) ((tau:A->num) x) = SUC n` SUBST1_TAC THENL
     [REWRITE_TAC[MIN] THEN ASM_ARITH_TAC; REAL_ARITH_TAC];
     SUBGOAL_THEN `MIN (SUC n) ((tau:A->num) x) = tau x` SUBST1_TAC THENL
     [REWRITE_TAC[MIN] THEN ASM_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `MIN n ((tau:A->num) x) = tau x` SUBST1_TAC THENL
     [REWRITE_TAC[MIN] THEN ASM_ARITH_TAC; REAL_ARITH_TAC]]]]);;

(* --- Doob Optional Stopping Theorem (martingale) --- *)

let DOOB_OPTIONAL_STOPPING = prove
 (`!p:A prob_space FF X tau N.
    martingale p FF X /\ bounded_stopping_time p FF tau N
    ==> !n. expectation p (stopped_process X tau n) = expectation p (X 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `filtration (p:A prob_space) FF` ASSUME_TAC THENL
  [ASM_MESON_TAC[martingale]; ALL_TAC] THEN
  SUBGOAL_THEN `adapted (p:A prob_space) FF (X:num->A->real)` ASSUME_TAC THENL
  [ASM_MESON_TAC[martingale]; ALL_TAC] THEN
  SUBGOAL_THEN `!k. integrable (p:A prob_space) ((X:num->A->real) k)` ASSUME_TAC THENL
  [ASM_MESON_TAC[martingale]; ALL_TAC] THEN
  SUBGOAL_THEN `stopping_time (p:A prob_space) FF (tau:A->num)` ASSUME_TAC THENL
  [ASM_MESON_TAC[bounded_stopping_time]; ALL_TAC] THEN
  SUBGOAL_THEN `!n a. a IN (FF:num->(A->bool)->bool) n
    ==> expectation (p:A prob_space) (\x. (X:num->A->real) (SUC n) x * indicator_fn a x) =
        expectation p (\x. X n x * indicator_fn a x)` ASSUME_TAC THENL
  [ASM_MESON_TAC[martingale]; ALL_TAC] THEN
  INDUCT_TAC THENL
  [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; STOPPED_PROCESS_ZERO];
   ASM_REWRITE_TAC[] THEN
   ABBREV_TAC `A = {x:A | x IN prob_carrier p /\ (tau:A->num) x > n}` THEN
   SUBGOAL_THEN `(A:A->bool) IN (FF:num->(A->bool)->bool) n` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN ASM_SIMP_TAC[STOPPING_TIME_GT_IN_FF]; ALL_TAC] THEN
   SUBGOAL_THEN `(A:A->bool) IN prob_events (p:A prob_space)` ASSUME_TAC THENL
   [ASM_MESON_TAC[filtration; sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (\x. ((X:num->A->real) (SUC n) x - X n x) * indicator_fn (A:A->bool) x)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (stopped_process (X:num->A->real) (tau:A->num) n)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_STOPPED_PROCESS THEN
    MAP_EVERY EXISTS_TAC [`FF:num->(A->bool)->bool`; `N:num`] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN
     `expectation (p:A prob_space) (stopped_process (X:num->A->real) (tau:A->num) (SUC n)) =
      expectation p (\x. stopped_process X tau n x + ((X (SUC n) x - X n x) * indicator_fn (A:A->bool) x))`
     SUBST1_TAC THENL
   [MATCH_MP_TAC EXPECTATION_EXT THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    BETA_TAC THEN
    MP_TAC(SPECL [`(X:num->A->real)`; `(tau:A->num)`; `n:num`; `x:A`]
      STOPPED_PROCESS_INCREMENT) THEN
    EXPAND_TAC "A" THEN REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(BETA_RULE(ISPECL [`p:A prob_space`;
     `stopped_process (X:num->A->real) (tau:A->num) n`;
     `\x:A. ((X:num->A->real) (SUC n) x - X n x) * indicator_fn (A:A->bool) x`]
     EXPECTATION_ADD)) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   SUBGOAL_THEN
     `expectation (p:A prob_space) (\x. ((X:num->A->real) (SUC n) x - X n x) * indicator_fn (A:A->bool) x) = &0`
     (fun th -> REWRITE_TAC[th] THEN REAL_ARITH_TAC) THEN
   SUBGOAL_THEN
     `(\x:A. ((X:num->A->real) (SUC n) x - X n x) * indicator_fn (A:A->bool) x) =
      (\x. X (SUC n) x * indicator_fn A x - X n x * indicator_fn A x)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (\x. (X:num->A->real) (SUC n) x * indicator_fn (A:A->bool) x) /\
                 integrable p (\x. X n x * indicator_fn A x)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
    ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
   ASM_SIMP_TAC[EXPECTATION_SUB] THEN REAL_ARITH_TAC]);;

(* --- Submartingale optional stopping (general) --- *)

let SUBMARTINGALE_OPTIONAL_STOPPING_GE = prove
 (`!p:A prob_space FF X tau N.
    submartingale p FF X /\ bounded_stopping_time p FF tau N
    ==> !n. expectation p (X 0) <= expectation p (stopped_process X tau n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `filtration (p:A prob_space) FF` ASSUME_TAC THENL
  [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `adapted (p:A prob_space) FF (X:num->A->real)` ASSUME_TAC THENL
  [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `!k. integrable (p:A prob_space) ((X:num->A->real) k)` ASSUME_TAC THENL
  [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `stopping_time (p:A prob_space) FF (tau:A->num)` ASSUME_TAC THENL
  [ASM_MESON_TAC[bounded_stopping_time]; ALL_TAC] THEN
  SUBGOAL_THEN `!n a. a IN (FF:num->(A->bool)->bool) n
    ==> expectation (p:A prob_space) (\x. (X:num->A->real) n x * indicator_fn a x) <=
        expectation p (\x. X (SUC n) x * indicator_fn a x)` ASSUME_TAC THENL
  [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  INDUCT_TAC THENL
  [SUBGOAL_THEN `stopped_process (X:num->A->real) (tau:A->num) 0 = X 0` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; STOPPED_PROCESS_ZERO]; REAL_ARITH_TAC];
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `expectation (p:A prob_space) (stopped_process (X:num->A->real) (tau:A->num) n)` THEN
   ASM_REWRITE_TAC[] THEN
   ABBREV_TAC `A = {x:A | x IN prob_carrier p /\ (tau:A->num) x > n}` THEN
   SUBGOAL_THEN `(A:A->bool) IN (FF:num->(A->bool)->bool) n` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN ASM_SIMP_TAC[STOPPING_TIME_GT_IN_FF]; ALL_TAC] THEN
   SUBGOAL_THEN `(A:A->bool) IN prob_events (p:A prob_space)` ASSUME_TAC THENL
   [ASM_MESON_TAC[filtration; sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (\x. ((X:num->A->real) (SUC n) x - X n x) * indicator_fn (A:A->bool) x)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (stopped_process (X:num->A->real) (tau:A->num) n)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_STOPPED_PROCESS THEN
    MAP_EVERY EXISTS_TAC [`FF:num->(A->bool)->bool`; `N:num`] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN
     `expectation (p:A prob_space) (stopped_process (X:num->A->real) (tau:A->num) (SUC n)) =
      expectation p (\x. stopped_process X tau n x + ((X (SUC n) x - X n x) * indicator_fn (A:A->bool) x))`
     SUBST1_TAC THENL
   [MATCH_MP_TAC EXPECTATION_EXT THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    BETA_TAC THEN
    MP_TAC(SPECL [`(X:num->A->real)`; `(tau:A->num)`; `n:num`; `x:A`]
      STOPPED_PROCESS_INCREMENT) THEN
    EXPAND_TAC "A" THEN REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(BETA_RULE(ISPECL [`p:A prob_space`;
     `stopped_process (X:num->A->real) (tau:A->num) n`;
     `\x:A. ((X:num->A->real) (SUC n) x - X n x) * indicator_fn (A:A->bool) x`]
     EXPECTATION_ADD)) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `A:A->bool`]) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (\x. (X:num->A->real) (SUC n) x * indicator_fn (A:A->bool) x) /\
                 integrable p (\x. X n x * indicator_fn A x)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
    ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
   SUBGOAL_THEN
     `expectation (p:A prob_space) (\x. ((X:num->A->real) (SUC n) x - X n x) * indicator_fn (A:A->bool) x) =
      expectation p (\x. X (SUC n) x * indicator_fn A x) -
      expectation p (\x. X n x * indicator_fn A x)` SUBST1_TAC THENL
   [SUBGOAL_THEN
      `(\x:A. ((X:num->A->real) (SUC n) x - X n x) * indicator_fn (A:A->bool) x) =
       (\x. X (SUC n) x * indicator_fn A x - X n x * indicator_fn A x)`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[EXPECTATION_SUB];
    ASM_REAL_ARITH_TAC]]);;

(* --- Supermartingale optional stopping (general) --- *)

let SUPERMARTINGALE_OPTIONAL_STOPPING_LE = prove
 (`!p:A prob_space FF X tau N.
    supermartingale p FF X /\ bounded_stopping_time p FF tau N
    ==> !n. expectation p (stopped_process X tau n) <= expectation p (X 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `filtration (p:A prob_space) FF` ASSUME_TAC THENL
  [ASM_MESON_TAC[supermartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `adapted (p:A prob_space) FF (X:num->A->real)` ASSUME_TAC THENL
  [ASM_MESON_TAC[supermartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `!k. integrable (p:A prob_space) ((X:num->A->real) k)` ASSUME_TAC THENL
  [ASM_MESON_TAC[supermartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `stopping_time (p:A prob_space) FF (tau:A->num)` ASSUME_TAC THENL
  [ASM_MESON_TAC[bounded_stopping_time]; ALL_TAC] THEN
  SUBGOAL_THEN `!n a. a IN (FF:num->(A->bool)->bool) n
    ==> expectation (p:A prob_space) (\x. (X:num->A->real) (SUC n) x * indicator_fn a x) <=
        expectation p (\x. X n x * indicator_fn a x)` ASSUME_TAC THENL
  [ASM_MESON_TAC[supermartingale]; ALL_TAC] THEN
  INDUCT_TAC THENL
  [SUBGOAL_THEN `stopped_process (X:num->A->real) (tau:A->num) 0 = X 0` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; STOPPED_PROCESS_ZERO]; REAL_ARITH_TAC];
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `expectation (p:A prob_space) (stopped_process (X:num->A->real) (tau:A->num) n)` THEN
   ASM_REWRITE_TAC[] THEN
   ABBREV_TAC `A = {x:A | x IN prob_carrier p /\ (tau:A->num) x > n}` THEN
   SUBGOAL_THEN `(A:A->bool) IN (FF:num->(A->bool)->bool) n` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN ASM_SIMP_TAC[STOPPING_TIME_GT_IN_FF]; ALL_TAC] THEN
   SUBGOAL_THEN `(A:A->bool) IN prob_events (p:A prob_space)` ASSUME_TAC THENL
   [ASM_MESON_TAC[filtration; sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (\x. ((X:num->A->real) (SUC n) x - X n x) * indicator_fn (A:A->bool) x)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (stopped_process (X:num->A->real) (tau:A->num) n)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_STOPPED_PROCESS THEN
    MAP_EVERY EXISTS_TAC [`FF:num->(A->bool)->bool`; `N:num`] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN
     `expectation (p:A prob_space) (stopped_process (X:num->A->real) (tau:A->num) (SUC n)) =
      expectation p (\x. stopped_process X tau n x + ((X (SUC n) x - X n x) * indicator_fn (A:A->bool) x))`
     SUBST1_TAC THENL
   [MATCH_MP_TAC EXPECTATION_EXT THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    BETA_TAC THEN
    MP_TAC(SPECL [`(X:num->A->real)`; `(tau:A->num)`; `n:num`; `x:A`]
      STOPPED_PROCESS_INCREMENT) THEN
    EXPAND_TAC "A" THEN REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(BETA_RULE(ISPECL [`p:A prob_space`;
     `stopped_process (X:num->A->real) (tau:A->num) n`;
     `\x:A. ((X:num->A->real) (SUC n) x - X n x) * indicator_fn (A:A->bool) x`]
     EXPECTATION_ADD)) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `A:A->bool`]) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (\x. (X:num->A->real) (SUC n) x * indicator_fn (A:A->bool) x) /\
                 integrable p (\x. X n x * indicator_fn A x)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
    ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
   SUBGOAL_THEN
     `expectation (p:A prob_space) (\x. ((X:num->A->real) (SUC n) x - X n x) * indicator_fn (A:A->bool) x) =
      expectation p (\x. X (SUC n) x * indicator_fn A x) -
      expectation p (\x. X n x * indicator_fn A x)` SUBST1_TAC THENL
   [SUBGOAL_THEN
      `(\x:A. ((X:num->A->real) (SUC n) x - X n x) * indicator_fn (A:A->bool) x) =
       (\x. X (SUC n) x * indicator_fn A x - X n x * indicator_fn A x)`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[EXPECTATION_SUB];
    ASM_REAL_ARITH_TAC]]);;

(* --- Bridge: simple_submartingale => submartingale optional stopping --- *)

let SIMPLE_SUBMARTINGALE_OPTIONAL_STOPPING_GE_GENERAL = prove
 (`!p:A prob_space FF X tau N.
    simple_submartingale p FF X /\ bounded_stopping_time p FF tau N
    ==> !n. expectation p (X 0) <= expectation p (stopped_process X tau n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
    SUBMARTINGALE_OPTIONAL_STOPPING_GE) THEN
  MAP_EVERY EXISTS_TAC [`FF:num->(A->bool)->bool`; `N:num`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SIMPLE_IMP_SUBMARTINGALE THEN ASM_REWRITE_TAC[]);;

(* --- Bridge: simple_supermartingale => supermartingale optional stopping --- *)

let SIMPLE_SUPERMARTINGALE_OPTIONAL_STOPPING_LE_GENERAL = prove
 (`!p:A prob_space FF X tau N.
    simple_supermartingale p FF X /\ bounded_stopping_time p FF tau N
    ==> !n. expectation p (stopped_process X tau n) <= expectation p (X 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
    SUPERMARTINGALE_OPTIONAL_STOPPING_LE) THEN
  MAP_EVERY EXISTS_TAC [`FF:num->(A->bool)->bool`; `N:num`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SIMPLE_IMP_SUPERMARTINGALE THEN ASM_REWRITE_TAC[]);;

(* ================================================================== *)
(* Conditional expectation tower property                             *)
(* ================================================================== *)

(* Multi-step simple_martingale property: for a IN FF m and m <= n,
   E[X_n * 1_a] = E[X_m * 1_a]. This is the integral form of
   E[X_n | FF_m] = X_m (a.e.). *)

let MARTINGALE_TOWER = prove
 (`!p:A prob_space FF X. martingale p FF X
    ==> !m n a. m <= n /\ a IN FF m
      ==> expectation p (\x. X n x * indicator_fn a x) =
          expectation p (\x. X m x * indicator_fn a x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[martingale] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?k. n = m + k:num` (CHOOSE_THEN SUBST_ALL_TAC) THENL
  [EXISTS_TAC `n - m:num` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `m:num <= m + k` THEN DISCH_THEN(K ALL_TAC) THEN
  SPEC_TAC(`k:num`,`k:num`) THEN INDUCT_TAC THENL
  [REWRITE_TAC[ADD_CLAUSES];
   REWRITE_TAC[ADD_CLAUSES] THEN
   SUBGOAL_THEN `(a:A->bool) IN (FF:num->(A->bool)->bool) (m + k)` ASSUME_TAC THENL
   [UNDISCH_TAC `(a:A->bool) IN (FF:num->(A->bool)->bool) m` THEN
    UNDISCH_TAC `filtration (p:A prob_space) FF` THEN
    REWRITE_TAC[filtration] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    DISCH_THEN(MP_TAC o SPECL [`m:num`; `m + k:num`]) THEN
    REWRITE_TAC[LE_ADD] THEN SET_TAC[];
    ASM_MESON_TAC[]]]);;

(* Multi-step simple_submartingale property *)

let SUBMARTINGALE_TOWER = prove
 (`!p:A prob_space FF X. submartingale p FF X
    ==> !m n a. m <= n /\ a IN FF m
      ==> expectation p (\x. X m x * indicator_fn a x) <=
          expectation p (\x. X n x * indicator_fn a x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[submartingale] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?k. n = m + k:num` (CHOOSE_THEN SUBST_ALL_TAC) THENL
  [EXISTS_TAC `n - m:num` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `m:num <= m + k` THEN DISCH_THEN(K ALL_TAC) THEN
  SPEC_TAC(`k:num`,`k:num`) THEN INDUCT_TAC THENL
  [REWRITE_TAC[ADD_CLAUSES; REAL_LE_REFL];
   REWRITE_TAC[ADD_CLAUSES] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `expectation (p:A prob_space) (\x. (X:num->A->real) (m + k) x * indicator_fn (a:A->bool) x)` THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `(a:A->bool) IN (FF:num->(A->bool)->bool) (m + k)` ASSUME_TAC THENL
   [UNDISCH_TAC `(a:A->bool) IN (FF:num->(A->bool)->bool) m` THEN
    UNDISCH_TAC `filtration (p:A prob_space) FF` THEN
    REWRITE_TAC[filtration] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    DISCH_THEN(MP_TAC o SPECL [`m:num`; `m + k:num`]) THEN
    REWRITE_TAC[LE_ADD] THEN SET_TAC[];
    ASM_MESON_TAC[]]]);;

(* Multi-step simple_supermartingale property *)

let SUPERMARTINGALE_TOWER = prove
 (`!p:A prob_space FF X. supermartingale p FF X
    ==> !m n a. m <= n /\ a IN FF m
      ==> expectation p (\x. X n x * indicator_fn a x) <=
          expectation p (\x. X m x * indicator_fn a x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[supermartingale] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?k. n = m + k:num` (CHOOSE_THEN SUBST_ALL_TAC) THENL
  [EXISTS_TAC `n - m:num` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `m:num <= m + k` THEN DISCH_THEN(K ALL_TAC) THEN
  SPEC_TAC(`k:num`,`k:num`) THEN INDUCT_TAC THENL
  [REWRITE_TAC[ADD_CLAUSES; REAL_LE_REFL];
   REWRITE_TAC[ADD_CLAUSES] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `expectation (p:A prob_space) (\x. (X:num->A->real) (m + k) x * indicator_fn (a:A->bool) x)` THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `(a:A->bool) IN (FF:num->(A->bool)->bool) (m + k)` ASSUME_TAC THENL
   [UNDISCH_TAC `(a:A->bool) IN (FF:num->(A->bool)->bool) m` THEN
    UNDISCH_TAC `filtration (p:A prob_space) FF` THEN
    REWRITE_TAC[filtration] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    DISCH_THEN(MP_TAC o SPECL [`m:num`; `m + k:num`]) THEN
    REWRITE_TAC[LE_ADD] THEN SET_TAC[];
    ASM_MESON_TAC[]]]);;

(* Tower property without m <= n restriction *)

let MARTINGALE_TOWER_EQ = prove
 (`!p:A prob_space FF X. martingale p FF X
    ==> !m n a. a IN FF (MIN m n)
      ==> expectation p (\x. X n x * indicator_fn a x) =
          expectation p (\x. X m x * indicator_fn a x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MARTINGALE_TOWER) THEN
  DISCH_TAC THEN
  DISJ_CASES_TAC(SPECL [`m:num`; `n:num`] LE_CASES) THENL
  [SUBGOAL_THEN `MIN m n = m` SUBST_ALL_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `n:num`; `a:A->bool`]) THEN
   ASM_REWRITE_TAC[];
   SUBGOAL_THEN `MIN m n = n` SUBST_ALL_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
   CONV_TAC SYM_CONV THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `m:num`; `a:A->bool`]) THEN
   ASM_REWRITE_TAC[]]);;

(* Characterization: martingale iff tower property holds *)

let MARTINGALE_CHARACTERIZATION = prove
 (`!p:A prob_space FF X.
    martingale p FF X <=>
    filtration p FF /\ adapted p FF X /\ (!n. integrable p (X n)) /\
    (!m n a. m <= n /\ a IN FF m
      ==> expectation p (\x. X n x * indicator_fn a x) =
          expectation p (\x. X m x * indicator_fn a x))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [DISCH_TAC THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[martingale]) THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC MARTINGALE_TOWER THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[martingale] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `SUC n`; `a:A->bool`]) THEN
   ASM_REWRITE_TAC[LE; LE_REFL]]);;
