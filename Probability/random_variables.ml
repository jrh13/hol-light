(* ========================================================================= *)
(* Random variables: definitions, measurability, and probability             *)
(* infrastructure (indexed families, Boole's inequality, continuity).        *)
(*                                                                           *)
(* Follows Williams "Probability with Martingales" Chapter 3.                *)
(* ========================================================================= *)

needs "Probability/measure.ml";;

(* ------------------------------------------------------------------------- *)
(* Chapter 3: Random Variables                                               *)
(* ------------------------------------------------------------------------- *)

let random_variable = new_definition
  `random_variable (p:(A)prob_space) (X:A->real) <=>
   (!a. {x | x IN prob_carrier p /\ X x <= a} IN prob_events p)`;;

let RANDOM_VARIABLE_CONST = prove
  (`!p:A prob_space c. random_variable p (\x. c)`,
   REPEAT GEN_TAC THEN REWRITE_TAC[random_variable] THEN
   TRY BETA_TAC THEN
   X_GEN_TAC `a:real` THEN
   ASM_CASES_TAC `c:real <= a` THENL
   [SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ c:real <= a} = prob_carrier p`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[];
     REWRITE_TAC[PROB_CARRIER_IN_EVENTS]];
    SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ c:real <= a} = {}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; NOT_EXISTS_THM] THEN
     ASM_MESON_TAC[];
     REWRITE_TAC[PROB_EMPTY_IN_EVENTS]]]);;


(* ------------------------------------------------------------------------- *)
(* Indicator functions                                                       *)
(* ------------------------------------------------------------------------- *)

let indicator_fn = new_definition
  `indicator_fn (a:A->bool) (x:A) = if x IN a then &1 else &0`;;


(* ------------------------------------------------------------------------- *)
(* Borel-preimage characterization of random variables.                      *)
(*                                                                           *)
(* A function X is a random variable (defined via the half-lines             *)
(* {X <= a} being events) iff the preimage X^-1(B) of EVERY Borel set B of   *)
(* the real line is an event.  This is Williams "Probability with            *)
(* Martingales" 3.1-3.2: the half-lines generate the Borel sigma-algebra,    *)
(* so the two notions coincide.  We use borel_in euclideanreal (from         *)
(* borel.ml) for the Borel sets of the reals.                                *)
(* ------------------------------------------------------------------------- *)

(* The < half-line preimage as a countable union of <= half-lines.           *)
let RV_PREIMAGE_LT_EQ_UNIONS = prove
 (`!p (X:A->real) a.
     {x | x IN prob_carrier p /\ X x < a} =
     UNIONS {{x | x IN prob_carrier p /\ X x <= a - inv(&n + &1)} | n IN (:num)}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[UNIONS_GSPEC; EXTENSION; IN_ELIM_THM; IN_UNIV] THEN
  X_GEN_TAC `y:A` THEN EQ_TAC THENL
  [STRIP_TAC THEN
   MP_TAC(SPEC `a - X(y:A):real` REAL_ARCH_INV) THEN
   ASM_REWRITE_TAC[REAL_SUB_LT] THEN
   DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `inv(&n + &1) <= inv(&n)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE; REAL_OF_NUM_ADD] THEN
    ASM_ARITH_TAC;
    ASM_REAL_ARITH_TAC];
   DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `&0 < inv(&n + &1)` MP_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]]);;

(* Half-line and interval preimages are events, for a random variable.       *)
let RV_PREIMAGE_LE = prove
 (`!p (X:A->real) a.
     random_variable p X
     ==> {x | x IN prob_carrier p /\ X x <= a} IN prob_events p`,
  SIMP_TAC[random_variable]);;

let RV_PREIMAGE_LT = prove
 (`!p (X:A->real) a.
     random_variable p X
     ==> {x | x IN prob_carrier p /\ X x < a} IN prob_events p`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RV_PREIMAGE_LT_EQ_UNIONS] THEN
  MATCH_MP_TAC PROB_COUNTABLE_UNION_IN_EVENTS THEN CONJ_TAC THENL
  [REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN
   GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[random_variable]) THEN
   DISCH_THEN(MP_TAC o SPEC `a - inv(&n + &1)`) THEN REWRITE_TAC[];
   REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC COUNTABLE_IMAGE THEN
   REWRITE_TAC[NUM_COUNTABLE]]);;

let RV_PREIMAGE_GE = prove
 (`!p (X:A->real) a.
     random_variable p X
     ==> {x | x IN prob_carrier p /\ X x >= a} IN prob_events p`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ X x >= a} =
     prob_carrier p DIFF {x | x IN prob_carrier p /\ X x < a}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN
   X_GEN_TAC `y:A` THEN ASM_CASES_TAC `(y:A) IN prob_carrier p` THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   MATCH_MP_TAC PROB_COMPL_IN_EVENTS THEN
   ASM_SIMP_TAC[RV_PREIMAGE_LT]]);;

let RV_PREIMAGE_GT = prove
 (`!p (X:A->real) a.
     random_variable p X
     ==> {x | x IN prob_carrier p /\ X x > a} IN prob_events p`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ X x > a} =
     prob_carrier p DIFF {x | x IN prob_carrier p /\ X x <= a}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN
   X_GEN_TAC `y:A` THEN ASM_CASES_TAC `(y:A) IN prob_carrier p` THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   MATCH_MP_TAC PROB_COMPL_IN_EVENTS THEN
   ASM_SIMP_TAC[RV_PREIMAGE_LE]]);;

let RV_PREIMAGE_REAL_INTERVAL = prove
 (`!p (X:A->real) a b.
     random_variable p X
     ==> {x | x IN prob_carrier p /\ X x IN real_interval(a,b)} IN prob_events p`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ X x IN real_interval(a,b)} =
     {x | x IN prob_carrier p /\ X x > a} INTER
     {x | x IN prob_carrier p /\ X x < b}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
   X_GEN_TAC `y:A` THEN ASM_CASES_TAC `(y:A) IN prob_carrier p` THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN
   ASM_SIMP_TAC[RV_PREIMAGE_GT; RV_PREIMAGE_LT]]);;

(* Every real-open set is a countable union of open intervals (real line).   *)
let REAL_OPEN_COUNTABLE_UNION_REAL_INTERVAL = prove
 (`!s:real->bool.
       real_open s
       ==> ?D. COUNTABLE D /\
               (!i. i IN D ==> i SUBSET s /\ ?a b. i = real_interval(a,b)) /\
               UNIONS D = s`,
  GEN_TAC THEN REWRITE_TAC[REAL_OPEN] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_COUNTABLE_UNION_OPEN_INTERVALS) THEN
  DISCH_THEN(X_CHOOSE_THEN `D:(real^1->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (IMAGE drop) D` THEN
  ASM_SIMP_TAC[COUNTABLE_IMAGE] THEN CONJ_TAC THENL
  [REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `j:real^1->bool` THEN
   DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `j:real^1->bool`) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `a:real^1` (X_CHOOSE_THEN `b:real^1` SUBST_ALL_TAC))) THEN
   REWRITE_TAC[IMAGE_DROP_INTERVAL] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
      `j SUBSET IMAGE lift s
       ==> IMAGE drop j SUBSET IMAGE drop (IMAGE lift s)`)) THEN
    REWRITE_TAC[IMAGE_DROP_INTERVAL; GSYM IMAGE_o; o_DEF; LIFT_DROP; IMAGE_ID];
    MESON_TAC[]];
   REWRITE_TAC[GSYM IMAGE_UNIONS] THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[GSYM IMAGE_o; o_DEF; LIFT_DROP; IMAGE_ID]]);;

(* The open base case: preimage of any real-open set is an event.            *)
let RV_PREIMAGE_REAL_OPEN = prove
 (`!p (X:A->real) t.
     random_variable p X /\ real_open t
     ==> {x | x IN prob_carrier p /\ X x IN t} IN prob_events p`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_OPEN_COUNTABLE_UNION_REAL_INTERVAL) THEN
  DISCH_THEN(X_CHOOSE_THEN `D:(real->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ X x IN UNIONS D} =
     UNIONS (IMAGE (\i:real->bool. {x:A | x IN prob_carrier p /\ X x IN i}) D)`
    SUBST1_TAC THENL
  [REWRITE_TAC[UNIONS_IMAGE; UNIONS_GSPEC; EXTENSION; IN_ELIM_THM] THEN
   SET_TAC[];
   ALL_TAC] THEN
  MATCH_MP_TAC PROB_COUNTABLE_UNION_IN_EVENTS THEN
  ASM_SIMP_TAC[COUNTABLE_IMAGE] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `i:real->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:real->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real` (X_CHOOSE_THEN `b:real` SUBST1_TAC)) THEN
  ASM_SIMP_TAC[RV_PREIMAGE_REAL_INTERVAL]);;

(* Main characterization: random variable iff all Borel preimages are events.*)
let RANDOM_VARIABLE_PREIMAGE_BOREL_IN = prove
 (`!p (X:A->real).
     random_variable p X <=>
     !b. borel_in euclideanreal b
         ==> {x | x IN prob_carrier p /\ X x IN b} IN prob_events p`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [DISCH_TAC THEN MATCH_MP_TAC borel_in_INDUCT THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OPEN_IN] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC RV_PREIMAGE_REAL_OPEN THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL] THEN X_GEN_TAC `s:real->bool` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\ X x IN (:real) DIFF s} =
       prob_carrier p DIFF {x | x IN prob_carrier p /\ X x IN s}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNIV; IN_ELIM_THM] THEN SET_TAC[];
     MATCH_MP_TAC PROB_COMPL_IN_EVENTS THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `u:(real->bool)->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\ X x IN UNIONS u} =
       UNIONS (IMAGE (\s:real->bool. {x:A | x IN prob_carrier p /\ X x IN s}) u)`
      SUBST1_TAC THENL
    [REWRITE_TAC[UNIONS_IMAGE; UNIONS_GSPEC; EXTENSION; IN_ELIM_THM] THEN
     SET_TAC[];
     MATCH_MP_TAC PROB_COUNTABLE_UNION_IN_EVENTS THEN
     ASM_SIMP_TAC[COUNTABLE_IMAGE] THEN
     REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]]];
   DISCH_TAC THEN REWRITE_TAC[random_variable] THEN X_GEN_TAC `a:real` THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `{y:real | y <= a}`) THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC CLOSED_IMP_BOREL_IN THEN
    REWRITE_TAC[GSYM REAL_CLOSED_IN; REAL_CLOSED_HALFSPACE_LE];
    REWRITE_TAC[IN_ELIM_THM]]]);;

(* Payoff: a Borel-measurable function of a random variable is a random       *)
(* variable (Williams "Probability with Martingales" 3.8).  This is the        *)
(* natural general form: the preimage of a Borel set under g is itself Borel   *)
(* (directly from the definition of borel_measurable_map), and the preimage    *)
(* of THAT under X is an event by RANDOM_VARIABLE_PREIMAGE_BOREL_IN.            *)
let RANDOM_VARIABLE_BOREL_MEASURABLE_COMPOSE = prove
 (`!p (X:A->real) g.
     random_variable p X /\
     borel_measurable_map (euclideanreal,euclideanreal) g
     ==> random_variable p (\x. g(X x))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[RANDOM_VARIABLE_PREIMAGE_BOREL_IN] THEN
  X_GEN_TAC `b:real->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [borel_measurable_map]) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEANREAL] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `b:real->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ (g:real->real) (X x) IN b} =
     {x:A | x IN prob_carrier p /\ X x IN {y:real | y IN (:real) /\ g y IN b}}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIV];
   UNDISCH_TAC `random_variable p (X:A->real)` THEN
   REWRITE_TAC[RANDOM_VARIABLE_PREIMAGE_BOREL_IN] THEN
   DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* A continuous function of a random variable is a random variable -- now an   *)
(* immediate corollary, since continuous maps are Borel measurable.            *)
let RANDOM_VARIABLE_CONTINUOUS_MAP_COMPOSE = prove
 (`!p (X:A->real) g.
     random_variable p X /\ continuous_map (euclideanreal,euclideanreal) g
     ==> random_variable p (\x. g(X x))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RANDOM_VARIABLE_BOREL_MEASURABLE_COMPOSE THEN
  ASM_SIMP_TAC[CONTINUOUS_IMP_BOREL_MEASURABLE_MAP]);;

(* ------------------------------------------------------------------------- *)
(* Closure under pointwise sequential limits.                                *)
(*                                                                           *)
(* If X n is a random variable for each n and X n x -> L x pointwise on the  *)
(* carrier, then L is a random variable.  The level set {L > a} is expressed *)
(* through countable set operations on the {X n >= a + 1/(j+1)} events       *)
(* (Williams "Probability with Martingales" 3.x).                            *)
(* ------------------------------------------------------------------------- *)

(* Characterization by open rays: it suffices that every {X > a} is an event. *)
(* (Named _SUFFICIENT to distinguish from the forward RV_PREIMAGE_GT.)        *)
let RANDOM_VARIABLE_GT_SUFFICIENT = prove
 (`!p (X:A->real).
     (!a. {x | x IN prob_carrier p /\ X x > a} IN prob_events p)
     ==> random_variable p X`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[random_variable] THEN X_GEN_TAC `a:real` THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ X x <= a} =
     prob_carrier p DIFF {x | x IN prob_carrier p /\ X x > a}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN
   X_GEN_TAC `y:A` THEN ASM_CASES_TAC `(y:A) IN prob_carrier p` THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   MATCH_MP_TAC PROB_COMPL_IN_EVENTS THEN ASM_SIMP_TAC[]]);;

(* The level set of a pointwise limit, via countable unions/intersections.    *)
let RV_LIMIT_GT_EQ = prove
 (`!p (X:num->A->real) L a.
     (!x. x IN prob_carrier p ==> ((\n. X n x) ---> L x) sequentially)
     ==> {x | x IN prob_carrier p /\ L x > a} =
         UNIONS {INTERS {{x | x IN prob_carrier p /\ X n x >= a + inv(&j + &1)}
                         | n IN from N} | j,N | T}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `y:A` THEN
  REWRITE_TAC[IN_ELIM_THM; UNIONS_GSPEC; INTERS_GSPEC; IN_FROM] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
  [STRIP_TAC THEN
   FIRST_ASSUM(MP_TAC o ISPEC `y:A`) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN BETA_TAC THEN
   DISCH_THEN(LABEL_TAC "lim") THEN
   SUBGOAL_THEN `?j. ~(j = 0) /\ &0 < inv(&j) /\ inv(&j) < L(y:A) - a`
     STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_ARCH_INV] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 < L(y:A) - (a + inv(&j + &1))` ASSUME_TAC THENL
   [SUBGOAL_THEN `inv(&j + &1) <= inv(&j)` MP_TAC THENL
    [MATCH_MP_TAC REAL_LE_INV2 THEN
     REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE; REAL_OF_NUM_ADD] THEN
     ASM_ARITH_TAC;
     ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
   REMOVE_THEN "lim" (MP_TAC o SPEC `L(y:A) - (a + inv(&j + &1))`) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "ev")) THEN
   MAP_EVERY EXISTS_TAC [`j:num`; `N:num`] THEN
   X_GEN_TAC `n:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
   REMOVE_THEN "ev" (MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
   REAL_ARITH_TAC;
   DISCH_THEN(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `N:num` ASSUME_TAC)) THEN
   SUBGOAL_THEN `y:A IN prob_carrier p` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN REWRITE_TAC[LE_REFL] THEN
    SIMP_TAC[]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `a + inv(&j + &1) <= L(y:A)` MP_TAC THENL
   [MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LBOUND) THEN
    EXISTS_TAC `\n:num. (X:num->A->real) n y` THEN
    ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN BETA_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH
      `&0 < inv(&j + &1) ==> a + inv(&j + &1) <= L ==> L > a`) THEN
    REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC]]);;

let RANDOM_VARIABLE_LIMIT = prove
 (`!p (X:num->A->real) L.
     (!n. random_variable p (X n)) /\
     (!x. x IN prob_carrier p ==> ((\n. X n x) ---> L x) sequentially)
     ==> random_variable p L`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_GT_SUFFICIENT THEN
  X_GEN_TAC `a:real` THEN ASM_SIMP_TAC[RV_LIMIT_GT_EQ] THEN
  MATCH_MP_TAC PROB_COUNTABLE_UNION_IN_EVENTS THEN CONJ_TAC THENL
  [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC PROB_COUNTABLE_INTERS_IN_EVENTS THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_FROM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC RV_PREIMAGE_GE THEN REWRITE_TAC[ETA_AX] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC COUNTABLE_SUBSET THEN
    EXISTS_TAC `IMAGE (\n. {x:A | x IN prob_carrier p /\
        (X:num->A->real) n x >= a + inv(&j + &1)}) (:num)` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[NUM_COUNTABLE];
     REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE; IN_UNIV] THEN
     REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; IN_FROM] THEN
    MAP_EVERY EXISTS_TAC
     [`{x:A | x IN prob_carrier p /\ (X:num->A->real) N x >= a + inv(&j + &1)}`;
      `N:num`] THEN
    REWRITE_TAC[LE_REFL]];
   MATCH_MP_TAC COUNTABLE_SUBSET THEN
   EXISTS_TAC `IMAGE (\(j,N). INTERS {{x:A | x IN prob_carrier p /\
                 X n x >= a + inv(&j + &1)} | n IN from N}) (:num#num)` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC COUNTABLE_IMAGE THEN
    REWRITE_TAC[GSYM CROSS_UNIV] THEN MATCH_MP_TAC COUNTABLE_CROSS THEN
    REWRITE_TAC[NUM_COUNTABLE];
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE; IN_UNIV] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `(j:num,N:num)` THEN REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Random variable properties                                                *)
(* ------------------------------------------------------------------------- *)

(* NEG and SCALE are instances of "continuous function of a random variable  *)
(* is a random variable" (RANDOM_VARIABLE_CONTINUOUS_MAP_COMPOSE above, via    *)
(* the Borel-preimage characterization): negation and scaling are continuous   *)
(* maps euclideanreal->euclideanreal.                                          *)

let RANDOM_VARIABLE_NEG = prove
  (`!p:A prob_space X.
      random_variable p X ==> random_variable p (\x. --(X x))`,
   REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `\y:real. --y`]
     RANDOM_VARIABLE_CONTINUOUS_MAP_COMPOSE) THEN
   REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_NEG THEN
   REWRITE_TAC[CONTINUOUS_MAP_ID]);;

let RANDOM_VARIABLE_SCALE = prove
  (`!p:A prob_space X c.
      random_variable p X /\ &0 < c
      ==> random_variable p (\x. c * X x)`,
   REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `\y:real. c * y`]
     RANDOM_VARIABLE_CONTINUOUS_MAP_COMPOSE) THEN
   REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_LMUL THEN
   REWRITE_TAC[CONTINUOUS_MAP_ID]);;


(* ------------------------------------------------------------------------- *)
(* Indexed families of events (using num->event)                             *)
(* ------------------------------------------------------------------------- *)

let PROB_INDEXED_UNION_IN_EVENTS = prove
  (`!p:A prob_space A.
      (!n:num. A n IN prob_events p)
      ==> UNIONS {A n | n IN (:num)} IN prob_events p`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC PROB_COUNTABLE_UNION_IN_EVENTS THEN
   CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIV] THEN ASM_MESON_TAC[];
    REWRITE_TAC[SIMPLE_IMAGE] THEN
    MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[NUM_COUNTABLE]]);;

let PROB_INDEXED_INTER_IN_EVENTS = prove
  (`!p:A prob_space A.
      (!n:num. A n IN prob_events p)
      ==> INTERS {A n | n IN (:num)} IN prob_events p`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC PROB_COUNTABLE_INTERS_IN_EVENTS THEN
   REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIV] THEN ASM_MESON_TAC[];
    REWRITE_TAC[SIMPLE_IMAGE] THEN
    MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[NUM_COUNTABLE];
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; IN_UNIV] THEN
    MESON_TAC[]]);;

let PROB_FINITE_INDEXED_UNION_IN_EVENTS = prove
  (`!p:A prob_space (A:num->A->bool) n.
      (!i. i <= n ==> A i IN prob_events p)
      ==> UNIONS (IMAGE A (0..n)) IN prob_events p`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC PROB_FINITE_UNION_IN_EVENTS THEN
   CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_NUMSEG]) THEN
    ARITH_TAC;
    MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_NUMSEG]]);;


(* ------------------------------------------------------------------------- *)
(* Boole's inequality (finite subadditivity for indexed families)            *)
(* ------------------------------------------------------------------------- *)

let PROB_FINITE_SUBADDITIVE = prove
  (`!p:A prob_space (A:num->A->bool) n.
      (!i. i <= n ==> A i IN prob_events p)
      ==> prob p (UNIONS (IMAGE A (0..n))) <= sum (0..n) (\i. prob p (A i))`,
   GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[NUMSEG_SING; IMAGE_CLAUSES; UNIONS_INSERT; UNIONS_0] THEN
    REWRITE_TAC[SUM_SING; UNION_EMPTY] THEN
    TRY BETA_TAC THEN
    DISCH_TAC THEN REAL_ARITH_TAC;
    DISCH_TAC THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `0 <= SUC n`] THEN
    REWRITE_TAC[NUMSEG_CLAUSES; ARITH_RULE `0 <= SUC n`] THEN
    REWRITE_TAC[IMAGE_CLAUSES; UNIONS_INSERT] THEN
    TRY BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `prob p (A (SUC n):A->bool) +
                prob p (UNIONS (IMAGE (A:num->A->bool) (0..n)))` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC PROB_SUBADDITIVE THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
      MATCH_MP_TAC PROB_FINITE_UNION_IN_EVENTS THEN
      CONJ_TAC THENL
      [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_NUMSEG] THEN
       REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
       MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_NUMSEG]]];
     MATCH_MP_TAC(REAL_ARITH `(b:real) <= c ==> a + b <= c + a`) THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;


(* ------------------------------------------------------------------------- *)
(* Monotonicity helpers for increasing sequences                             *)
(* ------------------------------------------------------------------------- *)

let INCREASING_MONO = prove
  (`!(A:num->A->bool) m n.
      (!k. A k SUBSET A (SUC k)) /\ m <= n ==> A m SUBSET A n`,
   GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [SIMP_TAC[LE; SUBSET_REFL];
    STRIP_TAC THEN ASM_CASES_TAC `m = SUC n` THENL
    [ASM_REWRITE_TAC[SUBSET_REFL];
     MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(A:num->A->bool) n` THEN
     CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ASM_ARITH_TAC];
      ASM_MESON_TAC[]]]]);;

let INCREASING_UNION_DECOMP = prove
  (`!(A:num->A->bool).
      (!n. A n SUBSET A (SUC n))
      ==> UNIONS {A n | n IN (:num)} =
          A 0 UNION UNIONS {A (SUC n) DIFF A n | n IN (:num)}`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[EXTENSION; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
   X_GEN_TAC `x:A` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
    SPEC_TAC(`n:num`, `n:num`) THEN INDUCT_TAC THENL
    [DISCH_TAC THEN DISJ1_TAC THEN ASM_REWRITE_TAC[];
     DISCH_TAC THEN ASM_CASES_TAC `(x:A) IN A (n:num)` THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `n:num` THEN
      REWRITE_TAC[IN_DIFF] THEN ASM_REWRITE_TAC[]]];
    DISCH_THEN(DISJ_CASES_TAC) THENL
    [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[];
     FIRST_X_ASSUM(X_CHOOSE_THEN `n:num` MP_TAC) THEN
     REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
     EXISTS_TAC `SUC n` THEN ASM_REWRITE_TAC[]]]);;

let INCREASING_A0_DISJOINT_DIFFS = prove
  (`!(A:num->A->bool).
      (!n. A n SUBSET A (SUC n))
      ==> DISJOINT (A 0) (UNIONS {A (SUC n) DIFF A n | n IN (:num)})`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY;
               UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV; IN_DIFF] THEN
   X_GEN_TAC `x:A` THEN
   ASM_CASES_TAC `(x:A) IN A 0` THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[NOT_EXISTS_THM; DE_MORGAN_THM] THEN
   X_GEN_TAC `n:num` THEN DISJ2_TAC THEN
   SUBGOAL_THEN `(A:num->A->bool) 0 SUBSET A n` ASSUME_TAC THENL
   [MATCH_MP_TAC INCREASING_MONO THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LE_0]];
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN ASM_MESON_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Continuity of probability from below                                      *)
(* If A_0 SUBSET A_1 SUBSET ... and A = UNIONS A_n, then P(A_n) --> P(A)     *)
(* Uses ---> and sequentially from the library                               *)
(* ------------------------------------------------------------------------- *)

let PROB_CONTINUITY_FROM_BELOW = prove
  (`!p:A prob_space A.
      (!n. A n IN prob_events p) /\
      (!n. A n SUBSET A (SUC n))
      ==> ((\n. prob p (A n)) --->
           prob p (UNIONS {A n | n IN (:num)})) sequentially`,
   REPEAT STRIP_TAC THEN
   ABBREV_TAC `B = \n:num. A(SUC n) DIFF (A:num->A->bool) n` THEN
   SUBGOAL_THEN `!n:num. (B:num->A->bool) n IN prob_events (p:A prob_space)`
     ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "B" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PROB_DIFF_IN_EVENTS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `!i j. ~(i = j) ==> DISJOINT ((B:num->A->bool) i) (B j)`
     ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_DIFF] THEN
    X_GEN_TAC `x:A` THEN
    ASM_CASES_TAC `i:num < j` THENL
    [SUBGOAL_THEN `(A:num->A->bool) (SUC i) SUBSET A j` MP_TAC THENL
     [MATCH_MP_TAC INCREASING_MONO THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ASM_ARITH_TAC];
      REWRITE_TAC[SUBSET] THEN MESON_TAC[]];
     SUBGOAL_THEN `(A:num->A->bool) (SUC j) SUBSET A i` MP_TAC THENL
     [MATCH_MP_TAC INCREASING_MONO THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ASM_ARITH_TAC];
      REWRITE_TAC[SUBSET] THEN MESON_TAC[]]];
    ALL_TAC] THEN
   SUBGOAL_THEN `UNIONS {(B:num->A->bool) n | n IN (:num)} IN
                  prob_events (p:A prob_space)` ASSUME_TAC THENL
   [MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `prob (p:A prob_space) (UNIONS {(A:num->A->bool) n | n IN (:num)}) =
      prob p (A 0) + prob p (UNIONS {(B:num->A->bool) n | n IN (:num)})`
     ASSUME_TAC THENL
   [SUBGOAL_THEN `UNIONS {(A:num->A->bool) n | n IN (:num)} =
                   A 0 UNION UNIONS {(B:num->A->bool) n | n IN (:num)}`
     SUBST1_TAC THENL
    [EXPAND_TAC "B" THEN REWRITE_TAC[] THEN
     MATCH_MP_TAC INCREASING_UNION_DECOMP THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    MATCH_MP_TAC PROB_ADDITIVE THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "B" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC INCREASING_A0_DISJOINT_DIFFS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `!N. sum (0..N) (\n. prob (p:A prob_space) ((B:num->A->bool) n)) =
          prob p ((A:num->A->bool) (SUC N)) - prob p (A 0)`
     ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `!n. prob (p:A prob_space) ((B:num->A->bool) n) =
                        prob p ((A:num->A->bool) (SUC n)) - prob p (A n)`
      (fun th -> REWRITE_TAC[th]) THENL
    [GEN_TAC THEN EXPAND_TAC "B" THEN REWRITE_TAC[] THEN
     MATCH_MP_TAC PROB_DIFF_SUBSET THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[ADD1; SUM_DIFFS_ALT; LE_0]];
    ALL_TAC] THEN
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   X_GEN_TAC `e:real` THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `B:num->A->bool`]
     PROB_COUNTABLY_ADDITIVE) THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[real_sums; FROM_0; INTER_UNIV; REALLIM_SEQUENTIALLY] THEN
   DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN
   EXISTS_TAC `SUC N0` THEN
   X_GEN_TAC `n:num` THEN DISCH_TAC THEN
   SUBGOAL_THEN `?m:num. n = SUC m /\ N0 <= m`
     (CHOOSE_THEN STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `n - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   FIRST_ASSUM(SUBST1_TAC o check (is_eq o concl)) THEN
   REWRITE_TAC[REAL_ARITH `x - a - b = x - (a + b):real`] THEN
   ASM_REWRITE_TAC[]);;

let PROB_CONTINUITY_FROM_ABOVE = prove
  (`!p:A prob_space A.
      (!n. A n IN prob_events p) /\
      (!n. A (SUC n) SUBSET A n)
      ==> ((\n. prob p (A n)) --->
           prob p (INTERS {A n | n IN (:num)})) sequentially`,
   REPEAT STRIP_TAC THEN
   ABBREV_TAC `C = \n:num. (A:num->A->bool) 0 DIFF A n` THEN
   SUBGOAL_THEN `!n:num. (A:num->A->bool) n SUBSET A 0` ASSUME_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[SUBSET_REFL] THEN
    ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
   SUBGOAL_THEN `!n. (C:num->A->bool) n IN prob_events (p:A prob_space)`
     ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "C" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PROB_DIFF_IN_EVENTS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `!n. (C:num->A->bool) n SUBSET C(SUC n)` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "C" THEN REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `INTERS {(A:num->A->bool) n | n IN (:num)} SUBSET A 0`
     ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTERS; IN_ELIM_THM; IN_UNIV] THEN
    GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(A:num->A->bool) 0`) THEN
    ANTS_TAC THENL [EXISTS_TAC `0` THEN REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
   SUBGOAL_THEN `INTERS {(A:num->A->bool) n | n IN (:num)} IN
                  prob_events (p:A prob_space)` ASSUME_TAC THENL
   [MATCH_MP_TAC PROB_INDEXED_INTER_IN_EVENTS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `!n. prob (p:A prob_space) ((C:num->A->bool) n) =
                       prob p ((A:num->A->bool) 0) - prob p (A n)`
     ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "C" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PROB_DIFF_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `prob (p:A prob_space) (UNIONS {(C:num->A->bool) n | n IN (:num)}) =
      prob p ((A:num->A->bool) 0) -
      prob p (INTERS {A n | n IN (:num)})`
     ASSUME_TAC THENL
   [SUBGOAL_THEN
      `UNIONS {(C:num->A->bool) n | n IN (:num)} =
       (A:num->A->bool) 0 DIFF INTERS {A n | n IN (:num)}`
      SUBST1_TAC THENL
    [EXPAND_TAC "C" THEN REWRITE_TAC[] THEN
     REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `x:A` THEN
     REWRITE_TAC[IN_UNIONS; IN_DIFF; IN_INTERS;
                  IN_ELIM_THM; IN_UNIV] THEN
     EQ_TAC THENL
     [(* Forward *)
      DISCH_THEN(X_CHOOSE_THEN `S:A->bool`
        (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `m:num` ASSUME_TAC) MP_TAC)) THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[NOT_FORALL_THM] THEN
      EXISTS_TAC `(A:num->A->bool) m` THEN
      REWRITE_TAC[NOT_IMP] THEN
      CONJ_TAC THENL
      [EXISTS_TAC `m:num` THEN REWRITE_TAC[]; ASM_REWRITE_TAC[]];
      (* Backward *)
      STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o
        GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
      REWRITE_TAC[NOT_IMP] THEN
      DISCH_THEN(X_CHOOSE_THEN `S:A->bool`
        (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `m:num` ASSUME_TAC) ASSUME_TAC)) THEN
      FIRST_X_ASSUM(fun th -> SUBST_ALL_TAC th) THEN
      EXISTS_TAC `(A:num->A->bool) 0 DIFF A m` THEN
      CONJ_TAC THENL
      [EXISTS_TAC `m:num` THEN REWRITE_TAC[];
       REWRITE_TAC[IN_DIFF] THEN ASM_REWRITE_TAC[]]];
     MATCH_MP_TAC PROB_DIFF_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   X_GEN_TAC `e:real` THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `C:num->A->bool`]
     PROB_CONTINUITY_FROM_BELOW) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
   EXISTS_TAC `N:num` THEN
   X_GEN_TAC `n:num` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
   ASM_REWRITE_TAC[] THEN
   ASM_REWRITE_TAC[REAL_ARITH `(a - x) - (a - y):real = --(x - y)`;
                    REAL_ABS_NEG]);;

(* ------------------------------------------------------------------------- *)
(* The distribution (law / pushforward measure) of a random variable.          *)
(*                                                                            *)
(* distribution p X b = P(X IN b) for a Borel set b -- the pushforward of the  *)
(* probability measure along X.  It is a probability measure on the real Borel  *)
(* sets: nonneg, total mass 1, countably additive.  This is the "law of X"      *)
(* (Williams "Probability with Martingales" Ch 3); its restriction to the       *)
(* half-lines is the distribution function distribution_fn (CDF, expectation.ml).*)
(* ------------------------------------------------------------------------- *)

let distribution = new_definition
  `distribution (p:A prob_space) (X:A->real) (b:real->bool) =
   prob p {x | x IN prob_carrier p /\ X x IN b}`;;

(* The preimage of a Borel set under a random variable is an event. *)
let DISTRIBUTION_IN_EVENTS = prove
 (`!p (X:A->real) b.
     random_variable p X /\ borel_in euclideanreal b
     ==> {x | x IN prob_carrier p /\ X x IN b} IN prob_events p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
    MP_TAC(SPEC `b:real->bool`
      (REWRITE_RULE[RANDOM_VARIABLE_PREIMAGE_BOREL_IN] th))) THEN
  ASM_REWRITE_TAC[]);;

let DISTRIBUTION_POS = prove
 (`!p (X:A->real) b.
     random_variable p X /\ borel_in euclideanreal b
     ==> &0 <= distribution p X b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[distribution] THEN
  MATCH_MP_TAC PROB_POSITIVE THEN MATCH_MP_TAC DISTRIBUTION_IN_EVENTS THEN
  ASM_REWRITE_TAC[]);;

let DISTRIBUTION_LE_1 = prove
 (`!p (X:A->real) b.
     random_variable p X /\ borel_in euclideanreal b
     ==> distribution p X b <= &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[distribution] THEN
  MATCH_MP_TAC PROB_LE_1 THEN MATCH_MP_TAC DISTRIBUTION_IN_EVENTS THEN
  ASM_REWRITE_TAC[]);;

let DISTRIBUTION_UNIV = prove
 (`!p (X:A->real). distribution p X (:real) = &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[distribution; IN_UNIV] THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p} = prob_carrier p` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM]; REWRITE_TAC[PROB_SPACE]]);;

let DISTRIBUTION_EMPTY = prove
 (`!p (X:A->real). distribution p X {} = &0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[distribution; NOT_IN_EMPTY; EMPTY_GSPEC; PROB_EMPTY]);;

let DISTRIBUTION_MONO = prove
 (`!p (X:A->real) b c.
     random_variable p X /\ borel_in euclideanreal b /\
     borel_in euclideanreal c /\ b SUBSET c
     ==> distribution p X b <= distribution p X c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[distribution] THEN
  MATCH_MP_TAC PROB_MONO THEN REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC DISTRIBUTION_IN_EVENTS THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC DISTRIBUTION_IN_EVENTS THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM SET_TAC[]]);;

(* Countable additivity: the law is a probability measure on the Borel sets. *)
let DISTRIBUTION_COUNTABLY_ADDITIVE = prove
 (`!p (X:A->real) B.
     random_variable p X /\ (!n. borel_in euclideanreal (B n)) /\
     (!i j. ~(i = j) ==> DISJOINT (B i) (B j))
     ==> ((\n. distribution p X (B n)) real_sums
          distribution p X (UNIONS {B n | n IN (:num)})) (from 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[distribution] THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ X x IN UNIONS {(B:num->real->bool) n | n IN (:num)}} =
     UNIONS {{x:A | x IN prob_carrier p /\ X x IN B n} | n IN (:num)}`
    SUBST1_TAC THENL
  [REWRITE_TAC[UNIONS_GSPEC; EXTENSION; IN_ELIM_THM] THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `\n:num. {x:A | x IN prob_carrier p /\ X x IN (B:num->real->bool) n}`]
    PROB_COUNTABLY_ADDITIVE) THEN
  BETA_TAC THEN ANTS_TAC THENL
  [CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC DISTRIBUTION_IN_EVENTS THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN DISCH_TAC THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`]) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN ASM SET_TAC[]];
   REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Joint distribution function of a pair of random variables.                  *)
(* joint_distribution_fn p X Y a b = P(X <= a, Y <= b).                        *)
(* ------------------------------------------------------------------------- *)

(* The rectangle preimage {X <= a, Y <= b} is an event. *)
let JOINT_RECTANGLE_IN_EVENTS = prove
 (`!p (X:A->real) Y a b.
     random_variable p X /\ random_variable p Y
     ==> {w | w IN prob_carrier p /\ X w <= a /\ Y w <= b} IN prob_events p`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{w:A | w IN prob_carrier p /\ X w <= a /\ Y w <= b} =
    {w | w IN prob_carrier p /\ X w <= a} INTER
    {w | w IN prob_carrier p /\ Y w <= b}`
   SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN
  CONJ_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC th THEN
    FIRST_X_ASSUM(fun th2 -> MP_TAC th2)) THEN
  REWRITE_TAC[random_variable] THEN MESON_TAC[]);;

let joint_distribution_fn = new_definition
  `joint_distribution_fn (p:A prob_space) (X:A->real) (Y:A->real)
                         (a:real) (b:real) =
   prob p {w | w IN prob_carrier p /\ X w <= a /\ Y w <= b}`;;

(* Symmetry of the joint distribution function. *)
let JOINT_DISTRIBUTION_SYM = prove
 (`!p (X:A->real) Y a b.
     joint_distribution_fn p X Y a b = joint_distribution_fn p Y X b a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[joint_distribution_fn] THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[]);;
