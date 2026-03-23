(* ========================================================================= *)
(* Expectation theory: simple and Lebesgue integration for probability.      *)
(*                                                                           *)
(* Follows Williams "Probability with Martingales" Chapters 5-6 and beyond.  *)
(* Part 1: Simple random variable algebra, simple expectation, simple        *)
(*   variance, Chebyshev and Markov inequalities, weak and strong LLN        *)
(*   (simple version), simple expectation extensionality, MCT for            *)
(*   nn_expectation, nn_expectation additivity.                              *)
(* Part 2: Lebesgue integration foundation (nonneg simple function           *)
(*   approximation, nn_expectation, integrable, general expectation).        *)
(* Part 3: Independence-expectation bridge (E[XY]=E[X]E[Y] for independent  *)
(*   simple RVs, simple covariance).                                         *)
(* Part 4: General expectation theory (variance, covariance, Chebyshev,      *)
(*   Markov, Jensen's inequality, DCT, LLN, convergence in distribution).    *)
(* ========================================================================= *)

needs "Probability/independence.ml";;

(* ========================================================================= *)
(* Part 1: Simple expectation (Williams Chapter 5)                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Random variable measurability: open half-lines and level sets             *)
(* ------------------------------------------------------------------------- *)

(* Helper lemma: backward direction *)
let OPEN_HALFLINE_AS_UNION_BACKWARD = prove
  (`!X:A->real v carrier y.
      (?t. (?n. t = {x | x IN carrier /\ X x <= v - inv(&n + &1)}) /\ y IN t)
      ==> y IN carrier /\ X y < v`,
   REPEAT GEN_TAC THEN
   DISCH_THEN(X_CHOOSE_THEN `t:A->bool` MP_TAC) THEN
   DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `n:num`) MP_TAC) THEN
   ASM_REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `&0 < inv(&n + &1)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC);;

(* Helper lemma: forward direction *)
let OPEN_HALFLINE_AS_UNION_FORWARD = prove
  (`!X:A->real v carrier y.
      y IN carrier /\ X y < v
      ==> ?t. (?n. t = {x | x IN carrier /\ X x <= v - inv(&n + &1)}) /\ y IN t`,
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `&0 < v - (X:A->real) y` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
   DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `?j:num. k = SUC j` (X_CHOOSE_TAC `j:num`) THENL
   [EXISTS_TAC `k - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
   EXISTS_TAC `{x:A | x IN carrier /\ X x <= v - inv(&j + &1)}` THEN
   CONJ_TAC THENL
   [EXISTS_TAC `j:num` THEN REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `inv(&j + &1) < v - (X:A->real) y` MP_TAC THENL
    [ASM_MESON_TAC[REAL_OF_NUM_SUC]; REAL_ARITH_TAC]]);;

(* Full lemma: open halfline as countable union of closed halflines *)
let OPEN_HALFLINE_AS_UNION = prove
  (`!X:A->real v carrier.
      {x | x IN carrier /\ X x < v} =
      UNIONS {({x | x IN carrier /\ X x <= v - inv(&n + &1)}) | n IN (:num)}`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC[EXTENSION; IN_UNIONS; IN_UNIV] THEN
   X_GEN_TAC `y:A` THEN
   REWRITE_TAC[IN_ELIM_THM] THEN
   EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`X:A->real`; `v:real`; `carrier:A->bool`; `y:A`]
      OPEN_HALFLINE_AS_UNION_FORWARD) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`X:A->real`; `v:real`; `carrier:A->bool`; `y:A`]
      OPEN_HALFLINE_AS_UNION_BACKWARD) THEN
    ASM_REWRITE_TAC[]]);;

(* {x | X(x) < v} is an event - key for showing level sets are measurable *)
(* Proof uses OPEN_HALFLINE_AS_UNION and countable union property *)
let RANDOM_VARIABLE_OPEN_HALFLINE = prove
  (`!p:A prob_space X v.
      random_variable p X
      ==> {x | x IN prob_carrier p /\ X x < v} IN prob_events p`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[ISPECL [`X:A->real`; `v:real`; `prob_carrier (p:A prob_space)`]
     OPEN_HALFLINE_AS_UNION] THEN
   MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN
   GEN_TAC THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [random_variable]) THEN
   DISCH_THEN(MP_TAC o SPEC `v - inv(&n + &1)`) THEN
   MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[EXTENSION; IN_ELIM_THM]);;

(* {x | X(x) = v} is an event (level set) *)
let RANDOM_VARIABLE_LEVEL_SET = prove
  (`!p:A prob_space X v.
      random_variable p X
      ==> {x | x IN prob_carrier p /\ X x = v} IN prob_events p`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ X x = v} =
      {x | x IN prob_carrier p /\ X x <= v} DIFF
      {x | x IN prob_carrier p /\ X x < v}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN
    X_GEN_TAC `z:A` THEN
    ASM_CASES_TAC `(z:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC PROB_DIFF_IN_EVENTS THEN CONJ_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [random_variable]) THEN
     SIMP_TAC[];
     MATCH_MP_TAC RANDOM_VARIABLE_OPEN_HALFLINE THEN ASM_REWRITE_TAC[]]]);;

(* {x | X(x) > v} is an event (complement of closed halfline) *)
let RANDOM_VARIABLE_GT = prove
  (`!p:A prob_space X v.
      random_variable p X
      ==> {x | x IN prob_carrier p /\ X x > v} IN prob_events p`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ X x > v} =
      prob_carrier p DIFF {x | x IN prob_carrier p /\ X x <= v}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN
    X_GEN_TAC `z:A` THEN
    ASM_CASES_TAC `(z:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC PROB_COMPL_IN_EVENTS THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [random_variable]) THEN
    SIMP_TAC[]]);;

(* {x | X(x) >= v} is an event (complement of open halfline) *)
let RANDOM_VARIABLE_GE = prove
  (`!p:A prob_space X v.
      random_variable p X
      ==> {x | x IN prob_carrier p /\ X x >= v} IN prob_events p`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ X x >= v} =
      prob_carrier p DIFF {x | x IN prob_carrier p /\ X x < v}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN
    X_GEN_TAC `z:A` THEN
    ASM_CASES_TAC `(z:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC PROB_COMPL_IN_EVENTS THEN
    MATCH_MP_TAC RANDOM_VARIABLE_OPEN_HALFLINE THEN ASM_REWRITE_TAC[]]);;

(* {x | a < X(x) < b} is an event (open interval) *)
let RANDOM_VARIABLE_OPEN_INTERVAL = prove
  (`!p:A prob_space X a b.
      random_variable p X
      ==> {x | x IN prob_carrier p /\ a < X x /\ X x < b} IN prob_events p`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ a < X x /\ X x < b} =
      {x | x IN prob_carrier p /\ X x < b} INTER
      {x | x IN prob_carrier p /\ X x > a}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `z:A` THEN
    ASM_CASES_TAC `(z:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_OPEN_HALFLINE THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC RANDOM_VARIABLE_GT THEN ASM_REWRITE_TAC[]]]);;

(* {t | t < b} is real_open *)
let REAL_OPEN_HALFSPACE_LT = prove
  (`!b. real_open {t | t < b}`,
   GEN_TAC THEN REWRITE_TAC[real_open; IN_ELIM_THM] THEN
   X_GEN_TAC `t:real` THEN DISCH_TAC THEN
   EXISTS_TAC `b - t:real` THEN
   CONJ_TAC THENL [ASM_REAL_ARITH_TAC; GEN_TAC THEN REAL_ARITH_TAC]);;

(* Continuous preimage of real_open set is real_open *)
let REAL_CONTINUOUS_OPEN_PREIMAGE_UNIV = prove
  (`!f U. f real_continuous_on (:real) /\ real_open U
          ==> real_open {t | f t IN U}`,
   REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[real_open; IN_ELIM_THM] THEN
   X_GEN_TAC `x:real` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [real_open]) THEN
   DISCH_THEN(MP_TAC o SPEC `(f:real->real) x`) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `eps:real` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [real_continuous_on]) THEN
   DISCH_THEN(MP_TAC o SPEC `x:real`) THEN
   REWRITE_TAC[IN_UNIV] THEN
   DISCH_THEN(MP_TAC o SPEC `eps:real`) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
   X_GEN_TAC `y:real` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `y:real`) THEN
   ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Preimage of real_open set under a random variable is an event *)
let RANDOM_VARIABLE_PREIMAGE_OPEN = prove
  (`!p:A prob_space X U. random_variable p X /\ real_open U
      ==> {x | x IN prob_carrier p /\ X x IN U} IN prob_events p`,
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ X x IN U} =
      UNIONS {{x | x IN prob_carrier p /\ r < X x /\ X x < s} |
              r,s | rational r /\ rational s /\ (!t. r < t /\ t < s ==> t IN U)}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `z:A` THEN EQ_TAC THENL
    [STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [real_open]) THEN
     DISCH_THEN(MP_TAC o SPEC `(X:A->real) z`) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     DISCH_THEN(X_CHOOSE_THEN `eps:real` STRIP_ASSUME_TAC) THEN
     MP_TAC(SPECL [`(X:A->real) z - eps`; `(X:A->real) z`]
       RATIONAL_BETWEEN) THEN
     ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
     MP_TAC(SPECL [`(X:A->real) z`; `(X:A->real) z + eps`]
       RATIONAL_BETWEEN) THEN
     ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
     EXISTS_TAC `{x:A | x IN prob_carrier p /\ r < X x /\ X x < s}` THEN
     CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`r:real`; `s:real`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
      [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
       ASM_REAL_ARITH_TAC;
       REWRITE_TAC[EXTENSION; IN_ELIM_THM]];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
     DISCH_THEN(X_CHOOSE_THEN `t:A->bool` MP_TAC) THEN
     DISCH_THEN(CONJUNCTS_THEN2
       (X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC))
       MP_TAC) THEN
     ASM_REWRITE_TAC[IN_ELIM_THM] THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   MATCH_MP_TAC PROB_COUNTABLE_UNION_IN_EVENTS THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RANDOM_VARIABLE_OPEN_INTERVAL THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC COUNTABLE_SUBSET THEN
    EXISTS_TAC `{({x:A | x IN prob_carrier p /\ r < X x /\ X x < s}:A->bool) |
                 r IN {q:real | rational q} /\ s IN {q:real | rational q}}` THEN
    CONJ_TAC THENL
    [MP_TAC(ISPECL
       [`\r s. {x:A | x IN prob_carrier p /\ r < X x /\ X x < s}`;
        `{q:real | rational q}`;
        `\r:real. {q:real | rational q}`] COUNTABLE_PRODUCT_DEPENDENT) THEN
     REWRITE_TAC[SET_RULE `{x | rational x} = rational`;
                 COUNTABLE_RATIONAL] THEN
     DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[COUNTABLE_RATIONAL];
     REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
     X_GEN_TAC `w:A->bool` THEN
     DISCH_THEN(X_CHOOSE_THEN `r:real`
       (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC)) THEN
     MAP_EVERY EXISTS_TAC [`r:real`; `s:real`] THEN
     ASM_REWRITE_TAC[IN_ELIM_THM]]]);;

(* ------------------------------------------------------------------------- *)
(* Algebra of random variables                                               *)
(* ------------------------------------------------------------------------- *)

(* Composition with a continuous function preserves random variable property *)
let RANDOM_VARIABLE_COMP_CONTINUOUS = prove
  (`!p:A prob_space X f.
      random_variable p X /\ f real_continuous_on (:real)
      ==> random_variable p (\x. f(X x))`,
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   REWRITE_TAC[random_variable] THEN X_GEN_TAC `a:real` THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ (f:real->real)(X x) <= a} =
      INTERS {{x | x IN prob_carrier p /\ f(X x) < a + inv(&n + &1)} |
              n IN (:num)}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `z:A` THEN
    REWRITE_TAC[INTERS_GSPEC; IN_UNIV; IN_ELIM_THM] THEN EQ_TAC THENL
    [STRIP_TAC THEN X_GEN_TAC `n:num` THEN
     ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `a:real` THEN
     ASM_REWRITE_TAC[REAL_LT_ADDR] THEN
     MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC;
     DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
      REWRITE_TAC[REAL_ADD_LID] THEN
      MATCH_MP_TAC(TAUT `(p /\ q ==> r) ==> p /\ q ==> r`) THEN
      SIMP_TAC[];
      REWRITE_TAC[REAL_ARITH `x <= a <=> ~(a < x)`] THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 < (f:real->real)(X(z:A)) - a` ASSUME_TAC THENL
      [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_ARCH_INV]) THEN
      DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k - 1`) THEN
      UNDISCH_TAC `inv(&k) < (f:real->real)(X(z:A)) - a` THEN
      UNDISCH_TAC `~(k = 0)` THEN
      SPEC_TAC(`k:num`, `k:num`) THEN
      INDUCT_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[SUC_SUB1; REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
   MATCH_MP_TAC PROB_INDEXED_INTER_IN_EVENTS THEN
   X_GEN_TAC `n:num` THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ (f:real->real)(X x) < a + inv(&n + &1)} =
      {x | x IN prob_carrier p /\ X x IN {t:real | f t < a + inv(&n + &1)}}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM]; ALL_TAC] THEN
   MATCH_MP_TAC RANDOM_VARIABLE_PREIMAGE_OPEN THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN
     `{t:real | (f:real->real) t < a + inv(&n + &1)} =
      {t | f t IN {s:real | s < a + inv(&n + &1)}}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
   ASM_REWRITE_TAC[REAL_OPEN_HALFSPACE_LT]);;

(* Maximum of two random variables is a random variable *)
let RANDOM_VARIABLE_MAX = prove
  (`!p:A prob_space X Y.
      random_variable p X /\ random_variable p Y
      ==> random_variable p (\x. max (X x) (Y x))`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[random_variable] THEN
   X_GEN_TAC `a:real` THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ max (X x) (Y x) <= a} =
      {x | x IN prob_carrier p /\ X x <= a} INTER
      {x | x IN prob_carrier p /\ Y x <= a}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `z:A` THEN
    ASM_CASES_TAC `(z:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_max] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN
    RULE_ASSUM_TAC(REWRITE_RULE[random_variable]) THEN
    ASM_SIMP_TAC[]]);;

(* Minimum of two random variables is a random variable *)
let RANDOM_VARIABLE_MIN = prove
  (`!p:A prob_space X Y.
      random_variable p X /\ random_variable p Y
      ==> random_variable p (\x. min (X x) (Y x))`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[random_variable] THEN
   X_GEN_TAC `a:real` THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ min (X x) (Y x) <= a} =
      {x | x IN prob_carrier p /\ X x <= a} UNION
      {x | x IN prob_carrier p /\ Y x <= a}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN
    X_GEN_TAC `z:A` THEN
    ASM_CASES_TAC `(z:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_min] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC PROB_UNION_IN_EVENTS THEN
    RULE_ASSUM_TAC(REWRITE_RULE[random_variable]) THEN
    ASM_SIMP_TAC[]]);;

(* Absolute value of a random variable is a random variable *)
let RANDOM_VARIABLE_ABS = prove
  (`!p:A prob_space X.
      random_variable p X ==> random_variable p (\x. abs(X x))`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[random_variable] THEN
   X_GEN_TAC `a:real` THEN
   ASM_CASES_TAC `a < &0` THENL
   [SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ abs(X x) <= a} = {}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM] THEN
     GEN_TAC THEN ASM_REAL_ARITH_TAC;
     REWRITE_TAC[PROB_EMPTY_IN_EVENTS]];
    SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\ abs(X x) <= a} =
       {x | x IN prob_carrier p /\ X x <= a} INTER
       {x | x IN prob_carrier p /\ X x >= --a}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN
     X_GEN_TAC `z:A` THEN
     ASM_CASES_TAC `(z:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
     ASM_REAL_ARITH_TAC;
     MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [random_variable]) THEN
      SIMP_TAC[];
      MATCH_MP_TAC RANDOM_VARIABLE_GE THEN ASM_REWRITE_TAC[]]]]);;

(* ------------------------------------------------------------------------- *)
(* Simple random variables (taking finitely many values)                     *)
(* ------------------------------------------------------------------------- *)

(* A simple random variable takes finitely many values *)
let simple_rv = new_definition
  `simple_rv (p:A prob_space) X <=>
   random_variable p X /\
   FINITE {X x | x IN prob_carrier p}`;;

(* Constant is a simple random variable *)
let SIMPLE_RV_CONST = prove
  (`!p:A prob_space c. simple_rv p (\x. c)`,
   REPEAT GEN_TAC THEN REWRITE_TAC[simple_rv; RANDOM_VARIABLE_CONST] THEN
   SUBGOAL_THEN `{(\x:A. c) x | x IN prob_carrier p} SUBSET {c:real}`
     (fun th -> MESON_TAC[th; FINITE_SUBSET; FINITE_SING]) THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_SING] THEN MESON_TAC[]);;

(* Indicator function of an event is a simple random variable *)
let SIMPLE_RV_INDICATOR = prove
  (`!p:A prob_space a.
      a IN prob_events p ==> simple_rv p (indicator_fn a)`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[simple_rv] THEN CONJ_TAC THENL
   [REWRITE_TAC[random_variable; indicator_fn] THEN
    X_GEN_TAC `v:real` THEN
    ASM_CASES_TAC `v < &0` THENL
    [SUBGOAL_THEN
       `{x:A | x IN prob_carrier p /\ (if x IN a then &1 else &0) <= v} = {}`
       SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM] THEN
      X_GEN_TAC `z:A` THEN
      ASM_CASES_TAC `(z:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[PROB_EMPTY_IN_EVENTS]];
     ASM_CASES_TAC `v < &1` THENL
     [SUBGOAL_THEN
        `{x:A | x IN prob_carrier p /\ (if x IN a then &1 else &0) <= v} =
         prob_carrier p DIFF a`
        SUBST1_TAC THENL
      [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN
       X_GEN_TAC `z:A` THEN
       ASM_CASES_TAC `(z:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
       COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
       MATCH_MP_TAC PROB_COMPL_IN_EVENTS THEN ASM_REWRITE_TAC[]];
      SUBGOAL_THEN
        `{x:A | x IN prob_carrier p /\ (if x IN a then &1 else &0) <= v} =
         prob_carrier p`
        SUBST1_TAC THENL
      [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
       X_GEN_TAC `z:A` THEN
       ASM_CASES_TAC `(z:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
       COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
       REWRITE_TAC[PROB_CARRIER_IN_EVENTS]]]];
    SUBGOAL_THEN `{indicator_fn a x | x:A IN prob_carrier p} SUBSET {&0, &1}`
      (fun th -> MESON_TAC[th; FINITE_SUBSET; FINITE_INSERT; FINITE_EMPTY]) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY; indicator_fn] THEN
    MESON_TAC[]]);;

(* Shifting a random variable by a constant preserves measurability *)
let RANDOM_VARIABLE_SHIFT = prove
  (`!p:A prob_space X c.
      random_variable p X ==> random_variable p (\x. X x + c)`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[random_variable] THEN
   X_GEN_TAC `a:real` THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ X x + c <= a} =
      {x | x IN prob_carrier p /\ X x <= a - c}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `z:A` THEN
    ASM_CASES_TAC `(z:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [random_variable]) THEN
    DISCH_THEN(MP_TAC o SPEC `a - c:real`) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM]]);;

(* Subtracting a constant from a random variable *)
let RANDOM_VARIABLE_SUB_CONST = prove
  (`!p:A prob_space X c.
      random_variable p X ==> random_variable p (\x. X x - c)`,
   REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `--c:real`]
     RANDOM_VARIABLE_SHIFT) THEN
   ASM_REWRITE_TAC[real_sub; REAL_NEG_NEG]);;

(* Positive part of a random variable is a random variable *)
let RANDOM_VARIABLE_POS_PART = prove
  (`!p:A prob_space X.
      random_variable p X ==> random_variable p (\x. max (X x) (&0))`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN
   ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST]);;

(* Negative part of a random variable is a random variable *)
let RANDOM_VARIABLE_NEG_PART = prove
  (`!p:A prob_space X.
      random_variable p X ==> random_variable p (\x. max (--(X x)) (&0))`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN
   ASM_SIMP_TAC[RANDOM_VARIABLE_NEG; RANDOM_VARIABLE_CONST]);;

(* Helper: x^2 <= a iff |x| <= sqrt(a) when a >= 0 *)
let POW_2_LE_SQRT = prove
  (`!x a. &0 <= a ==> (x pow 2 <= a <=> abs x <= sqrt a)`,
   REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`(x:real) pow 2`; `a:real`] SQRT_MONO_LE) THEN
    ASM_REWRITE_TAC[POW_2_SQRT_ABS];
    DISCH_TAC THEN
    SUBGOAL_THEN `sqrt(x pow 2) <= sqrt a` MP_TAC THENL
    [ASM_REWRITE_TAC[POW_2_SQRT_ABS]; ALL_TAC] THEN
    SIMP_TAC[SQRT_MONO_LE_EQ; REAL_LE_POW_2]]);;

(* Square of a random variable is a random variable *)
let RANDOM_VARIABLE_SQUARE = prove
  (`!p:A prob_space X.
      random_variable p X ==> random_variable p (\x. (X x) pow 2)`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[random_variable] THEN
   X_GEN_TAC `a:real` THEN
   ASM_CASES_TAC `a < &0` THENL
   [SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ X x pow 2 <= a} = {}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM] THEN
     GEN_TAC THEN STRIP_TAC THEN
     MP_TAC(SPEC `(X:A->real) x` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
     REWRITE_TAC[PROB_EMPTY_IN_EVENTS]];
    SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\ X x pow 2 <= a} =
       {x | x IN prob_carrier p /\ X x <= sqrt a} INTER
       {x | x IN prob_carrier p /\ X x >= --(sqrt a)}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN
     X_GEN_TAC `z:A` THEN
     ASM_CASES_TAC `(z:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
     MP_TAC(ISPECL [`(X:A->real) z`; `a:real`] POW_2_LE_SQRT) THEN
     ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     REWRITE_TAC[REAL_ABS_BOUNDS] THEN REAL_ARITH_TAC;
     MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [random_variable]) THEN
      SIMP_TAC[];
      MATCH_MP_TAC RANDOM_VARIABLE_GE THEN ASM_REWRITE_TAC[]]]]);;

(* Test: prove --a / --c = a / c *)
(* --a / --c = (--a) * inv(--c) = (--a) * (--(inv c)) = --((--a) * inv c)
   = --(--((a * inv c))) = a * inv c = a / c *)
let NEG_DIV_NEG = prove
  (`!(a:real) c. --a / --c = a / c`,
   SIMP_TAC[real_div; REAL_INV_NEG; REAL_MUL_RNEG;
            REAL_MUL_LNEG; REAL_NEG_NEG]);;

(* Helper lemma: multiplication by negative flips inequality *)
(* c * x <= a <=> x >= a / c  when c < 0 *)
let MUL_LNEG_LE = prove
  (`!c x a. c < &0 ==> (c * x <= a <=> x >= a / c)`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[real_ge] THEN
   SUBGOAL_THEN `&0 < --c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   (* Transform using negation: c * x <= a <=> --a <= (--c) * x *)
   GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM REAL_LE_NEG2] THEN
   REWRITE_TAC[GSYM REAL_MUL_LNEG; REAL_NEG_NEG] THEN
   REWRITE_TAC[REAL_MUL_SYM] THEN
   ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; NEG_DIV_NEG]);;

(* Product of a random variable by a constant (handling all cases) *)
let RANDOM_VARIABLE_CMUL = prove
  (`!p:A prob_space X c.
      random_variable p X ==> random_variable p (\x. c * X x)`,
   REPEAT STRIP_TAC THEN
   ASM_CASES_TAC `c = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO; RANDOM_VARIABLE_CONST];
    ASM_CASES_TAC `&0 < c` THENL
    [ASM_SIMP_TAC[RANDOM_VARIABLE_SCALE];
     SUBGOAL_THEN `c < &0` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     REWRITE_TAC[random_variable] THEN X_GEN_TAC `a:real` THEN
     SUBGOAL_THEN
       `{x:A | x IN prob_carrier p /\ c * X x <= a} =
        {x | x IN prob_carrier p /\ X x >= a / c}`
       SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `z:A` THEN
      ASM_CASES_TAC `(z:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[MUL_LNEG_LE];
      MATCH_MP_TAC RANDOM_VARIABLE_GE THEN ASM_REWRITE_TAC[]]]]);;


(* Helper: inv(&n + &1) version of archimedean principle *)
let REAL_ARCH_INV_SUC = prove
  (`!x. &0 < x ==> ?n. inv(&n + &1) < x`,
   GEN_TAC THEN
   GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
   DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `n:num` THEN
   MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `inv(&n)` THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LT_INV2 THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_LT_INV_EQ];
    REAL_ARITH_TAC]);;

(* Helper: the open halfline for sum can be expressed via rationals *)
(* {x | X x + Y x < a} = UNIONS { {x | X x < r} INTER {x | Y x < a - r} | rational r } *)
let SUM_OPEN_HALFLINE_AS_RATIONAL_UNION = prove
  (`!(X:A->real) Y a carrier.
      {x | x IN carrier /\ X x + Y x < a} =
      UNIONS {{x | x IN carrier /\ X x < r} INTER {x | x IN carrier /\ Y x < a - r} |
              rational r}`,
   REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_UNIONS; IN_INTER; IN_ELIM_THM] THEN
   X_GEN_TAC `z:A` THEN EQ_TAC THENL
   [(* Forward: if X z + Y z < a, find rational r with X z < r < a - Y z *)
    STRIP_TAC THEN
    MP_TAC(ISPECL [`(X:A->real) z`; `a - (Y:A->real) z`] RATIONAL_BETWEEN) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `{x:A | x IN carrier /\ X x < r} INTER {x | x IN carrier /\ Y x < a - r}` THEN
    CONJ_TAC THENL
    [EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[IN_INTER; IN_ELIM_THM];
     REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
     REPEAT CONJ_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    (* Backward: if there exists r with X z < r and Y z < a - r, then X z + Y z < a *)
    DISCH_THEN(X_CHOOSE_THEN `s:A->bool` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(z:A) IN s` THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    STRIP_TAC THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]]);;

(* COUNTABLE_RATIONAL is already available in the session *)

(* The set of rational-indexed sets is countable *)
let COUNTABLE_RATIONAL_SETS = prove
  (`!f:(real->A->bool). COUNTABLE {f r | rational r}`,
   GEN_TAC THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
   MATCH_MP_TAC COUNTABLE_IMAGE THEN
   REWRITE_TAC[SET_RULE `{x | rational x} = rational`; COUNTABLE_RATIONAL]);;

(* Sum of two random variables is a random variable *)
let RANDOM_VARIABLE_ADD = prove
  (`!p:A prob_space X Y.
      random_variable p X /\ random_variable p Y
      ==> random_variable p (\x. X x + Y x)`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[random_variable] THEN X_GEN_TAC `a:real` THEN
   (* Express {X + Y <= a} as intersection of open halflines *)
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ X x + Y x <= a} =
      INTERS {{x | x IN prob_carrier p /\ X x + Y x < a + inv(&n + &1)} | n IN (:num)}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `z:A` THEN
    REWRITE_TAC[IN_INTERS; IN_ELIM_THM] THEN EQ_TAC THENL
    [STRIP_TAC THEN X_GEN_TAC `s:A->bool` THEN
     DISCH_THEN(X_CHOOSE_THEN `n:num`
       (CONJUNCTS_THEN2 (K ALL_TAC) SUBST1_TAC)) THEN
     REWRITE_TAC[IN_ELIM_THM] THEN
     CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `a:real` THEN
     ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[REAL_LT_ADDR] THEN MATCH_MP_TAC REAL_LT_INV THEN
     REAL_ARITH_TAC;
     DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC
        `{x:A | x IN prob_carrier p /\ X x + Y x < a + inv(&1)}`) THEN
      ANTS_TAC THENL
      [EXISTS_TAC `0` THEN REWRITE_TAC[IN_UNIV]; ALL_TAC] THEN
      REWRITE_TAC[IN_ELIM_THM; REAL_ADD_LID] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_ARITH `x <= a <=> ~(a < x)`] THEN DISCH_TAC THEN
      MP_TAC(SPEC `(X:A->real) z + Y z - a` REAL_ARCH_INV_SUC) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `n:num` ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC
        `{x:A | x IN prob_carrier p /\ X x + Y x < a + inv(&n + &1)}`) THEN
      ANTS_TAC THENL
      [EXISTS_TAC `n:num` THEN REWRITE_TAC[IN_UNIV]; ALL_TAC] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
   (* The intersection is in prob_events *)
   MATCH_MP_TAC PROB_INDEXED_INTER_IN_EVENTS THEN
   X_GEN_TAC `n:num` THEN
   (* Each open halfline for X+Y is a countable union *)
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ X x + Y x < a + inv(&n + &1)} =
      UNIONS {{x | x IN prob_carrier p /\ X x < r} INTER
              {x | x IN prob_carrier p /\ Y x < (a + inv(&n + &1)) - r} | rational r}`
     SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_OPEN_HALFLINE_AS_RATIONAL_UNION]; ALL_TAC] THEN
   MATCH_MP_TAC PROB_COUNTABLE_UNION_IN_EVENTS THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `s:A->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN
    ASM_SIMP_TAC[RANDOM_VARIABLE_OPEN_HALFLINE];
    REWRITE_TAC[COUNTABLE_RATIONAL_SETS]]);;

(* Difference of two random variables is a random variable *)
let RANDOM_VARIABLE_SUB = prove
  (`!p:A prob_space X Y.
      random_variable p X /\ random_variable p Y
      ==> random_variable p (\x. X x - Y x)`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[real_sub] THEN
   MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN
   ASM_SIMP_TAC[RANDOM_VARIABLE_NEG]);;

(* {f <= g} is an event when f, g are random variables *)
let RV_LEVEL_LE_RV = prove
 (`!p:A prob_space f g.
     random_variable p f /\ random_variable p g
     ==> {x | x IN prob_carrier p /\ f x <= g x} IN prob_events p`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `random_variable p (\x:A. f x - g x)` ASSUME_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ f x <= g x} =
     {x | x IN prob_carrier p /\ f x - g x <= &0}` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
   EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
   FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[random_variable]) THEN
   DISCH_THEN(MP_TAC o SPEC `&0`) THEN REWRITE_TAC[BETA_THM]]);;

(* ========================================================================= *)
(* CHAPTER 5: Expectation - Simple Random Variables                          *)
(* ========================================================================= *)

(* The carrier of a probability space is nonempty *)
(* Proof: P(carrier) = 1 > 0 implies carrier is nonempty *)
let PROB_CARRIER_NONEMPTY = prove
  (`!p:A prob_space. ~(prob_carrier p = {})`,
   GEN_TAC THEN DISCH_TAC THEN
   MP_TAC(SPEC `p:A prob_space` PROB_SPACE) THEN
   ASM_REWRITE_TAC[PROB_EMPTY; prob_carrier] THEN
   REAL_ARITH_TAC);;

(* Expectation of a simple random variable *)
(* E[X] = SUM_{v in range(X)} v * P({X = v}) *)
let simple_expectation = new_definition
  `simple_expectation (p:A prob_space) (X:A->real) =
   sum {v | v IN IMAGE X (prob_carrier p)}
       (\v. v * prob p {x | x IN prob_carrier p /\ X x = v})`;;

(* Basic property: expectation of constant is that constant *)
let SET_IN_SIMP = SET_RULE `{x:A | x IN s} = s`;;

let SIMPLE_EXPECTATION_CONST = prove
  (`!p:A prob_space (c:real). simple_expectation p (\x. c) = c`,
   REPEAT GEN_TAC THEN REWRITE_TAC[simple_expectation] THEN
   MP_TAC(SPEC `p:A prob_space` PROB_CARRIER_NONEMPTY) THEN
   SIMP_TAC[IMAGE_CONST] THEN DISCH_TAC THEN
   REWRITE_TAC[IN_SING; SET_RULE `{v | v = c} = {c:real}`] THEN
   REWRITE_TAC[SUM_SING] THEN
   REWRITE_TAC[SET_IN_SIMP] THEN
   REWRITE_TAC[PROB_SPACE; REAL_MUL_RID]);;

(* Eta-expansion lemma: indicator_fn a = (\x. if x IN a then &1 else &0) *)
(* Needed because REWRITE_TAC[indicator_fn] only rewrites indicator_fn a x,
   not the partial application indicator_fn a in IMAGE (indicator_fn a) etc. *)
let INDICATOR_FN_ETA = prove
  (`!a:A->bool. indicator_fn a = (\x. if x IN a then &1 else &0)`,
   GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; indicator_fn]);;

(* E[indicator_fn A] = prob p A *)
let SIMPLE_EXPECTATION_INDICATOR = prove
  (`!p:A prob_space a.
      a IN prob_events p
      ==> simple_expectation p (indicator_fn a) = prob p a`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[simple_expectation; INDICATOR_FN_ETA] THEN
   (* The image of indicator_fn a over the carrier is a subset of {0, 1} *)
   SUBGOAL_THEN
     `IMAGE (\x:A. if x IN a then &1 else &0) (prob_carrier p) SUBSET {&0, &1}`
     ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_IMAGE; IN_INSERT; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
   (* Split into cases: is a INTER carrier empty or not? *)
   SUBGOAL_THEN `FINITE (IMAGE (\x:A. if x IN a then &1 else &0) (prob_carrier p))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{&0, &1}` THEN
    ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    ALL_TAC] THEN
   (* Simplify {v | v IN IMAGE ...} = IMAGE ... *)
   REWRITE_TAC[SET_IN_SIMP] THEN
   (* Case: a INTER prob_carrier p could be empty or not *)
   ASM_CASES_TAC `(a:A->bool) INTER prob_carrier p = {}` THENL
   [(* Case 1: no elements of carrier are in a, so image = {0} *)
    SUBGOAL_THEN
      `IMAGE (\x:A. if x IN a then &1 else &0) (prob_carrier p) = {&0}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SING] THEN X_GEN_TAC `y:real` THEN
     EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THENL
      [UNDISCH_TAC `(a:A->bool) INTER prob_carrier p = {}` THEN
       REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
       DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[];
       REWRITE_TAC[]];
      DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `p:A prob_space` PROB_CARRIER_NONEMPTY) THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `z:A`) THEN EXISTS_TAC `z:A` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(a:A->bool) INTER prob_carrier p = {}` THEN
      REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `z:A`) THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[]];
     ALL_TAC] THEN
    REWRITE_TAC[SUM_SING; REAL_MUL_LZERO] THEN
    (* prob p a = 0 since a INTER carrier = {} *)
    SUBGOAL_THEN `a INTER prob_carrier p = (a:A->bool)` ASSUME_TAC THENL
    [MATCH_MP_TAC(SET_RULE `(a:A->bool) SUBSET s ==> a INTER s = a`) THEN
     MATCH_MP_TAC PROB_EVENT_SUBSET THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    UNDISCH_TAC `(a:A->bool) INTER prob_carrier p = {}` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[PROB_EMPTY];
    ALL_TAC] THEN
   (* Case 2: some elements of carrier are in a *)
   (* Also check if all elements are in a *)
   ASM_CASES_TAC `prob_carrier p SUBSET (a:A->bool)` THENL
   [(* Subcase: all carrier elements in a, image = {1} *)
    SUBGOAL_THEN
      `IMAGE (\x:A. if x IN a then &1 else &0) (prob_carrier p) = {&1}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SING] THEN X_GEN_TAC `y:real` THEN
     EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(x:A) IN a` ASSUME_TAC THENL
      [ASM SET_TAC[]; ASM_REWRITE_TAC[]];
      DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `p:A prob_space` PROB_CARRIER_NONEMPTY) THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `z:A`) THEN EXISTS_TAC `z:A` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(z:A) IN a` ASSUME_TAC THENL
      [ASM SET_TAC[]; ASM_REWRITE_TAC[]]];
     ALL_TAC] THEN
    REWRITE_TAC[SUM_SING; REAL_MUL_LID] THEN
    SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ (if x IN a then &1 else &0) = &1} =
                  prob_carrier p` SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN EQ_TAC THENL
     [SIMP_TAC[]; DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(x:A) IN a` ASSUME_TAC THENL
      [ASM SET_TAC[]; ASM_REWRITE_TAC[]]];
     ALL_TAC] THEN
    REWRITE_TAC[PROB_SPACE] THEN
    (* prob p a = 1 since carrier SUBSET a and a SUBSET carrier *)
    SUBGOAL_THEN `(a:A->bool) = prob_carrier p` SUBST1_TAC THENL
    [MATCH_MP_TAC(SET_RULE `(a:A->bool) SUBSET s /\ s SUBSET a ==> a = s`) THEN
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PROB_EVENT_SUBSET THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[PROB_SPACE]];
    ALL_TAC] THEN
   (* Subcase: image = {0, 1} *)
   SUBGOAL_THEN
     `IMAGE (\x:A. if x IN a then &1 else &0) (prob_carrier p) = {&0, &1}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INSERT; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real` THEN EQ_TAC THENL
    [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[];
     STRIP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(prob_carrier p SUBSET (a:A->bool))` THEN
      REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~((a:A->bool) INTER prob_carrier p = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
   (* sum {0, 1} f = f(0) + f(1) *)
   SIMP_TAC[SUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
   CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_EQ_CONV) THEN
   REWRITE_TAC[SUM_CLAUSES; NOT_IN_EMPTY; REAL_ADD_RID] THEN
   (* Simplify: 0 * P({X=0}) + 1 * P({X=1}) = P({X=1}) *)
   REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID; REAL_MUL_LID] THEN
   (* {x IN carrier | indicator = 1} = a INTER carrier = a *)
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ (if x IN a then &1 else &0) = &1} =
      a INTER prob_carrier p` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN X_GEN_TAC `x:A` THEN
    EQ_TAC THENL
    [STRIP_TAC THEN
     UNDISCH_TAC `(if (x:A) IN a then &1 else &0) = &1` THEN
     COND_CASES_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
     STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   SUBGOAL_THEN `(a:A->bool) INTER prob_carrier p = a` SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE `(a:A->bool) SUBSET s ==> a INTER s = a`) THEN
    MATCH_MP_TAC PROB_EVENT_SUBSET THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[]]);;

(* Non-negativity: if X >= 0 everywhere on carrier, then E[X] >= 0 *)
let SIMPLE_EXPECTATION_POS = prove
  (`!p:A prob_space X.
      simple_rv p X /\ (!x. x IN prob_carrier p ==> &0 <= X x)
      ==> &0 <= simple_expectation p X`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[simple_expectation] THEN
   REWRITE_TAC[SET_IN_SIMP] THEN
   MATCH_MP_TAC SUM_POS_LE THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simple_rv]) THEN
   STRIP_TAC THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
   X_GEN_TAC `v:real` THEN REWRITE_TAC[IN_IMAGE] THEN
   DISCH_THEN(X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `w:A`) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PROB_POSITIVE THEN
    MATCH_MP_TAC RANDOM_VARIABLE_LEVEL_SET THEN ASM_REWRITE_TAC[]]);;

(* Monotonicity: if X <= Y everywhere, then E[X] <= E[Y] *)
(* This is harder for simple expectation - defer for now *)

(* Scaling: E[c * X] = c * E[X] for simple random variables *)
let SIMPLE_EXPECTATION_CMUL = prove
  (`!p:A prob_space X c.
      simple_rv p X
      ==> simple_expectation p (\x. c * X x) = c * simple_expectation p X`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[simple_expectation] THEN
   REWRITE_TAC[SET_IN_SIMP] THEN
   (* Use SUM_LMUL on the right side *)
   REWRITE_TAC[GSYM SUM_LMUL] THEN
   ASM_CASES_TAC `c = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO; IMAGE_CONST] THEN
    MP_TAC(SPEC `p:A prob_space` PROB_CARRIER_NONEMPTY) THEN
    SIMP_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[IN_SING; SET_RULE `{v | v = c} = {c:real}`] THEN
    REWRITE_TAC[SUM_SING; REAL_MUL_LZERO; SUM_0];
    ALL_TAC] THEN
   (* When c != 0, IMAGE (\x. c * X x) carrier = IMAGE (\v. c * v) (IMAGE X carrier) *)
   SUBGOAL_THEN
     `IMAGE (\x:A. c * X x) (prob_carrier p) =
      IMAGE (\v. c * v) (IMAGE (X:A->real) (prob_carrier p))`
     SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF]; ALL_TAC] THEN
   (* Use SUM_IMAGE to reindex the sum *)
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simple_rv]) THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `FINITE (IMAGE (X:A->real) (prob_carrier p))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM SIMPLE_IMAGE]; ALL_TAC] THEN
   SUBGOAL_THEN
     `!g:real->real.
        sum (IMAGE (\v. c * v) (IMAGE (X:A->real) (prob_carrier p))) g =
        sum (IMAGE X (prob_carrier p)) (g o (\v. c * v))`
     (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC SUM_IMAGE THEN
    REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_EQ_MUL_LCANCEL];
    ALL_TAC] THEN
   REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC SUM_EQ THEN
   X_GEN_TAC `v:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
   SUBGOAL_THEN `!w:A. c * (X:A->real) w = c * v <=> X w = v`
     (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[REAL_EQ_MUL_LCANCEL]; REWRITE_TAC[REAL_MUL_ASSOC]]);;

(* Sum of two simple random variables is a simple random variable *)
let SIMPLE_RV_ADD = prove
  (`!p:A prob_space X Y.
      simple_rv p X /\ simple_rv p Y
      ==> simple_rv p (\x. X x + Y x)`,
   REPEAT GEN_TAC THEN REWRITE_TAC[simple_rv] THEN STRIP_TAC THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   MP_TAC(ISPECL [`(+):real->real->real`;
                   `IMAGE (X:A->real) (prob_carrier p)`;
                   `\u:real. IMAGE (Y:A->real) (prob_carrier p)`]
     FINITE_PRODUCT_DEPENDENT) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [ASM_REWRITE_TAC[GSYM SIMPLE_IMAGE; FINITE_IMAGE];
     GEN_TAC THEN DISCH_TAC THEN
     ASM_REWRITE_TAC[GSYM SIMPLE_IMAGE; FINITE_IMAGE]];
    ALL_TAC] THEN
   REWRITE_TAC[] THEN
   DISCH_TAC THEN
   MATCH_MP_TAC FINITE_SUBSET THEN
   FIRST_X_ASSUM(fun th -> EXISTS_TAC(rand(concl th)) THEN
     CONJ_TAC THENL [ACCEPT_TAC th; ALL_TAC]) THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
   X_GEN_TAC `w:real` THEN
   DISCH_THEN(X_CHOOSE_THEN `x:A` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
   MAP_EVERY EXISTS_TAC [`(X:A->real) x`; `(Y:A->real) x`] THEN
   REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]);;


(* ========================================================================= *)
(* Null events and almost sure properties (Williams 1.5, 2.4)                *)
(* ========================================================================= *)

let null_event = new_definition
  `null_event (p:A prob_space) a <=>
   a IN prob_events p /\ prob p a = &0`;;

let almost_surely = new_definition
  `almost_surely (p:A prob_space) (P:A->bool) <=>
   ?n. null_event p n /\ {x | x IN prob_carrier p /\ ~(x IN P)} SUBSET n`;;

(* The empty set is a null event *)
let NULL_EVENT_EMPTY = prove
  (`!p:A prob_space. null_event p {}`,
   GEN_TAC THEN REWRITE_TAC[null_event; PROB_EMPTY] THEN
   MESON_TAC[SIGMA_ALGEBRA_EMPTY; PROB_SPACE_SIGMA_ALGEBRA]);;

(* A sub-event of a null event is null *)
let NULL_EVENT_SUBSET = prove
  (`!p:A prob_space a b.
      null_event p b /\ a IN prob_events p /\ a SUBSET b
      ==> null_event p a`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[null_event] THEN
   ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [null_event]) THEN
   STRIP_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `a:A->bool`; `b:A->bool`] PROB_MONO) THEN
   ASM_REWRITE_TAC[] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `a:A->bool`] PROB_POSITIVE) THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Union of two null events is null *)
let NULL_EVENT_UNION = prove
  (`!p:A prob_space a b.
      null_event p a /\ null_event p b
      ==> null_event p (a UNION b)`,
   REPEAT GEN_TAC THEN REWRITE_TAC[null_event] THEN STRIP_TAC THEN
   CONJ_TAC THENL
   [ASM_SIMP_TAC[PROB_UNION_IN_EVENTS]; ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `a:A->bool`; `b:A->bool`]
     PROB_SUBADDITIVE) THEN
   ASM_REWRITE_TAC[] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `a UNION b:A->bool`] PROB_POSITIVE) THEN
   ASM_SIMP_TAC[PROB_UNION_IN_EVENTS] THEN REAL_ARITH_TAC);;

(* Countable union of null events is null *)
let NULL_EVENT_COUNTABLE_UNION = prove
  (`!p:A prob_space (B:num->A->bool).
      (!n. null_event p (B n))
      ==> null_event p (UNIONS {B n | n IN (:num)})`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[null_event] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN
    ASM_MESON_TAC[null_event]; ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `B:num->A->bool`]
     PROB_COUNTABLE_SUBADDITIVE_INDEXED) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[null_event]; ALL_TAC] THEN
    SUBGOAL_THEN `(\i. prob (p:A prob_space) ((B:num->A->bool) i)) = (\i. &0)`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[null_event]; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUMMABLE_0];
    ALL_TAC] THEN
   SUBGOAL_THEN `real_infsum (from 0) (\i. prob (p:A prob_space) ((B:num->A->bool) i)) = &0`
     SUBST1_TAC THENL
   [SUBGOAL_THEN `(\i. prob (p:A prob_space) ((B:num->A->bool) i)) = (\i. &0)`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[null_event]; ALL_TAC] THEN
    REWRITE_TAC[REAL_INFSUM_0]; ALL_TAC] THEN
   DISCH_TAC THEN
   REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC PROB_POSITIVE THEN
    MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN
    ASM_MESON_TAC[null_event]]);;

(* Complement of a prob-1 event is null *)
let NULL_EVENT_COMPL_ONE = prove
  (`!p:A prob_space a.
      a IN prob_events p /\ prob p a = &1
      ==> null_event p (prob_carrier p DIFF a)`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[null_event] THEN
   ASM_SIMP_TAC[PROB_COMPL_IN_EVENTS; PROB_COMPL] THEN
   REAL_ARITH_TAC);;

(* Intersection of null events is null *)
let NULL_EVENT_INTER = prove
  (`!p:A prob_space a b.
      null_event p a /\ null_event p b ==> null_event p (a INTER b)`,
   REPEAT STRIP_TAC THEN MATCH_MP_TAC NULL_EVENT_SUBSET THEN
   EXISTS_TAC `a:A->bool` THEN ASM_REWRITE_TAC[INTER_SUBSET] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[null_event]) THEN
   ASM_SIMP_TAC[PROB_INTER_IN_EVENTS]);;

(* Difference with null event minuend is null *)
let NULL_EVENT_DIFF = prove
  (`!p:A prob_space a b.
      null_event p a /\ b IN prob_events p ==> null_event p (a DIFF b)`,
   REPEAT STRIP_TAC THEN MATCH_MP_TAC NULL_EVENT_SUBSET THEN
   EXISTS_TAC `a:A->bool` THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[null_event]) THEN
    ASM_SIMP_TAC[PROB_DIFF_IN_EVENTS];
    SET_TAC[]]);;

(* Complement of a null event has probability 1 *)
let NULL_EVENT_COMPL = prove
  (`!p:A prob_space a.
      null_event p a ==> prob p (prob_carrier p DIFF a) = &1`,
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[null_event]) THEN
   ASM_SIMP_TAC[PROB_COMPL] THEN REAL_ARITH_TAC);;

(* null_event is equivalent to prob = 0 for events *)
let NULL_EVENT_IFF_PROB_ZERO = prove
  (`!p:A prob_space a.
      a IN prob_events p ==> (null_event p a <=> prob p a = &0)`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[null_event] THEN
   ASM_REWRITE_TAC[]);;

(* Intersection of two a.s. properties holds a.s. *)
let ALMOST_SURELY_INTER = prove
  (`!p:A prob_space P Q.
      almost_surely p P /\ almost_surely p Q
      ==> almost_surely p (P INTER Q)`,
   REPEAT GEN_TAC THEN REWRITE_TAC[almost_surely] THEN
   DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `n1:A->bool` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `n2:A->bool` STRIP_ASSUME_TAC)) THEN
   EXISTS_TAC `n1 UNION n2:A->bool` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC NULL_EVENT_UNION THEN ASM_REWRITE_TAC[];
    ASM SET_TAC[IN_INTER]]);;

(* An event that holds a.s. has probability 1 *)
let ALMOST_SURELY_EVENT = prove
  (`!p:A prob_space E.
      E IN prob_events p /\ almost_surely p E
      ==> prob p E = &1`,
   REPEAT GEN_TAC THEN REWRITE_TAC[almost_surely] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `n:A->bool` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `prob_carrier p DIFF E SUBSET n:A->bool` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DIFF] THEN
    MESON_TAC[PROB_EVENT_SUBSET];
    ALL_TAC] THEN
   SUBGOAL_THEN `prob p (prob_carrier p DIFF E:A->bool) = &0` ASSUME_TAC THENL
   [SUBGOAL_THEN `null_event p (prob_carrier p DIFF E:A->bool)` MP_TAC THENL
    [MATCH_MP_TAC NULL_EVENT_SUBSET THEN
     EXISTS_TAC `n:A->bool` THEN ASM_SIMP_TAC[PROB_COMPL_IN_EVENTS];
     SIMP_TAC[null_event]];
    ALL_TAC] THEN
   SUBGOAL_THEN `prob p (E:A->bool) = &1 - prob p (prob_carrier p DIFF E)`
     SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `b = &1 - a ==> a = &1 - b`) THEN
    MATCH_MP_TAC PROB_COMPL THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* An event with probability 1 holds a.s. *)
let ALMOST_SURELY_FROM_PROB_ONE = prove
  (`!p:A prob_space E.
      E IN prob_events p /\ prob p E = &1
      ==> almost_surely p E`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[almost_surely] THEN
   EXISTS_TAC `prob_carrier p DIFF E:A->bool` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC NULL_EVENT_COMPL_ONE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DIFF] THEN MESON_TAC[]]);;

(* Countable intersection of a.s. properties holds a.s. *)
let ALMOST_SURELY_COUNTABLE_INTER = prove
  (`!p:A prob_space (P:num->A->bool).
      (!n. almost_surely p (P n))
      ==> almost_surely p (INTERS {P n | n IN (:num)})`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[almost_surely] THEN
   FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[almost_surely]) THEN
   REWRITE_TAC[SKOLEM_THM] THEN
   DISCH_THEN(X_CHOOSE_THEN `N:num->A->bool` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `UNIONS {(N:num->A->bool) n | n IN (:num)}` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC NULL_EVENT_COUNTABLE_UNION THEN ASM_MESON_TAC[];
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERS; IN_UNIONS; IN_UNIV;
                NOT_FORALL_THM; NOT_IMP] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    EXISTS_TAC `(N:num->A->bool) n` THEN CONJ_TAC THENL
    [EXISTS_TAC `n:num` THEN REWRITE_TAC[];
     FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
     REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
     DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) MP_TAC) THEN
     DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
     ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]]);;

(* Union of two a.s. properties holds a.s. *)
let ALMOST_SURELY_UNION = prove
  (`!p:A prob_space P Q.
      almost_surely p P /\ almost_surely p Q
      ==> almost_surely p (P UNION Q)`,
   REPEAT GEN_TAC THEN REWRITE_TAC[almost_surely] THEN
   DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `n1:A->bool` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `n2:A->bool` STRIP_ASSUME_TAC)) THEN
   EXISTS_TAC `n1 INTER n2:A->bool` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC NULL_EVENT_INTER THEN ASM_REWRITE_TAC[];
    ASM SET_TAC[]]);;

(* The carrier holds almost surely *)
let ALMOST_SURELY_CARRIER = prove
  (`!p:A prob_space. almost_surely p (prob_carrier p)`,
   GEN_TAC THEN REWRITE_TAC[almost_surely] THEN
   EXISTS_TAC `{}:A->bool` THEN
   REWRITE_TAC[NULL_EVENT_EMPTY] THEN SET_TAC[]);;

(* Properties that agree on the carrier are a.s. equivalent *)
let ALMOST_SURELY_EQ = prove
  (`!p:A prob_space P Q.
      almost_surely p P /\
      (!x. x IN prob_carrier p ==> (x IN P <=> x IN Q))
      ==> almost_surely p Q`,
   REPEAT GEN_TAC THEN REWRITE_TAC[almost_surely] THEN
   DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `n:A->bool` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
   EXISTS_TAC `n:A->bool` THEN ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

(* ========================================================================= *)
(* Countable intersection of probability-1 events (Williams 2.4(a))          *)
(* ========================================================================= *)

(* ========================================================================= *)
(* Liminf of events (Williams 2.8)                                           *)
(* ========================================================================= *)

let liminf_events = new_definition
  `liminf_events (A:num->A->bool) =
   UNIONS {INTERS {A n | n >= m} | m IN (:num)}`;;

let LIMINF_EVENTS_ALT = prove
  (`!A:num->A->bool. liminf_events A =
     {x | ?m. !n. n >= m ==> x IN A n}`,
   GEN_TAC THEN REWRITE_TAC[liminf_events; EXTENSION; IN_UNIONS] THEN
   REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
   X_GEN_TAC `x:A` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    POP_ASSUM(MP_TAC o REWRITE_RULE[IN_INTERS]) THEN
    DISCH_TAC THEN
    EXISTS_TAC `m:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(A:num->A->bool) n`) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `m:num` ASSUME_TAC) THEN
    EXISTS_TAC `INTERS {(A:num->A->bool) n | n >= m}` THEN
    CONJ_TAC THENL [EXISTS_TAC `m:num` THEN REFL_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_INTERS; IN_ELIM_THM] THEN
    X_GEN_TAC `s:A->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Liminf is a sub-event of limsup *)
let LIMINF_SUBSET_LIMSUP = prove
  (`!A:num->A->bool. liminf_events A SUBSET limsup_events A`,
   GEN_TAC THEN REWRITE_TAC[LIMINF_EVENTS_ALT; LIMSUP_EVENTS_ALT] THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
   GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `m:num` ASSUME_TAC) THEN
   X_GEN_TAC `k:num` THEN
   EXISTS_TAC `m + k:num` THEN CONJ_TAC THENL
   [ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]);;

(* Liminf is an event when each A_n is *)
let LIMINF_EVENTS_IN_EVENTS = prove
  (`!p:A prob_space A.
      (!n. A n IN prob_events p)
      ==> liminf_events A IN prob_events p`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[liminf_events] THEN
   SUBGOAL_THEN
     `!m. INTERS {(A:num->A->bool) n | n >= m} IN prob_events p`
     ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC PROB_COUNTABLE_INTERS_IN_EVENTS THEN
    REPEAT CONJ_TAC THENL
    [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
     GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[COUNTABLE_GSPEC_NUM];
     REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
     EXISTS_TAC `(A:num->A->bool) m` THEN
     EXISTS_TAC `m:num` THEN REWRITE_TAC[GE; LE_REFL]];
    ALL_TAC] THEN
   MATCH_MP_TAC PROB_COUNTABLE_UNION_IN_EVENTS THEN
   CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIV] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[COUNTABLE_GSPEC_NUM]]);;

(* ========================================================================= *)
(* Countable subadditivity (standalone, promoted from BC1 infrastructure)    *)
(* ========================================================================= *)

(* This is PROB_COUNTABLE_SUBADDITIVE_INDEXED restated for clarity:
   P(UNIONS_{n} B_n) <= sum_{n=0}^{inf} P(B_n)
   Already proved at line ~1404, just providing a reference comment. *)

(* ========================================================================= *)
(* Distribution function (Williams 3.9)                                      *)
(* ========================================================================= *)

let distribution_fn = new_definition
  `distribution_fn (p:A prob_space) (X:A->real) (c:real) =
   prob p {x | x IN prob_carrier p /\ X x <= c}`;;

(* F_X is well-defined for random variables *)
let DIST_FN_IN_EVENTS = prove
  (`!p:A prob_space X c.
      random_variable p X
      ==> {x | x IN prob_carrier p /\ X x <= c} IN prob_events p`,
   SIMP_TAC[random_variable]);;

(* F_X(c) >= 0 *)
let DIST_FN_NONNEG = prove
  (`!p:A prob_space X c.
      random_variable p X ==> &0 <= distribution_fn p X c`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[distribution_fn] THEN
   MATCH_MP_TAC PROB_POSITIVE THEN ASM_SIMP_TAC[DIST_FN_IN_EVENTS]);;

(* F_X(c) <= 1 *)
let DIST_FN_LE_1 = prove
  (`!p:A prob_space X c.
      random_variable p X ==> distribution_fn p X c <= &1`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[distribution_fn] THEN
   MATCH_MP_TAC PROB_LE_1 THEN ASM_SIMP_TAC[DIST_FN_IN_EVENTS]);;

(* F_X is monotone non-decreasing *)
let DIST_FN_MONO = prove
  (`!p:A prob_space X a b.
      random_variable p X /\ a <= b
      ==> distribution_fn p X a <= distribution_fn p X b`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[distribution_fn] THEN
   MATCH_MP_TAC PROB_MONO THEN
   ASM_SIMP_TAC[DIST_FN_IN_EVENTS] THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
   GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   ASM_MESON_TAC[REAL_LE_TRANS]);;

(* ========================================================================= *)
(* Independence of random variables (Williams 4.1)                           *)
(* ========================================================================= *)

let indep_rv = new_definition
  `indep_rv (p:A prob_space) (X:A->real) (Y:A->real) <=>
   random_variable p X /\ random_variable p Y /\
   !a b. prob p {x | x IN prob_carrier p /\ X x <= a /\ Y x <= b} =
         prob p {x | x IN prob_carrier p /\ X x <= a} *
         prob p {x | x IN prob_carrier p /\ Y x <= b}`;;

(* Independence is symmetric *)
let INDEP_RV_SYM = prove
  (`!p:A prob_space X Y. indep_rv p X Y <=> indep_rv p Y X`,
   REPEAT GEN_TAC THEN REWRITE_TAC[indep_rv] THEN
   EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `a:real` THEN X_GEN_TAC `b:real` THEN
    SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\ Y x <= a /\ X x <= b} =
       {x | x IN prob_carrier p /\ X x <= b /\ Y x <= a}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[];
     ASM_MESON_TAC[REAL_MUL_SYM]];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `a:real` THEN X_GEN_TAC `b:real` THEN
    SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\ X x <= a /\ Y x <= b} =
       {x | x IN prob_carrier p /\ Y x <= b /\ X x <= a}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[];
     ASM_MESON_TAC[REAL_MUL_SYM]]]);;

(* Independent RVs are individually random variables *)
let INDEP_RV_IMP_RV = prove
  (`!p:A prob_space X Y.
      indep_rv p X Y ==> random_variable p X /\ random_variable p Y`,
   REWRITE_TAC[indep_rv] THEN MESON_TAC[]);;

(* Independence in terms of distribution functions *)
let INDEP_RV_DIST_FN = prove
  (`!p:A prob_space X Y.
      indep_rv p X Y <=>
      random_variable p X /\ random_variable p Y /\
      !a b. prob p {x | x IN prob_carrier p /\ X x <= a /\ Y x <= b} =
            distribution_fn p X a * distribution_fn p Y b`,
   REPEAT GEN_TAC THEN REWRITE_TAC[indep_rv; distribution_fn]);;


(* ========================================================================= *)
(* Generated sigma-algebra (Williams 1.1)                                    *)
(* ========================================================================= *)

(* Powerset forms a sigma-algebra *)
let SIGMA_ALGEBRA_POWERSET = prove
  (`!U:A->bool. sigma_algebra {s | s SUBSET U}`,
   GEN_TAC THEN REWRITE_TAC[sigma_algebra; IN_ELIM_THM] THEN
   REPEAT CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[];
    GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[];
    GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    ASM SET_TAC[]]);;

(* Carrier of powerset sigma-algebra *)
let SIGMA_ALGEBRA_POWERSET_CARRIER = prove
  (`!U:A->bool. UNIONS {s | s SUBSET U} = U`,
   GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM] THEN
   GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `s:A->bool` STRIP_ASSUME_TAC) THEN
    ASM SET_TAC[];
    DISCH_TAC THEN EXISTS_TAC `U:A->bool` THEN
    ASM_REWRITE_TAC[SUBSET_REFL]]);;

(* Generated sigma-algebra: smallest sigma-algebra over U containing C *)
let sigma_generated = new_definition
  `sigma_generated (U:A->bool) (C:(A->bool)->bool) =
   INTERS {f | sigma_algebra f /\ C SUBSET f /\ UNIONS f = U}`;;

(* C is contained in sigma(C) *)
let SIGMA_GENERATED_SUPERSET = prove
  (`!U:A->bool C.
      (!a. a IN C ==> a SUBSET U)
      ==> C SUBSET sigma_generated U C`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[sigma_generated; SUBSET; IN_INTERS] THEN
   REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[]);;

(* Clean characterization of membership in sigma_generated *)
let SIGMA_GENERATED_MEM = prove
  (`!U:A->bool C a.
      a IN sigma_generated U C <=>
      !f. sigma_algebra f /\ C SUBSET f /\ UNIONS f = U ==> a IN f`,
   REPEAT GEN_TAC THEN REWRITE_TAC[sigma_generated; IN_INTERS] THEN
   EQ_TAC THENL
   [(* forward: a IN INTERS {f | P f} ==> !f. P f ==> a IN f *)
    DISCH_TAC THEN X_GEN_TAC `g:(A->bool)->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `g:(A->bool)->bool`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    (* backward: (!f. P f ==> a IN f) ==> a IN INTERS {f | P f} *)
    DISCH_TAC THEN X_GEN_TAC `t:(A->bool)->bool` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* sigma(C) has carrier U *)
let SIGMA_GENERATED_CARRIER = prove
  (`!U:A->bool C.
      (!a. a IN C ==> a SUBSET U)
      ==> UNIONS (sigma_generated U C) = U`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `x:A` THEN EQ_TAC THENL
   [(* forward: x IN UNIONS(sigma_generated U C) ==> x IN U *)
    REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:A->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(s:A->bool) SUBSET U` ASSUME_TAC THENL
    [UNDISCH_TAC `(s:A->bool) IN sigma_generated U C` THEN
     REWRITE_TAC[SIGMA_GENERATED_MEM] THEN
     DISCH_THEN(MP_TAC o SPEC `{t:A->bool | t SUBSET U}`) THEN
     REWRITE_TAC[SIGMA_ALGEBRA_POWERSET; SIGMA_ALGEBRA_POWERSET_CARRIER;
                  IN_ELIM_THM] THEN
     DISCH_THEN MATCH_MP_TAC THEN
     ASM SET_TAC[];
     ASM SET_TAC[]];
    (* backward: x IN U ==> x IN UNIONS(sigma_generated U C) *)
    DISCH_TAC THEN REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `U:A->bool` THEN
    CONJ_TAC THENL
    [(* U IN sigma_generated U C *)
     REWRITE_TAC[SIGMA_GENERATED_MEM] THEN
     X_GEN_TAC `f:(A->bool)->bool` THEN STRIP_TAC THEN
     ASM_MESON_TAC[SIGMA_ALGEBRA_CARRIER];
     (* x IN U *)
     ASM_REWRITE_TAC[]]]);;

(* sigma(C) is a sigma-algebra *)
let SIGMA_GENERATED_IS_SIGMA_ALGEBRA = prove
  (`!U:A->bool C.
      (!a. a IN C ==> a SUBSET U)
      ==> sigma_algebra (sigma_generated U C)`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `UNIONS (sigma_generated U (C:(A->bool)->bool)) = U`
     ASSUME_TAC THENL
   [ASM_SIMP_TAC[SIGMA_GENERATED_CARRIER]; ALL_TAC] THEN
   REWRITE_TAC[sigma_algebra] THEN ASM_REWRITE_TAC[] THEN
   REPEAT CONJ_TAC THENL
   [(* U IN sigma_generated U C *)
    REWRITE_TAC[SIGMA_GENERATED_MEM] THEN
    X_GEN_TAC `f:(A->bool)->bool` THEN STRIP_TAC THEN
    ASM_MESON_TAC[SIGMA_ALGEBRA_CARRIER];
    (* complement closure *)
    X_GEN_TAC `a:A->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[SIGMA_GENERATED_MEM] THEN
    X_GEN_TAC `f:(A->bool)->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(a:A->bool) IN f` ASSUME_TAC THENL
    [UNDISCH_TAC `(a:A->bool) IN sigma_generated U C` THEN
     REWRITE_TAC[SIGMA_GENERATED_MEM] THEN
     DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN `(U:A->bool) DIFF a = UNIONS f DIFF a` SUBST1_TAC THENL
    [ASM_REWRITE_TAC[]; ASM_MESON_TAC[SIGMA_ALGEBRA_COMPL]];
    (* countable union closure *)
    X_GEN_TAC `s:(A->bool)->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[SIGMA_GENERATED_MEM] THEN
    X_GEN_TAC `f:(A->bool)->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s SUBSET (f:(A->bool)->bool)` ASSUME_TAC THENL
    [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `a:A->bool` THEN DISCH_TAC THEN
     SUBGOAL_THEN `(a:A->bool) IN sigma_generated U C` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
     REWRITE_TAC[SIGMA_GENERATED_MEM] THEN
     DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    MATCH_MP_TAC SIGMA_ALGEBRA_UNION_COUNTABLE THEN
    ASM_REWRITE_TAC[]]);;

(* sigma(C) is the smallest: if f is a sigma-algebra over U containing C,
   then sigma(C) SUBSET f *)
let SIGMA_GENERATED_MINIMAL = prove
  (`!U:A->bool C f.
      sigma_algebra f /\ C SUBSET f /\ UNIONS f = U
      ==> sigma_generated U C SUBSET f`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN
   X_GEN_TAC `a:A->bool` THEN
   REWRITE_TAC[SIGMA_GENERATED_MEM] THEN
   DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;


(* ========================================================================= *)
(* Pi-system definition (Williams 1.6)                                       *)
(* ========================================================================= *)

(* A pi-system is a family closed under finite intersection *)
let pi_system = new_definition
  `pi_system (C:(A->bool)->bool) <=>
   ~(C = {}) /\ (!a b. a IN C /\ b IN C ==> (a INTER b) IN C)`;;

(* Every sigma-algebra is a pi-system *)
let SIGMA_ALGEBRA_IS_PI_SYSTEM = prove
  (`!f:(A->bool)->bool. sigma_algebra f ==> pi_system f`,
   GEN_TAC THEN REWRITE_TAC[pi_system; sigma_algebra] THEN
   STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `a INTER b = UNIONS f DIFF ((UNIONS f DIFF a) UNION (UNIONS f DIFF b)):A->bool`
      SUBST1_TAC THENL
    [MP_TAC(ISPECL [`f:(A->bool)->bool`; `a:A->bool`] SIGMA_ALGEBRA_SUBSET) THEN
     MP_TAC(ISPECL [`f:(A->bool)->bool`; `b:A->bool`] SIGMA_ALGEBRA_SUBSET) THEN
     ASM_REWRITE_TAC[] THEN SET_TAC[];
     ALL_TAC] THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC th) THEN
    SUBGOAL_THEN `(UNIONS f DIFF a) UNION (UNIONS f DIFF b) = UNIONS {UNIONS f DIFF a, UNIONS f DIFF b}:A->bool`
      SUBST1_TAC THENL
    [REWRITE_TAC[UNIONS_2]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[COUNTABLE_INSERT; COUNTABLE_EMPTY] THEN
    ASM_SIMP_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[]]);;


(* ========================================================================= *)
(* Dynkin Pi-Lambda Theorem                                                  *)
(* If a pi-system is contained in a lambda-system, then sigma(pi) is    *)
(* contained in the lambda-system. Fundamental for measure uniqueness.       *)
(* ========================================================================= *)

(* A lambda-system (Dynkin system): contains the carrier, closed under
   complement and countable disjoint union *)
let lambda_system = new_definition
  `lambda_system (U:A->bool) (L:(A->bool)->bool) <=>
   U IN L /\
   (!a. a IN L ==> (U DIFF a) IN L) /\
   (!B:num->A->bool. (!n. B n IN L) /\
     (!m n. ~(m = n) ==> DISJOINT (B m) (B n))
     ==> UNIONS {B n | n IN (:num)} IN L)`;;

let LAMBDA_SYSTEM_EMPTY = prove
 (`!U:A->bool L. lambda_system U L ==> {} IN L`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lambda_system] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `({}:A->bool) = U DIFF U` SUBST1_TAC THENL
  [SET_TAC[]; ASM_MESON_TAC[]]);;

(* Binary disjoint union via encoding as countable union *)
let LAMBDA_SYSTEM_UNION2 = prove
 (`!U:A->bool L a b.
     lambda_system U L /\ a IN L /\ b IN L /\ DISJOINT a b
     ==> (a UNION b) IN L`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [lambda_system]) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `\n:num. if n = 0 then a:A->bool else if n = 1 then b else {}`) THEN
  SUBGOAL_THEN `({}:A->bool) IN L` ASSUME_TAC THENL
  [SUBGOAL_THEN `({}:A->bool) = U DIFF U` SUBST1_TAC THENL
   [SET_TAC[]; ASM_MESON_TAC[]]; ALL_TAC] THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
  [CONJ_TAC THENL
   [GEN_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]); ALL_TAC] THEN
   MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN
   REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
   TRY(ASM_MESON_TAC[]) THEN
   REWRITE_TAC[DISJOINT_SYM] THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
   ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV; IN_UNION] THEN
  X_GEN_TAC `x:A` THEN EQ_TAC THENL
  [DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
   REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[NOT_IN_EMPTY]) THEN
   MESON_TAC[];
   STRIP_TAC THENL
   [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `1` THEN ASM_REWRITE_TAC[ARITH_EQ]]]);;

(* Proper difference in a lambda-system *)
let LAMBDA_SYSTEM_DIFF = prove
 (`!U:A->bool L a b.
     lambda_system U L /\ a IN L /\ b IN L /\ b SUBSET a /\ a SUBSET U
     ==> (a DIFF b) IN L`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a DIFF b = U DIFF ((U DIFF a) UNION b):A->bool`
    SUBST1_TAC THENL
  [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [lambda_system]) THEN
  STRIP_TAC THEN FIRST_ASSUM(fun th -> MATCH_MP_TAC th) THEN
  MATCH_MP_TAC LAMBDA_SYSTEM_UNION2 THEN
  EXISTS_TAC `U:A->bool` THEN
  REWRITE_TAC[lambda_system] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ASM SET_TAC[]]);;

(* Countable union = countable disjoint union via decomposition *)
let COUNTABLE_UNION_DISJOINT_DECOMP = prove
 (`!f:num->A->bool.
     UNIONS (IMAGE f (:num)) =
     UNIONS (IMAGE (\n. f n DIFF UNIONS (IMAGE f {m | m < n})) (:num))`,
  GEN_TAC THEN REWRITE_TAC[EXTENSION] THEN
  X_GEN_TAC `x:A` THEN
  REWRITE_TAC[UNIONS_IMAGE; IN_UNIV; IN_ELIM_THM; IN_DIFF] THEN
  EQ_TAC THENL
  [DISCH_TAC THEN
   MP_TAC(ISPEC `\n:num. (x:A) IN f n` num_WOP) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[UNIONS_IMAGE; IN_ELIM_THM] THEN
   DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
   ASM_MESON_TAC[LT];
   DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
   ASM_MESON_TAC[]]);;

(* The pieces in the disjoint decomposition are pairwise disjoint *)
let COUNTABLE_DISJOINT_DECOMP_DISJOINT = prove
 (`!f:num->A->bool m n.
     ~(m = n)
     ==> DISJOINT (f m DIFF UNIONS (IMAGE f {k | k < m}))
                   (f n DIFF UNIONS (IMAGE f {k | k < n}))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER;
    NOT_IN_EMPTY; IN_DIFF; UNIONS_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `x:A` THEN
  ASM_CASES_TAC `(m:num) < n` THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(n:num) < m` THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_ARITH_TAC);;

(* Lambda + intersection closure + subset U ==> sigma-algebra *)
let LAMBDA_SYSTEM_INTER_IMP_SIGMA = prove
 (`!U:A->bool L.
     lambda_system U L /\
     (!a b. a IN L /\ b IN L ==> (a INTER b) IN L) /\
     (!a. a IN L ==> a SUBSET U)
     ==> sigma_algebra L /\ UNIONS L = U`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U:A->bool) IN L` ASSUME_TAC THENL
  [ASM_MESON_TAC[lambda_system]; ALL_TAC] THEN
  SUBGOAL_THEN `!a:A->bool. a IN L ==> U DIFF a IN L` ASSUME_TAC THENL
  [ASM_MESON_TAC[lambda_system]; ALL_TAC] THEN
  SUBGOAL_THEN `({}:A->bool) IN L` ASSUME_TAC THENL
  [SUBGOAL_THEN `({}:A->bool) = U DIFF U` SUBST1_TAC THENL
   [SET_TAC[]; ASM_MESON_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `!a b:A->bool. a IN L /\ b IN L ==> (a UNION b) IN L`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `(a:A->bool) UNION b = U DIFF ((U DIFF a) INTER (U DIFF b))`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_DIFF; IN_INTER] THEN
    GEN_TAC THEN ASM_CASES_TAC `(x:A) IN U` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET]; ASM_MESON_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS (L:(A->bool)->bool) = U` ASSUME_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_UNIONS] THEN X_GEN_TAC `x:A` THEN
   EQ_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
   DISCH_TAC THEN EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[sigma_algebra] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:(A->bool)->bool` THEN STRIP_TAC THEN
  ASM_CASES_TAC `s:(A->bool)->bool = {}` THENL
  [ASM_REWRITE_TAC[UNIONS_0]; ALL_TAC] THEN
  MP_TAC(ISPEC `s:(A->bool)->bool` COUNTABLE_AS_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->A->bool` SUBST_ALL_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [COUNTABLE_UNION_DISJOINT_DECOMP] THEN
  MP_TAC(ASSUME `lambda_system (U:A->bool) L`) THEN
  REWRITE_TAC[lambda_system] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) MP_TAC)) THEN
  DISCH_THEN(MP_TAC o SPEC
    `\n:num. (f:num->A->bool) n DIFF UNIONS (IMAGE f {m | m < n})`) THEN
  REWRITE_TAC[SIMPLE_IMAGE; UNIONS_IMAGE; IN_UNIV] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL
  [GEN_TAC THEN
   SUBGOAL_THEN `!n:num. (f:num->A->bool) n IN L` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE; IN_UNIV]) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN
     `{y:A | ?x:num. x IN {m | m < n} /\ y IN (f:num->A->bool) x} =
      UNIONS (IMAGE f {m | m < n})` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    MESON_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `!j:num. UNIONS (IMAGE (f:num->A->bool) {m | m < j}) IN L`
     ASSUME_TAC THENL
   [INDUCT_TAC THENL
    [SUBGOAL_THEN `{m:num | m < 0} = {}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN ARITH_TAC;
      REWRITE_TAC[IMAGE_CLAUSES; UNIONS_0] THEN ASM_REWRITE_TAC[]];
     SUBGOAL_THEN `{m:num | m < SUC j} = j INSERT {m | m < j}`
       SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN ARITH_TAC;
      REWRITE_TAC[IMAGE_CLAUSES; UNIONS_INSERT] THEN ASM_MESON_TAC[]]];
    ALL_TAC] THEN
   SUBGOAL_THEN `(f:num->A->bool) n DIFF UNIONS (IMAGE f {m | m < n}) =
     f n INTER (U DIFF UNIONS (IMAGE f {m | m < n}))` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DIFF; IN_INTER] THEN
    GEN_TAC THEN EQ_TAC THENL
    [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET];
     MESON_TAC[]]; ALL_TAC] THEN
   ASM_MESON_TAC[];
   MAP_EVERY X_GEN_TAC [`m:num`; `p:num`] THEN DISCH_TAC THEN
   REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY;
     IN_DIFF; IN_ELIM_THM] THEN
   X_GEN_TAC `y:A` THEN
   ASM_CASES_TAC `(m:num) < p` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   ASM_CASES_TAC `(p:num) < m` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   ASM_ARITH_TAC]);;

(* lambda_generated: smallest lambda-system over U containing C *)
let lambda_generated = new_definition
  `lambda_generated (U:A->bool) (C:(A->bool)->bool) =
   INTERS {L | lambda_system U L /\ C SUBSET L}`;;

let LAMBDA_GENERATED_MEM = prove
 (`!U:A->bool C a.
     a IN lambda_generated U C <=>
     (!L. lambda_system U L /\ C SUBSET L ==> a IN L)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lambda_generated; IN_INTERS; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let LAMBDA_GENERATED_IS_LAMBDA = prove
 (`!U:A->bool C.
     (!a. a IN C ==> a SUBSET U)
     ==> lambda_system U (lambda_generated U C)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[lambda_system] THEN
  REWRITE_TAC[LAMBDA_GENERATED_MEM] THEN
  REPEAT CONJ_TAC THENL
  [MESON_TAC[lambda_system];
   X_GEN_TAC `a:A->bool` THEN DISCH_TAC THEN
   X_GEN_TAC `L:(A->bool)->bool` THEN STRIP_TAC THEN
   ASM_MESON_TAC[lambda_system];
   X_GEN_TAC `B:num->A->bool` THEN STRIP_TAC THEN
   X_GEN_TAC `L:(A->bool)->bool` THEN STRIP_TAC THEN
   SUBGOAL_THEN `!n:num. (B n:A->bool) IN L` ASSUME_TAC THENL
   [GEN_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [lambda_system]) THEN
   STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let LAMBDA_GENERATED_SUBSET = prove
 (`!U:A->bool C.
     (!a. a IN C ==> a SUBSET U) ==> C SUBSET lambda_generated U C`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; LAMBDA_GENERATED_MEM] THEN
  X_GEN_TAC `a:A->bool` THEN DISCH_TAC THEN
  X_GEN_TAC `L:(A->bool)->bool` THEN STRIP_TAC THEN ASM SET_TAC[]);;

let LAMBDA_GENERATED_MINIMAL = prove
 (`!U:A->bool C L.
     lambda_system U L /\ C SUBSET L ==> lambda_generated U C SUBSET L`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `a:A->bool` THEN
  REWRITE_TAC[LAMBDA_GENERATED_MEM] THEN
  DISCH_THEN(MP_TAC o SPEC `L:(A->bool)->bool`) THEN ASM_REWRITE_TAC[]);;

let LAMBDA_GENERATED_SUBSET_U = prove
 (`!U:A->bool C a.
     (!c. c IN C ==> c SUBSET U) /\ a IN lambda_generated U C
     ==> a SUBSET U`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LAMBDA_GENERATED_MEM] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `{s:A->bool | s SUBSET U}`) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [REWRITE_TAC[lambda_system; IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THENL
    [SET_TAC[];
     SET_TAC[];
     REPEAT STRIP_TAC THEN
     REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:A` THEN
     REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
     DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
     ASM SET_TAC[]];
   ASM SET_TAC[]];
  SIMP_TAC[IN_ELIM_THM]]);;

(* G_A is a lambda system *)
let LAMBDA_GENERATED_GA_IS_LAMBDA = prove
 (`!(U:A->bool) C A.
     (!c. c IN C ==> c SUBSET U) /\
     A IN lambda_generated U C
     ==> lambda_system U
           {B | B IN lambda_generated U C /\ A INTER B IN lambda_generated U C}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(A:A->bool) SUBSET U` ASSUME_TAC THENL
  [ASM_MESON_TAC[LAMBDA_GENERATED_SUBSET_U]; ALL_TAC] THEN
  ABBREV_TAC `LL = lambda_generated (U:A->bool) C` THEN
  SUBGOAL_THEN `lambda_system (U:A->bool) LL` ASSUME_TAC THENL
  [EXPAND_TAC "LL" THEN ASM_SIMP_TAC[LAMBDA_GENERATED_IS_LAMBDA]; ALL_TAC] THEN
  REWRITE_TAC[lambda_system; IN_ELIM_THM] THEN
  CONJ_TAC THENL
  [SUBGOAL_THEN `(U:A->bool) IN LL` ASSUME_TAC THENL
   [ASM_MESON_TAC[lambda_system]; ALL_TAC] THEN
   SUBGOAL_THEN `(A:A->bool) INTER U = A` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [X_GEN_TAC `B:A->bool` THEN STRIP_TAC THEN
   SUBGOAL_THEN `(B:A->bool) SUBSET U` ASSUME_TAC THENL
   [EXPAND_TAC "LL" THEN ASM_MESON_TAC[LAMBDA_GENERATED_SUBSET_U]; ALL_TAC] THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC[lambda_system]; ALL_TAC] THEN
   SUBGOAL_THEN `(A:A->bool) INTER (U DIFF B) = A DIFF (A INTER B)`
     SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC(ISPECL [`U:A->bool`; `LL:(A->bool)->bool`;
     `A:A->bool`; `(A:A->bool) INTER B`] LAMBDA_SYSTEM_DIFF) THEN
   ASM_REWRITE_TAC[] THEN SET_TAC[];
   X_GEN_TAC `B:num->A->bool` THEN STRIP_TAC THEN
   SUBGOAL_THEN `!n:num. (B n:A->bool) IN LL` ASSUME_TAC THENL
   [GEN_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `!n:num. (A:A->bool) INTER B n IN LL` ASSUME_TAC THENL
   [GEN_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `UNIONS {(B:num->A->bool) n | n IN (:num)} IN LL`
     ASSUME_TAC THENL
   [MP_TAC(ASSUME `lambda_system (U:A->bool) LL`) THEN
    REWRITE_TAC[lambda_system] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (K ALL_TAC) MP_TAC)) THEN
    DISCH_THEN(MP_TAC o SPEC `B:num->A->bool`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN
     `(A:A->bool) INTER UNIONS {(B:num->A->bool) n | n IN (:num)} =
      UNIONS {A INTER B n | n IN (:num)}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
    MESON_TAC[]; ALL_TAC] THEN
   MP_TAC(ASSUME `lambda_system (U:A->bool) LL`) THEN
   REWRITE_TAC[lambda_system] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC)
     (CONJUNCTS_THEN2 (K ALL_TAC) MP_TAC)) THEN
   DISCH_THEN(MP_TAC o SPEC `\n:num. (A:A->bool) INTER (B:num->A->bool) n`) THEN
   REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[] THEN
   MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `n:num`]) THEN
   ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

(* Step 1: Pi-system elements INTER with lambda_generated *)
let LAMBDA_GENERATED_INTER_PI = prove
 (`!(U:A->bool) C.
     pi_system C /\ (!c. c IN C ==> c SUBSET U)
     ==> !A B. A IN C /\ B IN lambda_generated U C
               ==> A INTER B IN lambda_generated U C`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `A IN lambda_generated (U:A->bool) C` ASSUME_TAC THENL
  [ASM_MESON_TAC[LAMBDA_GENERATED_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:A->bool`; `C:(A->bool)->bool`; `A:A->bool`]
    LAMBDA_GENERATED_GA_IS_LAMBDA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `C SUBSET {B:A->bool | B IN lambda_generated U C /\
    A INTER B IN lambda_generated U C}` ASSUME_TAC THENL
  [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `D:A->bool` THEN
   DISCH_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[LAMBDA_GENERATED_SUBSET; SUBSET]; ALL_TAC] THEN
   SUBGOAL_THEN `(A:A->bool) INTER D IN C` ASSUME_TAC THENL
   [ASM_MESON_TAC[pi_system]; ALL_TAC] THEN
   ASM_MESON_TAC[LAMBDA_GENERATED_SUBSET; SUBSET];
   ALL_TAC] THEN
  MP_TAC(ISPECL [`U:A->bool`; `C:(A->bool)->bool`;
    `{B:A->bool | B IN lambda_generated U C /\ A INTER B IN lambda_generated U C}`]
    LAMBDA_GENERATED_MINIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

(* Step 2: lambda_generated is closed under intersection *)
let LAMBDA_GENERATED_INTER_CLOSED = prove
 (`!(U:A->bool) C.
     pi_system C /\ (!c. c IN C ==> c SUBSET U)
     ==> !A B. A IN lambda_generated U C /\ B IN lambda_generated U C
               ==> A INTER B IN lambda_generated U C`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:A->bool`; `C:(A->bool)->bool`; `A:A->bool`]
    LAMBDA_GENERATED_GA_IS_LAMBDA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `C SUBSET {B:A->bool | B IN lambda_generated U C /\
    A INTER B IN lambda_generated U C}` ASSUME_TAC THENL
  [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `D:A->bool` THEN
   DISCH_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[LAMBDA_GENERATED_SUBSET; SUBSET]; ALL_TAC] THEN
   SUBGOAL_THEN `(A:A->bool) INTER D = D INTER A` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
   MP_TAC(ISPECL [`U:A->bool`; `C:(A->bool)->bool`]
     LAMBDA_GENERATED_INTER_PI) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`D:A->bool`; `A:A->bool`]) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MP_TAC(ISPECL [`U:A->bool`; `C:(A->bool)->bool`;
    `{B:A->bool | B IN lambda_generated U C /\ A INTER B IN lambda_generated U C}`]
    LAMBDA_GENERATED_MINIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

(* Main theorem: Dynkin Pi-Lambda *)
let DYNKIN_PI_LAMBDA = prove
 (`!(U:A->bool) C L.
     pi_system C /\ UNIONS C = U /\
     lambda_system U L /\ C SUBSET L
     ==> sigma_generated U C SUBSET L`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!c:A->bool. c IN C ==> c SUBSET U` ASSUME_TAC THENL
  [ASM_MESON_TAC[SUBSET; IN_UNIONS]; ALL_TAC] THEN
  SUBGOAL_THEN `!A B:A->bool. A IN lambda_generated U C /\
    B IN lambda_generated U C ==> A INTER B IN lambda_generated U C`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[LAMBDA_GENERATED_INTER_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `!a:A->bool. a IN lambda_generated U C ==> a SUBSET U`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[LAMBDA_GENERATED_SUBSET_U]; ALL_TAC] THEN
  SUBGOAL_THEN `lambda_system (U:A->bool) (lambda_generated U C)`
    ASSUME_TAC THENL
  [ASM_SIMP_TAC[LAMBDA_GENERATED_IS_LAMBDA]; ALL_TAC] THEN
  SUBGOAL_THEN `sigma_algebra (lambda_generated (U:A->bool) C) /\
    UNIONS (lambda_generated U C) = U` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC LAMBDA_SYSTEM_INTER_IMP_SIGMA THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `sigma_generated (U:A->bool) C SUBSET lambda_generated U C`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIGMA_GENERATED_MINIMAL THEN ASM_REWRITE_TAC[] THEN
   ASM_SIMP_TAC[LAMBDA_GENERATED_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `lambda_generated (U:A->bool) C SUBSET L` ASSUME_TAC THENL
  [MATCH_MP_TAC LAMBDA_GENERATED_MINIMAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM SET_TAC[]);;


(* ========================================================================= *)
(* Linearity of simple expectation: E[X + Y] = E[X] + E[Y]                   *)
(* (Williams, fundamental property)                                          *)
(* ========================================================================= *)


(* Finite additivity for indexed families of disjoint events *)
let PROB_FINITE_ADDITIVE_IMAGE = prove
  (`!p:A prob_space (f:B->A->bool) s.
      FINITE s /\
      (!x. x IN s ==> f x IN prob_events p) /\
      (!x y. x IN s /\ y IN s /\ ~(x = y) ==> DISJOINT (f x) (f y))
      ==> prob p (UNIONS (IMAGE f s)) = sum s (\x. prob p (f x))`,
   GEN_TAC THEN GEN_TAC THEN
   REWRITE_TAC[IMP_CONJ] THEN
   MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[IMAGE_CLAUSES; UNIONS_0; SUM_CLAUSES; PROB_EMPTY;
                NOT_IN_EMPTY];
    ALL_TAC] THEN
   MAP_EVERY X_GEN_TAC [`a:B`; `t:B->bool`] THEN
   (* Split IH /\ ~(a IN t) /\ FINITE t *)
   DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
   ASM_SIMP_TAC[IMAGE_CLAUSES; UNIONS_INSERT; SUM_CLAUSES] THEN
   DISCH_TAC THEN DISCH_TAC THEN
   (* Establish events membership for a and for t *)
   SUBGOAL_THEN `(f:B->A->bool) a IN prob_events p` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
   SUBGOAL_THEN `!x:B. x IN t ==> (f:B->A->bool) x IN prob_events p`
     (LABEL_TAC "EV_T") THENL
   [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
   (* Establish disjointness for t *)
   SUBGOAL_THEN `!x:B y:B. x IN t /\ y IN t /\ ~(x = y)
                  ==> DISJOINT ((f:B->A->bool) x) (f y)`
     (LABEL_TAC "DISJ_T") THENL
   [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
   (* Apply IH to get equation for t *)
   SUBGOAL_THEN `prob p (UNIONS (IMAGE (f:B->A->bool) t)) =
                  sum t (\x:B. prob p (f x))` ASSUME_TAC THENL
   [USE_THEN "IH" MP_TAC THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
   (* UNIONS IMAGE in events *)
   SUBGOAL_THEN `UNIONS (IMAGE (f:B->A->bool) t) IN prob_events p` ASSUME_TAC THENL
   [MATCH_MP_TAC PROB_FINITE_UNION_IN_EVENTS THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
   (* DISJOINT f(a) (UNIONS IMAGE) *)
   SUBGOAL_THEN `DISJOINT ((f:B->A->bool) a) (UNIONS (IMAGE f t))`
     ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE
      `DISJOINT (a:A->bool) (UNIONS s) <=> !x:A->bool. x IN s ==> DISJOINT a x`] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_MESON_TAC[IN_INSERT];
    ALL_TAC] THEN
   (* Apply PROB_ADDITIVE *)
   SUBGOAL_THEN `prob p ((f:B->A->bool) a UNION UNIONS (IMAGE f t)) =
                  prob p (f a) + prob p (UNIONS (IMAGE f t))` SUBST1_TAC THENL
   [MATCH_MP_TAC PROB_ADDITIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   ASM_REWRITE_TAC[]);;

(* Helper: joint level sets are disjoint for different Y values *)
let JOINT_LEVEL_SETS_DISJOINT_Y = prove
  (`!p:A prob_space. !X:A->real. !Y:A->real. !u:real. !v1:real. !v2:real.
      ~(v1 = v2)
      ==> DISJOINT {x | x IN prob_carrier p /\ X x = u /\ Y x = v1}
                    {x | x IN prob_carrier p /\ X x = u /\ Y x = v2}`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER;
     IN_ELIM_THM; NOT_IN_EMPTY] THEN
   ASM_MESON_TAC[]);;

(* Helper: prob of level set = sum over joint level sets *)
let PROB_LEVEL_SET_AS_SUM = prove
  (`!p:A prob_space. !X:A->real. !Y:A->real. !u:real.
      simple_rv p X /\ simple_rv p Y /\
      u IN IMAGE X (prob_carrier p)
      ==> prob p {x | x IN prob_carrier p /\ X x = u} =
          sum (IMAGE Y (prob_carrier p))
              (\v. prob p {x | x IN prob_carrier p /\ X x = u /\ Y x = v})`,
   REPEAT STRIP_TAC THEN
   (* {X = u} = UNIONS_v ({X = u} INTER {Y = v}) *)
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ (X:A->real) x = u} =
      UNIONS (IMAGE (\v:real. {x:A | x IN prob_carrier p /\ X x = u /\ (Y:A->real) x = v})
                    (IMAGE (Y:A->real) (prob_carrier p)))`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN EQ_TAC THENL
    [(* forward *)
     STRIP_TAC THEN REWRITE_TAC[IN_UNIONS] THEN
     EXISTS_TAC `{x':A | x' IN prob_carrier p /\ (X:A->real) x' = u /\ (Y:A->real) x' = Y x}` THEN
     CONJ_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(Y:A->real) x` THEN CONJ_TAC THENL
      [REWRITE_TAC[];
       REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]];
     (* backward *)
     REWRITE_TAC[IN_UNIONS] THEN
     DISCH_THEN(X_CHOOSE_THEN `s:A->bool` STRIP_ASSUME_TAC) THEN
     UNDISCH_TAC `(s:A->bool) IN IMAGE (\v:real. {x:A | x IN prob_carrier p /\ (X:A->real) x = u /\ (Y:A->real) x = v})
                                        (IMAGE (Y:A->real) (prob_carrier p))` THEN
     REWRITE_TAC[IN_IMAGE] THEN
     DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
     UNDISCH_TAC `x:A IN s` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
     SIMP_TAC[]];
    ALL_TAC] THEN
   (* These sets are pairwise disjoint events *)
   SUBGOAL_THEN `FINITE (IMAGE (Y:A->real) (prob_carrier p))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simple_rv]) THEN
    SIMP_TAC[GSYM SIMPLE_IMAGE; FINITE_IMAGE];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `!v:real. {x:A | x IN prob_carrier p /\ (X:A->real) x = u /\ (Y:A->real) x = v} IN prob_events p`
     ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\ (X:A->real) x = u /\ (Y:A->real) x = v} =
       {x:A | x IN prob_carrier p /\ X x = u} INTER
       {x:A | x IN prob_carrier p /\ Y x = v}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN MESON_TAC[];
     ALL_TAC] THEN
    MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simple_rv]) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simple_rv]) THEN
    STRIP_TAC THEN STRIP_TAC THEN
    ASM_SIMP_TAC[RANDOM_VARIABLE_LEVEL_SET];
    ALL_TAC] THEN
   (* Use finite additivity *)
   MATCH_MP_TAC PROB_FINITE_ADDITIVE_IMAGE THEN
   ASM_REWRITE_TAC[] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC JOINT_LEVEL_SETS_DISJOINT_Y THEN
   ASM_REWRITE_TAC[]);;

(* Key identity: expectation via double sum over pairs of level sets *)
(* E[X] = sum_u sum_v u * P({X=u,Y=v}) for any simple Y *)
let SIMPLE_EXPECTATION_DOUBLE_SUM = prove
  (`!p:A prob_space (X:A->real) (Y:A->real).
      simple_rv p X /\ simple_rv p Y
      ==> simple_expectation p X =
          sum (IMAGE X (prob_carrier p))
              (\u. sum (IMAGE Y (prob_carrier p))
                       (\v. u * prob p {x | x IN prob_carrier p /\ X x = u /\ Y x = v}))`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[simple_expectation; SET_IN_SIMP] THEN
   MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN
   REWRITE_TAC[] THEN
   REWRITE_TAC[SUM_LMUL] THEN AP_TERM_TAC THEN
   MATCH_MP_TAC PROB_LEVEL_SET_AS_SUM THEN
   ASM_REWRITE_TAC[]);;

(* Helper: sums over two finite sets with same function are equal when the
   function vanishes on the symmetric difference *)
let SUM_SUPPORT_EQ = prove
  (`!f:A->real s t.
        FINITE s /\ FINITE t /\
        (!x. x IN s /\ ~(x IN t) ==> f x = &0) /\
        (!x. x IN t /\ ~(x IN s) ==> f x = &0)
        ==> sum s f = sum t f`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `sum (s UNION t:A->bool) f = sum s (f:A->real)` MP_TAC THENL
   [MATCH_MP_TAC SUM_SUPERSET THEN
    REWRITE_TAC[SUBSET_UNION] THEN ASM SET_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `sum (s UNION t:A->bool) f = sum t (f:A->real)` MP_TAC THENL
   [MATCH_MP_TAC SUM_SUPERSET THEN
    REWRITE_TAC[SUBSET_UNION] THEN ASM SET_TAC[]; ALL_TAC] THEN
   MESON_TAC[]);;

(* Inner sum reindexing for E[X+Y]: for each u,
   sum over IMAGE(X+Y) of w*P({X=u,Y=w-u}) = sum over IMAGE(Y) of (u+v)*P({X=u,Y=v}) *)
let INNER_SUM_REINDEX = prove(
  `!p:A prob_space (X:A->real) (Y:A->real) u:real.
      FINITE (IMAGE (Y:A->real) (prob_carrier p)) /\
      FINITE (IMAGE (\x:A. (X:A->real) x + (Y:A->real) x) (prob_carrier p))
      ==> sum (IMAGE (\x. X x + Y x) (prob_carrier p))
              (\w. w * prob p {x | x IN prob_carrier p /\ X x = u /\ Y x = w - u}) =
          sum (IMAGE Y (prob_carrier p))
              (\v. (u + v) * prob p {x | x IN prob_carrier p /\ X x = u /\ Y x = v})`,
   REPEAT STRIP_TAC THEN
   CONV_TAC SYM_CONV THEN
   (* Reindex sum over IMAGE Y to sum over IMAGE (\v.u+v)(IMAGE Y) *)
   SUBGOAL_THEN
     `sum (IMAGE (Y:A->real) (prob_carrier p))
          (\v. (u + v) * prob p {x | x IN prob_carrier p /\ (X:A->real) x = u /\ Y x = v}) =
      sum (IMAGE (\v:real. u + v) (IMAGE (Y:A->real) (prob_carrier p)))
          (\w. w * prob p {x | x IN prob_carrier p /\ X x = u /\ Y x = w - u})`
     SUBST1_TAC THENL
   [MP_TAC(ISPECL [`\v:real. u + v`;
                    `\w:real. w * prob (p:A prob_space)
                        {x:A | x IN prob_carrier p /\ (X:A->real) x = u /\ (Y:A->real) x = w - u}`;
                    `IMAGE (Y:A->real) (prob_carrier p)`] SUM_IMAGE) THEN
    ANTS_TAC THENL [REWRITE_TAC[REAL_EQ_ADD_LCANCEL]; ALL_TAC] THEN
    REWRITE_TAC[o_DEF] THEN
    TRY BETA_TAC THEN
    REWRITE_TAC[REAL_ADD_SUB] THEN SIMP_TAC[];
    ALL_TAC] THEN
   (* Equate summation domains via SUM_SUPPORT_EQ *)
   MATCH_MP_TAC SUM_SUPPORT_EQ THEN
   ASM_SIMP_TAC[FINITE_IMAGE] THEN
   (* Key lemma: if w not in BOTH images, the summand is 0 *)
   SUBGOAL_THEN
     `!w:real. ~(w IN IMAGE (\v:real. u + v) (IMAGE (Y:A->real) (prob_carrier p)) /\
                 w IN IMAGE (\x:A. (X:A->real) x + (Y:A->real) x) (prob_carrier p))
      ==> w * prob (p:A prob_space)
              {x:A | x IN prob_carrier p /\ (X:A->real) x = u /\ (Y:A->real) x = w - u} = &0`
     ASSUME_TAC THENL
   [X_GEN_TAC `w:real` THEN REWRITE_TAC[DE_MORGAN_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ (X:A->real) x = u /\ (Y:A->real) x = w - u} = {}`
      (fun th -> REWRITE_TAC[th; PROB_EMPTY; REAL_MUL_RZERO]) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `a:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `w IN IMAGE (\v:real. u + v) (IMAGE (Y:A->real) (prob_carrier (p:A prob_space)))`
      ASSUME_TAC THENL
    [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `w - u:real` THEN
     TRY BETA_TAC THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      EXISTS_TAC `a:A` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
     ALL_TAC] THEN
    SUBGOAL_THEN `w IN IMAGE (\x:A. (X:A->real) x + (Y:A->real) x) (prob_carrier (p:A prob_space))`
      ASSUME_TAC THENL
    [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `a:A` THEN
     TRY BETA_TAC THEN
     ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
     ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
   CONJ_TAC THEN X_GEN_TAC `w:real` THEN STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

(* Linearity of simple expectation: E[X+Y] = E[X] + E[Y] *)
let SIMPLE_EXPECTATION_ADD = prove
  (`!p:A prob_space (X:A->real) (Y:A->real).
      simple_rv p X /\ simple_rv p Y
      ==> simple_expectation p (\x. X x + Y x) =
          simple_expectation p X + simple_expectation p Y`,
   REPEAT STRIP_TAC THEN
   (* Step 1: Express E[X] and E[Y] as double sums *)
   SUBGOAL_THEN
     `simple_expectation p (X:A->real) =
      sum (IMAGE X (prob_carrier p))
          (\u. sum (IMAGE (Y:A->real) (prob_carrier p))
                   (\v. u * prob p {x | x IN prob_carrier p /\ X x = u /\ Y x = v}))`
     SUBST1_TAC THENL
   [ASM_SIMP_TAC[SIMPLE_EXPECTATION_DOUBLE_SUM]; ALL_TAC] THEN
   SUBGOAL_THEN
     `simple_expectation p (Y:A->real) =
      sum (IMAGE Y (prob_carrier p))
          (\v. sum (IMAGE (X:A->real) (prob_carrier p))
                   (\u. v * prob p {x | x IN prob_carrier p /\ X x = u /\ Y x = v}))`
     SUBST1_TAC THENL
   [MP_TAC(SPECL [`p:A prob_space`; `Y:A->real`; `X:A->real`]
       SIMPLE_EXPECTATION_DOUBLE_SUM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `v:real` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `u:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
   (* Step 2: Swap the sums in E[Y] using SUM_SWAP *)
   SUBGOAL_THEN `FINITE (IMAGE (X:A->real) (prob_carrier p))` ASSUME_TAC THENL
   [UNDISCH_TAC `simple_rv (p:A prob_space) (X:A->real)` THEN
    REWRITE_TAC[simple_rv] THEN
    SIMP_TAC[GSYM SIMPLE_IMAGE; FINITE_IMAGE];
    ALL_TAC] THEN
   SUBGOAL_THEN `FINITE (IMAGE (Y:A->real) (prob_carrier p))` ASSUME_TAC THENL
   [UNDISCH_TAC `simple_rv (p:A prob_space) (Y:A->real)` THEN
    REWRITE_TAC[simple_rv] THEN
    SIMP_TAC[GSYM SIMPLE_IMAGE; FINITE_IMAGE];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `sum (IMAGE (Y:A->real) (prob_carrier p))
          (\v. sum (IMAGE (X:A->real) (prob_carrier p))
                   (\u. v * prob p {x | x IN prob_carrier p /\ X x = u /\ Y x = v})) =
      sum (IMAGE X (prob_carrier p))
          (\u. sum (IMAGE Y (prob_carrier p))
                   (\v. v * prob p {x | x IN prob_carrier p /\ X x = u /\ Y x = v}))`
     SUBST1_TAC THENL
   [MP_TAC(ISPECL
      [`\(v:real) (u:real). v * prob (p:A prob_space)
          {x | x IN prob_carrier p /\ (X:A->real) x = u /\ (Y:A->real) x = v}`;
       `IMAGE (Y:A->real) (prob_carrier p)`;
       `IMAGE (X:A->real) (prob_carrier p)`] SUM_SWAP) THEN
    ASM_REWRITE_TAC[] THEN
    TRY BETA_TAC THEN
    DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    ALL_TAC] THEN
   (* Step 3: Combine RHS into single double sum using SUM_ADD *)
   SUBGOAL_THEN
     `sum (IMAGE (X:A->real) (prob_carrier p))
          (\u. sum (IMAGE (Y:A->real) (prob_carrier p))
                   (\v. u * prob p {x | x IN prob_carrier p /\ X x = u /\ Y x = v})) +
      sum (IMAGE X (prob_carrier p))
          (\u. sum (IMAGE Y (prob_carrier p))
                   (\v. v * prob p {x | x IN prob_carrier p /\ X x = u /\ Y x = v})) =
      sum (IMAGE X (prob_carrier p))
          (\u. sum (IMAGE Y (prob_carrier p))
                   (\v. (u + v) * prob p {x | x IN prob_carrier p /\ X x = u /\ Y x = v}))`
     SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN
    ASM_SIMP_TAC[GSYM SUM_ADD] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    ASM_SIMP_TAC[GSYM SUM_ADD] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `v:real` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ADD_RDISTRIB];
    ALL_TAC] THEN
   (* Step 4: Express E[X+Y] as the same double sum *)
   SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. (X:A->real) x + (Y:A->real) x)` ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `FINITE (IMAGE (\x:A. (X:A->real) x + (Y:A->real) x) (prob_carrier p))` ASSUME_TAC THENL
   [UNDISCH_TAC `simple_rv (p:A prob_space) (\x:A. (X:A->real) x + (Y:A->real) x)` THEN
    REWRITE_TAC[simple_rv] THEN
    SIMP_TAC[GSYM SIMPLE_IMAGE; FINITE_IMAGE];
    ALL_TAC] THEN
   REWRITE_TAC[simple_expectation; SET_IN_SIMP] THEN
   TRY BETA_TAC THEN
   (* Decompose P({X+Y=w}) as sum over X values *)
   SUBGOAL_THEN
     `!w:real. w IN IMAGE (\x:A. (X:A->real) x + (Y:A->real) x) (prob_carrier p)
      ==> prob (p:A prob_space) {x | x IN prob_carrier p /\ X x + Y x = w} =
          sum (IMAGE (X:A->real) (prob_carrier p))
              (\u. prob p {x | x IN prob_carrier p /\ X x = u /\ (Y:A->real) x = w - u})`
     ASSUME_TAC THENL
   [X_GEN_TAC `w:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\ (X:A->real) x + (Y:A->real) x = w} =
       UNIONS (IMAGE (\u. {x | x IN prob_carrier p /\ X x = u /\ Y x = w - u})
                     (IMAGE X (prob_carrier p)))`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `a:A` THEN EQ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM; IN_UNIONS; IN_IMAGE] THEN
      STRIP_TAC THEN
      EXISTS_TAC `{x:A | x IN prob_carrier p /\ (X:A->real) x = X a /\ (Y:A->real) x = w - X a}` THEN
      CONJ_TAC THENL
      [EXISTS_TAC `(X:A->real) a` THEN
       TRY BETA_TAC THEN
       CONJ_TAC THENL [REWRITE_TAC[]; EXISTS_TAC `a:A` THEN ASM_REWRITE_TAC[]];
       REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[IN_UNIONS] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:A->bool` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(s:A->bool) IN IMAGE (\u:real. {x:A | x IN prob_carrier p /\
        (X:A->real) x = u /\ (Y:A->real) x = w - u})
        (IMAGE (X:A->real) (prob_carrier (p:A prob_space)))` THEN
      REWRITE_TAC[IN_IMAGE] THEN
      TRY BETA_TAC THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(a:A) IN s` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
     ALL_TAC] THEN
    MATCH_MP_TAC PROB_FINITE_ADDITIVE_IMAGE THEN
    REPEAT CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     X_GEN_TAC `u:real` THEN DISCH_TAC THEN
     SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ (X:A->real) x = u /\ (Y:A->real) x = w - u} =
                   {x | x IN prob_carrier p /\ X x = u} INTER {x | x IN prob_carrier p /\ Y x = w - u}`
       SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN MESON_TAC[]; ALL_TAC] THEN
     MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN
     ASM_MESON_TAC[simple_rv; RANDOM_VARIABLE_LEVEL_SET];
     X_GEN_TAC `u1:real` THEN X_GEN_TAC `u2:real` THEN STRIP_TAC THEN
     REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_ELIM_THM] THEN
     X_GEN_TAC `a:A` THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
   (* w * P({X+Y=w}) = sum imgX (\u. w * P({X=u,Y=w-u})) *)
   SUBGOAL_THEN
     `sum (IMAGE (\x:A. (X:A->real) x + (Y:A->real) x) (prob_carrier p))
          (\w. w * prob (p:A prob_space) {x | x IN prob_carrier p /\ X x + Y x = w}) =
      sum (IMAGE (\x. X x + Y x) (prob_carrier p))
          (\w. sum (IMAGE (X:A->real) (prob_carrier p))
               (\u. w * prob p {x | x IN prob_carrier p /\ X x = u /\ (Y:A->real) x = w - u}))`
     SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `w:real` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `prob (p:A prob_space) {x:A | x IN prob_carrier p /\ (X:A->real) x + (Y:A->real) x = w} =
                  sum (IMAGE X (prob_carrier p))
                      (\u. prob p {x | x IN prob_carrier p /\ X x = u /\ Y x = w - u})`
      SUBST1_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUM_LMUL];
    ALL_TAC] THEN
   (* Swap sums: sum_w sum_u = sum_u sum_w *)
   SUBGOAL_THEN
     `sum (IMAGE (\x:A. (X:A->real) x + (Y:A->real) x) (prob_carrier p))
          (\w. sum (IMAGE (X:A->real) (prob_carrier p))
               (\u. w * prob (p:A prob_space) {x | x IN prob_carrier p /\ X x = u /\ (Y:A->real) x = w - u})) =
      sum (IMAGE X (prob_carrier p))
          (\u. sum (IMAGE (\x. X x + Y x) (prob_carrier p))
               (\w. w * prob p {x | x IN prob_carrier p /\ X x = u /\ Y x = w - u}))`
     SUBST1_TAC THENL
   [MP_TAC(ISPECL
     [`\(w:real) (u:real). w * prob (p:A prob_space)
         {x:A | x IN prob_carrier p /\ (X:A->real) x = u /\ (Y:A->real) x = w - u}`;
      `IMAGE (\x:A. (X:A->real) x + (Y:A->real) x) (prob_carrier p)`;
      `IMAGE (X:A->real) (prob_carrier p)`] SUM_SWAP) THEN
    ASM_REWRITE_TAC[] THEN
    TRY BETA_TAC THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
   (* Apply INNER_SUM_REINDEX to each inner sum *)
   MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN
   REWRITE_TAC[] THEN
   MATCH_MP_TAC INNER_SUM_REINDEX THEN
   ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* More simple rv operations and expectation properties                      *)
(* ========================================================================= *)

(* Scalar multiplication preserves simple rv property *)
let SIMPLE_RV_CMUL = prove
  (`!p:A prob_space X c.
      simple_rv p X ==> simple_rv p (\x. c * X x)`,
   REPEAT GEN_TAC THEN REWRITE_TAC[simple_rv] THEN STRIP_TAC THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
   SUBGOAL_THEN `(\x:A. c * (X:A->real) x) = (\v:real. c * v) o X`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
   REWRITE_TAC[IMAGE_o] THEN
   MATCH_MP_TAC FINITE_IMAGE THEN
   ASM_REWRITE_TAC[GSYM SIMPLE_IMAGE]);;

(* Negation preserves simple rv property *)
let SIMPLE_RV_NEG = prove
  (`!p:A prob_space X.
      simple_rv p X ==> simple_rv p (\x. --(X x))`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `(\x:A. --((X:A->real) x)) = (\x. (--(&1)) * X x)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC SIMPLE_RV_CMUL THEN ASM_REWRITE_TAC[]);;

(* Subtraction preserves simple rv property *)
let SIMPLE_RV_SUB = prove
  (`!p:A prob_space X Y.
      simple_rv p X /\ simple_rv p Y
      ==> simple_rv p (\x. X x - Y x)`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `(\x:A. (X:A->real) x - (Y:A->real) x) =
                 (\x. X x + (--(&1)) * Y x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC SIMPLE_RV_ADD THEN ASM_SIMP_TAC[SIMPLE_RV_CMUL]);;

(* Absolute value preserves simple rv property *)
let SIMPLE_RV_ABS = prove
  (`!p:A prob_space X.
      simple_rv p X ==> simple_rv p (\x. abs(X x))`,
   REPEAT GEN_TAC THEN REWRITE_TAC[simple_rv] THEN STRIP_TAC THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
   SUBGOAL_THEN `(\x:A. abs((X:A->real) x)) = abs o X` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
   REWRITE_TAC[IMAGE_o] THEN
   MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[GSYM SIMPLE_IMAGE]);;

(* Multiplication preserves simple rv property *)
let SIMPLE_RV_MUL = prove
  (`!p:A prob_space X Y.
      simple_rv p X /\ simple_rv p Y
      ==> simple_rv p (\x. X x * Y x)`,
   REPEAT GEN_TAC THEN REWRITE_TAC[simple_rv] THEN STRIP_TAC THEN
   CONJ_TAC THENL
   [(* Measurability: X*Y = ((X+Y)^2 - X^2 - Y^2) / 2 *)
    SUBGOAL_THEN `(\x:A. (X:A->real) x * (Y:A->real) x) =
                  (\x. inv(&2) * ((X x + Y x) pow 2 - X x pow 2 - Y x pow 2))`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `a:A` THEN
     REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN
    MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN CONJ_TAC THENL
     [MATCH_MP_TAC RANDOM_VARIABLE_SQUARE THEN
      MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RANDOM_VARIABLE_SQUARE THEN ASM_REWRITE_TAC[]];
     MATCH_MP_TAC RANDOM_VARIABLE_SQUARE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   (* Finiteness: IMAGE(X*Y) subset of {a*b | a IN IMAGE(X), b IN IMAGE(Y)} *)
   MP_TAC(ISPECL [`( * ):real->real->real`;
                   `IMAGE (X:A->real) (prob_carrier p)`;
                   `\u:real. IMAGE (Y:A->real) (prob_carrier p)`]
     FINITE_PRODUCT_DEPENDENT) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [ASM_REWRITE_TAC[GSYM SIMPLE_IMAGE; FINITE_IMAGE];
     GEN_TAC THEN DISCH_TAC THEN
     ASM_REWRITE_TAC[GSYM SIMPLE_IMAGE; FINITE_IMAGE]];
    ALL_TAC] THEN
   REWRITE_TAC[] THEN
   DISCH_TAC THEN
   MATCH_MP_TAC FINITE_SUBSET THEN
   FIRST_X_ASSUM(fun th -> EXISTS_TAC(rand(concl th)) THEN
     CONJ_TAC THENL [ACCEPT_TAC th; ALL_TAC]) THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
   X_GEN_TAC `w:real` THEN
   DISCH_THEN(X_CHOOSE_THEN `x:A` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
   MAP_EVERY EXISTS_TAC [`(X:A->real) x`; `(Y:A->real) x`] THEN
   REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]);;

(* Square preserves simple rv property *)
let SIMPLE_RV_SQUARE = prove
  (`!p:A prob_space X.
      simple_rv p X ==> simple_rv p (\x. X x pow 2)`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `(\x:A. (X:A->real) x pow 2) = (\x. X x * X x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; REAL_POW_2]; ALL_TAC] THEN
   MATCH_MP_TAC SIMPLE_RV_MUL THEN ASM_REWRITE_TAC[]);;

(* E[-X] = -E[X] *)
let SIMPLE_EXPECTATION_NEG = prove
  (`!p:A prob_space X.
      simple_rv p X
      ==> simple_expectation p (\x. --(X x)) = --(simple_expectation p X)`,
   REPEAT STRIP_TAC THEN
   MP_TAC(SPECL [`p:A prob_space`; `X:A->real`; `--(&1)`]
     SIMPLE_EXPECTATION_CMUL) THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_LID]);;

(* E[X - Y] = E[X] - E[Y] *)
let SIMPLE_EXPECTATION_SUB = prove
  (`!p:A prob_space X Y.
      simple_rv p X /\ simple_rv p Y
      ==> simple_expectation p (\x. X x - Y x) =
          simple_expectation p X - simple_expectation p Y`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `(\x:A. (X:A->real) x - (Y:A->real) x) =
                 (\x. X x + (--(&1)) * Y x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. (--(&1)) * (Y:A->real) x)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_SIMP_TAC[SIMPLE_EXPECTATION_ADD] THEN
   ASM_SIMP_TAC[SIMPLE_EXPECTATION_CMUL] THEN REAL_ARITH_TAC);;

(* Monotonicity: X <= Y everywhere on carrier ==> E[X] <= E[Y] *)
let SIMPLE_EXPECTATION_MONO = prove
  (`!p:A prob_space X Y.
      simple_rv p X /\ simple_rv p Y /\
      (!x. x IN prob_carrier p ==> X x <= Y x)
      ==> simple_expectation p X <= simple_expectation p Y`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `&0 <= simple_expectation (p:A prob_space)
                        (\x:A. (Y:A->real) x - (X:A->real) x)` MP_TAC THENL
   [MATCH_MP_TAC SIMPLE_EXPECTATION_POS THEN CONJ_TAC THENL
    [MATCH_MP_TAC SIMPLE_RV_SUB THEN ASM_REWRITE_TAC[];
     X_GEN_TAC `a:A` THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `a:A`) THEN ASM_REWRITE_TAC[] THEN
     REAL_ARITH_TAC];
    ALL_TAC] THEN
   ASM_SIMP_TAC[SIMPLE_EXPECTATION_SUB] THEN REAL_ARITH_TAC);;

(* Triangle inequality for simple expectation *)
let SIMPLE_EXPECTATION_ABS_LE = prove
  (`!p:A prob_space X.
      simple_rv p X
      ==> abs(simple_expectation p X) <= simple_expectation p (\x. abs(X x))`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[REAL_ABS_BOUNDS] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `--(simple_expectation (p:A prob_space) (\x:A. abs((X:A->real) x))) <=
                   simple_expectation p X`
      (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. abs((X:A->real) x))` ASSUME_TAC THENL
    [MATCH_MP_TAC SIMPLE_RV_ABS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `--(simple_expectation (p:A prob_space) (\x:A. abs((X:A->real) x))) =
                   simple_expectation p (\x. --(abs(X x)))` SUBST1_TAC THENL
    [CONV_TAC SYM_CONV THEN
     MATCH_MP_TAC SIMPLE_EXPECTATION_NEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
    ASM_SIMP_TAC[SIMPLE_RV_NEG; SIMPLE_RV_ABS] THEN
    X_GEN_TAC `a:A` THEN DISCH_TAC THEN REAL_ARITH_TAC;
    MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
    ASM_SIMP_TAC[SIMPLE_RV_ABS] THEN
    X_GEN_TAC `a:A` THEN DISCH_TAC THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Markov and Chebyshev inequalities for simple random variables             *)
(* ========================================================================= *)

(* Markov's inequality: for non-negative X, P(X >= a) <= E[X] / a *)
let MARKOV_INEQUALITY_SIMPLE = prove
  (`!p:A prob_space X a.
      simple_rv p X /\
      (!x. x IN prob_carrier p ==> &0 <= X x) /\
      &0 < a
      ==> prob p {x | x IN prob_carrier p /\ X x >= a} <=
          simple_expectation p X / a`,
   REPEAT STRIP_TAC THEN
   ABBREV_TAC `S = {x:A | x IN prob_carrier p /\ (X:A->real) x >= a}` THEN
   (* Step 1: S is a measurable event *)
   SUBGOAL_THEN `(S:A->bool) IN prob_events p` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC RANDOM_VARIABLE_GE THEN
    ASM_MESON_TAC[simple_rv]; ALL_TAC] THEN
   (* Step 2: E[a * 1_S] <= E[X] *)
   SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. a * indicator_fn (S:A->bool) x)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_CMUL THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `simple_expectation (p:A prob_space)
                   (\x:A. a * indicator_fn (S:A->bool) x) <=
                 simple_expectation p (X:A->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THENL
    [UNDISCH_TAC `(x:A) IN (S:A->bool)` THEN EXPAND_TAC "S" THEN
     REWRITE_TAC[IN_ELIM_THM] THEN
     DISCH_THEN(MP_TAC o CONJUNCT2) THEN REAL_ARITH_TAC;
     ASM_SIMP_TAC[REAL_MUL_RZERO]]; ALL_TAC] THEN
   (* Step 3: E[a * 1_S] = a * P(S), combine with step 2 *)
   SUBGOAL_THEN `simple_expectation (p:A prob_space) (indicator_fn (S:A->bool)) =
                 prob p S` ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_EXPECTATION_INDICATOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `simple_expectation (p:A prob_space)
                   (\x:A. a * indicator_fn (S:A->bool) x) =
                 a * prob p S` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `indicator_fn (S:A->bool)`; `a:real`]
      SIMPLE_EXPECTATION_CMUL) THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[SIMPLE_RV_INDICATOR] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   (* a * P(S) <= E[X] *)
   SUBGOAL_THEN `a * prob (p:A prob_space) (S:A->bool) <=
                 simple_expectation p (X:A->real)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   (* Step 4: divide by a *)
   ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC);;

(* Cauchy-Schwarz inequality for simple expectations:
   E[XY]^2 <= E[X^2] * E[Y^2]
   Proof: expand E[(X - tY)^2] >= 0 as quadratic in t, optimize *)

let SIMPLE_EXPECTATION_QUADRATIC = prove
 (`!p:A prob_space (X:A->real) (Y:A->real) (t:real).
     simple_rv p X /\ simple_rv p Y
     ==> simple_expectation p (\x. (X x - t * Y x) pow 2) =
         simple_expectation p (\x. X x pow 2) -
         &2 * t * simple_expectation p (\x. X x * Y x) +
         (t pow 2) * simple_expectation p (\x. Y x pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. (X:A->real) x * (Y:A->real) x)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. (X:A->real) x pow 2)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_SQUARE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. (Y:A->real) x pow 2)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_SQUARE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `(\x:A. ((X:A->real) x - (t:real) * (Y:A->real) x) pow 2) =
     (\x. (X x pow 2 + (t pow 2) * Y x pow 2) - (&2 * t) * (X x * Y x))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
   REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space)
    (\x:A. (X:A->real) x pow 2 + ((t:real) pow 2) * (Y:A->real) x pow 2)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_ADD THEN ASM_SIMP_TAC[SIMPLE_RV_CMUL]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space)
    (\x:A. (&2 * (t:real)) * ((X:A->real) x * (Y:A->real) x))`
    ASSUME_TAC THENL
  [ASM_SIMP_TAC[SIMPLE_RV_CMUL]; ALL_TAC] THEN
  MP_TAC(ISPECL
    [`p:A prob_space`;
     `\x:A. (X:A->real) x pow 2 + ((t:real) pow 2) * (Y:A->real) x pow 2`;
     `\x:A. (&2 * (t:real)) * ((X:A->real) x * (Y:A->real) x)`]
    SIMPLE_EXPECTATION_SUB) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL
    [`p:A prob_space`;
     `\x:A. (X:A->real) x pow 2`;
     `\x:A. ((t:real) pow 2) * (Y:A->real) x pow 2`]
    SIMPLE_EXPECTATION_ADD) THEN
  ASM_SIMP_TAC[SIMPLE_RV_CMUL] THEN BETA_TAC THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `\x:A. (X:A->real) x * (Y:A->real) x`;
    `&2 * (t:real)`] SIMPLE_EXPECTATION_CMUL) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `\x:A. (Y:A->real) x pow 2`;
    `(t:real) pow 2`] SIMPLE_EXPECTATION_CMUL) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN
  DISCH_THEN SUBST1_TAC THEN
  REAL_ARITH_TAC);;

let SIMPLE_EXPECTATION_CAUCHY_SCHWARZ = prove
 (`!p:A prob_space (X:A->real) (Y:A->real).
     simple_rv p X /\ simple_rv p Y
     ==> (simple_expectation p (\x. X x * Y x):real) pow 2 <=
         simple_expectation p (\x. X x pow 2) *
         simple_expectation p (\x. Y x pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `exy = simple_expectation (p:A prob_space)
    (\x:A. (X:A->real) x * (Y:A->real) x)` THEN
  ABBREV_TAC `ex2 = simple_expectation (p:A prob_space)
    (\x:A. (X:A->real) x pow 2)` THEN
  ABBREV_TAC `ey2 = simple_expectation (p:A prob_space)
    (\x:A. (Y:A->real) x pow 2)` THEN
  SUBGOAL_THEN `!t:real. &0 <= ex2 - &2 * t * exy + t pow 2 * ey2`
    ASSUME_TAC THENL
  [X_GEN_TAC `t:real` THEN
   SUBGOAL_THEN
     `ex2 - &2 * t * exy + t pow 2 * ey2 =
      simple_expectation (p:A prob_space)
        (\x:A. ((X:A->real) x - t * (Y:A->real) x) pow 2)`
     SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `Y:A->real`; `t:real`]
      SIMPLE_EXPECTATION_QUADRATIC) THEN
    ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "ex2" THEN EXPAND_TAC "exy" THEN EXPAND_TAC "ey2" THEN
    DISCH_THEN ACCEPT_TAC; ALL_TAC] THEN
   MATCH_MP_TAC SIMPLE_EXPECTATION_POS THEN CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_SQUARE THEN MATCH_MP_TAC SIMPLE_RV_SUB THEN
    ASM_SIMP_TAC[SIMPLE_RV_CMUL]; REWRITE_TAC[REAL_LE_POW_2]];
   ALL_TAC] THEN
  ASM_CASES_TAC `ey2 = &0` THENL
  [(* Case ey2 = 0: forces exy = 0 by contradiction *)
   SUBGOAL_THEN `exy = &0` SUBST1_TAC THENL
   [ASM_CASES_TAC `exy = &0` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(&2 * exy = &0)` ASSUME_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= ex2 - &2 * ((ex2 + &1) / (&2 * exy)) * exy +
                  ((ex2 + &1) / (&2 * exy)) pow 2 * ey2` MP_TAC THENL
    [UNDISCH_TAC `!t:real. &0 <= ex2 - &2 * t * exy + t pow 2 * ey2` THEN
     DISCH_THEN(fun th -> ACCEPT_TAC(SPEC `(ex2 + &1) / (&2 * exy)` th));
     ALL_TAC] THEN
    SUBGOAL_THEN `((ex2 + &1) / (&2 * exy)) pow 2 * ey2 = &0`
      SUBST1_TAC THENL
    [ASM_REWRITE_TAC[REAL_MUL_RZERO]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ADD_RID] THEN
    SUBGOAL_THEN `&2 * ((ex2 + &1) / (&2 * exy)) * exy = ex2 + &1`
      SUBST1_TAC THENL
    [REWRITE_TAC[real_div] THEN
     SUBGOAL_THEN
       `&2 * ((ex2 + &1) * inv (&2 * exy)) * exy =
        (ex2 + &1) * (inv (&2 * exy) * (&2 * exy))`
       SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
     ASM_SIMP_TAC[REAL_MUL_LINV] THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Case ey2 > 0: optimize quadratic at t = exy/ey2 *)
  SUBGOAL_THEN `&0 < ey2` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= ey2` MP_TAC THENL
   [EXPAND_TAC "ey2" THEN MATCH_MP_TAC SIMPLE_EXPECTATION_POS THEN
    CONJ_TAC THENL
    [ASM_SIMP_TAC[SIMPLE_RV_SQUARE]; REWRITE_TAC[REAL_LE_POW_2]];
    ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `~(ey2 = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ex2 - &2 * ((exy:real) / ey2) * exy +
                ((exy:real) / ey2) pow 2 * ey2` MP_TAC THENL
  [UNDISCH_TAC `!t:real. &0 <= ex2 - &2 * t * exy + t pow 2 * ey2` THEN
   DISCH_THEN(fun th -> ACCEPT_TAC(SPEC `(exy:real) / ey2` th));
   ALL_TAC] THEN
  SUBGOAL_THEN `ex2 - &2 * ((exy:real) / ey2) * exy +
                ((exy:real) / ey2) pow 2 * ey2 = ex2 - exy pow 2 / ey2`
    SUBST1_TAC THENL
  [UNDISCH_TAC `~(ey2 = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(exy:real) pow 2 / ey2 <= ex2` MP_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ]);;

(* Chebyshev's inequality: P(|X - mu| >= t) <= Var(X) / t^2
   where mu = E[X] and Var(X) = E[(X - mu)^2] *)
(* First define variance for simple rv *)
let simple_variance = new_definition
  `simple_variance (p:A prob_space) (X:A->real) =
   simple_expectation p (\x. (X x - simple_expectation p X) pow 2)`;;

(* Variance is non-negative *)
let SIMPLE_VARIANCE_NONNEG = prove
  (`!p:A prob_space X.
      simple_rv p X ==> &0 <= simple_variance p X`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[simple_variance] THEN
   MATCH_MP_TAC SIMPLE_EXPECTATION_POS THEN CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_SQUARE THEN
    MATCH_MP_TAC SIMPLE_RV_SUB THEN
    ASM_SIMP_TAC[SIMPLE_RV_CONST]; ALL_TAC] THEN
   X_GEN_TAC `a:A` THEN DISCH_TAC THEN REWRITE_TAC[REAL_LE_POW_2]);;

(* Variance formula: Var(X) = E[X^2] - (E[X])^2 *)
let SIMPLE_VARIANCE_ALT = prove
  (`!p:A prob_space X.
      simple_rv p X
      ==> simple_variance p X =
          simple_expectation p (\x. X x pow 2) -
          (simple_expectation p X) pow 2`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[simple_variance; REAL_POW_2] THEN
   (* (X - mu)^2 = X^2 - 2*mu*X + mu^2 *)
   ABBREV_TAC `mu = simple_expectation (p:A prob_space) (X:A->real)` THEN
   SUBGOAL_THEN `(\x:A. ((X:A->real) x - mu) * (X x - mu)) =
                 (\x. X x * X x + (--(&2) * mu) * X x + mu * mu)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `a:A` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. (X:A->real) x * X x)` ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. (--(&2) * mu) * (X:A->real) x)` ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   (* E[X^2 + (-2mu)X + mu^2] = E[X^2] + E[(-2mu)X] + E[mu^2] *)
   SUBGOAL_THEN `(\x:A. (X:A->real) x * X x + (--(&2) * mu) * X x + mu * mu) =
                 (\x. (X x * X x + (--(&2) * mu) * X x) + mu * mu)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. (X:A->real) x * X x + (--(&2) * mu) * X x)` ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_SIMP_TAC[SIMPLE_EXPECTATION_ADD; SIMPLE_RV_CONST] THEN
   ASM_SIMP_TAC[SIMPLE_EXPECTATION_ADD] THEN
   ASM_SIMP_TAC[SIMPLE_EXPECTATION_CMUL] THEN
   SUBGOAL_THEN `simple_expectation (p:A prob_space) (\x:A. mu * mu) = mu * mu` SUBST1_TAC THENL
   [REWRITE_TAC[SIMPLE_EXPECTATION_CONST]; ALL_TAC] THEN
   EXPAND_TAC "mu" THEN REAL_ARITH_TAC);;

(* Chebyshev's inequality *)
let CHEBYSHEV_INEQUALITY_SIMPLE = prove
  (`!p:A prob_space X t.
      simple_rv p X /\ &0 < t
      ==> prob p {x | x IN prob_carrier p /\
                      abs(X x - simple_expectation p X) >= t} <=
          simple_variance p X / t pow 2`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[simple_variance] THEN
   ABBREV_TAC `mu = simple_expectation (p:A prob_space) (X:A->real)` THEN
   (* P(|X-mu| >= t) = P((X-mu)^2 >= t^2), then apply Markov *)
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ abs((X:A->real) x - mu) >= t} =
                 {x | x IN prob_carrier p /\ (X x - mu) pow 2 >= t pow 2}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `a:A` THEN
    ASM_CASES_TAC `(a:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_ge; GSYM REAL_LE_SQUARE_ABS] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`];
    ALL_TAC] THEN
   SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. ((X:A->real) x - mu) pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_SQUARE THEN
    MATCH_MP_TAC SIMPLE_RV_SUB THEN ASM_SIMP_TAC[SIMPLE_RV_CONST]; ALL_TAC] THEN
   (* Use Markov on (X-mu)^2 with threshold t^2 *)
   MATCH_MP_TAC MARKOV_INEQUALITY_SIMPLE THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `a:A` THEN DISCH_TAC THEN REWRITE_TAC[REAL_LE_POW_2];
    ASM_SIMP_TAC[REAL_POW_LT]]);;

(* Variance of constant is zero *)
let SIMPLE_VARIANCE_CONST = prove
  (`!p:A prob_space c. simple_variance p (\x. c) = &0`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC[simple_variance; SIMPLE_EXPECTATION_CONST] THEN
   REAL_ARITH_TAC);;

(* Variance of scaled rv: Var(cX) = c^2 * Var(X) *)
let SIMPLE_VARIANCE_CMUL = prove
  (`!p:A prob_space X c.
      simple_rv p X
      ==> simple_variance p (\x. c * X x) = c pow 2 * simple_variance p X`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[simple_variance] THEN
   ASM_SIMP_TAC[SIMPLE_EXPECTATION_CMUL] THEN
   SUBGOAL_THEN `(\x:A. (c * (X:A->real) x - c * simple_expectation p X) pow 2) =
                 (\x. c pow 2 * (X x - simple_expectation p X) pow 2)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `a:A` THEN
    REWRITE_TAC[REAL_POW_2; REAL_SUB_LDISTRIB] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   MATCH_MP_TAC SIMPLE_EXPECTATION_CMUL THEN
   MATCH_MP_TAC SIMPLE_RV_SQUARE THEN
   MATCH_MP_TAC SIMPLE_RV_SUB THEN
   ASM_SIMP_TAC[SIMPLE_RV_CONST]);;

(* ========================================================================= *)
(* Convergence of random variables                                           *)
(* ========================================================================= *)

(* Convergence in probability: X_n -> L in probability *)
let converges_in_prob = new_definition
  `converges_in_prob (p:A prob_space) (X:num->A->real) (L:A->real) <=>
   !e. &0 < e ==>
     ((\n. prob p {x | x IN prob_carrier p /\ abs(X n x - L x) >= e})
      ---> &0) sequentially`;;

(* Almost sure convergence: X_n -> L a.s. *)
let converges_as = new_definition
  `converges_as (p:A prob_space) (X:num->A->real) (L:A->real) <=>
   prob p {x | x IN prob_carrier p /\
               ((\n. X n x) ---> L x) sequentially} = &1`;;

(* Convergence in probability to a constant *)
let converges_in_prob_const = new_definition
  `converges_in_prob_const (p:A prob_space) (X:num->A->real) (c:real) <=>
   converges_in_prob p X (\x. c)`;;

(* L2 (mean-square) convergence *)
let converges_L2 = new_definition
  `converges_L2 (p:A prob_space) (X:num->A->real) (L:A->real) <=>
   ((\n. simple_expectation p (\x. (X n x - L x) pow 2)) ---> &0) sequentially`;;

(* ========================================================================= *)
(* Chebyshev implies convergence in probability                              *)
(* ========================================================================= *)

(* Key lemma: if Var(X_n) -> 0 and E[X_n] = mu for all n,
   then X_n converges in probability to the constant mu *)
let SIMPLE_CHEBYSHEV_CONVERGENCE = prove
  (`!p:A prob_space X mu.
      (!n. simple_rv p (X n)) /\
      (!n. simple_expectation p (X n) = mu) /\
      ((\n. simple_variance p (X n)) ---> &0) sequentially
      ==> converges_in_prob_const p X mu`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[converges_in_prob_const; converges_in_prob] THEN
   X_GEN_TAC `e:real` THEN DISCH_TAC THEN
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
   UNDISCH_TAC `((\n. simple_variance (p:A prob_space) ((X:num->A->real) n))
     ---> &0) sequentially` THEN
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   DISCH_THEN(MP_TAC o SPEC `eps * (e:real) pow 2`) THEN
   ASM_SIMP_TAC[REAL_LT_MUL; REAL_POW_LT] THEN
   DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
   EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
   ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_TAC THEN
   (* Rewrite set with E[X_n] for Chebyshev *)
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
     abs ((X:num->A->real) n x - mu) >= e} =
     {x | x IN prob_carrier p /\
     abs(X n x - simple_expectation p (X n)) >= e}` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   (* Apply Chebyshev *)
   MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) n`; `e:real`]
     CHEBYSHEV_INEQUALITY_SIMPLE) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   (* Establish random_variable for X n *)
   SUBGOAL_THEN `random_variable (p:A prob_space) ((X:num->A->real) n)`
     ASSUME_TAC THENL
   [SUBGOAL_THEN `simple_rv (p:A prob_space) ((X:num->A->real) n)` MP_TAC THENL
    [ASM_REWRITE_TAC[]; SIMP_TAC[simple_rv]]; ALL_TAC] THEN
   (* Show P >= 0 *)
   SUBGOAL_THEN `&0 <= prob (p:A prob_space)
     {x:A | x IN prob_carrier p /\
      abs ((X:num->A->real) n x - mu) >= e}`
     ASSUME_TAC THENL
   [MATCH_MP_TAC PROB_POSITIVE THEN
    MATCH_MP_TAC RANDOM_VARIABLE_GE THEN
    MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN
    MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN
    ASM_REWRITE_TAC[ETA_AX; RANDOM_VARIABLE_CONST]; ALL_TAC] THEN
   (* Need: abs P < eps from P >= 0 *)
   MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a < b ==> abs a < b`) THEN
   ASM_REWRITE_TAC[] THEN
   (* Need: P < eps via P <= Var/e^2 < eps *)
   MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `simple_variance (p:A prob_space) ((X:num->A->real) n) /
               e pow 2` THEN
   ASM_REWRITE_TAC[] THEN
   (* Need: Var/e^2 < eps, i.e., Var < eps * e^2 *)
   ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_POW_LT] THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= v /\ abs v < e ==> v < e`) THEN
   ASM_SIMP_TAC[SIMPLE_VARIANCE_NONNEG]);;

(* ========================================================================= *)
(* Variance additivity for independent simple random variables               *)
(* ========================================================================= *)

(* Covariance definition for simple rv *)
let simple_covariance = new_definition
  `simple_covariance (p:A prob_space) (X:A->real) (Y:A->real) =
   simple_expectation p (\x. (X x - simple_expectation p X) *
                              (Y x - simple_expectation p Y))`;;

(* Var(X + Y) = Var(X) + Var(Y) + 2*Cov(X,Y) *)
let SIMPLE_VARIANCE_ADD = prove
  (`!p:A prob_space X Y.
      simple_rv p X /\ simple_rv p Y
      ==> simple_variance p (\x. X x + Y x) =
          simple_variance p X + simple_variance p Y +
          &2 * simple_covariance p X Y`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[simple_variance; simple_covariance] THEN
   ASM_SIMP_TAC[SIMPLE_EXPECTATION_ADD] THEN
   ABBREV_TAC `mx = simple_expectation (p:A prob_space) (X:A->real)` THEN
   ABBREV_TAC `my = simple_expectation (p:A prob_space) (Y:A->real)` THEN
   (* Use transitivity: LHS = E[expanded] = RHS *)
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `simple_expectation (p:A prob_space)
     (\x:A. ((X:A->real) x - mx) pow 2 + ((Y:A->real) x - my) pow 2 +
            &2 * (((X:A->real) x - mx) * ((Y:A->real) x - my)))` THEN
   CONJ_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `a:A` THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   (* Establish simple_rv for components *)
   SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. ((X:A->real) x - mx) pow 2)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_SQUARE THEN MATCH_MP_TAC SIMPLE_RV_SUB THEN
    ASM_SIMP_TAC[SIMPLE_RV_CONST]; ALL_TAC] THEN
   SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. ((Y:A->real) x - my) pow 2)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_SQUARE THEN MATCH_MP_TAC SIMPLE_RV_SUB THEN
    ASM_SIMP_TAC[SIMPLE_RV_CONST]; ALL_TAC] THEN
   SUBGOAL_THEN `simple_rv (p:A prob_space)
     (\x:A. ((X:A->real) x - mx) * ((Y:A->real) x - my))` ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_MUL THEN
    CONJ_TAC THEN MATCH_MP_TAC SIMPLE_RV_SUB THEN
    ASM_SIMP_TAC[SIMPLE_RV_CONST]; ALL_TAC] THEN
   SUBGOAL_THEN `simple_rv (p:A prob_space)
     (\x:A. &2 * (((X:A->real) x - mx) * ((Y:A->real) x - my)))` ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `simple_rv (p:A prob_space)
     (\x:A. ((Y:A->real) x - my) pow 2 +
            &2 * (((X:A->real) x - mx) * ((Y:A->real) x - my)))` ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   (* Split E[A + (B + C)] = E[A] + E[B + C] *)
   MP_TAC(ISPECL [`p:A prob_space`;
                   `\x:A. ((X:A->real) x - mx) pow 2`;
                   `\x:A. ((Y:A->real) x - my) pow 2 +
                          &2 * (((X:A->real) x - mx) * ((Y:A->real) x - my))`]
     SIMPLE_EXPECTATION_ADD) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   (* Split E[B + C] = E[B] + E[C] *)
   MP_TAC(ISPECL [`p:A prob_space`;
                   `\x:A. ((Y:A->real) x - my) pow 2`;
                   `\x:A. &2 * (((X:A->real) x - mx) * ((Y:A->real) x - my))`]
     SIMPLE_EXPECTATION_ADD) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   (* Factor E[2*D] = 2*E[D] *)
   MP_TAC(ISPECL [`p:A prob_space`;
                   `\x:A. ((X:A->real) x - mx) * ((Y:A->real) x - my)`;
                   `&2`] SIMPLE_EXPECTATION_CMUL) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   REAL_ARITH_TAC);;

(* Variance of sum for uncorrelated RVs: Var(X+Y) = Var(X) + Var(Y) *)
let SIMPLE_VARIANCE_ADD_UNCORRELATED = prove
  (`!p:A prob_space X Y.
      simple_rv p X /\ simple_rv p Y /\
      simple_covariance p X Y = &0
      ==> simple_variance p (\x. X x + Y x) =
          simple_variance p X + simple_variance p Y`,
   REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SIMPLE_VARIANCE_ADD] THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Weak Law of Large Numbers - Helper Lemmas                                 *)
(* ========================================================================= *)

(* simple_rv is preserved under finite sums *)
let SIMPLE_RV_SUM_NUMSEG = prove
 (`!p:A prob_space (X:num->A->real) n.
     (!i. i <= n ==> simple_rv p (X i))
     ==> simple_rv p (\x. sum(0..n) (\i. X i x))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [SIMP_TAC[SUM_CLAUSES_NUMSEG; LE; ETA_AX] THEN
   DISCH_THEN(MP_TAC o SPEC `0`) THEN REWRITE_TAC[];
   ALL_TAC] THEN
  DISCH_TAC THEN
  SIMP_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
  MATCH_MP_TAC SIMPLE_RV_ADD THEN
  REWRITE_TAC[ETA_AX] THEN
  CONJ_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN
   REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
   FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]);;

(* Linearity of expectation for finite sums *)
let SIMPLE_EXPECTATION_SUM_NUMSEG = prove
 (`!p:A prob_space (X:num->A->real) n.
     (!i. i <= n ==> simple_rv p (X i))
     ==> simple_expectation p (\x. sum(0..n) (\i. X i x)) =
         sum(0..n) (\i. simple_expectation p (X i))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [SIMP_TAC[SUM_CLAUSES_NUMSEG; LE; ETA_AX] THEN
   DISCH_THEN(MP_TAC o SPEC `0`) THEN REWRITE_TAC[];
   ALL_TAC] THEN
  DISCH_TAC THEN
  SIMP_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
  MP_TAC(BETA_RULE(ISPECL [`p:A prob_space`;
                  `\x:A. sum(0..n) (\i. (X:num->A->real) i x)`;
                  `(X:num->A->real) (SUC n)`]
    SIMPLE_EXPECTATION_ADD)) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_SUM_NUMSEG THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC];
   ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* Bilinearity of covariance in first argument *)
let SIMPLE_COVARIANCE_ADD_LEFT = prove
 (`!p:A prob_space X Y Z.
     simple_rv p X /\ simple_rv p Y /\ simple_rv p Z
     ==> simple_covariance p (\x. X x + Y x) Z =
         simple_covariance p X Z + simple_covariance p Y Z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simple_covariance] THEN
  SUBGOAL_THEN `simple_expectation (p:A prob_space) (\x. (X:A->real) x + (Y:A->real) x) =
     simple_expectation p X + simple_expectation p Y` SUBST1_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
    `simple_expectation (p:A prob_space) (\x. ((X:A->real) x - simple_expectation p X) *
     ((Z:A->real) x - simple_expectation p Z) + ((Y:A->real) x - simple_expectation p Y) *
     (Z x - simple_expectation p Z))` THEN
  CONJ_TAC THENL
  [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`p:A prob_space`;
     `\x:A. ((X:A->real) x - simple_expectation p X) * ((Z:A->real) x - simple_expectation p Z)`;
     `\x:A. ((Y:A->real) x - simple_expectation p Y) * ((Z:A->real) x - simple_expectation p Z)`]
    SIMPLE_EXPECTATION_ADD)) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC SIMPLE_RV_MUL THEN CONJ_TAC THEN
   MATCH_MP_TAC SIMPLE_RV_SUB THEN ASM_REWRITE_TAC[SIMPLE_RV_CONST];
   DISCH_THEN(fun th -> REWRITE_TAC[th])]);;

(* Covariance of sum with a single RV *)
let SIMPLE_COVARIANCE_SUM_LEFT = prove
 (`!p:A prob_space (X:num->A->real) Y n.
     (!i. i <= n ==> simple_rv p (X i)) /\ simple_rv p Y
     ==> simple_covariance p (\x. sum(0..n) (\i. X i x)) Y =
         sum(0..n) (\i. simple_covariance p (X i) Y)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [SIMP_TAC[SUM_CLAUSES_NUMSEG; LE; ETA_AX] THEN STRIP_TAC THEN
   SUBGOAL_THEN `simple_rv (p:A prob_space) ((X:num->A->real) 0)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  STRIP_TAC THEN SIMP_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
  MP_TAC(BETA_RULE(ISPECL [`p:A prob_space`;
     `\x:A. sum(0..n) (\i. (X:num->A->real) i x)`;
     `\x:A. (X:num->A->real) (SUC n) x`; `(Y:A->real)`]
    SIMPLE_COVARIANCE_ADD_LEFT)) THEN
  ANTS_TAC THENL
  [REWRITE_TAC[ETA_AX] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_SUM_NUMSEG THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* Variance of sum for pairwise uncorrelated RVs *)
let SIMPLE_VARIANCE_SUM_UNCORRELATED = prove
 (`!p:A prob_space (X:num->A->real) n.
     (!i. i <= n ==> simple_rv p (X i)) /\
     (!i j. i <= n /\ j <= n /\ ~(i = j)
            ==> simple_covariance p (X i) (X j) = &0)
     ==> simple_variance p (\x. sum(0..n) (\i. X i x)) =
         sum(0..n) (\i. simple_variance p (X i))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [SIMP_TAC[SUM_CLAUSES_NUMSEG; LE; ETA_AX] THEN
   STRIP_TAC THEN REWRITE_TAC[ETA_AX];
   ALL_TAC] THEN
  STRIP_TAC THEN
  SIMP_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
  MP_TAC(BETA_RULE(ISPECL
    [`p:A prob_space`;
     `\x:A. sum(0..n) (\i. (X:num->A->real) i x)`;
     `\x:A. (X:num->A->real) (SUC n) x`]
    SIMPLE_VARIANCE_ADD)) THEN
  REWRITE_TAC[ETA_AX] THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_SUM_NUMSEG THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC];
   ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
    `simple_covariance (p:A prob_space)
       (\x. sum(0..n) (\i. (X:num->A->real) i x)) (X (SUC n)) = &0`
    SUBST1_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`;
                   `(X:num->A->real) (SUC n)`; `n:num`]
    SIMPLE_COVARIANCE_SUM_LEFT) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
     FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
   REPEAT STRIP_TAC THEN BETA_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_ARITH_TAC;
   ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
   REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* E[(X/c)^2] = E[X^2] / c^2 for nonzero c *)
let SIMPLE_EXPECTATION_POW2_DIV = prove
 (`!p:A prob_space (X:A->real) (c:real).
     simple_rv p X /\ ~(c = &0)
     ==> simple_expectation p (\x. (X x / c) pow 2) =
         simple_expectation p (\x. X x pow 2) / c pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. (X:A->real) x pow 2)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_SQUARE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `(\x:A. ((X:A->real) x / c) pow 2) = (\x. inv((c:real) pow 2) * (X x pow 2))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
   REWRITE_TAC[real_div; REAL_POW_MUL; REAL_POW_INV] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `\x:A. (X:A->real) x pow 2`;
                  `inv((c:real) pow 2)`] SIMPLE_EXPECTATION_CMUL) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

(* E[sum X_i] = 0 when all E[X_i] = 0 *)
let SIMPLE_EXPECTATION_SUM_ZERO = prove
 (`!p:A prob_space (X:num->A->real) n.
     (!i. i <= n ==> simple_rv p (X i)) /\
     (!i. i <= n ==> simple_expectation p (X i) = &0)
     ==> simple_expectation p (\x. sum(0..n) (\i. X i x)) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`; `n:num`]
    SIMPLE_EXPECTATION_SUM_NUMSEG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Variance of sum for IID: Var(sum X_i) = (n+1)*Var(X_0) *)
let SIMPLE_VARIANCE_SUM_IID = prove
 (`!p:A prob_space (X:num->A->real) n.
     (!i. i <= n ==> simple_rv p (X i)) /\
     (!i j. i <= n /\ j <= n /\ ~(i = j)
            ==> simple_covariance p (X i) (X j) = &0) /\
     (!i. i <= n ==> simple_variance p (X i) = simple_variance p (X 0))
     ==> simple_variance p (\x. sum(0..n) (\i. X i x)) =
         &(SUC n) * simple_variance p (X 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`; `n:num`]
    SIMPLE_VARIANCE_SUM_UNCORRELATED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
    `sum(0..n) (\i. simple_variance (p:A prob_space) ((X:num->A->real) i)) =
     sum(0..n) (\i:num. simple_variance p (X 0))`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SUM_EQ_NUMSEG THEN
   REPEAT STRIP_TAC THEN BETA_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0; GSYM ADD1]);;

(* ------------------------------------------------------------------------- *)
(* Weak Law of Large Numbers (for simple random variables)                   *)
(* ------------------------------------------------------------------------- *)

(* If X_1, X_2, ... are pairwise uncorrelated simple RVs with common   *)
(* mean mu and variance sigma^2, then the sample mean converges in      *)
(* probability to mu.                                                   *)

let WEAK_LAW_OF_LARGE_NUMBERS_SIMPLE = prove
 (`!p:A prob_space (X:num->A->real) mu sigma_sq.
     (!n. simple_rv p (X n)) /\
     (!n. simple_expectation p (X n) = mu) /\
     (!n. simple_variance p (X n) = sigma_sq) /\
     (!i j. ~(i = j) ==> simple_covariance p (X i) (X j) = &0)
     ==> converges_in_prob_const p
           (\n x. inv(&(SUC n)) * sum(0..n) (\i. X i x)) mu`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(BETA_RULE(ISPECL
    [`p:A prob_space`;
     `\n:num. \x:A. inv(&(SUC n)) * sum(0..n) (\i. (X:num->A->real) i x)`;
     `mu:real`] SIMPLE_CHEBYSHEV_CONVERGENCE)) THEN
  REPEAT CONJ_TAC THENL
  [
    (* Goal 1: !n. simple_rv p (\x. inv(SUC n) * sum(0..n) X_i) *)
    GEN_TAC THEN MATCH_MP_TAC SIMPLE_RV_CMUL THEN
    MATCH_MP_TAC SIMPLE_RV_SUM_NUMSEG THEN ASM_REWRITE_TAC[];

    (* Goal 2: !n. E[inv(SUC n) * sum X_i] = mu *)
    GEN_TAC THEN
    MP_TAC(BETA_RULE(ISPECL
      [`p:A prob_space`;
       `\x:A. sum(0..n) (\i. (X:num->A->real) i x)`;
       `inv(&(SUC n))`] SIMPLE_EXPECTATION_CMUL)) THEN
    ANTS_TAC THENL
    [MATCH_MP_TAC SIMPLE_RV_SUM_NUMSEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`; `n:num`]
      SIMPLE_EXPECTATION_SUM_NUMSEG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
      `sum(0..n) (\i. simple_expectation (p:A prob_space) ((X:num->A->real) i)) =
       sum(0..n) (\i:num. mu:real)` SUBST1_TAC THENL
    [MATCH_MP_TAC SUM_EQ_NUMSEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUM_CONST_NUMSEG; ARITH_RULE `(n + 1) - 0 = SUC n`] THEN
    CONV_TAC REAL_FIELD;

    (* Goal 3: (\n. Var(inv(SUC n) * sum X_i)) ---> 0 *)
    SUBGOAL_THEN
      `!n. simple_variance (p:A prob_space)
             (\x. inv(&(SUC n)) * sum(0..n) (\i. (X:num->A->real) i x)) =
           sigma_sq * inv(&(SUC n))`
      (fun th -> REWRITE_TAC[th]) THENL
    [GEN_TAC THEN
     (* Var(c*Z) = c^2 * Var(Z) *)
     MP_TAC(BETA_RULE(ISPECL
       [`p:A prob_space`;
        `\x:A. sum(0..n) (\i. (X:num->A->real) i x)`;
        `inv(&(SUC n))`] SIMPLE_VARIANCE_CMUL)) THEN
     ANTS_TAC THENL
     [MATCH_MP_TAC SIMPLE_RV_SUM_NUMSEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     DISCH_THEN SUBST1_TAC THEN
     (* Var(sum X_i) = sum Var(X_i) for pairwise uncorrelated *)
     MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`; `n:num`]
       SIMPLE_VARIANCE_SUM_UNCORRELATED) THEN
     ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
     DISCH_THEN SUBST1_TAC THEN
     SUBGOAL_THEN
       `sum(0..n) (\i. simple_variance (p:A prob_space) ((X:num->A->real) i)) =
        sum(0..n) (\i:num. sigma_sq:real)` SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     REWRITE_TAC[SUM_CONST_NUMSEG; ARITH_RULE `(n + 1) - 0 = SUC n`] THEN
     (* inv(&(SUC n)) pow 2 * &(SUC n) * sigma_sq = sigma_sq * inv(&(SUC n)) *)
     CONV_TAC REAL_FIELD;
     ALL_TAC] THEN
    (* (\n. sigma_sq * inv(&(SUC n))) ---> 0 *)
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
    MATCH_MP_TAC REALLIM_NULL_LMUL THEN
    REWRITE_TAC[REALLIM_1_OVER_N_OFFSET]]);;

(* ========================================================================= *)
(* STRONG LAW OF LARGE NUMBERS - Auxiliary lemmas                            *)
(* ========================================================================= *)

(* Integer square root existence *)
let NUM_SQRT_EXISTS = prove
 (`!n. ?k. k * k <= n /\ n < (k + 1) * (k + 1)`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `n = 0` THENL
  [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `n < (k + 1) * (k + 1)` THENL
  [EXISTS_TAC `k:num` THEN CONJ_TAC THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
   EXISTS_TAC `k + 1` THEN
   SUBGOAL_THEN `n:num = (k + 1) * (k + 1)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[LE_REFL] THEN MATCH_MP_TAC LT_MULT2 THEN ARITH_TAC]);;

(* Summability of 1/SUC(k*k) - needed for Borel-Cantelli in SLLN *)
let SUMMABLE_INV_SUC_SQUARES = prove
 (`real_summable (from 0) (\k. inv(&(SUC(k * k))))`,
  MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
  EXISTS_TAC `\k:num. inv(&k pow 2)` THEN
  CONJ_TAC THENL
  [MP_TAC(SPECL [`0`; `2`] REAL_SUMMABLE_ZETA_INTEGER) THEN
   REWRITE_TAC[ARITH_RULE `2 <= 2 <=> T`];
   EXISTS_TAC `1` THEN X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_FROM] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `abs(inv(&(SUC(k * k)))) = inv(&(SUC(k * k)))` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NUM]; ALL_TAC] THEN
   SUBGOAL_THEN `inv(&k pow 2) = inv(&(k * k))` SUBST1_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[REAL_POW_2; REAL_OF_NUM_MUL]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_INV2 THEN
   REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
   CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `0 < x <=> ~(x = 0)`; MULT_EQ_0] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `x <= SUC x`]]]);;

(* Convergence along k^2 + bounded gaps implies full convergence *)
let REALLIM_SUBSEQUENCE_SQUARES = prove
 (`!f c g.
     ((\k. f(k * k)) ---> c) sequentially /\
     (!k n. k * k <= n /\ n <= (k + 1) * (k + 1) ==> abs(f n - f(k * k)) <= g k) /\
     (g ---> &0) sequentially
     ==> (f ---> c) sequentially`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `K2:num` (LABEL_TAC "Hg")) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `K1:num` (LABEL_TAC "Hf")) THEN
  EXISTS_TAC `((K1:num) + K2) * (K1 + K2)` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MP_TAC(SPEC `n:num` NUM_SQRT_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(K1:num) + K2 <= k` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
   SUBGOAL_THEN `(k + 1) * (k + 1) <= ((K1:num) + K2) * (K1 + K2)` MP_TAC THENL
   [MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `abs(f(n:num) - f(k * k)) <= (g:num->real) k` MP_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs((g:num->real) k) < e / &2` MP_TAC THENL
  [REMOVE_THEN "Hg" (MP_TAC o SPEC `k:num`) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC];
   ALL_TAC] THEN
  USE_THEN "Hf" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  BETA_TAC THEN
  REAL_ARITH_TAC);;

(* BCL1 => almost sure convergence bridge lemma *)
let BCL1_CONVERGENCE = prove
 (`!p:A prob_space (Y:num->A->real) c.
     (!n. simple_rv p (Y n)) /\
     (!eps. &0 < eps ==>
        real_summable (from 0) (\n. prob p {x | x IN prob_carrier p /\ abs(Y n x - c) >= eps}))
     ==> almost_surely p {x | ((\n. Y n x) ---> c) sequentially}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[almost_surely] THEN
  EXISTS_TAC `UNIONS {limsup_events
    (\n. {x:A | x IN prob_carrier p /\ abs((Y:num->A->real) n x - c) >= inv(&(SUC k))})
    | k IN (:num)}` THEN
  SUBGOAL_THEN
    `!k n. {x:A | x IN prob_carrier p /\ abs((Y:num->A->real) n x - c) >= inv(&(SUC k))}
           IN prob_events p`
    (LABEL_TAC "Hev") THENL
  [REPEAT GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_GE THEN
   MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN
   MATCH_MP_TAC RANDOM_VARIABLE_SUB_CONST THEN
   REWRITE_TAC[ETA_AX] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
   SIMP_TAC[simple_rv];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC NULL_EVENT_COUNTABLE_UNION THEN
   X_GEN_TAC `k:num` THEN
   REWRITE_TAC[null_event] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LIMSUP_EVENTS_IN_EVENTS THEN
    GEN_TAC THEN USE_THEN "Hev" (MP_TAC o SPECL [`k:num`; `n:num`]) THEN
    REWRITE_TAC[];
    MP_TAC(ISPECL
      [`p:A prob_space`;
       `\n. {x:A | x IN prob_carrier p /\ abs((Y:num->A->real) n x - c) >= inv(&(SUC k))}`]
      FIRST_BOREL_CANTELLI) THEN
    TRY BETA_TAC THEN
    DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
    [GEN_TAC THEN USE_THEN "Hev" (MP_TAC o SPECL [`k:num`; `n:num`]) THEN
     REWRITE_TAC[];
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     MATCH_MP_TAC REAL_LT_INV THEN
     REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC]];
   REWRITE_TAC[SUBSET] THEN
   X_GEN_TAC `x:A` THEN
   REWRITE_TAC[IN_ELIM_THM] THEN
   STRIP_TAC THEN
   REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
   FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[REALLIM_SEQUENTIALLY]) THEN
   TRY BETA_TAC THEN
   REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM;
               NOT_FORALL_THM; NOT_IMP; REAL_NOT_LT] THEN
   DISCH_THEN(X_CHOOSE_THEN `eps:real` STRIP_ASSUME_TAC) THEN
   MP_TAC(fst(EQ_IMP_RULE(SPEC `eps:real` REAL_ARCH_INV))) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `?kk:num. m = SUC kk`
     (X_CHOOSE_THEN `kk:num` SUBST_ALL_TAC) THENL
   [MP_TAC(SPEC `m:num` num_CASES) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   EXISTS_TAC `limsup_events
     (\n. {x:A | x IN prob_carrier p /\ abs((Y:num->A->real) n x - c) >= inv(&(SUC kk))})` THEN
   CONJ_TAC THENL
   [EXISTS_TAC `kk:num` THEN REFL_TAC;
    REWRITE_TAC[LIMSUP_EVENTS_ALT; IN_ELIM_THM] THEN
    TRY BETA_TAC THEN
    REWRITE_TAC[IN_ELIM_THM; GE] THEN
    X_GEN_TAC `N:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
    DISCH_THEN(X_CHOOSE_THEN `nn:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `nn:num` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_ge] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `eps:real` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[]]]]);;


(* Subsequence SLLN: sample means along k^2 converge a.s. *)
let SIMPLE_SLLN_SUBSEQ = prove
 (`!p:A prob_space (X:num->A->real) mu sigma_sq.
    (!n. simple_rv p (X n)) /\
    (!n. simple_expectation p (X n) = mu) /\
    (!n. simple_variance p (X n) = sigma_sq) /\
    (!i j. ~(i = j) ==> simple_covariance p (X i) (X j) = &0)
    ==> almost_surely p
          {x | ((\k. inv(&(SUC(k * k))) * sum(0..k * k) (\i. X i x)) ---> mu) sequentially}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC BCL1_CONVERGENCE THEN
  TRY BETA_TAC THEN
  CONJ_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC SIMPLE_RV_CMUL THEN
   MATCH_MP_TAC SIMPLE_RV_SUM_NUMSEG THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
  EXISTS_TAC `\k:num. sigma_sq / eps pow 2 * inv(&(SUC(k * k)))` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_SUMMABLE_LMUL THEN
   REWRITE_TAC[SUMMABLE_INV_SUC_SQUARES];
   ALL_TAC] THEN
  EXISTS_TAC `0` THEN X_GEN_TAC `k:num` THEN
  REWRITE_TAC[GE; LE_0; IN_FROM] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC PROB_POSITIVE THEN
   MATCH_MP_TAC RANDOM_VARIABLE_GE THEN
   MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN
   MATCH_MP_TAC RANDOM_VARIABLE_SUB_CONST THEN
   SUBGOAL_THEN `simple_rv (p:A prob_space)
     (\x. inv(&(SUC(k * k))) * sum(0..k * k) (\i. (X:num->A->real) i x))`
     MP_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_CMUL THEN
    MATCH_MP_TAC SIMPLE_RV_SUM_NUMSEG THEN ASM_REWRITE_TAC[];
    MESON_TAC[simple_rv]];
   ALL_TAC] THEN
  SUBGOAL_THEN `simple_expectation (p:A prob_space)
    (\x. inv(&(SUC(k * k))) * sum(0..k * k) (\i. (X:num->A->real) i x)) = mu`
    (LABEL_TAC "exp_eq") THENL
  [MP_TAC(BETA_RULE(ISPECL [`p:A prob_space`;
     `\x:A. sum(0..k * k) (\i. (X:num->A->real) i x)`;
     `inv(&(SUC(k * k)))`] SIMPLE_EXPECTATION_CMUL)) THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_SUM_NUMSEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`; `k * k:num`]
     SIMPLE_EXPECTATION_SUM_NUMSEG) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   SUBGOAL_THEN
     `sum(0..k * k) (\i. simple_expectation (p:A prob_space) ((X:num->A->real) i)) =
      sum(0..k * k) (\i:num. mu:real)` SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUM_CONST_NUMSEG; ARITH_RULE `(n + 1) - 0 = SUC n`] THEN
    CONV_TAC REAL_FIELD];
   ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
    [`p:A prob_space`;
     `\x:A. inv(&(SUC(k * k))) * sum(0..k * k) (\i. (X:num->A->real) i x)`;
     `eps:real`]
    CHEBYSHEV_INEQUALITY_SIMPLE)) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_CMUL THEN
    MATCH_MP_TAC SIMPLE_RV_SUM_NUMSEG THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  USE_THEN "exp_eq" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `simple_variance (p:A prob_space)
    (\x. inv(&(SUC(k * k))) * sum(0..k * k) (\i. (X:num->A->real) i x)) /
    eps pow 2` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_variance (p:A prob_space)
    (\x. inv(&(SUC(k * k))) * sum(0..k * k) (\i. (X:num->A->real) i x)) =
    sigma_sq * inv(&(SUC(k * k)))` SUBST1_TAC THENL
  [MP_TAC(BETA_RULE(ISPECL
    [`p:A prob_space`;
     `\x:A. sum(0..k * k) (\i. (X:num->A->real) i x)`;
     `inv(&(SUC(k * k)))`] SIMPLE_VARIANCE_CMUL)) THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_SUM_NUMSEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`; `k * k:num`]
     SIMPLE_VARIANCE_SUM_UNCORRELATED) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   SUBGOAL_THEN
     `sum(0..k * k) (\i. simple_variance (p:A prob_space) ((X:num->A->real) i)) =
      sum(0..k * k) (\i:num. sigma_sq:real)` SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[SUM_CONST_NUMSEG; ARITH_RULE `(n + 1) - 0 = SUC n`] THEN
   CONV_TAC REAL_FIELD;
   ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= b`) THEN
  REWRITE_TAC[real_div; REAL_MUL_AC]);;

(* ALMOST_SURELY_SUBSET: if P holds a.s. and P => Q on the carrier, then Q holds a.s. *)
let ALMOST_SURELY_SUBSET = prove
 (`!p:A prob_space P Q.
    almost_surely p P /\
    (!x. x IN prob_carrier p ==> x IN P ==> x IN Q)
    ==> almost_surely p Q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[almost_surely] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `n:A->bool` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  EXISTS_TAC `n:A->bool` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* Interpolation bound for sample means of bounded sequences *)
let SAMPLE_MEAN_INTERPOLATION = prove
 (`!f:num->real M k n.
    &0 <= M /\
    (!i. abs(f i) <= M) /\ k * k <= n /\ n <= (k + 1) * (k + 1)
    ==> abs(inv(&(SUC n)) * sum(0..n) f -
            inv(&(SUC(k * k))) * sum(0..k * k) f)
        <= &2 * M * &(2 * k + 1) * inv(&(SUC(k * k)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `sum(0..n) f = sum(0..k * k) f + sum(k * k + 1..n) f`
    SUBST1_TAC THENL
  [SUBGOAL_THEN `n = k * k + (n - k * k):num` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC SUM_ADD_SPLIT THEN ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `inv(&(SUC n)) * (sum(0..k * k) f + sum(k * k + 1..n) f) -
     inv(&(SUC(k * k))) * sum(0..k * k) f =
     inv(&(SUC n)) * sum(k * k + 1..n) f +
     (inv(&(SUC n)) - inv(&(SUC(k * k)))) * sum(0..k * k) f`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(inv(&(SUC n)) * sum(k * k + 1..n) f) +
              abs((inv(&(SUC n)) - inv(&(SUC(k * k)))) * sum(0..k * k) f)` THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_ABS_TRIANGLE]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  SUBGOAL_THEN `~(&(SUC n) = &0)` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(&(SUC(k * k)) = &0)` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &(SUC n)` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &(SUC(k * k))` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv(&(SUC n)) <= inv(&(SUC(k * k)))` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_INV2 THEN
   ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(inv(&(SUC n))) = inv(&(SUC n))` SUBST1_TAC THENL
  [REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC REAL_LE_INV THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(inv(&(SUC n)) - inv(&(SUC(k * k)))) =
    inv(&(SUC(k * k))) - inv(&(SUC n))` SUBST1_TAC THENL
  [MATCH_MP_TAC(REAL_ARITH `x <= y ==> abs(x - y) = y - x`) THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(sum(k * k + 1..n) f) <= &(n - k * k) * M`
    ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `sum(k * k + 1..n) (\i:num. M:real)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SUM_CONST_NUMSEG] THEN
    SUBGOAL_THEN `(n + 1) - (k * k + 1) = n - k * k` SUBST1_TAC THENL
    [ASM_ARITH_TAC; REAL_ARITH_TAC]];
   ALL_TAC] THEN
  SUBGOAL_THEN `abs(sum(0..k * k) f) <= &(SUC(k * k)) * M`
    ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `sum(0..k * k) (\i:num. M:real)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SUM_CONST_NUMSEG; ARITH_RULE `(n + 1) - 0 = SUC n`] THEN
    REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `inv(&(SUC n)) * abs(sum(k * k + 1..n) f) <=
     &(n - k * k) * M * inv(&(SUC(k * k)))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `inv(&(SUC(k * k))) * (&(n - k * k) * M)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
     ASM_REWRITE_TAC[];
     REWRITE_TAC[REAL_ABS_POS];
     ASM_REWRITE_TAC[]];
    MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= y`) THEN
    REWRITE_TAC[REAL_MUL_AC]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `(inv(&(SUC(k * k))) - inv(&(SUC n))) * abs(sum(0..k * k) f) <=
     &(n - k * k) * M * inv(&(SUC(k * k)))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `(inv(&(SUC(k * k))) - inv(&(SUC n))) * (&(SUC(k * k)) * M)` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    SUBGOAL_THEN
      `(inv(&(SUC(k * k))) - inv(&(SUC n))) * (&(SUC(k * k)) * M) =
       (&(SUC n) - &(SUC(k * k))) * inv(&(SUC n)) * M` SUBST1_TAC THENL
    [MATCH_MP_TAC(REAL_FIELD
      `~(a = &0) /\ ~(b = &0) ==>
       (inv(a) - inv(b)) * (a * M) = (b - a) * inv(b) * M`) THEN
     ASM_REWRITE_TAC[];
     SUBGOAL_THEN `&(SUC n) - &(SUC(k * k)) = &(n - k * k)` SUBST1_TAC THENL
     [SUBGOAL_THEN `&(n - k * k) = &n - &(k * k):real` MP_TAC THENL
      [ASM_SIMP_TAC[REAL_OF_NUM_SUB];
       REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC];
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
      [REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
       GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
       MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]]]]];
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(n - k * k) * M * inv(&(SUC(k * k))) +
              &(n - k * k) * M * inv(&(SUC(k * k)))` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[];
   SUBGOAL_THEN
     `&(n - k * k) * M * inv(&(SUC(k * k))) +
      &(n - k * k) * M * inv(&(SUC(k * k))) =
      (&2 * &(n - k * k)) * (M * inv(&(SUC(k * k))))` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
     `&2 * M * &(2 * k + 1) * inv(&(SUC(k * k))) =
      (&2 * &(2 * k + 1)) * (M * inv(&(SUC(k * k))))` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [REAL_ARITH_TAC;
     REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC]]]);;

(* Cross-multiplication bound: (2k+1)(k+1) <= 3(k^2+1) *)
let CROSS_MULT_BOUND = prove
 (`!k. (2 * k + 1) * SUC k <= 3 * SUC(k * k)`,
  GEN_TAC THEN
  REWRITE_TAC[ADD1; LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN
  ASM_CASES_TAC `k = 0` THENL
  [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `k = 1` THENL
  [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `k = 2` THENL
  [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `3 <= k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `3 * k <= k * k` ASSUME_TAC THENL
  [MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_ARITH_TAC);;

(* Cross-multiplication for inverse inequalities *)
let REAL_LE_INV_CROSS = prove
 (`!a b c d:real. &0 < b /\ &0 < d /\ a * b <= c * d
   ==> a * inv d <= c * inv b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `(c:real) / b * d = (c * d) / b` SUBST1_TAC THENL
  [REWRITE_TAC[real_div] THEN REWRITE_TAC[REAL_MUL_AC]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  ASM_REWRITE_TAC[]);;

(* Gap bound for sample mean interpolation converges to 0 *)
let GAP_LIMIT = prove
 (`!M. &0 <= M ==>
   ((\k. &2 * M * &(2 * k + 1) * inv(&(SUC(k * k)))) ---> &0) sequentially`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\k. &2 * M * &3 * inv(&(SUC k))` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
   X_GEN_TAC `k:num` THEN DISCH_TAC THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
    [REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
      [REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
       MATCH_MP_TAC REAL_LE_INV THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC]]];
    ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     MATCH_MP_TAC REAL_LE_INV_CROSS THEN
     REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
     REWRITE_TAC[ARITH_RULE `0 < SUC n`; CROSS_MULT_BOUND]]];
   ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  MATCH_MP_TAC REALLIM_NULL_LMUL THEN
  MATCH_MP_TAC REALLIM_NULL_LMUL THEN
  MATCH_MP_TAC REALLIM_NULL_LMUL THEN
  REWRITE_TAC[REALLIM_1_OVER_N_OFFSET]);;

(* ========================================================================= *)
(* STRONG LAW OF LARGE NUMBERS                                               *)
(* For bounded, pairwise uncorrelated simple random variables                *)
(* ========================================================================= *)

let STRONG_LAW_OF_LARGE_NUMBERS_SIMPLE = prove
 (`!p:A prob_space (X:num->A->real) mu sigma_sq M.
    (!n. simple_rv p (X n)) /\
    (!n. simple_expectation p (X n) = mu) /\
    (!n. simple_variance p (X n) = sigma_sq) /\
    (!i j. ~(i = j) ==> simple_covariance p (X i) (X j) = &0) /\
    (!n x. x IN prob_carrier p ==> abs(X n x) <= M)
    ==> almost_surely p
          {x | ((\n. inv(&(SUC n)) * sum(0..n) (\i. X i x)) ---> mu) sequentially}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Step 1: Reduce to subsequence convergence via ALMOST_SURELY_SUBSET *)
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC
    `{x:A | ((\k. inv(&(SUC(k * k))) * sum(0..k * k) (\i. X i x)) ---> mu) sequentially}` THEN
  CONJ_TAC THENL
  [(* Subsequence converges a.s. by Chebyshev + Borel-Cantelli *)
   MATCH_MP_TAC SIMPLE_SLLN_SUBSEQ THEN EXISTS_TAC `sigma_sq:real` THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 2: Show subseq convergence implies full convergence pointwise *)
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `abs((X:num->A->real) 0 x)` THEN
   CONJ_TAC THENL [REAL_ARITH_TAC; ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `!i:num. abs((X:num->A->real) i x) <= M` ASSUME_TAC THENL
  [ASM_SIMP_TAC[]; ALL_TAC] THEN
  (* Step 3: Apply subsequence interpolation *)
  MATCH_MP_TAC REALLIM_SUBSEQUENCE_SQUARES THEN
  EXISTS_TAC `\k. &2 * M * &(2 * k + 1) * inv(&(SUC(k * k)))` THEN
  TRY BETA_TAC THEN
  CONJ_TAC THENL
  [FIRST_ASSUM ACCEPT_TAC;
   ALL_TAC] THEN
  CONJ_TAC THENL
  [REPEAT GEN_TAC THEN STRIP_TAC THEN
   MATCH_MP_TAC SAMPLE_MEAN_INTERPOLATION THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MATCH_MP_TAC GAP_LIMIT THEN ASM_REWRITE_TAC[]);;


(* ========================================================================= *)
(* Part 2: General Lebesgue Integration for Probability Spaces               *)
(* (Williams Chapters 5-6)                                                   *)
(* ========================================================================= *)

(* Standard dyadic approximation of a nonneg measurable function.
   For nonneg f, this gives the largest k/2^n <= f(x) with k <= n*2^n.
   The approximation is increasing in n, bounded by f, and converges to f. *)
let nonneg_simple_fn_approx = new_definition
  `nonneg_simple_fn_approx (p:A prob_space) (f:A->real) (n:num) (x:A) =
   if x IN prob_carrier p /\ &0 <= f x
   then sup (IMAGE (\k. &k / &(2 EXP n))
                    {k | k <= n * 2 EXP n /\ &k / &(2 EXP n) <= f x})
   else &0`;;

(* The index set is always finite *)
let NONNEG_APPROX_INDEX_FINITE = prove
 (`!n:num (f:A->real) (x:A). FINITE {k | k <= n * 2 EXP n /\ &k / &(2 EXP n) <= f x}`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{k | k <= n * 2 EXP n}` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[FINITE_NUMSEG_LE]; SET_TAC[]]);;

(* The image set is always finite *)
let NONNEG_APPROX_SET_FINITE = prove
 (`!n:num (f:A->real) (x:A). FINITE (IMAGE (\k. &k / &(2 EXP n))
                              {k | k <= n * 2 EXP n /\ &k / &(2 EXP n) <= f x})`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC FINITE_IMAGE THEN
  REWRITE_TAC[NONNEG_APPROX_INDEX_FINITE]);;

(* When f(x) >= 0, the index set is nonempty (contains 0) *)
let NONNEG_APPROX_INDEX_NONEMPTY = prove
 (`!n:num (f:A->real) (x:A). &0 <= f x ==> 0 IN {k | k <= n * 2 EXP n /\ &k / &(2 EXP n) <= f x}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC);;

(* When f(x) >= 0, the image set is nonempty *)
let NONNEG_APPROX_SET_NONEMPTY = prove
 (`!n:num (f:A->real) (x:A). &0 <= f x
   ==> ~(IMAGE (\k. &k / &(2 EXP n))
               {k | k <= n * 2 EXP n /\ &k / &(2 EXP n) <= f x} = {})`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`n:num`; `f:A->real`; `x:A`] NONNEG_APPROX_INDEX_NONEMPTY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 / &(2 EXP n) IN IMAGE (\k. &k / &(2 EXP n))
                {k | k <= n * 2 EXP n /\ &k / &(2 EXP n) <= f (x:A)}` MP_TAC THENL
  [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `0` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY]);;

(* Helper tactic pattern: extract SUP_FINITE facts for our approx sets *)
(* After applying SUP_FINITE, the sup is IN the image set and is an upper bound *)

(* The approx is nonneg *)
let NONNEG_SIMPLE_FN_APPROX_NONNEG = prove
 (`!p:A prob_space f n x.
     &0 <= nonneg_simple_fn_approx p f n x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[nonneg_simple_fn_approx] THEN
  COND_CASES_TAC THENL
  [ALL_TAC; REAL_ARITH_TAC] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN DISCH_TAC THEN
  MP_TAC (SPECL [`n:num`; `f:A->real`; `x:A`] NONNEG_APPROX_SET_FINITE) THEN
  MP_TAC (SPECL [`n:num`; `f:A->real`; `x:A`] NONNEG_APPROX_SET_NONEMPTY) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC (SPEC `IMAGE (\k. &k / &(2 EXP n))
                {k | k <= n * 2 EXP n /\ &k / &(2 EXP n) <= f (x:A)}`
               SUP_FINITE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `sup (IMAGE (\k. &k / &(2 EXP n))
      {k | k <= n * 2 EXP n /\ &k / &(2 EXP n) <= f (x:A)}) IN
      IMAGE (\k. &k / &(2 EXP n))
      {k | k <= n * 2 EXP n /\ &k / &(2 EXP n) <= f x}` THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[REAL_LE_DIV; REAL_POS]);;

(* The approx is <= f(x) on the carrier *)
let NONNEG_SIMPLE_FN_APPROX_LE = prove
 (`!p:A prob_space f n x.
     x IN prob_carrier p /\ &0 <= f x
     ==> nonneg_simple_fn_approx p f n x <= f x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[nonneg_simple_fn_approx] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC (SPECL [`n:num`; `f:A->real`; `x:A`] NONNEG_APPROX_SET_FINITE) THEN
  MP_TAC (SPECL [`n:num`; `f:A->real`; `x:A`] NONNEG_APPROX_SET_NONEMPTY) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC (SPEC `IMAGE (\k. &k / &(2 EXP n))
                {k | k <= n * 2 EXP n /\ &k / &(2 EXP n) <= f (x:A)}`
               SUP_FINITE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `sup (IMAGE (\k. &k / &(2 EXP n))
      {k | k <= n * 2 EXP n /\ &k / &(2 EXP n) <= f (x:A)}) IN
      IMAGE (\k. &k / &(2 EXP n))
      {k | k <= n * 2 EXP n /\ &k / &(2 EXP n) <= f x}` THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* On carrier with f >= 0, the approx value is some k/2^n from the grid *)
let NONNEG_SIMPLE_FN_APPROX_IN_GRID = prove
 (`!p:A prob_space f n x.
    x IN prob_carrier p /\ &0 <= f x
    ==> ?k. k <= n * 2 EXP n /\
            nonneg_simple_fn_approx p f n x = &k / &(2 EXP n)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[nonneg_simple_fn_approx] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC (SPECL [`n:num`; `f:A->real`; `x:A`] NONNEG_APPROX_SET_FINITE) THEN
  MP_TAC (SPECL [`n:num`; `f:A->real`; `x:A`] NONNEG_APPROX_SET_NONEMPTY) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC (SPEC `IMAGE (\k. &k / &(2 EXP n))
                {k | k <= n * 2 EXP n /\ &k / &(2 EXP n) <= f (x:A)}`
               SUP_FINITE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `sup (IMAGE (\k. &k / &(2 EXP n))
      {k | k <= n * 2 EXP n /\ &k / &(2 EXP n) <= f (x:A)}) IN
      IMAGE (\k. &k / &(2 EXP n))
      {k | k <= n * 2 EXP n /\ &k / &(2 EXP n) <= f x}` THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[]);;

(* The approx function is a random variable *)
let NONNEG_SIMPLE_FN_APPROX_RV = prove
 (`!p:A prob_space f n.
    random_variable p f /\ (!x. x IN prob_carrier p ==> &0 <= f x)
    ==> random_variable p (nonneg_simple_fn_approx p f n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[random_variable] THEN
  X_GEN_TAC `a:real` THEN
  ASM_CASES_TAC `a < &0` THENL
  [SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ nonneg_simple_fn_approx p f n x <= a} = {}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`p:A prob_space`; `f:A->real`; `n:num`; `z:A`]
      NONNEG_SIMPLE_FN_APPROX_NONNEG) THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[PROB_EMPTY_IN_EVENTS]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ nonneg_simple_fn_approx p f n x <= a} =
     {x | x IN prob_carrier p /\
          !j. j <= n * 2 EXP n /\ ~(&j / &(2 EXP n) <= a)
              ==> f x < &j / &(2 EXP n)}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
   X_GEN_TAC `z:A` THEN
   ASM_CASES_TAC `(z:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
   EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(f:A->real) z < &j / &(2 EXP n)` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= (f:A->real) z` ASSUME_TAC THENL
      [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&j / &(2 EXP n) <= nonneg_simple_fn_approx p (f:A->real) n z`
      MP_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    REWRITE_TAC[nonneg_simple_fn_approx] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC (SPECL [`n:num`; `f:A->real`; `z:A`] NONNEG_APPROX_SET_FINITE) THEN
    MP_TAC (SPECL [`n:num`; `f:A->real`; `z:A`] NONNEG_APPROX_SET_NONEMPTY) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    MP_TAC (SPEC `IMAGE (\k. &k / &(2 EXP n))
                  {k | k <= n * 2 EXP n /\ &k / &(2 EXP n) <= f (z:A)}`
                 SUP_FINITE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[GSYM REAL_NOT_LT];
    DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (f:A->real) z` ASSUME_TAC THENL
      [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[nonneg_simple_fn_approx] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC (SPECL [`n:num`; `f:A->real`; `z:A`] NONNEG_APPROX_SET_FINITE) THEN
    MP_TAC (SPECL [`n:num`; `f:A->real`; `z:A`] NONNEG_APPROX_SET_NONEMPTY) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    MP_TAC (SPEC `IMAGE (\k. &k / &(2 EXP n))
                  {k | k <= n * 2 EXP n /\ &k / &(2 EXP n) <= f (z:A)}`
                 SUP_FINITE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `sup (IMAGE (\k. &k / &(2 EXP n))
        {k | k <= n * 2 EXP n /\ &k / &(2 EXP n) <= f (z:A)}) IN
        IMAGE (\k. &k / &(2 EXP n))
        {k | k <= n * 2 EXP n /\ &k / &(2 EXP n) <= f z}` THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `&m / &(2 EXP n) <= a` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\
            (!j. j <= n * 2 EXP n /\ ~(&j / &(2 EXP n) <= a)
                 ==> f x < &j / &(2 EXP n))} =
     prob_carrier p INTER
     INTERS (IMAGE (\j. {x | x IN prob_carrier p /\ f x < &j / &(2 EXP n)})
                   {j | j <= n * 2 EXP n /\ ~(&j / &(2 EXP n) <= a)})`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION] THEN GEN_TAC THEN
   REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_INTERS] THEN
   EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:(A->bool)` THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(j:num) IN {j | j <= n * 2 EXP n /\ ~(&j / &(2 EXP n) <= a)}` THEN
    REWRITE_TAC[IN_ELIM_THM];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `{z:A | z IN prob_carrier p /\ f z < &j / &(2 EXP n)}`) THEN
    ANTS_TAC THENL
    [REWRITE_TAC[IN_IMAGE] THEN
     EXISTS_TAC `j:num` THEN
     CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN REFL_TAC;
      ASM_REWRITE_TAC[IN_ELIM_THM]];
     REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]]];
   ALL_TAC] THEN
  ASM_CASES_TAC `{j:num | j <= n * 2 EXP n /\ ~(&j / &(2 EXP n) <= a)} = {}` THENL
  [ASM_REWRITE_TAC[IMAGE_CLAUSES; INTERS_0; INTER_UNIV; PROB_CARRIER_IN_EVENTS];
   MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN
   REWRITE_TAC[PROB_CARRIER_IN_EVENTS] THEN
   MATCH_MP_TAC PROB_COUNTABLE_INTERS_IN_EVENTS THEN
   REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC RANDOM_VARIABLE_OPEN_HALFLINE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FINITE_IMP_COUNTABLE THEN
    MATCH_MP_TAC FINITE_IMAGE THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{j:num | j <= n * 2 EXP n}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LE; SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[];
    ASM_SIMP_TAC[IMAGE_EQ_EMPTY]]]);;

(* The approx function is a simple random variable *)
let NONNEG_SIMPLE_FN_APPROX_SIMPLE_RV = prove
 (`!p:A prob_space f n.
    random_variable p f /\ (!x. x IN prob_carrier p ==> &0 <= f x)
    ==> simple_rv p (nonneg_simple_fn_approx p f n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simple_rv] THEN CONJ_TAC THENL
  [ASM_SIMP_TAC[NONNEG_SIMPLE_FN_APPROX_RV]; ALL_TAC] THEN
  SUBGOAL_THEN
    `{nonneg_simple_fn_approx (p:A prob_space) f n x | x | x IN prob_carrier p} SUBSET
     IMAGE (\k. &k / &(2 EXP n)) {k | k <= n * 2 EXP n} UNION {&0:real}`
    MP_TAC THENL
  [REWRITE_TAC[SUBSET; IN_UNION; IN_IMAGE; IN_ELIM_THM; IN_SING;
               FORALL_IN_GSPEC] THEN
   X_GEN_TAC `z:A` THEN DISCH_TAC THEN
   ASM_CASES_TAC `&0 <= (f:A->real) z` THENL
   [MP_TAC(SPECL [`p:A prob_space`; `f:A->real`; `n:num`; `z:A`]
     NONNEG_SIMPLE_FN_APPROX_IN_GRID) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    DISJ1_TAC THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN
    REWRITE_TAC[nonneg_simple_fn_approx] THEN
    ASM_REWRITE_TAC[]];
   DISCH_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
   EXISTS_TAC `IMAGE (\k. &k / &(2 EXP n)) {k | k <= n * 2 EXP n} UNION {&0:real}` THEN
   ASM_REWRITE_TAC[FINITE_UNION; FINITE_SING] THEN
   MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_NUMSEG_LE]]);;

(* Monotonicity: coarser grid gives smaller approximation *)
let NONNEG_SIMPLE_FN_APPROX_MONO = prove
 (`!p:A prob_space f m n x.
    m <= n /\ x IN prob_carrier p /\ &0 <= f x
    ==> nonneg_simple_fn_approx p f m x <= nonneg_simple_fn_approx p f n x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[nonneg_simple_fn_approx] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC (SPECL [`m:num`; `f:A->real`; `x:A`] NONNEG_APPROX_SET_FINITE) THEN
  MP_TAC (SPECL [`m:num`; `f:A->real`; `x:A`] NONNEG_APPROX_SET_NONEMPTY) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC (SPEC `IMAGE (\k. &k / &(2 EXP m))
                {k | k <= m * 2 EXP m /\ &k / &(2 EXP m) <= f (x:A)}`
               SUP_FINITE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC (SPECL [`n:num`; `f:A->real`; `x:A`] NONNEG_APPROX_SET_FINITE) THEN
  MP_TAC (SPECL [`n:num`; `f:A->real`; `x:A`] NONNEG_APPROX_SET_NONEMPTY) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC (SPEC `IMAGE (\k. &k / &(2 EXP n))
                {k | k <= n * 2 EXP n /\ &k / &(2 EXP n) <= f (x:A)}`
               SUP_FINITE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_SUP_LE_SUBSET THEN
  REPEAT CONJ_TAC THENL
  [ASM_REWRITE_TAC[];
   (* SUBSET: m-grid image SUBSET n-grid image *)
   REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_IMAGE; IN_ELIM_THM] THEN
   X_GEN_TAC `km:num` THEN STRIP_TAC THEN
   EXISTS_TAC `km * 2 EXP (n - m)` THEN
   SUBGOAL_THEN `2 EXP n = 2 EXP m * 2 EXP (n - m)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `&0 < &(2 EXP m) /\ &0 < &(2 EXP n)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ; EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
   SUBGOAL_THEN `&km / &(2 EXP m) = &(km * 2 EXP (n - m)) / &(2 EXP n)`
     ASSUME_TAC THENL
   [MP_TAC(INST [`&km`,`x1:real`; `&(2 EXP m)`, `y1:real`;
                  `&(km * 2 EXP (n - m))`, `x2:real`; `&(2 EXP n)`, `y2:real`]
                 RAT_LEMMA5) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_EQ] THEN
    ASM_REWRITE_TAC[GSYM MULT_ASSOC] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[MULT_ASSOC] THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[LE_REFL] THEN
    ASM_MESON_TAC[LE_TRANS; LE_MULT2; LE_REFL];
    UNDISCH_TAC `&km / &(2 EXP m) = &(km * 2 EXP (n - m)) / &(2 EXP n)` THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o GSYM) THEN
    ASM_REWRITE_TAC[]];
   (* bounded *)
   EXISTS_TAC `(f:A->real) x` THEN
   REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Gap bound: when f(x) <= n, the gap is at most 1/2^n *)
let NONNEG_SIMPLE_FN_APPROX_GAP = prove
 (`!p:A prob_space f n x.
    x IN prob_carrier p /\ &0 <= f x /\ f x <= &n
    ==> f x - nonneg_simple_fn_approx p f n x <= &1 / &(2 EXP n)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[nonneg_simple_fn_approx] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC (SPECL [`n:num`; `f:A->real`; `x:A`] NONNEG_APPROX_SET_FINITE) THEN
  MP_TAC (SPECL [`n:num`; `f:A->real`; `x:A`] NONNEG_APPROX_SET_NONEMPTY) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC (SPEC `IMAGE (\k. &k / &(2 EXP n))
                {k | k <= n * 2 EXP n /\ &k / &(2 EXP n) <= f (x:A)}`
               SUP_FINITE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `sup (IMAGE (\k. &k / &(2 EXP n))
      {k | k <= n * 2 EXP n /\ &k / &(2 EXP n) <= f (x:A)}) IN
      IMAGE (\k. &k / &(2 EXP n))
      {k | k <= n * 2 EXP n /\ &k / &(2 EXP n) <= f x}` THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `km:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(&(2 EXP n) = &0)` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_OF_NUM_EQ; EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &(2 EXP n)` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ; EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `&(km + 1) / &(2 EXP n) = &km / &(2 EXP n) + &1 / &(2 EXP n)`
    ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_ADD_RDISTRIB; real_div] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[REAL_OF_NUM_ADD]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&(km + 1) / &(2 EXP n) <= (f:A->real) x` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `km + 1 <= n * 2 EXP n` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_OF_NUM_LE; REAL_OF_NUM_MUL] THEN
   SUBGOAL_THEN `&(km + 1) / &(2 EXP n) * &(2 EXP n) <= &n * &(2 EXP n)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_POS] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `&(km + 1) / &(2 EXP n) * &(2 EXP n) = &(km + 1)` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE]];
   ALL_TAC] THEN
  SUBGOAL_THEN `&(km + 1) / &(2 EXP n) IN
    IMAGE (\k. &k / &(2 EXP n)) {k | k <= n * 2 EXP n /\ &k / &(2 EXP n) <= f (x:A)}`
    MP_TAC THENL
  [REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
   EXISTS_TAC `km + 1` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&(km + 1) / &(2 EXP n)`) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < &1 / &(2 EXP n)` MP_TAC THENL
  [SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; LT_NZ; EXP_EQ_0; ARITH_EQ; ARITH];
   ALL_TAC] THEN
  UNDISCH_TAC `&(km + 1) / &(2 EXP n) = &km / &(2 EXP n) + &1 / &(2 EXP n)` THEN
  REAL_ARITH_TAC);;

(* Pointwise convergence to f *)
let NONNEG_SIMPLE_FN_APPROX_CONVERGES = prove
 (`!p:A prob_space f x.
    x IN prob_carrier p /\ &0 <= f x
    ==> ((\n. nonneg_simple_fn_approx p f n x) ---> f x) sequentially`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`&1 / &2`; `e:real`] REAL_ARCH_POW_INV) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` ASSUME_TAC) THEN
  MP_TAC(SPEC `(f:A->real) x` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` ASSUME_TAC) THEN
  EXISTS_TAC `N1 + N2:num` THEN
  X_GEN_TAC `nn:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs(nonneg_simple_fn_approx p (f:A->real) nn x - f x) =
                f x - nonneg_simple_fn_approx p f nn x` SUBST1_TAC THENL
  [REWRITE_TAC[REAL_ABS_SUB] THEN
   MATCH_MP_TAC(REAL_ARITH `a <= b ==> abs(b - a) = b - a`) THEN
   MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_LE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `&1 / &(2 EXP nn)` THEN CONJ_TAC THENL
  [MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_GAP THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N2` THEN
   ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `(&1 / &2) pow N1` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&1 / &(2 EXP nn) = (&1 / &2) pow nn` SUBST1_TAC THENL
  [REWRITE_TAC[REAL_POW_DIV; REAL_POW_ONE; REAL_OF_NUM_POW]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_MONO_INV THEN
  REPEAT CONJ_TAC THENL
  [REAL_ARITH_TAC; REAL_ARITH_TAC; ASM_ARITH_TAC]);;

(* ========================================================================= *)
(* Phase 2: Non-negative Expectation via sup of simple approximations        *)
(* ========================================================================= *)

let nn_expectation = new_definition
  `nn_expectation (p:A prob_space) (f:A->real) =
   sup {simple_expectation p g | g |
        simple_rv p g /\
        (!x. x IN prob_carrier p ==> &0 <= g x) /\
        (!x. x IN prob_carrier p ==> g x <= f x)}`;;

(* The zero function is always in the nn_expectation set for nonneg f *)
let NN_EXPECT_SET_NONEMPTY = prove
 (`!p:A prob_space f.
    (!x. x IN prob_carrier p ==> &0 <= f x)
    ==> ~({simple_expectation p g | g |
           simple_rv p g /\
           (!x. x IN prob_carrier p ==> &0 <= g x) /\
           (!x. x IN prob_carrier p ==> g x <= f x)} = {})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  EXISTS_TAC `simple_expectation p (\x:A. &0)` THEN
  EXISTS_TAC `\x:A. &0` THEN
  REWRITE_TAC[SIMPLE_RV_CONST; REAL_LE_REFL] THEN
  ASM_SIMP_TAC[]);;

(* nn_expectation agrees with simple_expectation for simple nonneg functions *)
let NN_EXPECTATION_SIMPLE = prove
 (`!p:A prob_space f.
    simple_rv p f /\ (!x. x IN prob_carrier p ==> &0 <= f x)
    ==> nn_expectation p f = simple_expectation p f`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[nn_expectation] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b /\ b <= a ==> b = a`) THEN
  CONJ_TAC THENL
  [(* simple_expectation p f <= sup S *)
   MATCH_MP_TAC REAL_LE_SUP THEN
   EXISTS_TAC `simple_expectation p (f:A->real)` THEN
   EXISTS_TAC `simple_expectation p (f:A->real)` THEN
   REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `f:A->real` THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    X_GEN_TAC `v:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
    ASM_REWRITE_TAC[]];
   (* sup S <= simple_expectation p f *)
   MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
   [MATCH_MP_TAC NN_EXPECT_SET_NONEMPTY THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   X_GEN_TAC `v:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
   ASM_REWRITE_TAC[]]);;

(* nn_expectation is monotone for bounded functions *)
let BOUNDED_NN_EXPECTATION_MONO = prove
 (`!p:A prob_space f g.
    (!x. x IN prob_carrier p ==> &0 <= f x) /\
    (!x. x IN prob_carrier p ==> &0 <= g x) /\
    (!x. x IN prob_carrier p ==> f x <= g x) /\
    (?B. !x. x IN prob_carrier p ==> g x <= B)
    ==> nn_expectation p f <= nn_expectation p g`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[nn_expectation] THEN
  MATCH_MP_TAC REAL_SUP_LE_SUBSET THEN CONJ_TAC THENL
  [MATCH_MP_TAC NN_EXPECT_SET_NONEMPTY THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
   X_GEN_TAC `v:real` THEN
   DISCH_THEN(X_CHOOSE_THEN `h:A->real` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `h:A->real` THEN ASM_REWRITE_TAC[] THEN
   X_GEN_TAC `z:A` THEN DISCH_TAC THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(f:A->real) z` THEN
   ASM_SIMP_TAC[];
   EXISTS_TAC `B:real` THEN
   X_GEN_TAC `v:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `simple_expectation (p:A prob_space) g' <=
                  simple_expectation p (\x:A. B)` MP_TAC THENL
   [MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
    ASM_REWRITE_TAC[SIMPLE_RV_CONST] THEN
    ASM_MESON_TAC[REAL_LE_TRANS];
    REWRITE_TAC[SIMPLE_EXPECTATION_CONST]]]);;

(* Simple random variables have bounded range *)
let SIMPLE_RV_BOUNDED = prove
 (`!p:A prob_space g. simple_rv p g
     ==> ?Bg. !x. x IN prob_carrier p ==> g x <= Bg`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simple_rv]) THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `prob_carrier (p:A prob_space) = {}` THENL
  [EXISTS_TAC `&0` THEN ASM SET_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `~({(g:A->real) x | x IN prob_carrier p} = {})` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
   UNDISCH_TAC `~(prob_carrier (p:A prob_space) = {})` THEN
   REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN MESON_TAC[];
   ALL_TAC] THEN
  EXISTS_TAC `sup {(g:A->real) x | x IN prob_carrier p}` THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{(g:A->real) x | x IN prob_carrier p}`] SUP_FINITE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MP_TAC(CONJUNCT2 th)) THEN
  DISCH_THEN(MP_TAC o SPEC `(g:A->real) x`) THEN
  ANTS_TAC THENL
  [REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[]]);;

(* Level set {x | h x >= c} is an event when h is simple *)
let SIMPLE_RV_GE_EVENT = prove
 (`!p:A prob_space h c. simple_rv p h
     ==> {x | x IN prob_carrier p /\ h x >= c} IN prob_events p`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ (h:A->real) x >= c} =
                prob_carrier p DIFF {x | x IN prob_carrier p /\ h x < c}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN
   GEN_TAC THEN ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN
   ASM_REWRITE_TAC[real_ge] THEN REAL_ARITH_TAC;
   MATCH_MP_TAC PROB_COMPL_IN_EVENTS THEN
   MATCH_MP_TAC RANDOM_VARIABLE_OPEN_HALFLINE THEN
   ASM_MESON_TAC[simple_rv]]);;

(* If f >= g on event a, then E[f] >= E[g * 1_a] *)
let SIMPLE_EXPECTATION_GE_ON_EVENT = prove
 (`!p:A prob_space f g a.
     simple_rv p f /\ simple_rv p g /\
     (!x. x IN prob_carrier p ==> &0 <= f x) /\
     (!x. x IN prob_carrier p ==> &0 <= g x) /\
     a IN prob_events p /\
     (!x. x IN a ==> f x >= g x)
     ==> simple_expectation p f >=
         simple_expectation p (\x. g x * indicator_fn a x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_ge] THEN
  MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_MUL THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THENL
  [REWRITE_TAC[REAL_MUL_RID] THEN
   UNDISCH_TAC `!x:A. x IN a ==> (f:A->real) x >= g x` THEN
   DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[real_ge];
   REWRITE_TAC[REAL_MUL_RZERO] THEN ASM_MESON_TAC[]]);;

(* Simple h below f implies E[h] <= nn_expectation f *)
let BOUNDED_NN_EXPECTATION_GE_SIMPLE = prove
 (`!p:A prob_space h f.
     simple_rv p h /\
     (!x. x IN prob_carrier p ==> &0 <= h x) /\
     (!x. x IN prob_carrier p ==> h x <= f x) /\
     (?B. !x. x IN prob_carrier p ==> f x <= B)
     ==> simple_expectation p h <= nn_expectation p f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nn_expectation] THEN
  MATCH_MP_TAC REAL_LE_SUP THEN
  EXISTS_TAC `B:real` THEN EXISTS_TAC `simple_expectation p (h:A->real)` THEN
  REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
  [REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `h:A->real` THEN
   ASM_REWRITE_TAC[];
   GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
   DISCH_THEN(X_CHOOSE_THEN `h':A->real` STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `simple_expectation (p:A prob_space) h' <=
                 simple_expectation p (\x:A. B:real)` MP_TAC THENL
   [MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
    ASM_REWRITE_TAC[SIMPLE_RV_CONST] THEN ASM_MESON_TAC[REAL_LE_TRANS];
    REWRITE_TAC[SIMPLE_EXPECTATION_CONST]]]);;

(* nn_expectation bounded above by bound on function *)
let NN_EXPECTATION_UPPER_BOUND = prove
 (`!p:A prob_space f B.
     (!x. x IN prob_carrier p ==> &0 <= f x) /\
     (!x. x IN prob_carrier p ==> f x <= B)
     ==> nn_expectation p f <= B`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nn_expectation] THEN
  MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
  [MATCH_MP_TAC NN_EXPECT_SET_NONEMPTY THEN ASM_REWRITE_TAC[];
   X_GEN_TAC `v:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
   DISCH_THEN(X_CHOOSE_THEN `g':A->real` STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `simple_expectation (p:A prob_space) g' <=
                 simple_expectation p (\x:A. B:real)` MP_TAC THENL
   [MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
    ASM_REWRITE_TAC[SIMPLE_RV_CONST] THEN ASM_MESON_TAC[REAL_LE_TRANS];
    REWRITE_TAC[SIMPLE_EXPECTATION_CONST]]]);;

(* If all simple approximations to f are bounded by c, then nn_exp(f) <= c *)
let NN_EXPECTATION_LE_FROM_SIMPLE = prove
 (`!p:A prob_space f c.
     (!x. x IN prob_carrier p ==> &0 <= f x) /\
     (!h. simple_rv p h /\
          (!x. x IN prob_carrier p ==> &0 <= h x) /\
          (!x. x IN prob_carrier p ==> h x <= f x)
          ==> simple_expectation p h <= c)
     ==> nn_expectation p f <= c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nn_expectation] THEN
  MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
  [MATCH_MP_TAC NN_EXPECT_SET_NONEMPTY THEN ASM_REWRITE_TAC[];
   X_GEN_TAC `v:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
   DISCH_THEN(X_CHOOSE_THEN `g:A->real` STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[]]);;

(* Easy direction of nn_expectation additivity *)
let NN_EXPECTATION_ADD_GE = prove
 (`!p:A prob_space f g.
     (!x. x IN prob_carrier p ==> &0 <= f x) /\
     (!x. x IN prob_carrier p ==> &0 <= g x) /\
     (?Bf. !x. x IN prob_carrier p ==> f x <= Bf) /\
     (?Bg. !x. x IN prob_carrier p ==> g x <= Bg)
     ==> nn_expectation p f + nn_expectation p g <=
         nn_expectation p (\x. f x + g x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `nn_expectation (p:A prob_space) g <=
    nn_expectation p (\x. (f:A->real) x + g x) - nn_expectation p f`
    (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
  MATCH_MP_TAC NN_EXPECTATION_LE_FROM_SIMPLE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k:A->real` THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_LE_SUB_LADD] THEN
  SUBGOAL_THEN `nn_expectation (p:A prob_space) f <=
    nn_expectation p (\x. (f:A->real) x + g x) -
    simple_expectation p (k:A->real)`
    (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
  MATCH_MP_TAC NN_EXPECTATION_LE_FROM_SIMPLE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `h:A->real` THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_LE_SUB_LADD] THEN
  SUBGOAL_THEN `simple_expectation (p:A prob_space) h +
    simple_expectation p k =
    simple_expectation p (\x:A. (h:A->real) x + (k:A->real) x)` SUBST1_TAC THENL
  [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SIMPLE_EXPECTATION_ADD THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MATCH_MP_TAC BOUNDED_NN_EXPECTATION_GE_SIMPLE THEN
  REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_ADD THEN ASM_REWRITE_TAC[];
   GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
   MATCH_MP_TAC REAL_LE_ADD THEN ASM_MESON_TAC[];
   GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
   MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_MESON_TAC[REAL_LE_TRANS];
   EXISTS_TAC `Bf + Bg:real` THEN GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
   MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_MESON_TAC[]]);;

(* Max of two simple RVs is simple *)
let SIMPLE_RV_MAX = prove
 (`!p:A prob_space X Y.
     simple_rv p X /\ simple_rv p Y
     ==> simple_rv p (\x. max (X x) (Y x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:A. max ((X:A->real) x) ((Y:A->real) x)) =
                (\x. inv(&2) * ((X x + Y x) + abs(X x - Y x)))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
   MATCH_MP_TAC SIMPLE_RV_CMUL THEN
   MATCH_MP_TAC SIMPLE_RV_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_ADD THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SIMPLE_RV_ABS THEN
    MATCH_MP_TAC SIMPLE_RV_SUB THEN ASM_REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* Phase 3: General Expectation and Integrability                            *)
(* ========================================================================= *)

let integrable = new_definition
  `integrable (p:A prob_space) (f:A->real) <=>
   random_variable p f /\
   (?B. !g. simple_rv p g /\
            (!x. x IN prob_carrier p ==> &0 <= g x) /\
            (!x. x IN prob_carrier p ==> g x <= abs(f x))
            ==> simple_expectation p g <= B)`;;

let expectation = new_definition
  `expectation (p:A prob_space) (f:A->real) =
   nn_expectation p (\x. max (f x) (&0)) -
   nn_expectation p (\x. max (--(f x)) (&0))`;;

(* Simple functions are integrable *)
let INTEGRABLE_SIMPLE = prove
 (`!p:A prob_space f. simple_rv p f ==> integrable p f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[integrable] THEN CONJ_TAC THENL
  [ASM_MESON_TAC[simple_rv];
   EXISTS_TAC `simple_expectation p (\x:A. abs(f x))` THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
   ASM_SIMP_TAC[SIMPLE_RV_ABS]]);;

(* General expectation agrees with simple_expectation for simple RVs *)
let EXPECTATION_SIMPLE_AGREE = prove
 (`!p:A prob_space f.
    simple_rv p f
    ==> expectation p f = simple_expectation p f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[expectation] THEN
  (* max(f, 0) and max(-f, 0) are simple *)
  SUBGOAL_THEN `simple_rv p (\x:A. max (f x) (&0))` ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_MAX THEN ASM_REWRITE_TAC[SIMPLE_RV_CONST];
   ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv p (\x:A. max (--(f x)) (&0))` ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_MAX THEN ASM_REWRITE_TAC[SIMPLE_RV_CONST] THEN
   MATCH_MP_TAC SIMPLE_RV_NEG THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Use NN_EXPECTATION_SIMPLE for both parts *)
  SUBGOAL_THEN `nn_expectation p (\x:A. max (f x) (&0)) =
                simple_expectation p (\x. max (f x) (&0))` SUBST1_TAC THENL
  [MATCH_MP_TAC NN_EXPECTATION_SIMPLE THEN ASM_REWRITE_TAC[] THEN
   GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `nn_expectation p (\x:A. max (--(f x)) (&0)) =
                simple_expectation p (\x. max (--(f x)) (&0))` SUBST1_TAC THENL
  [MATCH_MP_TAC NN_EXPECTATION_SIMPLE THEN ASM_REWRITE_TAC[] THEN
   GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Now: E[f+] - E[f-] = E[f] *)
  SUBGOAL_THEN `!x:A. max (f x) (&0) - max (--(f x)) (&0) = f x`
    (fun th -> MP_TAC th) THENL
  [GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `simple_expectation p (\x:A. max (f x) (&0) - max (--(f x)) (&0))` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC SIMPLE_EXPECTATION_SUB THEN ASM_REWRITE_TAC[];
   AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* Expectation extensionality, MCT for nn_expectation, nn_expectation        *)
(* additivity. (Moved from martingales.ml -- purely about expectation.)      *)
(* ========================================================================= *)

(* Expectation only depends on values in prob_carrier *)
let SIMPLE_EXPECTATION_EXT = prove
 (`!p:A prob_space f g.
     (!x. x IN prob_carrier p ==> f x = g x)
     ==> simple_expectation p f = simple_expectation p g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simple_expectation] THEN
  SUBGOAL_THEN
    `IMAGE (f:A->real) (prob_carrier p) = IMAGE g (prob_carrier p)`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN GEN_TAC THEN
   EQ_TAC THEN STRIP_TAC THEN EXISTS_TAC `x':A` THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `v:real` THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
  DISCH_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

(* X * indicator_fn(prob_carrier p) has same expectation as X *)
let SIMPLE_EXPECTATION_MUL_INDICATOR_CARRIER = prove
 (`!p:A prob_space X.
     simple_expectation p (\x. X x * indicator_fn (prob_carrier p) x) =
     simple_expectation p X`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  REWRITE_TAC[indicator_fn] THEN
  ASM_REWRITE_TAC[REAL_MUL_RID]);;


(* ========================================================================= *)
(* Monotone Convergence Theorem for nn_expectation                           *)
(* If fn are simple, nonneg, increasing pointwise to f (bounded), then       *)
(* E[fn n] -> nn_expectation p f                                             *)
(* ========================================================================= *)

(* Helper: if for all 0 < a < 1, a*c <= L, then c <= L *)
let REAL_LE_FROM_SCALE = prove
 (`!c L:real. &0 < c /\ (!a. &0 < a /\ a < &1 ==> a * c <= L) ==> c <= L`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 / &2 * c <= L` ASSUME_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * c` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(c + L) / (&2 * c)`) THEN
  REWRITE_TAC[NOT_IMP; REAL_NOT_LE] THEN
  REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
   ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
   MP_TAC(REAL_FIELD `~(c = &0) ==> (c + L) / (&2 * c) * c = (c + L) / &2`) THEN
   ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC]]);;

let SIMPLE_MCT_NN_EXPECTATION = prove
 (`!p:A prob_space fn f.
    (!n. simple_rv p (fn n)) /\
    (!n x. x IN prob_carrier p ==> &0 <= fn n x) /\
    (!n x. x IN prob_carrier p ==> fn n x <= fn (SUC n) x) /\
    (!x. x IN prob_carrier p ==> ((\n. fn n x) ---> f x) sequentially) /\
    (?B. !x. x IN prob_carrier p ==> f x <= B)
    ==> ((\n. simple_expectation p (fn n)) ---> nn_expectation p f) sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  (* Establish: f is nonneg *)
  SUBGOAL_THEN `!x:A. x IN prob_carrier p ==> &0 <= f x` ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LBOUND) THEN
   EXISTS_TAC `\n:num. (fn:num->A->real) n x` THEN
   ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
   EXISTS_TAC `0` THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  (* Establish: fn m <= fn n for m <= n (transitive monotonicity) *)
  SUBGOAL_THEN `!m n x:A. m <= n /\ x IN prob_carrier p ==> fn m x <= (fn:num->A->real) n x`
    ASSUME_TAC THENL
  [GEN_TAC THEN INDUCT_TAC THENL
   [SIMP_TAC[LE] THEN MESON_TAC[REAL_LE_REFL];
    GEN_TAC THEN REWRITE_TAC[LE] THEN STRIP_TAC THENL
    [ASM_REWRITE_TAC[REAL_LE_REFL];
     MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(fn:num->A->real) n x` THEN
     CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]]]];
   ALL_TAC] THEN
  (* Establish: fn n <= f pointwise *)
  SUBGOAL_THEN `!n x:A. x IN prob_carrier p ==> (fn:num->A->real) n x <= (f:A->real) x` ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LBOUND) THEN
   EXISTS_TAC `\m:num. (fn:num->A->real) m x` THEN
   ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
   EXISTS_TAC `n:num` THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  (* E[fn n] is monotone nondecreasing *)
  SUBGOAL_THEN `!n. simple_expectation (p:A prob_space) (fn n) <=
                    simple_expectation p (fn (SUC n))` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* E[fn n] is bounded: |E[fn n]| <= B *)
  SUBGOAL_THEN `!n. abs(simple_expectation (p:A prob_space) ((fn:num->A->real) n)) <= B`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   SUBGOAL_THEN `&0 <= simple_expectation (p:A prob_space) ((fn:num->A->real) n)` ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_EXPECTATION_POS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `simple_expectation (p:A prob_space) ((fn:num->A->real) n) <= B` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `nn_expectation (p:A prob_space) f` THEN CONJ_TAC THENL
    [MATCH_MP_TAC BOUNDED_NN_EXPECTATION_GE_SIMPLE THEN ASM_REWRITE_TAC[] THEN
     ASM_MESON_TAC[];
     MATCH_MP_TAC NN_EXPECTATION_UPPER_BOUND THEN ASM_REWRITE_TAC[]];
    ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* E[fn n] converges to some L *)
  MP_TAC(SPEC `\n:num. simple_expectation (p:A prob_space) ((fn:num->A->real) n)`
    CONVERGENT_REAL_BOUNDED_MONOTONE) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [REWRITE_TAC[real_bounded; FORALL_IN_IMAGE; IN_UNIV] THEN
    EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[BETA_THM];
    DISJ1_TAC THEN REWRITE_TAC[BETA_THM] THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  REWRITE_TAC[BETA_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `L:real`) THEN
  (* Show L = nn_expectation p f, then conclude *)
  SUBGOAL_THEN `L = nn_expectation (p:A prob_space) f`
    (fun th -> ASM_REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
  [(* Easy direction: L <= nn_exp(f) *)
   MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
   EXISTS_TAC `\n:num. simple_expectation (p:A prob_space) ((fn:num->A->real) n)` THEN
   ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
   EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
   MATCH_MP_TAC BOUNDED_NN_EXPECTATION_GE_SIMPLE THEN
   ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];

   (* Hard direction: nn_exp(f) <= L *)
   MATCH_MP_TAC NN_EXPECTATION_LE_FROM_SIMPLE THEN
   ASM_REWRITE_TAC[] THEN
   X_GEN_TAC `g:A->real` THEN STRIP_TAC THEN
   (* Establish 0 <= L *)
   SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LBOUND) THEN
    EXISTS_TAC `\n:num. simple_expectation (p:A prob_space) ((fn:num->A->real) n)` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SIMPLE_EXPECTATION_POS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* Case: E[g] = 0 *)
   ASM_CASES_TAC `simple_expectation (p:A prob_space) g = &0` THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   (* Case: E[g] > 0 - use alpha trick *)
   MATCH_MP_TAC REAL_LE_FROM_SCALE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `&0 <= simple_expectation (p:A prob_space) g` MP_TAC THENL
    [MATCH_MP_TAC SIMPLE_EXPECTATION_POS THEN ASM_REWRITE_TAC[];
     ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
   X_GEN_TAC `a:real` THEN STRIP_TAC THEN
   (* Define An *)
   ABBREV_TAC `An = \n:num. {x:A | x IN prob_carrier p /\ (fn:num->A->real) n x >= a * (g:A->real) x}` THEN
   (* An are events *)
   SUBGOAL_THEN `!n:num. (An:num->A->bool) n IN prob_events p` ASSUME_TAC THENL
   [GEN_TAC THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(AP_THM th `n:num`)) THEN
    REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ (fn:num->A->real) (n:num) x >= a * (g:A->real) x} =
      {x | x IN prob_carrier p /\ (\x. fn n x - a * g x) x >= &0}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
     AP_TERM_TAC THEN REAL_ARITH_TAC;
     MATCH_MP_TAC(ISPEC `p:A prob_space` SIMPLE_RV_GE_EVENT) THEN
     MP_TAC(ISPECL [`p:A prob_space`; `(fn:num->A->real) (n:num)`;
                     `\x:A. a * (g:A->real) x`] SIMPLE_RV_SUB) THEN
     REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
     ASM_REWRITE_TAC[ETA_AX] THEN
     MP_TAC(ISPECL [`p:A prob_space`; `g:A->real`; `a:real`] SIMPLE_RV_CMUL) THEN
     ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   (* An are increasing *)
   SUBGOAL_THEN `!n. (An:num->A->bool) n SUBSET An (SUC n)` ASSUME_TAC THENL
   [GEN_TAC THEN
    UNDISCH_TAC `(\n:num. {x:A | x IN prob_carrier p /\ (fn:num->A->real) n x >= a * (g:A->real) x}) = (An:num->A->bool)` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(AP_THM th `n:num`); GSYM(AP_THM th `SUC n`)]) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_ge] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(fn:num->A->real) n x` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[GSYM real_ge]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
   (* An n SUBSET carrier *)
   SUBGOAL_THEN `!n (x:A). x IN (An:num->A->bool) n ==> x IN prob_carrier p`
     ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    UNDISCH_TAC `(\n:num. {x:A | x IN prob_carrier p /\ (fn:num->A->real) n x >= a * (g:A->real) x}) = (An:num->A->bool)` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
   (* UNIONS An = carrier *)
   SUBGOAL_THEN `UNIONS {(An:num->A->bool) n | n IN (:num)} = prob_carrier p`
     ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
    [REWRITE_TAC[UNIONS_GSPEC; SUBSET; IN_ELIM_THM; IN_UNIV] THEN
     ASM_MESON_TAC[];
     REWRITE_TAC[UNIONS_GSPEC; SUBSET; IN_ELIM_THM; IN_UNIV] THEN
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN
     ASM_CASES_TAC `(g:A->real) x = &0` THENL
     [EXISTS_TAC `0` THEN
      UNDISCH_TAC `(\n:num. {x:A | x IN prob_carrier p /\ (fn:num->A->real) n x >= a * (g:A->real) x}) = (An:num->A->bool)` THEN
      DISCH_THEN(fun th -> REWRITE_TAC[GSYM(AP_THM th `0`)]) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_MUL_RZERO; real_ge] THEN ASM_MESON_TAC[];
      (* g x > 0 case *)
      SUBGOAL_THEN `&0 < (g:A->real) x` ASSUME_TAC THENL
      [ASM_MESON_TAC[REAL_LE_LT]; ALL_TAC] THEN
      SUBGOAL_THEN `a * (g:A->real) x < f x` ASSUME_TAC THENL
      [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&1 * (g:A->real) x` THEN
       CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_RMUL]; ASM_SIMP_TAC[REAL_MUL_LID]];
       ALL_TAC] THEN
      UNDISCH_TAC `!x:A. x IN prob_carrier p ==> ((\n. (fn:num->A->real) n x) ---> (f:A->real) x) sequentially` THEN
      DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[tendsto_real; EVENTUALLY_SEQUENTIALLY] THEN
      DISCH_THEN(MP_TAC o SPEC `(f:A->real) x - a * (g:A->real) x`) THEN
      ASM_REWRITE_TAC[REAL_SUB_LT] THEN
      DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
      EXISTS_TAC `N:num` THEN
      UNDISCH_TAC `(\n:num. {x:A | x IN prob_carrier p /\ (fn:num->A->real) n x >= a * (g:A->real) x}) = (An:num->A->bool)` THEN
      DISCH_THEN(fun th -> REWRITE_TAC[GSYM(AP_THM th `N:num`)]) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[real_ge] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
      REWRITE_TAC[LE_REFL] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
   (* P(An n) -> P(carrier) = 1 *)
   SUBGOAL_THEN
     `((\n:num. prob (p:A prob_space) (An n)) ---> &1) sequentially`
     ASSUME_TAC THENL
   [SUBGOAL_THEN `((\n:num. prob (p:A prob_space) (An n)) ---> prob p (UNIONS {An n | n IN (:num)})) sequentially` MP_TAC THENL
    [MATCH_MP_TAC(ISPEC `p:A prob_space` PROB_CONTINUITY_FROM_BELOW) THEN
     ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[PROB_SPACE]];
    ALL_TAC] THEN
   (* Key inequality: E[fn n] >= a * E[g * 1_{An n}] *)
   SUBGOAL_THEN
     `!n:num. a * simple_expectation (p:A prob_space) (\x. g x * indicator_fn (An n) x) <=
              simple_expectation p (fn n)` ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `simple_rv (p:A prob_space) (\x. g x * indicator_fn ((An:num->A->bool) n) x)` ASSUME_TAC THENL
    [MP_TAC(ISPECL [`p:A prob_space`; `g:A->real`;
                     `indicator_fn ((An:num->A->bool) n)`] SIMPLE_RV_MUL) THEN
     REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    (* E[fn n] >= E[(a*g) * 1_{An}] by SIMPLE_EXPECTATION_GE_ON_EVENT *)
    SUBGOAL_THEN
      `simple_expectation (p:A prob_space) (fn (n:num)) >=
       simple_expectation p (\x. (a * g x) * indicator_fn (An n) x)`
      MP_TAC THENL
    [MATCH_MP_TAC SIMPLE_EXPECTATION_GE_ON_EVENT THEN
     ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SIMPLE_RV_CMUL THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]];
      X_GEN_TAC `x:A` THEN
      FIRST_X_ASSUM(fun th -> MP_TAC(AP_THM th `n:num`)) THEN
      REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]];
     ALL_TAC] THEN
    (* E[(a*g) * 1_{An}] = a * E[g * 1_{An}] *)
    MP_TAC(ISPECL [`p:A prob_space`;
      `\x:A. g x * indicator_fn ((An:num->A->bool) n) x`;
      `a:real`] SIMPLE_EXPECTATION_CMUL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    SUBGOAL_THEN `(\x:A. (a * g x) * indicator_fn ((An:num->A->bool) n) x) =
                  (\x. a * (g x * indicator_fn (An n) x))`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM; REAL_MUL_ASSOC]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
   (* Use REALLIM_LE: need E[g * 1_{An}] -> E[g] *)
   MATCH_MP_TAC(ISPECL [`sequentially`;
     `\n:num. a * simple_expectation (p:A prob_space) (\x. g x * indicator_fn ((An:num->A->bool) n) x)`;
     `\n:num. simple_expectation (p:A prob_space) ((fn:num->A->real) n)`] REALLIM_LE) THEN
   REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
   REPEAT CONJ_TAC THENL
   [(* (\n. a * E[g * 1_{An}]) -> a * E[g] *)
    MATCH_MP_TAC REALLIM_LMUL THEN
    (* E[g * 1_{An}] -> E[g] *)
    SUBGOAL_THEN `?Bg:real. !x:A. x IN prob_carrier p ==> g x <= Bg`
      STRIP_ASSUME_TAC THENL
    [MATCH_MP_TAC SIMPLE_RV_BOUNDED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    (* Splitting identity *)
    SUBGOAL_THEN
      `!n:num. simple_expectation (p:A prob_space) g =
       simple_expectation p (\x. g x * indicator_fn (An n) x) +
       simple_expectation p (\x. g x * indicator_fn (prob_carrier p DIFF An n) x)`
      ASSUME_TAC THENL
    [GEN_TAC THEN CONV_TAC SYM_CONV THEN
     SUBGOAL_THEN
       `simple_expectation (p:A prob_space) (\x. g x * indicator_fn (An (n:num)) x) +
        simple_expectation p (\x. g x * indicator_fn (prob_carrier p DIFF An n) x) =
        simple_expectation p (\x. g x * indicator_fn (An n) x + g x * indicator_fn (prob_carrier p DIFF An n) x)`
       SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SIMPLE_EXPECTATION_ADD THEN CONJ_TAC THENL
      [MP_TAC(ISPECL [`p:A prob_space`; `g:A->real`;
                       `indicator_fn ((An:num->A->bool) n)`] SIMPLE_RV_MUL) THEN
       REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
       MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[];
       MP_TAC(ISPECL [`p:A prob_space`; `g:A->real`;
                       `indicator_fn (prob_carrier (p:A prob_space) DIFF (An:num->A->bool) n)`] SIMPLE_RV_MUL) THEN
       REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
       MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
       MATCH_MP_TAC PROB_COMPL_IN_EVENTS THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      REWRITE_TAC[indicator_fn] THEN
      ASM_CASES_TAC `(x:A) IN An (n:num)` THENL
      [ASM_REWRITE_TAC[IN_DIFF] THEN REAL_ARITH_TAC;
       ASM_REWRITE_TAC[IN_DIFF] THEN REAL_ARITH_TAC]];
     ALL_TAC] THEN
    (* Rewrite E[g*1_An] = E[g] - E[g*1_{comp An}] *)
    SUBGOAL_THEN
      `(\n:num. simple_expectation (p:A prob_space) (\x. g x * indicator_fn (An n) x)) =
       (\n. simple_expectation p g - simple_expectation p (\x. g x * indicator_fn (prob_carrier p DIFF An n) x))`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
     MP_TAC(SPEC `x:num` (ASSUME `!n:num. simple_expectation (p:A prob_space) g =
      simple_expectation p (\x. g x * indicator_fn (An n) x) +
      simple_expectation p (\x. g x * indicator_fn (prob_carrier p DIFF An n) x)`)) THEN
     REAL_ARITH_TAC;
     ALL_TAC] THEN
    (* (c - h(n)) -> c when h(n) -> 0 *)
    SUBGOAL_THEN
      `((\n:num. simple_expectation (p:A prob_space)
        (\x. g x * indicator_fn (prob_carrier p DIFF An n) x)) ---> &0) sequentially`
      MP_TAC THENL
    [(* Prove h(n) -> 0 using bound and P(comp An) -> 0 *)
     (* First: P(comp An) -> 0 *)
     SUBGOAL_THEN
       `((\n:num. prob (p:A prob_space) (prob_carrier p DIFF An n)) ---> &0) sequentially`
       ASSUME_TAC THENL
     [SUBGOAL_THEN `(\n:num. prob (p:A prob_space) (prob_carrier p DIFF An n)) =
       (\n. &1 - prob p (An n))` SUBST1_TAC THENL
      [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
       MP_TAC(ISPECL [`p:A prob_space`; `(An:num->A->bool) x`] PROB_COMPL) THEN
       ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
       SUBGOAL_THEN `&0 = &1 - &1` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
       MATCH_MP_TAC REALLIM_SUB THEN
       ASM_REWRITE_TAC[REALLIM_CONST]];
      ALL_TAC] THEN
     (* Bound: 0 <= h(n) <= Bg * P(comp An) *)
     SUBGOAL_THEN
       `!n:num. &0 <= simple_expectation (p:A prob_space)
         (\x. g x * indicator_fn (prob_carrier p DIFF An n) x) /\
        simple_expectation p (\x. g x * indicator_fn (prob_carrier p DIFF An n) x) <=
        Bg * prob p (prob_carrier p DIFF An n)` ASSUME_TAC THENL
     [GEN_TAC THEN CONJ_TAC THENL
      [(* Nonneg *)
       MATCH_MP_TAC SIMPLE_EXPECTATION_POS THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`p:A prob_space`; `g:A->real`;
         `indicator_fn (prob_carrier (p:A prob_space) DIFF (An:num->A->bool) n)`] SIMPLE_RV_MUL) THEN
        REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN MATCH_MP_TAC PROB_COMPL_IN_EVENTS THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC[] THEN REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THEN REAL_ARITH_TAC];
       (* Upper bound *)
       SUBGOAL_THEN `prob_carrier (p:A prob_space) DIFF (An:num->A->bool) n IN prob_events p`
         ASSUME_TAC THENL
       [MATCH_MP_TAC PROB_COMPL_IN_EVENTS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
       SUBGOAL_THEN `Bg * prob (p:A prob_space) (prob_carrier p DIFF (An:num->A->bool) n) =
         simple_expectation p (\x. Bg * indicator_fn (prob_carrier p DIFF An n) x)` SUBST1_TAC THENL
       [MP_TAC(ISPECL [`p:A prob_space`;
          `indicator_fn (prob_carrier (p:A prob_space) DIFF (An:num->A->bool) n)`;
          `Bg:real`] SIMPLE_EXPECTATION_CMUL) THEN
        ANTS_TAC THENL
        [MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[];
         DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
         ASM_SIMP_TAC[SIMPLE_EXPECTATION_INDICATOR]];
        MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
        [MP_TAC(ISPECL [`p:A prob_space`; `g:A->real`;
           `indicator_fn (prob_carrier (p:A prob_space) DIFF (An:num->A->bool) n)`] SIMPLE_RV_MUL) THEN
         REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
         MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[];
         MP_TAC(ISPECL [`p:A prob_space`;
           `indicator_fn (prob_carrier (p:A prob_space) DIFF (An:num->A->bool) n)`;
           `Bg:real`] SIMPLE_RV_CMUL) THEN
         REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
         MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[];
         REPEAT STRIP_TAC THEN
         MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
         [ASM_MESON_TAC[];
          REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THEN REAL_ARITH_TAC]]]];
      ALL_TAC] THEN
     (* Use Bg * P(comp An) -> 0 and squeeze *)
     REWRITE_TAC[tendsto_real; EVENTUALLY_SEQUENTIALLY] THEN
     X_GEN_TAC `e:real` THEN DISCH_TAC THEN
     MP_TAC(ISPECL [`sequentially`; `\n:num. prob (p:A prob_space) (prob_carrier p DIFF (An:num->A->bool) n)`;
       `Bg:real`] REALLIM_NULL_LMUL) THEN
     ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[tendsto_real; EVENTUALLY_SEQUENTIALLY] THEN
     DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
     DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
     DISCH_TAC THEN
     MP_TAC(SPEC `n:num` (ASSUME `!n:num. &0 <= simple_expectation (p:A prob_space)
       (\x. g x * indicator_fn (prob_carrier p DIFF An n) x) /\
       simple_expectation p (\x. g x * indicator_fn (prob_carrier p DIFF An n) x) <=
       Bg * prob p (prob_carrier p DIFF An n)`)) THEN
     STRIP_TAC THEN
     SUBGOAL_THEN `&0 <= prob (p:A prob_space) (prob_carrier p DIFF (An:num->A->bool) n)` ASSUME_TAC THENL
     [MATCH_MP_TAC PROB_POSITIVE THEN MATCH_MP_TAC PROB_COMPL_IN_EVENTS THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
     (* h(n) -> 0 implies c - h(n) -> c *)
     DISCH_TAC THEN
     MP_TAC(ISPECL [`sequentially`;
       `(\n:num. simple_expectation (p:A prob_space) g)`;
       `(\n:num. simple_expectation (p:A prob_space) (\x. g x * indicator_fn (prob_carrier p DIFF (An:num->A->bool) n) x))`;
       `simple_expectation (p:A prob_space) g`;
       `&0`] REALLIM_SUB) THEN
     REWRITE_TAC[REAL_SUB_RZERO] THEN
     DISCH_THEN MATCH_MP_TAC THEN
     ASM_REWRITE_TAC[REALLIM_CONST]];
    (* E[fn n] -> L *)
    ASM_REWRITE_TAC[];
    (* eventually a * E[g*1_An] <= E[fn n] *)
    EXISTS_TAC `0` THEN ASM_REWRITE_TAC[]]]);;


(* ========================================================================= *)
(* Full additivity of nn_expectation via MCT                                 *)
(* nn_exp(f + g) = nn_exp(f) + nn_exp(g) for nonneg bounded measurable f,g   *)
(* ========================================================================= *)

let BOUNDED_NN_EXPECTATION_ADD = prove
 (`!p:A prob_space f g.
    random_variable p f /\
    random_variable p g /\
    (!x. x IN prob_carrier p ==> &0 <= f x) /\
    (!x. x IN prob_carrier p ==> &0 <= g x) /\
    (?Bf. !x. x IN prob_carrier p ==> f x <= Bf) /\
    (?Bg. !x. x IN prob_carrier p ==> g x <= Bg)
    ==> nn_expectation p (\x. f x + g x) =
        nn_expectation p f + nn_expectation p g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Name the approximating sequences *)
  ABBREV_TAC `fn = \n:num. nonneg_simple_fn_approx (p:A prob_space) (f:A->real) n` THEN
  ABBREV_TAC `gn = \n:num. nonneg_simple_fn_approx (p:A prob_space) (g:A->real) n` THEN
  ABBREV_TAC `hn = \n:num. (\x:A. (fn:num->A->real) n x + (gn:num->A->real) n x)` THEN
  (* fn are simple *)
  SUBGOAL_THEN `!n. simple_rv (p:A prob_space) ((fn:num->A->real) n)` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "fn" THEN BETA_TAC THEN
   MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_SIMPLE_RV THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* gn are simple *)
  SUBGOAL_THEN `!n. simple_rv (p:A prob_space) ((gn:num->A->real) n)` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "gn" THEN BETA_TAC THEN
   MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_SIMPLE_RV THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* hn are simple *)
  SUBGOAL_THEN `!n. simple_rv (p:A prob_space) ((hn:num->A->real) n)` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "hn" THEN BETA_TAC THEN
   MATCH_MP_TAC SIMPLE_RV_ADD THEN ASM_REWRITE_TAC[ETA_AX];
   ALL_TAC] THEN
  (* fn are nonneg *)
  SUBGOAL_THEN `!n x:A. x IN prob_carrier p ==> &0 <= (fn:num->A->real) n x`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "fn" THEN BETA_TAC THEN
   REWRITE_TAC[NONNEG_SIMPLE_FN_APPROX_NONNEG];
   ALL_TAC] THEN
  (* gn are nonneg *)
  SUBGOAL_THEN `!n x:A. x IN prob_carrier p ==> &0 <= (gn:num->A->real) n x`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "gn" THEN BETA_TAC THEN
   REWRITE_TAC[NONNEG_SIMPLE_FN_APPROX_NONNEG];
   ALL_TAC] THEN
  (* hn are nonneg *)
  SUBGOAL_THEN `!n x:A. x IN prob_carrier p ==> &0 <= (hn:num->A->real) n x`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "hn" THEN BETA_TAC THEN
   MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  (* fn are increasing *)
  SUBGOAL_THEN `!n x:A. x IN prob_carrier p ==> (fn:num->A->real) n x <= fn (SUC n) x`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "fn" THEN BETA_TAC THEN
   MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_MONO THEN ASM_SIMP_TAC[LE; LE_REFL];
   ALL_TAC] THEN
  (* gn are increasing *)
  SUBGOAL_THEN `!n x:A. x IN prob_carrier p ==> (gn:num->A->real) n x <= gn (SUC n) x`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "gn" THEN BETA_TAC THEN
   MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_MONO THEN ASM_SIMP_TAC[LE; LE_REFL];
   ALL_TAC] THEN
  (* hn are increasing *)
  SUBGOAL_THEN `!n x:A. x IN prob_carrier p ==> (hn:num->A->real) n x <= hn (SUC n) x`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "hn" THEN BETA_TAC THEN
   MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  (* fn converges to f *)
  SUBGOAL_THEN `!x:A. x IN prob_carrier p ==>
    ((\n. (fn:num->A->real) n x) ---> (f:A->real) x) sequentially`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "fn" THEN BETA_TAC THEN
   MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_CONVERGES THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  (* gn converges to g *)
  SUBGOAL_THEN `!x:A. x IN prob_carrier p ==>
    ((\n. (gn:num->A->real) n x) ---> (g:A->real) x) sequentially`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "gn" THEN BETA_TAC THEN
   MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_CONVERGES THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  (* hn converges to f + g *)
  SUBGOAL_THEN `!x:A. x IN prob_carrier p ==>
    ((\n. (hn:num->A->real) n x) ---> (f:A->real) x + (g:A->real) x) sequentially`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "hn" THEN BETA_TAC THEN
   MATCH_MP_TAC REALLIM_ADD THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  (* MCT for fn: E[fn n] -> nn_exp(f) *)
  SUBGOAL_THEN `((\n. simple_expectation (p:A prob_space) ((fn:num->A->real) n))
    ---> nn_expectation p f) sequentially` ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_MCT_NN_EXPECTATION THEN
   ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* MCT for gn: E[gn n] -> nn_exp(g) *)
  SUBGOAL_THEN `((\n. simple_expectation (p:A prob_space) ((gn:num->A->real) n))
    ---> nn_expectation p g) sequentially` ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_MCT_NN_EXPECTATION THEN
   ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* MCT for hn: E[hn n] -> nn_exp(f + g) *)
  SUBGOAL_THEN `((\n. simple_expectation (p:A prob_space) ((hn:num->A->real) n))
    ---> nn_expectation p (\x. f x + g x)) sequentially` ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_MCT_NN_EXPECTATION THEN
   ASM_REWRITE_TAC[] THEN
   EXISTS_TAC `Bf + Bg:real` THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  (* E[hn n] = E[fn n] + E[gn n] *)
  SUBGOAL_THEN `!n. simple_expectation (p:A prob_space) ((hn:num->A->real) n) =
    simple_expectation p ((fn:num->A->real) n) + simple_expectation p ((gn:num->A->real) n)`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   SUBGOAL_THEN `(hn:num->A->real) n = (\x:A. fn n x + gn n x)` SUBST1_TAC THENL
   [EXPAND_TAC "hn" THEN REFL_TAC; ALL_TAC] THEN
   MATCH_MP_TAC SIMPLE_EXPECTATION_ADD THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* E[fn n] + E[gn n] -> nn_exp(f) + nn_exp(g) *)
  SUBGOAL_THEN `((\n. simple_expectation (p:A prob_space) ((fn:num->A->real) n) +
    simple_expectation p ((gn:num->A->real) n))
    ---> nn_expectation p f + nn_expectation p g) sequentially`
    ASSUME_TAC THENL
  [MATCH_MP_TAC REALLIM_ADD THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Both limits are the same sequence, so apply uniqueness *)
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC `\n:num. simple_expectation (p:A prob_space) ((hn:num->A->real) n)` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  CONJ_TAC THENL
  [ASM_REWRITE_TAC[];
   ASM_REWRITE_TAC[ETA_AX]]);;

(* ========================================================================= *)
(* Independence-expectation bridge: point mass independence, product         *)
(* expectations, covariance. (Moved from characteristic_functions.ml.)       *)
(* ========================================================================= *)

(* ========================================================================= *)
(* Independence: CDF to point mass bridge                                    *)
(* ========================================================================= *)

(* Algebraic identity for inclusion-exclusion factoring *)
let REAL_SUB_MUL_FACTOR = prove
 (`!a b c d:real.
     a * c - b * c - (a * d - b * d) = (a - b) * (c - d)`,
  CONV_TAC REAL_RING);;

(* For simple RVs, there's a gap below each value in the finite range.
   This lets us find a threshold 'a' such that X <= a iff X < u on Omega. *)
let SIMPLE_RV_GAP_BELOW = prove
 (`!p:A prob_space (X:A->real) u.
     simple_rv p X
     ==> ?a. !x. x IN prob_carrier p ==> (X x <= a <=> X x < u)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simple_rv]) THEN
  SUBGOAL_THEN `FINITE (IMAGE (X:A->real) (prob_carrier p))` ASSUME_TAC THENL
  [ASM_SIMP_TAC[GSYM SIMPLE_IMAGE; FINITE_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN
    `FINITE {v:real | v IN IMAGE (X:A->real) (prob_carrier p) /\ v < u}`
    ASSUME_TAC THENL
  [MATCH_MP_TAC FINITE_SUBSET THEN
   EXISTS_TAC `IMAGE (X:A->real) (prob_carrier p)` THEN
   ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
   ALL_TAC] THEN
  ASM_CASES_TAC
    `{v:real | v IN IMAGE (X:A->real) (prob_carrier p) /\ v < u} = {}` THENL
  [(* Case: no value in range is < u, so X x >= u for all x *)
   EXISTS_TAC `u - &1` THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
   SUBGOAL_THEN `~((X:A->real) z < u)` MP_TAC THENL
   [SUBGOAL_THEN `(X:A->real) z IN IMAGE X (prob_carrier p)` MP_TAC THENL
    [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    UNDISCH_TAC
      `{v:real | v IN IMAGE (X:A->real) (prob_carrier p) /\ v < u} = {}` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    MESON_TAC[];
    ALL_TAC] THEN
   REAL_ARITH_TAC;
   (* Case: some values in range are < u; use sup as the gap threshold *)
   EXISTS_TAC
     `sup {v:real | v IN IMAGE (X:A->real) (prob_carrier p) /\ v < u}` THEN
   X_GEN_TAC `z:A` THEN DISCH_TAC THEN
   SUBGOAL_THEN `(X:A->real) z IN IMAGE X (prob_carrier p)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   MP_TAC(SPEC
     `{v:real | v IN IMAGE (X:A->real) (prob_carrier p) /\ v < u}`
     SUP_FINITE) THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[IN_ELIM_THM] THEN
   DISCH_THEN(CONJUNCTS_THEN2
     (CONJUNCTS_THEN2 (fun _ -> ALL_TAC) ASSUME_TAC)
     ASSUME_TAC) THEN
   EQ_TAC THENL
   [(* X z <= sup S ==> X z < u: since sup S < u *)
    DISCH_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC
      `sup {v:real | v IN IMAGE (X:A->real) (prob_carrier p) /\ v < u}` THEN
    CONJ_TAC THENL
    [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC];
    (* X z < u ==> X z <= sup S: X z is in the set, so <= sup *)
    DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    CONJ_TAC THENL
    [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC]]]);;

(* Key bridge lemma: CDF independence implies point mass independence
   for simple random variables *)
let INDEP_RV_POINT_MASS = prove
 (`!p:A prob_space (X:A->real) (Y:A->real) u v.
     simple_rv p X /\ simple_rv p Y /\ indep_rv p X Y
     ==> prob p {x | x IN prob_carrier p /\ X x = u /\ Y x = v} =
         prob p {x | x IN prob_carrier p /\ X x = u} *
         prob p {x | x IN prob_carrier p /\ Y x = v}`,
  REPEAT STRIP_TAC THEN
  (* Get gap thresholds a_X, a_Y *)
  MP_TAC(SPECL [`p:A prob_space`; `X:A->real`; `u:real`]
    SIMPLE_RV_GAP_BELOW) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `aX:real` (LABEL_TAC "Xgap")) THEN
  MP_TAC(SPECL [`p:A prob_space`; `Y:A->real`; `v:real`]
    SIMPLE_RV_GAP_BELOW) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `aY:real` (LABEL_TAC "Ygap")) THEN
  (* Establish set equalities using the gap property *)
  (* {X <= aX} = {X < u} on Omega *)
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ (X:A->real) x <= aX} =
     {x | x IN prob_carrier p /\ X x < u}`
    ASSUME_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  (* {Y <= aY} = {Y < v} on Omega *)
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ (Y:A->real) x <= aY} =
     {x | x IN prob_carrier p /\ Y x < v}`
    ASSUME_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  (* Measurability facts *)
  SUBGOAL_THEN `random_variable (p:A prob_space) (X:A->real)` ASSUME_TAC THENL
  [ASM_MESON_TAC[simple_rv]; ALL_TAC] THEN
  SUBGOAL_THEN `random_variable (p:A prob_space) (Y:A->real)` ASSUME_TAC THENL
  [ASM_MESON_TAC[simple_rv]; ALL_TAC] THEN
  (* Key events are measurable *)
  SUBGOAL_THEN
    `!a. {x:A | x IN prob_carrier p /\ (X:A->real) x <= a} IN prob_events p`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[random_variable]; ALL_TAC] THEN
  SUBGOAL_THEN
    `!b. {x:A | x IN prob_carrier p /\ (Y:A->real) x <= b} IN prob_events p`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[random_variable]; ALL_TAC] THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ (X:A->real) x = u} IN prob_events p`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[RANDOM_VARIABLE_LEVEL_SET]; ALL_TAC] THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ (Y:A->real) x = v} IN prob_events p`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[RANDOM_VARIABLE_LEVEL_SET]; ALL_TAC] THEN
  (* Use PROB_DIFF_SUBSET: {X=u} = {X<=u} DIFF {X<=aX} = {X<=u} DIFF {X<u} *)
  (* P(X=u) = P(X<=u) - P(X<=aX) *)
  SUBGOAL_THEN
    `prob p {x:A | x IN prob_carrier p /\ (X:A->real) x = u} =
     prob p {x | x IN prob_carrier p /\ X x <= u} -
     prob p {x | x IN prob_carrier p /\ X x <= aX}`
    ASSUME_TAC THENL
  [SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ (X:A->real) x = u} =
      {x | x IN prob_carrier p /\ X x <= u} DIFF
      {x | x IN prob_carrier p /\ X x <= aX}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF] THEN
    X_GEN_TAC `x:A` THEN
    ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "Xgap" (MP_TAC o SPEC `x:A`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   MATCH_MP_TAC PROB_DIFF_SUBSET THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
   X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   USE_THEN "Xgap" (MP_TAC o SPEC `x:A`) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* P(Y=v) = P(Y<=v) - P(Y<=aY) *)
  SUBGOAL_THEN
    `prob p {x:A | x IN prob_carrier p /\ (Y:A->real) x = v} =
     prob p {x | x IN prob_carrier p /\ Y x <= v} -
     prob p {x | x IN prob_carrier p /\ Y x <= aY}`
    ASSUME_TAC THENL
  [SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ (Y:A->real) x = v} =
      {x | x IN prob_carrier p /\ Y x <= v} DIFF
      {x | x IN prob_carrier p /\ Y x <= aY}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF] THEN
    X_GEN_TAC `x:A` THEN
    ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "Ygap" (MP_TAC o SPEC `x:A`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   MATCH_MP_TAC PROB_DIFF_SUBSET THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
   X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   USE_THEN "Ygap" (MP_TAC o SPEC `x:A`) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* Now for the joint: P(X=u,Y=v) = P(X<=u,Y<=v) - P(X<=aX,Y<=v)
                                     - P(X<=u,Y<=aY) + P(X<=aX,Y<=aY) *)
  (* Step 1: P(X=u,Y<=v) = P(X<=u,Y<=v) - P(X<=aX,Y<=v) *)
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ (X:A->real) x = u /\ (Y:A->real) x <= v} =
     {x | x IN prob_carrier p /\ X x <= u /\ Y x <= v} DIFF
     {x | x IN prob_carrier p /\ X x <= aX /\ Y x <= v}`
    ASSUME_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF] THEN
   X_GEN_TAC `x:A` THEN
   ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
   USE_THEN "Xgap" (MP_TAC o SPEC `x:A`) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Step 2: P(X=u,Y=v) = P(X=u,Y<=v) - P(X=u,Y<=aY) *)
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ (X:A->real) x = u /\ (Y:A->real) x = v} =
     {x | x IN prob_carrier p /\ X x = u /\ Y x <= v} DIFF
     {x | x IN prob_carrier p /\ X x = u /\ Y x <= aY}`
    ASSUME_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF] THEN
   X_GEN_TAC `x:A` THEN
   ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
   USE_THEN "Ygap" (MP_TAC o SPEC `x:A`) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Similarly: {X=u,Y<=aY} = {X<=u,Y<=aY} DIFF {X<=aX,Y<=aY} *)
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ (X:A->real) x = u /\ (Y:A->real) x <= aY} =
     {x | x IN prob_carrier p /\ X x <= u /\ Y x <= aY} DIFF
     {x | x IN prob_carrier p /\ X x <= aX /\ Y x <= aY}`
    ASSUME_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF] THEN
   X_GEN_TAC `x:A` THEN
   ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
   USE_THEN "Xgap" (MP_TAC o SPEC `x:A`) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Joint CDF sets are events (intersections of halfline events) *)
  SUBGOAL_THEN
    `!a b. {x:A | x IN prob_carrier p /\
                   (X:A->real) x <= a /\ (Y:A->real) x <= b} IN prob_events p`
    ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ (X:A->real) x <= a /\ (Y:A->real) x <= b} =
      {x | x IN prob_carrier p /\ X x <= a} INTER
      {x | x IN prob_carrier p /\ Y x <= b}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN MESON_TAC[];
    MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* Joint level-CDF sets are events *)
  SUBGOAL_THEN
    `!b. {x:A | x IN prob_carrier p /\
                 (X:A->real) x = u /\ (Y:A->real) x <= b} IN prob_events p`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ (X:A->real) x = u /\ (Y:A->real) x <= b} =
      {x | x IN prob_carrier p /\ X x = u} INTER
      {x | x IN prob_carrier p /\ Y x <= b}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN MESON_TAC[];
    MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* Subset: {X<=aX, Y<=v} SUBSET {X<=u, Y<=v} via gap property *)
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ (X:A->real) x <= aX /\ (Y:A->real) x <= v}
     SUBSET {x | x IN prob_carrier p /\ X x <= u /\ Y x <= v}`
    ASSUME_TAC THENL
  [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LT_IMP_LE THEN
   USE_THEN "Xgap" (MP_TAC o SPEC `x:A`) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* Subset: {X<=aX, Y<=aY} SUBSET {X<=u, Y<=aY} via gap property *)
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ (X:A->real) x <= aX /\ (Y:A->real) x <= aY}
     SUBSET {x | x IN prob_carrier p /\ X x <= u /\ Y x <= aY}`
    ASSUME_TAC THENL
  [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LT_IMP_LE THEN
   USE_THEN "Xgap" (MP_TAC o SPEC `x:A`) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* Subset: {X=u, Y<=aY} SUBSET {X=u, Y<=v} via gap property *)
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ (X:A->real) x = u /\ (Y:A->real) x <= aY}
     SUBSET {x | x IN prob_carrier p /\ X x = u /\ Y x <= v}`
    ASSUME_TAC THENL
  [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LT_IMP_LE THEN
   USE_THEN "Ygap" (MP_TAC o SPEC `x:A`) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* Compute P(X=u,Y<=v) = P(X<=u,Y<=v) - P(X<=aX,Y<=v) *)
  SUBGOAL_THEN
    `prob (p:A prob_space) {x:A | x IN prob_carrier p /\
       (X:A->real) x = u /\ (Y:A->real) x <= v} =
     prob p {x | x IN prob_carrier p /\ X x <= u /\ Y x <= v} -
     prob p {x | x IN prob_carrier p /\ X x <= aX /\ Y x <= v}`
    ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `{x:A | x IN prob_carrier p /\ (X:A->real) x <= aX /\ (Y:A->real) x <= v}`;
     `{x:A | x IN prob_carrier p /\ (X:A->real) x <= u /\ (Y:A->real) x <= v}`]
     PROB_DIFF_SUBSET) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN ACCEPT_TAC;
   ALL_TAC] THEN
  (* Compute P(X=u,Y<=aY) = P(X<=u,Y<=aY) - P(X<=aX,Y<=aY) *)
  SUBGOAL_THEN
    `prob (p:A prob_space) {x:A | x IN prob_carrier p /\
       (X:A->real) x = u /\ (Y:A->real) x <= aY} =
     prob p {x | x IN prob_carrier p /\ X x <= u /\ Y x <= aY} -
     prob p {x | x IN prob_carrier p /\ X x <= aX /\ Y x <= aY}`
    ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `{x:A | x IN prob_carrier p /\ (X:A->real) x <= aX /\ (Y:A->real) x <= aY}`;
     `{x:A | x IN prob_carrier p /\ (X:A->real) x <= u /\ (Y:A->real) x <= aY}`]
     PROB_DIFF_SUBSET) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN ACCEPT_TAC;
   ALL_TAC] THEN
  (* Compute P(X=u,Y=v) = P(X=u,Y<=v) - P(X=u,Y<=aY) *)
  SUBGOAL_THEN
    `prob (p:A prob_space) {x:A | x IN prob_carrier p /\
       (X:A->real) x = u /\ (Y:A->real) x = v} =
     prob p {x | x IN prob_carrier p /\ X x = u /\ Y x <= v} -
     prob p {x | x IN prob_carrier p /\ X x = u /\ Y x <= aY}`
    ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `{x:A | x IN prob_carrier p /\ (X:A->real) x = u /\ (Y:A->real) x <= aY}`;
     `{x:A | x IN prob_carrier p /\ (X:A->real) x = u /\ (Y:A->real) x <= v}`]
     PROB_DIFF_SUBSET) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN ACCEPT_TAC;
   ALL_TAC] THEN
  (* Use CDF independence: P(X<=a,Y<=b) = P(X<=a)*P(Y<=b) *)
  SUBGOAL_THEN
    `!a b. prob (p:A prob_space) {x:A | x IN prob_carrier p /\
             (X:A->real) x <= a /\ (Y:A->real) x <= b} =
           prob p {x | x IN prob_carrier p /\ X x <= a} *
           prob p {x | x IN prob_carrier p /\ Y x <= b}`
    ASSUME_TAC THENL
  [UNDISCH_TAC `indep_rv (p:A prob_space) (X:A->real) (Y:A->real)` THEN
   REWRITE_TAC[indep_rv] THEN MESON_TAC[];
   ALL_TAC] THEN
  (* Substitute all CDF terms and factor algebraically:
     (P(X<=u) - P(X<=aX)) * (P(Y<=v) - P(Y<=aY)) = P(X=u) * P(Y=v) *)
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_SUB_MUL_FACTOR]);;


let REAL_MUL_4_FACTOR = prove
 (`!a:real b c d. a * b * (c * d) = (a * c) * (b * d)`,
  REPEAT GEN_TAC THEN CONV_TAC REAL_RING);;

(* Event {X=u, Y=v} is in prob_events for simple RVs *)
let SIMPLE_RV_LEVEL_SET_INTER_IN_EVENTS = prove
 (`!p:A prob_space (X:A->real) (Y:A->real) (u:real) (v:real).
    simple_rv p X /\ simple_rv p Y
    ==> {z | z IN prob_carrier p /\ X z = u /\ Y z = v} IN prob_events p`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `{z:A | z IN prob_carrier p /\ (X:A->real) z = (u:real) /\ (Y:A->real) z = (v:real)} =
     {z | z IN prob_carrier p /\ X z = u} INTER
     {z | z IN prob_carrier p /\ Y z = v}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN
   GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN CONJ_TAC THEN
   MATCH_MP_TAC RANDOM_VARIABLE_LEVEL_SET THEN
   ASM_MESON_TAC[simple_rv]]);;

(* Helper: simple_rv for u*v*indicator of a joint level set *)
let SIMPLE_RV_CMUL_INDICATOR_PAIR = prove
 (`!p:A prob_space (X:A->real) (Y:A->real) (u:real) (v:real).
    simple_rv p X /\ simple_rv p Y
    ==> simple_rv p (\x. u * v *
          indicator_fn {z | z IN prob_carrier p /\ X z = u /\ Y z = v} x)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SIMPLE_RV_CMUL THEN
  MATCH_MP_TAC SIMPLE_RV_CMUL THEN
  REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
  MATCH_MP_TAC SIMPLE_RV_LEVEL_SET_INTER_IN_EVENTS THEN
  ASM_REWRITE_TAC[]);;

(* Helper: E[u*v*indicator A] = u*v*P(A) *)
let SIMPLE_EXPECTATION_CMUL_INDICATOR_PAIR = prove
 (`!p:A prob_space (X:A->real) (Y:A->real) (u:real) (v:real).
    simple_rv p X /\ simple_rv p Y
    ==> simple_expectation p (\x. u * v *
          indicator_fn {z | z IN prob_carrier p /\ X z = u /\ Y z = v} x) =
        u * v * prob p {z | z IN prob_carrier p /\ X z = u /\ Y z = v}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `{z:A | z IN prob_carrier p /\ (X:A->real) z = (u:real) /\
     (Y:A->real) z = (v:real)} IN prob_events p`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_LEVEL_SET_INTER_IN_EVENTS THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Convert u*(v*I) to (u*v)*I using SIMPLE_EXPECTATION_EXT + REAL_MUL_ASSOC *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space) (\x. u * v *
       indicator_fn {z | z IN prob_carrier p /\ (X:A->real) z = u /\
         (Y:A->real) z = v} x) =
     simple_expectation p (\x. (u * v) *
       indicator_fn {z | z IN prob_carrier p /\ X z = u /\ Y z = v} x)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
   REWRITE_TAC[REAL_MUL_ASSOC]; ALL_TAC] THEN
  (* Apply SIMPLE_EXPECTATION_CMUL with c = u*v *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space) (\x. (u * v) *
       indicator_fn {z | z IN prob_carrier p /\ (X:A->real) z = u /\
         (Y:A->real) z = v} x) =
     (u * v) * simple_expectation p
       (indicator_fn {z | z IN prob_carrier p /\ X z = u /\ Y z = v})`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_CMUL THEN REWRITE_TAC[ETA_AX] THEN
   MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Apply SIMPLE_EXPECTATION_INDICATOR *)
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SIMPLE_EXPECTATION_INDICATOR THEN ASM_REWRITE_TAC[]);;

(* Pointwise: X(x)*Y(x) = double sum of u*v*indicator_{X=u,Y=v}(x) *)
let SIMPLE_RV_PRODUCT_SUM_INDICATOR = prove
 (`!p:A prob_space (X:A->real) (Y:A->real) x.
     simple_rv p X /\ simple_rv p Y /\ x IN prob_carrier p
     ==> X x * Y x =
         sum (IMAGE X (prob_carrier p)) (\u.
           sum (IMAGE Y (prob_carrier p)) (\v.
             u * v * indicator_fn
               {z | z IN prob_carrier p /\ X z = u /\ Y z = v} x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (IMAGE (X:A->real) (prob_carrier p))` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN ASM_MESON_TAC[simple_rv]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (IMAGE (Y:A->real) (prob_carrier p))` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN ASM_MESON_TAC[simple_rv]; ALL_TAC] THEN
  SUBGOAL_THEN `(X:A->real) x IN IMAGE X (prob_carrier p)` ASSUME_TAC THENL
  [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `(Y:A->real) x IN IMAGE Y (prob_carrier p)` ASSUME_TAC THENL
  [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN
  (* Convert indicator to conditional *)
  SUBGOAL_THEN
    `!u v. u * v * indicator_fn
        {z:A | z IN prob_carrier p /\ (X:A->real) z = u /\ (Y:A->real) z = v} x =
      if X x = u /\ Y x = v then u * v else &0`
    (fun th -> REWRITE_TAC[th]) THENL
  [REPEAT GEN_TAC THEN REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
   ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Inner sum: collapse v-sum *)
  SUBGOAL_THEN
    `!u:real. sum (IMAGE (Y:A->real) (prob_carrier p))
        (\v. if (X:A->real) x = u /\ Y x = v then u * v else &0) =
      if X x = u then u * Y x else &0`
    (fun th -> REWRITE_TAC[th]) THENL
  [X_GEN_TAC `u:real` THEN
   ASM_CASES_TAC `(X:A->real) x = u` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum (IMAGE (Y:A->real) (prob_carrier p))
                    (\v. if v = Y x then u * Y x else &0)` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `v:real` THEN DISCH_TAC THEN
     BETA_TAC THEN
     ASM_CASES_TAC `(Y:A->real) x = v` THENL
     [ASM_REWRITE_TAC[];
      SUBGOAL_THEN `~(v:real = (Y:A->real) x)` ASSUME_TAC THENL
      [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]]];
     REWRITE_TAC[SUM_DELTA] THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[SUM_0]];
   ALL_TAC] THEN
  (* Outer sum: collapse u-sum *)
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum (IMAGE (X:A->real) (prob_carrier p))
                  (\u. if u = X x then X x * (Y:A->real) x else &0)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN
   BETA_TAC THEN
   ASM_CASES_TAC `(X:A->real) x = u` THENL
   [ASM_REWRITE_TAC[];
    SUBGOAL_THEN `~(u:real = (X:A->real) x)` ASSUME_TAC THENL
    [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]]];
   REWRITE_TAC[SUM_DELTA] THEN ASM_REWRITE_TAC[]]);;

(* Closure of simple_rv under finite sums *)
let SIMPLE_RV_SUM_FINITE = prove
 (`!p:A prob_space (f:B->A->real) s.
    FINITE s /\ (!i. i IN s ==> simple_rv p (f i))
    ==> simple_rv p (\x. sum s (\i. f i x))`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
  [DISCH_TAC THEN REWRITE_TAC[SUM_CLAUSES] THEN
   REWRITE_TAC[SIMPLE_RV_CONST];
   MAP_EVERY X_GEN_TAC [`a:B`; `t:B->bool`] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
   DISCH_TAC THEN
   ASM_SIMP_TAC[SUM_CLAUSES] THEN
   SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. sum t (\i. (f:B->A->real) i x))`
     ASSUME_TAC THENL
   [USE_THEN "IH" MATCH_MP_TAC THEN ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
   SUBGOAL_THEN `simple_rv (p:A prob_space) ((f:B->A->real) a)` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `(f:B->A->real) a`;
                   `\x:A. sum t (\i. (f:B->A->real) i x)`] SIMPLE_RV_ADD) THEN
   ASM_REWRITE_TAC[]]);;

(* Linearity of expectation for sums over finite sets *)
let SIMPLE_EXPECTATION_SUM_FINITE = prove
 (`!p:A prob_space (f:B->A->real) s.
    FINITE s /\ (!i. i IN s ==> simple_rv p (f i))
    ==> simple_expectation p (\x. sum s (\i. f i x)) =
        sum s (\i. simple_expectation p (f i))`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
  [DISCH_TAC THEN REWRITE_TAC[SUM_CLAUSES] THEN
   REWRITE_TAC[SIMPLE_EXPECTATION_CONST];
   MAP_EVERY X_GEN_TAC [`a:B`; `t:B->bool`] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
   DISCH_TAC THEN ASM_SIMP_TAC[SUM_CLAUSES] THEN
   SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. sum t (\i. (f:B->A->real) i x))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_SUM_FINITE THEN ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
   SUBGOAL_THEN `simple_rv (p:A prob_space) ((f:B->A->real) a)` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `(f:B->A->real) a`;
                   `\x:A. sum t (\i. (f:B->A->real) i x)`]
                  SIMPLE_EXPECTATION_ADD) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   AP_TERM_TAC THEN USE_THEN "IH" MATCH_MP_TAC THEN
   ASM_MESON_TAC[IN_INSERT]]);;

(* E[X*Y] as double sum of u*v*P(X=u,Y=v) for simple RVs *)
let SIMPLE_EXPECTATION_PRODUCT_DOUBLE_SUM = prove
 (`!p:A prob_space (X:A->real) (Y:A->real).
     simple_rv p X /\ simple_rv p Y
     ==> simple_expectation p (\x. X x * Y x) =
         sum (IMAGE X (prob_carrier p)) (\u.
           sum (IMAGE Y (prob_carrier p)) (\v.
             u * v * prob p {z | z IN prob_carrier p /\ X z = u /\ Y z = v}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `RX = IMAGE (X:A->real) (prob_carrier p)` THEN
  ABBREV_TAC `RY = IMAGE (Y:A->real) (prob_carrier p)` THEN
  SUBGOAL_THEN `FINITE (RX:real->bool)` ASSUME_TAC THENL
  [EXPAND_TAC "RX" THEN REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
   ASM_MESON_TAC[simple_rv]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (RY:real->bool)` ASSUME_TAC THENL
  [EXPAND_TAC "RY" THEN REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
   ASM_MESON_TAC[simple_rv]; ALL_TAC] THEN
  (* Step a: E[XY] = E[double sum of indicators] by SIMPLE_EXPECTATION_EXT *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space) (\x. (X:A->real) x * (Y:A->real) x) =
     simple_expectation p (\x. sum (RX:real->bool) (\u:real. sum (RY:real->bool)
       (\v:real. u * v * indicator_fn
         {z | z IN prob_carrier p /\ X z = u /\ Y z = v} x)))`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
   EXPAND_TAC "RX" THEN EXPAND_TAC "RY" THEN
   MATCH_MP_TAC SIMPLE_RV_PRODUCT_SUM_INDICATOR THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Steps b-d: E[double sum of indicators] = double sum of u*v*P *)
  (* We need to push E through two sums and apply CMUL_INDICATOR_PAIR *)
  (* Use ISPECL to avoid higher-order matching issues with MATCH_MP_TAC *)
  MP_TAC(ISPECL
    [`p:A prob_space`;
     `\(u:real) (x:A). sum (RY:real->bool) (\(v:real). u * v *
        indicator_fn {z:A | z IN prob_carrier (p:A prob_space) /\
          (X:A->real) z = u /\ (Y:A->real) z = v} x)`;
     `RX:real->bool`]
    SIMPLE_EXPECTATION_SUM_FINITE) THEN
  BETA_TAC THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN
   MP_TAC(ISPECL
     [`p:A prob_space`;
      `\(v:real) (x:A). (u:real) * v *
         indicator_fn {z:A | z IN prob_carrier (p:A prob_space) /\
           (X:A->real) z = u /\ (Y:A->real) z = v} x`;
      `RY:real->bool`]
     SIMPLE_RV_SUM_FINITE) THEN
   BETA_TAC THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC SIMPLE_RV_CMUL_INDICATOR_PAIR THEN ASM_REWRITE_TAC[];
    DISCH_THEN ACCEPT_TAC];
   ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  (* Now goal: sum RX (\u. E[\x. sum RY ...]) = sum RX (\u. sum RY (\v. u*v*P)) *)
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN
  BETA_TAC THEN
  (* Push E through inner sum *)
  MP_TAC(ISPECL
    [`p:A prob_space`;
     `\(v:real) (x:A). (u:real) * v *
        indicator_fn {z:A | z IN prob_carrier (p:A prob_space) /\
          (X:A->real) z = u /\ (Y:A->real) z = v} x`;
     `RY:real->bool`]
    SIMPLE_EXPECTATION_SUM_FINITE) THEN
  BETA_TAC THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real` THEN DISCH_TAC THEN
   MATCH_MP_TAC SIMPLE_RV_CMUL_INDICATOR_PAIR THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  (* Now: sum RY (\v. E[u*v*I]) = sum RY (\v. u*v*P) *)
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `v:real` THEN DISCH_TAC THEN
  BETA_TAC THEN EXPAND_TAC "RX" THEN EXPAND_TAC "RY" THEN
  MATCH_MP_TAC SIMPLE_EXPECTATION_CMUL_INDICATOR_PAIR THEN
  ASM_REWRITE_TAC[]);;

(* E[X*Y] = E[X]*E[Y] for independent simple random variables *)
let SIMPLE_EXPECTATION_PRODUCT_INDEP = prove
 (`!p:A prob_space (X:A->real) (Y:A->real).
    simple_rv p X /\ simple_rv p Y /\ indep_rv p X Y
    ==> simple_expectation p (\x. X x * Y x) =
        simple_expectation p X * simple_expectation p Y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `RX = IMAGE (X:A->real) (prob_carrier p)` THEN
  ABBREV_TAC `RY = IMAGE (Y:A->real) (prob_carrier p)` THEN
  SUBGOAL_THEN `FINITE (RX:real->bool)` ASSUME_TAC THENL
  [EXPAND_TAC "RX" THEN REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
   ASM_MESON_TAC[simple_rv]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (RY:real->bool)` ASSUME_TAC THENL
  [EXPAND_TAC "RY" THEN REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
   ASM_MESON_TAC[simple_rv]; ALL_TAC] THEN
  (* Step 1: E[XY] = sum_u sum_v u*v*P(X=u,Y=v) *)
  SUBGOAL_THEN
    `simple_expectation p (\x. X x * Y x) =
     sum (RX:real->bool) (\u:real. sum (RY:real->bool) (\v:real. u * v *
       prob (p:A prob_space) {z | z IN prob_carrier p /\ X z = u /\ Y z = v}))`
    SUBST1_TAC THENL
  [EXPAND_TAC "RX" THEN EXPAND_TAC "RY" THEN
   MATCH_MP_TAC SIMPLE_EXPECTATION_PRODUCT_DOUBLE_SUM THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Step 2: Apply independence: P(X=u,Y=v) = P(X=u)*P(Y=v) *)
  SUBGOAL_THEN
    `sum (RX:real->bool) (\u:real. sum (RY:real->bool) (\v:real. u * v *
       prob (p:A prob_space) {z | z IN prob_carrier p /\ X z = u /\ Y z = v})) =
     sum RX (\u. sum RY (\v. u * v *
       (prob p {z | z IN prob_carrier p /\ X z = u} *
        prob p {z | z IN prob_carrier p /\ Y z = v})))`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN
   BETA_TAC THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `v:real` THEN
   DISCH_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
   MATCH_MP_TAC INDEP_RV_POINT_MASS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Step 3: Factor the double sum into product of sums *)
  (* Use explicit parens: (u * prob{X=u}) * sum RY ... *)
  SUBGOAL_THEN
    `!u:real. sum (RY:real->bool) (\v:real. u * v *
       prob (p:A prob_space) {z | z IN prob_carrier p /\ X z = u} *
       prob p {z | z IN prob_carrier p /\ Y z = v}) =
     (u * prob p {z | z IN prob_carrier p /\ X z = u}) *
     sum RY (\v. v * prob p {z | z IN prob_carrier p /\ Y z = v})`
    (fun th -> REWRITE_TAC[th]) THENL
  [GEN_TAC THEN
   SUBGOAL_THEN
     `(\v:real. (u:real) * v *
        prob (p:A prob_space) {z | z IN prob_carrier p /\ X z = u} *
        prob p {z | z IN prob_carrier p /\ Y z = v}) =
      (\v. (u * prob p {z | z IN prob_carrier p /\ X z = u}) *
           (v * prob p {z | z IN prob_carrier p /\ Y z = v}))`
     SUBST1_TAC THENL
   [ABS_TAC THEN REWRITE_TAC[REAL_MUL_4_FACTOR]; REWRITE_TAC[SUM_LMUL]];
   REWRITE_TAC[SUM_RMUL]] THEN
  (* Step 4: Recognize as E[X]*E[Y] via simple_expectation definition *)
  EXPAND_TAC "RX" THEN EXPAND_TAC "RY" THEN
  REWRITE_TAC[simple_expectation; SET_IN_SIMP]);;

(* Covariance expansion: Cov(X,Y) = E[XY] - E[X]*E[Y] *)
let SIMPLE_COVARIANCE_ALT = prove
 (`!p:A prob_space (X:A->real) (Y:A->real).
     simple_rv p X /\ simple_rv p Y
     ==> simple_covariance p X Y =
         simple_expectation p (\x. X x * Y x) -
         simple_expectation p X * simple_expectation p Y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[simple_covariance] THEN
  ABBREV_TAC `mx = simple_expectation (p:A prob_space) (X:A->real)` THEN
  ABBREV_TAC `my = simple_expectation (p:A prob_space) (Y:A->real)` THEN
  SUBGOAL_THEN
    `(\x:A. ((X:A->real) x - mx) * ((Y:A->real) x - my)) =
     (\x. X x * Y x + (-- mx) * Y x + (-- my) * X x + mx * my)`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. (X:A->real) x * (Y:A->real) x)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. (-- mx) * (Y:A->real) x)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. (-- my) * (X:A->real) x)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. mx * my :real)`
    ASSUME_TAC THENL
  [REWRITE_TAC[SIMPLE_RV_CONST]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. (-- my) * (X:A->real) x + mx * my)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space)
    (\x:A. (-- mx) * (Y:A->real) x + (-- my) * (X:A->real) x + mx * my)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
       (\x:A. (X:A->real) x * Y x + (-- mx) * Y x + (-- my) * X x + mx * my) =
     simple_expectation p (\x. X x * Y x) +
     simple_expectation p (\x. (-- mx) * Y x + (-- my) * X x + mx * my)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
       (\x:A. (-- mx) * (Y:A->real) x + (-- my) * (X:A->real) x + mx * my) =
     simple_expectation p (\x. (-- mx) * Y x) +
     simple_expectation p (\x. (-- my) * X x + mx * my)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
       (\x:A. (-- my) * (X:A->real) x + mx * my) =
     simple_expectation p (\x. (-- my) * X x) +
     simple_expectation p (\x:A. mx * my :real)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `Y:A->real`; `--(mx:real)`]
    SIMPLE_EXPECTATION_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `--(my:real)`]
    SIMPLE_EXPECTATION_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[SIMPLE_EXPECTATION_CONST] THEN
  EXPAND_TAC "mx" THEN EXPAND_TAC "my" THEN REAL_ARITH_TAC);;

(* Independence implies zero covariance *)
let SIMPLE_COVARIANCE_INDEP = prove
 (`!p:A prob_space (X:A->real) (Y:A->real).
     simple_rv p X /\ simple_rv p Y /\ indep_rv p X Y
     ==> simple_covariance p X Y = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SIMPLE_COVARIANCE_ALT] THEN
  ASM_SIMP_TAC[SIMPLE_EXPECTATION_PRODUCT_INDEP] THEN
  REAL_ARITH_TAC);;


(* ========================================================================= *)
(* Part 4: General expectation theory for integrable random variables.       *)
(* Extends simple expectation to general integrable functions: variance,     *)
(* covariance, Chebyshev/Markov inequalities, LLN, Jensen, convergence.      *)
(* ========================================================================= *)

(* ========================================================================= *)
(* Phase 6: General Variance, Characteristic Functions, CDF                  *)
(* ========================================================================= *)

(* General variance using general expectation *)
let variance = new_definition
  `variance (p:A prob_space) (X:A->real) =
   expectation p (\x. (X x - expectation p X) pow 2)`;;

(* General characteristic function (real and imaginary parts) *)
let gen_char_fn_re = new_definition
  `gen_char_fn_re (p:A prob_space) (X:A->real) (t:real) =
   expectation p (\x. cos(t * X x))`;;

let gen_char_fn_im = new_definition
  `gen_char_fn_im (p:A prob_space) (X:A->real) (t:real) =
   expectation p (\x. sin(t * X x))`;;

(* General CDF *)
let gen_cdf = new_definition
  `gen_cdf (p:A prob_space) (X:A->real) (x:real) =
   prob p {a | a IN prob_carrier p /\ X a <= x}`;;

(* Bounded random variables are integrable *)
let INTEGRABLE_BOUNDED = prove
 (`!p:A prob_space f M.
      random_variable p f /\ (!x. x IN prob_carrier p ==> abs(f x) <= M)
      ==> integrable p f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[integrable] THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `M:real` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simple_expectation (p:A prob_space) g <=
                simple_expectation p (\x:A. M)` MP_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
   ASM_REWRITE_TAC[SIMPLE_RV_CONST] THEN
   X_GEN_TAC `z:A` THEN DISCH_TAC THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((f:A->real) z)` THEN
   ASM_SIMP_TAC[];
   REWRITE_TAC[SIMPLE_EXPECTATION_CONST]]);;

(* Agreement: variance = simple_variance for simple RVs *)
let VARIANCE_SIMPLE = prove
 (`!p:A prob_space X. simple_rv p X ==> variance p X = simple_variance p X`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[variance] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. ((X:A->real) x - expectation p X) pow 2) =
                simple_expectation p (\x. (X x - expectation p X) pow 2)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN
   MATCH_MP_TAC SIMPLE_RV_SQUARE THEN MATCH_MP_TAC SIMPLE_RV_SUB THEN
   ASM_REWRITE_TAC[SIMPLE_RV_CONST];
   ALL_TAC] THEN
  REWRITE_TAC[simple_variance] THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN
  MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Phase 6b: Properties of general expectation and variance                  *)
(* ========================================================================= *)

(* nn_expectation extensionality: equal on carrier implies equal nn_expectation *)
let NN_EXPECTATION_EXT = prove
 (`!p:A prob_space f g.
    (!x. x IN prob_carrier p ==> f x = g x)
    ==> nn_expectation p f = nn_expectation p g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nn_expectation] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
  EQ_TAC THEN STRIP_TAC THEN EXISTS_TAC `g':A->real` THEN
  ASM_REWRITE_TAC[] THENL
  [GEN_TAC THEN DISCH_TAC THEN
   SUBGOAL_THEN `(f:A->real) x' = (g:A->real) x'` MP_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `(g':A->real) x' <= (f:A->real) x'` MP_TAC THENL
   [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
   GEN_TAC THEN DISCH_TAC THEN
   SUBGOAL_THEN `(f:A->real) x' = (g:A->real) x'` MP_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `(g':A->real) x' <= (g:A->real) x'` MP_TAC THENL
   [ASM_SIMP_TAC[]; REAL_ARITH_TAC]]);;

(* nn_expectation is nonneg for bounded nonneg functions *)
let NN_EXPECTATION_POS = prove
 (`!p:A prob_space f.
    (!x. x IN prob_carrier p ==> &0 <= f x) /\
    (?B. !x. x IN prob_carrier p ==> f x <= B)
    ==> &0 <= nn_expectation p f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `nn_expectation (p:A prob_space) (\x:A. &0) <= nn_expectation p f`
    MP_TAC THENL
  [MATCH_MP_TAC BOUNDED_NN_EXPECTATION_MONO THEN
   REWRITE_TAC[REAL_LE_REFL] THEN ASM_SIMP_TAC[] THEN
   EXISTS_TAC `B:real` THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `nn_expectation (p:A prob_space) (\x:A. &0) = &0` (fun th ->
    REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `nn_expectation (p:A prob_space) (\x:A. &0) =
    simple_expectation p (\x:A. &0)` SUBST1_TAC THENL
  [MATCH_MP_TAC NN_EXPECTATION_SIMPLE THEN
   REWRITE_TAC[SIMPLE_RV_CONST; REAL_LE_REFL];
   REWRITE_TAC[SIMPLE_EXPECTATION_CONST]]);;

(* Expectation extensionality *)
let EXPECTATION_EXT = prove
 (`!p:A prob_space f g.
    (!x. x IN prob_carrier p ==> f x = g x)
    ==> expectation p f = expectation p g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[expectation] THEN
  SUBGOAL_THEN `nn_expectation (p:A prob_space) (\x. max ((f:A->real) x) (&0)) =
                nn_expectation p (\x. max (g x) (&0))` SUBST1_TAC THENL
  [MATCH_MP_TAC NN_EXPECTATION_EXT THEN GEN_TAC THEN DISCH_TAC THEN
   ASM_SIMP_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `nn_expectation (p:A prob_space) (\x. max (--((f:A->real) x)) (&0)) =
                nn_expectation p (\x. max (--(g x)) (&0))` SUBST1_TAC THENL
  [MATCH_MP_TAC NN_EXPECTATION_EXT THEN GEN_TAC THEN DISCH_TAC THEN
   ASM_SIMP_TAC[];
   REFL_TAC]);;

(* Expectation of a constant *)
let EXPECTATION_CONST = prove
 (`!p:A prob_space c. expectation p (\x. c) = c`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. c:real)` ASSUME_TAC THENL
  [REWRITE_TAC[SIMPLE_RV_CONST]; ALL_TAC] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. c:real) =
    simple_expectation p (\x. c)` SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[SIMPLE_EXPECTATION_CONST]]);;

(* Expectation is nonneg for bounded nonneg functions *)
let BOUNDED_EXPECTATION_POS = prove
 (`!p:A prob_space f.
    (!x. x IN prob_carrier p ==> &0 <= f x) /\
    (?B. !x. x IN prob_carrier p ==> f x <= B)
    ==> &0 <= expectation p f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[expectation] THEN
  SUBGOAL_THEN `nn_expectation (p:A prob_space) (\x. max (--((f:A->real) x)) (&0)) = &0`
    SUBST1_TAC THENL
  [REWRITE_TAC[nn_expectation] THEN
   SUBGOAL_THEN `{simple_expectation (p:A prob_space) g | g |
     simple_rv p g /\
     (!x:A. x IN prob_carrier p ==> &0 <= g x) /\
     (!x. x IN prob_carrier p ==> g x <= max (--((f:A->real) x)) (&0))} = {&0}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN X_GEN_TAC `v:real` THEN
    EQ_TAC THENL
    [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN `!z:A. z IN prob_carrier p ==> (g:A->real) z = &0` ASSUME_TAC THENL
     [X_GEN_TAC `z:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 <= (g:A->real) z` ASSUME_TAC THENL
      [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(g:A->real) z <= max (--((f:A->real) z)) (&0)` ASSUME_TAC THENL
      [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `max (--((f:A->real) z)) (&0) = &0` ASSUME_TAC THENL
      [SUBGOAL_THEN `&0 <= (f:A->real) z` MP_TAC THENL
       [ASM_SIMP_TAC[]; ASM_REAL_ARITH_TAC];
       ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
     SUBGOAL_THEN `simple_expectation (p:A prob_space) g =
                   simple_expectation p (\x:A. &0)` SUBST1_TAC THENL
     [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN ASM_SIMP_TAC[];
      REWRITE_TAC[SIMPLE_EXPECTATION_CONST]];
     DISCH_THEN SUBST1_TAC THEN
     EXISTS_TAC `\x:A. &0` THEN
     REWRITE_TAC[SIMPLE_RV_CONST; REAL_LE_REFL; SIMPLE_EXPECTATION_CONST] THEN
     GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC];
    REWRITE_TAC[SUP_SING]];
   ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  MATCH_MP_TAC NN_EXPECTATION_POS THEN
  CONJ_TAC THENL
  [GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
   EXISTS_TAC `B:real` THEN GEN_TAC THEN DISCH_TAC THEN
   SUBGOAL_THEN `max ((f:A->real) x) (&0) = f x` SUBST1_TAC THENL
   [SUBGOAL_THEN `&0 <= (f:A->real) x` MP_TAC THENL
    [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
    ASM_SIMP_TAC[]] THEN
   SUBGOAL_THEN `(f:A->real) x <= B /\ &0 <= B` MP_TAC THENL
   [CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(f:A->real) x` THEN
    ASM_SIMP_TAC[];
    REAL_ARITH_TAC]]);;

(* Linearity of expectation for simple RVs *)
let EXPECTATION_ADD_SIMPLE = prove
 (`!p:A prob_space f g.
    simple_rv p f /\ simple_rv p g
    ==> expectation p (\x. f x + g x) = expectation p f + expectation p g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. (f:A->real) x + (g:A->real) x) =
    simple_expectation p (\x. f x + g x)` SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN
   MATCH_MP_TAC SIMPLE_RV_ADD THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (f:A->real) = simple_expectation p f`
    SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (g:A->real) = simple_expectation p g`
    SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  ASM_SIMP_TAC[SIMPLE_EXPECTATION_ADD]);;

(* Scalar multiplication of expectation for simple RVs *)
let EXPECTATION_CMUL_SIMPLE = prove
 (`!p:A prob_space c f.
    simple_rv p f
    ==> expectation p (\x. c * f x) = c * expectation p f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. c * (f:A->real) x) =
    simple_expectation p (\x. c * f x)` SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN
   MATCH_MP_TAC SIMPLE_RV_CMUL THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (f:A->real) = simple_expectation p f`
    SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  ASM_SIMP_TAC[SIMPLE_EXPECTATION_CMUL]);;

(* Negation of expectation for simple RVs *)
let EXPECTATION_NEG_SIMPLE = prove
 (`!p:A prob_space f.
    simple_rv p f
    ==> expectation p (\x. --(f x)) = --(expectation p f)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. --((f:A->real) x)) =
    simple_expectation p (\x. --(f x))` SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN
   MATCH_MP_TAC SIMPLE_RV_NEG THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (f:A->real) = simple_expectation p f`
    SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  ASM_SIMP_TAC[SIMPLE_EXPECTATION_NEG]);;

(* Subtraction of expectation for simple RVs *)
let EXPECTATION_SUB_SIMPLE = prove
 (`!p:A prob_space f g.
    simple_rv p f /\ simple_rv p g
    ==> expectation p (\x. f x - g x) = expectation p f - expectation p g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. (f:A->real) x - (g:A->real) x) =
    simple_expectation p (\x. f x - g x)` SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN
   MATCH_MP_TAC SIMPLE_RV_SUB THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (f:A->real) = simple_expectation p f`
    SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (g:A->real) = simple_expectation p g`
    SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  ASM_SIMP_TAC[SIMPLE_EXPECTATION_SUB]);;

(* Monotonicity of expectation for simple RVs *)
let EXPECTATION_MONO_SIMPLE = prove
 (`!p:A prob_space f g.
    simple_rv p f /\ simple_rv p g /\
    (!x. x IN prob_carrier p ==> f x <= g x)
    ==> expectation p f <= expectation p g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (f:A->real) = simple_expectation p f`
    SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (g:A->real) = simple_expectation p g`
    SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  ASM_SIMP_TAC[SIMPLE_EXPECTATION_MONO]);;

(* Sum of expectations for simple RVs *)
let EXPECTATION_SUM_SIMPLE = prove
 (`!p:A prob_space (X:num->A->real) n.
    (!i. i <= n ==> simple_rv p (X i))
    ==> expectation p (\x. sum(0..n) (\i. X i x)) =
        sum(0..n) (\i. expectation p (X i))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. sum(0..n) (\i. (X:num->A->real) i x))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_SUM_NUMSEG THEN ASM_MESON_TAC[IN_NUMSEG; LE_0];
   ALL_TAC] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. sum(0..n) (\i. (X:num->A->real) i x)) =
    simple_expectation p (\x. sum(0..n) (\i. X i x))` SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  ASM_SIMP_TAC[SIMPLE_EXPECTATION_SUM_NUMSEG; IN_NUMSEG; LE_0] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN ASM_SIMP_TAC[]);;

(* Chebyshev's inequality using general variance *)
let SIMPLE_CHEBYSHEV_INEQUALITY = prove
 (`!p:A prob_space X t.
    simple_rv p X /\ &0 < t
    ==> prob p {x | x IN prob_carrier p /\ abs(X x - expectation p X) >= t}
        <= variance p X / t pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (X:A->real) = simple_expectation p X`
    ASSUME_TAC THENL
  [MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `variance (p:A prob_space) (X:A->real) = simple_variance p X`
    SUBST1_TAC THENL
  [MATCH_MP_TAC VARIANCE_SIMPLE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CHEBYSHEV_INEQUALITY_SIMPLE THEN ASM_REWRITE_TAC[]);;

(* Strong Law of Large Numbers using general expectation/variance *)
let SIMPLE_STRONG_LAW_OF_LARGE_NUMBERS = prove
 (`!p:A prob_space (X:num->A->real) mu sigma_sq M.
    (!n. simple_rv p (X n)) /\
    (!n. expectation p (X n) = mu) /\
    (!n. variance p (X n) = sigma_sq) /\
    (!i j. ~(i = j) ==> simple_covariance p (X i) (X j) = &0) /\
    (!n x. x IN prob_carrier p ==> abs(X n x) <= M)
    ==> almost_surely p
          {x | ((\n. inv(&(SUC n)) * sum(0..n) (\i. X i x)) ---> mu) sequentially}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC STRONG_LAW_OF_LARGE_NUMBERS_SIMPLE THEN
  MAP_EVERY EXISTS_TAC [`sigma_sq:real`; `M:real`] THEN
  REPEAT CONJ_TAC THENL
  [ASM_REWRITE_TAC[];
   GEN_TAC THEN
   SUBGOAL_THEN `expectation (p:A prob_space) ((X:num->A->real) n) =
     simple_expectation p (X n)` MP_TAC THENL
   [MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]];
   GEN_TAC THEN
   SUBGOAL_THEN `variance (p:A prob_space) ((X:num->A->real) n) =
     simple_variance p (X n)` MP_TAC THENL
   [MATCH_MP_TAC VARIANCE_SIMPLE THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]];
   ASM_REWRITE_TAC[];
   ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Phase 6c: General covariance and variance properties                      *)
(* ========================================================================= *)

let covariance = new_definition
 `covariance (p:A prob_space) (X:A->real) (Y:A->real) =
  expectation p (\x. (X x - expectation p X) * (Y x - expectation p Y))`;;

(* Agreement: general covariance = simple covariance for simple RVs *)
let COVARIANCE_SIMPLE_AGREE = prove
 (`!p:A prob_space X Y. simple_rv p X /\ simple_rv p Y
    ==> covariance p X Y = simple_covariance p X Y`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[covariance; simple_covariance] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) X = simple_expectation p X`
    SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) Y = simple_expectation p Y`
    SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `\x:A. ((X:A->real) x - simple_expectation p X) *
           ((Y:A->real) x - simple_expectation p Y)`]
    EXPECTATION_SIMPLE_AGREE) THEN
  ANTS_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_MUL THEN
   CONJ_TAC THEN MATCH_MP_TAC SIMPLE_RV_SUB THEN
   ASM_REWRITE_TAC[SIMPLE_RV_CONST];
   DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[]]);;

(* E[XY] = E[X]*E[Y] for independent simple RVs *)
let EXPECTATION_PRODUCT_INDEP_SIMPLE = prove
 (`!p:A prob_space X Y. simple_rv p X /\ simple_rv p Y /\ indep_rv p X Y
    ==> expectation p (\x. X x * Y x) =
        expectation p X * expectation p Y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. X x * Y x) =
    simple_expectation p (\x. X x * Y x)` SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN
   MATCH_MP_TAC SIMPLE_RV_MUL THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  ASM_SIMP_TAC[EXPECTATION_SIMPLE_AGREE] THEN
  MATCH_MP_TAC SIMPLE_EXPECTATION_PRODUCT_INDEP THEN
  ASM_REWRITE_TAC[]);;

(* Cov(X,Y) = 0 for independent RVs *)
let COVARIANCE_INDEP_SIMPLE = prove
 (`!p:A prob_space X Y. simple_rv p X /\ simple_rv p Y /\ indep_rv p X Y
    ==> covariance p X Y = &0`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[COVARIANCE_SIMPLE_AGREE] THEN
  ASM_SIMP_TAC[SIMPLE_COVARIANCE_INDEP]);;

(* Var(X+Y) = Var(X) + Var(Y) + 2*Cov(X,Y) *)
let VARIANCE_ADD_SIMPLE = prove
 (`!p:A prob_space X Y. simple_rv p X /\ simple_rv p Y
    ==> variance p (\x. X x + Y x) =
        variance p X + variance p Y + &2 * covariance p X Y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `variance (p:A prob_space) (\x. X x + Y x) =
                simple_variance p (\x:A. X x + Y x)` SUBST1_TAC THENL
  [MATCH_MP_TAC VARIANCE_SIMPLE THEN MATCH_MP_TAC SIMPLE_RV_ADD THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  ASM_SIMP_TAC[VARIANCE_SIMPLE; COVARIANCE_SIMPLE_AGREE] THEN
  ASM_SIMP_TAC[SIMPLE_VARIANCE_ADD]);;

(* Var(X+Y) = Var(X) + Var(Y) for independent RVs *)
let VARIANCE_ADD_INDEPENDENT = prove
 (`!p:A prob_space X Y. simple_rv p X /\ simple_rv p Y /\ indep_rv p X Y
    ==> variance p (\x. X x + Y x) = variance p X + variance p Y`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[VARIANCE_ADD_SIMPLE; COVARIANCE_INDEP_SIMPLE] THEN
  REAL_ARITH_TAC);;

(* Var(sum_0^n X_i) = sum_0^n Var(X_i) for uncorrelated RVs *)
let VARIANCE_SUM_UNCORRELATED_SIMPLE = prove
 (`!p:A prob_space X n.
    (!(i:num). i <= n ==> simple_rv p (X i)) /\
    (!i j. i <= n /\ j <= n /\ ~(i = j) ==> covariance p (X i) (X j) = &0)
    ==> variance p (\x. sum (0..n) (\i. X i x)) =
        sum (0..n) (\i. variance p (X i))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `variance (p:A prob_space) (\x. sum (0..n) (\i. X i x)) =
                simple_variance p (\x:A. sum (0..n) (\i. X i x))` SUBST1_TAC THENL
  [MATCH_MP_TAC VARIANCE_SIMPLE THEN
   MATCH_MP_TAC SIMPLE_RV_SUM_NUMSEG THEN
   ASM_SIMP_TAC[IN_NUMSEG; LE_0];
   ALL_TAC] THEN
  SUBGOAL_THEN `!i j. i <= n /\ j <= n /\ ~(i = j)
    ==> simple_covariance (p:A prob_space) ((X:num->A->real) i) (X j) = &0`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `simple_rv (p:A prob_space) ((X:num->A->real) i) /\
                 simple_rv p (X j)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
   ASM_MESON_TAC[COVARIANCE_SIMPLE_AGREE];
   ALL_TAC] THEN
  ASM_SIMP_TAC[SIMPLE_VARIANCE_SUM_UNCORRELATED] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC VARIANCE_SIMPLE THEN
  ASM_SIMP_TAC[IN_NUMSEG; LE_0]);;

(* Var(sum_0^n X_i) = (n+1) * Var(X_0) for uncorrelated IID RVs *)
let VARIANCE_SUM_IID = prove
 (`!p:A prob_space X n.
    (!(i:num). i <= n ==> simple_rv p (X i)) /\
    (!i j. i <= n /\ j <= n /\ ~(i = j) ==> covariance p (X i) (X j) = &0) /\
    (!i. i <= n ==> variance p (X i) = variance p (X 0))
    ==> variance p (\x. sum (0..n) (\i. X i x)) = &(SUC n) * variance p (X 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[VARIANCE_SUM_UNCORRELATED_SIMPLE] THEN
  SIMP_TAC[SUM_CONST_NUMSEG; SUB_0] THEN
  REWRITE_TAC[ADD1]);;

(* General L2 convergence *)
let gen_converges_L2 = new_definition
  `gen_converges_L2 (p:A prob_space) (X:num->A->real) (L:A->real) <=>
   ((\n. expectation p (\x. (X n x - L x) pow 2)) ---> &0) sequentially`;;

(* Agreement: gen_converges_L2 = converges_L2 for simple RVs *)
let GEN_CONVERGES_L2_AGREE = prove
 (`!p:A prob_space X L. (!n. simple_rv p (X n)) /\ simple_rv p L
    ==> (gen_converges_L2 p X L <=> converges_L2 p X L)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[gen_converges_L2; converges_L2] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN BETA_TAC THEN
  MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN
  MATCH_MP_TAC SIMPLE_RV_SQUARE THEN
  MATCH_MP_TAC SIMPLE_RV_SUB THEN
  REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Phase 8d: Linearity of general expectation for bounded random variables   *)
(* ========================================================================= *)

(* Helper: max(c*x, 0) = c * max(x, 0) for c >= 0 *)
let REAL_MAX_MUL_NONNEG = prove
 (`!c x. &0 <= c ==> max (c * x) (&0) = c * max x (&0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_max] THEN
  COND_CASES_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO] THENL
  [SUBGOAL_THEN `&0 <= c * x` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC];
   SUBGOAL_THEN `c * x <= &0` MP_TAC THENL
   [REWRITE_TAC[REAL_ARITH `a <= &0 <=> &0 <= --a`; GSYM REAL_MUL_RNEG] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]]);;

(* BOUNDED_NN_EXPECTATION_CMUL: scalar mult for nn_expectation (c >= 0) *)
let BOUNDED_NN_EXPECTATION_CMUL = prove
 (`!p:A prob_space c f.
    &0 <= c /\
    random_variable p f /\
    (!x. x IN prob_carrier p ==> &0 <= f x) /\
    (?B. !x. x IN prob_carrier p ==> f x <= B)
    ==> nn_expectation p (\x. c * f x) = c * nn_expectation p f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `fn = \n:num. nonneg_simple_fn_approx (p:A prob_space) (f:A->real) n` THEN
  ABBREV_TAC `gn = \n:num. (\x:A. c * (fn:num->A->real) n x)` THEN
  (* fn properties *)
  SUBGOAL_THEN `!n. simple_rv (p:A prob_space) ((fn:num->A->real) n)` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "fn" THEN BETA_TAC THEN
   MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_SIMPLE_RV THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n x:A. x IN prob_carrier p ==> &0 <= (fn:num->A->real) n x`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "fn" THEN BETA_TAC THEN
   REWRITE_TAC[NONNEG_SIMPLE_FN_APPROX_NONNEG];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n x:A. x IN prob_carrier p ==> (fn:num->A->real) n x <= fn (SUC n) x`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "fn" THEN BETA_TAC THEN
   MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_MONO THEN ASM_SIMP_TAC[LE; LE_REFL];
   ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN prob_carrier p ==>
    ((\n. (fn:num->A->real) n x) ---> (f:A->real) x) sequentially`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "fn" THEN BETA_TAC THEN
   MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_CONVERGES THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  (* gn properties *)
  SUBGOAL_THEN `!n. simple_rv (p:A prob_space) ((gn:num->A->real) n)` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "gn" THEN BETA_TAC THEN
   MATCH_MP_TAC SIMPLE_RV_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n x:A. x IN prob_carrier p ==> &0 <= (gn:num->A->real) n x`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "gn" THEN BETA_TAC THEN
   MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n x:A. x IN prob_carrier p ==> (gn:num->A->real) n x <= gn (SUC n) x`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "gn" THEN BETA_TAC THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN prob_carrier p ==>
    ((\n. (gn:num->A->real) n x) ---> c * (f:A->real) x) sequentially`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "gn" THEN BETA_TAC THEN
   MATCH_MP_TAC REALLIM_LMUL THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  (* MCT for fn *)
  SUBGOAL_THEN `((\n. simple_expectation (p:A prob_space) ((fn:num->A->real) n))
    ---> nn_expectation p f) sequentially` ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_MCT_NN_EXPECTATION THEN
   ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* MCT for gn *)
  SUBGOAL_THEN `((\n. simple_expectation (p:A prob_space) ((gn:num->A->real) n))
    ---> nn_expectation p (\x. c * f x)) sequentially` ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_MCT_NN_EXPECTATION THEN ASM_REWRITE_TAC[] THEN
   EXISTS_TAC `c * B:real` THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  (* E[gn n] = c * E[fn n] *)
  SUBGOAL_THEN `!n. simple_expectation (p:A prob_space) ((gn:num->A->real) n) =
    c * simple_expectation p ((fn:num->A->real) n)` ASSUME_TAC THENL
  [GEN_TAC THEN
   SUBGOAL_THEN `(gn:num->A->real) n = (\x:A. c * (fn:num->A->real) n x)` SUBST1_TAC THENL
   [EXPAND_TAC "gn" THEN REFL_TAC; ALL_TAC] THEN
   MATCH_MP_TAC SIMPLE_EXPECTATION_CMUL THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* c * E[fn n] -> c * nn_exp(f) *)
  SUBGOAL_THEN `((\n. c * simple_expectation (p:A prob_space) ((fn:num->A->real) n))
    ---> c * nn_expectation p f) sequentially` ASSUME_TAC THENL
  [MATCH_MP_TAC REALLIM_LMUL THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Limit uniqueness *)
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC `\n:num. simple_expectation (p:A prob_space) ((gn:num->A->real) n)` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  CONJ_TAC THENL
  [ASM_REWRITE_TAC[];
   ASM_REWRITE_TAC[ETA_AX]]);;

(* EXPECTATION_NEG: negation of expectation (unconditional from definition) *)
let EXPECTATION_NEG = prove
 (`!p:A prob_space f.
    random_variable p f
    ==> expectation p (\x. --(f x)) = --(expectation p f)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[expectation; REAL_NEG_NEG] THEN
  REAL_ARITH_TAC);;

(* Helper: BOUNDED_EXPECTATION_CMUL for c >= 0 *)
let EXPECTATION_CMUL_NONNEG = prove
 (`!p:A prob_space c f.
    &0 <= c /\
    random_variable p f /\
    (?B. !x. x IN prob_carrier p ==> abs(f x) <= B)
    ==> expectation p (\x. c * f x) = c * expectation p f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[expectation] THEN
  (* max(c*f x, 0) = c * max(f x, 0) on carrier *)
  SUBGOAL_THEN `nn_expectation (p:A prob_space) (\x. max (c * f x) (&0)) =
    nn_expectation p (\x. c * max (f x) (&0))` SUBST1_TAC THENL
  [MATCH_MP_TAC NN_EXPECTATION_EXT THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   BETA_TAC THEN MATCH_MP_TAC REAL_MAX_MUL_NONNEG THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* max(-(c*f x), 0) = c * max(-f x, 0) on carrier *)
  SUBGOAL_THEN `nn_expectation (p:A prob_space) (\x. max (--(c * f x)) (&0)) =
    nn_expectation p (\x. c * max (--(f x)) (&0))` SUBST1_TAC THENL
  [MATCH_MP_TAC NN_EXPECTATION_EXT THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   BETA_TAC THEN REWRITE_TAC[GSYM REAL_MUL_RNEG] THEN
   MATCH_MP_TAC REAL_MAX_MUL_NONNEG THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Apply BOUNDED_NN_EXPECTATION_CMUL to positive part *)
  SUBGOAL_THEN `nn_expectation (p:A prob_space) (\x. c * max ((f:A->real) x) (&0)) =
    c * nn_expectation p (\x. max (f x) (&0))` SUBST1_TAC THENL
  [MATCH_MP_TAC BOUNDED_NN_EXPECTATION_CMUL THEN ASM_REWRITE_TAC[] THEN
   REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_POS_PART THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
    EXISTS_TAC `B:real` THEN GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* Apply BOUNDED_NN_EXPECTATION_CMUL to negative part *)
  SUBGOAL_THEN `nn_expectation (p:A prob_space) (\x. c * max (--((f:A->real) x)) (&0)) =
    c * nn_expectation p (\x. max (--(f x)) (&0))` SUBST1_TAC THENL
  [MATCH_MP_TAC BOUNDED_NN_EXPECTATION_CMUL THEN ASM_REWRITE_TAC[] THEN
   REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `random_variable (p:A prob_space) (\x:A. --((f:A->real) x))`
      (fun th -> MP_TAC th THEN REWRITE_TAC[RANDOM_VARIABLE_POS_PART; ETA_AX]) THEN
    MATCH_MP_TAC RANDOM_VARIABLE_NEG THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
    EXISTS_TAC `B:real` THEN GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC];
   ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* BOUNDED_EXPECTATION_CMUL: scalar multiplication for general expectation *)
let BOUNDED_EXPECTATION_CMUL = prove
 (`!p:A prob_space c f.
    random_variable p f /\
    (?B. !x. x IN prob_carrier p ==> abs(f x) <= B)
    ==> expectation p (\x. c * f x) = c * expectation p f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= c` THENL
  [MATCH_MP_TAC EXPECTATION_CMUL_NONNEG THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* c < 0: rewrite c*f as (-c)*(-f), apply nonneg case, then EXPECTATION_NEG *)
  SUBGOAL_THEN `expectation (p:A prob_space) (\x. c * (f:A->real) x) =
    expectation p (\x. --c * --((f:A->real) x))`
    (fun th -> REWRITE_TAC[th]) THENL
  [MATCH_MP_TAC EXPECTATION_EXT THEN GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (\x. --c * --((f:A->real) x)) =
    --c * expectation p (\x. --(f x))`
    (fun th -> REWRITE_TAC[th]) THENL
  [MATCH_MP_TAC EXPECTATION_CMUL_NONNEG THEN
   REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC RANDOM_VARIABLE_NEG THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `B:real` THEN GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ABS_NEG] THEN ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  ASM_SIMP_TAC[EXPECTATION_NEG] THEN REAL_ARITH_TAC);;

(* BOUNDED_EXPECTATION_ADD: additivity of general expectation *)
let BOUNDED_EXPECTATION_ADD = prove
 (`!p:A prob_space f g.
    random_variable p f /\ random_variable p g /\
    (?Bf. !x. x IN prob_carrier p ==> abs(f x) <= Bf) /\
    (?Bg. !x. x IN prob_carrier p ==> abs(g x) <= Bg)
    ==> expectation p (\x. f x + g x) = expectation p f + expectation p g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[expectation] THEN
  (* We prove 5 intermediate equalities, then combine with linear arithmetic.
     L1: neg_f + neg_g -> nn_exp(neg_f + neg_g)
     L2: pos_f + pos_g -> nn_exp(pos_f + pos_g)
     L3: pos_fg + nn_exp(neg_f + neg_g) -> nn_exp(pos_fg + (neg_f + neg_g))
     L4: neg_fg + nn_exp(pos_f + pos_g) -> nn_exp(neg_fg + (pos_f + pos_g))
     L5: nn_exp(pos_fg + (neg_f + neg_g)) = nn_exp(neg_fg + (pos_f + pos_g)) *)
  SUBGOAL_THEN
    `nn_expectation (p:A prob_space) (\x. max (--((f:A->real) x)) (&0)) +
     nn_expectation p (\x. max (--((g:A->real) x)) (&0)) =
     nn_expectation p (\x. max (--(f x)) (&0) + max (--(g x)) (&0))`
    (LABEL_TAC "L1") THENL
  [CONV_TAC SYM_CONV THEN
   MATCH_MP_TAC BOUNDED_NN_EXPECTATION_ADD THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_POS_PART THEN MATCH_MP_TAC RANDOM_VARIABLE_NEG THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RANDOM_VARIABLE_POS_PART THEN MATCH_MP_TAC RANDOM_VARIABLE_NEG THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
    EXISTS_TAC `Bf:real` THEN GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs((f:A->real) x) <= Bf` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN REAL_ARITH_TAC;
    EXISTS_TAC `Bg:real` THEN GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs((g:A->real) x) <= Bg` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `nn_expectation (p:A prob_space) (\x. max ((f:A->real) x) (&0)) +
     nn_expectation p (\x. max ((g:A->real) x) (&0)) =
     nn_expectation p (\x. max (f x) (&0) + max (g x) (&0))`
    (LABEL_TAC "L2") THENL
  [CONV_TAC SYM_CONV THEN
   MATCH_MP_TAC BOUNDED_NN_EXPECTATION_ADD THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_POS_PART THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RANDOM_VARIABLE_POS_PART THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
    EXISTS_TAC `Bf:real` THEN GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs((f:A->real) x) <= Bf` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN REAL_ARITH_TAC;
    EXISTS_TAC `Bg:real` THEN GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs((g:A->real) x) <= Bg` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `nn_expectation (p:A prob_space) (\x. max ((f:A->real) x + (g:A->real) x) (&0)) +
     nn_expectation p (\x. max (--(f x)) (&0) + max (--(g x)) (&0)) =
     nn_expectation p (\x. max (f x + g x) (&0) + (max (--(f x)) (&0) + max (--(g x)) (&0)))`
    (LABEL_TAC "L3") THENL
  [CONV_TAC SYM_CONV THEN
   MATCH_MP_TAC BOUNDED_NN_EXPECTATION_ADD THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_POS_PART THEN MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC RANDOM_VARIABLE_POS_PART THEN
    TRY(MATCH_MP_TAC RANDOM_VARIABLE_NEG) THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN REAL_ARITH_TAC;
    EXISTS_TAC `Bf + Bg:real` THEN GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs((f:A->real) x) <= Bf` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `abs((g:A->real) x) <= Bg` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN REAL_ARITH_TAC;
    EXISTS_TAC `Bf + Bg:real` THEN GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
    [SUBGOAL_THEN `abs((f:A->real) x) <= Bf` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN REAL_ARITH_TAC;
     SUBGOAL_THEN `abs((g:A->real) x) <= Bg` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN REAL_ARITH_TAC]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `nn_expectation (p:A prob_space) (\x. max (--((f:A->real) x + (g:A->real) x)) (&0)) +
     nn_expectation p (\x. max (f x) (&0) + max (g x) (&0)) =
     nn_expectation p (\x. max (--(f x + g x)) (&0) + (max (f x) (&0) + max (g x) (&0)))`
    (LABEL_TAC "L4") THENL
  [CONV_TAC SYM_CONV THEN
   MATCH_MP_TAC BOUNDED_NN_EXPECTATION_ADD THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_POS_PART THEN MATCH_MP_TAC RANDOM_VARIABLE_NEG THEN
    MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC RANDOM_VARIABLE_POS_PART THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN REAL_ARITH_TAC;
    EXISTS_TAC `Bf + Bg:real` THEN GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs((f:A->real) x) <= Bf` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `abs((g:A->real) x) <= Bg` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN REAL_ARITH_TAC;
    EXISTS_TAC `Bf + Bg:real` THEN GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
    [SUBGOAL_THEN `abs((f:A->real) x) <= Bf` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN REAL_ARITH_TAC;
     SUBGOAL_THEN `abs((g:A->real) x) <= Bg` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN REAL_ARITH_TAC]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `nn_expectation (p:A prob_space) (\x. max ((f:A->real) x + (g:A->real) x) (&0) +
      (max (--((f:A->real) x)) (&0) + max (--((g:A->real) x)) (&0))) =
     nn_expectation p (\x. max (--((f:A->real) x + (g:A->real) x)) (&0) +
      (max ((f:A->real) x) (&0) + max ((g:A->real) x) (&0)))`
    (LABEL_TAC "L5") THENL
  [MATCH_MP_TAC NN_EXPECTATION_EXT THEN GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* BOUNDED_EXPECTATION_MONO: monotonicity of general expectation *)
let BOUNDED_EXPECTATION_MONO = prove
 (`!p:A prob_space f g.
    random_variable p f /\ random_variable p g /\
    (?Bf. !x. x IN prob_carrier p ==> abs(f x) <= Bf) /\
    (?Bg. !x. x IN prob_carrier p ==> abs(g x) <= Bg) /\
    (!x. x IN prob_carrier p ==> f x <= g x)
    ==> expectation p f <= expectation p g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[expectation] THEN
  MATCH_MP_TAC(REAL_ARITH `a + d <= c + b ==> a - b <= c - d`) THEN
  (* a = nn_exp(pos f), b = nn_exp(neg f), c = nn_exp(pos g), d = nn_exp(neg g) *)
  (* Need: nn_exp(pos f) + nn_exp(neg g) <= nn_exp(pos g) + nn_exp(neg f) *)
  (* i.e., nn_exp(pos f + neg g) <= nn_exp(pos g + neg f) *)
  SUBGOAL_THEN
    `nn_expectation (p:A prob_space) (\x. max ((f:A->real) x) (&0)) +
     nn_expectation p (\x. max (--((g:A->real) x)) (&0)) =
     nn_expectation p (\x. max (f x) (&0) + max (--(g x)) (&0))` SUBST1_TAC THENL
  [CONV_TAC SYM_CONV THEN MATCH_MP_TAC BOUNDED_NN_EXPECTATION_ADD THEN
   REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_POS_PART THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RANDOM_VARIABLE_POS_PART THEN MATCH_MP_TAC RANDOM_VARIABLE_NEG THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
    EXISTS_TAC `Bf:real` THEN GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs((f:A->real) x) <= Bf` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN REAL_ARITH_TAC;
    EXISTS_TAC `Bg:real` THEN GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs((g:A->real) x) <= Bg` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `nn_expectation (p:A prob_space) (\x. max ((g:A->real) x) (&0)) +
     nn_expectation p (\x. max (--((f:A->real) x)) (&0)) =
     nn_expectation p (\x. max (g x) (&0) + max (--(f x)) (&0))` SUBST1_TAC THENL
  [CONV_TAC SYM_CONV THEN MATCH_MP_TAC BOUNDED_NN_EXPECTATION_ADD THEN
   REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_POS_PART THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RANDOM_VARIABLE_POS_PART THEN MATCH_MP_TAC RANDOM_VARIABLE_NEG THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
    EXISTS_TAC `Bg:real` THEN GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs((g:A->real) x) <= Bg` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN REAL_ARITH_TAC;
    EXISTS_TAC `Bf:real` THEN GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs((f:A->real) x) <= Bf` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  MATCH_MP_TAC BOUNDED_NN_EXPECTATION_MONO THEN
  BETA_TAC THEN REPEAT CONJ_TAC THENL
  [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_ADD THEN
   CONJ_TAC THEN REAL_ARITH_TAC;
   GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_ADD THEN
   CONJ_TAC THEN REAL_ARITH_TAC;
   GEN_TAC THEN DISCH_TAC THEN
   SUBGOAL_THEN `(f:A->real) x <= (g:A->real) x` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
   REAL_ARITH_TAC;
   EXISTS_TAC `Bg + Bf:real` THEN GEN_TAC THEN DISCH_TAC THEN
   MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [SUBGOAL_THEN `abs((g:A->real) x) <= Bg` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `abs((f:A->real) x) <= Bf` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* Phase 8e: Lift downstream theorems to general expectation                 *)
(* ========================================================================= *)

(* EXPECTATION_BOUND: |E[f]| <= B when f is bounded by B *)
let EXPECTATION_BOUND = prove
 (`!p:A prob_space f B.
   random_variable p f /\
   (!x. x IN prob_carrier p ==> abs(f x) <= B)
   ==> abs(expectation p f) <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_ABS_BOUNDS] THEN CONJ_TAC THENL
  [(* --B <= E[f] *)
   SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. --B) <= expectation p f`
     MP_TAC THENL
   [MATCH_MP_TAC BOUNDED_EXPECTATION_MONO THEN BETA_TAC THEN
    ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN
    REPEAT CONJ_TAC THENL
    [EXISTS_TAC `abs(B):real` THEN GEN_TAC THEN DISCH_TAC THEN
     REAL_ARITH_TAC;
     EXISTS_TAC `B:real` THEN ASM_SIMP_TAC[];
     GEN_TAC THEN DISCH_TAC THEN
     SUBGOAL_THEN `abs((f:A->real) x) <= B` MP_TAC THENL
     [ASM_SIMP_TAC[]; REAL_ARITH_TAC]];
    REWRITE_TAC[EXPECTATION_CONST]];
   (* E[f] <= B *)
   SUBGOAL_THEN `expectation (p:A prob_space) f <= expectation p (\x:A. B)`
     MP_TAC THENL
   [MATCH_MP_TAC BOUNDED_EXPECTATION_MONO THEN BETA_TAC THEN
    ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN
    REPEAT CONJ_TAC THENL
    [EXISTS_TAC `B:real` THEN ASM_SIMP_TAC[];
     EXISTS_TAC `abs(B):real` THEN GEN_TAC THEN DISCH_TAC THEN
     REAL_ARITH_TAC;
     GEN_TAC THEN DISCH_TAC THEN
     SUBGOAL_THEN `abs((f:A->real) x) <= B` MP_TAC THENL
     [ASM_SIMP_TAC[]; REAL_ARITH_TAC]];
    REWRITE_TAC[EXPECTATION_CONST]]]);;

(* BOUNDED_EXPECTATION_SUB: E[f - g] = E[f] - E[g] *)
let BOUNDED_EXPECTATION_SUB = prove
 (`!p:A prob_space f g.
   random_variable p f /\ random_variable p g /\
   (?Bf. !x. x IN prob_carrier p ==> abs(f x) <= Bf) /\
   (?Bg. !x. x IN prob_carrier p ==> abs(g x) <= Bg)
   ==> expectation p (\x. f x - g x) = expectation p f - expectation p g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x:A. (f:A->real) x - (g:A->real) x) =
    (\x. f x + (--(g x)))` SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. (f:A->real) x +
    --((g:A->real) x)) = expectation p f + expectation p (\x. --(g x))`
    SUBST1_TAC THENL
  [MATCH_MP_TAC BOUNDED_EXPECTATION_ADD THEN
   CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_NEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   CONJ_TAC THENL [EXISTS_TAC `Bf:real` THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
   EXISTS_TAC `Bg:real` THEN GEN_TAC THEN DISCH_TAC THEN
   REWRITE_TAC[REAL_ABS_NEG] THEN ASM_SIMP_TAC[];
   ASM_SIMP_TAC[EXPECTATION_NEG] THEN REAL_ARITH_TAC]);;

(* EXPECTATION_AFFINE: E[c1 * f + c2] = c1 * E[f] + c2 *)
let EXPECTATION_AFFINE = prove
 (`!p:A prob_space c1 c2 f.
   random_variable p f /\
   (?B. !x. x IN prob_carrier p ==> abs(f x) <= B)
   ==> expectation p (\x. c1 * f x + c2) = c1 * expectation p f + c2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `(\x:A. c2:real)`
    (SPEC `(\x:A. c1 * (f:A->real) x)`
    (SPEC `p:A prob_space` BOUNDED_EXPECTATION_ADD))) THEN
  BETA_TAC THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   CONJ_TAC THENL [REWRITE_TAC[RANDOM_VARIABLE_CONST]; ALL_TAC] THEN
   CONJ_TAC THENL
   [EXISTS_TAC `abs(c1) * B` THEN GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_ABS_POS; REAL_LE_REFL];
    EXISTS_TAC `abs(c2)` THEN GEN_TAC THEN DISCH_TAC THEN
    REAL_ARITH_TAC];
   ALL_TAC] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[EXPECTATION_CONST] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. c1 * (f:A->real) x) =
    c1 * expectation p f` SUBST1_TAC THENL
  [MATCH_MP_TAC BOUNDED_EXPECTATION_CMUL THEN ASM_REWRITE_TAC[] THEN
   EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[];
   REAL_ARITH_TAC]);;

(* RANDOM_VARIABLE_MUL: product of random variables is a random variable *)
let RANDOM_VARIABLE_MUL = prove
 (`!p:A prob_space X Y.
   random_variable p X /\ random_variable p Y
   ==> random_variable p (\x. X x * Y x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x:A. (X:A->real) x * (Y:A->real) x) =
    (\x. inv(&2) * (X x + Y x) pow 2 +
         (-- inv(&2) * X x pow 2 + -- inv(&2) * Y x pow 2))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
   REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `(\x:A. -- inv(&2) * (X:A->real) x pow 2 +
                       -- inv(&2) * (Y:A->real) x pow 2)`
    (SPEC `(\x:A. inv(&2) * ((X:A->real) x + (Y:A->real) x) pow 2)`
    (SPEC `p:A prob_space` RANDOM_VARIABLE_ADD))) THEN
  BETA_TAC THEN ANTS_TAC THENL
  [CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN
    MATCH_MP_TAC RANDOM_VARIABLE_SQUARE THEN
    MP_TAC(SPEC `Y:A->real`
      (SPEC `X:A->real`
      (SPEC `p:A prob_space` RANDOM_VARIABLE_ADD))) THEN
    BETA_TAC THEN ASM_SIMP_TAC[];
    MP_TAC(SPEC `(\x:A. -- inv(&2) * (Y:A->real) x pow 2)`
      (SPEC `(\x:A. -- inv(&2) * (X:A->real) x pow 2)`
      (SPEC `p:A prob_space` RANDOM_VARIABLE_ADD))) THEN
    BETA_TAC THEN ANTS_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN
     MATCH_MP_TAC RANDOM_VARIABLE_SQUARE THEN ASM_REWRITE_TAC[];
     SIMP_TAC[]]];
   SIMP_TAC[]]);;

(* COVARIANCE_SYM: Cov(X,Y) = Cov(Y,X) *)
let COVARIANCE_SYM = prove
 (`!p:A prob_space X Y. covariance p X Y = covariance p Y X`,
  REPEAT GEN_TAC THEN REWRITE_TAC[covariance] THEN
  MATCH_MP_TAC EXPECTATION_EXT THEN
  GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN REAL_ARITH_TAC);;

(* COVARIANCE_SELF: Cov(X,X) = Var(X) *)
let COVARIANCE_SELF = prove
 (`!p:A prob_space X. covariance p X X = variance p X`,
  REPEAT GEN_TAC THEN REWRITE_TAC[covariance; variance] THEN
  MATCH_MP_TAC EXPECTATION_EXT THEN
  GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

(* BOUNDED_COVARIANCE_ALT: Cov(X,Y) = E[XY] - E[X]*E[Y] *)
let BOUNDED_COVARIANCE_ALT = prove
 (`!p:A prob_space X Y.
   random_variable p X /\ random_variable p Y /\
   (?Bx. !x. x IN prob_carrier p ==> abs(X x) <= Bx) /\
   (?By. !x. x IN prob_carrier p ==> abs(Y x) <= By)
   ==> covariance p X Y =
       expectation p (\x. X x * Y x) - expectation p X * expectation p Y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `a = expectation (p:A prob_space) (X:A->real)` THEN
  ABBREV_TAC `b' = expectation (p:A prob_space) (Y:A->real)` THEN
  SUBGOAL_THEN `abs(a:real) <= Bx` ASSUME_TAC THENL
  [EXPAND_TAC "a" THEN MATCH_MP_TAC EXPECTATION_BOUND THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(b':real) <= By` ASSUME_TAC THENL
  [EXPAND_TAC "b'" THEN MATCH_MP_TAC EXPECTATION_BOUND THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[covariance] THEN ASM_REWRITE_TAC[] THEN
  (* (X-a)(Y-b') = XY - (aY + (b'X - ab')) *)
  SUBGOAL_THEN `(\x:A. ((X:A->real) x - a) * ((Y:A->real) x - b')) =
    (\x. X x * Y x - (a * Y x + b' * X x - a * b'))` SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* E[XY - g] = E[XY] - E[g] via BOUNDED_EXPECTATION_SUB *)
  MP_TAC(SPEC `(\x:A. a * (Y:A->real) x + b' * (X:A->real) x - a * b')`
    (SPEC `(\x:A. (X:A->real) x * (Y:A->real) x)`
    (SPEC `p:A prob_space` BOUNDED_EXPECTATION_SUB))) THEN
  BETA_TAC THEN ANTS_TAC THENL
  [CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   CONJ_TAC THENL
   [(* random_variable p (\x. a*Y x + (b'*X x - a*b')) *)
    (* NB: a+b-c parses as a+(b-c) in HOL Light, so use ADD not SUB *)
    MP_TAC(SPEC `(\x:A. b' * (X:A->real) x - a * b')`
       (SPEC `(\x:A. a * (Y:A->real) x)`
       (SPEC `p:A prob_space` RANDOM_VARIABLE_ADD))) THEN
     BETA_TAC THEN ANTS_TAC THENL
     [CONJ_TAC THENL
      [MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(SPEC `(\x:A. a * b':real)`
         (SPEC `(\x:A. b' * (X:A->real) x)`
         (SPEC `p:A prob_space` RANDOM_VARIABLE_SUB))) THEN
      BETA_TAC THEN ANTS_TAC THENL
      [CONJ_TAC THENL
       [MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[RANDOM_VARIABLE_CONST]]; SIMP_TAC[]];
      SIMP_TAC[]]; ALL_TAC] THEN
   CONJ_TAC THENL
   [EXISTS_TAC `Bx * By:real` THEN GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs((X:A->real) x) <= Bx` ASSUME_TAC THENL
    [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `abs((Y:A->real) x) <= By` ASSUME_TAC THENL
    [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
   EXISTS_TAC `abs(a) * By + abs(b') * Bx + abs(a) * abs(b')` THEN
   GEN_TAC THEN DISCH_TAC THEN
   SUBGOAL_THEN `abs((X:A->real) x) <= Bx` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `abs((Y:A->real) x) <= By` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC(REAL_ARITH `abs(u:real) <= a /\ abs(v) <= b /\ abs(w) <= c
     ==> abs(u + v - w) <= a + b + c`) THEN
   REPEAT CONJ_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
   MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS; REAL_LE_REFL];
   DISCH_THEN SUBST1_TAC] THEN
  (* Now: E[XY] - E[\x. a*Y x + (b'*X x - a*b')] = E[XY] - a*b' *)
  SUBGOAL_THEN `expectation (p:A prob_space)
    (\x:A. a * (Y:A->real) x + b' * (X:A->real) x - a * b') = a * b'`
    (fun th -> REWRITE_TAC[th] THEN REAL_ARITH_TAC) THEN
  (* Split via BOUNDED_EXPECTATION_ADD (not SUB, since a+b-c = a+(b-c)) *)
  MP_TAC(SPEC `(\x:A. b' * (X:A->real) x - a * b')`
    (SPEC `(\x:A. a * (Y:A->real) x)`
    (SPEC `p:A prob_space` BOUNDED_EXPECTATION_ADD))) THEN
  BETA_TAC THEN ANTS_TAC THENL
  [CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   CONJ_TAC THENL
   [MP_TAC(SPEC `(\x:A. a * b':real)`
      (SPEC `(\x:A. b' * (X:A->real) x)`
      (SPEC `p:A prob_space` RANDOM_VARIABLE_SUB))) THEN
    BETA_TAC THEN ANTS_TAC THENL
    [CONJ_TAC THENL
     [MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[RANDOM_VARIABLE_CONST]]; SIMP_TAC[]]; ALL_TAC] THEN
   CONJ_TAC THENL
   [EXISTS_TAC `abs(a) * By` THEN GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs((Y:A->real) x) <= By` ASSUME_TAC THENL
    [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS; REAL_LE_REFL];
    EXISTS_TAC `abs(b') * Bx + abs(a) * abs(b')` THEN GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs((X:A->real) x) <= Bx` ASSUME_TAC THENL
    [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `abs(u:real) <= a /\ abs(v) <= b
      ==> abs(u - v) <= a + b`) THEN
    CONJ_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS; REAL_LE_REFL]];
   DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. a * (Y:A->real) x) =
    a * expectation p Y` SUBST1_TAC THENL
  [MATCH_MP_TAC BOUNDED_EXPECTATION_CMUL THEN ASM_REWRITE_TAC[] THEN
   EXISTS_TAC `By:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPEC `(\x:A. a * b':real)`
    (SPEC `(\x:A. b' * (X:A->real) x)`
    (SPEC `p:A prob_space` BOUNDED_EXPECTATION_SUB))) THEN
  BETA_TAC THEN ANTS_TAC THENL
  [CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   CONJ_TAC THENL [REWRITE_TAC[RANDOM_VARIABLE_CONST]; ALL_TAC] THEN
   CONJ_TAC THENL
   [EXISTS_TAC `abs(b') * Bx` THEN GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs((X:A->real) x) <= Bx` ASSUME_TAC THENL
    [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS; REAL_LE_REFL];
    EXISTS_TAC `abs(a) * abs(b')` THEN GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN REAL_ARITH_TAC];
   DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[EXPECTATION_CONST] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. b' * (X:A->real) x) =
    b' * expectation p X` SUBST1_TAC THENL
  [MATCH_MP_TAC BOUNDED_EXPECTATION_CMUL THEN ASM_REWRITE_TAC[] THEN
   EXISTS_TAC `Bx:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* BOUNDED_COVARIANCE_CMUL: Cov(aX, Y) = a * Cov(X, Y) *)
let BOUNDED_COVARIANCE_CMUL = prove
 (`!p:A prob_space X Y a.
   random_variable p X /\ random_variable p Y /\
   (?Bx. !x. x IN prob_carrier p ==> abs(X x) <= Bx) /\
   (?By. !x. x IN prob_carrier p ==> abs(Y x) <= By)
   ==> covariance p (\x. a * X x) Y = a * covariance p X Y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[covariance] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. a * (X:A->real) x) =
    a * expectation p X` ASSUME_TAC THENL
  [MATCH_MP_TAC BOUNDED_EXPECTATION_CMUL THEN ASM_REWRITE_TAC[] THEN
   EXISTS_TAC `Bx:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\x:A. (a * (X:A->real) x - a * expectation p X) *
    ((Y:A->real) x - expectation p Y)) =
    (\x. a * ((X x - expectation p X) * (Y x - expectation p Y)))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC BOUNDED_EXPECTATION_CMUL THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN
   CONJ_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_SUB_CONST THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(expectation (p:A prob_space) (X:A->real)) <= Bx`
    ASSUME_TAC THENL
  [MATCH_MP_TAC EXPECTATION_BOUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(expectation (p:A prob_space) (Y:A->real)) <= By`
    ASSUME_TAC THENL
  [MATCH_MP_TAC EXPECTATION_BOUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `(&2 * Bx) * (&2 * By)` THEN GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs((X:A->real) x) <= Bx` ASSUME_TAC THENL
  [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs((Y:A->real) x) <= By` ASSUME_TAC THENL
  [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
  CONJ_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
    `abs(u:real) <= B /\ abs(v) <= B ==> abs(u - v) <= &2 * B`) THEN
  ASM_REWRITE_TAC[]);;

(* BOUNDED_VARIANCE_ADD: Var(X+Y) = Var(X) + Var(Y) + 2*Cov(X,Y) *)
let BOUNDED_VARIANCE_ADD = prove
 (`!p:A prob_space X Y.
   random_variable p X /\ random_variable p Y /\
   (?Bx. !x. x IN prob_carrier p ==> abs(X x) <= Bx) /\
   (?By. !x. x IN prob_carrier p ==> abs(Y x) <= By)
   ==> variance p (\x. X x + Y x) =
       variance p X + variance p Y + &2 * covariance p X Y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `a = expectation (p:A prob_space) (X:A->real)` THEN
  ABBREV_TAC `b' = expectation (p:A prob_space) (Y:A->real)` THEN
  SUBGOAL_THEN `abs(a:real) <= Bx` ASSUME_TAC THENL
  [EXPAND_TAC "a" THEN MATCH_MP_TAC EXPECTATION_BOUND THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(b':real) <= By` ASSUME_TAC THENL
  [EXPAND_TAC "b'" THEN MATCH_MP_TAC EXPECTATION_BOUND THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[variance; covariance] THEN
  (* E[X+Y] = a + b' *)
  SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. (X:A->real) x + (Y:A->real) x) =
    a + b'` ASSUME_TAC THENL
  [EXPAND_TAC "a" THEN EXPAND_TAC "b'" THEN
   MATCH_MP_TAC BOUNDED_EXPECTATION_ADD THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL
   [EXISTS_TAC `Bx:real` THEN ASM_SIMP_TAC[];
    EXISTS_TAC `By:real` THEN ASM_SIMP_TAC[]]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* Rewrite integrand: (X+Y - (a+b'))^2 = ((X-a) + (Y-b'))^2
     = (X-a)^2 + (Y-b')^2 + 2*(X-a)*(Y-b') *)
  SUBGOAL_THEN `(\x:A. (((X:A->real) x + (Y:A->real) x) - (a + b')) pow 2) =
    (\x. (X x - a) pow 2 + ((Y x - b') pow 2 + &2 * (X x - a) * (Y x - b')))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; REAL_POW_2] THEN GEN_TAC THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  (* Establish key random_variable and bound facts *)
  SUBGOAL_THEN `random_variable (p:A prob_space) (\x:A. ((X:A->real) x - a) pow 2)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_SQUARE THEN
   MATCH_MP_TAC RANDOM_VARIABLE_SUB_CONST THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `random_variable (p:A prob_space) (\x:A. ((Y:A->real) x - b') pow 2)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_SQUARE THEN
   MATCH_MP_TAC RANDOM_VARIABLE_SUB_CONST THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `random_variable (p:A prob_space)
    (\x:A. ((X:A->real) x - a) * ((Y:A->real) x - b'))` ASSUME_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN CONJ_TAC THEN
   MATCH_MP_TAC RANDOM_VARIABLE_SUB_CONST THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN prob_carrier p ==>
    abs(((X:A->real) x - a) pow 2) <= (&2 * Bx) * (&2 * Bx)` ASSUME_TAC THENL
  [GEN_TAC THEN DISCH_TAC THEN
   SUBGOAL_THEN `abs((X:A->real) x - a) <= &2 * Bx` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
      `abs(u:real) <= B /\ abs(v) <= B ==> abs(u - v) <= &2 * B`) THEN
    CONJ_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[REAL_POW_2; REAL_ABS_MUL] THEN
   MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN prob_carrier p ==>
    abs(((Y:A->real) x - b') pow 2) <= (&2 * By) * (&2 * By)` ASSUME_TAC THENL
  [GEN_TAC THEN DISCH_TAC THEN
   SUBGOAL_THEN `abs((Y:A->real) x - b') <= &2 * By` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
      `abs(u:real) <= B /\ abs(v) <= B ==> abs(u - v) <= &2 * B`) THEN
    CONJ_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[REAL_POW_2; REAL_ABS_MUL] THEN
   MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN prob_carrier p ==>
    abs(((X:A->real) x - a) * ((Y:A->real) x - b')) <=
    (&2 * Bx) * (&2 * By)` ASSUME_TAC THENL
  [GEN_TAC THEN DISCH_TAC THEN
   REWRITE_TAC[REAL_ABS_MUL] THEN
   MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
   CONJ_TAC THEN
   MATCH_MP_TAC(REAL_ARITH
     `abs(u:real) <= B /\ abs(v) <= B ==> abs(u - v) <= &2 * B`) THEN
   CONJ_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  (* First split: E[A + (B + C)] = E[A] + E[B + C] *)
  MP_TAC(SPEC `(\x:A. ((Y:A->real) x - b') pow 2 +
      &2 * ((X:A->real) x - a) * ((Y:A->real) x - b'))`
    (SPEC `(\x:A. ((X:A->real) x - a) pow 2)`
    (SPEC `p:A prob_space` BOUNDED_EXPECTATION_ADD))) THEN
  BETA_TAC THEN ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(SPEC `(\x:A. &2 * ((X:A->real) x - a) * ((Y:A->real) x - b'))`
      (SPEC `(\x:A. ((Y:A->real) x - b') pow 2)`
      (SPEC `p:A prob_space` RANDOM_VARIABLE_ADD))) THEN
    BETA_TAC THEN ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     MP_TAC(SPECL [`p:A prob_space`;
       `(\x:A. ((X:A->real) x - a) * ((Y:A->real) x - b'))`; `&2`]
       RANDOM_VARIABLE_CMUL) THEN
     BETA_TAC THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
     SIMP_TAC[]]; ALL_TAC] THEN
   CONJ_TAC THENL
   [EXISTS_TAC `(&2 * Bx) * (&2 * Bx)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   EXISTS_TAC `(&2 * By) * (&2 * By) + &2 * (&2 * Bx) * (&2 * By)` THEN
   GEN_TAC THEN DISCH_TAC THEN
   MATCH_MP_TAC(REAL_ARITH
     `abs(u:real) <= a /\ abs(v) <= b ==> abs(u + v) <= a + b`) THEN
   CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[GSYM REAL_ABS_MUL] THEN ASM_SIMP_TAC[];
   DISCH_THEN SUBST1_TAC] THEN
  (* Second split: E[B + C] = E[B] + E[C] *)
  AP_TERM_TAC THEN
  MP_TAC(SPEC `(\x:A. &2 * ((X:A->real) x - a) * ((Y:A->real) x - b'))`
    (SPEC `(\x:A. ((Y:A->real) x - b') pow 2)`
    (SPEC `p:A prob_space` BOUNDED_EXPECTATION_ADD))) THEN
  BETA_TAC THEN ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`p:A prob_space`;
      `(\x:A. ((X:A->real) x - a) * ((Y:A->real) x - b'))`; `&2`]
      RANDOM_VARIABLE_CMUL) THEN
    BETA_TAC THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [EXISTS_TAC `(&2 * By) * (&2 * By)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   EXISTS_TAC `&2 * (&2 * Bx) * (&2 * By)` THEN GEN_TAC THEN DISCH_TAC THEN
   REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[GSYM REAL_ABS_MUL] THEN ASM_SIMP_TAC[];
   DISCH_THEN SUBST1_TAC] THEN
  (* E[2*(X-a)*(Y-b')] = 2*E[(X-a)*(Y-b')] *)
  AP_TERM_TAC THEN
  MATCH_MP_TAC BOUNDED_EXPECTATION_CMUL THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `(&2 * Bx) * (&2 * By)` THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Phase 9: Generalization from bounded to integrable hypotheses             *)
(* ========================================================================= *)

(* Min of two simple RVs is simple *)
let SIMPLE_RV_MIN = prove
 (`!p:A prob_space X Y.
     simple_rv p X /\ simple_rv p Y
     ==> simple_rv p (\x. min (X x) (Y x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:A. min ((X:A->real) x) ((Y:A->real) x)) =
                (\x. inv(&2) * ((X x + Y x) - abs(X x - Y x)))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
   MATCH_MP_TAC SIMPLE_RV_CMUL THEN
   MATCH_MP_TAC SIMPLE_RV_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_ADD THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SIMPLE_RV_ABS THEN
    MATCH_MP_TAC SIMPLE_RV_SUB THEN ASM_REWRITE_TAC[]]]);;

(* Nonneg integrable functions have bounded nn_expectation *)
let INTEGRABLE_NONNEG_NN_BOUNDED = prove
 (`!p:A prob_space f.
     integrable p f /\
     (!x. x IN prob_carrier p ==> &0 <= f x)
     ==> ?B. !g. simple_rv p g /\
                  (!x. x IN prob_carrier p ==> &0 <= g x) /\
                  (!x. x IN prob_carrier p ==> g x <= f x)
                  ==> simple_expectation p g <= B`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [integrable]) THEN
  STRIP_TAC THEN EXISTS_TAC `B:real` THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:A` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(f:A->real) z` THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> x <= abs x`) THEN
  ASM_SIMP_TAC[]);;

(* nn_expectation bounded for integrable nonneg functions *)
let NN_EXPECTATION_INTEGRABLE_BOUND = prove
 (`!p:A prob_space f.
     integrable p f /\
     (!x. x IN prob_carrier p ==> &0 <= f x)
     ==> ?B. nn_expectation p f <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:A prob_space`; `f:A->real`]
    INTEGRABLE_NONNEG_NN_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  EXISTS_TAC `B:real` THEN
  MATCH_MP_TAC NN_EXPECTATION_LE_FROM_SIMPLE THEN
  ASM_REWRITE_TAC[]);;

(* Simple h below nonneg integrable f: E[h] <= nn_exp(f) *)
let NN_EXPECTATION_GE_SIMPLE = prove
 (`!p:A prob_space h f.
     simple_rv p h /\
     (!x. x IN prob_carrier p ==> &0 <= h x) /\
     (!x. x IN prob_carrier p ==> h x <= f x) /\
     (!x. x IN prob_carrier p ==> &0 <= f x) /\
     integrable p f
     ==> simple_expectation p h <= nn_expectation p f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nn_expectation] THEN
  MATCH_MP_TAC REAL_LE_SUP THEN
  MP_TAC(SPECL [`p:A prob_space`; `f:A->real`]
    INTEGRABLE_NONNEG_NN_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  EXISTS_TAC `B:real` THEN
  EXISTS_TAC `simple_expectation p (h:A->real)` THEN
  REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
  [REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `h:A->real` THEN
   ASM_REWRITE_TAC[];
   X_GEN_TAC `v:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
   DISCH_THEN(X_CHOOSE_THEN `h':A->real` STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[]]);;

(* nn_expectation monotone for integrable nonneg upper bound *)
let NN_EXPECTATION_MONO = prove
 (`!p:A prob_space f g.
     (!x. x IN prob_carrier p ==> &0 <= f x) /\
     (!x. x IN prob_carrier p ==> &0 <= g x) /\
     (!x. x IN prob_carrier p ==> f x <= g x) /\
     integrable p g
     ==> nn_expectation p f <= nn_expectation p g`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[nn_expectation] THEN
  MATCH_MP_TAC REAL_SUP_LE_SUBSET THEN CONJ_TAC THENL
  [MATCH_MP_TAC NN_EXPECT_SET_NONEMPTY THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
   X_GEN_TAC `v:real` THEN
   DISCH_THEN(X_CHOOSE_THEN `h:A->real` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `h:A->real` THEN ASM_REWRITE_TAC[] THEN
   X_GEN_TAC `z:A` THEN DISCH_TAC THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(f:A->real) z` THEN
   ASM_SIMP_TAC[];
   MP_TAC(SPECL [`p:A prob_space`; `g:A->real`]
     INTEGRABLE_NONNEG_NN_BOUNDED) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
   EXISTS_TAC `B:real` THEN
   X_GEN_TAC `v:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
   DISCH_THEN(X_CHOOSE_THEN `h:A->real` STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[]]);;

(* BOUNDED_NN_EXPECTATION_ADD for integrable nonneg functions *)
let NN_EXPECTATION_ADD = prove
 (`!p:A prob_space f g.
     random_variable p f /\
     random_variable p g /\
     (!x. x IN prob_carrier p ==> &0 <= f x) /\
     (!x. x IN prob_carrier p ==> &0 <= g x) /\
     integrable p f /\
     integrable p g
     ==> nn_expectation p (\x. f x + g x) =
         nn_expectation p f + nn_expectation p g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Abbreviate f+g to avoid beta-redex issues with MATCH_MP_TAC *)
  ABBREV_TAC `fg = \x:A. (f:A->real) x + (g:A->real) x` THEN
  (* KEY BOUND: every simple h below fg has E[h] <= nn_exp(f)+nn_exp(g) *)
  SUBGOAL_THEN
    `!h:A->real. simple_rv p h /\
     (!x. x IN prob_carrier p ==> &0 <= h x) /\
     (!x. x IN prob_carrier p ==> h x <= (fg:A->real) x)
     ==> simple_expectation p h <=
         nn_expectation p f + nn_expectation p g`
    (LABEL_TAC "KEY") THENL
  [X_GEN_TAC `h:A->real` THEN STRIP_TAC THEN
   (* Establish h x <= f x + g x from h x <= fg x *)
   SUBGOAL_THEN `!x:A. x IN prob_carrier p ==>
     (h:A->real) x <= (f:A->real) x + (g:A->real) x` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(h:A->real) x <= (fg:A->real) x` MP_TAC THENL
    [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "fg" THEN BETA_TAC THEN SIMP_TAC[];
    ALL_TAC] THEN
   (* h is bounded by some M0; use M = max(M0, 0) to ensure M >= 0 *)
   MP_TAC(SPECL [`p:A prob_space`; `h:A->real`] SIMPLE_RV_BOUNDED) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `M0:real` ASSUME_TAC) THEN
   ABBREV_TAC `M = max (M0:real) (&0)` THEN
   SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `!x:A. x IN prob_carrier p ==> (h:A->real) x <= M`
     ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "M" THEN
    MATCH_MP_TAC(REAL_ARITH `x <= M0 ==> x <= max M0 (&0)`) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
   (* E[h] <= nn_exp(min(f,M)+min(g,M)) via BOUNDED_NN_EXPECTATION_GE_SIMPLE *)
   SUBGOAL_THEN `simple_expectation (p:A prob_space) h <=
     nn_expectation p (\x:A. min ((f:A->real) x) M + min ((g:A->real) x) M)`
     MP_TAC THENL
   [MATCH_MP_TAC BOUNDED_NN_EXPECTATION_GE_SIMPLE THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
     SUBGOAL_THEN `(h:A->real) x <= M /\
       (h:A->real) x <= (f:A->real) x + (g:A->real) x /\
       &0 <= (f:A->real) x /\ &0 <= (g:A->real) x` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
     REWRITE_TAC[real_min] THEN
     REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_REAL_ARITH_TAC;
     EXISTS_TAC `M + M:real` THEN GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
     REWRITE_TAC[real_min] THEN
     REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
     ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
   (* nn_exp(min(f,M) + min(g,M)) = nn_exp(min(f,M)) + nn_exp(min(g,M)) *)
   SUBGOAL_THEN `nn_expectation (p:A prob_space) (\x:A. min ((f:A->real) x) M +
     min ((g:A->real) x) M) =
     nn_expectation p (\x. min (f x) M) + nn_expectation p (\x. min (g x) M)`
     SUBST1_TAC THENL
   [MATCH_MP_TAC BOUNDED_NN_EXPECTATION_ADD THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
     ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST];
     MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
     ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST];
     GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
     REWRITE_TAC[REAL_LE_MIN] THEN ASM_SIMP_TAC[];
     GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
     REWRITE_TAC[REAL_LE_MIN] THEN ASM_SIMP_TAC[];
     EXISTS_TAC `M:real` THEN GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
     REAL_ARITH_TAC;
     EXISTS_TAC `M:real` THEN GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
     REAL_ARITH_TAC];
    ALL_TAC] THEN
   (* nn_exp(min(f,M)) <= nn_exp(f) and nn_exp(min(g,M)) <= nn_exp(g) *)
   DISCH_TAC THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `nn_expectation (p:A prob_space) (\x. min ((f:A->real) x) M) +
     nn_expectation p (\x. min ((g:A->real) x) M)` THEN
   CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
    [MATCH_MP_TAC NN_EXPECTATION_MONO THEN
     ASM_REWRITE_TAC[] THEN
     CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
      REWRITE_TAC[REAL_LE_MIN] THEN ASM_SIMP_TAC[];
      GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN REAL_ARITH_TAC];
     MATCH_MP_TAC NN_EXPECTATION_MONO THEN
     ASM_REWRITE_TAC[] THEN
     CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
      REWRITE_TAC[REAL_LE_MIN] THEN ASM_SIMP_TAC[];
      GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN REAL_ARITH_TAC]]];
   ALL_TAC] THEN
  (* Now prove both directions using KEY *)
  MATCH_MP_TAC(REAL_ARITH `a <= b /\ b <= a ==> a = b`) THEN
  CONJ_TAC THENL
  [(* <= direction: nn_exp(fg) <= nn_exp(f) + nn_exp(g) *)
   MATCH_MP_TAC NN_EXPECTATION_LE_FROM_SIMPLE THEN
   CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "fg" THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN USE_THEN "KEY" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]];
   (* >= direction: nn_exp(f) + nn_exp(g) <= nn_exp(fg) *)
   (* Step 1: For all simple h1 <= f: E[h1] + nn_exp(g) <= nn_exp(fg) *)
   SUBGOAL_THEN `!h1:A->real. simple_rv p h1 /\
     (!x. x IN prob_carrier p ==> &0 <= h1 x) /\
     (!x. x IN prob_carrier p ==> h1 x <= (f:A->real) x)
     ==> simple_expectation p h1 + nn_expectation p g <=
         nn_expectation p (fg:A->real)` ASSUME_TAC THENL
   [X_GEN_TAC `h1:A->real` THEN STRIP_TAC THEN
    (* nn_exp(g) <= nn_exp(fg) - E[h1], then rearrange *)
    SUBGOAL_THEN `nn_expectation (p:A prob_space) (g:A->real) <=
      nn_expectation p (fg:A->real) -
      simple_expectation p (h1:A->real)`
      (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
    (* Use NN_EXPECTATION_LE_FROM_SIMPLE on g *)
    MATCH_MP_TAC NN_EXPECTATION_LE_FROM_SIMPLE THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `h2:A->real` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_LE_SUB_LADD] THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    (* E[h1] + E[h2] = E[h1+h2] *)
    SUBGOAL_THEN `simple_expectation (p:A prob_space) (h1:A->real) +
      simple_expectation p (h2:A->real) =
      simple_expectation p (\x:A. h1 x + h2 x)` SUBST1_TAC THENL
    [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SIMPLE_EXPECTATION_ADD THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    (* E[h1+h2] <= nn_exp(fg) using REAL_LE_SUP *)
    REWRITE_TAC[nn_expectation] THEN
    MATCH_MP_TAC REAL_LE_SUP THEN
    EXISTS_TAC `nn_expectation (p:A prob_space) (f:A->real) +
      nn_expectation p (g:A->real)` THEN
    EXISTS_TAC `simple_expectation (p:A prob_space)
      (\x:A. (h1:A->real) x + (h2:A->real) x)` THEN
    REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
    [(* h1+h2 is in the nn_exp(fg) set *)
     REWRITE_TAC[IN_ELIM_THM] THEN
     EXISTS_TAC `\x:A. (h1:A->real) x + (h2:A->real) x` THEN
     CONJ_TAC THENL
     [REPEAT CONJ_TAC THENL
      [MATCH_MP_TAC SIMPLE_RV_ADD THEN ASM_REWRITE_TAC[];
       GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
       MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[];
       GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
       EXPAND_TAC "fg" THEN BETA_TAC THEN
       MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_SIMP_TAC[]];
      REFL_TAC];
     (* Every element of the set <= nn_exp(f) + nn_exp(g) by KEY *)
     X_GEN_TAC `w:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
     DISCH_THEN(X_CHOOSE_THEN `k:A->real` STRIP_ASSUME_TAC) THEN
     ASM_REWRITE_TAC[] THEN
     USE_THEN "KEY" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   (* Step 2: nn_exp(f) + nn_exp(g) <= nn_exp(fg) via sup over h1 *)
   SUBGOAL_THEN `nn_expectation (p:A prob_space) (f:A->real) <=
     nn_expectation p (fg:A->real) - nn_expectation p g`
     (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
   MATCH_MP_TAC NN_EXPECTATION_LE_FROM_SIMPLE THEN
   CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   X_GEN_TAC `h1:A->real` THEN STRIP_TAC THEN
   MATCH_MP_TAC(REAL_ARITH `a + b <= c ==> a <= c - b`) THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Phase 9b: Integrable closure properties and expectation theorems          *)
(* ========================================================================= *)

(* Absolute value of integrable function is integrable *)
let INTEGRABLE_ABS = prove
 (`!p:A prob_space f.
     integrable p f ==> integrable p (\x. abs(f x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[integrable] THEN STRIP_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `B:real` THEN
  X_GEN_TAC `g':A->real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(g':A->real) z <= abs((\x:A. abs((f:A->real) x)) z)` MP_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  BETA_TAC THEN REAL_ARITH_TAC);;

(* Negation of integrable function is integrable *)
let INTEGRABLE_NEG = prove
 (`!p:A prob_space f.
     integrable p f ==> integrable p (\x. --(f x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[integrable] THEN STRIP_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_NEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `B:real` THEN
  X_GEN_TAC `g':A->real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(g':A->real) z <= abs((\x:A. --((f:A->real) x)) z)` MP_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  BETA_TAC THEN REWRITE_TAC[REAL_ABS_NEG] THEN REAL_ARITH_TAC);;

(* Positive part of integrable function is integrable *)
let INTEGRABLE_POS_PART = prove
 (`!p:A prob_space f.
     integrable p f ==> integrable p (\x. max (f x) (&0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[integrable] THEN STRIP_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_POS_PART THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `B:real` THEN
  X_GEN_TAC `g':A->real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(g':A->real) z <= abs((\x:A. max ((f:A->real) x) (&0)) z)` MP_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  BETA_TAC THEN REWRITE_TAC[real_max] THEN
  COND_CASES_TAC THEN REAL_ARITH_TAC);;

(* Negative part of integrable function is integrable *)
let INTEGRABLE_NEG_PART = prove
 (`!p:A prob_space f.
     integrable p f ==> integrable p (\x. max (--(f x)) (&0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[integrable] THEN STRIP_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_NEG_PART THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `B:real` THEN
  X_GEN_TAC `g':A->real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(g':A->real) z <= abs((\x:A. max (--((f:A->real) x)) (&0)) z)` MP_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  BETA_TAC THEN REWRITE_TAC[real_max] THEN
  COND_CASES_TAC THEN REAL_ARITH_TAC);;

(* Scalar multiple of integrable function is integrable *)
let INTEGRABLE_CMUL = prove
 (`!p:A prob_space c f.
     integrable p f ==> integrable p (\x. c * f x)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `c = &0` THENL
  [ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
   DISCH_TAC THEN MATCH_MP_TAC INTEGRABLE_SIMPLE THEN
   REWRITE_TAC[SIMPLE_RV_CONST];
   ALL_TAC] THEN
  REWRITE_TAC[integrable] THEN STRIP_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(abs(c:real) = &0)` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[REAL_ABS_ZERO]; ALL_TAC] THEN
  EXISTS_TAC `abs(c) * B` THEN
  X_GEN_TAC `g':A->real` THEN STRIP_TAC THEN
  (* E[g'] = abs(c) * E[inv(abs c) * g'] <= abs(c) * B *)
  SUBGOAL_THEN `simple_expectation (p:A prob_space) (g':A->real) =
    abs(c) * simple_expectation p (\x:A. inv(abs c) * (g':A->real) x)` SUBST1_TAC THENL
  [SUBGOAL_THEN `simple_expectation (p:A prob_space) (\x:A. inv(abs c) * (g':A->real) x) =
    inv(abs c) * simple_expectation p g'` SUBST1_TAC THENL
   [MATCH_MP_TAC SIMPLE_EXPECTATION_CMUL THEN ASM_REWRITE_TAC[];
    CONV_TAC(RAND_CONV(REWR_CONV REAL_MUL_ASSOC)) THEN
    SUBGOAL_THEN `abs(c:real) * inv(abs c) = &1`
      (fun th -> REWRITE_TAC[th; REAL_MUL_LID]) THEN
    MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_CMUL THEN ASM_REWRITE_TAC[];
   X_GEN_TAC `z:A` THEN DISCH_TAC THEN BETA_TAC THEN
   MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV THEN REAL_ARITH_TAC; ASM_MESON_TAC[]];
   X_GEN_TAC `z:A` THEN DISCH_TAC THEN BETA_TAC THEN
   SUBGOAL_THEN `(g':A->real) z <= abs((\x:A. c * (f:A->real) x) z)` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
   BETA_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
   DISCH_TAC THEN
   SUBGOAL_THEN `inv(abs c) * (g':A->real) z <= inv(abs c) * (abs c * abs((f:A->real) z))`
     MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_INV THEN REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `inv(abs(c:real)) * (abs c * abs((f:A->real) z)) = abs(f z)`
      (fun th -> ASM_SIMP_TAC[th]) THEN
    ONCE_REWRITE_TAC[REAL_MUL_ASSOC] THEN
    SUBGOAL_THEN `inv(abs(c:real)) * abs c = &1`
      (fun th -> REWRITE_TAC[th; REAL_MUL_LID]) THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[]]]);;


(* Sum of integrable functions is integrable *)
let INTEGRABLE_ADD = prove
 (`!p:A prob_space f g.
     integrable p f /\ integrable p g
     ==> integrable p (\x. f x + g x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[integrable] THEN CONJ_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN ASM_MESON_TAC[integrable];
   ALL_TAC] THEN
  (* Get bounds from integrability of |f| and |g| *)
  SUBGOAL_THEN `integrable (p:A prob_space) (\x. abs((f:A->real) x))` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_ABS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x. abs((g:A->real) x))` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_ABS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`p:A prob_space`; `\x:A. abs((f:A->real) x)`]
    NN_EXPECTATION_INTEGRABLE_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `Bf:real`) THEN
  MP_TAC(SPECL [`p:A prob_space`; `\x:A. abs((g:A->real) x)`]
    NN_EXPECTATION_INTEGRABLE_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `Bg:real`) THEN
  EXISTS_TAC `Bf + Bg:real` THEN
  X_GEN_TAC `h:A->real` THEN STRIP_TAC THEN
  (* h is simple, bounded by some M *)
  MP_TAC(SPECL [`p:A prob_space`; `h:A->real`] SIMPLE_RV_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M0:real` ASSUME_TAC) THEN
  ABBREV_TAC `M = max M0 (&0)` THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
  [EXPAND_TAC "M" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN prob_carrier p ==> (h:A->real) x <= M`
    ASSUME_TAC THENL
  [GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "M" THEN
   MATCH_MP_TAC(REAL_ARITH `x <= M0 ==> x <= max M0 (&0)`) THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* Define truncated functions *)
  ABBREV_TAC `fM = \x:A. min (abs((f:A->real) x)) M` THEN
  ABBREV_TAC `gM = \x:A. min (abs((g:A->real) x)) M` THEN
  (* h <= fM + gM *)
  SUBGOAL_THEN `!x:A. x IN prob_carrier p ==>
    (h:A->real) x <= (fM:A->real) x + (gM:A->real) x` ASSUME_TAC THENL
  [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   EXPAND_TAC "fM" THEN EXPAND_TAC "gM" THEN BETA_TAC THEN
   SUBGOAL_THEN `(h:A->real) x <= abs((f:A->real) x + (g:A->real) x)` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `(h:A->real) x <= M` MP_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[real_min] THEN
   REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* fM and gM are nonneg and bounded by M *)
  SUBGOAL_THEN `!x:A. x IN prob_carrier p ==> &0 <= (fM:A->real) x` ASSUME_TAC THENL
  [GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "fM" THEN BETA_TAC THEN
   REWRITE_TAC[REAL_LE_MIN] THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN prob_carrier p ==> &0 <= (gM:A->real) x` ASSUME_TAC THENL
  [GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "gM" THEN BETA_TAC THEN
   REWRITE_TAC[REAL_LE_MIN] THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN prob_carrier p ==> (fM:A->real) x <= M` ASSUME_TAC THENL
  [GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "fM" THEN BETA_TAC THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN prob_carrier p ==> (gM:A->real) x <= M` ASSUME_TAC THENL
  [GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "gM" THEN BETA_TAC THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  (* fM and gM are random_variables *)
  SUBGOAL_THEN `random_variable (p:A prob_space) (fM:A->real)` ASSUME_TAC THENL
  [EXPAND_TAC "fM" THEN MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
   CONJ_TAC THENL [MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN ASM_MESON_TAC[integrable];
                    REWRITE_TAC[RANDOM_VARIABLE_CONST]];
   ALL_TAC] THEN
  SUBGOAL_THEN `random_variable (p:A prob_space) (gM:A->real)` ASSUME_TAC THENL
  [EXPAND_TAC "gM" THEN MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
   CONJ_TAC THENL [MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN ASM_MESON_TAC[integrable];
                    REWRITE_TAC[RANDOM_VARIABLE_CONST]];
   ALL_TAC] THEN
  (* E[h] <= nn_exp(fM + gM) via BOUNDED_NN_EXPECTATION_GE_SIMPLE *)
  SUBGOAL_THEN `simple_expectation (p:A prob_space) (h:A->real) <=
    nn_expectation p (\x:A. (fM:A->real) x + (gM:A->real) x)` MP_TAC THENL
  [MATCH_MP_TAC BOUNDED_NN_EXPECTATION_GE_SIMPLE THEN ASM_REWRITE_TAC[] THEN
   EXISTS_TAC `M + M:real` THEN GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
   MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  (* nn_exp(fM+gM) = nn_exp(fM) + nn_exp(gM) via BOUNDED_NN_EXPECTATION_ADD *)
  SUBGOAL_THEN `nn_expectation (p:A prob_space) (\x:A. (fM:A->real) x + (gM:A->real) x) =
    nn_expectation p fM + nn_expectation p gM` SUBST1_TAC THENL
  [MATCH_MP_TAC BOUNDED_NN_EXPECTATION_ADD THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL [EXISTS_TAC `M:real` THEN ASM_SIMP_TAC[];
                    EXISTS_TAC `M:real` THEN ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  (* nn_exp(fM) <= nn_exp(|f|) and nn_exp(gM) <= nn_exp(|g|) *)
  SUBGOAL_THEN `nn_expectation (p:A prob_space) (fM:A->real) <=
    nn_expectation p (\x:A. abs((f:A->real) x))` ASSUME_TAC THENL
  [MATCH_MP_TAC NN_EXPECTATION_MONO THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "fM" THEN BETA_TAC THEN
    REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `nn_expectation (p:A prob_space) (gM:A->real) <=
    nn_expectation p (\x:A. abs((g:A->real) x))` ASSUME_TAC THENL
  [MATCH_MP_TAC NN_EXPECTATION_MONO THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "gM" THEN BETA_TAC THEN
    REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* Combine: E[h] <= nn_exp(fM) + nn_exp(gM) <= Bf + Bg *)
  ASM_REAL_ARITH_TAC);;

(* Simple expectations are bounded by nn_expectation for integrable functions *)
let NN_EXPECTATION_LE = prove
 (`!p:A prob_space g f.
   simple_rv p g /\
   (!x. x IN prob_carrier p ==> &0 <= g x) /\
   (!x. x IN prob_carrier p ==> g x <= f x) /\
   integrable p f /\
   (!x. x IN prob_carrier p ==> &0 <= f x)
   ==> simple_expectation p g <= nn_expectation p f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[nn_expectation] THEN
  SUBGOAL_THEN `simple_expectation (p:A prob_space) (g:A->real) IN
    {simple_expectation p g' | g' | simple_rv p g' /\
     (!x. x IN prob_carrier p ==> &0 <= g' x) /\
     (!x. x IN prob_carrier p ==> g' x <= (f:A->real) x)}` ASSUME_TAC THENL
  [REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `g:A->real` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [integrable]) THEN
  STRIP_TAC THEN
  ABBREV_TAC `S = {simple_expectation (p:A prob_space) g' | g' |
    simple_rv p g' /\ (!x. x IN prob_carrier p ==> &0 <= g' x) /\
    (!x. x IN prob_carrier p ==> g' x <= (f:A->real) x)}` THEN
  SUBGOAL_THEN `!y:real. y IN S ==> y <= B` ASSUME_TAC THENL
  [EXPAND_TAC "S" THEN X_GEN_TAC `y:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
   GEN_TAC THEN DISCH_TAC THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(f:A->real) x` THEN
   ASM_SIMP_TAC[REAL_ARITH `&0 <= f ==> f <= abs f`];
   ALL_TAC] THEN
  MP_TAC(SPEC `S:real->bool` SUP) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `simple_expectation (p:A prob_space) g` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `B:real` THEN ASM_MESON_TAC[]];
   DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (K ALL_TAC)) THEN
   DISCH_THEN(MP_TAC o SPEC `simple_expectation (p:A prob_space) g`) THEN
   ASM_REWRITE_TAC[]]);;

(* Scalar multiplication for nn_expectation of nonneg integrable functions *)
let NN_EXPECTATION_CMUL = prove
 (`!p:A prob_space c f.
     &0 <= c /\
     integrable p f /\
     (!x. x IN prob_carrier p ==> &0 <= f x)
     ==> nn_expectation p (\x. c * f x) = c * nn_expectation p f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `c = &0` THENL
  [ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
   SUBGOAL_THEN `nn_expectation (p:A prob_space) (\x:A. &0) =
     simple_expectation p (\x:A. &0)` SUBST1_TAC THENL
   [MATCH_MP_TAC NN_EXPECTATION_SIMPLE THEN
    REWRITE_TAC[SIMPLE_RV_CONST] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SIMPLE_EXPECTATION_CONST]];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
  [(* <= direction: nn_exp(c*f) <= c * nn_exp(f) *)
   CONV_TAC(LAND_CONV(REWR_CONV nn_expectation)) THEN
   MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `simple_expectation (p:A prob_space) (\x:A. &0)` THEN
    EXISTS_TAC `\x:A. &0` THEN
    REWRITE_TAC[SIMPLE_RV_CONST] THEN BETA_TAC THEN
    CONJ_TAC THENL [REAL_ARITH_TAC;
      GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[]];
    X_GEN_TAC `y:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `simple_expectation (p:A prob_space) (g:A->real) =
      c * simple_expectation p (\x:A. inv(c) * (g:A->real) x)` SUBST1_TAC THENL
    [SUBGOAL_THEN `simple_expectation (p:A prob_space) (\x:A. inv(c) * (g:A->real) x) =
      inv(c) * simple_expectation p g` SUBST1_TAC THENL
     [MATCH_MP_TAC SIMPLE_EXPECTATION_CMUL THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[REAL_MUL_ASSOC] THEN
      SUBGOAL_THEN `c * inv(c:real) = &1` (fun th -> REWRITE_TAC[th; REAL_MUL_LID]) THEN
      MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC NN_EXPECTATION_LE THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC SIMPLE_RV_CMUL THEN ASM_REWRITE_TAC[];
     GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
     MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]];
     GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
     SUBGOAL_THEN `inv(c) * (g:A->real) x <= inv(c) * (c * (f:A->real) x)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]];
      ONCE_REWRITE_TAC[REAL_MUL_ASSOC] THEN
      SUBGOAL_THEN `inv(c:real) * c = &1` (fun th -> REWRITE_TAC[th; REAL_MUL_LID]) THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[]]]];
   (* >= direction: c * nn_exp(f) <= nn_exp(c*f) *)
   SUBGOAL_THEN `nn_expectation (p:A prob_space) (f:A->real) <=
     inv(c) * nn_expectation p (\x:A. c * f x)` MP_TAC THENL
   [CONV_TAC(LAND_CONV(REWR_CONV nn_expectation)) THEN
    MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
    [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
     EXISTS_TAC `simple_expectation (p:A prob_space) (\x:A. &0)` THEN
     EXISTS_TAC `\x:A. &0` THEN
     REWRITE_TAC[SIMPLE_RV_CONST] THEN BETA_TAC THEN
     CONJ_TAC THENL [REAL_ARITH_TAC; ASM_MESON_TAC[]];
     X_GEN_TAC `y:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN `c * simple_expectation (p:A prob_space) (g:A->real) <=
       nn_expectation p (\x:A. c * (f:A->real) x)` MP_TAC THENL
     [SUBGOAL_THEN `c * simple_expectation (p:A prob_space) (g:A->real) =
       simple_expectation p (\x:A. c * (g:A->real) x)` SUBST1_TAC THENL
      [MATCH_MP_TAC(GSYM SIMPLE_EXPECTATION_CMUL) THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
      MATCH_MP_TAC NN_EXPECTATION_LE THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
      [MATCH_MP_TAC SIMPLE_RV_CMUL THEN ASM_REWRITE_TAC[];
       GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
       MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
       GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
       MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
       MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
       GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
       ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      DISCH_TAC THEN
      SUBGOAL_THEN `simple_expectation (p:A prob_space) (g:A->real) =
        inv(c) * (c * simple_expectation p g)` SUBST1_TAC THENL
      [ONCE_REWRITE_TAC[REAL_MUL_ASSOC] THEN
       SUBGOAL_THEN `inv(c:real) * c = &1` (fun th -> REWRITE_TAC[th; REAL_MUL_LID]) THEN
       MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]]]];
    DISCH_TAC THEN
    SUBGOAL_THEN `c * nn_expectation (p:A prob_space) (f:A->real) <=
      c * (inv(c) * nn_expectation p (\x:A. c * f x))` MP_TAC THENL
    [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
     ONCE_REWRITE_TAC[REAL_MUL_ASSOC] THEN
     SUBGOAL_THEN `c * inv(c:real) = &1` (fun th -> REWRITE_TAC[th; REAL_MUL_LID]) THEN
     MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REWRITE_TAC[]]]]);;

(* ========================================================================= *)
(* Phase 10b: EXPECTATION theorems for integrable functions                  *)
(* ========================================================================= *)

(* EXPECTATION_CMUL: c * E[f] = E[c * f] for integrable f *)
let EXPECTATION_CMUL = prove
 (`!p:A prob_space c f. integrable p f
    ==> expectation p (\x. c * f x) = c * expectation p f`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!d. &0 <= d ==>
    expectation (p:A prob_space) (\x:A. d * (f:A->real) x) = d * expectation p f`
    ASSUME_TAC THENL
  [X_GEN_TAC `d:real` THEN DISCH_TAC THEN
   REWRITE_TAC[expectation] THEN
   (* Rewrite pos part: max(d*f x, 0) = d * max(f x, 0) *)
   SUBGOAL_THEN `nn_expectation (p:A prob_space) (\x. max (d * (f:A->real) x) (&0)) =
     nn_expectation p (\x. d * max (f x) (&0))` SUBST1_TAC THENL
   [MATCH_MP_TAC NN_EXPECTATION_EXT THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    BETA_TAC THEN
    ASM_CASES_TAC `&0 <= (f:A->real) x` THENL
    [ASM_SIMP_TAC[REAL_ARITH `&0 <= f ==> max f (&0) = f`] THEN
     MATCH_MP_TAC(REAL_ARITH `&0 <= d * f ==> max (d * f) (&0) = d * f`) THEN
     MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
     ASM_SIMP_TAC[REAL_ARITH `~(&0 <= f) ==> max f (&0) = &0`] THEN
     REWRITE_TAC[REAL_MUL_RZERO] THEN
     MATCH_MP_TAC(REAL_ARITH `d * f <= &0 ==> max (d * f) (&0) = &0`) THEN
     SUBGOAL_THEN `d * (f:A->real) x <= d * &0` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_MUL_RZERO]]];
    ALL_TAC] THEN
   (* Rewrite neg part: max(-(d*f x), 0) = d * max(-f x, 0) *)
   SUBGOAL_THEN `nn_expectation (p:A prob_space) (\x. max (--(d * (f:A->real) x)) (&0)) =
     nn_expectation p (\x. d * max (--(f x)) (&0))` SUBST1_TAC THENL
   [MATCH_MP_TAC NN_EXPECTATION_EXT THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    BETA_TAC THEN REWRITE_TAC[GSYM REAL_MUL_RNEG] THEN
    ASM_CASES_TAC `&0 <= --((f:A->real) x)` THENL
    [ASM_SIMP_TAC[REAL_ARITH `&0 <= f ==> max f (&0) = f`] THEN
     MATCH_MP_TAC(REAL_ARITH `&0 <= d * f ==> max (d * f) (&0) = d * f`) THEN
     MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
     ASM_SIMP_TAC[REAL_ARITH `~(&0 <= f) ==> max f (&0) = &0`] THEN
     REWRITE_TAC[REAL_MUL_RZERO] THEN
     MATCH_MP_TAC(REAL_ARITH `d * f <= &0 ==> max (d * f) (&0) = &0`) THEN
     SUBGOAL_THEN `d * --((f:A->real) x) <= d * &0` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_MUL_RZERO]]];
    ALL_TAC] THEN
   (* Apply NN_EXPECTATION_CMUL to both parts *)
   SUBGOAL_THEN `nn_expectation (p:A prob_space) (\x:A. d * max ((f:A->real) x) (&0)) =
     d * nn_expectation p (\x. max (f x) (&0))` SUBST1_TAC THENL
   [MATCH_MP_TAC NN_EXPECTATION_CMUL THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [MATCH_MP_TAC INTEGRABLE_POS_PART THEN ASM_REWRITE_TAC[];
                     GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
   SUBGOAL_THEN `nn_expectation (p:A prob_space) (\x:A. d * max (--((f:A->real) x)) (&0)) =
     d * nn_expectation p (\x. max (--(f x)) (&0))` SUBST1_TAC THENL
   [MATCH_MP_TAC NN_EXPECTATION_CMUL THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [MATCH_MP_TAC INTEGRABLE_NEG_PART THEN ASM_REWRITE_TAC[];
                     GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= c` THENL
  [ASM_SIMP_TAC[];
   SUBGOAL_THEN `&0 <= --c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `random_variable (p:A prob_space) (\x:A. --c * (f:A->real) x)` ASSUME_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_MESON_TAC[integrable]; ALL_TAC] THEN
   SUBGOAL_THEN `(\x:A. c * (f:A->real) x) = (\x. --(--c * f x))`
     (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; REAL_MUL_LNEG; REAL_NEG_NEG]; ALL_TAC] THEN
   ASM_SIMP_TAC[EXPECTATION_NEG] THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC]);;

(* EXPECTATION_NEG_INTEGRABLE: E[-f] = -E[f] for integrable f *)
let EXPECTATION_NEG_INTEGRABLE = prove
 (`!p:A prob_space f.
    integrable p f
    ==> expectation p (\x. --(f x)) = --(expectation p f)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`p:A prob_space`; `-- &1`; `f:A->real`] EXPECTATION_CMUL) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `-- &1 * x = --x`]);;

(* EXPECTATION_ADD: E[f + g] = E[f] + E[g] for integrable f, g *)
let EXPECTATION_ADD = prove
 (`!p:A prob_space f g.
    integrable p f /\ integrable p g
    ==> expectation p (\x. f x + g x) = expectation p f + expectation p g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[expectation] THEN
  (* Establish integrability and rv of all parts *)
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. (f:A->real) x + (g:A->real) x)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. max ((f:A->real) x) (&0))` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_POS_PART THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. max (--((f:A->real) x)) (&0))` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_NEG_PART THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. max ((g:A->real) x) (&0))` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_POS_PART THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. max (--((g:A->real) x)) (&0))` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_NEG_PART THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. max ((f:A->real) x + (g:A->real) x) (&0))` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_POS_PART THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. max (--((f:A->real) x + (g:A->real) x)) (&0))` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_NEG_PART THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `random_variable (p:A prob_space) (f:A->real)` ASSUME_TAC THENL
  [ASM_MESON_TAC[integrable]; ALL_TAC] THEN
  SUBGOAL_THEN `random_variable (p:A prob_space) (g:A->real)` ASSUME_TAC THENL
  [ASM_MESON_TAC[integrable]; ALL_TAC] THEN
  (* L1: split neg parts *)
  SUBGOAL_THEN
    `nn_expectation (p:A prob_space) (\x. max (--((f:A->real) x)) (&0)) +
     nn_expectation p (\x. max (--((g:A->real) x)) (&0)) =
     nn_expectation p (\x. max (--(f x)) (&0) + max (--(g x)) (&0))`
    (LABEL_TAC "L1") THENL
  [CONV_TAC SYM_CONV THEN MATCH_MP_TAC NN_EXPECTATION_ADD THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_POS_PART THEN MATCH_MP_TAC RANDOM_VARIABLE_NEG THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RANDOM_VARIABLE_POS_PART THEN MATCH_MP_TAC RANDOM_VARIABLE_NEG THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* L2: split pos parts *)
  SUBGOAL_THEN
    `nn_expectation (p:A prob_space) (\x. max ((f:A->real) x) (&0)) +
     nn_expectation p (\x. max ((g:A->real) x) (&0)) =
     nn_expectation p (\x. max (f x) (&0) + max (g x) (&0))`
    (LABEL_TAC "L2") THENL
  [CONV_TAC SYM_CONV THEN MATCH_MP_TAC NN_EXPECTATION_ADD THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_POS_PART THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RANDOM_VARIABLE_POS_PART THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* L3: split pos_fg + (neg_f + neg_g) *)
  SUBGOAL_THEN
    `nn_expectation (p:A prob_space) (\x. max ((f:A->real) x + (g:A->real) x) (&0)) +
     nn_expectation p (\x. max (--(f x)) (&0) + max (--(g x)) (&0)) =
     nn_expectation p (\x. max (f x + g x) (&0) + (max (--(f x)) (&0) + max (--(g x)) (&0)))`
    (LABEL_TAC "L3") THENL
  [CONV_TAC SYM_CONV THEN MATCH_MP_TAC NN_EXPECTATION_ADD THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_POS_PART THEN MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC RANDOM_VARIABLE_POS_PART THEN
    TRY(MATCH_MP_TAC RANDOM_VARIABLE_NEG) THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN REAL_ARITH_TAC;
    MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* L4: split neg_fg + (pos_f + pos_g) *)
  SUBGOAL_THEN
    `nn_expectation (p:A prob_space) (\x. max (--((f:A->real) x + (g:A->real) x)) (&0)) +
     nn_expectation p (\x. max (f x) (&0) + max (g x) (&0)) =
     nn_expectation p (\x. max (--(f x + g x)) (&0) + (max (f x) (&0) + max (g x) (&0)))`
    (LABEL_TAC "L4") THENL
  [CONV_TAC SYM_CONV THEN MATCH_MP_TAC NN_EXPECTATION_ADD THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_POS_PART THEN MATCH_MP_TAC RANDOM_VARIABLE_NEG THEN
    MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC RANDOM_VARIABLE_POS_PART THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN REAL_ARITH_TAC;
    MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* L5: pointwise identity *)
  SUBGOAL_THEN
    `nn_expectation (p:A prob_space) (\x. max ((f:A->real) x + (g:A->real) x) (&0) +
      max (--((f:A->real) x)) (&0) + max (--((g:A->real) x)) (&0)) =
     nn_expectation p (\x. max (--((f:A->real) x + (g:A->real) x)) (&0) +
      max ((f:A->real) x) (&0) + max ((g:A->real) x) (&0))`
    (LABEL_TAC "L5") THENL
  [MATCH_MP_TAC NN_EXPECTATION_EXT THEN GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* EXPECTATION_POS: E[f] >= 0 for nonneg integrable f *)
let EXPECTATION_POS = prove
 (`!p:A prob_space f.
    integrable p f /\
    (!x. x IN prob_carrier p ==> &0 <= f x)
    ==> &0 <= expectation p f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[expectation] THEN
  SUBGOAL_THEN `nn_expectation (p:A prob_space) (\x. max (--((f:A->real) x)) (&0)) =
    &0` SUBST1_TAC THENL
  [SUBGOAL_THEN `nn_expectation (p:A prob_space) (\x. max (--((f:A->real) x)) (&0)) =
    nn_expectation p (\x:A. &0)` SUBST1_TAC THENL
   [MATCH_MP_TAC NN_EXPECTATION_EXT THEN GEN_TAC THEN DISCH_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= f ==> max (--f) (&0) = &0`) THEN
    ASM_SIMP_TAC[]; ALL_TAC] THEN
   MP_TAC(SPECL [`p:A prob_space`; `\x:A. &0`] NN_EXPECTATION_SIMPLE) THEN
   REWRITE_TAC[SIMPLE_RV_CONST] THEN BETA_TAC THEN
   ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[SIMPLE_EXPECTATION_CONST]; ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  SUBGOAL_THEN `nn_expectation (p:A prob_space) (\x. max ((f:A->real) x) (&0)) =
    nn_expectation p f` SUBST1_TAC THENL
  [MATCH_MP_TAC NN_EXPECTATION_EXT THEN GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= f ==> max f (&0) = f`) THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `simple_expectation (p:A prob_space) (\x:A. &0) <= nn_expectation p (f:A->real)` MP_TAC THENL
  [MATCH_MP_TAC NN_EXPECTATION_LE THEN ASM_REWRITE_TAC[SIMPLE_RV_CONST] THEN
   BETA_TAC THEN GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
   REWRITE_TAC[SIMPLE_EXPECTATION_CONST]]);;

(* EXPECTATION_MONO: f <= g pointwise ==> E[f] <= E[g] *)
let EXPECTATION_MONO = prove
 (`!p:A prob_space f g.
    integrable p f /\ integrable p g /\
    (!x. x IN prob_carrier p ==> f x <= g x)
    ==> expectation p f <= expectation p g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= expectation (p:A prob_space) (\x:A. (g:A->real) x - (f:A->real) x)` MP_TAC THENL
  [MATCH_MP_TAC EXPECTATION_POS THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(\x:A. (g:A->real) x - (f:A->real) x) = (\x. g x + --(f x))` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INTEGRABLE_NEG THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:A->real) x <= (g:A->real) x` MP_TAC THENL
    [ASM_SIMP_TAC[]; REAL_ARITH_TAC]];
   ALL_TAC] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. (g:A->real) x - (f:A->real) x) =
    expectation p g - expectation p f` SUBST1_TAC THENL
  [SUBGOAL_THEN `(\x:A. (g:A->real) x - (f:A->real) x) = (\x. g x + --(f x))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`p:A prob_space`; `g:A->real`; `\x:A. --((f:A->real) x)`]
     EXPECTATION_ADD) THEN
   BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_NEG THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   ASM_SIMP_TAC[EXPECTATION_NEG_INTEGRABLE] THEN REAL_ARITH_TAC;
   REAL_ARITH_TAC]);;

(* EXPECTATION_SUB: E[f - g] = E[f] - E[g] *)
let EXPECTATION_SUB = prove
 (`!p:A prob_space f g.
    integrable p f /\ integrable p g
    ==> expectation p (\x. f x - g x) = expectation p f - expectation p g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x:A. (f:A->real) x - (g:A->real) x) = (\x. f x + --(g x))` SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`p:A prob_space`; `f:A->real`; `\x:A. --((g:A->real) x)`]
    EXPECTATION_ADD) THEN
  BETA_TAC THEN ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_NEG THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  ASM_SIMP_TAC[EXPECTATION_NEG_INTEGRABLE] THEN REAL_ARITH_TAC);;

(* EXPECTATION_ABS_BOUND: |E[f]| <= E[|f|] *)
let EXPECTATION_ABS_BOUND = prove
 (`!p:A prob_space f.
    integrable p f
    ==> abs(expectation p f) <= expectation p (\x. abs(f x))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_ABS_BOUNDS] THEN CONJ_TAC THENL
  [SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. --(abs((f:A->real) x))) <=
     expectation p f` MP_TAC THENL
   [MATCH_MP_TAC EXPECTATION_MONO THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_NEG THEN MATCH_MP_TAC INTEGRABLE_ABS THEN ASM_REWRITE_TAC[];
     GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC];
    ASM_SIMP_TAC[EXPECTATION_NEG_INTEGRABLE; INTEGRABLE_ABS] THEN REAL_ARITH_TAC];
   MATCH_MP_TAC EXPECTATION_MONO THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ABS THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC]]);;

(* Subtraction of integrable functions is integrable *)
let INTEGRABLE_SUB = prove
 (`!p:A prob_space f g.
    integrable p f /\ integrable p g
    ==> integrable p (\x. f x - g x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_sub] THEN
  MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_SIMP_TAC[INTEGRABLE_NEG]);;

(* ========================================================================= *)
(* Phase 11: Variance, Markov, and Chebyshev for integrable functions        *)
(* ========================================================================= *)

(* Constants are integrable *)
let INTEGRABLE_CONST = prove
 (`!p:A prob_space c. integrable p (\x:A. c)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
  EXISTS_TAC `abs c` THEN REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN REAL_ARITH_TAC);;

(* Level set measurability: {f > a} is an event for random variable f *)
let RV_LEVEL_GT_IN_EVENTS = prove
 (`!p:A prob_space f a.
    random_variable p f
    ==> {x | x IN prob_carrier p /\ f x > a} IN prob_events p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[random_variable] THEN DISCH_TAC THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ (f:A->real) x > a} =
    prob_carrier p DIFF {x | x IN prob_carrier p /\ f x <= a}` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN GEN_TAC THEN
   ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   MATCH_MP_TAC PROB_DIFF_IN_EVENTS THEN REWRITE_TAC[PROB_CARRIER_IN_EVENTS] THEN
   ASM_REWRITE_TAC[]]);;

(* Level set measurability: {f >= a} is an event for random variable f *)
let RV_LEVEL_GE_IN_EVENTS = prove
 (`!p:A prob_space f a.
    random_variable p f
    ==> {x | x IN prob_carrier p /\ f x >= a} IN prob_events p`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ f x >= a} =
    prob_carrier p DIFF {x | x IN prob_carrier p /\ (f:A->real) x < a}` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN GEN_TAC THEN
   ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   MATCH_MP_TAC PROB_DIFF_IN_EVENTS THEN REWRITE_TAC[PROB_CARRIER_IN_EVENTS] THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ (f:A->real) x < a} =
     {x | x IN prob_carrier p /\ (\x. --(f x)) x > --a}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN BETA_TAC THEN
    ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC RV_LEVEL_GT_IN_EVENTS THEN MATCH_MP_TAC RANDOM_VARIABLE_NEG THEN
    ASM_REWRITE_TAC[]]]);;

(* Indicator functions of events are integrable *)
let INTEGRABLE_INDICATOR = prove
 (`!p:A prob_space a. a IN prob_events p ==> integrable p (indicator_fn a)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `&1` THEN
  CONJ_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `a:A->bool`] SIMPLE_RV_INDICATOR) THEN
   ASM_REWRITE_TAC[] THEN SIMP_TAC[simple_rv];
   GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[indicator_fn] THEN
   COND_CASES_TAC THEN REAL_ARITH_TAC]);;

(* E[indicator_fn a] = prob p a *)
let EXPECTATION_INDICATOR = prove
 (`!p:A prob_space a. a IN prob_events p
    ==> expectation p (indicator_fn a) = prob p a`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (indicator_fn (a:A->bool)) =
    simple_expectation p (indicator_fn a)` SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN
   MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[];
   ASM_SIMP_TAC[SIMPLE_EXPECTATION_INDICATOR]]);;

(* Variance of a constant is zero *)
let VARIANCE_CONST = prove
 (`!p:A prob_space c. variance p (\x:A. c) = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[variance; EXPECTATION_CONST] THEN
  REWRITE_TAC[REAL_SUB_REFL; REAL_POW_ZERO; ARITH; EXPECTATION_CONST]);;

(* Variance is nonneg *)
let VARIANCE_NONNEG = prove
 (`!p:A prob_space f. integrable p (\x. (f x - expectation p f) pow 2)
    ==> &0 <= variance p f`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[variance] THEN
  MATCH_MP_TAC EXPECTATION_POS THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_LE_POW_2]);;

(* Variance alternative formula: Var(X) = E[X^2] - (E[X])^2 *)
let VARIANCE_ALT = prove
 (`!p:A prob_space f.
    integrable p f /\ integrable p (\x. (f x) pow 2)
    ==> variance p f = expectation p (\x. (f x) pow 2) - (expectation p f) pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `mu = expectation (p:A prob_space) f` THEN
  REWRITE_TAC[variance] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\x:A. ((f:A->real) x - mu) pow 2) = (\x. f x pow 2 - &2 * mu * f x + mu pow 2)` SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. &2 * mu * (f:A->real) x)` ASSUME_TAC THENL
  [SUBGOAL_THEN `(\x:A. &2 * mu * (f:A->real) x) = (\x. (&2 * mu) * f x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; REAL_MUL_ASSOC]; ALL_TAC] THEN
   MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
   ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. mu pow 2)` ASSUME_TAC THENL
  [REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. (f:A->real) x pow 2 - &2 * mu * f x + mu pow 2) =
    expectation p (\x. f x pow 2) - expectation p (\x. &2 * mu * f x) + expectation p (\x. mu pow 2)` SUBST1_TAC THENL
  [SUBGOAL_THEN `(\x:A. (f:A->real) x pow 2 - &2 * mu * f x + mu pow 2) =
    (\x. f x pow 2 + (--(&2 * mu * f x) + mu pow 2))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. (f:A->real) x pow 2 + (--(&2 * mu * f x) + mu pow 2)) =
     expectation p (\x. f x pow 2) + expectation p (\x. --(&2 * mu * f x) + mu pow 2)` SUBST1_TAC THENL
   [MATCH_MP_TAC EXPECTATION_ADD THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(\x:A. --((&2 * mu) * (f:A->real) x) + mu pow 2) = (\x. (--(&2 * mu * f x)) + mu pow 2)` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM; REAL_MUL_ASSOC]; ALL_TAC] THEN
    MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_NEG THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. --(&2 * mu * (f:A->real) x) + mu pow 2) =
     expectation p (\x. --(&2 * mu * f x)) + expectation p (\x. mu pow 2)` SUBST1_TAC THENL
   [MATCH_MP_TAC EXPECTATION_ADD THEN CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_NEG THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. --(&2 * mu * (f:A->real) x)) =
     --(expectation p (\x. &2 * mu * f x))` SUBST1_TAC THENL
   [MATCH_MP_TAC EXPECTATION_NEG_INTEGRABLE THEN ASM_REWRITE_TAC[];
    REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. &2 * mu * (f:A->real) x) =
    &2 * mu * expectation p f` SUBST1_TAC THENL
  [SUBGOAL_THEN `(\x:A. &2 * mu * (f:A->real) x) = (\x. (&2 * mu) * f x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; REAL_MUL_ASSOC]; ALL_TAC] THEN
   SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. (&2 * mu) * (f:A->real) x) = (&2 * mu) * expectation p f` MP_TAC THENL
   [MATCH_MP_TAC EXPECTATION_CMUL THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_MUL_ASSOC]];
   ALL_TAC] THEN
  REWRITE_TAC[EXPECTATION_CONST] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Var(cX) = c^2 * Var(X) *)
let VARIANCE_CMUL = prove
 (`!p:A prob_space c f.
    integrable p f /\ integrable p (\x. (f x) pow 2)
    ==> variance p (\x. c * f x) = c pow 2 * variance p f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `mu = expectation (p:A prob_space) f` THEN
  REWRITE_TAC[variance] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. c * (f:A->real) x) = c * mu` SUBST1_TAC THENL
  [SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. c * (f:A->real) x) = c * expectation p f` MP_TAC THENL
   [MATCH_MP_TAC EXPECTATION_CMUL THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `(\x:A. (c * (f:A->real) x - c * mu) pow 2) = (\x. c pow 2 * (f x - mu) pow 2)` SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
   REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_POW_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. ((f:A->real) x - mu) pow 2)` ASSUME_TAC THENL
  [SUBGOAL_THEN `(\x:A. ((f:A->real) x - mu) pow 2) =
    (\x. f x pow 2 + (--(&2 * mu) * f x + mu pow 2))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
     REWRITE_TAC[INTEGRABLE_CONST]]];
   ALL_TAC] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. c pow 2 * ((f:A->real) x - mu) pow 2) =
    c pow 2 * expectation p (\x. (f x - mu) pow 2)` SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_CMUL THEN ASM_REWRITE_TAC[];
   ASM_REWRITE_TAC[]]);;

(* Var(X + c) = Var(X): shifting by a constant doesn't change variance *)
let VARIANCE_SHIFT = prove
 (`!p:A prob_space c f.
    integrable p f
    ==> variance p (\x. f x + c) = variance p f`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[variance] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. (f:A->real) x + c) =
    expectation p f + c` SUBST1_TAC THENL
  [SUBGOAL_THEN `(\x:A. (f:A->real) x + c) = (\x. f x + (\x:A. c) x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
   SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. (f:A->real) x + (\x:A. c) x) =
     expectation p f + expectation p (\x:A. c)` MP_TAC THENL
   [MATCH_MP_TAC EXPECTATION_ADD THEN
    ASM_REWRITE_TAC[INTEGRABLE_CONST] THEN
    REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[EXPECTATION_CONST; ETA_AX]];
   ALL_TAC] THEN
  SUBGOAL_THEN `(\x:A. (((f:A->real) x + c) - (expectation p f + c)) pow 2) =
    (\x. (f x - expectation p f) pow 2)` (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:A` THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

(* Markov's inequality for integrable functions *)
let MARKOV_INEQUALITY = prove
 (`!p:A prob_space f a.
    integrable p f /\
    (!x. x IN prob_carrier p ==> &0 <= f x) /\
    &0 < a
    ==> prob p {x | x IN prob_carrier p /\ f x > a} <=
        expectation p f / a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `S = {x:A | x IN prob_carrier p /\ f x > a}` THEN
  SUBGOAL_THEN `(S:A->bool) IN prob_events p` ASSUME_TAC THENL
  [EXPAND_TAC "S" THEN MATCH_MP_TAC RV_LEVEL_GT_IN_EVENTS THEN
   UNDISCH_TAC `integrable (p:A prob_space) f` THEN SIMP_TAC[integrable];
   ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (indicator_fn S)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN prob_carrier p ==> a * indicator_fn S x <= (f:A->real) x` ASSUME_TAC THENL
  [X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[indicator_fn] THEN
   COND_CASES_TAC THENL
   [REWRITE_TAC[REAL_MUL_RID] THEN
    SUBGOAL_THEN `x IN (S:A->bool)` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
    REWRITE_TAC[REAL_MUL_RZERO] THEN ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  SUBGOAL_THEN `a * prob p (S:A->bool) = expectation (p:A prob_space) (\x. a * indicator_fn S x)` SUBST1_TAC THENL
  [SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. a * indicator_fn S x) = a * expectation p (indicator_fn S)` SUBST1_TAC THENL
   [MATCH_MP_TAC EXPECTATION_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
    ASM_SIMP_TAC[EXPECTATION_INDICATOR]];
   ALL_TAC] THEN
  MATCH_MP_TAC EXPECTATION_MONO THEN
  BETA_TAC THEN ASM_REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[ETA_AX]);;

(* Chebyshev's inequality for integrable functions *)
let CHEBYSHEV_INEQUALITY = prove
 (`!p:A prob_space X t.
    integrable p X /\
    integrable p (\x. (X x - expectation p X) pow 2) /\
    &0 < t
    ==> prob p {x | x IN prob_carrier p /\ abs(X x - expectation p X) >= t} <=
        variance p X / t pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `mu = expectation (p:A prob_space) X` THEN
  ABBREV_TAC `S = {x:A | x IN prob_carrier p /\ abs(X x - mu) >= t}` THEN
  SUBGOAL_THEN `random_variable (p:A prob_space) X` ASSUME_TAC THENL
  [UNDISCH_TAC `integrable (p:A prob_space) X` THEN SIMP_TAC[integrable]; ALL_TAC] THEN
  SUBGOAL_THEN `(S:A->bool) IN prob_events p` ASSUME_TAC THENL
  [EXPAND_TAC "S" THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ abs((X:A->real) x - mu) >= t} =
     {x | x IN prob_carrier p /\ X x - mu >= t} UNION
     {x | x IN prob_carrier p /\ --(X x - mu) >= t}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN GEN_TAC THEN
    ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC PROB_UNION_IN_EVENTS THEN CONJ_TAC THENL
    [MATCH_MP_TAC RV_LEVEL_GE_IN_EVENTS THEN
     MATCH_MP_TAC RANDOM_VARIABLE_SUB_CONST THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC RV_LEVEL_GE_IN_EVENTS THEN
     MATCH_MP_TAC RANDOM_VARIABLE_NEG THEN
     MATCH_MP_TAC RANDOM_VARIABLE_SUB_CONST THEN ASM_REWRITE_TAC[]]];
   ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (indicator_fn S)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `prob p (S:A->bool) = expectation (p:A prob_space) (indicator_fn S)` SUBST1_TAC THENL
  [MATCH_MP_TAC(GSYM EXPECTATION_INDICATOR) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `variance (p:A prob_space) X / t pow 2 =
    expectation p (\x:A. ((X x - mu) pow 2) / t pow 2)` SUBST1_TAC THENL
  [SUBGOAL_THEN `variance (p:A prob_space) X = expectation p (\x. (X x - mu) pow 2)` SUBST1_TAC THENL
   [REWRITE_TAC[variance] THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `(\x:A. (((X:A->real) x - mu) pow 2) / t pow 2) =
      (\x. inv(t pow 2) * (X x - mu) pow 2)` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM; real_div; REAL_MUL_SYM]; ALL_TAC] THEN
    SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. inv(t pow 2) * ((X:A->real) x - mu) pow 2) =
      inv(t pow 2) * expectation p (\x. (X x - mu) pow 2)` MP_TAC THENL
    [MATCH_MP_TAC EXPECTATION_CMUL THEN ASM_REWRITE_TAC[];
     REAL_ARITH_TAC]];
   ALL_TAC] THEN
  MATCH_MP_TAC EXPECTATION_MONO THEN
  ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
  [SUBGOAL_THEN `(\x:A. (((X:A->real) x - mu) pow 2) / t pow 2) =
    (\x. inv(t pow 2) * (X x - mu) pow 2)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; real_div; REAL_MUL_SYM]; ALL_TAC] THEN
   MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
   ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THENL
  [SUBGOAL_THEN `(x:A) IN S` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
   SUBGOAL_THEN `t pow 2 <= ((X:A->real) x - mu) pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `t pow 2 <= abs((X:A->real) x - mu) pow 2` MP_TAC THENL
    [MATCH_MP_TAC REAL_POW_LE2 THEN
     UNDISCH_TAC `abs((X:A->real) x - mu) >= t` THEN
     UNDISCH_TAC `&0 < t` THEN REAL_ARITH_TAC;
     REWRITE_TAC[REAL_POW2_ABS]];
    ALL_TAC] THEN
   SUBGOAL_THEN `&0 < t pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REWRITE_TAC[REAL_MUL_LID] THEN
   ASM_REWRITE_TAC[];
   MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2]]);;

(* ========================================================================= *)
(* Phase 12: Sums of RVs and Weak Law of Large Numbers                       *)
(* ========================================================================= *)

(* Sum of simple RVs is simple *)
let SIMPLE_RV_SUM = prove
 (`!p:A prob_space X n.
    (!i. i <= n ==> simple_rv p (X i))
    ==> simple_rv p (\x. sum(0..n) (\i. X i x))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [REWRITE_TAC[NUMSEG_SING; SUM_SING; LE] THEN
   DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
   SIMP_TAC[ETA_AX];
   DISCH_TAC THEN
   SUBGOAL_THEN `(\x:A. sum(0..SUC n) (\i. (X:num->A->real) i x)) =
     (\x. sum(0..n) (\i. X i x) + X (SUC n) x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; SUM_CLAUSES_NUMSEG; LE_0]; ALL_TAC] THEN
   MATCH_MP_TAC SIMPLE_RV_ADD THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `(\x:A. (X:num->A->real) (SUC n) x) = X (SUC n)` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM; ETA_AX]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]]);;

(* Sum of integrable functions is integrable *)
let INTEGRABLE_SUM = prove
 (`!p:A prob_space X n.
    (!i. i <= n ==> integrable p (X i))
    ==> integrable p (\x. sum(0..n) (\i. X i x))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [REWRITE_TAC[NUMSEG_SING; SUM_SING; LE] THEN
   DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
   SIMP_TAC[ETA_AX];
   DISCH_TAC THEN
   SUBGOAL_THEN `(\x:A. sum(0..SUC n) (\i. (X:num->A->real) i x)) =
     (\x. sum(0..n) (\i. X i x) + X (SUC n) x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; SUM_CLAUSES_NUMSEG; LE_0]; ALL_TAC] THEN
   MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `(\x:A. (X:num->A->real) (SUC n) x) = X (SUC n)` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM; ETA_AX]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]]);;

(* Linearity of expectation for sums *)
let EXPECTATION_SUM = prove
 (`!p:A prob_space X n.
    (!i. i <= n ==> integrable p (X i))
    ==> expectation p (\x. sum(0..n) (\i. X i x)) =
        sum(0..n) (\i. expectation p (X i))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [REWRITE_TAC[NUMSEG_SING; SUM_SING; LE] THEN
   DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
   DISCH_TAC THEN
   SUBGOAL_THEN `(\x:A. (X:num->A->real) 0 x) = X 0` (fun th -> REWRITE_TAC[th]) THEN
   REWRITE_TAC[FUN_EQ_THM; ETA_AX];
   DISCH_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
   SUBGOAL_THEN `(\x:A. sum(0..SUC n) (\i. (X:num->A->real) i x)) =
     (\x. sum(0..n) (\i. X i x) + X (SUC n) x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; SUM_CLAUSES_NUMSEG; LE_0]; ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. sum(0..n) (\i. (X:num->A->real) i x))` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SUM THEN GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space) ((X:num->A->real) (SUC n))` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. sum(0..n) (\i. (X:num->A->real) i x) + X (SUC n) x) =
     expectation p (\x. sum(0..n) (\i. X i x)) + expectation p (X (SUC n))` SUBST1_TAC THENL
   [SUBGOAL_THEN `(\x:A. sum(0..n) (\i. (X:num->A->real) i x) + X (SUC n) x) =
     (\x. (\x. sum(0..n) (\i. X i x)) x + (X (SUC n)) x)` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
    MATCH_MP_TAC EXPECTATION_ADD THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. sum(0..n) (\i. (X:num->A->real) i x)) =
     sum(0..n) (\i. expectation p (X i))` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[]]]);;

(* Weak Law of Large Numbers *)
(* For pairwise independent, identically distributed simple RVs with common *)
(* mean mu and variance sigma2: P(|Sn/(n+1) - mu| >= epsilon) <= sigma2/((n+1)*epsilon^2) *)
let SIMPLE_WEAK_LAW_OF_LARGE_NUMBERS = prove
 (`!p:A prob_space X n mu sigma2 epsilon.
    (!i. i <= n ==> simple_rv p (X i)) /\
    (!i j. i <= n /\ j <= n /\ ~(i = j) ==> indep_rv p (X i) (X j)) /\
    (!i. i <= n ==> expectation p (X i) = mu) /\
    (!i. i <= n ==> variance p (X i) = sigma2) /\
    &0 < epsilon
    ==> prob p {x | x IN prob_carrier p /\
          abs(sum(0..n) (\i. X i x) / &(n + 1) - mu) >= epsilon} <=
        sigma2 / (&(n + 1) * epsilon pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Xbar = \x:A. sum(0..n) (\i. (X:num->A->real) i x) / &(n + 1)` THEN
  (* Xbar is simple_rv *)
  SUBGOAL_THEN `simple_rv (p:A prob_space) Xbar` ASSUME_TAC THENL
  [EXPAND_TAC "Xbar" THEN
   SUBGOAL_THEN `(\x:A. sum(0..n) (\i. (X:num->A->real) i x) / &(n + 1)) =
     (\x. inv(&(n + 1)) * sum(0..n) (\i. X i x))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; real_div; REAL_MUL_SYM]; ALL_TAC] THEN
   MATCH_MP_TAC SIMPLE_RV_CMUL THEN
   MATCH_MP_TAC SIMPLE_RV_SUM THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. sum (0..n) (\i. (X:num->A->real) i x) / &(n + 1) = Xbar x`
    (fun th -> REWRITE_TAC[th]) THENL
  [GEN_TAC THEN EXPAND_TAC "Xbar" THEN REWRITE_TAC[]; ALL_TAC] THEN
  (* E[Xbar] = mu *)
  SUBGOAL_THEN `expectation (p:A prob_space) Xbar = mu` ASSUME_TAC THENL
  [EXPAND_TAC "Xbar" THEN
   SUBGOAL_THEN `(\x:A. sum(0..n) (\i. (X:num->A->real) i x) / &(n + 1)) =
     (\x. inv(&(n + 1)) * sum(0..n) (\i. X i x))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; real_div; REAL_MUL_SYM]; ALL_TAC] THEN
   SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. inv(&(n + 1)) * sum(0..n) (\i. (X:num->A->real) i x)) =
     inv(&(n + 1)) * expectation p (\x. sum(0..n) (\i. X i x))` SUBST1_TAC THENL
   [MATCH_MP_TAC EXPECTATION_CMUL THEN
    MATCH_MP_TAC INTEGRABLE_SUM THEN GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC INTEGRABLE_SIMPLE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. sum(0..n) (\i. (X:num->A->real) i x)) =
     sum(0..n) (\i. expectation p (X i))` SUBST1_TAC THENL
   [MATCH_MP_TAC EXPECTATION_SUM THEN GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC INTEGRABLE_SIMPLE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
   ASM_SIMP_TAC[SUM_CONST_NUMSEG; SUB_0] THEN
   REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
   REWRITE_TAC[REAL_MUL_ASSOC] THEN
   SUBGOAL_THEN `inv(&n + &1) * (&n + &1) = &1` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_MUL_LINV THEN REAL_ARITH_TAC; REWRITE_TAC[REAL_MUL_LID]];
   ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x. sum(0..n) (\i. (X:num->A->real) i x))` ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_SUM THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  (* Var(Xbar) = sigma2 / (n+1) *)
  SUBGOAL_THEN `variance (p:A prob_space) Xbar = sigma2 / &(n + 1)` ASSUME_TAC THENL
  [EXPAND_TAC "Xbar" THEN
   SUBGOAL_THEN `(\x:A. sum(0..n) (\i. (X:num->A->real) i x) / &(n + 1)) =
     (\x. inv(&(n + 1)) * sum(0..n) (\i. X i x))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; real_div; REAL_MUL_SYM]; ALL_TAC] THEN
   SUBGOAL_THEN `variance (p:A prob_space) (\x:A. inv(&(n + 1)) * sum(0..n) (\i. (X:num->A->real) i x)) =
     inv(&(n + 1)) pow 2 * variance p (\x. sum(0..n) (\i. X i x))` SUBST1_TAC THENL
   [MATCH_MP_TAC VARIANCE_CMUL THEN CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_SIMPLE THEN ASM_REWRITE_TAC[];
     SUBGOAL_THEN `(\x:A. (\x. sum(0..n) (\i. (X:num->A->real) i x)) x pow 2) =
       (\x. sum(0..n) (\i. X i x) pow 2)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
     SUBGOAL_THEN `(\x:A. sum(0..n) (\i. (X:num->A->real) i x) pow 2) =
       (\x. (\x. sum(0..n) (\i. X i x)) x * (\x. sum(0..n) (\i. X i x)) x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; REAL_POW_2]; ALL_TAC] THEN
     MATCH_MP_TAC INTEGRABLE_SIMPLE THEN MATCH_MP_TAC SIMPLE_RV_MUL THEN
     ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   SUBGOAL_THEN `variance (p:A prob_space) (\x:A. sum(0..n) (\i. (X:num->A->real) i x)) =
     sum(0..n) (\i. variance p (X i))` SUBST1_TAC THENL
   [MATCH_MP_TAC VARIANCE_SUM_UNCORRELATED_SIMPLE THEN CONJ_TAC THENL
    [ASM_SIMP_TAC[];
     REPEAT STRIP_TAC THEN MATCH_MP_TAC COVARIANCE_INDEP_SIMPLE THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
   ASM_SIMP_TAC[SUM_CONST_NUMSEG; SUB_0] THEN
   REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
   SUBGOAL_THEN `~(&n + &1 = &0)` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_POW_2; real_div] THEN
   SUBGOAL_THEN `(inv(&n + &1) * inv(&n + &1)) * ((&n + &1) * sigma2) =
     inv(&n + &1) * (inv(&n + &1) * (&n + &1)) * sigma2` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_MUL_LINV; REAL_MUL_LID] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Apply Chebyshev *)
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ abs (Xbar x - mu) >= epsilon} =
    {x | x IN prob_carrier p /\ abs (Xbar x - expectation (p:A prob_space) Xbar) >= epsilon}`
    SUBST1_TAC THENL
  [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `prob p {x:A | x IN prob_carrier p /\ abs (Xbar x - expectation (p:A prob_space) Xbar) >= epsilon} <=
    variance p Xbar / epsilon pow 2` MP_TAC THENL
  [MATCH_MP_TAC SIMPLE_CHEBYSHEV_INEQUALITY THEN ASM_REWRITE_TAC[];
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[real_div; REAL_INV_MUL; GSYM REAL_MUL_ASSOC]]);;

(* ========================================================================= *)
(* Phase 13: Generalizing covariance and variance to integrable functions    *)
(* ========================================================================= *)

(* AM-GM inequality: |xy| <= (x^2 + y^2)/2 *)
let AM_GM_ABS = prove
 (`!x y:real. abs(x * y) <= inv(&2) * (x pow 2 + y pow 2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  SUBGOAL_THEN `&0 <= (abs x - abs y) pow 2` MP_TAC THENL
  [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN
  SUBGOAL_THEN `abs x * abs x = x pow 2` SUBST1_TAC THENL
  [REWRITE_TAC[REAL_POW_2] THEN
   ONCE_REWRITE_TAC[GSYM REAL_ABS_MUL] THEN
   REWRITE_TAC[REAL_ABS_REFL; REAL_LE_SQUARE]; ALL_TAC] THEN
  SUBGOAL_THEN `abs y * abs y = y pow 2` SUBST1_TAC THENL
  [REWRITE_TAC[REAL_POW_2] THEN
   ONCE_REWRITE_TAC[GSYM REAL_ABS_MUL] THEN
   REWRITE_TAC[REAL_ABS_REFL; REAL_LE_SQUARE]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* Domination: if |f| <= |h| pointwise and h integrable, then f integrable *)
let INTEGRABLE_DOMINATED = prove
 (`!p:A prob_space f h.
     random_variable p f /\ integrable p h /\
     (!x. x IN prob_carrier p ==> abs(f x) <= abs(h x))
     ==> integrable p f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[integrable] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [integrable]) THEN
  STRIP_TAC THEN EXISTS_TAC `B:real` THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:A` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((f:A->real) z)` THEN
  ASM_SIMP_TAC[]);;

(* Square-integrable implies product integrable (Cauchy-Schwarz corollary) *)
let INTEGRABLE_MUL_SQUARE = prove
 (`!p:A prob_space X Y.
     random_variable p X /\ random_variable p Y /\
     integrable p (\x. X x pow 2) /\ integrable p (\x. Y x pow 2)
     ==> integrable p (\x. X x * Y x)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRABLE_DOMINATED THEN
  EXISTS_TAC `\x:A. inv(&2) * ((X:A->real) x pow 2 + (Y:A->real) x pow 2)` THEN
  REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC INTEGRABLE_CMUL THEN MATCH_MP_TAC INTEGRABLE_ADD THEN
   ASM_REWRITE_TAC[];
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `inv(&2) * ((X:A->real) x pow 2 + (Y:A->real) x pow 2)` THEN
   REWRITE_TAC[AM_GM_ABS] THEN
   REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NUM] THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV THEN REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> x <= abs x`) THEN
    MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2]]]);;

(* Covariance is symmetric (no hypotheses needed) *)
let COVARIANCE_SYM_GENERAL = prove
 (`!p:A prob_space X Y. covariance p X Y = covariance p Y X`,
  REPEAT GEN_TAC THEN REWRITE_TAC[covariance] THEN
  MATCH_MP_TAC EXPECTATION_EXT THEN
  GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN REAL_ARITH_TAC);;

(* Cov(X,X) = Var(X) (no hypotheses needed) *)
let COVARIANCE_SELF_GENERAL = prove
 (`!p:A prob_space X. covariance p X X = variance p X`,
  REPEAT GEN_TAC THEN REWRITE_TAC[covariance; variance] THEN
  MATCH_MP_TAC EXPECTATION_EXT THEN
  GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[REAL_POW_2]);;

(* Cov(X,Y) = E[XY] - E[X]*E[Y] for integrable X, Y, XY *)
let COVARIANCE_ALT = prove
 (`!p:A prob_space X Y.
     integrable p X /\ integrable p Y /\ integrable p (\x. X x * Y x)
     ==> covariance p X Y =
         expectation p (\x. X x * Y x) - expectation p X * expectation p Y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[covariance] THEN
  ABBREV_TAC `a = expectation (p:A prob_space) (X:A->real)` THEN
  ABBREV_TAC `b = expectation (p:A prob_space) (Y:A->real)` THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. (--b) * (X:A->real) x + a * b)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[INTEGRABLE_CONST]]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space)
    (\x:A. (--a) * (Y:A->real) x + ((--b) * (X:A->real) x + a * b))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `(\x:A. ((X:A->real) x - a) * ((Y:A->real) x - b)) =
    (\x. X x * Y x + ((--a) * Y x + ((--b) * X x + a * b)))` SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EXPECTATION_ADD] THEN
  ASM_SIMP_TAC[EXPECTATION_ADD; INTEGRABLE_CMUL; INTEGRABLE_CONST] THEN
  ASM_SIMP_TAC[EXPECTATION_CMUL; EXPECTATION_CONST] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Cov(X+Y, Z) = Cov(X,Z) + Cov(Y,Z) for square-integrable functions *)
let COVARIANCE_ADD_LEFT = prove
 (`!p:A prob_space X Y Z.
     integrable p X /\ integrable p Y /\ integrable p Z /\
     integrable p (\x. X x pow 2) /\ integrable p (\x. Y x pow 2) /\
     integrable p (\x. Z x pow 2)
     ==> covariance p (\x. X x + Y x) Z =
         covariance p X Z + covariance p Y Z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. (X:A->real) x * (Z:A->real) x)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_MUL_SQUARE THEN ASM_MESON_TAC[integrable]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. (Y:A->real) x * (Z:A->real) x)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_MUL_SQUARE THEN ASM_MESON_TAC[integrable]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. (X:A->real) x + (Y:A->real) x)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. ((X:A->real) x + (Y:A->real) x) * (Z:A->real) x)` ASSUME_TAC THENL
  [SUBGOAL_THEN `(\x:A. ((X:A->real) x + (Y:A->real) x) * (Z:A->real) x) =
    (\x. X x * Z x + Y x * Z x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
    MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  ASM_SIMP_TAC[COVARIANCE_ALT] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. ((X:A->real) x + (Y:A->real) x) * (Z:A->real) x) =
    expectation p (\x. X x * Z x) + expectation p (\x. Y x * Z x)` SUBST1_TAC THENL
  [SUBGOAL_THEN `(\x:A. ((X:A->real) x + (Y:A->real) x) * (Z:A->real) x) =
    (\x. X x * Z x + Y x * Z x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[EXPECTATION_ADD]]; ALL_TAC] THEN
  ASM_SIMP_TAC[EXPECTATION_ADD] THEN REAL_ARITH_TAC);;

(* Square of sum of integrable functions is integrable *)
let INTEGRABLE_SUM_SQUARE = prove
 (`!p:A prob_space X n.
     (!i. i <= n ==> integrable p (X i)) /\
     (!i. i <= n ==> integrable p (\x. X i x pow 2))
     ==> integrable p (\x. (sum(0..n) (\i. X i x)) pow 2)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [(* Base case: sum(0..0)(Xi) = X 0, so square = X 0 pow 2 *)
   STRIP_TAC THEN
   SUBGOAL_THEN `(\x:A. (sum(0..0) (\i. (X:num->A->real) i x)) pow 2) =
     (\x. X 0 x pow 2)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; SUM_SING_NUMSEG]; ALL_TAC] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
   ALL_TAC] THEN
  STRIP_TAC THEN
  (* (sum(0..SUC n) Xi)^2 = (sum(0..n) Xi + X(SUC n))^2
     = (sum)^2 + 2*sum*X(SUC n) + X(SUC n)^2 *)
  SUBGOAL_THEN `(\x:A. (sum(0..SUC n) (\i. (X:num->A->real) i x)) pow 2) =
    (\x. (sum(0..n) (\i. X i x)) pow 2 +
         (&2 * (sum(0..n) (\i. X i x) * X (SUC n) x) +
          X (SUC n) x pow 2))` SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; SUM_CLAUSES_NUMSEG; LE_0; REAL_POW_2] THEN
   GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* Establish needed integrabilities *)
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. (sum(0..n) (\i. (X:num->A->real) i x)) pow 2)`
    ASSUME_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THEN X_GEN_TAC `i:num` THEN
   DISCH_TAC THEN ASM_MESON_TAC[ARITH_RULE `i <= n ==> i <= SUC n`];
   ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. (X:num->A->real) (SUC n) x pow 2)`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. sum(0..n) (\i. (X:num->A->real) i x))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_SUM THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   ASM_MESON_TAC[ARITH_RULE `i <= n ==> i <= SUC n`]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) ((X:num->A->real) (SUC n))`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `random_variable (p:A prob_space) (\x:A. sum(0..n) (\i. (X:num->A->real) i x))`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[integrable]; ALL_TAC] THEN
  SUBGOAL_THEN `random_variable (p:A prob_space) (\x:A. (X:num->A->real) (SUC n) x)`
    ASSUME_TAC THENL
  [MP_TAC(REWRITE_RULE[integrable] (ASSUME `integrable (p:A prob_space) ((X:num->A->real) (SUC n))`)) THEN
   SIMP_TAC[ETA_AX]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. sum(0..n) (\i. (X:num->A->real) i x) * X (SUC n) x)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_MUL_SQUARE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
   ASM_REWRITE_TAC[]]);;

(* Covariance of sum: Cov(sum Xi, Y) = sum Cov(Xi, Y) *)
let COVARIANCE_SUM_LEFT = prove
 (`!p:A prob_space X Y n.
     (!i. i <= n ==> integrable p (X i)) /\
     (!i. i <= n ==> integrable p (\x. X i x pow 2)) /\
     integrable p Y /\ integrable p (\x. Y x pow 2)
     ==> covariance p (\x. sum(0..n) (\i. X i x)) Y =
         sum(0..n) (\i. covariance p (X i) Y)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [(* Base *)
   STRIP_TAC THEN REWRITE_TAC[SUM_SING_NUMSEG; ETA_AX];
   ALL_TAC] THEN
  STRIP_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
  (* Use COVARIANCE_ADD_LEFT *)
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. sum(0..n) (\i. (X:num->A->real) i x))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_SUM THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   UNDISCH_TAC `!i:num. i <= SUC n ==> integrable (p:A prob_space) ((X:num->A->real) i)` THEN
   DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
   MATCH_MP_TAC(TAUT `a ==> (a ==> b) ==> b`) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. (sum(0..n) (\i. (X:num->A->real) i x)) pow 2)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_SUM_SQUARE THEN REPEAT CONJ_TAC THEN X_GEN_TAC `i:num` THEN
   DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) ((X:num->A->real) (SUC n))` ASSUME_TAC THENL
  [UNDISCH_TAC `!i:num. i <= SUC n ==> integrable (p:A prob_space) ((X:num->A->real) i)` THEN
   DISCH_THEN(MP_TAC o SPEC `SUC n`) THEN REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. (X:num->A->real) (SUC n) x pow 2)` ASSUME_TAC THENL
  [UNDISCH_TAC `!i:num. i <= SUC n ==> integrable (p:A prob_space) (\x:A. (X:num->A->real) i x pow 2)` THEN
   DISCH_THEN(MP_TAC o SPEC `SUC n`) THEN REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `covariance (p:A prob_space) (\x:A. sum(0..n) (\i. (X:num->A->real) i x) + X (SUC n) x) Y =
    covariance p (\x. sum(0..n) (\i. X i x)) Y + covariance p (X (SUC n)) Y` SUBST1_TAC THENL
  [MATCH_MP_TAC COVARIANCE_ADD_LEFT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* Var(X+Y) = Var(X) + Var(Y) + 2*Cov(X,Y) for square-integrable X, Y *)
let VARIANCE_ADD = prove
 (`!p:A prob_space X Y.
     integrable p X /\ integrable p Y /\
     integrable p (\x. X x pow 2) /\ integrable p (\x. Y x pow 2)
     ==> variance p (\x. X x + Y x) =
         variance p X + variance p Y + &2 * covariance p X Y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. (X:A->real) x * (Y:A->real) x)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_MUL_SQUARE THEN ASM_MESON_TAC[integrable]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. (X:A->real) x + (Y:A->real) x)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. ((X:A->real) x + (Y:A->real) x) pow 2)` ASSUME_TAC THENL
  [SUBGOAL_THEN `(\x:A. ((X:A->real) x + (Y:A->real) x) pow 2) =
    (\x. X x pow 2 + (&2 * (X x * Y x) + Y x pow 2))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; REAL_POW_2] THEN GEN_TAC THEN REAL_ARITH_TAC;
    MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]];
   ALL_TAC] THEN
  ASM_SIMP_TAC[VARIANCE_ALT; COVARIANCE_ALT] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. ((X:A->real) x + (Y:A->real) x) pow 2) =
    expectation p (\x. X x pow 2) + &2 * expectation p (\x. X x * Y x) + expectation p (\x. Y x pow 2)` SUBST1_TAC THENL
  [SUBGOAL_THEN `(\x:A. ((X:A->real) x + (Y:A->real) x) pow 2) =
    (\x. X x pow 2 + (&2 * (X x * Y x) + Y x pow 2))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; REAL_POW_2] THEN GEN_TAC THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[EXPECTATION_ADD; INTEGRABLE_ADD; INTEGRABLE_CMUL] THEN
    ASM_SIMP_TAC[EXPECTATION_CMUL] THEN REAL_ARITH_TAC]; ALL_TAC] THEN
  ASM_SIMP_TAC[EXPECTATION_ADD] THEN REAL_ARITH_TAC);;

(* Cov(aX, Y) = a * Cov(X,Y) for integrable X, Y *)
let COVARIANCE_CMUL = prove
 (`!p:A prob_space X Y a.
     integrable p X /\ integrable p Y /\ integrable p (\x. X x * Y x)
     ==> covariance p (\x. a * X x) Y = a * covariance p X Y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. a * (X:A->real) x)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. (a * (X:A->real) x) * (Y:A->real) x)` ASSUME_TAC THENL
  [SUBGOAL_THEN `(\x:A. (a * (X:A->real) x) * (Y:A->real) x) =
    (\x. a * (X x * Y x))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
    MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  ASM_SIMP_TAC[COVARIANCE_ALT] THEN
  SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. (a * (X:A->real) x) * (Y:A->real) x) =
    a * expectation p (\x. X x * Y x)` SUBST1_TAC THENL
  [SUBGOAL_THEN `(\x:A. (a * (X:A->real) x) * (Y:A->real) x) =
    (\x. a * (X x * Y x))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[EXPECTATION_CMUL]]; ALL_TAC] THEN
  ASM_SIMP_TAC[EXPECTATION_CMUL] THEN REAL_ARITH_TAC);;

(* Variance of sum = sum of variances for uncorrelated square-integrable RVs *)
let VARIANCE_SUM_UNCORRELATED = prove
 (`!p:A prob_space X n.
     (!i. i <= n ==> integrable p (X i)) /\
     (!i. i <= n ==> integrable p (\x. X i x pow 2)) /\
     (!i j. i <= n /\ j <= n /\ ~(i = j) ==> covariance p (X i) (X j) = &0)
     ==> variance p (\x. sum(0..n) (\i. X i x)) =
         sum(0..n) (\i. variance p (X i))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [(* Base case *)
   STRIP_TAC THEN REWRITE_TAC[SUM_SING_NUMSEG; ETA_AX];
   ALL_TAC] THEN
  STRIP_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
  (* Var(Sn + X(SUC n)) = Var(Sn) + Var(X(SUC n)) + 2*Cov(Sn, X(SUC n)) *)
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. sum(0..n) (\i. (X:num->A->real) i x))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_SUM THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   UNDISCH_TAC `!i:num. i <= SUC n ==> integrable (p:A prob_space) ((X:num->A->real) i)` THEN
   DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
   MATCH_MP_TAC(TAUT `a ==> (a ==> b) ==> b`) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. (sum(0..n) (\i. (X:num->A->real) i x)) pow 2)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_SUM_SQUARE THEN REPEAT CONJ_TAC THEN X_GEN_TAC `i:num` THEN
   DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) ((X:num->A->real) (SUC n))` ASSUME_TAC THENL
  [UNDISCH_TAC `!i:num. i <= SUC n ==> integrable (p:A prob_space) ((X:num->A->real) i)` THEN
   DISCH_THEN(MP_TAC o SPEC `SUC n`) THEN REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. (X:num->A->real) (SUC n) x pow 2)` ASSUME_TAC THENL
  [UNDISCH_TAC `!i:num. i <= SUC n ==> integrable (p:A prob_space) (\x:A. (X:num->A->real) i x pow 2)` THEN
   DISCH_THEN(MP_TAC o SPEC `SUC n`) THEN REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  (* Apply VARIANCE_ADD *)
  SUBGOAL_THEN `variance (p:A prob_space) (\x:A. sum(0..n) (\i. (X:num->A->real) i x) + X (SUC n) x) =
    variance p (\x. sum(0..n) (\i. X i x)) + variance p (X (SUC n)) +
    &2 * covariance p (\x. sum(0..n) (\i. X i x)) (X (SUC n))` SUBST1_TAC THENL
  [MATCH_MP_TAC VARIANCE_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* By COVARIANCE_SUM_LEFT, Cov(Sn, X(SUC n)) = sum(0..n) Cov(Xi, X(SUC n)) *)
  SUBGOAL_THEN `covariance (p:A prob_space) (\x:A. sum(0..n) (\i. (X:num->A->real) i x)) (X (SUC n)) =
    sum(0..n) (\i. covariance p (X i) (X (SUC n)))` SUBST1_TAC THENL
  [MATCH_MP_TAC COVARIANCE_SUM_LEFT THEN ASM_REWRITE_TAC[] THEN
   REPEAT CONJ_TAC THEN TRY(X_GEN_TAC `i:num` THEN DISCH_TAC) THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  (* Each Cov(Xi, X(SUC n)) = 0 *)
  SUBGOAL_THEN `sum(0..n) (\i:num. covariance (p:A prob_space) ((X:num->A->real) i) (X (SUC n))) = &0`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  (* By IH: Var(Sn) = sum Var(Xi) *)
  SUBGOAL_THEN `variance (p:A prob_space) (\x:A. sum(0..n) (\i. (X:num->A->real) i x)) =
    sum(0..n) (\i. variance p (X i))` SUBST1_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* Weak Law of Large Numbers for integrable functions *)
let WEAK_LAW_OF_LARGE_NUMBERS = prove
 (`!p:A prob_space X n mu sigma2 epsilon.
    (!i. i <= n ==> integrable p (X i)) /\
    (!i. i <= n ==> integrable p (\x. X i x pow 2)) /\
    (!i j. i <= n /\ j <= n /\ ~(i = j) ==> covariance p (X i) (X j) = &0) /\
    (!i. i <= n ==> expectation p (X i) = mu) /\
    (!i. i <= n ==> variance p (X i) = sigma2) /\
    &0 < epsilon
    ==> prob p {x | x IN prob_carrier p /\
          abs(sum(0..n) (\i. X i x) / &(n + 1) - mu) >= epsilon} <=
        sigma2 / (&(n + 1) * epsilon pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Xbar = \x:A. sum(0..n) (\i. (X:num->A->real) i x) / &(n + 1)` THEN
  (* Xbar is integrable *)
  SUBGOAL_THEN `integrable (p:A prob_space) Xbar` ASSUME_TAC THENL
  [EXPAND_TAC "Xbar" THEN
   SUBGOAL_THEN `(\x:A. sum(0..n) (\i. (X:num->A->real) i x) / &(n + 1)) =
     (\x. inv(&(n + 1)) * sum(0..n) (\i. X i x))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; real_div; REAL_MUL_SYM]; ALL_TAC] THEN
   MATCH_MP_TAC INTEGRABLE_CMUL THEN
   MATCH_MP_TAC INTEGRABLE_SUM THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. sum (0..n) (\i. (X:num->A->real) i x) / &(n + 1) = Xbar x`
    (fun th -> REWRITE_TAC[th]) THENL
  [GEN_TAC THEN EXPAND_TAC "Xbar" THEN REWRITE_TAC[]; ALL_TAC] THEN
  (* Xbar^2 is integrable *)
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. Xbar x pow 2)` ASSUME_TAC THENL
  [EXPAND_TAC "Xbar" THEN
   SUBGOAL_THEN `(\x:A. (sum(0..n) (\i. (X:num->A->real) i x) / &(n + 1)) pow 2) =
     (\x. inv(&(n + 1)) pow 2 * (sum(0..n) (\i. X i x)) pow 2)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; real_div; REAL_POW_MUL; REAL_MUL_SYM]; ALL_TAC] THEN
   MATCH_MP_TAC INTEGRABLE_CMUL THEN
   MATCH_MP_TAC INTEGRABLE_SUM_SQUARE THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  (* E[Xbar] = mu *)
  SUBGOAL_THEN `expectation (p:A prob_space) Xbar = mu` ASSUME_TAC THENL
  [EXPAND_TAC "Xbar" THEN
   SUBGOAL_THEN `(\x:A. sum(0..n) (\i. (X:num->A->real) i x) / &(n + 1)) =
     (\x. inv(&(n + 1)) * sum(0..n) (\i. X i x))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; real_div; REAL_MUL_SYM]; ALL_TAC] THEN
   ASM_SIMP_TAC[EXPECTATION_CMUL; INTEGRABLE_SUM] THEN
   ASM_SIMP_TAC[EXPECTATION_SUM] THEN
   ASM_SIMP_TAC[SUM_CONST_NUMSEG; SUB_0] THEN
   REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
   REWRITE_TAC[REAL_MUL_ASSOC] THEN
   SUBGOAL_THEN `inv(&n + &1) * (&n + &1) = &1` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_MUL_LINV THEN REAL_ARITH_TAC; REWRITE_TAC[REAL_MUL_LID]];
   ALL_TAC] THEN
  (* Var(Xbar) = sigma2 / (n+1) *)
  SUBGOAL_THEN `variance (p:A prob_space) Xbar = sigma2 / &(n + 1)` ASSUME_TAC THENL
  [EXPAND_TAC "Xbar" THEN
   SUBGOAL_THEN `(\x:A. sum(0..n) (\i. (X:num->A->real) i x) / &(n + 1)) =
     (\x. inv(&(n + 1)) * sum(0..n) (\i. X i x))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; real_div; REAL_MUL_SYM]; ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. sum(0..n) (\i. (X:num->A->real) i x))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SUM THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. (sum(0..n) (\i. (X:num->A->real) i x)) pow 2)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SUM_SQUARE THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
   ASM_SIMP_TAC[VARIANCE_CMUL] THEN
   ASM_SIMP_TAC[VARIANCE_SUM_UNCORRELATED] THEN
   ASM_SIMP_TAC[SUM_CONST_NUMSEG; SUB_0] THEN
   REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
   SUBGOAL_THEN `~(&n + &1 = &0)` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_POW_2; real_div] THEN
   SUBGOAL_THEN `(inv(&n + &1) * inv(&n + &1)) * ((&n + &1) * sigma2) =
     inv(&n + &1) * (inv(&n + &1) * (&n + &1)) * sigma2` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_MUL_LINV; REAL_MUL_LID] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* (Xbar - mu)^2 is integrable *)
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. (Xbar x - mu) pow 2)` ASSUME_TAC THENL
  [SUBGOAL_THEN `(\x:A. (Xbar x - mu) pow 2) =
    (\x. Xbar x pow 2 + (-- &2 * mu * Xbar x + mu pow 2))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; REAL_POW_2] THEN GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
   [ASM_MESON_TAC[];
    MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_CMUL THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_MESON_TAC[];
     REWRITE_TAC[INTEGRABLE_CONST]]]; ALL_TAC] THEN
  (* Apply Chebyshev *)
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ abs (Xbar x - mu) >= epsilon} =
    {x | x IN prob_carrier p /\ abs (Xbar x - expectation (p:A prob_space) Xbar) >= epsilon}`
    SUBST1_TAC THENL
  [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. (Xbar x - expectation (p:A prob_space) Xbar) pow 2)`
    ASSUME_TAC THENL
  [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `prob p {x:A | x IN prob_carrier p /\ abs (Xbar x - expectation (p:A prob_space) Xbar) >= epsilon} <=
    variance p Xbar / epsilon pow 2` MP_TAC THENL
  [MATCH_MP_TAC CHEBYSHEV_INEQUALITY THEN ASM_REWRITE_TAC[];
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[real_div; REAL_INV_MUL; GSYM REAL_MUL_ASSOC]]);;

(* Phase 14: Jensen's inequality and supporting lemmas *)

(* |E[f]| <= E[|f|] for integrable f *)
let EXPECTATION_ABS_LE = prove
 (`!p:A prob_space f.
     integrable p f
     ==> abs(expectation p f) <= expectation p (\x. abs(f x))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_ABS_BOUNDS] THEN CONJ_TAC THENL
  [SUBGOAL_THEN `--expectation (p:A prob_space) (\x:A. abs((f:A->real) x)) =
     expectation p (\x. --(abs(f x)))` SUBST1_TAC THENL
   [MATCH_MP_TAC(GSYM EXPECTATION_NEG_INTEGRABLE) THEN
    MATCH_MP_TAC INTEGRABLE_ABS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   MATCH_MP_TAC EXPECTATION_MONO THEN
   ASM_SIMP_TAC[INTEGRABLE_NEG; INTEGRABLE_ABS] THEN
   GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
   MATCH_MP_TAC EXPECTATION_MONO THEN
   ASM_SIMP_TAC[INTEGRABLE_ABS] THEN
   GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC]);;

(* Subgradient property for convex functions on all of R:
   for any x0, there exists c such that f(y) >= f(x0) + c*(y - x0) for all y *)
let REAL_CONVEX_ON_SUBGRADIENT = prove
 (`!f:real->real x0. f real_convex_on (:real)
    ==> ?c. !y. f(x0) + c * (y - x0) <= f(y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  (* Three-point secant inequality from convexity *)
  SUBGOAL_THEN
    `!a b:real. a < x0 /\ x0 < b
     ==> ((f:real->real)(x0) - f(a)) * (b - x0) <= (f(b) - f(x0)) * (x0 - a)`
    (LABEL_TAC "3PT") THENL
  [REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_CONVEX_ON_LEFT_SECANT_MUL]) THEN
   DISCH_THEN(MP_TAC o SPECL [`a:real`; `b:real`; `x0:real`]) THEN
   REWRITE_TAC[IN_UNIV; IN_REAL_SEGMENT] THEN
   ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `abs(b - a) = b - a` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `abs(x0 - a) = x0 - a` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(MP_TAC o REWRITE_RULE[REAL_SUB_RDISTRIB; REAL_SUB_LDISTRIB]) THEN
   REWRITE_TAC[REAL_SUB_RDISTRIB; REAL_SUB_LDISTRIB] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  ABBREV_TAC `r = (f:real->real)(x0 + &1) - f(x0)` THEN
  (* All left secant slopes are <= r *)
  SUBGOAL_THEN `!z. z < x0 ==> ((f:real->real)(x0) - f(z)) <= r * (x0 - z)`
    (LABEL_TAC "LEFT_BDD") THENL
  [X_GEN_TAC `z:real` THEN DISCH_TAC THEN
   REMOVE_THEN "3PT" (MP_TAC o SPECL [`z:real`; `x0 + &1`]) THEN
   ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   EXPAND_TAC "r" THEN
   SUBGOAL_THEN `(x0 + &1) - x0 = &1` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_MUL_RID] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Define S = set of left secant slopes at x0 *)
  ABBREV_TAC `S = {s:real | ?z. z < x0 /\ s = ((f:real->real)(x0) - f(z)) / (x0 - z)}` THEN
  SUBGOAL_THEN `~(S:real->bool = {})` (LABEL_TAC "NE") THENL
  [EXPAND_TAC "S" THEN REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; NOT_FORALL_THM; IN_ELIM_THM] THEN
   EXISTS_TAC `((f:real->real)(x0) - f(x0 - &1)) / (x0 - (x0 - &1))` THEN
   EXISTS_TAC `x0 - &1` THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `!s:real. s IN S ==> s <= r`
    (LABEL_TAC "BDD") THENL
  [X_GEN_TAC `s:real` THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
   DISCH_THEN(X_CHOOSE_THEN `z:real` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
   ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_SUB_LT] THEN
   USE_THEN "LEFT_BDD" (MP_TAC o SPEC `z:real`) THEN ASM_REWRITE_TAC[] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Take c = sup S *)
  EXISTS_TAC `sup S` THEN X_GEN_TAC `y:real` THEN
  ASM_CASES_TAC `y:real = x0` THENL
  [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_ADD_RID; REAL_LE_REFL]; ALL_TAC] THEN
  ASM_CASES_TAC `y:real < x0` THENL
  [(* Case y < x0: left secant slope at y is in S, hence <= sup S *)
   SUBGOAL_THEN `&0 < x0 - y` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `((f:real->real)(x0) - f(y)) / (x0 - y) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `y:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   MP_TAC(SPEC `S:real->bool` SUP) THEN ASM_REWRITE_TAC[] THEN
   ANTS_TAC THENL [EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `((f:real->real)(x0) - f(y)) / (x0 - y)`) ASSUME_TAC) THEN
   ASM_REWRITE_TAC[] THEN
   ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Case y > x0 *)
  SUBGOAL_THEN `x0 < y` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < y - x0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* Each s IN S satisfies s * (y - x0) <= f y - f x0 (from three-point) *)
  SUBGOAL_THEN `!s. s IN S ==> s * (y - x0) <= (f:real->real)(y) - f(x0)` (LABEL_TAC "RIGHT") THENL
  [X_GEN_TAC `s:real` THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
   DISCH_THEN(X_CHOOSE_THEN `z:real` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
   SUBGOAL_THEN `&0 < x0 - z` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `((f:real->real)(x0) - f(z)) / (x0 - z) * (y - x0) =
     ((f(x0) - f(z)) * (y - x0)) / (x0 - z)` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_AC]; ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
   SUBGOAL_THEN `((f:real->real)(y) - f(x0)) * (x0 - z) >=
     (f(x0) - f(z)) * (y - x0)` MP_TAC THENL
   [REWRITE_TAC[real_ge] THEN USE_THEN "3PT" (MP_TAC o SPECL [`z:real`; `y:real`]) THEN
    ASM_REWRITE_TAC[];
    REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* sup S * (y - x0) <= f y - f x0 via sup S <= (f y - f x0)/(y - x0) *)
  SUBGOAL_THEN `sup S * (y - x0) <= (f:real->real)(y) - f(x0)` MP_TAC THENL
  [SUBGOAL_THEN `sup S <= ((f:real->real)(y) - f(x0)) / (y - x0)` MP_TAC THENL
   [MATCH_MP_TAC REAL_SUP_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    USE_THEN "RIGHT" (MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC];
   REAL_ARITH_TAC]);;

(* Jensen's inequality for integrable random variables:
   f convex on R, X integrable, f(X) integrable ==> f(E[X]) <= E[f(X)] *)
let JENSEN = prove
 (`!p:A prob_space (X:A->real) (f:real->real).
     integrable p X /\ integrable p (\a. f(X a)) /\ f real_convex_on (:real)
     ==> f(expectation p X) <= expectation p (\a. f(X a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `mu = expectation (p:A prob_space) (X:A->real)` THEN
  MP_TAC(SPECL [`f:real->real`; `mu:real`] REAL_CONVEX_ON_SUBGRADIENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `c:real`) THEN
  (* E[f(mu) + c*(X - mu)] <= E[f(X)] by monotonicity *)
  SUBGOAL_THEN `expectation (p:A prob_space) (\a:A. f(mu:real) + c * ((X:A->real) a - mu)) <=
    expectation p (\a. (f:real->real)(X a))` MP_TAC THENL
  [MATCH_MP_TAC EXPECTATION_MONO THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(\a:A. f(mu:real) + c * ((X:A->real) a - mu)) =
     (\a. (f mu - c * mu) + c * X a)` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC INTEGRABLE_ADD THEN REWRITE_TAC[INTEGRABLE_CONST] THEN
    MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    X_GEN_TAC `a:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(X:A->real) a`) THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* E[f(mu) + c*(X - mu)] = f(mu) + c*(E[X] - mu) = f(mu) *)
  SUBGOAL_THEN `expectation (p:A prob_space) (\a:A. f(mu:real) + c * ((X:A->real) a - mu)) =
    f mu` SUBST1_TAC THENL
  [SUBGOAL_THEN `(\a:A. f(mu:real) + c * ((X:A->real) a - mu)) =
    (\a. (f mu - c * mu) + c * X a)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `(\a:A. (f(mu:real) - c * mu):real)`; `(\a:A. c * (X:A->real) a)`]
     EXPECTATION_ADD) THEN
   BETA_TAC THEN
   ANTS_TAC THENL
   [REWRITE_TAC[INTEGRABLE_CONST] THEN
    MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   REWRITE_TAC[EXPECTATION_CONST] THEN
   DISCH_THEN SUBST1_TAC THEN
   SUBGOAL_THEN `expectation (p:A prob_space) (\a:A. c * (X:A->real) a) =
     c * mu` SUBST1_TAC THENL
   [SUBGOAL_THEN `expectation (p:A prob_space) (\a:A. c * (X:A->real) a) =
     c * expectation p X` SUBST1_TAC THENL
    [MATCH_MP_TAC EXPECTATION_CMUL THEN ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[]];
    REAL_ARITH_TAC];
   REWRITE_TAC[]]);;

(* Phase 15: Generalize BCL1 and SLLN to integrable/random_variable *)

(* BCL1_CONVERGENCE generalized from simple_rv to random_variable *)
let BCL1_CONVERGENCE_RV = prove
 (`!p:A prob_space (Y:num->A->real) c.
     (!n. random_variable p (Y n)) /\
     (!eps. &0 < eps ==>
        real_summable (from 0) (\n. prob p {x | x IN prob_carrier p /\ abs(Y n x - c) >= eps}))
     ==> almost_surely p {x | ((\n. Y n x) ---> c) sequentially}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[almost_surely] THEN
  EXISTS_TAC `UNIONS {limsup_events
    (\n. {x:A | x IN prob_carrier p /\ abs((Y:num->A->real) n x - c) >= inv(&(SUC k))})
    | k IN (:num)}` THEN
  SUBGOAL_THEN
    `!k n. {x:A | x IN prob_carrier p /\ abs((Y:num->A->real) n x - c) >= inv(&(SUC k))}
           IN prob_events p`
    (LABEL_TAC "Hev") THENL
  [REPEAT GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_GE THEN
   MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN
   MATCH_MP_TAC RANDOM_VARIABLE_SUB_CONST THEN
   REWRITE_TAC[ETA_AX] THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC NULL_EVENT_COUNTABLE_UNION THEN
   X_GEN_TAC `k:num` THEN
   REWRITE_TAC[null_event] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LIMSUP_EVENTS_IN_EVENTS THEN
    GEN_TAC THEN USE_THEN "Hev" (MP_TAC o SPECL [`k:num`; `n:num`]) THEN
    REWRITE_TAC[];
    MP_TAC(ISPECL
      [`p:A prob_space`;
       `\n. {x:A | x IN prob_carrier p /\ abs((Y:num->A->real) n x - c) >= inv(&(SUC k))}`]
      FIRST_BOREL_CANTELLI) THEN
    TRY BETA_TAC THEN
    DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
    [GEN_TAC THEN USE_THEN "Hev" (MP_TAC o SPECL [`k:num`; `n:num`]) THEN
     REWRITE_TAC[];
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     MATCH_MP_TAC REAL_LT_INV THEN
     REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC]];
   REWRITE_TAC[SUBSET] THEN
   X_GEN_TAC `x:A` THEN
   REWRITE_TAC[IN_ELIM_THM] THEN
   STRIP_TAC THEN
   REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
   FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[REALLIM_SEQUENTIALLY]) THEN
   TRY BETA_TAC THEN
   REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM;
               NOT_FORALL_THM; NOT_IMP; REAL_NOT_LT] THEN
   DISCH_THEN(X_CHOOSE_THEN `eps:real` STRIP_ASSUME_TAC) THEN
   MP_TAC(fst(EQ_IMP_RULE(SPEC `eps:real` REAL_ARCH_INV))) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `?kk:num. m = SUC kk`
     (X_CHOOSE_THEN `kk:num` SUBST_ALL_TAC) THENL
   [MP_TAC(SPEC `m:num` num_CASES) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   EXISTS_TAC `limsup_events
     (\n. {x:A | x IN prob_carrier p /\ abs((Y:num->A->real) n x - c) >= inv(&(SUC kk))})` THEN
   CONJ_TAC THENL
   [EXISTS_TAC `kk:num` THEN REFL_TAC;
    REWRITE_TAC[LIMSUP_EVENTS_ALT; IN_ELIM_THM] THEN
    TRY BETA_TAC THEN
    REWRITE_TAC[IN_ELIM_THM; GE] THEN
    X_GEN_TAC `N:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
    DISCH_THEN(X_CHOOSE_THEN `nn:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `nn:num` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_ge] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `eps:real` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[]]]]);;

(* Subsequence SLLN for integrable random variables *)
let SLLN_SUBSEQ = prove
 (`!p:A prob_space (X:num->A->real) mu sigma_sq.
    (!n. integrable p (X n)) /\
    (!n. integrable p (\x. X n x pow 2)) /\
    (!n. expectation p (X n) = mu) /\
    (!n. variance p (X n) = sigma_sq) /\
    (!i j. ~(i = j) ==> covariance p (X i) (X j) = &0)
    ==> almost_surely p
          {x | ((\k. inv(&(SUC(k * k))) * sum(0..k * k) (\i. X i x)) ---> mu) sequentially}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC BCL1_CONVERGENCE_RV THEN TRY BETA_TAC THEN
  CONJ_TAC THENL
  [(* Each Y_k = inv(SUC(k*k)) * sum Xi is a random variable *)
   GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`; `k * k:num`] INTEGRABLE_SUM) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC THEN ASM_MESON_TAC[integrable]];
   ALL_TAC] THEN
  (* Summability of deviation probabilities *)
  X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
  EXISTS_TAC `\k:num. sigma_sq / eps pow 2 * inv(&(SUC(k * k)))` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_SUMMABLE_LMUL THEN REWRITE_TAC[SUMMABLE_INV_SUC_SQUARES]; ALL_TAC] THEN
  EXISTS_TAC `0` THEN X_GEN_TAC `k:num` THEN
  REWRITE_TAC[GE; LE_0; IN_FROM] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. sum(0..k * k) (\i. (X:num->A->real) i x))`
    ASSUME_TAC THENL [MATCH_MP_TAC INTEGRABLE_SUM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. (sum(0..k * k) (\i. (X:num->A->real) i x)) pow 2)`
    ASSUME_TAC THENL [MATCH_MP_TAC INTEGRABLE_SUM_SQUARE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
  [(* prob >= 0 *)
   MATCH_MP_TAC PROB_POSITIVE THEN MATCH_MP_TAC RANDOM_VARIABLE_GE THEN
   MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN MATCH_MP_TAC RANDOM_VARIABLE_SUB_CONST THEN
   MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_MESON_TAC[integrable]; ALL_TAC] THEN
  ABBREV_TAC `nn = SUC(k * k)` THEN
  SUBGOAL_THEN `~(&nn = &0)` ASSUME_TAC THENL
  [EXPAND_TAC "nn" THEN REWRITE_TAC[REAL_OF_NUM_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. inv(&nn) * sum(0..k * k) (\i. (X:num->A->real) i x))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `CARD(0..k * k) = nn` ASSUME_TAC THENL
  [REWRITE_TAC[CARD_NUMSEG; SUB_0] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv(&nn) * &nn = &1` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* E[Xbar] = mu *)
  SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. inv(&nn) * sum(0..k * k) (\i. (X:num->A->real) i x)) = mu`
    (LABEL_TAC "EXP") THENL
  [ASM_SIMP_TAC[EXPECTATION_CMUL] THEN
   ASM_SIMP_TAC[EXPECTATION_SUM] THEN
   ASM_SIMP_TAC[SUM_CONST_NUMSEG; SUB_0] THEN
   SUBGOAL_THEN `&(k * k + 1) = &nn` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[REAL_MUL_LID];
   ALL_TAC] THEN
  (* Var(Xbar) = sigma_sq / nn *)
  SUBGOAL_THEN `variance (p:A prob_space) (\x:A. inv(&nn) * sum(0..k * k) (\i. (X:num->A->real) i x)) =
    sigma_sq * inv(&nn)` (LABEL_TAC "VAR") THENL
  [ASM_SIMP_TAC[VARIANCE_CMUL] THEN
   ASM_SIMP_TAC[VARIANCE_SUM_UNCORRELATED] THEN
   ASM_SIMP_TAC[SUM_CONST_NUMSEG; SUB_0] THEN
   SUBGOAL_THEN `&(k * k + 1) = &nn` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_POW_2; REAL_MUL_ASSOC] THEN
   SUBGOAL_THEN `(inv(&nn) * inv(&nn)) * &nn = inv(&nn:real)` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[REAL_MUL_RID];
    REWRITE_TAC[REAL_MUL_SYM]];
   ALL_TAC] THEN
  (* (Xbar - mu)^2 is integrable *)
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. (inv(&nn) * sum(0..k * k) (\i. (X:num->A->real) i x) - mu) pow 2)`
    ASSUME_TAC THENL
  [SUBGOAL_THEN `(\x:A. (inv(&nn) * sum(0..k * k) (\i. (X:num->A->real) i x) - mu) pow 2) =
    (\x. inv(&nn) pow 2 * (sum(0..k * k) (\i. X i x) - &nn * mu) pow 2)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    SUBGOAL_THEN `inv(&nn) * sum (0..k * k) (\i. (X:num->A->real) i x) - mu =
      inv(&nn) * (sum (0..k * k) (\i. X i x) - &nn * mu)` SUBST1_TAC THENL
    [REWRITE_TAC[REAL_SUB_LDISTRIB; REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[REAL_MUL_LID];
     REWRITE_TAC[REAL_POW_MUL]]; ALL_TAC] THEN
   MATCH_MP_TAC INTEGRABLE_CMUL THEN
   SUBGOAL_THEN `(\x:A. (sum(0..k * k) (\i. (X:num->A->real) i x) - &nn * mu) pow 2) =
     (\x. (sum(0..k * k) (\i. X i x)) pow 2 +
          (--(&2 * &nn * mu) * sum(0..k * k) (\i. X i x) + (&nn * mu) pow 2))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[INTEGRABLE_CONST]];
   ALL_TAC] THEN
  (* Apply Chebyshev *)
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ abs(inv(&nn) * sum(0..k * k) (\i. (X:num->A->real) i x) - mu) >= eps} =
    {x | x IN prob_carrier p /\ abs(inv(&nn) * sum(0..k * k) (\i. X i x) - expectation p (\x. inv(&nn) * sum(0..k * k) (\i. X i x))) >= eps}`
    SUBST1_TAC THENL
  [USE_THEN "EXP" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `\x:A. inv(&nn) * sum(0..k * k) (\i. (X:num->A->real) i x)`; `eps:real`]
    CHEBYSHEV_INEQUALITY) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `variance (p:A prob_space) (\x:A. inv(&nn) * sum(0..k * k) (\i. (X:num->A->real) i x)) / eps pow 2` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "VAR" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; GSYM REAL_MUL_ASSOC] THEN
  REAL_ARITH_TAC);;

(* SIMPLE_CHEBYSHEV_CONVERGENCE generalized to integrable hypotheses *)
let CHEBYSHEV_CONVERGENCE = prove
 (`!p:A prob_space X mu.
      (!n. integrable p (X n)) /\
      (!n. integrable p (\x. (X n x - expectation p (X n)) pow 2)) /\
      (!n. expectation p (X n) = mu) /\
      ((\n. variance p (X n)) ---> &0) sequentially
      ==> converges_in_prob_const p X mu`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[converges_in_prob_const; converges_in_prob] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
  UNDISCH_TAC `((\n. variance (p:A prob_space) ((X:num->A->real) n))
    ---> &0) sequentially` THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `eps * (e:real) pow 2`) THEN
  ASM_SIMP_TAC[REAL_LT_MUL; REAL_POW_LT] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_TAC THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
    abs ((X:num->A->real) n x - mu) >= e} =
    {x | x IN prob_carrier p /\
    abs(X n x - expectation p (X n)) >= e}` SUBST1_TAC THENL
  [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `random_variable (p:A prob_space) ((X:num->A->real) n)`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[integrable]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= prob (p:A prob_space)
    {x:A | x IN prob_carrier p /\
     abs ((X:num->A->real) n x - expectation p (X n)) >= e}`
    ASSUME_TAC THENL
  [MATCH_MP_TAC PROB_POSITIVE THEN
   MATCH_MP_TAC RANDOM_VARIABLE_GE THEN
   MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN
   MATCH_MP_TAC RANDOM_VARIABLE_SUB_CONST THEN
   ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a < b ==> abs a < b`) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `variance (p:A prob_space) ((X:num->A->real) n) / e pow 2` THEN
  CONJ_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) n`; `e:real`]
     CHEBYSHEV_INEQUALITY) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= variance (p:A prob_space) ((X:num->A->real) n)` ASSUME_TAC THENL
  [REWRITE_TAC[variance] THEN MATCH_MP_TAC EXPECTATION_POS THEN
   ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_LE_POW_2];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 < e pow 2` ASSUME_TAC THENL
  [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  ASM_REAL_ARITH_TAC);;

(* Asymptotic WLLN: convergence in probability for integrable RVs *)
let WLLN_CONVERGENCE = prove
 (`!p:A prob_space (X:num->A->real) mu sigma_sq.
    (!n. integrable p (X n)) /\
    (!n. integrable p (\x. X n x pow 2)) /\
    (!n. expectation p (X n) = mu) /\
    (!n. variance p (X n) <= sigma_sq) /\
    (!i j. ~(i = j) ==> covariance p (X i) (X j) = &0)
    ==> converges_in_prob_const p
          (\n x. inv(&(SUC n)) * sum(0..n) (\i. X i x)) mu`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(BETA_RULE(ISPECL
    [`p:A prob_space`;
     `\n:num. \x:A. inv(&(SUC n)) * sum(0..n) (\i. (X:num->A->real) i x)`;
     `mu:real`] CHEBYSHEV_CONVERGENCE)) THEN
  REPEAT CONJ_TAC THENL
  [(* integrable p (\x. inv(SUC n) * sum ...) *)
   GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
   MATCH_MP_TAC INTEGRABLE_SUM THEN ASM_REWRITE_TAC[];
   (* integrable p (\x. (Xbar - E[Xbar])^2) *)
   GEN_TAC THEN
   ABBREV_TAC `nn = SUC n` THEN
   SUBGOAL_THEN `~(&nn = &0)` ASSUME_TAC THENL
   [EXPAND_TAC "nn" THEN REWRITE_TAC[REAL_OF_NUM_EQ] THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. sum(0..n) (\i. (X:num->A->real) i x))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SUM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. inv(&nn) * sum(0..n) (\i. (X:num->A->real) i x))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. (sum(0..n) (\i. (X:num->A->real) i x)) pow 2)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SUM_SQUARE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. inv(&nn) * sum(0..n) (\i. (X:num->A->real) i x)) =
     inv(&nn) * expectation p (\x. sum(0..n) (\i. X i x))` SUBST1_TAC THENL
   [MATCH_MP_TAC EXPECTATION_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `(\x:A. (inv(&nn) * sum(0..n) (\i. (X:num->A->real) i x) -
       inv(&nn) * expectation p (\x. sum(0..n) (\i. X i x))) pow 2) =
     (\x. inv(&nn) pow 2 * (sum(0..n) (\i. X i x) - expectation p (\x. sum(0..n) (\i. X i x))) pow 2)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM REAL_SUB_LDISTRIB; REAL_POW_MUL]; ALL_TAC] THEN
   MATCH_MP_TAC INTEGRABLE_CMUL THEN
   SUBGOAL_THEN `(\x:A. (sum(0..n) (\i. (X:num->A->real) i x) -
       expectation p (\x. sum(0..n) (\i. X i x))) pow 2) =
     (\x. (sum(0..n) (\i. X i x)) pow 2 +
         (--(&2 * expectation p (\x. sum(0..n) (\i. X i x))) * sum(0..n) (\i. X i x) +
          (expectation p (\x. sum(0..n) (\i. X i x))) pow 2))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[INTEGRABLE_CONST]];
   (* E[Xbar] = mu *)
   GEN_TAC THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. sum(0..n) (\i. (X:num->A->real) i x))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SUM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_SIMP_TAC[EXPECTATION_CMUL] THEN
   ASM_SIMP_TAC[EXPECTATION_SUM] THEN
   ASM_SIMP_TAC[SUM_CONST_NUMSEG; SUB_0] THEN
   REWRITE_TAC[ARITH_RULE `n + 1 = SUC n`] THEN
   SUBGOAL_THEN `~(&(SUC n) = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_MUL_ASSOC] THEN
   ASM_SIMP_TAC[REAL_MUL_LINV; REAL_MUL_LID];
   ALL_TAC] THEN
  (* Var(Xbar_n) -> 0 *)
  SUBGOAL_THEN
    `!n. variance (p:A prob_space) (\x:A. inv(&(SUC n)) * sum(0..n) (\i. (X:num->A->real) i x)) <=
         sigma_sq * inv(&(SUC n))`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   ABBREV_TAC `nn = SUC n` THEN
   SUBGOAL_THEN `~(&nn = &0)` ASSUME_TAC THENL
   [EXPAND_TAC "nn" THEN REWRITE_TAC[REAL_OF_NUM_EQ] THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. sum(0..n) (\i. (X:num->A->real) i x))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SUM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. (sum(0..n) (\i. (X:num->A->real) i x)) pow 2)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SUM_SQUARE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_SIMP_TAC[VARIANCE_CMUL] THEN
   ASM_SIMP_TAC[VARIANCE_SUM_UNCORRELATED] THEN
   SUBGOAL_THEN `sum(0..n) (\i. variance (p:A prob_space) ((X:num->A->real) i)) <= &nn * sigma_sq`
     ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..n) (\i:num. sigma_sq:real)` THEN CONJ_TAC THENL
    [MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0] THEN
     SUBGOAL_THEN `&(n + 1) = &nn` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
   SUBGOAL_THEN `inv(&nn) * &nn = &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `inv(&nn) pow 2 * (&nn * sigma_sq)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_POW_2; REAL_MUL_ASSOC] THEN
    SUBGOAL_THEN `((inv(&nn) * inv(&nn)) * &nn) = inv(&nn)` SUBST1_TAC THENL
    [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[REAL_MUL_RID];
     REWRITE_TAC[REAL_MUL_SYM; REAL_LE_REFL]]];
   ALL_TAC] THEN
  SUBGOAL_THEN `((\n. sigma_sq * inv(&(SUC n))) ---> &0) sequentially` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
   MATCH_MP_TAC REALLIM_NULL_LMUL THEN
   REWRITE_TAC[REALLIM_1_OVER_N_OFFSET]; ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n:num. sigma_sq * inv(&(SUC n))` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[variance] THEN MATCH_MP_TAC EXPECTATION_POS THEN
  CONJ_TAC THENL
  [SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. sum(0..n) (\i. (X:num->A->real) i x))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SUM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. inv(&(SUC n)) * sum(0..n) (\i. (X:num->A->real) i x))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. (sum(0..n) (\i. (X:num->A->real) i x)) pow 2)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SUM_SQUARE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. inv(&(SUC n)) * sum(0..n) (\i. (X:num->A->real) i x)) =
     inv(&(SUC n)) * expectation p (\x. sum(0..n) (\i. X i x))` SUBST1_TAC THENL
   [MATCH_MP_TAC EXPECTATION_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `(\x:A. (inv(&(SUC n)) * sum(0..n) (\i. (X:num->A->real) i x) -
     inv(&(SUC n)) * expectation p (\x. sum(0..n) (\i. X i x))) pow 2) =
     (\x. inv(&(SUC n)) pow 2 * (sum(0..n) (\i. X i x) - expectation p (\x. sum(0..n) (\i. X i x))) pow 2)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM REAL_SUB_LDISTRIB; REAL_POW_MUL]; ALL_TAC] THEN
   MATCH_MP_TAC INTEGRABLE_CMUL THEN
   SUBGOAL_THEN `(\x:A. (sum(0..n) (\i. (X:num->A->real) i x) -
     expectation p (\x. sum(0..n) (\i. X i x))) pow 2) =
     (\x. (sum(0..n) (\i. X i x)) pow 2 +
       (--(&2 * expectation p (\x. sum(0..n) (\i. X i x))) * sum(0..n) (\i. X i x) +
        (expectation p (\x. sum(0..n) (\i. X i x))) pow 2))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[INTEGRABLE_CONST]];
   GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_LE_POW_2]]);;

(* Strong Law of Large Numbers for integrable, bounded RVs *)
let STRONG_LAW_OF_LARGE_NUMBERS = prove
 (`!p:A prob_space (X:num->A->real) mu sigma_sq.
    (!n. integrable p (X n)) /\
    (!n. integrable p (\x. X n x pow 2)) /\
    (!n. expectation p (X n) = mu) /\
    (!n. variance p (X n) = sigma_sq) /\
    (!i j. ~(i = j) ==> covariance p (X i) (X j) = &0) /\
    (?M. !n x. x IN prob_carrier p ==> abs(X n x) <= M)
    ==> almost_surely p
          {x | ((\n. inv(&(SUC n)) * sum(0..n) (\i. X i x)) ---> mu) sequentially}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC
    `{x:A | ((\k. inv(&(SUC(k * k))) * sum(0..k * k) (\i. X i x)) ---> mu) sequentially}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SLLN_SUBSEQ THEN
   EXISTS_TAC `sigma_sq:real` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `abs((X:num->A->real) 0 x)` THEN
   CONJ_TAC THENL [REAL_ARITH_TAC; ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `!i:num. abs((X:num->A->real) i x) <= M` ASSUME_TAC THENL
  [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_SUBSEQUENCE_SQUARES THEN
  EXISTS_TAC `\k. &2 * M * &(2 * k + 1) * inv(&(SUC(k * k)))` THEN
  TRY BETA_TAC THEN
  CONJ_TAC THENL
  [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
  [REPEAT GEN_TAC THEN STRIP_TAC THEN
   MATCH_MP_TAC SAMPLE_MEAN_INTERPOLATION THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MATCH_MP_TAC GAP_LIMIT THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Phase 17: RV measurability for cos/sin and CLT infrastructure             *)
(* ========================================================================= *)

(* RANDOM_VARIABLE_STRICT_LT: strict inequality version of measurability *)
let RANDOM_VARIABLE_STRICT_LT = prove
 (`!p:A prob_space X a.
     random_variable p X
     ==> {x | x IN prob_carrier p /\ X x < a} IN prob_events p`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ X x < a} =
    prob_carrier p DIFF {x | x IN prob_carrier p /\ X x >= a}` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN
   GEN_TAC THEN ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   MATCH_MP_TAC PROB_COMPL_IN_EVENTS THEN
   MATCH_MP_TAC RANDOM_VARIABLE_GE THEN ASM_REWRITE_TAC[]]);;

(* RANDOM_VARIABLE_POW: power of a random variable is a random variable *)
let RANDOM_VARIABLE_POW = prove
 (`!p:A prob_space X n. random_variable p X
     ==> random_variable p (\x. X x pow n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [DISCH_TAC THEN REWRITE_TAC[real_pow] THEN
   REWRITE_TAC[RANDOM_VARIABLE_CONST];
   DISCH_TAC THEN REWRITE_TAC[real_pow] THEN
   MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN
   ASM_SIMP_TAC[]]);;

(* RANDOM_VARIABLE_SUM: finite sum of random variables *)
let RANDOM_VARIABLE_SUM = prove
 (`!p:A prob_space X n. (!i. i <= n ==> random_variable p (X i))
     ==> random_variable p (\x. sum(0..n) (\i. X i x))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [DISCH_TAC THEN REWRITE_TAC[SUM_SING_NUMSEG] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
   REWRITE_TAC[LE_REFL; ETA_AX];
   DISCH_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
   MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN
   CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[ETA_AX] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]]);;

(* RANDOM_VARIABLE_POINTWISE_LIMIT: pointwise limit of random variables *)
let RANDOM_VARIABLE_POINTWISE_LIMIT = prove
 (`!p:A prob_space Y Y_seq.
     (!n. random_variable p (Y_seq n)) /\
     (!x. x IN prob_carrier p ==> ((\n. Y_seq n x) ---> Y x) sequentially)
     ==> random_variable p Y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[random_variable] THEN
  X_GEN_TAC `a:real` THEN
  (* Key set-theoretic characterization using IMAGE:
     {Y <= a} = INTERS_m UNIONS_N INTERS_{n>=N} {Y_n < a + inv(m+1)} *)
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ Y x <= a} =
     INTERS (IMAGE (\m. UNIONS (IMAGE (\N.
       INTERS (IMAGE (\n. {x | x IN prob_carrier p /\
         Y_seq n x < a + inv(&(SUC m))}) {n | n >= N})) (:num))) (:num))`
    SUBST1_TAC THENL
  [(* Set equality proof *)
   REWRITE_TAC[EXTENSION; INTERS_IMAGE; UNIONS_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
   X_GEN_TAC `x:A` THEN EQ_TAC THENL
   [(* Forward: Y(x) <= a ==> membership in all intersections *)
    STRIP_TAC THEN X_GEN_TAC `m:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
    DISCH_THEN(MP_TAC o SPEC `inv(&(SUC m))`) THEN
    REWRITE_TAC[REAL_LT_INV_EQ; REAL_OF_NUM_LT; LT_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` ASSUME_TAC) THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `nn:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs(Y_seq (nn:num) (x:A) - Y x) < inv(&(SUC m))` MP_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN
     UNDISCH_TAC `nn >= N:num` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    (* Backward: membership implies Y(x) <= a *)
    DISCH_TAC THEN
    (* Extract carrier membership *)
    SUBGOAL_THEN `(x:A) IN prob_carrier p` ASSUME_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
     DISCH_THEN(X_CHOOSE_THEN `N:num` ASSUME_TAC) THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
     REWRITE_TAC[GE; LE_REFL] THEN STRIP_TAC;
     ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    (* Proof by contradiction *)
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    ABBREV_TAC `eps = (Y (x:A) - a) / &2` THEN
    SUBGOAL_THEN `&0 < eps` ASSUME_TAC THENL
    [EXPAND_TAC "eps" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `inv(eps:real)` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `mm:num`) THEN
    (* Get convergence Y_seq n x --> Y x *)
    SUBGOAL_THEN `((\n. Y_seq n (x:A)) ---> Y x) sequentially` MP_TAC THENL
    [FIRST_X_ASSUM(MATCH_MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
    DISCH_THEN(MP_TAC o SPEC `eps:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N2:num` ASSUME_TAC) THEN
    (* Get hypothesis at mm *)
    FIRST_X_ASSUM(fun th ->
      MP_TAC(SPEC `mm:num` th) THEN
      DISCH_THEN(X_CHOOSE_THEN `N1:num` ASSUME_TAC)) THEN
    (* Use n = N1 + N2 for both bounds *)
    FIRST_X_ASSUM(MP_TAC o SPEC `N1 + N2:num`) THEN
    REWRITE_TAC[GE; LE_ADD] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `N1 + N2:num`) THEN
    ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
    SUBGOAL_THEN `inv(&(SUC mm)) <= eps` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(inv(eps:real))` THEN
     CONJ_TAC THENL [
       MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN
       MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&mm` THEN
       ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
       REWRITE_TAC[REAL_INV_INV; REAL_LE_REFL]];
     ASM_REAL_ARITH_TAC]];
   ALL_TAC] THEN
  (* Measurability: outer countable intersection *)
  MATCH_MP_TAC PROB_COUNTABLE_INTERS_IN_EVENTS THEN
  REPEAT CONJ_TAC THENL
  [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN
   X_GEN_TAC `m:num` THEN BETA_TAC THEN
   (* Middle: countable union *)
   MATCH_MP_TAC PROB_COUNTABLE_UNION_IN_EVENTS THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN
    X_GEN_TAC `N:num` THEN BETA_TAC THEN
    (* Inner: countable intersection *)
    MATCH_MP_TAC PROB_COUNTABLE_INTERS_IN_EVENTS THEN
    REPEAT CONJ_TAC THENL
    [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
     X_GEN_TAC `n:num` THEN DISCH_TAC THEN BETA_TAC THEN
     MATCH_MP_TAC RANDOM_VARIABLE_STRICT_LT THEN
     REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC COUNTABLE_IMAGE THEN
     MATCH_MP_TAC COUNTABLE_SUBSET THEN EXISTS_TAC `(:num)` THEN
     REWRITE_TAC[NUM_COUNTABLE; SUBSET_UNIV];
     REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
     REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
     EXISTS_TAC `N:num` THEN REWRITE_TAC[IN_ELIM_THM; GE; LE_REFL]];
    MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[NUM_COUNTABLE]];
   MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[NUM_COUNTABLE];
   REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
   REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_UNIV] THEN
   EXISTS_TAC `0` THEN REWRITE_TAC[]]);;

(* COS_TAYLOR_CONVERGES: real Taylor series for cosine converges *)
let COS_TAYLOR_CONVERGES = prove
 (`!x:real. ((\n. sum(0..n)
    (\k. (-- &1) pow k * x pow (2 * k) / &(FACT(2 * k)))) ---> cos x)
    sequentially`,
  X_GEN_TAC `x:real` THEN
  MP_TAC(SPEC `Cx x` CCOS_CONVERGES) THEN
  REWRITE_TAC[sums; FROM_0; INTER_UNIV; GSYM CX_COS] THEN
  SUBGOAL_THEN `!n. vsum(0..n) (\n. --Cx(&1) pow n * Cx x pow (2 * n) /
    Cx(&(FACT(2 * n)))) =
    Cx(sum(0..n) (\k. (-- &1) pow k * x pow (2 * k) / &(FACT(2 * k))))`
    (fun th -> REWRITE_TAC[th]) THENL
  [GEN_TAC THEN
   REWRITE_TAC[GSYM VSUM_CX] THEN
   MATCH_MP_TAC VSUM_EQ THEN
   REWRITE_TAC[IN_NUMSEG] THEN
   REPEAT STRIP_TAC THEN BETA_TAC THEN
   REWRITE_TAC[GSYM CX_NEG; GSYM CX_POW; GSYM CX_MUL; GSYM CX_DIV];
   REWRITE_TAC[REALLIM_COMPLEX; o_DEF]]);;

(* SIN_TAYLOR_CONVERGES: real Taylor series for sine converges *)
let SIN_TAYLOR_CONVERGES = prove
 (`!x:real. ((\n. sum(0..n)
    (\k. (-- &1) pow k * x pow (2 * k + 1) / &(FACT(2 * k + 1)))) ---> sin x)
    sequentially`,
  X_GEN_TAC `x:real` THEN
  MP_TAC(SPEC `Cx x` CSIN_CONVERGES) THEN
  REWRITE_TAC[sums; FROM_0; INTER_UNIV; GSYM CX_SIN] THEN
  SUBGOAL_THEN `!n. vsum(0..n) (\n. --Cx(&1) pow n * Cx x pow (2 * n + 1) /
    Cx(&(FACT(2 * n + 1)))) =
    Cx(sum(0..n) (\k. (-- &1) pow k * x pow (2 * k + 1) / &(FACT(2 * k + 1))))`
    (fun th -> REWRITE_TAC[th]) THENL
  [GEN_TAC THEN
   REWRITE_TAC[GSYM VSUM_CX] THEN
   MATCH_MP_TAC VSUM_EQ THEN
   REWRITE_TAC[IN_NUMSEG] THEN
   REPEAT STRIP_TAC THEN BETA_TAC THEN
   REWRITE_TAC[GSYM CX_NEG; GSYM CX_POW; GSYM CX_MUL; GSYM CX_DIV];
   REWRITE_TAC[REALLIM_COMPLEX; o_DEF]]);;

(* RANDOM_VARIABLE_COS: composition with cosine preserves measurability *)
(* Proof: Taylor partial sums are polynomials in X (hence RVs),
   converge pointwise to cos(X), so by RANDOM_VARIABLE_POINTWISE_LIMIT *)
let RANDOM_VARIABLE_COS = prove
 (`!p:A prob_space X. random_variable p X
     ==> random_variable p (\x. cos(X x))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RANDOM_VARIABLE_POINTWISE_LIMIT THEN
  EXISTS_TAC `\n (x:A). sum(0..n)
    (\k. (-- &1) pow k * (X x) pow (2 * k) / &(FACT(2 * k)))` THEN
  BETA_TAC THEN CONJ_TAC THENL
  [GEN_TAC THEN
   SUBGOAL_THEN
     `(\x:A. sum(0..n) (\k. (-- &1) pow k * (X:A->real) x pow (2 * k) /
       &(FACT(2 * k)))) =
      (\x:A. sum(0..n) (\k. ((-- &1) pow k / &(FACT(2 * k))) *
       X x pow (2 * k)))`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `a:A` THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_NUMSEG] THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[real_div; REAL_MUL_AC];
    MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN
    GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN
    MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
    ASM_REWRITE_TAC[]];
   REPEAT STRIP_TAC THEN REWRITE_TAC[COS_TAYLOR_CONVERGES]]);;

(* RANDOM_VARIABLE_SIN: composition with sine preserves measurability *)
let RANDOM_VARIABLE_SIN = prove
 (`!p:A prob_space X. random_variable p X
     ==> random_variable p (\x. sin(X x))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RANDOM_VARIABLE_POINTWISE_LIMIT THEN
  EXISTS_TAC `\n (x:A). sum(0..n)
    (\k. (-- &1) pow k * (X x) pow (2 * k + 1) / &(FACT(2 * k + 1)))` THEN
  BETA_TAC THEN CONJ_TAC THENL
  [GEN_TAC THEN
   SUBGOAL_THEN
     `(\x:A. sum(0..n) (\k. (-- &1) pow k * (X:A->real) x pow (2 * k + 1) /
       &(FACT(2 * k + 1)))) =
      (\x:A. sum(0..n) (\k. ((-- &1) pow k / &(FACT(2 * k + 1))) *
       X x pow (2 * k + 1)))`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `a:A` THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_NUMSEG] THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[real_div; REAL_MUL_AC];
    MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN
    GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN
    MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
    ASM_REWRITE_TAC[]];
   REPEAT STRIP_TAC THEN REWRITE_TAC[SIN_TAYLOR_CONVERGES]]);;

(* Integrability of cos/sin compositions (bounded RVs are integrable) *)
let INTEGRABLE_COS_CMUL = prove
 (`!p:A prob_space X t. random_variable p X
     ==> integrable p (\x. cos(t * X x))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
  EXISTS_TAC `&1` THEN CONJ_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_COS THEN
   MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[];
   REPEAT STRIP_TAC THEN REWRITE_TAC[COS_BOUND]]);;

let INTEGRABLE_SIN_CMUL = prove
 (`!p:A prob_space X t. random_variable p X
     ==> integrable p (\x. sin(t * X x))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
  EXISTS_TAC `&1` THEN CONJ_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_SIN THEN
   MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[];
   REPEAT STRIP_TAC THEN REWRITE_TAC[SIN_BOUND]]);;

(* Bounds on generalized characteristic function components *)
let GEN_CHAR_FN_RE_BOUND = prove
 (`!p:A prob_space X t. random_variable p X
     ==> abs(gen_char_fn_re p X t) <= &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gen_char_fn_re] THEN
  MP_TAC(SPECL [`p:A prob_space`; `(\x:A. cos(t * (X:A->real) x))`; `&1`]
    EXPECTATION_BOUND) THEN
  BETA_TAC THEN ANTS_TAC THENL
  [CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_COS THEN
    MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[COS_BOUND]];
   SIMP_TAC[]]);;

let GEN_CHAR_FN_IM_BOUND = prove
 (`!p:A prob_space X t. random_variable p X
     ==> abs(gen_char_fn_im p X t) <= &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gen_char_fn_im] THEN
  MP_TAC(SPECL [`p:A prob_space`; `(\x:A. sin(t * (X:A->real) x))`; `&1`]
    EXPECTATION_BOUND) THEN
  BETA_TAC THEN ANTS_TAC THENL
  [CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_SIN THEN
    MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[SIN_BOUND]];
   SIMP_TAC[]]);;

(* Characteristic function values at t=0 *)
let GEN_CHAR_FN_RE_ZERO = prove
 (`!p:A prob_space X. random_variable p X
     ==> gen_char_fn_re p X (&0) = &1`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[gen_char_fn_re; REAL_MUL_LZERO; COS_0; EXPECTATION_CONST]);;

(* Auxiliary: n <= 2^n for all n *)
let LE_2_EXP = prove
 (`!n. n <= 2 EXP n`,
  INDUCT_TAC THENL [
    REWRITE_TAC[EXP; LE_0];
    REWRITE_TAC[EXP] THEN
    SUBGOAL_THEN `1 <= 2 EXP n` ASSUME_TAC THENL [
      REWRITE_TAC[ONE; LE_SUC_LT; LT_NZ; EXP_EQ_0] THEN ARITH_TAC;
      ASM_ARITH_TAC]]);;

(* Helper: monotone sequence implies gn m <= gn n when m <= n *)
let MONO_SEQ_LE = prove
 (`!(gn:num->A->real) (s:A->bool).
     (!n x. x IN s ==> gn n x <= gn (SUC n) x)
     ==> !m n x. m <= n /\ x IN s ==> gn m x <= gn n x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN INDUCT_TAC THENL [
    SIMP_TAC[LE] THEN MESON_TAC[REAL_LE_REFL];
    GEN_TAC THEN REWRITE_TAC[LE] THEN STRIP_TAC THENL [
      ASM_REWRITE_TAC[REAL_LE_REFL];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(gn:num->A->real) n x` THEN
      ASM_SIMP_TAC[]]]);;

(* Monotone Convergence Theorem for bounded nonneg random variables:
   If gn are random variables, nonneg, monotone, converging pointwise to f,
   and f is bounded by B, then nn_expectation(gn n) -> nn_expectation(f) *)
let MCT_NN_EXPECTATION_RV = prove
 (`!p:A prob_space gn f B.
     (!n. random_variable p (gn n)) /\
     (!n x. x IN prob_carrier p ==> &0 <= gn n x) /\
     (!n x. x IN prob_carrier p ==> gn n x <= gn (SUC n) x) /\
     (!x. x IN prob_carrier p ==> ((\n. gn n x) ---> f x) sequentially) /\
     (!x. x IN prob_carrier p ==> &0 <= f x) /\
     (!x. x IN prob_carrier p ==> f x <= B)
     ==> ((\n. nn_expectation p (gn n)) ---> nn_expectation p f) sequentially`,
  REPEAT STRIP_TAC THEN
  (* Step 0: gn n <= f for all n (from monotone limit bound) *)
  SUBGOAL_THEN `!n (x:A). x IN prob_carrier p ==> (gn:num->A->real) n x <= f x`
    ASSUME_TAC THENL [
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LBOUND) THEN
    EXISTS_TAC `\n. (gn:num->A->real) n x` THEN
    ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `n:num` THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`gn:num->A->real`; `prob_carrier (p:A prob_space)`] MONO_SEQ_LE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* Step 1: Define sn and tn *)
  ABBREV_TAC `sn = \n. nonneg_simple_fn_approx p ((gn:num->A->real) n) n` THEN
  MP_TAC(ISPECL [`(sn:num->A->real) 0`;
                  `\(prev:A->real) (n:num) (x:A). max (prev x) ((sn:num->A->real) (SUC n) x)`]
    num_RECURSION) THEN
  DISCH_THEN(X_CHOOSE_THEN `tn:num->A->real` STRIP_ASSUME_TAC) THEN
  (* Step 1b: pointwise recursion for tn *)
  SUBGOAL_THEN `!n (x:A). (tn:num->A->real) (SUC n) x =
                max (tn n x) ((sn:num->A->real) (SUC n) x)` ASSUME_TAC THENL [
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Step 2: sn is simple_rv *)
  SUBGOAL_THEN `!n. simple_rv p ((sn:num->A->real) n)` ASSUME_TAC THENL [
    GEN_TAC THEN EXPAND_TAC "sn" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_SIMPLE_RV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* Step 3: tn is simple_rv *)
  SUBGOAL_THEN `!n. simple_rv p ((tn:num->A->real) n)` ASSUME_TAC THENL [
    INDUCT_TAC THENL [
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SIMPLE_RV_MAX THEN
      CONJ_TAC THENL [
        SUBGOAL_THEN `(\x:A. (tn:num->A->real) n x) = tn n`
          SUBST1_TAC THENL [
          REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN BETA_TAC THEN REFL_TAC;
          ASM_REWRITE_TAC[]];
        SUBGOAL_THEN `(\x:A. (sn:num->A->real) (SUC n) x) = sn (SUC n)`
          SUBST1_TAC THENL [
          REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN BETA_TAC THEN REFL_TAC;
          ASM_REWRITE_TAC[]]]];
    ALL_TAC] THEN
  (* Step 4: sn nonneg *)
  SUBGOAL_THEN `!(n:num) (x:A). x IN prob_carrier p
                ==> &0 <= (sn:num->A->real) n x` ASSUME_TAC THENL [
    REPEAT STRIP_TAC THEN EXPAND_TAC "sn" THEN REWRITE_TAC[] THEN
    REWRITE_TAC[NONNEG_SIMPLE_FN_APPROX_NONNEG];
    ALL_TAC] THEN
  (* Step 5: sn <= gn *)
  SUBGOAL_THEN `!(n:num) (x:A). x IN prob_carrier p
                ==> (sn:num->A->real) n x <= gn n x` ASSUME_TAC THENL [
    REPEAT STRIP_TAC THEN EXPAND_TAC "sn" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_LE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* Step 6: tn nonneg *)
  SUBGOAL_THEN `!(n:num) (x:A). x IN prob_carrier p
                ==> &0 <= (tn:num->A->real) n x` ASSUME_TAC THENL [
    INDUCT_TAC THENL [
      ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REAL_LE_MAX] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* Step 7: tn monotone *)
  SUBGOAL_THEN `!(n:num) (x:A). x IN prob_carrier p
                ==> (tn:num->A->real) n x <= tn (SUC n) x` ASSUME_TAC THENL [
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REAL_LE_MAX] THEN
    DISJ1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* Step 8: tn <= gn *)
  SUBGOAL_THEN `!(n:num) (x:A). x IN prob_carrier p
                ==> (tn:num->A->real) n x <= (gn:num->A->real) n x`
    ASSUME_TAC THENL [
    INDUCT_TAC THENL [
      ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REAL_MAX_LE] THEN
      CONJ_TAC THENL [
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `(gn:num->A->real) n x` THEN ASM_SIMP_TAC[];
        ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  (* Step 9: sn n <= tn n *)
  SUBGOAL_THEN `!(n:num) (x:A). (sn:num->A->real) n x
                <= (tn:num->A->real) n x` ASSUME_TAC THENL [
    INDUCT_TAC THENL [
      GEN_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
      GEN_TAC THEN ASM_REWRITE_TAC[REAL_LE_MAX] THEN
      DISJ2_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* Step 10: tn <= f *)
  SUBGOAL_THEN `!(n:num) (x:A). x IN prob_carrier p
                ==> (tn:num->A->real) n x <= (f:A->real) x` ASSUME_TAC THENL [
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(gn:num->A->real) n x` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* Step 11: tn -> f pointwise via squeeze *)
  SUBGOAL_THEN `!(x:A). x IN prob_carrier p
                ==> ((\n. (tn:num->A->real) n x) ---> (f:A->real) x) sequentially`
    ASSUME_TAC THENL [
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REALLIM_TRANSFORM_STRADDLE THEN
    EXISTS_TAC `\n. (gn:num->A->real) n x - &1 / &(2 EXP n)` THEN
    EXISTS_TAC `\n:num. (f:A->real) x` THEN
    BETA_TAC THEN REPEAT CONJ_TAC THENL [
      (* eventually lower bound: gn n x - 1/2^n <= tn n x *)
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      MP_TAC(SPEC `B:real` REAL_ARCH_SIMPLE) THEN
      DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
      EXISTS_TAC `N:num` THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(sn:num->A->real) n x` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(sn:num->A->real) n x =
                    nonneg_simple_fn_approx p ((gn:num->A->real) n) n x`
        SUBST1_TAC THENL [
        EXPAND_TAC "sn" THEN REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `f - s <= e ==> f - e <= s`) THEN
      MP_TAC(SPECL [`p:A prob_space`; `(gn:num->A->real) n`;
                     `n:num`; `x:A`] NONNEG_SIMPLE_FN_APPROX_GAP) THEN
      ANTS_TAC THENL [
        ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `B:real` THEN CONJ_TAC THENL [
          MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `(f:A->real) x` THEN ASM_SIMP_TAC[];
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N:real` THEN
          ASM_REWRITE_TAC[REAL_OF_NUM_LE]];
        SIMP_TAC[]];
      (* gn n x - 1/2^n -> f x *)
      SUBGOAL_THEN `(f:A->real) x = f x - &0` SUBST1_TAC THENL [
        REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REALLIM_SUB THEN CONJ_TAC THENL [
        ASM_SIMP_TAC[];
        MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
        EXISTS_TAC `\n. inv(&n)` THEN CONJ_TAC THENL [
          REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
          REPEAT STRIP_TAC THEN
          REWRITE_TAC[real_div; REAL_MUL_LID; REAL_ABS_INV; REAL_ABS_NUM] THEN
          MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL [
            REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
            REWRITE_TAC[REAL_OF_NUM_LE; LE_2_EXP]];
          REWRITE_TAC[REALLIM_1_OVER_N]]];
      (* eventually upper bound: tn n x <= f x *)
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      EXISTS_TAC `0` THEN ASM_SIMP_TAC[];
      (* constant -> f x *)
      REWRITE_TAC[REALLIM_CONST]];
    ALL_TAC] THEN
  (* Main squeeze: simple_exp(tn n) <= nn_exp(gn n) <= nn_exp(f) *)
  MATCH_MP_TAC REALLIM_TRANSFORM_STRADDLE THEN
  EXISTS_TAC `\n. simple_expectation p ((tn:num->A->real) n)` THEN
  EXISTS_TAC `\n:num. nn_expectation p (f:A->real)` THEN
  BETA_TAC THEN REPEAT CONJ_TAC THENL [
    (* eventually: simple_exp(tn n) <= nn_exp(gn n) *)
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC BOUNDED_NN_EXPECTATION_GE_SIMPLE THEN
    ASM_SIMP_TAC[] THEN EXISTS_TAC `B:real` THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(f:A->real) x` THEN ASM_SIMP_TAC[];
    (* simple_exp(tn n) -> nn_exp(f) via MCT *)
    MATCH_MP_TAC SIMPLE_MCT_NN_EXPECTATION THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `B:real` THEN ASM_SIMP_TAC[];
    (* eventually: nn_exp(gn n) <= nn_exp(f) *)
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC BOUNDED_NN_EXPECTATION_MONO THEN
    ASM_SIMP_TAC[] THEN EXISTS_TAC `B:real` THEN ASM_SIMP_TAC[];
    (* constant -> nn_exp(f) *)
    REWRITE_TAC[REALLIM_CONST]]);;

(* ========================================================================= *)
(* Fatou's lemma for bounded nonneg random variables                         *)
(* ========================================================================= *)

(* --- real_liminf and helper lemmas --- *)

let real_liminf = new_definition
  `real_liminf (f:num->real) =
   sup {inf {f k | k >= n} | n IN (:num)}`;;

let REAL_LIMINF_LBOUND = prove
 (`!f b B. (!n. b <= f n) /\ (!n. f n <= B)
           ==> b <= real_liminf f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_liminf] THEN
  MATCH_MP_TAC REAL_LE_SUP THEN
  EXISTS_TAC `B:real` THEN
  EXISTS_TAC `inf {(f:num->real) k | k >= 0:num}` THEN
  REPEAT CONJ_TAC THENL
  [REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN EXISTS_TAC `0` THEN REFL_TAC;
   MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `(f:num->real) 0` THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[GE; LE_REFL];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]];
   REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(f:num->real) n` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC INF_LE_ELEMENT THEN CONJ_TAC THENL
    [EXISTS_TAC `b:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
     REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `n:num` THEN
     REWRITE_TAC[GE; LE_REFL]];
    ASM_REWRITE_TAC[]]]);;

let REAL_LIMINF_UBOUND = prove
 (`!f b B. (!n. b <= f n) /\ (!n. f n <= B)
           ==> real_liminf f <= B`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_liminf] THEN
  MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
  [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; IN_UNIV] THEN
   EXISTS_TAC `inf {(f:num->real) k | k >= 0:num}` THEN
   EXISTS_TAC `0` THEN REFL_TAC;
   REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(f:num->real) n` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC INF_LE_ELEMENT THEN CONJ_TAC THENL
    [EXISTS_TAC `b:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
     REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `n:num` THEN
     REWRITE_TAC[GE; LE_REFL]];
    ASM_REWRITE_TAC[]]]);;

let REAL_LIMINF_MONO = prove
 (`!f g b B. (!n. f n <= g n) /\ (!n. b <= f n) /\ (!n. g n <= B)
             ==> real_liminf f <= real_liminf g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_liminf] THEN
  MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
  [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; IN_UNIV] THEN
   EXISTS_TAC `inf {(f:num->real) k | k >= 0:num}` THEN
   EXISTS_TAC `0` THEN REFL_TAC;
   REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LE_SUP THEN
   EXISTS_TAC `B:real` THEN
   EXISTS_TAC `inf {(g:num->real) k | k >= n}` THEN
   REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN EXISTS_TAC `n:num` THEN
    REFL_TAC;
    MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
    [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
     EXISTS_TAC `(g:num->real) n` THEN EXISTS_TAC `n:num` THEN
     REWRITE_TAC[GE; LE_REFL];
     REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `inf {(f:num->real) k | k >= n}` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(f:num->real) k` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC INF_LE_ELEMENT THEN CONJ_TAC THENL
      [EXISTS_TAC `b:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
       REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
       REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `k:num` THEN
       ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[]]];
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(g:num->real) n'` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC INF_LE_ELEMENT THEN CONJ_TAC THENL
     [EXISTS_TAC `b:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(f:num->real) k` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `n':num` THEN
      REWRITE_TAC[GE; LE_REFL]];
     ASM_REWRITE_TAC[]]]]);;

let REALLIM_IMP_REAL_LIMINF = prove
 (`!f l b B. (f ---> l) sequentially /\ (!n. b <= f n) /\ (!n. f n <= B)
             ==> real_liminf f = l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_liminf] THEN
  MATCH_MP_TAC REAL_SUP_UNIQUE THEN CONJ_TAC THENL
  [REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LBOUND) THEN
   EXISTS_TAC `f:num->real` THEN
   ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
   REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
   EXISTS_TAC `n:num` THEN REPEAT STRIP_TAC THEN
   MATCH_MP_TAC INF_LE_ELEMENT THEN
   CONJ_TAC THENL
   [EXISTS_TAC `b:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `n':num` THEN
    ASM_REWRITE_TAC[GE]];
   REPEAT STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
   DISCH_THEN(MP_TAC o SPEC `(l - b') / &2`) THEN
   ASM_SIMP_TAC[REAL_SUB_LT; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
   STRIP_TAC THEN EXISTS_TAC `inf {(f:num->real) k | k >= N}` THEN
   CONJ_TAC THENL
   [EXISTS_TAC `N:num` THEN REFL_TAC;
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(l + b') / &2` THEN
    CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `(f:num->real) N` THEN EXISTS_TAC `N:num` THEN
      REWRITE_TAC[GE; LE_REFL];
      REWRITE_TAC[IN_ELIM_THM; GE] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REAL_ARITH_TAC]]]]);;

let iter_min = define
  `(iter_min (X:num->real) (N:num) 0 = X N) /\
   (iter_min X N (SUC j) = min (X (N + SUC j)) (iter_min X N j))`;;

let ITER_MIN_MONO = prove
 (`!X N j. iter_min X N (SUC j) <= iter_min X N j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[iter_min] THEN REAL_ARITH_TAC);;

let ITER_MIN_LE = prove
 (`!X N j k. N <= k /\ k <= N + j ==> iter_min X N j <= X k`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [REPEAT STRIP_TAC THEN SUBGOAL_THEN `k:num = N` SUBST_ALL_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[iter_min; REAL_LE_REFL]];
   REPEAT STRIP_TAC THEN REWRITE_TAC[iter_min] THEN
   ASM_CASES_TAC `k = N + SUC j` THENL
   [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> min a b <= c`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

let ITER_MIN_POS = prove
 (`!X N j. (!n. &0 <= X n) ==> &0 <= iter_min X N j`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [REWRITE_TAC[iter_min] THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[iter_min] THEN STRIP_TAC THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= min a b`) THEN
   ASM_SIMP_TAC[]]);;

let RANDOM_VARIABLE_ITER_MIN = prove
 (`!p:A prob_space X N j.
     (!n. random_variable p (X n))
     ==> random_variable p (\x. iter_min (\n. X n x) N j)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN STRIP_TAC THENL
  [REWRITE_TAC[iter_min; ETA_AX] THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[iter_min] THEN
   MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN ASM_SIMP_TAC[ETA_AX]]);;

let RANDOM_VARIABLE_INF_SEQ = prove
 (`!p:A prob_space (X:num->A->real) N.
     (!n. random_variable p (X n)) /\
     (!n x. x IN prob_carrier p ==> &0 <= X n x)
     ==> random_variable p (\x. inf {X k x | k >= N})`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RANDOM_VARIABLE_POINTWISE_LIMIT THEN
  EXISTS_TAC `\j x:A. iter_min (\n. X n x) N j` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_ITER_MIN THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!j. &0 <= iter_min (\n. (X:num->A->real) n x) N j`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC ITER_MIN_POS THEN
   GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `x:A`]) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!k. k >= N ==> inf {(X:num->A->real) k x | k >= N} <= X k x`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC INF_LE_ELEMENT THEN CONJ_TAC THENL
   [EXISTS_TAC `&0` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!j. inf {(X:num->A->real) k x | k >= N} <= iter_min (\n. X n x) N j`
    ASSUME_TAC THENL
  [INDUCT_TAC THENL
   [REWRITE_TAC[iter_min] THEN FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
    REWRITE_TAC[GE; LE_REFL];
    REWRITE_TAC[iter_min] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b /\ a <= c ==> a <= min b c`) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPEC `N + SUC j`) THEN
    REWRITE_TAC[GE] THEN DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC];
   ALL_TAC] THEN
  ABBREV_TAC `i = inf {(X:num->A->real) k x | k >= N}` THEN
  SUBGOAL_THEN `?k:num. k >= N /\ (X:num->A->real) k x < i + e`
    STRIP_ASSUME_TAC THENL
  [MP_TAC(ISPECL [`{(X:num->A->real) k x | k >= N}`; `i + e:real`]
    INF_APPROACH) THEN
   ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
    [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
     EXISTS_TAC `(X:num->A->real) N x` THEN EXISTS_TAC `N:num` THEN
     REWRITE_TAC[GE; LE_REFL];
     CONJ_TAC THENL
     [EXISTS_TAC `&0` THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
      ASM_REAL_ARITH_TAC]];
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
   EXISTS_TAC `k - N:num` THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
   SUBGOAL_THEN `iter_min (\n. (X:num->A->real) n x) N j <= X k x`
     ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\n. (X:num->A->real) n x`; `N:num`; `j:num`; `k:num`]
     ITER_MIN_LE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `k:num >= N` THEN REWRITE_TAC[GE] THEN
    UNDISCH_TAC `k - N:num <= j` THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REAL_ARITH_TAC]]);;

(* --- Convergence of increasing bounded sequences to sup --- *)

let MONOTONE_EXTENDS = prove
 (`!s:num->real. (!n. s n <= s (SUC n))
                 ==> (!m n. m <= n ==> s m <= s n)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `\m n:num. (s:num->real) m <= s n`
    TRANSITIVE_STEPWISE_LE) THEN
  REWRITE_TAC[REAL_LE_REFL] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; SIMP_TAC[]]);;

let INCREASING_BOUNDED_CONVERGES_TO_SUP = prove
 (`!s:num->real b B. (!n. b <= s n) /\ (!n. s n <= B) /\
                     (!n. s n <= s (SUC n))
    ==> (s ---> sup {s n | n IN (:num)}) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!m n. m <= n ==> (s:num->real) m <= s n` ASSUME_TAC THENL
  [MATCH_MP_TAC MONOTONE_EXTENDS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:num->real`; `abs b + abs B`]
    CONVERGENT_BOUNDED_MONOTONE) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH
      `b <= x /\ x <= B ==> abs x <= abs b + abs B`) THEN
    ASM_REWRITE_TAC[];
    DISJ1_TAC THEN ASM_REWRITE_TAC[]];
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   DISCH_THEN(X_CHOOSE_TAC `l:real`) THEN
   SUBGOAL_THEN `!n:num. (s:num->real) n <= l` ASSUME_TAC THENL
   [GEN_TAC THEN
    MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LBOUND) THEN
    EXISTS_TAC `s:num->real` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; REALLIM_SEQUENTIALLY] THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `n:num` THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `sup {(s:num->real) n | n IN (:num)} <= l` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
    [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; IN_UNIV] THEN
     EXISTS_TAC `(s:num->real) 0` THEN EXISTS_TAC `0` THEN REFL_TAC;
     REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN REPEAT STRIP_TAC THEN
     ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   SUBGOAL_THEN `l <= sup {(s:num->real) n | n IN (:num)}` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
    EXISTS_TAC `s:num->real` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; REALLIM_SEQUENTIALLY] THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_SUP THEN EXISTS_TAC `B:real` THEN
    EXISTS_TAC `(s:num->real) n` THEN REPEAT CONJ_TAC THENL
    [REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN EXISTS_TAC `n:num` THEN
     REFL_TAC;
     REWRITE_TAC[REAL_LE_REFL];
     REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN REPEAT STRIP_TAC THEN
     ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   ABBREV_TAC `S = sup {(s:num->real) n | n IN (:num)}` THEN
   SUBGOAL_THEN `l:real = S` SUBST_ALL_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]]);;

(* --- Fatou's lemma --- *)

let FATOU_NN_EXPECTATION = prove
 (`!p:A prob_space X B.
     (!n. random_variable p (X n)) /\
     (!n x. x IN prob_carrier p ==> &0 <= X n x) /\
     (!n x. x IN prob_carrier p ==> X n x <= B)
     ==> nn_expectation p (\x. real_liminf (\n. X n x))
         <= real_liminf (\n. nn_expectation p (X n))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `gn = \n x:A. inf {(X:num->A->real) k x | k >= n}` THEN
  SUBGOAL_THEN `!n. random_variable p ((gn:num->A->real) n)` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "gn" THEN REWRITE_TAC[] THEN
   MATCH_MP_TAC RANDOM_VARIABLE_INF_SEQ THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n x:A. x IN prob_carrier p ==> &0 <= (gn:num->A->real) n x`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "gn" THEN REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `(X:num->A->real) n x` THEN EXISTS_TAC `n:num` THEN
    REWRITE_TAC[GE; LE_REFL];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n x:A. x IN prob_carrier p ==> (gn:num->A->real) n x <= B`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "gn" THEN REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(X:num->A->real) n x` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC INF_LE_ELEMENT THEN CONJ_TAC THENL
    [EXISTS_TAC `&0` THEN REWRITE_TAC[IN_ELIM_THM] THEN
     REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
     REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `n:num` THEN
     REWRITE_TAC[GE; LE_REFL]];
    ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n x:A. x IN prob_carrier p
                         ==> (gn:num->A->real) n x <= gn (SUC n) x`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "gn" THEN REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `(X:num->A->real) (SUC n) x` THEN EXISTS_TAC `SUC n` THEN
    REWRITE_TAC[GE; LE_REFL];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INF_LE_ELEMENT THEN CONJ_TAC THENL
    [EXISTS_TAC `&0` THEN REWRITE_TAC[IN_ELIM_THM] THEN
     REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
     REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `k:num` THEN
     ASM_REWRITE_TAC[GE] THEN ASM_ARITH_TAC]];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n x:A. x IN prob_carrier p
                         ==> (gn:num->A->real) n x <= X n x`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "gn" THEN REWRITE_TAC[] THEN
   MATCH_MP_TAC INF_LE_ELEMENT THEN CONJ_TAC THENL
   [EXISTS_TAC `&0` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `n:num` THEN
    REWRITE_TAC[GE; LE_REFL]];
   ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN prob_carrier p
    ==> ((\n. (gn:num->A->real) n x) --->
         real_liminf (\n. (X:num->A->real) n x)) sequentially`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN REWRITE_TAC[real_liminf] THEN
   SUBGOAL_THEN `{inf {(X:num->A->real) k x | k >= n} | n IN (:num)} =
                 {(gn:num->A->real) n x | n IN (:num)}`
     SUBST1_TAC THENL
   [EXPAND_TAC "gn" THEN REWRITE_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC INCREASING_BOUNDED_CONVERGES_TO_SUP THEN
   EXISTS_TAC `&0` THEN EXISTS_TAC `B:real` THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN prob_carrier p
    ==> &0 <= real_liminf (\n. (X:num->A->real) n x)` ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN REWRITE_TAC[real_liminf] THEN
   SUBGOAL_THEN `{inf {(X:num->A->real) k x | k >= n} | n IN (:num)} =
                 {(gn:num->A->real) n x | n IN (:num)}`
     SUBST1_TAC THENL
   [EXPAND_TAC "gn" THEN REWRITE_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_SUP THEN EXISTS_TAC `B:real` THEN
   EXISTS_TAC `(gn:num->A->real) 0 x` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN EXISTS_TAC `0` THEN REFL_TAC;
    ASM_SIMP_TAC[];
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN prob_carrier p
    ==> real_liminf (\n. (X:num->A->real) n x) <= B` ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN REWRITE_TAC[real_liminf] THEN
   SUBGOAL_THEN `{inf {(X:num->A->real) k x | k >= n} | n IN (:num)} =
                 {(gn:num->A->real) n x | n IN (:num)}`
     SUBST1_TAC THENL
   [EXPAND_TAC "gn" THEN REWRITE_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; IN_UNIV] THEN
    EXISTS_TAC `(gn:num->A->real) 0 x` THEN EXISTS_TAC `0` THEN REFL_TAC;
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `((\n. nn_expectation p ((gn:num->A->real) n)) --->
      nn_expectation p (\x. real_liminf (\n. X n x))) sequentially`
    ASSUME_TAC THENL
  [MATCH_MP_TAC MCT_NN_EXPECTATION_RV THEN
   EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n. nn_expectation p ((gn:num->A->real) n) <=
                    nn_expectation p ((X:num->A->real) n)` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC BOUNDED_NN_EXPECTATION_MONO THEN
   ASM_SIMP_TAC[] THEN EXISTS_TAC `B:real` THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n. &0 <= nn_expectation p ((gn:num->A->real) n)`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC NN_EXPECTATION_POS THEN
   ASM_SIMP_TAC[] THEN EXISTS_TAC `B:real` THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n. nn_expectation p ((X:num->A->real) n) <= B`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC NN_EXPECTATION_UPPER_BOUND THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n. nn_expectation p ((gn:num->A->real) n) <= B`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `nn_expectation p ((X:num->A->real) n)` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `nn_expectation p (\x:A. real_liminf (\n. X n x)) =
     real_liminf (\n. nn_expectation p ((gn:num->A->real) n))`
    SUBST1_TAC THENL
  [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REALLIM_IMP_REAL_LIMINF THEN
   EXISTS_TAC `&0` THEN EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC REAL_LIMINF_MONO THEN
   EXISTS_TAC `&0` THEN EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Bounded Dominated Convergence Theorem                                     *)
(* ========================================================================= *)

let real_limsup = new_definition
  `real_limsup (f:num->real) =
   inf {sup {f k | k >= n} | n IN (:num)}`;;

let REAL_LIMINF_EVENTUALLY_LBOUND = prove
 (`!f b B L.
     (!n. b <= f n) /\ (!n. f n <= B) /\ L <= real_liminf f
     ==> !e. &0 < e ==> ?N. !n. N <= n ==> L - e < f n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `L - e < real_liminf (f:num->real)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[real_liminf] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`{inf {(f:num->real) k | k >= n} | n IN (:num)}`;
                  `L - e:real`] SUP_APPROACH) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; IN_UNIV] THEN
    EXISTS_TAC `inf {(f:num->real) k | k >= 0}` THEN
    EXISTS_TAC `0` THEN REFL_TAC;
    EXISTS_TAC `B:real` THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(f:num->real) n` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC INF_LE_ELEMENT THEN CONJ_TAC THENL
     [EXISTS_TAC `b:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `n:num` THEN
      REWRITE_TAC[GE; LE_REFL]];
     ASM_REWRITE_TAC[]]];
   ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `N:num` ASSUME_TAC) ASSUME_TAC) THEN
  EXISTS_TAC `N:num` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `L - e < inf {(f:num->real) k | k >= N}` ASSUME_TAC THENL
  [UNDISCH_TAC `L - e < s:real` THEN
   UNDISCH_TAC `s = inf {(f:num->real) k | k >= N}` THEN
   DISCH_THEN SUBST1_TAC THEN SIMP_TAC[];
   MATCH_MP_TAC REAL_LTE_TRANS THEN
   EXISTS_TAC `inf {(f:num->real) k | k >= N}` THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC INF_LE_ELEMENT THEN CONJ_TAC THENL
   [EXISTS_TAC `b:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `n:num` THEN
    ASM_REWRITE_TAC[GE]]]);;

let BOUNDED_LIMINF_SANDWICH = prove
 (`!f b B L c.
     (!n. b <= f n) /\ (!n. f n <= B) /\
     L <= real_liminf f /\
     c - L <= real_liminf (\n. c - f n)
     ==> (f ---> L) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`f:num->real`; `b:real`; `B:real`; `L:real`]
    REAL_LIMINF_EVENTUALLY_LBOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  SUBGOAL_THEN
    `!n:num. c - B <= (\n. c - (f:num->real) n) n` ASSUME_TAC THENL
  [GEN_TAC THEN REWRITE_TAC[] THEN
   UNDISCH_TAC `!n. (f:num->real) n <= B` THEN
   DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `!n:num. (\n. c - (f:num->real) n) n <= c - b` ASSUME_TAC THENL
  [GEN_TAC THEN REWRITE_TAC[] THEN
   UNDISCH_TAC `!n. b <= (f:num->real) n` THEN
   DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`\n:num. c - (f:num->real) n`; `c - B:real`;
    `c - b:real`; `c - L:real`] REAL_LIMINF_EVENTUALLY_LBOUND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  EXISTS_TAC `MAX N1 N2` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `N1:num <= n` ASSUME_TAC THENL
  [UNDISCH_TAC `MAX N1 N2 <= n` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `N2:num <= n` ASSUME_TAC THENL
  [UNDISCH_TAC `MAX N1 N2 <= n` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `L - e < (f:num->real) n` ASSUME_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:num->real) n < L + e` ASSUME_TAC THENL
  [UNDISCH_TAC `!n. N2 <= n ==> c - L - e < c - (f:num->real) n` THEN
   DISCH_THEN(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let NN_EXPECTATION_CONST = prove
 (`!p:A prob_space B. &0 <= B ==> nn_expectation p (\x. B) = B`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `nn_expectation p (\x:A. B) = simple_expectation p (\x. B)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC NN_EXPECTATION_SIMPLE THEN
   REWRITE_TAC[SIMPLE_RV_CONST] THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[SIMPLE_EXPECTATION_CONST]]);;

let NN_EXPECTATION_CONST_MINUS = prove
 (`!p:A prob_space f B.
     random_variable p f /\
     (!x. x IN prob_carrier p ==> &0 <= f x) /\
     (!x. x IN prob_carrier p ==> f x <= B)
     ==> nn_expectation p (\x. B - f x) = B - nn_expectation p f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= B:real` ASSUME_TAC THENL
  [MP_TAC(ISPEC `p:A prob_space` PROB_CARRIER_NONEMPTY) THEN
   REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
   DISCH_THEN(X_CHOOSE_TAC `a:A`) THEN
   ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `random_variable p (\x:A. B - f x)` ASSUME_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN
   ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST]; ALL_TAC] THEN
  SUBGOAL_THEN
    `nn_expectation p f + nn_expectation p (\x:A. B - f x) =
     nn_expectation p (\x. B)` ASSUME_TAC THENL
  [SUBGOAL_THEN
     `nn_expectation p (\x:A. B) =
      nn_expectation p (\x. f x + (B - f x))` SUBST1_TAC THENL
   [MATCH_MP_TAC NN_EXPECTATION_EXT THEN GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   CONV_TAC SYM_CONV THEN MATCH_MP_TAC BOUNDED_NN_EXPECTATION_ADD THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    UNDISCH_TAC `!x:A. x IN prob_carrier p ==> f x <= B` THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    EXISTS_TAC `B:real` THEN ASM_SIMP_TAC[];
    EXISTS_TAC `B:real` THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    UNDISCH_TAC `!x:A. x IN prob_carrier p ==> &0 <= f x` THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `nn_expectation p (\x:A. B) = B` ASSUME_TAC THENL
  [ASM_SIMP_TAC[NN_EXPECTATION_CONST]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let BOUNDED_CONVERGENCE_NN = prove
 (`!p:A prob_space (X:num->A->real) Y B.
     (!n. random_variable p (X n)) /\
     random_variable p Y /\
     (!n x. x IN prob_carrier p ==> &0 <= X n x) /\
     (!x. x IN prob_carrier p ==> &0 <= Y x) /\
     (!n x. x IN prob_carrier p ==> X n x <= B) /\
     (!x. x IN prob_carrier p ==> Y x <= B) /\
     (!x. x IN prob_carrier p ==> ((\n. X n x) ---> Y x) sequentially)
     ==> ((\n. nn_expectation p (X n)) ---> nn_expectation p Y) sequentially`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SPEC `\n:num. nn_expectation (p:A prob_space)
    ((X:num->A->real) n)` BOUNDED_LIMINF_SANDWICH) THEN
  MAP_EVERY EXISTS_TAC [`&0`; `B:real`; `B:real`] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `!n:num. &0 <= nn_expectation (p:A prob_space)
    ((X:num->A->real) n)` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC NN_EXPECTATION_POS THEN
   ASM_SIMP_TAC[] THEN EXISTS_TAC `B:real` THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n:num. nn_expectation (p:A prob_space)
    ((X:num->A->real) n) <= B` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC NN_EXPECTATION_UPPER_BOUND THEN
   ASM_SIMP_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!x:A. x IN prob_carrier p ==>
       real_liminf (\n. (X:num->A->real) n x) = Y x` ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC REALLIM_IMP_REAL_LIMINF THEN
   EXISTS_TAC `&0` THEN EXISTS_TAC `B:real` THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `nn_expectation p (Y:A->real) <=
    real_liminf (\n. nn_expectation p ((X:num->A->real) n))` ASSUME_TAC THENL
  [SUBGOAL_THEN
     `nn_expectation p (Y:A->real) =
      nn_expectation p (\x. real_liminf (\n. (X:num->A->real) n x))`
     SUBST1_TAC THENL
   [MATCH_MP_TAC NN_EXPECTATION_EXT THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC FATOU_NN_EXPECTATION THEN
    EXISTS_TAC `B:real` THEN ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `B - nn_expectation p (Y:A->real) =
    nn_expectation p (\x. B - Y x)` SUBST1_TAC THENL
  [CONV_TAC SYM_CONV THEN MATCH_MP_TAC NN_EXPECTATION_CONST_MINUS THEN
   ASM_SIMP_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!x:A. x IN prob_carrier p ==>
       real_liminf (\n. B - (X:num->A->real) n x) = B - Y x`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC REALLIM_IMP_REAL_LIMINF THEN
   EXISTS_TAC `&0` THEN EXISTS_TAC `B:real` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_SUB THEN ASM_SIMP_TAC[REALLIM_CONST];
    X_GEN_TAC `m:num` THEN ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `!n:num (x:A). x IN prob_carrier p
      ==> (X:num->A->real) n x <= B` THEN
    DISCH_THEN(MP_TAC o SPECL [`m:num`; `x:A`]) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    X_GEN_TAC `m:num` THEN ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `!n:num (x:A). x IN prob_carrier p
      ==> &0 <= (X:num->A->real) n x` THEN
    DISCH_THEN(MP_TAC o SPECL [`m:num`; `x:A`]) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `nn_expectation p (\x:A. B - Y x) =
     nn_expectation p (\x. real_liminf (\n. B - (X:num->A->real) n x))`
    SUBST1_TAC THENL
  [MATCH_MP_TAC NN_EXPECTATION_EXT THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `real_liminf (\n. nn_expectation p
      (\x:A. B - (X:num->A->real) n x))` THEN
  CONJ_TAC THENL
  [MP_TAC(SPECL [`p:A prob_space`;
    `\n:num. \x:A. B - (X:num->A->real) n x`; `B:real`]
    FATOU_NN_EXPECTATION) THEN
   REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
   REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN
    CONJ_TAC THENL
    [REWRITE_TAC[RANDOM_VARIABLE_CONST]; ALL_TAC] THEN
    SUBGOAL_THEN `(\x:A. (X:num->A->real) n x) = X n` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM]; ASM_REWRITE_TAC[]];
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC `!n:num (x:A). x IN prob_carrier p
      ==> (X:num->A->real) n x <= B` THEN
    DISCH_THEN(MP_TAC o SPECL [`n:num`; `x:A`]) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC `!n:num (x:A). x IN prob_carrier p
      ==> &0 <= (X:num->A->real) n x` THEN
    DISCH_THEN(MP_TAC o SPECL [`n:num`; `x:A`]) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!n:num. nn_expectation p (\x:A. B - (X:num->A->real) n x) =
             B - nn_expectation p (X n)` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC NN_EXPECTATION_CONST_MINUS THEN
   ASM_SIMP_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `(\n:num. nn_expectation p (\x:A. B - (X:num->A->real) n x)) =
     (\n. B - nn_expectation p (X n))` SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[];
   REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Fatou's lemma for integrable (unbounded) functions.                       *)
(* Drops the uniform pointwise bound from FATOU_NN_EXPECTATION; instead      *)
(* requires integrability and a bound on expectations. Conclusion uses        *)
(* truncation min(...,M) to ensure well-definedness.                         *)
(* ------------------------------------------------------------------------- *)

let FATOU_INTEGRABLE = prove
  (`!p:A prob_space X M.
      (!n. integrable p (X n)) /\
      (!n x. x IN prob_carrier p ==> &0 <= X n x) /\
      &0 < M /\
      (?B. !n. nn_expectation p (X n) <= B)
      ==> nn_expectation p (\x. real_liminf (\n. min (X n x) M))
          <= real_liminf (\n. nn_expectation p (X n))`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC
     `real_liminf (\n. nn_expectation (p:A prob_space)
        (\x. min ((X:num->A->real) n x) M))` THEN
   CONJ_TAC THENL
   [(* Bounded Fatou on min(X_n, M) *)
    MP_TAC(ISPECL [`p:A prob_space`;
                    `\n:num. \x:A. min ((X:num->A->real) n x) M`;
                    `M:real`] FATOU_NN_EXPECTATION) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
     CONJ_TAC THENL
     [UNDISCH_TAC `!n. integrable (p:A prob_space) ((X:num->A->real) n)` THEN
      DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
      REWRITE_TAC[integrable] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[ETA_AX];
      REWRITE_TAC[RANDOM_VARIABLE_CONST]];
     REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_MIN] THEN
     ASM_SIMP_TAC[REAL_LT_IMP_LE];
     REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_MIN_LE] THEN
     DISJ2_TAC THEN REAL_ARITH_TAC];
    (* Monotonicity: nn_exp(min(X_n,M)) <= nn_exp(X_n) *)
    MP_TAC(ISPECL
      [`\n. nn_expectation (p:A prob_space)
              (\x:A. min ((X:num->A->real) n x) M)`;
       `\n. nn_expectation (p:A prob_space) ((X:num->A->real) n)`;
       `&0`; `B:real`] REAL_LIMINF_MONO) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC NN_EXPECTATION_MONO THEN
     REPEAT CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_LE_MIN] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[];
      GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_MIN_LE] THEN
      DISJ1_TAC THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]];
     GEN_TAC THEN MATCH_MP_TAC NN_EXPECTATION_POS THEN
     CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_MIN] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      EXISTS_TAC `M:real` THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[REAL_MIN_LE] THEN DISJ2_TAC THEN REAL_ARITH_TAC];
     ASM_REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* KOLMOGOROV 0-1 LAW                                                        *)
(* Tail events of independent event sequences have probability 0 or 1.      *)
(* Uses the Dynkin pi-lambda theorem (proved above) to bootstrap             *)
(* independence from finite intersections to sigma-algebras.                 *)
(* ========================================================================= *)

let tail_sigma = new_definition
  `tail_sigma (p:A prob_space) (B:num->A->bool) =
   INTERS {sigma_generated (prob_carrier p) (IMAGE B (from n)) | n IN (:num)}`;;

let fin_inters = new_definition
  `fin_inters (p:A prob_space) (B:num->A->bool) S =
   {prob_carrier p} UNION
   {INTERS (IMAGE B s) | FINITE s /\ s SUBSET S /\ ~(s = {})}`;;

let INTERS_IMAGE_IN_EVENTS = prove
 (`!p:A prob_space B (s:num->bool).
    FINITE s /\ ~(s = {}) /\
    (!n. n IN s ==> B n IN prob_events p)
    ==> INTERS (IMAGE B s) IN prob_events p`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PROB_COUNTABLE_INTERS_IN_EVENTS THEN
  ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN CONJ_TAC THENL
  [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[];
   MATCH_MP_TAC COUNTABLE_IMAGE THEN ASM_SIMP_TAC[FINITE_IMP_COUNTABLE]]);;

let FIN_INTERS_PI_SYSTEM = prove
 (`!p:A prob_space B S.
    (!n. n IN S ==> B n IN prob_events p)
    ==> pi_system (fin_inters p B S)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[fin_inters; pi_system] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNION; IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THENL
  [ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN SET_TAC[];
   DISJ2_TAC THEN EXISTS_TAC `s:num->bool` THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `INTERS (IMAGE (B:num->A->bool) s) SUBSET prob_carrier p`
     ASSUME_TAC THENL
   [SUBGOAL_THEN `INTERS (IMAGE (B:num->A->bool) s) IN prob_events p`
      MP_TAC THENL
    [MATCH_MP_TAC INTERS_IMAGE_IN_EVENTS THEN
     ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET; IN];
     ASM_MESON_TAC[PROB_EVENT_SUBSET]]; ALL_TAC] THEN
   ASM SET_TAC[];
   DISJ2_TAC THEN EXISTS_TAC `s:num->bool` THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `INTERS (IMAGE (B:num->A->bool) s) SUBSET prob_carrier p`
     ASSUME_TAC THENL
   [SUBGOAL_THEN `INTERS (IMAGE (B:num->A->bool) s) IN prob_events p`
      MP_TAC THENL
    [MATCH_MP_TAC INTERS_IMAGE_IN_EVENTS THEN
     ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET; IN];
     ASM_MESON_TAC[PROB_EVENT_SUBSET]]; ALL_TAC] THEN
   ASM SET_TAC[];
   DISJ2_TAC THEN EXISTS_TAC `(s:num->bool) UNION s'` THEN
   ASM_SIMP_TAC[FINITE_UNION] THEN
   CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
   ASM_REWRITE_TAC[IMAGE_UNION; INTERS_UNION]]);;

let SIGMA_GENERATED_SUBSET_EVENTS = prove
 (`!p:A prob_space P.
    P SUBSET prob_events p
    ==> sigma_generated (prob_carrier p) P SUBSET prob_events p`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SIGMA_GENERATED_MINIMAL THEN
  ASM_REWRITE_TAC[PROB_SPACE_SIGMA_ALGEBRA; GSYM prob_carrier]);;

let INDEP_LAMBDA_SYSTEM = prove
 (`!p:A prob_space A.
    A IN prob_events p ==>
    lambda_system (prob_carrier p)
      {C | C IN prob_events p /\
           prob p (A INTER C) = prob p A * prob p C}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lambda_system; IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THENL
  [ASM_MESON_TAC[PROB_CARRIER_IN_EVENTS];
   SUBGOAL_THEN `(A:A->bool) INTER prob_carrier p = A` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER] THEN
    ASM_MESON_TAC[PROB_EVENT_SUBSET; SUBSET]; ALL_TAC] THEN
   MP_TAC(ISPEC `p:A prob_space` PROB_SPACE) THEN
   DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_MUL_RID];
   X_GEN_TAC `C:A->bool` THEN
   DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC) THEN
   CONJ_TAC THENL [ASM_MESON_TAC[PROB_COMPL_IN_EVENTS]; ALL_TAC] THEN
   SUBGOAL_THEN `(A:A->bool) SUBSET prob_carrier p` ASSUME_TAC THENL
   [ASM_MESON_TAC[PROB_EVENT_SUBSET]; ALL_TAC] THEN
   SUBGOAL_THEN `(A:A->bool) INTER (prob_carrier p DIFF C) =
     A DIFF (A INTER C)` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `(A:A->bool) INTER C IN prob_events p` ASSUME_TAC THENL
   [MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   MP_TAC(SPECL [`p:A prob_space`; `A:A->bool`; `(A:A->bool) INTER C`]
     PROB_DIFF) THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `(A:A->bool) INTER A INTER C = A INTER C` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
   MP_TAC(SPECL [`p:A prob_space`; `C:A->bool`] PROB_COMPL) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
   X_GEN_TAC `B:num->A->bool` THEN STRIP_TAC THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC PROB_COUNTABLE_UNION_IN_EVENTS THEN
    CONJ_TAC THENL
    [REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN ASM_MESON_TAC[];
     REWRITE_TAC[SIMPLE_IMAGE] THEN
     MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[NUM_COUNTABLE]];
    ALL_TAC] THEN
   SUBGOAL_THEN `(A:A->bool) INTER UNIONS {B k | k IN (:num)} =
     UNIONS {A INTER B k | k IN (:num)}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
    MESON_TAC[]; ALL_TAC] THEN
   MP_TAC(SPECL [`p:A prob_space`; `\k:num. (A:A->bool) INTER B k`]
     PROB_COUNTABLY_ADDITIVE) THEN
   BETA_TAC THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN
     ASM_MESON_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `k:num`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `k:num`]) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
   REWRITE_TAC[real_sums] THEN DISCH_TAC THEN
   MP_TAC(SPECL [`p:A prob_space`; `B:num->A->bool`]
     PROB_COUNTABLY_ADDITIVE) THEN
   ASM_REWRITE_TAC[real_sums] THEN DISCH_TAC THEN
   SUBGOAL_THEN `!k:num. prob p ((A:A->bool) INTER B k) =
     prob p A * prob p (B k)` ASSUME_TAC THENL
   [GEN_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN
     `((\n. sum (from 0 INTER (0..n))
       (\k:num. prob p (A:A->bool) * prob p ((B:num->A->bool) k))) --->
       prob p A * prob p (UNIONS {B k | k IN (:num)})) sequentially`
     ASSUME_TAC THENL
   [SUBGOAL_THEN `(\n. sum (from 0 INTER (0..n))
       (\k:num. prob p (A:A->bool) * prob p ((B:num->A->bool) k))) =
     (\n. prob p A * sum (from 0 INTER (0..n)) (\k. prob p (B k)))`
     SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
     REWRITE_TAC[SUM_LMUL]; ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] REALLIM_LMUL) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `((\n. sum (from 0 INTER (0..n))
       (\k:num. prob p (A:A->bool) * prob p ((B:num->A->bool) k))) --->
       prob p (UNIONS {A INTER B n | n IN (:num)})) sequentially`
     ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\n. sum (from 0 INTER (0..n))
       (\k:num. prob p (A:A->bool) * prob p ((B:num->A->bool) k))) =
      (\n. sum (from 0 INTER (0..n)) (\k. prob p (A INTER B k)))`
     SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
     MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_INTER; IN_FROM; IN_NUMSEG] THEN
     GEN_TAC THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
     ASM_MESON_TAC[];
     ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   MP_TAC(ISPECL
     [`sequentially`;
      `\n:num. sum (from 0 INTER (0..n))
       (\k. prob p (A:A->bool) * prob p ((B:num->A->bool) k))`;
      `prob p (UNIONS {(A:A->bool) INTER (B:num->A->bool) n | n IN (:num)})`;
      `prob p (A:A->bool) * prob p (UNIONS {(B:num->A->bool) k | k IN (:num)})`]
     REALLIM_UNIQUE) THEN
   ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY]]);;

let INDEP_EXTENDS_TO_SIGMA = prove
 (`!p:A prob_space A P.
    A IN prob_events p /\
    pi_system P /\ UNIONS P = prob_carrier p /\
    P SUBSET prob_events p /\
    (!C. C IN P ==> prob p (A INTER C) = prob p A * prob p C)
    ==> !C. C IN sigma_generated (prob_carrier p) P
            ==> prob p (A INTER C) = prob p A * prob p C`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `C:A->bool IN prob_events p` ASSUME_TAC THENL
  [ASM_MESON_TAC[SIGMA_GENERATED_SUBSET_EVENTS; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `sigma_generated (prob_carrier p) P SUBSET
    {C:A->bool | C IN prob_events p /\
     prob p (A INTER C) = prob p A * prob p C}` MP_TAC THENL
  [MP_TAC(SPECL [`prob_carrier (p:A prob_space)`; `P:(A->bool)->bool`;
    `{C:A->bool | C IN prob_events p /\
     prob p (A INTER C) = prob p A * prob p C}`]
    DYNKIN_PI_LAMBDA) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC INDEP_LAMBDA_SYSTEM THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[SUBSET]];
   REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

let SIGMA_GENERATED_MONO = prove
 (`!(U:A->bool) C1 C2.
    C1 SUBSET C2 /\ (!a. a IN C2 ==> a SUBSET U)
    ==> sigma_generated U C1 SUBSET sigma_generated U C2`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SIGMA_GENERATED_MINIMAL THEN
  ASM_SIMP_TAC[SIGMA_GENERATED_IS_SIGMA_ALGEBRA;
               SIGMA_GENERATED_CARRIER] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `C2:(A->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[SIGMA_GENERATED_SUPERSET]);;

let INDEP_FIN_INTER_SIGMA_FUTURE = prove
 (`!p:A prob_space (B:num->A->bool) (S1:num->bool) N.
    indep_events_seq p B /\
    FINITE S1 /\ ~(S1 = {}) /\ S1 SUBSET {m | m < N}
    ==> !D. D IN sigma_generated (prob_carrier p) (IMAGE B (from N))
            ==> prob p (INTERS (IMAGE B S1) INTER D) =
                prob p (INTERS (IMAGE B S1)) * prob p D`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!n:num. (B:num->A->bool) n IN prob_events p` ASSUME_TAC THENL
  [ASM_MESON_TAC[indep_events_seq]; ALL_TAC] THEN
  ABBREV_TAC `FI = {prob_carrier (p:A prob_space)} UNION
    {INTERS (IMAGE (B:num->A->bool) s) |
     FINITE s /\ s SUBSET from N /\ ~(s = {})}` THEN
  SUBGOAL_THEN `pi_system (FI:(A->bool)->bool)` ASSUME_TAC THENL
  [EXPAND_TAC "FI" THEN REWRITE_TAC[pi_system] THEN
   CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[IN_UNION; IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM] THEN
   REPEAT GEN_TAC THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN SET_TAC[];
    DISJ2_TAC THEN EXISTS_TAC `s:num->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `INTERS (IMAGE (B:num->A->bool) s) SUBSET prob_carrier p`
      ASSUME_TAC THENL
    [ASM_MESON_TAC[PROB_EVENT_SUBSET; INTERS_IMAGE_IN_EVENTS; SUBSET; IN;
                    from]; ALL_TAC] THEN
    ASM SET_TAC[];
    DISJ2_TAC THEN EXISTS_TAC `s:num->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `INTERS (IMAGE (B:num->A->bool) s) SUBSET prob_carrier p`
      ASSUME_TAC THENL
    [ASM_MESON_TAC[PROB_EVENT_SUBSET; INTERS_IMAGE_IN_EVENTS; SUBSET; IN;
                    from]; ALL_TAC] THEN
    ASM SET_TAC[];
    DISJ2_TAC THEN EXISTS_TAC `(s:num->bool) UNION s'` THEN
    ASM_SIMP_TAC[FINITE_UNION] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IMAGE_UNION; INTERS_UNION]];
   ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS (FI:(A->bool)->bool) = prob_carrier (p:A prob_space)`
    ASSUME_TAC THENL
  [EXPAND_TAC "FI" THEN REWRITE_TAC[UNIONS_UNION; UNIONS_1] THEN
   SUBGOAL_THEN `UNIONS {INTERS (IMAGE (B:num->A->bool) s) |
     FINITE s /\ s SUBSET from N /\ ~(s = {})}
     SUBSET prob_carrier (p:A prob_space)` MP_TAC THENL
   [REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
    X_GEN_TAC `x:A` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:num->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `INTERS (IMAGE (B:num->A->bool) s) IN prob_events p`
      MP_TAC THENL
    [MATCH_MP_TAC INTERS_IMAGE_IN_EVENTS THEN
     ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET; IN; from];
     ASM_MESON_TAC[PROB_EVENT_SUBSET; SUBSET]];
    SET_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `FI SUBSET prob_events (p:A prob_space)` ASSUME_TAC THENL
  [EXPAND_TAC "FI" THEN REWRITE_TAC[UNION_SUBSET; SING_SUBSET] THEN
   CONJ_TAC THENL [REWRITE_TAC[PROB_CARRIER_IN_EVENTS]; ALL_TAC] THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTERS_IMAGE_IN_EVENTS THEN
   ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET; IN; from];
   ALL_TAC] THEN
  SUBGOAL_THEN `INTERS (IMAGE (B:num->A->bool) S1) IN prob_events p`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTERS_IMAGE_IN_EVENTS THEN ASM_REWRITE_TAC[] THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!C:A->bool. C IN FI
    ==> prob p (INTERS (IMAGE (B:num->A->bool) S1) INTER C) =
        prob p (INTERS (IMAGE B S1)) * prob p C` ASSUME_TAC THENL
  [X_GEN_TAC `C:A->bool` THEN EXPAND_TAC "FI" THEN
   REWRITE_TAC[IN_UNION; IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM] THEN
   STRIP_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `INTERS (IMAGE (B:num->A->bool) S1) INTER prob_carrier p =
      INTERS (IMAGE B S1)` SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_INTER] THEN
     ASM_MESON_TAC[PROB_EVENT_SUBSET; SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPEC `p:A prob_space` PROB_SPACE) THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_MUL_RID];
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `INTERS (IMAGE (B:num->A->bool) S1) INTER INTERS (IMAGE B s)
      = INTERS (IMAGE B (S1 UNION s))` SUBST1_TAC THENL
    [REWRITE_TAC[IMAGE_UNION; INTERS_UNION]; ALL_TAC] THEN
    SUBGOAL_THEN `DISJOINT (S1:num->bool) s` ASSUME_TAC THENL
    [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
     X_GEN_TAC `j:num` THEN
     UNDISCH_TAC `(S1:num->bool) SUBSET {m | m < N}` THEN
     UNDISCH_TAC `(s:num->bool) SUBSET from N` THEN
     REWRITE_TAC[SUBSET; IN_ELIM_THM; IN; from] THEN
     MESON_TAC[NOT_LT; LT_IMP_LE]; ALL_TAC] THEN
    UNDISCH_TAC `indep_events_seq (p:A prob_space) B` THEN
    REWRITE_TAC[indep_events_seq] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~((S1:num->bool) UNION s = {})` ASSUME_TAC THENL
    [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[FINITE_UNION] THEN
    SUBGOAL_THEN `product ((S1:num->bool) UNION s)
      (\i. prob p ((B:num->A->bool) i)) =
      product S1 (\i. prob p (B i)) * product s (\i. prob p (B i))`
      SUBST1_TAC THENL
    [MATCH_MP_TAC PRODUCT_UNION THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `(D:A->bool) IN sigma_generated (prob_carrier p) FI`
    ASSUME_TAC THENL
  [SUBGOAL_THEN `sigma_generated (prob_carrier p)
      (IMAGE (B:num->A->bool) (from N))
    SUBSET sigma_generated (prob_carrier p) FI` MP_TAC THENL
   [MATCH_MP_TAC SIGMA_GENERATED_MONO THEN CONJ_TAC THENL
    [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
     X_GEN_TAC `n:num` THEN DISCH_TAC THEN
     EXPAND_TAC "FI" THEN
     REWRITE_TAC[IN_UNION; IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM] THEN
     DISJ2_TAC THEN EXISTS_TAC `{n:num}` THEN
     ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; NOT_INSERT_EMPTY;
                      IMAGE_CLAUSES; INTERS_1] THEN
     ASM SET_TAC[];
     EXPAND_TAC "FI" THEN
     REWRITE_TAC[IN_UNION; IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM] THEN
     X_GEN_TAC `x:A->bool` THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_REFL];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PROB_EVENT_SUBSET THEN
      MATCH_MP_TAC INTERS_IMAGE_IN_EVENTS THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[SUBSET; IN; from]]];
    REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[]];
   ALL_TAC] THEN
  MP_TAC(SPECL [`p:A prob_space`;
    `INTERS(IMAGE (B:num->A->bool) S1)`;
    `FI:(A->bool)->bool`] INDEP_EXTENDS_TO_SIGMA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `D:A->bool`) THEN
  ASM_REWRITE_TAC[]);;

let KOLMOGOROV_ZERO_ONE = prove
 (`!p:A prob_space (B:num->A->bool) E.
    indep_events_seq p B /\
    E IN tail_sigma p B /\ E IN prob_events p
    ==> prob p E = &0 \/ prob p E = &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!n:num. (B:num->A->bool) n IN prob_events p` ASSUME_TAC THENL
  [ASM_MESON_TAC[indep_events_seq]; ALL_TAC] THEN
  SUBGOAL_THEN `!C:A->bool. C IN fin_inters p B (:num)
    ==> prob p (E INTER C) = prob p E * prob p C` ASSUME_TAC THENL
  [X_GEN_TAC `C:A->bool` THEN
   REWRITE_TAC[fin_inters; IN_UNION; IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM] THEN
   STRIP_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(E:A->bool) INTER prob_carrier p = E` SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_INTER] THEN
     ASM_MESON_TAC[PROB_EVENT_SUBSET; SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPEC `p:A prob_space` PROB_SPACE) THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_MUL_RID];
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `s:num->bool` FINITE_SUBSET_NUMSEG) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
    SUBGOAL_THEN `(s:num->bool) SUBSET {m | m < SUC n}` ASSUME_TAC THENL
    [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
     ASM_MESON_TAC[SUBSET; IN_NUMSEG; LT_SUC_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `(E:A->bool) IN sigma_generated (prob_carrier p)
      (IMAGE B (from (SUC n)))` ASSUME_TAC THENL
    [UNDISCH_TAC `E IN tail_sigma (p:A prob_space) B` THEN
     REWRITE_TAC[tail_sigma; IN_INTERS; FORALL_IN_GSPEC; IN_UNIV] THEN
     DISCH_THEN(MP_TAC o SPEC `SUC n`) THEN REWRITE_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN `(E:A->bool) INTER INTERS (IMAGE B s) =
      INTERS (IMAGE (B:num->A->bool) s) INTER E` SUBST1_TAC THENL
    [SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `prob p (INTERS (IMAGE (B:num->A->bool) s) INTER E) =
      prob p (INTERS (IMAGE B s)) * prob p E` SUBST1_TAC THENL
    [MP_TAC(SPECL [`p:A prob_space`; `B:num->A->bool`;
       `s:num->bool`; `SUC n`]
      INDEP_FIN_INTER_SIGMA_FUTURE) THEN
     ASM_REWRITE_TAC[] THEN
     DISCH_THEN(MP_TAC o SPEC `E:A->bool`) THEN ASM_REWRITE_TAC[];
     REAL_ARITH_TAC]];
   ALL_TAC] THEN
  SUBGOAL_THEN `pi_system (fin_inters (p:A prob_space) B (:num))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC FIN_INTERS_PI_SYSTEM THEN ASM_REWRITE_TAC[IN_UNIV];
   ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS (fin_inters (p:A prob_space) B (:num)) =
    prob_carrier p` ASSUME_TAC THENL
  [REWRITE_TAC[fin_inters; UNIONS_UNION; UNIONS_1] THEN
   SUBGOAL_THEN `UNIONS {INTERS (IMAGE (B:num->A->bool) s) |
     FINITE s /\ s SUBSET (:num) /\ ~(s = {})}
     SUBSET prob_carrier (p:A prob_space)` MP_TAC THENL
   [REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
    X_GEN_TAC `x:A` THEN
    DISCH_THEN(X_CHOOSE_THEN `t:num->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `INTERS (IMAGE (B:num->A->bool) t) IN prob_events p`
      MP_TAC THENL
    [MATCH_MP_TAC INTERS_IMAGE_IN_EVENTS THEN
     ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
     ASM_MESON_TAC[PROB_EVENT_SUBSET; SUBSET]];
    SET_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `fin_inters (p:A prob_space) B (:num) SUBSET prob_events p`
    ASSUME_TAC THENL
  [REWRITE_TAC[fin_inters; UNION_SUBSET; SING_SUBSET] THEN
   CONJ_TAC THENL [REWRITE_TAC[PROB_CARRIER_IN_EVENTS]; ALL_TAC] THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTERS_IMAGE_IN_EVENTS THEN
   ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `from 0 = (:num)` ASSUME_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_UNIV; IN; from] THEN GEN_TAC THEN
   REWRITE_TAC[IN_ELIM_THM; LE_0]; ALL_TAC] THEN
  SUBGOAL_THEN `(E:A->bool) IN sigma_generated (prob_carrier p)
    (IMAGE B (:num))` ASSUME_TAC THENL
  [UNDISCH_TAC `E IN tail_sigma (p:A prob_space) B` THEN
   REWRITE_TAC[tail_sigma; IN_INTERS; FORALL_IN_GSPEC; IN_UNIV] THEN
   DISCH_THEN(MP_TAC o SPEC `0`) THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `(E:A->bool) IN sigma_generated (prob_carrier p)
    (fin_inters p B (:num))` ASSUME_TAC THENL
  [MP_TAC(SPECL [`prob_carrier (p:A prob_space)`;
    `IMAGE (B:num->A->bool) (:num)`;
    `fin_inters (p:A prob_space) B (:num)`] SIGMA_GENERATED_MONO) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; fin_inters;
                  IN_UNION; IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM] THEN
     X_GEN_TAC `n:num` THEN DISJ2_TAC THEN
     EXISTS_TAC `{n:num}` THEN
     REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; NOT_INSERT_EMPTY;
                  IMAGE_CLAUSES; INTERS_1] THEN SET_TAC[];
     REWRITE_TAC[fin_inters; IN_UNION; IN_INSERT; NOT_IN_EMPTY;
                  IN_ELIM_THM] THEN
     X_GEN_TAC `x:A->bool` THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[PROB_EVENT_SUBSET; PROB_CARRIER_IN_EVENTS];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PROB_EVENT_SUBSET THEN
      MATCH_MP_TAC INTERS_IMAGE_IN_EVENTS THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]];
    REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[]];
   ALL_TAC] THEN
  MP_TAC(SPECL [`p:A prob_space`;
    `E:A->bool`;
    `fin_inters (p:A prob_space) B (:num)`] INDEP_EXTENDS_TO_SIGMA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `E:A->bool`) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(E:A->bool) INTER E = E` SUBST1_TAC THENL
  [SET_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `prob (p:A prob_space) E * (&1 - prob p E) = &0`
    MP_TAC THENL
  [UNDISCH_TAC `prob (p:A prob_space) E = prob p E * prob p E` THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ENTIRE; REAL_SUB_0] THEN MESON_TAC[]);;

(* ========================================================================= *)
(* Fatou's Lemma for Events and Convergence Relationships                    *)
(* ========================================================================= *)

(* Inner sets of liminf are increasing: intersecting over fewer terms
   gives a larger set *)
let TAIL_INTERS_INCREASING = prove
 (`!A:num->A->bool m.
     INTERS {A n | n >= m} SUBSET INTERS {A n | n >= SUC m}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET; IN_INTERS; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

(* Inner sets of liminf are events *)
let TAIL_INTERS_IN_EVENTS = prove
 (`!p:A prob_space A (m:num).
     (!n. A n IN prob_events p)
     ==> INTERS {A n | n >= m} IN prob_events p`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC PROB_COUNTABLE_INTERS_IN_EVENTS THEN
  REPEAT CONJ_TAC THENL
  [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
   GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[COUNTABLE_GSPEC_NUM];
   REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
   EXISTS_TAC `(A:num->A->bool) m` THEN EXISTS_TAC `m:num` THEN
   REWRITE_TAC[GE; LE_REFL]]);;

(* Fatou's lemma for events (liminf version):
   P(liminf A_n) <= real_liminf (\n. P(A_n)) *)
let FATOU_EVENTS_LIMINF = prove
 (`!p:A prob_space A.
     (!n. A n IN prob_events p)
     ==> prob p (liminf_events A) <=
         real_liminf (\n. prob p (A n))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `C = \m:num. INTERS {(A:num->A->bool) n | n >= m}` THEN
  SUBGOAL_THEN `!m. (C:num->A->bool) m SUBSET C (SUC m)` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "C" THEN REWRITE_TAC[] THEN
   REWRITE_TAC[TAIL_INTERS_INCREASING];
   ALL_TAC] THEN
  SUBGOAL_THEN `!m. (C:num->A->bool) m IN prob_events p` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "C" THEN REWRITE_TAC[] THEN
   MATCH_MP_TAC TAIL_INTERS_IN_EVENTS THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `liminf_events (A:num->A->bool) = UNIONS {C m | m IN (:num)}`
    SUBST1_TAC THENL
  [EXPAND_TAC "C" THEN REWRITE_TAC[liminf_events]; ALL_TAC] THEN
  SUBGOAL_THEN
    `((\m. prob p ((C:num->A->bool) m)) --->
      prob p (UNIONS {C m | m IN (:num)})) sequentially` ASSUME_TAC THENL
  [MATCH_MP_TAC PROB_CONTINUITY_FROM_BELOW THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!m n. n >= m ==> (C:num->A->bool) m SUBSET (A:num->A->bool) n`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "C" THEN
   REWRITE_TAC[SUBSET; IN_INTERS; IN_ELIM_THM] THEN
   REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!m. prob p ((C:num->A->bool) m) <=
    inf {prob p ((A:num->A->bool) n) | n >= m}` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `prob p ((A:num->A->bool) m)` THEN
    EXISTS_TAC `m:num` THEN REWRITE_TAC[GE; LE_REFL];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PROB_MONO THEN
    ASM_SIMP_TAC[GE]];
   ALL_TAC] THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
  EXISTS_TAC `\m:num. prob p ((C:num->A->bool) m)` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inf {prob p ((A:num->A->bool) k) | k >= n}` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[real_liminf] THEN BETA_TAC THEN
  MATCH_MP_TAC REAL_LE_SUP THEN
  EXISTS_TAC `&1` THEN
  EXISTS_TAC `inf {prob p ((A:num->A->bool) k) | k >= n}` THEN
  REPEAT CONJ_TAC THENL
  [REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN EXISTS_TAC `n:num` THEN
   REFL_TAC;
   REWRITE_TAC[REAL_LE_REFL];
   REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
   X_GEN_TAC `y:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `prob p ((A:num->A->bool) n')` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(ISPEC `{prob p ((A:num->A->bool) k) | k >= n'}`
      INF_LE_ELEMENT) THEN
    CONJ_TAC THENL
    [EXISTS_TAC `&0` THEN REWRITE_TAC[IN_ELIM_THM] THEN
     REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `n':num` THEN
     REWRITE_TAC[GE; LE_REFL]];
    MATCH_MP_TAC PROB_LE_1 THEN ASM_REWRITE_TAC[]]]);;

(* Fatou's lemma for events (limsup version):
   real_limsup (\n. P(A_n)) <= P(limsup A_n) *)
let FATOU_EVENTS_LIMSUP = prove
 (`!p:A prob_space A.
     (!n. A n IN prob_events p)
     ==> real_limsup (\n. prob p (A n)) <=
         prob p (limsup_events A)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `D = \m:num. UNIONS {(A:num->A->bool) n | n >= m}` THEN
  SUBGOAL_THEN `!m. (D:num->A->bool) (SUC m) SUBSET D m` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "D" THEN REWRITE_TAC[] THEN
   REWRITE_TAC[TAIL_UNION_DECREASING];
   ALL_TAC] THEN
  SUBGOAL_THEN `!m. (D:num->A->bool) m IN prob_events p` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "D" THEN REWRITE_TAC[] THEN
   MATCH_MP_TAC TAIL_UNION_IN_EVENTS THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `limsup_events (A:num->A->bool) = INTERS {D m | m IN (:num)}`
    SUBST1_TAC THENL
  [EXPAND_TAC "D" THEN REWRITE_TAC[limsup_events]; ALL_TAC] THEN
  SUBGOAL_THEN
    `((\m. prob p ((D:num->A->bool) m)) --->
      prob p (INTERS {D m | m IN (:num)})) sequentially` ASSUME_TAC THENL
  [MATCH_MP_TAC PROB_CONTINUITY_FROM_ABOVE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!m (n:num). n >= m ==> prob p ((A:num->A->bool) n) <=
    prob p ((D:num->A->bool) m)` ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC PROB_MONO THEN
   ASM_REWRITE_TAC[] THEN
   EXPAND_TAC "D" THEN REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   EXISTS_TAC `(A:num->A->bool) n` THEN ASM_REWRITE_TAC[] THEN
   EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!m. sup {prob p ((A:num->A->bool) n) | n >= m} <=
    prob p ((D:num->A->bool) m)` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `prob p ((A:num->A->bool) m)` THEN
    EXISTS_TAC `m:num` THEN REWRITE_TAC[GE; LE_REFL];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[GE]];
   ALL_TAC] THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LBOUND) THEN
  EXISTS_TAC `\m:num. prob p ((D:num->A->bool) m)` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sup {prob p ((A:num->A->bool) k) | k >= n}` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[real_limsup] THEN BETA_TAC THEN
  MATCH_MP_TAC(ISPEC `{sup {prob p ((A:num->A->bool) k) | k >= n} |
      n IN (:num)}` INF_LE_ELEMENT) THEN
  CONJ_TAC THENL
  [EXISTS_TAC `&0` THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `prob p ((A:num->A->bool) n')` THEN CONJ_TAC THENL
   [MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_SUP THEN
    EXISTS_TAC `&1` THEN
    EXISTS_TAC `prob p ((A:num->A->bool) n')` THEN
    REPEAT CONJ_TAC THENL
    [REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `n':num` THEN
     REWRITE_TAC[GE; LE_REFL];
     REWRITE_TAC[REAL_LE_REFL];
     REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PROB_LE_1 THEN
     ASM_REWRITE_TAC[]]];
   REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN EXISTS_TAC `n:num` THEN
   REFL_TAC]);;

(* ========================================================================= *)
(* Real liminf/limsup relationship lemmas                                    *)
(* ========================================================================= *)

(* real_liminf <= real_limsup for bounded sequences *)
let REAL_LIMINF_LE_LIMSUP = prove
 (`!f b B. (!n. b <= f n) /\ (!n. f n <= B)
           ==> real_liminf f <= real_limsup f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_liminf; real_limsup] THEN
  SUBGOAL_THEN `!m n. inf {(f:num->real) k | k >= m} <=
      sup {f k | k >= n}` ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `(f:num->real) (MAX m n)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC INF_LE_ELEMENT THEN CONJ_TAC THENL
    [EXISTS_TAC `b:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
     REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `MAX m n` THEN
     REWRITE_TAC[GE] THEN ARITH_TAC];
    MATCH_MP_TAC REAL_LE_SUP THEN
    EXISTS_TAC `B:real` THEN EXISTS_TAC `(f:num->real) (MAX m n)` THEN
    REPEAT CONJ_TAC THENL
    [REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `MAX m n` THEN
     REWRITE_TAC[GE] THEN ARITH_TAC;
     REWRITE_TAC[REAL_LE_REFL];
     REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
     ASM_REWRITE_TAC[]]];
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
  [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; IN_UNIV] THEN
   EXISTS_TAC `inf {(f:num->real) k | k >= 0}` THEN
   EXISTS_TAC `0` THEN REFL_TAC;
   REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; IN_UNIV] THEN
    EXISTS_TAC `sup {(f:num->real) k | k >= 0}` THEN
    EXISTS_TAC `0` THEN REFL_TAC;
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]]);;

(* Upper bound from real_limsup (symmetric to REAL_LIMINF_EVENTUALLY_LBOUND) *)
let REAL_LIMSUP_EVENTUALLY_UBOUND = prove
 (`!f b B L.
     (!n. b <= f n) /\ (!n. f n <= B) /\ real_limsup f <= L
     ==> !e. &0 < e ==> ?N. !n. N <= n ==> f n < L + e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `real_limsup (f:num->real) < L + e` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[real_limsup] THEN DISCH_TAC THEN
  (* inf{sup{f k|k>=n}|n} < L + e, so there exists n with sup{f k|k>=n} < L + e *)
  MP_TAC(ISPECL [`{sup {(f:num->real) k | k >= n} | n IN (:num)}`;
                  `L + e:real`] INF_APPROACH) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; IN_UNIV] THEN
    EXISTS_TAC `sup {(f:num->real) k | k >= 0}` THEN
    EXISTS_TAC `0` THEN REFL_TAC;
    EXISTS_TAC `b:real` THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(f:num->real) n` THEN CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     MATCH_MP_TAC REAL_LE_SUP THEN
     EXISTS_TAC `B:real` THEN EXISTS_TAC `(f:num->real) n` THEN
     REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `n:num` THEN
      REWRITE_TAC[GE; LE_REFL];
      REWRITE_TAC[REAL_LE_REFL];
      REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[]]]];
   ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `n:num` THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `s:real` THEN CONJ_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LE_SUP THEN
   EXISTS_TAC `B:real` THEN EXISTS_TAC `(f:num->real) n'` THEN
   REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `n':num` THEN
    ASM_REWRITE_TAC[GE];
    REWRITE_TAC[REAL_LE_REFL];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[]];
   ASM_REWRITE_TAC[]]);;

(* If real_liminf >= L and real_limsup <= L, then f --> L *)
let REAL_LIMINF_LIMSUP_CONVERGES = prove
 (`!f b B L.
     (!n. b <= f n) /\ (!n. f n <= B) /\
     L <= real_liminf f /\ real_limsup f <= L
     ==> (f ---> L) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`f:num->real`; `b:real`; `B:real`; `L:real`]
    REAL_LIMINF_EVENTUALLY_LBOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  MP_TAC(SPECL [`f:num->real`; `b:real`; `B:real`; `L:real`]
    REAL_LIMSUP_EVENTUALLY_UBOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  EXISTS_TAC `MAX N1 N2` THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `N1:num <= m /\ N2 <= m` STRIP_ASSUME_TAC THENL
  [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `L - e < (f:num->real) m` ASSUME_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:num->real) m < L + e` ASSUME_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* If liminf_events A = limsup_events A = E, then P(A_n) --> P(E) *)
let PROB_CONVERGENCE_EVENTS = prove
 (`!p:A prob_space A E.
     (!n. A n IN prob_events p) /\
     liminf_events A = E /\ limsup_events A = E
     ==> ((\n. prob p (A n)) ---> prob p E) sequentially`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL [`\n:num. prob (p:A prob_space) ((A:num->A->bool) n)`;
    `&0`; `&1`; `prob (p:A prob_space) (E:A->bool)`]
    REAL_LIMINF_LIMSUP_CONVERGES) THEN
  BETA_TAC THEN REPEAT CONJ_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[];
   GEN_TAC THEN MATCH_MP_TAC PROB_LE_1 THEN ASM_REWRITE_TAC[];
   MP_TAC(ISPECL [`p:A prob_space`; `A:num->A->bool`]
     FATOU_EVENTS_LIMINF) THEN
   ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
   MP_TAC(ISPECL [`p:A prob_space`; `A:num->A->bool`]
     FATOU_EVENTS_LIMSUP) THEN
   ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* ========================================================================= *)
(* Convergence mode relationships                                            *)
(* ========================================================================= *)

(* limsup of "bad" events is contained in the complement of the
   convergence set *)
let LIMSUP_BAD_SUBSET_COMPL_CONV = prove
 (`!p:A prob_space (X:num->A->real) (L:A->real) e.
     &0 < e ==>
     limsup_events
       (\n. {x:A | x IN prob_carrier p /\ abs(X n x - L x) >= e})
     SUBSET
     prob_carrier p DIFF
       {x | x IN prob_carrier p /\
            ((\n. X n x) ---> L x) sequentially}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIMSUP_EVENTS_ALT; SUBSET; IN_DIFF; IN_ELIM_THM] THEN
  X_GEN_TAC `w:A` THEN DISCH_TAC THEN
  CONJ_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[BETA_THM] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
   UNDISCH_TAC `!m. ?n. n >= m /\ (w:A) IN prob_carrier p /\
     abs((X:num->A->real) n w - (L:A->real) w) >= e` THEN
   DISCH_THEN(MP_TAC o SPEC `N:num`) THEN
   DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `abs((X:num->A->real) n w - (L:A->real) w) < e`
     MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `n:num >= N` THEN REWRITE_TAC[GE];
    ASM_REAL_ARITH_TAC]]);;

(* Almost sure convergence implies convergence in probability *)
let ALMOST_SURE_IMP_IN_PROB = prove
 (`!p:A prob_space (X:num->A->real) (L:A->real).
     (!n:num e. &0 < e ==>
       {x:A | x IN prob_carrier p /\ abs(X n x - L x) >= e}
         IN prob_events p) /\
     {x:A | x IN prob_carrier p /\
            ((\n. X n x) ---> L x) sequentially} IN prob_events p /\
     converges_as p X L
     ==> converges_in_prob p X L`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[converges_as; converges_in_prob] THEN
  STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `B = \n:num.
    {x:A | x IN prob_carrier p /\ abs(X n x - L x) >= e}` THEN
  SUBGOAL_THEN `!n. (B:num->A->bool) n IN prob_events p` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "B" THEN REWRITE_TAC[] THEN
   ASM_SIMP_TAC[];
   ALL_TAC] THEN
  (* D_m = UNIONS{B_n | n >= m} is decreasing *)
  ABBREV_TAC `DD = \m:num. UNIONS {(B:num->A->bool) n | n >= m}` THEN
  SUBGOAL_THEN `!m. (DD:num->A->bool) m IN prob_events p` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "DD" THEN REWRITE_TAC[] THEN
   MATCH_MP_TAC TAIL_UNION_IN_EVENTS THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!m. (DD:num->A->bool) (SUC m) SUBSET DD m` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "DD" THEN REWRITE_TAC[] THEN
   REWRITE_TAC[TAIL_UNION_DECREASING];
   ALL_TAC] THEN
  (* limsup_events B = INTERS{DD_m} *)
  SUBGOAL_THEN `limsup_events (B:num->A->bool) =
    INTERS {DD m | m IN (:num)}` ASSUME_TAC THENL
  [EXPAND_TAC "DD" THEN EXPAND_TAC "B" THEN REWRITE_TAC[limsup_events];
   ALL_TAC] THEN
  (* P(limsup B) = 0 *)
  SUBGOAL_THEN `prob p (limsup_events (B:num->A->bool)) = &0`
    ASSUME_TAC THENL
  [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC PROB_POSITIVE THEN
    MATCH_MP_TAC LIMSUP_EVENTS_IN_EVENTS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* limsup B SUBSET carrier DIFF {convergence set} *)
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `prob p (prob_carrier (p:A prob_space) DIFF
     {x:A | x IN prob_carrier p /\
            ((\n. (X:num->A->real) n x) ---> L x) sequentially})` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC PROB_MONO THEN CONJ_TAC THENL
    [MATCH_MP_TAC LIMSUP_EVENTS_IN_EVENTS THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC PROB_COMPL_IN_EVENTS THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    EXPAND_TAC "B" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC LIMSUP_BAD_SUBSET_COMPL_CONV THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[PROB_COMPL] THEN ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* P(DD_m) --> P(limsup B) via continuity from above *)
  SUBGOAL_THEN
    `((\m. prob p ((DD:num->A->bool) m)) --->
      prob p (limsup_events (B:num->A->bool))) sequentially`
    ASSUME_TAC THENL
  [SUBGOAL_THEN `limsup_events (B:num->A->bool) =
      INTERS {(DD:num->A->bool) m | m IN (:num)}` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC PROB_CONTINUITY_FROM_ABOVE THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* P(DD_m) --> 0 *)
  SUBGOAL_THEN `((\m. prob p ((DD:num->A->bool) m)) ---> &0) sequentially`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  (* Rewrite goal in terms of B *)
  SUBGOAL_THEN `(\n. prob p {x:A | x IN prob_carrier p /\
    abs ((X:num->A->real) n x - (L:A->real) x) >= e}) =
    (\n. prob p ((B:num->A->bool) n))` SUBST1_TAC THENL
  [EXPAND_TAC "B" THEN REWRITE_TAC[];
   ALL_TAC] THEN
  (* Squeeze: 0 <= P(B_n) <= P(DD_n) --> 0 *)
  MATCH_MP_TAC(ISPECL [`\n:num. &0`;
    `\n:num. prob p ((B:num->A->bool) n)`;
    `\m:num. prob p ((DD:num->A->bool) m)`; `&0`]
    REALLIM_TRANSFORM_STRADDLE) THEN BETA_TAC THEN
  REPEAT CONJ_TAC THENL
  [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
   EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN
   MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[REALLIM_CONST];
   REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
   EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN
   MATCH_MP_TAC PROB_MONO THEN ASM_REWRITE_TAC[] THEN
   EXPAND_TAC "DD" THEN REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   EXISTS_TAC `(B:num->A->bool) n` THEN ASM_REWRITE_TAC[] THEN
   EXISTS_TAC `n:num` THEN REWRITE_TAC[GE; LE_REFL];
   ASM_REWRITE_TAC[]]);;

(* L2 convergence implies convergence in probability *)
let L2_IMP_IN_PROB = prove
 (`!p:A prob_space (X:num->A->real) (L:A->real).
     (!n. simple_rv p (X n)) /\ simple_rv p L /\
     converges_L2 p X L
     ==> converges_in_prob p X L`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[converges_L2; converges_in_prob] THEN
  STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  (* P(|X_n - L| >= e) <= E[(X_n - L)^2] / e^2 by Markov *)
  SUBGOAL_THEN `!n. prob p {x:A | x IN prob_carrier p /\
    abs((X:num->A->real) n x - (L:A->real) x) >= e} <=
    simple_expectation p (\x. (X n x - L x) pow 2) / e pow 2`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
     abs((X:num->A->real) n x - (L:A->real) x) >= e} =
     {x | x IN prob_carrier p /\ (X n x - L x) pow 2 >= e pow 2}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `a:A` THEN
    ASM_CASES_TAC `(a:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_ge; GSYM REAL_LE_SQUARE_ABS] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> abs e = e`];
    MATCH_MP_TAC MARKOV_INEQUALITY_SIMPLE THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [MATCH_MP_TAC SIMPLE_RV_SQUARE THEN
     MATCH_MP_TAC SIMPLE_RV_SUB THEN ASM_REWRITE_TAC[ETA_AX];
     CONJ_TAC THENL
     [X_GEN_TAC `a:A` THEN DISCH_TAC THEN REWRITE_TAC[REAL_LE_POW_2];
      ASM_SIMP_TAC[REAL_POW_LT]]]];
   ALL_TAC] THEN
  (* Squeeze: 0 <= P(...) <= E[...]/e^2 --> 0 *)
  MATCH_MP_TAC(ISPECL [`\n:num. &0`;
    `\n:num. prob (p:A prob_space) {x:A | x IN prob_carrier p /\
      abs((X:num->A->real) n x - (L:A->real) x) >= e}`;
    `\n:num. simple_expectation (p:A prob_space)
      (\x:A. ((X:num->A->real) n x - (L:A->real) x) pow 2) / e pow 2`;
    `&0`] REALLIM_TRANSFORM_STRADDLE) THEN BETA_TAC THEN
  REPEAT CONJ_TAC THENL
  [(* 0 <= prob(...) eventually *)
   REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
   X_GEN_TAC `n:num` THEN DISCH_TAC THEN
   MATCH_MP_TAC PROB_POSITIVE THEN
   MATCH_MP_TAC RANDOM_VARIABLE_GE THEN
   SUBGOAL_THEN `simple_rv (p:A prob_space)
     (\x:A. abs((X:num->A->real) n x - (L:A->real) x))` MP_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_ABS THEN
    MATCH_MP_TAC SIMPLE_RV_SUB THEN ASM_REWRITE_TAC[ETA_AX];
    REWRITE_TAC[simple_rv] THEN MESON_TAC[]];
   (* (\n. &0) ---> &0 *)
   REWRITE_TAC[REALLIM_CONST];
   (* prob(...) <= E[...]/e^2 eventually *)
   REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
   (* E[(X_n - L)^2]/e^2 --> 0 *)
   SUBGOAL_THEN `(\n. simple_expectation (p:A prob_space)
     (\x:A. ((X:num->A->real) n x - (L:A->real) x) pow 2) / e pow 2) =
     (\n. inv(e pow 2) * simple_expectation p
       (\x. (X n x - L x) pow 2))`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; real_div; REAL_MUL_SYM]; ALL_TAC] THEN
   SUBGOAL_THEN `&0 = inv(e pow 2) * &0` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_MUL_RZERO]; ALL_TAC] THEN
   MATCH_MP_TAC REALLIM_LMUL THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Abel summation by parts and Kronecker's lemma                             *)
(* ========================================================================= *)

let ABEL_SUMMATION_IDENTITY = prove
  (`!b c n.
      sum (0..SUC n) (\k. b k * c k) =
      b (SUC n) * sum (0..SUC n) c -
      sum (0..n) (\k. sum (0..k) c * (b (SUC k) - b k))`,
   GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `0 <= 0`;
                ARITH_RULE `0 <= SUC 0`] THEN
    REWRITE_TAC[SUM_SING_NUMSEG] THEN
    REAL_ARITH_TAC;
    ONCE_REWRITE_TAC[SUM_CLAUSES_NUMSEG] THEN
    REWRITE_TAC[LE_0] THEN
    FIRST_X_ASSUM SUBST1_TAC THEN
    REAL_ARITH_TAC]);;

let REAL_ABS_TRIANGLE_SUB = REAL_ARITH `!x y. abs(x - y) <= abs x + abs y`;;

let KRONECKER_LEMMA = prove
  (`!a b.
      (!n. &0 < b(n)) /\
      (!n. b(n) <= b(n + 1)) /\
      (!M. ?N. !n. N <= n ==> M <= b(n)) /\
      real_summable (from 0) (\k. a(k) / b(k))
      ==> ((\n. inv(b(n)) * sum(0..n) a) ---> &0) sequentially`,
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   X_GEN_TAC `e:real` THEN DISCH_TAC THEN
   ABBREV_TAC `c = \k:num. (a(k):real) / b(k)` THEN
   ABBREV_TAC `S = real_infsum (from 0) (c:num->real)` THEN
   SUBGOAL_THEN `((\n. sum(0..n) (c:num->real)) ---> S) sequentially`
     ASSUME_TAC THENL
   [UNDISCH_TAC `real_summable (from 0) (c:num->real)` THEN
    UNDISCH_TAC `real_infsum (from 0) (c:num->real) = S` THEN
    REWRITE_TAC[real_summable; real_sums; FROM_0; INTER_UNIV;
                real_infsum] THEN
    MESON_TAC[SELECT_AX];
    ALL_TAC] THEN
   FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
   DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN
   ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
   DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
   SUBGOAL_THEN `!n. ~(b(n:num) = &0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LT_IMP_NZ]; ALL_TAC] THEN
   SUBGOAL_THEN `!k:num. (a(k):real) = b(k) * c(k)` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "c" THEN REWRITE_TAC[] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(b * a) * c = a * (b * c):real`] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_RID];
    ALL_TAC] THEN
   SUBGOAL_THEN `?Cs. !k:num. abs(sum(0..k) (c:num->real)) <= Cs`
     (X_CHOOSE_TAC `Cs:real`) THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
    DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
    DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN
    EXISTS_TAC `sum(0..N0) (\k:num. abs(sum(0..k) (c:num->real))) +
                abs(S:real) + &1` THEN
    X_GEN_TAC `k:num` THEN ASM_CASES_TAC `k:num <= N0` THENL
    [MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= y + abs S + &1`) THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `sum(0..N0)
       (\i:num. if i = k then abs(sum(0..k) (c:num->real)) else &0)` THEN
     CONJ_TAC THENL
     [REWRITE_TAC[SUM_DELTA; IN_NUMSEG] THEN
      ASM_REWRITE_TAC[LE_0; REAL_LE_REFL];
      MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
      BETA_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[REAL_ABS_POS; REAL_LE_REFL]];
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `abs(S:real) + &1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
       `abs(x - S) < &1 ==> abs x <= abs S + &1`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> a + &1 <= y + a + &1`) THEN
      MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[REAL_ABS_POS]]];
    ALL_TAC] THEN
   SUBGOAL_THEN `!k:num. &0 <= b(SUC k) - b(k)` ASSUME_TAC THENL
   [GEN_TAC THEN
    UNDISCH_TAC `!n. b n <= b(n + 1)` THEN
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
    REWRITE_TAC[ADD1] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   ABBREV_TAC `D = (&3 / e) * ((Cs + abs(S:real)) * b(SUC N1) +
                abs S * b(0:num)) + &1` THEN
   UNDISCH_TAC `!M. ?N. !n:num. N <= n ==> M <= b n` THEN
   DISCH_THEN(MP_TAC o SPEC `D:real`) THEN
   DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
   EXISTS_TAC `SUC(MAX N1 N2)` THEN
   X_GEN_TAC `n:num` THEN DISCH_TAC THEN
   SUBGOAL_THEN `?j. n = SUC j /\ N1 <= j /\ N2 <= SUC j`
     (CHOOSE_THEN STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `n - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `sum(0..SUC j) a = sum(0..SUC j) (\k. b(k) * c(k))`
     SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[ABEL_SUMMATION_IDENTITY] THEN
   REWRITE_TAC[REAL_SUB_LDISTRIB] THEN
   SUBGOAL_THEN
     `inv(b(SUC j)) * (b(SUC j) * sum(0..SUC j) (c:num->real)) =
      sum(0..SUC j) c` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_MUL_LID];
    ALL_TAC] THEN
   REWRITE_TAC[REAL_SUB_RZERO] THEN
   MATCH_MP_TAC(REAL_ARITH
     `abs(s - S) < e / &3 /\ abs(S - w) <= &2 * e / &3
      ==> abs(s - w) < e`) THEN
   CONJ_TAC THENL
   [UNDISCH_TAC
      `!n:num. N1 <= n ==> abs(sum(0..n) (c:num->real) - S) < e / &3` THEN
    DISCH_THEN(MP_TAC o SPEC `SUC j`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
   REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN
   SUBGOAL_THEN
     `!j. sum(0..j) (\k. sum(0..k) (c:num->real) * (b(SUC k) - b k)) =
          sum(0..j) (\k. S * (b(SUC k) - b k)) -
          sum(0..j) (\k. (S - sum(0..k) c) * (b(SUC k) - b k))`
     (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
   REWRITE_TAC[SUM_LMUL] THEN
   SUBGOAL_THEN `sum(0..j) (\k. b(SUC k) - b(k:num)) = b(SUC j) - b(0)`
     SUBST1_TAC THENL
   [REWRITE_TAC[ADD1; SUM_DIFFS_ALT; LE_0]; ALL_TAC] THEN
   ABBREV_TAC `R = sum(0..j) (\k. (S - sum(0..k) (c:num->real)) *
                    (b(SUC k) - b(k)))` THEN
   SUBGOAL_THEN `inv(b(SUC j)) * b(SUC j) = &1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_MUL_LINV]; ALL_TAC] THEN
   SUBGOAL_THEN `&0 < inv(b(SUC j))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
   (* Algebraic rearrangement: S - inv(b)*(S*(b-b0) - R) *)
   (* = S - S + S*b0*inv(b) + inv(b)*R = S*b0*inv(b) + inv(b)*R *)
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `abs(S:real) * b(0:num) * inv(b(SUC j)) +
               inv(b(SUC j)) * abs(R:real)` THEN
   CONJ_TAC THENL
   [REWRITE_TAC[REAL_SUB_LDISTRIB] THEN
    SUBGOAL_THEN `inv(b(SUC j)) * ((S:real) * b(SUC j)) = S` SUBST1_TAC THENL
    [ONCE_REWRITE_TAC[REAL_ARITH `a * (s * b) = s * (a * b):real`] THEN
     ASM_REWRITE_TAC[REAL_MUL_RID];
     ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `S - (S - x - y) = x + y:real`] THEN
    MATCH_MP_TAC(REAL_ARITH
      `abs(a + b) <= abs a + abs b /\
       abs a <= sa /\ abs b <= sb
       ==> abs(a + b) <= sa + sb`) THEN
    REWRITE_TAC[REAL_ABS_TRIANGLE] THEN CONJ_TAC THENL
    [REWRITE_TAC[REAL_ABS_MUL] THEN
     ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_LT_INV] THEN
     REAL_ARITH_TAC;
     REWRITE_TAC[REAL_ABS_MUL] THEN
     ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_LT_INV] THEN
     REAL_ARITH_TAC];
    ALL_TAC] THEN
   (* Bound |R| *)
   SUBGOAL_THEN `abs(R:real) <=
       (Cs + abs S) * b(SUC N1) + e / &3 * b(SUC j)` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..j) (\k. abs((S - sum(0..k) (c:num->real)) *
                  (b(SUC k) - b(k:num))))` THEN
    CONJ_TAC THENL [REWRITE_TAC[SUM_ABS_NUMSEG]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    SUBGOAL_THEN `!k:num. abs(b(SUC k) - b k) = b(SUC k) - b k`
      (fun th -> REWRITE_TAC[th]) THENL
    [GEN_TAC THEN REWRITE_TAC[REAL_ABS_REFL] THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    ASM_CASES_TAC `N1 = 0` THENL
    [MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `sum(0..j) (\k. e / &3 * (b(SUC k) - b(k:num)))` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `abs(x - S) < e ==> abs(S - x) <= e`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[SUM_LMUL; ADD1; SUM_DIFFS_ALT; LE_0;
                  REAL_SUB_LDISTRIB] THEN
      MATCH_MP_TAC(REAL_ARITH
        `&0 <= c * b + e * b0
         ==> e * b1 - e * b0 <= c * b + e * b1`) THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= a + b`) THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= a + b`) THEN
        CONJ_TAC THENL
        [MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `abs(sum(0..0) (c:num->real))` THEN
          ASM_REWRITE_TAC[REAL_ABS_POS];
         REWRITE_TAC[REAL_ABS_POS]];
        ASM_SIMP_TAC[REAL_LT_IMP_LE]];
       MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH];
        ASM_SIMP_TAC[REAL_LT_IMP_LE]]]];
     SUBGOAL_THEN `?N1'. N1 = SUC N1'` (X_CHOOSE_TAC `N1':num`) THENL
     [ASM_MESON_TAC[num_CASES]; ALL_TAC] THEN
     SUBGOAL_THEN `(N1':num) < j` ASSUME_TAC THENL
     [UNDISCH_TAC `(N1:num) <= j` THEN
      UNDISCH_TAC `N1 = SUC N1'` THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[LE_SUC_LT];
      ALL_TAC] THEN
     MP_TAC(ISPECL
       [`\k. abs(S - sum(0..k) (c:num->real)) * (b(SUC k) - b(k:num))`;
        `0`; `N1':num`; `j:num`] SUM_COMBINE_R) THEN
     ANTS_TAC THENL
     [CONJ_TAC THENL [REWRITE_TAC[LE_0]; ASM_SIMP_TAC[LT_IMP_LE]];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
     MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum(0..N1')
        (\k. (Cs + abs(S:real)) * (b(SUC k) - b(k:num)))` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
       MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
       MATCH_MP_TAC(REAL_ARITH
         `abs(S - x) <= abs S + abs x /\ abs x <= C
          ==> abs(S - x) <= C + abs S`) THEN
       ASM_REWRITE_TAC[REAL_ABS_TRIANGLE_SUB];
       REWRITE_TAC[SUM_LMUL; ADD1; SUM_DIFFS_ALT; LE_0] THEN
       MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= a + b`) THEN
        CONJ_TAC THENL
        [MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `abs(sum(0..0) (c:num->real))` THEN
          ASM_REWRITE_TAC[REAL_ABS_POS];
         REWRITE_TAC[REAL_ABS_POS]];
        MATCH_MP_TAC(REAL_ARITH
          `&0 < z /\ x <= y ==> x - z <= y`) THEN
        CONJ_TAC THENL
        [ASM_MESON_TAC[];
         UNDISCH_TAC `N1 = SUC N1'` THEN DISCH_THEN SUBST1_TAC THEN
         REWRITE_TAC[ADD1] THEN ASM_MESON_TAC[]]]];
      SUBGOAL_THEN
        `sum(N1' + 1..j)
          (\k. abs(S - sum(0..k) (c:num->real)) * (b(SUC k) - b(k:num)))
         <= sum(N1' + 1..j) (\k. e / &3 * (b(SUC k) - b(k:num)))` MP_TAC THENL
      [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
       MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
       MATCH_MP_TAC(REAL_ARITH `abs(x - S) < e ==> abs(S - x) <= e`) THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
       UNDISCH_TAC `N1 = SUC N1'` THEN DISCH_THEN SUBST1_TAC THEN
       REWRITE_TAC[ADD1] THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
      SUBGOAL_THEN
        `sum(N1' + 1..j) (\k. e / &3 * (b(SUC k) - b(k:num)))
         <= e / &3 * (b:num->real)(SUC j)` MP_TAC THENL
      [REWRITE_TAC[SUM_LMUL] THEN
       SUBGOAL_THEN `sum(N1' + 1..j) (\k. b(SUC k) - b(k:num)) =
                      b(SUC j) - b(N1' + 1)`
         SUBST1_TAC THENL
       [REWRITE_TAC[ADD1; SUM_DIFFS_ALT] THEN
        ASM_SIMP_TAC[ARITH_RULE `m < n ==> m + 1 <= n`];
        MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH; REAL_LT_IMP_LE] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> b - x <= b`) THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE]];
       ALL_TAC] THEN
      REAL_ARITH_TAC]];
    ALL_TAC] THEN
   (* Now bound the total *)
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `abs(S:real) * b(0:num) * inv(b(SUC j)) +
               inv(b(SUC j)) * ((Cs + abs S) * b(SUC N1) +
               e / &3 * b(SUC j))` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
    [REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_LE_LMUL THEN
     ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
   REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
   SUBGOAL_THEN `inv(b(SUC j)) * (e / &3 * b(SUC j)) = e / &3`
     SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[REAL_ARITH `a * (b * c) = b * (a * c):real`] THEN
    ASM_REWRITE_TAC[REAL_MUL_RID];
    ALL_TAC] THEN
   ONCE_REWRITE_TAC[REAL_ADD_ASSOC] THEN
   MATCH_MP_TAC(REAL_ARITH `x < e3 ==> x + e3 <= &2 * e3`) THEN
   SUBGOAL_THEN
     `abs(S:real) * b(0:num) * inv(b(SUC j)) +
      inv(b(SUC j)) * (Cs + abs S) * b(SUC N1) =
      ((Cs + abs S) * b(SUC N1) + abs S * b(0:num)) * inv(b(SUC j))`
     SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(a * b) * c = a * (b * c):real`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
   ABBREV_TAC `X = (Cs + abs(S:real)) * b(SUC N1) + abs S * b(0:num)` THEN
   SUBGOAL_THEN `&0 <= X` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= a + b`) THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_ABS_POS; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= a + b`) THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `abs(sum(0..0) (c:num->real))` THEN
      ASM_REWRITE_TAC[REAL_ABS_POS];
     REWRITE_TAC[REAL_ABS_POS]];
    ALL_TAC] THEN
   SUBGOAL_THEN `D <= b(SUC j)` ASSUME_TAC THENL
   [UNDISCH_TAC `!n:num. N2 <= n ==> D <= b n` THEN
    DISCH_THEN(MP_TAC o SPEC `SUC j`) THEN
    UNDISCH_TAC `N2 <= SUC j` THEN SIMP_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `&0 < D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_OF_NUM_LE; ARITH_RULE `0 <= 3`];
    ALL_TAC] THEN
   MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `X * inv(D:real)` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
   SUBGOAL_THEN `(e / &3) * D = X + e / &3` SUBST1_TAC THENL
   [EXPAND_TAC "D" THEN EXPAND_TAC "X" THEN
    MATCH_MP_TAC(REAL_FIELD `~(e = &0) ==>
      (e / &3) * ((&3 / e) * x + &1) = x + e / &3`) THEN
    ASM_MESON_TAC[REAL_LT_IMP_NZ];
    MATCH_MP_TAC(REAL_ARITH `&0 < t ==> x < x + t`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH]]);;

(* ========================================================================= *)
(* Scheffe's lemma (L1 convergence)                                          *)
(* ========================================================================= *)

let REAL_MIN_REFL = REAL_ARITH `!x. min x x = x`;;

let REALLIM_MIN_CONST = prove
 (`!f L c. (f ---> L) sequentially
           ==> ((\n. min (f n) c) ---> min L c) sequentially`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[real_min] THEN REAL_ARITH_TAC);;

let SIMPLE_RV_UPPER_BOUND = prove
 (`!p:A prob_space f. simple_rv p f ==>
   ?M. !x. x IN prob_carrier p ==> f x <= M`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:A prob_space`; `f:A->real`] SIMPLE_RV_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `M:real` THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `abs x <= M ==> x <= M`) THEN
  ASM_SIMP_TAC[]);;

let NN_EXPECTATION_MIN_LIMIT = prove
 (`!p:A prob_space f.
     (!x. x IN prob_carrier p ==> &0 <= f x) /\
     integrable p f
     ==> ((\n. nn_expectation p (\x. min (f x) (&n))) --->
          nn_expectation p f) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!m n. m <= n ==>
    nn_expectation (p:A prob_space) (\x:A. min ((f:A->real) x) (&m)) <=
    nn_expectation p (\x. min (f x) (&n))` ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC BOUNDED_NN_EXPECTATION_MONO THEN
   BETA_TAC THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= min a b`) THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= min a b`) THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> min x a <= min x b`) THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    EXISTS_TAC `&n` THEN GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n. nn_expectation (p:A prob_space) (\x:A. min ((f:A->real) x) (&n)) <=
                    nn_expectation p f` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC NN_EXPECTATION_MONO THEN
   BETA_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= min a b`) THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC]; ALL_TAC] THEN
  MP_TAC(SPECL [`p:A prob_space`; `f:A->real`] INTEGRABLE_NONNEG_NN_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `Bf:real`) THEN
  SUBGOAL_THEN `nn_expectation (p:A prob_space) (f:A->real) - e <
    nn_expectation p f` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`{simple_expectation (p:A prob_space) g | g |
     simple_rv p g /\ (!x:A. x IN prob_carrier p ==> &0 <= g x) /\
     (!x. x IN prob_carrier p ==> g x <= (f:A->real) x)}`;
     `nn_expectation (p:A prob_space) (f:A->real) - e`] SUP_APPROACH) THEN
  REWRITE_TAC[GSYM nn_expectation] THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [MATCH_MP_TAC NN_EXPECT_SET_NONEMPTY THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   CONJ_TAC THENL
   [EXISTS_TAC `Bf:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `h:A->real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:A->real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`p:A prob_space`; `g:A->real`] SIMPLE_RV_UPPER_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `Mg:real`) THEN
  MP_TAC(SPEC `Mg:real` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `simple_expectation (p:A prob_space) (g:A->real) <=
    nn_expectation p (\x:A. min ((f:A->real) x) (&n))` ASSUME_TAC THENL
  [MATCH_MP_TAC BOUNDED_NN_EXPECTATION_GE_SIMPLE THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_LE_MIN] THEN CONJ_TAC THENL
    [ASM_SIMP_TAC[];
     MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Mg:real` THEN
     ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `&N` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]];
    EXISTS_TAC `&n` THEN GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  UNDISCH_TAC `v = simple_expectation (p:A prob_space) (g:A->real)` THEN
  ASM_REAL_ARITH_TAC);;

let EXPECTATION_NONNEG_EQ_NN = prove
 (`!p:A prob_space (f:A->real).
    integrable p f /\
    (!x. x IN prob_carrier p ==> &0 <= f x)
    ==> expectation p f = nn_expectation p f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[expectation] THEN
  SUBGOAL_THEN `nn_expectation (p:A prob_space) (\x. max ((f:A->real) x) (&0)) =
    nn_expectation p f` SUBST1_TAC THENL
  [MATCH_MP_TAC NN_EXPECTATION_EXT THEN GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= f ==> max f (&0) = f`) THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `nn_expectation (p:A prob_space) (\x. max (--((f:A->real) x)) (&0)) = &0`
    (fun th -> REWRITE_TAC[th; REAL_SUB_RZERO]) THEN
  SUBGOAL_THEN `nn_expectation (p:A prob_space) (\x. max (--((f:A->real) x)) (&0)) =
    nn_expectation p (\x:A. &0)` SUBST1_TAC THENL
  [MATCH_MP_TAC NN_EXPECTATION_EXT THEN GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= f ==> max (--f) (&0) = &0`) THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `(\x:A. &0):A->real`] NN_EXPECTATION_SIMPLE) THEN
  REWRITE_TAC[SIMPLE_RV_CONST; REAL_LE_REFL; SIMPLE_EXPECTATION_CONST]);;

let SCHEFFE_LEMMA = prove
 (`!p:A prob_space X f.
    (!n. integrable p (X n)) /\
    integrable p f /\
    (!n x. x IN prob_carrier p ==> &0 <= X n x) /\
    (!x. x IN prob_carrier p ==> &0 <= f x) /\
    (!x. x IN prob_carrier p ==> ((\n. X n x) ---> f x) sequentially) /\
    ((\n. nn_expectation p (X n)) ---> nn_expectation p f) sequentially
    ==> ((\n. nn_expectation p (\x. abs(X n x - f x))) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  (* Integrability of min(X_n, f) *)
  SUBGOAL_THEN
    `!n:num. integrable (p:A prob_space)
               (\x. min ((X:num->A->real) n x) ((f:A->real) x))`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_DOMINATED THEN
   EXISTS_TAC `(f:A->real)` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
    CONJ_TAC THEN REWRITE_TAC[ETA_AX] THENL
    [UNDISCH_TAC `!n. integrable (p:A prob_space) ((X:num->A->real) n)` THEN
     DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
     REWRITE_TAC[integrable] THEN STRIP_TAC;
     UNDISCH_TAC `integrable (p:A prob_space) (f:A->real)` THEN
     REWRITE_TAC[integrable] THEN STRIP_TAC];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= (X:num->A->real) n x /\ &0 <= (f:A->real) x`
      MP_TAC THENL
    [ASM_MESON_TAC[]; REWRITE_TAC[real_min] THEN REAL_ARITH_TAC]];
   ALL_TAC] THEN
  (* Algebraic identity via signed expectation linearity *)
  SUBGOAL_THEN
    `!n:num. nn_expectation (p:A prob_space)
               (\x. abs((X:num->A->real) n x - (f:A->real) x)) =
             nn_expectation p (X n) + nn_expectation p f -
             &2 * nn_expectation p (\x. min (X n x) (f x))`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   SUBGOAL_THEN
     `integrable (p:A prob_space)
        (\x. abs((X:num->A->real) n x - (f:A->real) x))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_DOMINATED THEN
    EXISTS_TAC `\x:A. abs((X:num->A->real) n x) + abs((f:A->real) x)` THEN
    REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN
     UNDISCH_TAC `!n. integrable (p:A prob_space) ((X:num->A->real) n)` THEN
     DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
     UNDISCH_TAC `integrable (p:A prob_space) (f:A->real)` THEN
     REWRITE_TAC[integrable] THEN REPEAT STRIP_TAC THEN
     MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THEN
     MATCH_MP_TAC INTEGRABLE_ABS THEN
     ASM_REWRITE_TAC[] THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `!x:A. x IN prob_carrier p
            ==> &0 <= min ((X:num->A->real) n x) ((f:A->real) x)`
     ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_MIN] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
   ASM_SIMP_TAC[GSYM EXPECTATION_NONNEG_EQ_NN; REAL_ABS_POS] THEN
   SUBGOAL_THEN
     `expectation (p:A prob_space)
        (\x. abs((X:num->A->real) n x - (f:A->real) x)) =
      expectation p (\x. (X n x + f x) - &2 * min (X n x) (f x))`
     SUBST1_TAC THENL
   [MATCH_MP_TAC EXPECTATION_EXT THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= (X:num->A->real) n x /\ &0 <= (f:A->real) x`
      MP_TAC THENL
    [ASM_MESON_TAC[]; REWRITE_TAC[real_min] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `integrable (p:A prob_space)
        (\x. &2 * min ((X:num->A->real) n x) ((f:A->real) x))`
     ASSUME_TAC THENL
   [SUBGOAL_THEN
      `(\x. &2 * min ((X:num->A->real) n x) ((f:A->real) x)) =
       (\x. min (X n x) (f x) + min (X n x) (f x))`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC;
     MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `integrable (p:A prob_space)
        (\x. (X:num->A->real) n x + (f:A->real) x)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   ASM_SIMP_TAC[EXPECTATION_SUB] THEN
   ASM_SIMP_TAC[EXPECTATION_ADD; ETA_AX] THEN
   ASM_SIMP_TAC[EXPECTATION_CMUL] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* Extract random_variable facts from integrable *)
  SUBGOAL_THEN
    `random_variable (p:A prob_space) (f:A->real) /\
     (!n:num. random_variable p ((X:num->A->real) n))`
    STRIP_ASSUME_TAC THENL
  [CONJ_TAC THENL
   [UNDISCH_TAC `integrable (p:A prob_space) (f:A->real)` THEN
    REWRITE_TAC[integrable] THEN STRIP_TAC;
    GEN_TAC THEN
    UNDISCH_TAC `!n:num. integrable (p:A prob_space) ((X:num->A->real) n)` THEN
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[integrable] THEN STRIP_TAC];
   ALL_TAC] THEN
  (* Get M from truncation convergence *)
  MP_TAC(ISPECL [`p:A prob_space`; `f:A->real`] NN_EXPECTATION_MIN_LIMIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &6`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
  (* Get N1 from bounded convergence for min(min(X_n, f), &M) *)
  MP_TAC(ISPECL
   [`p:A prob_space`;
    `\n:num. \(x:A). min (min ((X:num->A->real) n x) ((f:A->real) x)) (&M)`;
    `\(x:A). min ((f:A->real) x) (&M)`;
    `&M`] BOUNDED_CONVERGENCE_NN) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
  [REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
    REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN
    MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN REWRITE_TAC[ETA_AX] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
    REWRITE_TAC[RANDOM_VARIABLE_CONST; ETA_AX] THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_LE_MIN; REAL_OF_NUM_LE; LE_0] THEN ASM_MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_LE_MIN; REAL_OF_NUM_LE; LE_0] THEN ASM_MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_MIN_LE] THEN DISJ2_TAC THEN REAL_ARITH_TAC;
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_MIN_LE] THEN DISJ2_TAC THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL
     [`\n:num. min ((X:num->A->real) n (x:A)) ((f:A->real) x)`;
      `min ((f:A->real) (x:A)) (f x)`; `&M`] REALLIM_MIN_CONST) THEN
    REWRITE_TAC[REAL_MIN_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL
     [`\n:num. (X:num->A->real) n (x:A)`;
      `(f:A->real) (x:A)`; `(f:A->real) (x:A)`] REALLIM_MIN_CONST) THEN
    REWRITE_TAC[REAL_MIN_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[]];
   ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &6`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  (* Get N2 from E[X_n] -> E[f] *)
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  (* Combine: N = max(N1, N2) *)
  EXISTS_TAC `MAX N1 N2` THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  (* Monotonicity: nn_exp(min(X_n, f)) <= nn_exp(f) *)
  SUBGOAL_THEN
    `nn_expectation (p:A prob_space)
       (\x. min ((X:num->A->real) n x) ((f:A->real) x)) <=
     nn_expectation p f`
    ASSUME_TAC THENL
  [MATCH_MP_TAC NN_EXPECTATION_MONO THEN REWRITE_TAC[] THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_MIN] THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_MIN_LE] THEN DISJ2_TAC THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* Monotonicity: nn_exp(min(min(X_n,f),&M)) <= nn_exp(min(X_n,f)) *)
  SUBGOAL_THEN
    `nn_expectation (p:A prob_space)
       (\x. min (min ((X:num->A->real) n x) ((f:A->real) x)) (&M)) <=
     nn_expectation p (\x. min (X n x) (f x))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC NN_EXPECTATION_MONO THEN REWRITE_TAC[] THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_MIN; REAL_OF_NUM_LE; LE_0] THEN
    ASM_MESON_TAC[];
    CONJ_TAC THENL
    [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_MIN] THEN ASM_MESON_TAC[];
     REPEAT STRIP_TAC THEN
     REWRITE_TAC[REAL_MIN_LE] THEN DISJ1_TAC THEN REAL_ARITH_TAC]];
   ALL_TAC] THEN
  (* Instantiate all epsilon bounds *)
  SUBGOAL_THEN `N1 <= (n:num) /\ N2 <= n` STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `MAX N1 N2 <= n` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  UNDISCH_TAC
    `!n. M <= n ==>
         abs(nn_expectation (p:A prob_space)
               (\x. min ((f:A->real) x) (&n)) -
             nn_expectation p f) < e / &6` THEN
  DISCH_THEN(MP_TAC o SPEC `M:num`) THEN REWRITE_TAC[LE_REFL] THEN
  DISCH_TAC THEN
  (* Final arithmetic *)
  UNDISCH_TAC
    `nn_expectation (p:A prob_space)
       (\x. min ((X:num->A->real) n x) ((f:A->real) x)) <=
     nn_expectation p f` THEN
  UNDISCH_TAC
    `nn_expectation (p:A prob_space)
       (\x. min (min ((X:num->A->real) n x) ((f:A->real) x)) (&M)) <=
     nn_expectation p (\x. min (X n x) (f x))` THEN
  UNDISCH_TAC
    `abs(nn_expectation (p:A prob_space) ((X:num->A->real) n) -
         nn_expectation p (f:A->real)) < e / &3` THEN
  UNDISCH_TAC
    `abs(nn_expectation (p:A prob_space)
           (\x. min (min ((X:num->A->real) n x) ((f:A->real) x)) (&M)) -
         nn_expectation p (\x. min (f x) (&M))) < e / &6` THEN
  UNDISCH_TAC
    `abs(nn_expectation (p:A prob_space)
           (\x. min ((f:A->real) x) (&M)) -
         nn_expectation p f) < e / &6` THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Dominated convergence theorem                                             *)
(* ========================================================================= *)

let INTEGRABLE_MAX = prove
 (`!p:A prob_space f g.
    integrable p f /\ integrable p g
    ==> integrable p (\x. max (f x) (g x))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRABLE_DOMINATED THEN
  EXISTS_TAC `\x:A. abs((f:A->real) x) + abs((g:A->real) x)` THEN
  REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN ASM_MESON_TAC[integrable];
   MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_SIMP_TAC[INTEGRABLE_ABS];
   REWRITE_TAC[real_max] THEN REAL_ARITH_TAC]);;

let INTEGRABLE_MIN = prove
 (`!p:A prob_space f g.
    integrable p f /\ integrable p g
    ==> integrable p (\x. min (f x) (g x))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRABLE_DOMINATED THEN
  EXISTS_TAC `\x:A. abs((f:A->real) x) + abs((g:A->real) x)` THEN
  REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN ASM_MESON_TAC[integrable];
   MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_SIMP_TAC[INTEGRABLE_ABS];
   REWRITE_TAC[real_min] THEN REAL_ARITH_TAC]);;

(* Probability of tail events for pointwise convergent bounded sequences *)
let PROB_POINTWISE_TAIL_VANISHES = prove
 (`!p:A prob_space (f:num->A->real) (g:A->real) M d.
    (!n. random_variable p (f n)) /\
    random_variable p g /\
    (!n x. x IN prob_carrier p ==> abs(f n x) <= M) /\
    (!x. x IN prob_carrier p ==> abs(g x) <= M) /\
    (!x. x IN prob_carrier p ==> ((\n. f n x) ---> g x) sequentially) /\
    &0 < d
    ==> ((\n. prob p {x | x IN prob_carrier p /\ abs(f n x - g x) >= d})
         ---> &0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n:num. prob (p:A prob_space)
    (UNIONS (IMAGE (\k. {x:A | x IN prob_carrier p /\
       abs((f:num->A->real) k x - (g:A->real) x) >= d}) {k:num | n <= k}))` THEN
  CONJ_TAC THENL
  [(* Eventually bound: abs(prob S_n) <= prob B_n *)
   REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
   X_GEN_TAC `n:num` THEN DISCH_TAC THEN BETA_TAC THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\
        abs((f:num->A->real) n x - (g:A->real) x) >= d}
      IN prob_events (p:A prob_space)` ASSUME_TAC THENL
   [MATCH_MP_TAC RV_LEVEL_GE_IN_EVENTS THEN
    MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN
    MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `UNIONS (IMAGE (\k. {x:A | x IN prob_carrier p /\
        abs((f:num->A->real) k x - (g:A->real) x) >= d})
      {k:num | n <= k}) IN prob_events (p:A prob_space)` ASSUME_TAC THENL
   [MATCH_MP_TAC PROB_COUNTABLE_UNION_IN_EVENTS THEN CONJ_TAC THENL
    [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
     X_GEN_TAC `k:num` THEN DISCH_TAC THEN
     MATCH_MP_TAC RV_LEVEL_GE_IN_EVENTS THEN
     MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN
     MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX];
     MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[COUNTABLE_SUBSET_NUM]];
    ALL_TAC] THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC PROB_MONO THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[SUBSET; IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN
   X_GEN_TAC `y:A` THEN STRIP_TAC THEN
   EXISTS_TAC `{x:A | x IN prob_carrier p /\
     abs((f:num->A->real) n x - (g:A->real) x) >= d}` THEN
   CONJ_TAC THENL
   [EXISTS_TAC `n:num` THEN REWRITE_TAC[LE_REFL] THEN SET_TAC[];
    ASM_REWRITE_TAC[IN_ELIM_THM]];
   ALL_TAC] THEN
  (* Limit: prob(B_n) --> 0 *)
  ABBREV_TAC `B = \n:num. UNIONS (IMAGE (\k. {x:A | x IN prob_carrier p /\
    abs((f:num->A->real) k x - (g:A->real) x) >= d}) {k:num | n <= k})` THEN
  SUBGOAL_THEN `(\n. prob (p:A prob_space)
    (UNIONS (IMAGE (\k. {x:A | x IN prob_carrier p /\
       abs((f:num->A->real) k x - (g:A->real) x) >= d})
     {k:num | n <= k}))) = (\n. prob p (B n))` SUBST1_TAC THENL
  [ASM_REWRITE_TAC[FUN_EQ_THM] THEN
   POP_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN
   BETA_TAC THEN REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n. (B:num->A->bool) n IN prob_events (p:A prob_space)`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN BETA_TAC THEN
   MATCH_MP_TAC PROB_COUNTABLE_UNION_IN_EVENTS THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC RV_LEVEL_GE_IN_EVENTS THEN
    MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN
    MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX];
    MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[COUNTABLE_SUBSET_NUM]];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n. (B:num->A->bool) (SUC n) SUBSET B n` ASSUME_TAC THENL
  [GEN_TAC THEN
   SUBGOAL_THEN `(B:num->A->bool) n = UNIONS (IMAGE (\k. {x:A | x IN
     prob_carrier p /\ abs((f:num->A->real) k x - (g:A->real) x) >= d})
     {k:num | n <= k})` SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `(B:num->A->bool) (SUC n) = UNIONS (IMAGE (\k. {x:A | x IN
     prob_carrier p /\ abs((f:num->A->real) k x - (g:A->real) x) >= d})
     {k:num | SUC n <= k})` SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC SUBSET_UNIONS THEN MATCH_MP_TAC IMAGE_SUBSET THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ARITH_TAC;
   ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `B:num->A->bool`]
    PROB_CONTINUITY_FROM_ABOVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `INTERS {(B:num->A->bool) n | n IN (:num)} = {}`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
  [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN X_GEN_TAC `y:A` THEN
   REWRITE_TAC[IN_INTERS] THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
   DISCH_TAC THEN
   SUBGOAL_THEN `(y:A) IN prob_carrier (p:A prob_space)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `(B:num->A->bool) 0`]
      PROB_EVENT_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(B:num->A->bool) 0`) THEN
    ANTS_TAC THENL [EXISTS_TAC `0` THEN REFL_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `((\n. (f:num->A->real) n (y:A)) ---> (g:A->real) y) sequentially`
     MP_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   DISCH_THEN(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `(B:num->A->bool) N`) THEN
   ANTS_TAC THENL [EXISTS_TAC `N:num` THEN REFL_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `(B:num->A->bool) N = UNIONS (IMAGE (\k. {x:A | x IN
     prob_carrier p /\ abs((f:num->A->real) k x - (g:A->real) x) >= d})
     {k:num | N <= k})` SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN
   DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_ELIM_THM]) THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `x:num`) THEN ASM_REWRITE_TAC[] THEN
   ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PROB_EMPTY]) THEN ASM_REWRITE_TAC[]);;

(* Bounded convergence theorem for expectations *)
let BOUNDED_CONVERGENCE_EXPECTATION = prove
 (`!p:A prob_space (f:num->A->real) (g:A->real) M.
    (!n. random_variable p (f n)) /\
    random_variable p g /\
    (!n x. x IN prob_carrier p ==> abs(f n x) <= M) /\
    (!x. x IN prob_carrier p ==> abs(g x) <= M) /\
    (!x. x IN prob_carrier p ==> ((\n. f n x) ---> g x) sequentially)
    ==> ((\n. expectation p (f n)) ---> expectation p g) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `f:num->A->real`; `g:A->real`;
    `M:real`; `e / &2`] PROB_POINTWISE_TAIL_VANISHES) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / (&4 * abs M + &2)`) THEN
  SUBGOAL_THEN `&0 < e / (&4 * abs M + &2)` (fun th -> REWRITE_TAC[th]) THENL
  [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &4 * x + &2`) THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  (* Establish integrability *)
  SUBGOAL_THEN `integrable (p:A prob_space) ((f:num->A->real) n)` ASSUME_TAC
    THENL
  [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `M:real` THEN
   ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (g:A->real)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `M:real` THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Rewrite E[f_n] - E[g] = E[f_n - g] *)
  SUBGOAL_THEN `expectation (p:A prob_space) ((f:num->A->real) n) -
    expectation p (g:A->real) = expectation p (\x. f n x - g x)`
    SUBST1_TAC THENL
  [ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `(f:num->A->real) n`; `g:A->real`]
     EXPECTATION_SUB) THEN ASM_REWRITE_TAC[] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* |E[f_n - g]| <= E[|f_n - g|] *)
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `expectation (p:A prob_space)
    (\x:A. abs((f:num->A->real) n x - (g:A->real) x))` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC EXPECTATION_ABS_BOUND THEN
   MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX];
   ALL_TAC] THEN
  (* E[|f_n - g|] <= e/2 + 2|M| * P(S_n) *)
  ABBREV_TAC `S_n = {x:A | x IN prob_carrier p /\
    abs((f:num->A->real) n x - (g:A->real) x) >= e / &2}` THEN
  SUBGOAL_THEN `S_n IN prob_events (p:A prob_space)` ASSUME_TAC THENL
  [EXPAND_TAC "S_n" THEN MATCH_MP_TAC RV_LEVEL_GE_IN_EVENTS THEN
   MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN
   MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX];
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `e / &2 + &2 * abs M *
    prob (p:A prob_space) (S_n:A->bool)` THEN
  CONJ_TAC THENL
  [(* E[|f_n - g|] <= e/2 + 2|M| * P(S_n) via EXPECTATION_MONO *)
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `expectation (p:A prob_space) (\x:A. e / &2 +
     &2 * abs M * indicator_fn S_n x)` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC EXPECTATION_MONO THEN CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_ABS THEN
     MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX];
     ALL_TAC] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
     EXISTS_TAC `e / &2 + &2 * abs M` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN CONJ_TAC THENL
      [REWRITE_TAC[RANDOM_VARIABLE_CONST];
       MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN
       SUBGOAL_THEN `simple_rv (p:A prob_space) (indicator_fn S_n)` MP_TAC
         THENL
       [MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[];
        SIMP_TAC[simple_rv]] THEN
       STRIP_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN
       REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `z:A` THEN DISCH_TAC THEN
      REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THENL
      [REWRITE_TAC[REAL_MUL_RID] THEN
       MATCH_MP_TAC(REAL_ARITH `&0 < e /\ &0 <= m
         ==> abs(e / &2 + &2 * m) <= e / &2 + &2 * m`) THEN
       ASM_REWRITE_TAC[REAL_ABS_POS];
       REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN
       MATCH_MP_TAC(REAL_ARITH `&0 < e /\ &0 <= m
         ==> abs(e / &2) <= e / &2 + &2 * m`) THEN
       ASM_REWRITE_TAC[REAL_ABS_POS]]];
     X_GEN_TAC `z:A` THEN DISCH_TAC THEN BETA_TAC THEN
     REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THENL
     [REWRITE_TAC[REAL_MUL_RID] THEN
      MATCH_MP_TAC(REAL_ARITH
        `abs a <= M /\ abs b <= M /\ &0 < e
         ==> abs(a - b) <= e / &2 + &2 * abs M`) THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN
      MATCH_MP_TAC(REAL_ARITH `x < e / &2 ==> x <= e / &2`) THEN
      FIRST_X_ASSUM(fun th -> MP_TAC(REWRITE_RULE[] th)) THEN
      EXPAND_TAC "S_n" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]];
    (* Compute E[e/2 + 2|M| * indicator] = e/2 + 2|M| * P(S_n) *)
    SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. e / &2 +
      &2 * abs M * indicator_fn S_n x) =
      e / &2 + &2 * abs M * prob p S_n`
      (fun th -> REWRITE_TAC[th; REAL_LE_REFL]) THEN
    SUBGOAL_THEN `integrable (p:A prob_space) (indicator_fn S_n)`
      ASSUME_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MP_TAC(ISPECL [`p:A prob_space`; `\x:A. e / &2`;
      `\x:A. (&2 * abs M) * indicator_fn S_n x`]
      EXPECTATION_ADD) THEN
    REWRITE_TAC[INTEGRABLE_CONST; EXPECTATION_CONST] THEN
    ANTS_TAC THENL
    [MP_TAC(ISPECL [`p:A prob_space`; `&2 * abs M`;
       `indicator_fn (S_n:A->bool)`] INTEGRABLE_CMUL) THEN
     ASM_REWRITE_TAC[];
     DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
     MP_TAC(ISPECL [`p:A prob_space`; `&2 * abs M`;
       `indicator_fn (S_n:A->bool)`] EXPECTATION_CMUL) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
     AP_TERM_TAC THEN
     MATCH_MP_TAC EXPECTATION_INDICATOR THEN ASM_REWRITE_TAC[]]];
   ALL_TAC] THEN
  (* e/2 + 2|M| * P(S_n) < e *)
  MATCH_MP_TAC(REAL_ARITH `x < e / &2 ==> e / &2 + x < e`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= prob (p:A prob_space) (S_n:A->bool)` ASSUME_TAC THENL
  [MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &4 * abs M + &2` ASSUME_TAC THENL
  [MATCH_MP_TAC(REAL_ARITH `&0 <= m ==> &0 < &4 * m + &2`) THEN
   REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `prob (p:A prob_space) (S_n:A->bool) < e / (&4 * abs M + &2)`
    ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `prob (p:A prob_space) (S_n:A->bool) * (&4 * abs M + &2) < e`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`prob (p:A prob_space) (S_n:A->bool)`;
     `e / (&4 * abs M + &2)`; `&4 * abs M + &2`] REAL_LT_RMUL) THEN
   ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  ABBREV_TAC `Q = abs M * prob (p:A prob_space) (S_n:A->bool)` THEN
  SUBGOAL_THEN `&4 * Q + &2 * prob (p:A prob_space) (S_n:A->bool) < e`
    ASSUME_TAC THENL
  [EXPAND_TAC "Q" THEN
   SUBGOAL_THEN `&4 * abs M * prob (p:A prob_space) (S_n:A->bool) +
     &2 * prob p S_n =
     prob p S_n * (&4 * abs M + &2)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
   ASM_REAL_ARITH_TAC]);;

(* Dominated Convergence Theorem for non-negative sequences converging to 0.
   If 0 <= f_n <= h pointwise, h integrable, and f_n -> 0, then E[f_n] -> 0. *)
let DOMINATED_CONVERGENCE_NULL = prove
 (`!p:A prob_space (f:num->A->real) h.
     (!n. random_variable p (f n)) /\
     random_variable p h /\
     integrable p h /\
     (!n x. x IN prob_carrier p ==> &0 <= f n x /\ f n x <= h x) /\
     (!x. x IN prob_carrier p ==> ((\n. f n x) ---> &0) sequentially)
     ==> ((\n. expectation p (f n)) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN
  DISCH_TAC THEN
  (* Step 1: h >= 0 *)
  SUBGOAL_THEN `!x:A. x IN prob_carrier p ==> &0 <= h x` ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(f:num->A->real) 0 x` THEN
   ASM_SIMP_TAC[];
   ALL_TAC] THEN
  (* Step 2: By NN_EXPECTATION_MIN_LIMIT, choose K so E[h]-E[min(h,K)] < e/2 *)
  MP_TAC(ISPECL [`p:A prob_space`; `h:A->real`] NN_EXPECTATION_MIN_LIMIT) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `K0:num` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `K = &K0` THEN
  SUBGOAL_THEN `&0 <= K` ASSUME_TAC THENL
  [EXPAND_TAC "K" THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  (* Step 3: E[min(h,K)] close to E[h] = nn_exp(h) *)
  SUBGOAL_THEN `nn_expectation (p:A prob_space) h - e / &2 <
    nn_expectation p (\x. min (h x) K)` ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `K0:num`) THEN
   REWRITE_TAC[LE_REFL] THEN EXPAND_TAC "K" THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Step 4: E[h] - E[min(h,K)] < e/2, rewrite in terms of expectation *)
  SUBGOAL_THEN `expectation (p:A prob_space) h =
    nn_expectation p h` ASSUME_TAC THENL
  [MATCH_MP_TAC EXPECTATION_NONNEG_EQ_NN THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* f n is integrable (dominated by h) *)
  SUBGOAL_THEN `!n. integrable (p:A prob_space) ((f:num->A->real) n)`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_DOMINATED THEN
   EXISTS_TAC `h:A->real` THEN ASM_REWRITE_TAC[] THEN
   GEN_TAC THEN DISCH_TAC THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= abs y`) THEN
   ASM_SIMP_TAC[];
   ALL_TAC] THEN
  (* Step 5: Define g_n = min(f_n, K), bounded by K *)
  (* g_n -> 0 pointwise, |g_n| <= K *)
  (* By BCT: E[g_n] -> 0 *)
  MP_TAC(ISPECL [`p:A prob_space`;
    `\n (x:A). min ((f:num->A->real) n x) K`;
    `\x:A. &0`;
    `K:real`] BOUNDED_CONVERGENCE_EXPECTATION) THEN
  BETA_TAC THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THENL
   [(* random_variable p (min(f n, K)) *)
    GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
    ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST; ETA_AX];
    (* random_variable p 0 *)
    REWRITE_TAC[RANDOM_VARIABLE_CONST];
    (* |min(f n x, K)| <= K *)
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
      `&0 <= a /\ &0 <= K ==> abs(min a K) <= K`) THEN
    ASM_SIMP_TAC[] THEN EXPAND_TAC "K" THEN REWRITE_TAC[REAL_POS];
    (* |0| <= K *)
    REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_NUM] THEN
    EXPAND_TAC "K" THEN REWRITE_TAC[REAL_POS];
    (* min(f n x, K) -> 0 pointwise *)
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 = min (&0) (K:real)` SUBST1_TAC THENL
    [REWRITE_TAC[real_min] THEN
     COND_CASES_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REALLIM_MIN THEN
    ASM_SIMP_TAC[REALLIM_CONST]];
   ALL_TAC] THEN
  REWRITE_TAC[EXPECTATION_CONST; REAL_SUB_RZERO] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  (* Step 6: Bound E[f_n] by E[min(f_n,K)] + tail bound *)
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  (* E[f_n] >= 0 since f_n >= 0 *)
  SUBGOAL_THEN `&0 <= expectation (p:A prob_space) ((f:num->A->real) n)`
    ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 = expectation (p:A prob_space) (\x:A. &0)` SUBST1_TAC THENL
   [REWRITE_TAC[EXPECTATION_CONST]; ALL_TAC] THEN
   MATCH_MP_TAC EXPECTATION_MONO THEN
   ASM_REWRITE_TAC[INTEGRABLE_CONST] THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  (* |E[min(f_n, K)]| < e/2 from BCT *)
  SUBGOAL_THEN `abs(expectation (p:A prob_space)
    (\x:A. min ((f:num->A->real) n x) K)) < e / &2` ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[REAL_SUB_RZERO];
   ALL_TAC] THEN
  (* min(f_n,K) is integrable *)
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. min ((f:num->A->real) n x) K)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_DOMINATED THEN EXISTS_TAC `h:A->real` THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
    ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST; ETA_AX]; ALL_TAC] THEN
   GEN_TAC THEN DISCH_TAC THEN
   MATCH_MP_TAC(REAL_ARITH
     `&0 <= a /\ a <= h /\ &0 <= h /\ &0 <= K ==> abs(min a K) <= abs h`) THEN
   ASM_SIMP_TAC[];
   ALL_TAC] THEN
  (* min(h,K) is integrable *)
  SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. min ((h:A->real) x) K)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_DOMINATED THEN EXISTS_TAC `h:A->real` THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
    ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST; ETA_AX]; ALL_TAC] THEN
   GEN_TAC THEN DISCH_TAC THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= h /\ &0 <= K ==> abs(min h K) <= abs h`) THEN
   ASM_SIMP_TAC[];
   ALL_TAC] THEN
  (* E[f_n] - E[min(f_n,K)] = E[f_n - min(f_n,K)] via EXPECTATION_SUB *)
  MP_TAC(ISPECL [`p:A prob_space`; `(f:num->A->real) n`;
    `(\x:A. min ((f:num->A->real) n x) K)`] EXPECTATION_SUB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN BETA_TAC THEN
  DISCH_TAC THEN
  (* E[f_n - min(f_n,K)] <= E[h - min(h,K)] by monotonicity *)
  SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. (f:num->A->real) n x - min (f n x) K) <=
    expectation p (\x. h x - min (h x) K)` ASSUME_TAC THENL
  [MATCH_MP_TAC EXPECTATION_MONO THEN BETA_TAC THEN
   REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX];
    MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX];
    GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
      `a <= h ==> a - min a K <= h - min h K`) THEN
    ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  (* E[h - min(h,K)] = E[h] - E[min(h,K)] *)
  MP_TAC(ISPECL [`p:A prob_space`; `h:A->real`;
    `(\x:A. min ((h:A->real) x) K)`] EXPECTATION_SUB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN BETA_TAC THEN
  DISCH_TAC THEN
  (* E[min(h,K)] = nn_E[min(h,K)] *)
  SUBGOAL_THEN `expectation (p:A prob_space) (\x:A. min (h x) K) =
    nn_expectation p (\x. min (h x) K)` ASSUME_TAC THENL
  [MATCH_MP_TAC EXPECTATION_NONNEG_EQ_NN THEN
   ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= h /\ &0 <= K ==> &0 <= min h K`) THEN
   ASM_SIMP_TAC[];
   ALL_TAC] THEN
  (* E[h] - E[min(h,K)] < e/2 *)
  SUBGOAL_THEN `expectation (p:A prob_space) h -
    expectation p (\x:A. min (h x) K) < e / &2` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let DOMINATED_CONVERGENCE = prove
 (`!p:A prob_space X f g.
    (!n. integrable p (X n)) /\
    integrable p g /\
    (!n x. x IN prob_carrier p ==> abs(X n x) <= g x) /\
    (!x. x IN prob_carrier p ==> ((\n. X n x) ---> f x) sequentially)
    ==> integrable p f /\
        ((\n. expectation p (X n)) ---> expectation p f) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Extract random_variable from integrable *)
  SUBGOAL_THEN `!n:num. random_variable (p:A prob_space) ((X:num->A->real) n)`
      ASSUME_TAC THENL
    [GEN_TAC THEN
     UNDISCH_TAC `!n:num. integrable (p:A prob_space) ((X:num->A->real) n)` THEN
     DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
     REWRITE_TAC[integrable] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
  (* |f(x)| <= g(x) on carrier *)
  SUBGOAL_THEN
      `!x:A. x IN prob_carrier p ==> abs((f:A->real) x) <= (g:A->real) x`
      ASSUME_TAC THENL
    [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
     REWRITE_TAC[REAL_ABS_BOUNDS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LBOUND) THEN
      EXISTS_TAC `\n:num. (X:num->A->real) n x` THEN
      ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `x:A`]) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `~(g < f) ==> f <= g`) THEN
      DISCH_TAC THEN
      MP_TAC(ISPECL [`sequentially`; `\n:num. --((X:num->A->real) n x)`;
                      `--((f:A->real) x)`; `--(g:A->real) x`]
        REALLIM_LBOUND) THEN
      REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; NOT_IMP] THEN
      REPEAT CONJ_TAC THENL
      [MATCH_MP_TAC REALLIM_NEG THEN ASM_SIMP_TAC[];
       REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
       EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
       FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `x:A`]) THEN
       ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
       ASM_REAL_ARITH_TAC]];
     ALL_TAC] THEN
  (* f is a random variable *)
  SUBGOAL_THEN `random_variable (p:A prob_space) (f:A->real)` ASSUME_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_POINTWISE_LIMIT THEN
     EXISTS_TAC `(X:num->A->real)` THEN ASM_SIMP_TAC[];
     ALL_TAC] THEN
  (* f is integrable *)
  SUBGOAL_THEN `integrable (p:A prob_space) (f:A->real)` ASSUME_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_DOMINATED THEN
     EXISTS_TAC `(g:A->real)` THEN ASM_REWRITE_TAC[] THEN
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `(g:A->real) x` THEN ASM_SIMP_TAC[] THEN
     MATCH_MP_TAC(REAL_ARITH `&0 <= g ==> g <= abs g`) THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `abs((f:A->real) x)` THEN
     ASM_SIMP_TAC[REAL_ABS_POS];
     ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* E[|X_n - f|] -> 0 via DOMINATED_CONVERGENCE_NULL *)
  SUBGOAL_THEN
      `((\n. expectation p (\x. abs((X:num->A->real) n x - (f:A->real) x)))
        ---> &0) sequentially`
      ASSUME_TAC THENL
    [MATCH_MP_TAC DOMINATED_CONVERGENCE_NULL THEN
     EXISTS_TAC `\x:A. &2 * (g:A->real) x` THEN
     REPEAT CONJ_TAC THENL
     [(* RV for |X_n - f| *)
      GEN_TAC THEN
      MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) n`; `f:A->real`]
        INTEGRABLE_SUB) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`p:A prob_space`;
        `\x:A. (X:num->A->real) n x - (f:A->real) x`]
        INTEGRABLE_ABS) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[integrable] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      (* RV for 2*g *)
      UNDISCH_TAC `integrable (p:A prob_space) (g:A->real)` THEN
      DISCH_THEN(fun th -> MP_TAC(MATCH_MP INTEGRABLE_CMUL th)) THEN
      DISCH_THEN(MP_TAC o SPEC `&2`) THEN
      REWRITE_TAC[integrable] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      (* integrable 2*g *)
      MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
      (* bounds: 0 <= |X_n - f| <= 2g *)
      REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
      [REAL_ARITH_TAC;
       MATCH_MP_TAC(REAL_ARITH
         `abs(x) <= g /\ abs(f) <= g ==> abs(x - f) <= &2 * g`) THEN
       ASM_SIMP_TAC[]];
      (* pointwise: |X_n x - f x| -> 0 *)
      REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN
        `((\n. (X:num->A->real) n x - (f:A->real) x) ---> &0) sequentially`
        (fun th -> MP_TAC(MATCH_MP REALLIM_ABS th) THEN
                   REWRITE_TAC[REAL_ABS_NUM]) THEN
      REWRITE_TAC[GSYM REALLIM_NULL] THEN ASM_SIMP_TAC[]];
     ALL_TAC] THEN
  (* E[X_n] -> E[f] from E[|X_n - f|] -> 0 *)
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `expectation (p:A prob_space)
    (\x:A. abs((X:num->A->real) n x - (f:A->real) x))` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `abs(expectation (p:A prob_space)
     (\x:A. (X:num->A->real) n x - (f:A->real) x))` THEN
   CONJ_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) n`; `f:A->real`]
      EXPECTATION_SUB) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC EXPECTATION_ABS_BOUND THEN
    MATCH_MP_TAC INTEGRABLE_SUB THEN
    ASM_REWRITE_TAC[ETA_AX]];
   FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
   ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
   REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Strong law of large numbers without bounded support                       *)
(* ========================================================================= *)

(* Chebyshev bound for shifted partial sums of uncorrelated RVs.
   P(|sum(0..j)(X(a+i) - mu)| >= t) <= (j+1)*sigma_sq / t^2. *)
let CHEBYSHEV_SHIFTED_SUM = prove
 (`!p:A prob_space X mu sigma_sq a j t.
    (!n. integrable p (X n)) /\
    (!n. integrable p (\x. X n x pow 2)) /\
    (!n. expectation p (X n) = mu) /\
    (!n. variance p (X n) = sigma_sq) /\
    (!i j. ~(i = j) ==> covariance p (X i) (X j) = &0) /\
    &0 < t
    ==> prob p {x | x IN prob_carrier p /\
         abs (sum (0..j) (\i. X (a + i) x - mu)) >= t}
        <= &(SUC j) * sigma_sq * inv (t pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `f = \x:A. sum(0..j) (\i. (X:num->A->real) (a + i) x - mu)` THEN
  ABBREV_TAC `g = \x:A. sum(0..j) (\i. (X:num->A->real) (a + i) x)` THEN
  (* f = g + constant *)
  SUBGOAL_THEN `f = (\x:A. (g:A->real) x + (-- &(SUC j) * mu))`
    (LABEL_TAC "fg") THENL
  [EXPAND_TAC "f" THEN EXPAND_TAC "g" THEN
   REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:A` THEN
   ONCE_REWRITE_TAC[SUM_SUB_NUMSEG] THEN
   REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0; ADD1] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* integrability of g *)
  SUBGOAL_THEN `integrable (p:A prob_space) (g:A->real)` (LABEL_TAC "ig") THENL
  [EXPAND_TAC "g" THEN
   MP_TAC(BETA_RULE(ISPECL [`p:A prob_space`;
     `\(i:num) (x:A). (X:num->A->real) (a + i) x`; `j:num`]
     INTEGRABLE_SUM)) THEN
   ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[]]; ALL_TAC] THEN
  (* integrability of f *)
  SUBGOAL_THEN `integrable (p:A prob_space) (f:A->real)` (LABEL_TAC "if") THENL
  [REMOVE_THEN "fg" SUBST1_TAC THEN
   MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[INTEGRABLE_CONST];
   ALL_TAC] THEN
  (* E[f] = 0 *)
  SUBGOAL_THEN `expectation (p:A prob_space) (f:A->real) = &0`
    (LABEL_TAC "ef") THENL
  [REMOVE_THEN "fg" SUBST1_TAC THEN
   W(MP_TAC o PART_MATCH (lhand o rand) EXPECTATION_ADD o lhand o snd) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[EXPECTATION_CONST] THEN
   EXPAND_TAC "g" THEN
   MP_TAC(BETA_RULE(ISPECL [`p:A prob_space`;
     `\(i:num) (x:A). (X:num->A->real) (a + i) x`; `j:num`]
     EXPECTATION_SUM)) THEN
   ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ETA_AX] THEN
    ASM_REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0; ADD1] THEN
    REAL_ARITH_TAC]; ALL_TAC] THEN
  (* Var(f) = (j+1)*sigma_sq *)
  SUBGOAL_THEN `variance (p:A prob_space) (f:A->real) = &(SUC j) * sigma_sq`
    (LABEL_TAC "vf") THENL
  [REMOVE_THEN "fg" SUBST1_TAC THEN
   SUBGOAL_THEN
     `variance p (\x:A. (g:A->real) x + -- &(SUC j) * mu) = variance p g`
     SUBST1_TAC THENL
   [MATCH_MP_TAC VARIANCE_SHIFT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   EXPAND_TAC "g" THEN
   MP_TAC(BETA_RULE(ISPECL [`p:A prob_space`;
     `\(i:num) (x:A). (X:num->A->real) (a + i) x`; `j:num`]
     VARIANCE_SUM_UNCORRELATED)) THEN
   ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
    [REPEAT STRIP_TAC THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
     REPEAT STRIP_TAC THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
     REPEAT STRIP_TAC THEN REWRITE_TAC[ETA_AX] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ETA_AX] THEN
    ASM_REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0; ADD1]]; ALL_TAC] THEN
  (* integrability of (f - E[f])^2 for Chebyshev *)
  SUBGOAL_THEN `integrable (p:A prob_space) (\x. ((f:A->real) x -
    expectation p f) pow 2)` (LABEL_TAC "if2") THENL
  [USE_THEN "ef" (fun th -> REWRITE_TAC[th; REAL_SUB_RZERO]) THEN
   EXPAND_TAC "f" THEN
   MP_TAC(BETA_RULE(ISPECL [`p:A prob_space`;
     `\(i:num) (x:A). (X:num->A->real) (a + i) x - mu`; `j:num`]
     INTEGRABLE_SUM_SQUARE)) THEN
   ANTS_TAC THENL
   [CONJ_TAC THEN REPEAT STRIP_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[INTEGRABLE_CONST; ETA_AX];
     (* integrable p (\x. (X(a+i) x - mu) pow 2) from X^2, X, and const *)
     SUBGOAL_THEN `(\x:A. ((X:num->A->real) (a + i) x - mu) pow 2) =
       (\x. X (a + i) x pow 2 - &2 * mu * X (a + i) x + mu pow 2)`
       SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
     MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
      [ASM_REWRITE_TAC[ETA_AX];
       REWRITE_TAC[REAL_MUL_ASSOC] THEN
       MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[ETA_AX]];
      REWRITE_TAC[INTEGRABLE_CONST]]];
    REWRITE_TAC[]]; ALL_TAC] THEN
  (* Rewrite event using f and apply Chebyshev *)
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
    abs(sum(0..j) (\i. (X:num->A->real) (a + i) x - mu)) >= t} =
    {x | x IN prob_carrier p /\ abs(f x - expectation p f) >= t}`
    SUBST1_TAC THENL
  [USE_THEN "ef" (fun th -> REWRITE_TAC[th; REAL_SUB_RZERO]) THEN
   REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
   UNDISCH_TAC `(\x:A. sum (0..j) (\i. (X:num->A->real) (a + i) x - mu)) =
     (f:A->real)` THEN
   DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]); ALL_TAC] THEN
  (* Apply Chebyshev and substitute Var(f) *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `variance (p:A prob_space) (f:A->real) / t pow 2` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC CHEBYSHEV_INEQUALITY THEN ASM_REWRITE_TAC[];
   ASM_REWRITE_TAC[real_div; REAL_MUL_ASSOC; REAL_LE_REFL]]);;

(* Gap control for SLLN: for each tolerance 1/(m+1), almost surely the
   centered partial sums in each gap (k^2, (k+1)^2] are bounded by
   (k^2+1)/(m+1). Proved via Chebyshev + union bound + Borel-Cantelli. *)
let SLLN_GAP_CONTROL = prove
 (`!p:A prob_space (X:num->A->real) mu sigma_sq.
    (!n. integrable p (X n)) /\
    (!n. integrable p (\x. X n x pow 2)) /\
    (!n. expectation p (X n) = mu) /\
    (!n. variance p (X n) = sigma_sq) /\
    (!i j. ~(i = j) ==> covariance p (X i) (X j) = &0)
    ==> !m:num. almost_surely p
          {x:A | ?N:num. !k. N <= k ==>
            !n. k * k < n /\ n <= (k + 1) * (k + 1) ==>
              abs(sum(k * k + 1..n) (\i. X i x - mu)) <
              &(SUC(k * k)) * inv(&(SUC m))}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `m:num` THEN
  REWRITE_TAC[almost_surely] THEN
  ABBREV_TAC `B = \k. {x:A | x IN prob_carrier p /\
    ?nn:num. k * k < nn /\ nn <= (k + 1) * (k + 1) /\
      abs(sum(k * k + 1..nn) (\i. (X:num->A->real) i x - mu)) >=
      &(SUC(k * k)) * inv(&(SUC m))}` THEN
  EXISTS_TAC `limsup_events (B:num->A->bool)` THEN
  (* Key subgoal: B k is a prob_event for each k *)
  SUBGOAL_THEN `!k. (B:num->A->bool) k IN prob_events p` (LABEL_TAC "Bev") THENL
  [X_GEN_TAC `k:num` THEN EXPAND_TAC "B" THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
     (?nn. k * k < nn /\ nn <= (k + 1) * (k + 1) /\
       abs (sum (k * k + 1..nn) (\i. X i x - mu)) >=
       &(SUC (k * k)) * inv (&(SUC m)))} =
     UNIONS (IMAGE (\nn. {x:A | x IN prob_carrier p /\
       abs (sum (k * k + 1..nn) (\i. X i x - mu)) >=
       &(SUC (k * k)) * inv (&(SUC m))})
       {nn | k * k < nn /\ nn <= (k + 1) * (k + 1)})`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; UNIONS_IMAGE; IN_ELIM_THM] THEN
    GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
   MATCH_MP_TAC PROB_FINITE_UNION_IN_EVENTS THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `nn:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC RANDOM_VARIABLE_GE THEN
    MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN
    (* sum(k*k+1..nn)(X_i - mu) = sum(0..nn)(X_i - mu) - sum(0..k*k)(X_i - mu) *)
    SUBGOAL_THEN `(\x:A. sum(k * k + 1..nn) (\i. (X:num->A->real) i x - mu)) =
      (\x. sum(0..nn) (\i. X i x - mu) - sum(0..k * k) (\i. X i x - mu))`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
     MATCH_MP_TAC(REAL_ARITH `!a b c:real. a + b = c ==> b = c - a`) THEN
     MATCH_MP_TAC SUM_COMBINE_R THEN ASM_ARITH_TAC;
     MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN CONJ_TAC THEN
     MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN
     REPEAT STRIP_TAC THEN BETA_TAC THEN
     MATCH_MP_TAC RANDOM_VARIABLE_SUB_CONST THEN
     REWRITE_TAC[ETA_AX] THEN
     ASM_MESON_TAC[integrable]];
    MATCH_MP_TAC FINITE_IMAGE THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `0..(k + 1) * (k + 1):num` THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN ARITH_TAC];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[null_event] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LIMSUP_EVENTS_IN_EVENTS THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FIRST_BOREL_CANTELLI THEN ASM_REWRITE_TAC[] THEN
    (* Need: real_summable (from 0) (\i. prob p (B i)) *)
    (* Strategy: P(B k) <= C/(k^2+1) via Chebyshev + union bound, then compare *)
    (* with summable 1/(k^2+1). *)
    ABBREV_TAC `A = \k j. {x:A | x IN prob_carrier p /\
      abs(sum(0..j) (\i. (X:num->A->real) (k * k + 1 + i) x - mu)) >=
      &(SUC(k * k)) * inv(&(SUC m))}` THEN
    (* Each A k j is a prob_event *)
    SUBGOAL_THEN `!k j. (A:num->num->A->bool) k j IN prob_events p`
      (LABEL_TAC "Aev") THENL
    [REPEAT GEN_TAC THEN EXPAND_TAC "A" THEN
     MATCH_MP_TAC RANDOM_VARIABLE_GE THEN
     MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN
     MP_TAC(BETA_RULE(ISPECL [`p:A prob_space`;
       `\(i:num) (x:A). (X:num->A->real) (k * k + 1 + i) x - mu`;
       `j:num`] RANDOM_VARIABLE_SUM)) THEN
     ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_SUB_CONST THEN
      MP_TAC(SPEC `k * k + 1 + i:num`
        (ASSUME `!n. integrable (p:A prob_space) ((X:num->A->real) n)`)) THEN
      REWRITE_TAC[integrable] THEN SIMP_TAC[ETA_AX];
      REWRITE_TAC[]]; ALL_TAC] THEN
    (* B k SUBSET UNIONS(IMAGE (A k) (0..2*k)) *)
    SUBGOAL_THEN `!k. (B:num->A->bool) k SUBSET
      UNIONS(IMAGE ((A:num->num->A->bool) k) (0..2 * k))`
      (LABEL_TAC "Bsub") THENL
    [X_GEN_TAC `k:num` THEN EXPAND_TAC "B" THEN EXPAND_TAC "A" THEN
     REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
     X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     EXISTS_TAC `nn - (k * k + 1):num` THEN
     SUBGOAL_THEN `nn - (k * k + 1) <= 2 * k` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `!i:num. k * k + 1 + i = (k * k + 1) + i`
       (fun th -> REWRITE_TAC[th]) THENL
     [ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN
       `sum (0..nn - (k * k + 1))
         (\i:num. (X:num->A->real) ((k * k + 1) + i) x - mu) =
        sum (k * k + 1..nn) (\i. X i x - mu)`
       (fun th -> ASM_REWRITE_TAC[th]) THEN
     MP_TAC(BETA_RULE(ISPECL [`\i:num. (X:num->A->real) i x - mu`;
       `k * k + 1`; `nn:num`] SUM_OFFSET_0)) THEN
     ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     DISCH_THEN SUBST1_TAC THEN
     MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_NUMSEG] THEN
     REPEAT STRIP_TAC THEN
     AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     ARITH_TAC; ALL_TAC] THEN
    (* Comparison test: bound P(B k) by C/(k^2+1) *)
    MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
    EXISTS_TAC `\k. &5 * sigma_sq * &(SUC m) pow 2 *
      inv(&(SUC(k * k)))` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC REAL_SUMMABLE_LMUL THEN
     MATCH_MP_TAC REAL_SUMMABLE_LMUL THEN
     MATCH_MP_TAC REAL_SUMMABLE_LMUL THEN
     REWRITE_TAC[SUMMABLE_INV_SUC_SQUARES]; ALL_TAC] THEN
    EXISTS_TAC `0` THEN REWRITE_TAC[GE; LE_0; IN_FROM] THEN
    X_GEN_TAC `k:num` THEN
    SUBGOAL_THEN `&0 <= prob p ((B:num->A->bool) k)`
      (fun th -> REWRITE_TAC[MATCH_MP
        (REAL_ARITH `&0 <= x ==> abs x = x`) th]) THENL
    [ASM_SIMP_TAC[PROB_POSITIVE]; ALL_TAC] THEN
    (* Chain: P(B k) <= P(union) <= sum(P(A k j)) <= bound *)
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `prob (p:A prob_space) (UNIONS(IMAGE
      ((A:num->num->A->bool) k) (0..2 * k)))` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC PROB_MONO THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC PROB_FINITE_UNION_IN_EVENTS THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_NUMSEG] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_NUMSEG]]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..2 * k)
      (\j. prob (p:A prob_space) ((A:num->num->A->bool) k j))` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC PROB_FINITE_SUBADDITIVE THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    (* Apply CHEBYSHEV_SHIFTED_SUM to each P(A k j) *)
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..2 * k) (\j. &(SUC j) * sigma_sq *
      inv((&(SUC(k * k)) * inv(&(SUC m))) pow 2))` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j':num` THEN STRIP_TAC THEN
     EXPAND_TAC "A" THEN
     ONCE_REWRITE_TAC[ARITH_RULE `k * k + 1 + i:num = (k * k + 1) + i`] THEN
     MATCH_MP_TAC CHEBYSHEV_SHIFTED_SUM THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC REAL_LT_MUL THEN
     REWRITE_TAC[REAL_OF_NUM_LT; LT_0] THEN
     MATCH_MP_TAC REAL_LT_INV THEN REWRITE_TAC[REAL_OF_NUM_LT; LT_0];
     ALL_TAC] THEN
    (* Simplify inv((N * inv(M))^2) = M^2 * inv(N^2) *)
    SUBGOAL_THEN `inv((&(SUC(k * k)) * inv(&(SUC m))) pow 2) =
      &(SUC m) pow 2 * inv(&(SUC(k * k)) pow 2)` SUBST1_TAC THENL
    [MATCH_MP_TAC(REAL_FIELD `~(a = &0) /\ ~(b = &0) ==>
       inv((a * inv b) pow 2) = b pow 2 * inv(a pow 2)`) THEN
     REWRITE_TAC[REAL_OF_NUM_EQ; NOT_SUC]; ALL_TAC] THEN
    REWRITE_TAC[SUM_RMUL] THEN
    (* sum(0..2k)(SUC j) * c <= 5*N * c, then 5*N*c = 5*sigma_sq*M^2/N *)
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&5 * &(SUC(k * k))) * sigma_sq *
      &(SUC m) pow 2 * inv(&(SUC(k * k)) pow 2)` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [(* sum(0..2k)(SUC j) <= 5*SUC(k*k) on reals *)
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum(0..2*k) (\j. &(SUC(2*k)))` THEN CONJ_TAC THENL
      [MATCH_MP_TAC SUM_LE_NUMSEG THEN
       GEN_TAC THEN STRIP_TAC THEN
       REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
       REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0; ADD1] THEN
       REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
       ASM_CASES_TAC `k <= 3` THENL
       [FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC o
         MATCH_MP(ARITH_RULE `k <= 3 ==> k = 0 \/ k = 1 \/ k = 2 \/ k = 3`)) THEN
        ASM_REWRITE_TAC[] THEN ARITH_TAC;
        MATCH_MP_TAC(ARITH_RULE
          `4 * k <= k * k ==> (2 * k + 1) * (2 * k + 1) <= 5 * (k * k + 1)`) THEN
        ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[LE_MULT_LCANCEL] THEN
        DISJ2_TAC THEN ASM_ARITH_TAC]];
      (* 0 <= sigma_sq * M^2 * inv(N^2) *)
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
      [SUBGOAL_THEN `sigma_sq = variance p ((X:num->A->real) 0)` SUBST1_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `0` o
         check(fun th -> fst(dest_const(fst(strip_comb(
           lhand(snd(dest_forall(concl th))))))) = "variance")) THEN
        REWRITE_TAC[EQ_SYM_EQ]; ALL_TAC] THEN
       MATCH_MP_TAC VARIANCE_NONNEG THEN
       SUBGOAL_THEN `expectation p ((X:num->A->real) 0) = mu` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
       SUBGOAL_THEN `(\x:A. ((X:num->A->real) 0 x - mu) pow 2) =
         (\x. X 0 x pow 2 - &2 * mu * X 0 x + mu pow 2)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
       MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
        [MP_TAC(SPEC `0` (ASSUME `!n. integrable p (\x:A. (X:num->A->real) n x pow 2)`)) THEN
         REWRITE_TAC[];
         MATCH_MP_TAC INTEGRABLE_CMUL THEN
         MATCH_MP_TAC INTEGRABLE_CMUL THEN
         MP_TAC(SPEC `0` (ASSUME `!n. integrable (p:A prob_space) ((X:num->A->real) n)`)) THEN
         SIMP_TAC[ETA_AX]];
        REWRITE_TAC[INTEGRABLE_CONST]];
       MATCH_MP_TAC REAL_LE_MUL THEN
       REWRITE_TAC[REAL_LE_POW_2] THEN
       MATCH_MP_TAC REAL_LE_INV THEN REWRITE_TAC[REAL_LE_POW_2]]];
     (* 5*N * c = 5 * sigma_sq * M^2 * inv(N) by algebra *)
     MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= b`) THEN
     MATCH_MP_TAC(REAL_FIELD `~(n = &0) ==>
       (&5 * n) * s * m * inv(n pow 2) = &5 * s * m * inv n`) THEN
     REWRITE_TAC[REAL_OF_NUM_EQ; NOT_SUC]]];
   (* Subset: complement of target within carrier is contained in limsup B *)
   REWRITE_TAC[SUBSET; IN_ELIM_THM; limsup_events; INTERS_GSPEC; IN_UNIV] THEN
   EXPAND_TAC "B" THEN REWRITE_TAC[IN_ELIM_THM] THEN
   X_GEN_TAC `x:A` THEN
   REWRITE_TAC[NOT_EXISTS_THM; NOT_FORALL_THM; NOT_IMP; REAL_NOT_LT] THEN
   STRIP_TAC THEN X_GEN_TAC `NN:num` THEN
   REWRITE_TAC[UNIONS_GSPEC; GE; IN_ELIM_THM] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `NN:num`) THEN
   ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
   DISCH_THEN(X_CHOOSE_THEN `kk:num` MP_TAC) THEN
   REWRITE_TAC[DE_MORGAN_THM; NOT_FORALL_THM; NOT_IMP; REAL_NOT_LT] THEN
   STRIP_TAC THEN
   EXISTS_TAC `kk:num` THEN ASM_REWRITE_TAC[] THEN
   EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[real_ge] THEN
   ASM_REAL_ARITH_TAC]);;

(* Strong Law of Large Numbers without bounded support *)
let STRONG_LAW_FINITE_VARIANCE = prove
 (`!p:A prob_space (X:num->A->real) mu sigma_sq.
    (!n. integrable p (X n)) /\
    (!n. integrable p (\x. X n x pow 2)) /\
    (!n. expectation p (X n) = mu) /\
    (!n. variance p (X n) = sigma_sq) /\
    (!i j. ~(i = j) ==> covariance p (X i) (X j) = &0)
    ==> almost_surely p
          {x | ((\n. inv(&(SUC n)) * sum(0..n) (\i. X i x)) ---> mu) sequentially}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Step 1: subsequence convergence from SLLN_SUBSEQ *)
  SUBGOAL_THEN
    `almost_surely (p:A prob_space)
      {x | ((\k. inv(&(SUC(k * k))) * sum(0..k * k) (\i. (X:num->A->real) i x)) ---> mu) sequentially}`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SLLN_SUBSEQ THEN
   EXISTS_TAC `sigma_sq:real` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 2: gap control *)
  SUBGOAL_THEN
    `!m:num. almost_surely (p:A prob_space)
      {x:A | ?N:num. !k. N <= k ==>
        !n. k * k < n /\ n <= (k + 1) * (k + 1) ==>
          abs(sum(k * k + 1..n) (\i. (X:num->A->real) i x - mu)) <
          &(SUC(k * k)) * inv(&(SUC m))}`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SLLN_GAP_CONTROL THEN
   EXISTS_TAC `sigma_sq:real` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 3: countable intersection of gap control events *)
  SUBGOAL_THEN
    `almost_surely (p:A prob_space)
      {x:A | !m. ?N:num. !k. N <= k ==>
        !n. k * k < n /\ n <= (k + 1) * (k + 1) ==>
          abs(sum(k * k + 1..n) (\i. (X:num->A->real) i x - mu)) <
          &(SUC(k * k)) * inv(&(SUC m))}`
    ASSUME_TAC THENL
  [MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
   EXISTS_TAC `INTERS {(\m. {x:A | ?N:num. !k. N <= k ==>
        !n. k * k < n /\ n <= (k + 1) * (k + 1) ==>
          abs(sum(k * k + 1..n) (\i. (X:num->A->real) i x - mu)) <
          &(SUC(k * k)) * inv(&(SUC m))}) m | m IN (:num)}` THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC ALMOST_SURELY_COUNTABLE_INTER THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[INTERS_GSPEC; IN_UNIV; IN_ELIM_THM] THEN MESON_TAC[]];
   ALL_TAC] THEN
  (* Step 4: intersect subsequence and gap control *)
  SUBGOAL_THEN
    `almost_surely (p:A prob_space)
      ({x:A | ((\k. inv(&(SUC(k * k))) * sum(0..k * k) (\i. (X:num->A->real) i x)) ---> mu) sequentially} INTER
       {x:A | !m. ?N:num. !k. N <= k ==>
        !n. k * k < n /\ n <= (k + 1) * (k + 1) ==>
          abs(sum(k * k + 1..n) (\i. X i x - mu)) <
          &(SUC(k * k)) * inv(&(SUC m))})`
    ASSUME_TAC THENL
  [MATCH_MP_TAC ALMOST_SURELY_INTER THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 5: on the intersection, show full convergence *)
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC `{x:A | ((\k. inv(&(SUC(k * k))) * sum(0..k * k) (\i. (X:num->A->real) i x)) ---> mu) sequentially} INTER
       {x:A | !m. ?N:num. !k. N <= k ==>
        !n. k * k < n /\ n <= (k + 1) * (k + 1) ==>
          abs(sum(k * k + 1..n) (\i. X i x - mu)) <
          &(SUC(k * k)) * inv(&(SUC m))}` THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
  (* Pointwise proof: use REALLIM_SEQUENTIALLY *)
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  (* Choose m such that inv(SUC m) < e/2 *)
  SUBGOAL_THEN `?m:num. inv(&(SUC m)) < e / &2` STRIP_ASSUME_TAC THENL
  [MP_TAC(SPEC `e / &2` REAL_ARCH_INV) THEN
   ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
   DISCH_THEN(X_CHOOSE_THEN `nn:num` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `nn - 1` THEN
   ASM_CASES_TAC `nn = 0` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `SUC(nn - 1) = nn` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* Get gap control N for this m *)
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
  DISCH_THEN(X_CHOOSE_TAC `K_gap:num`) THEN
  (* Get subsequence bound for e/2 *)
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_TAC `K_subseq:num`) THEN
  (* Choose N = (K_gap + K_subseq)^2 *)
  EXISTS_TAC `(K_gap + K_subseq) * (K_gap + K_subseq):num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  (* Find k with k*k <= n < (k+1)*(k+1) *)
  MP_TAC(SPEC `n:num` NUM_SQRT_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  (* Show K_gap + K_subseq <= k *)
  SUBGOAL_THEN `K_gap + K_subseq <= k:num` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
   SUBGOAL_THEN `(k + 1) * (k + 1) <= (K_gap + K_subseq) * (K_gap + K_subseq):num` MP_TAC THENL
   [MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
   ALL_TAC] THEN
  (* Case split: n = k*k or k*k < n *)
  ASM_CASES_TAC `n = k * k:num` THENL
  [(* Case n = k*k: directly from subsequence convergence *)
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `e / &2` THEN
   CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o
     check (fun th -> free_in `K_subseq:num` (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC];
    ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* Case k*k < n *)
  SUBGOAL_THEN `k * k < n:num` ASSUME_TAC THENL
  [ASM_ARITH_TAC; ALL_TAC] THEN
  (* Split the sum: sum(0..n) = sum(0..k*k) + sum(k*k+1..n) *)
  SUBGOAL_THEN
    `sum(0..n) (\i. (X:num->A->real) i x) =
     sum(0..k * k) (\i. X i x) + sum(k * k + 1..n) (\i. X i x)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC(GSYM SUM_COMBINE_R) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  (* Centering identity: inv(SUC n) * S_n - mu = inv(SUC n) * sum(centered) *)
  SUBGOAL_THEN
    `inv(&(SUC n)) * sum(0..n) (\i. (X:num->A->real) i x) - mu =
     inv(&(SUC n)) * sum(0..n) (\i. X i x - mu)`
    SUBST1_TAC THENL
  [REWRITE_TAC[SUM_SUB_NUMSEG; SUM_CONST_NUMSEG; SUB_0] THEN
   SUBGOAL_THEN `&(SUC n) = &(n + 1)` (fun th -> REWRITE_TAC[GSYM th]) THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ; ADD1]; ALL_TAC] THEN
   SUBGOAL_THEN `~(&(SUC n) = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `~(&(SUC n) = &0)` THEN CONV_TAC REAL_FIELD;
   ALL_TAC] THEN
  (* Split the centered sum *)
  SUBGOAL_THEN
    `sum(0..n) (\i. (X:num->A->real) i x - mu) =
     sum(0..k * k) (\i. X i x - mu) + sum(k * k + 1..n) (\i. X i x - mu)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC(GSYM SUM_COMBINE_R) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  (* Get the gap bound *)
  SUBGOAL_THEN
    `abs(sum(k * k + 1..n) (\i. (X:num->A->real) i x - mu)) < &(SUC(k * k)) * inv(&(SUC m))`
    ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o
    check (fun th -> free_in `K_gap:num` (concl th))) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC];
   ALL_TAC] THEN
  (* Get the centered subsequence bound *)
  SUBGOAL_THEN
    `abs(inv(&(SUC(k * k))) * sum(0..k * k) (\i. (X:num->A->real) i x - mu)) < e / &2`
    ASSUME_TAC THENL
  [SUBGOAL_THEN `inv(&(SUC(k * k))) * sum(0..k * k) (\i. (X:num->A->real) i x - mu) =
     inv(&(SUC(k * k))) * sum(0..k * k) (\i. X i x) - mu` SUBST1_TAC THENL
   [REWRITE_TAC[SUM_SUB_NUMSEG; SUM_CONST_NUMSEG; SUB_0] THEN
    SUBGOAL_THEN `&(SUC(k * k)) = &(k * k + 1)` (fun th -> REWRITE_TAC[GSYM th]) THENL
    [REWRITE_TAC[REAL_OF_NUM_EQ; ADD1]; ALL_TAC] THEN
    SUBGOAL_THEN `~(&(SUC(k * k)) = &0)` ASSUME_TAC THENL
    [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `~(&(SUC(k * k)) = &0)` THEN CONV_TAC REAL_FIELD;
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o
      check (fun th -> free_in `K_subseq:num` (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC]];
   ALL_TAC] THEN
  (* Triangle inequality *)
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `abs(inv(&(SUC n)) * sum(0..k * k) (\i. (X:num->A->real) i x - mu)) +
              abs(inv(&(SUC n)) * sum(k * k + 1..n) (\i. X i x - mu))` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[REAL_ABS_MUL; GSYM REAL_ADD_LDISTRIB] THEN
   REWRITE_TAC[REAL_ABS_ABS] THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_ABS_POS]; REWRITE_TAC[REAL_ABS_TRIANGLE]];
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `e / &2 + e / &2` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LT_ADD2;
   ASM_REAL_ARITH_TAC] THEN
  CONJ_TAC THENL
  [(* First term: |inv(SUC n) * sum(0..k*k)(centered)| < e/2 *)
   MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `abs(inv(&(SUC(k * k))) * sum(0..k * k) (\i. (X:num->A->real) i x - mu))` THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[REAL_ABS_MUL] THEN
   MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
   REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NUM] THEN
   MATCH_MP_TAC REAL_LE_INV2 THEN
   REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
   (* Second term: |inv(SUC n) * gap| < e/2 *)
   MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `inv(&(SUC(k * k))) * abs(sum(k * k + 1..n) (\i. (X:num->A->real) i x - mu))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
   MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&(SUC m))` THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `inv(&(SUC(k * k))) * (&(SUC(k * k)) * inv(&(SUC m)))` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_INV THEN REWRITE_TAC[REAL_POS];
     MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    SUBGOAL_THEN `inv(&(SUC(k * k))) * &(SUC(k * k)) = &1` SUBST1_TAC THENL
    [MATCH_MP_TAC REAL_MUL_LINV THEN REWRITE_TAC[REAL_OF_NUM_EQ] THEN ARITH_TAC;
     REWRITE_TAC[REAL_MUL_LID; REAL_LE_REFL]]]]);;
