(* ========================================================================= *)
(* Standard discrete distributions: Bernoulli, Binomial, Poisson,          *)
(* and Geometric.                                                          *)
(*                                                                         *)
(* Defines what it means for a random variable to have a Bernoulli or      *)
(* Binomial distribution, proves expectation, variance, and the connection *)
(* between indicators and Bernoulli RVs.                                   *)
(*                                                                         *)
(* Also defines the Poisson PMF and proves the Poisson limit theorem:      *)
(* Bin(n, lam/n) -> Poisson(lam) pointwise as n -> infinity.               *)
(*                                                                         *)
(* Defines the Geometric PMF and proves normalization and mean.            *)
(* ========================================================================= *)

needs "Probability/clt.ml";;

(* ========================================================================= *)
(* Bernoulli random variables                                              *)
(* ========================================================================= *)

(* A Bernoulli(q) random variable takes values 0 and 1 with P(X=1)=q *)
let bernoulli_rv = new_definition
  `bernoulli_rv (p:A prob_space) (X:A->real) (q:real) <=>
   simple_rv p X /\
   &0 <= q /\ q <= &1 /\
   (!x. x IN prob_carrier p ==> X x = &0 \/ X x = &1) /\
   prob p {x | x IN prob_carrier p /\ X x = &1} = q`;;

(* P(X=0) = 1 - q for Bernoulli *)
let BERNOULLI_RV_PROB_ZERO = prove
  (`!p:A prob_space X q.
      bernoulli_rv p X q
      ==> prob p {x | x IN prob_carrier p /\ X x = &0} = &1 - q`,
   REPEAT GEN_TAC THEN REWRITE_TAC[bernoulli_rv] THEN STRIP_TAC THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ X x = &0} =
      prob_carrier p DIFF {x | x IN prob_carrier p /\ X x = &1}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN
    X_GEN_TAC `z:A` THEN ASM_CASES_TAC `(z:A) IN prob_carrier p` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:A`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ X x = &1} IN prob_events p`
     ASSUME_TAC THENL
   [SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\ X x = &1} =
       prob_carrier p DIFF {x | x IN prob_carrier p /\ X x <= &0}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN
     X_GEN_TAC `z:A` THEN ASM_CASES_TAC `(z:A) IN prob_carrier p` THEN
     ASM_REWRITE_TAC[] THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `z:A`) THEN ASM_REWRITE_TAC[] THEN
     REAL_ARITH_TAC;
     MATCH_MP_TAC PROB_COMPL_IN_EVENTS THEN
     UNDISCH_TAC `simple_rv (p:A prob_space) (X:A->real)` THEN
     REWRITE_TAC[simple_rv; random_variable] THEN MESON_TAC[]];
    ASM_SIMP_TAC[PROB_COMPL]]);;

(* E[X] = q for Bernoulli *)
let BERNOULLI_RV_EXPECTATION = prove
  (`!p:A prob_space X q.
      bernoulli_rv p X q ==> simple_expectation p X = q`,
   REPEAT GEN_TAC THEN REWRITE_TAC[bernoulli_rv] THEN STRIP_TAC THEN
   ABBREV_TAC `A = {x:A | x IN prob_carrier p /\ X x = &1}` THEN
   SUBGOAL_THEN `(A:A->bool) IN prob_events p` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN
    SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\ X x = &1} =
       prob_carrier p DIFF {x | x IN prob_carrier p /\ (X:A->real) x <= &0}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN
     X_GEN_TAC `z:A` THEN ASM_CASES_TAC `(z:A) IN prob_carrier p` THEN
     ASM_REWRITE_TAC[] THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `z:A`) THEN ASM_REWRITE_TAC[] THEN
     REAL_ARITH_TAC;
     MATCH_MP_TAC PROB_COMPL_IN_EVENTS THEN
     UNDISCH_TAC `simple_rv (p:A prob_space) (X:A->real)` THEN
     REWRITE_TAC[simple_rv; random_variable] THEN MESON_TAC[]];
    ALL_TAC] THEN
   SUBGOAL_THEN `!z:A. z IN prob_carrier p ==> X z = indicator_fn A z`
     ASSUME_TAC THENL
   [X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THENL
    [UNDISCH_TAC `(z:A) IN A` THEN EXPAND_TAC "A" THEN
     REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
     UNDISCH_TAC `~((z:A) IN A)` THEN EXPAND_TAC "A" THEN
     REWRITE_TAC[IN_ELIM_THM; DE_MORGAN_THM; NOT_IMP] THEN
     ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `z:A`) THEN ASM_REWRITE_TAC[] THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     ASM_MESON_TAC[]];
    ALL_TAC] THEN
   SUBGOAL_THEN `simple_expectation p X =
     simple_expectation p (indicator_fn (A:A->bool))` SUBST1_TAC THENL
   [REWRITE_TAC[simple_expectation] THEN
    SUBGOAL_THEN `IMAGE (X:A->real) (prob_carrier p) =
      IMAGE (indicator_fn (A:A->bool)) (prob_carrier p)` SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN GEN_TAC THEN
     EQ_TAC THEN STRIP_TAC THEN EXISTS_TAC `x':A` THEN ASM_REWRITE_TAC[] THEN
     ASM_MESON_TAC[];
     AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
     X_GEN_TAC `v:real` THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
     REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `z:A` THEN
     ASM_CASES_TAC `(z:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
     ASM_MESON_TAC[]];
    ASM_SIMP_TAC[SIMPLE_EXPECTATION_INDICATOR]]);;

(* Var(X) = q(1-q) for Bernoulli *)
let BERNOULLI_RV_VARIANCE = prove
  (`!p:A prob_space X q.
      bernoulli_rv p X q ==> simple_variance p X = q * (&1 - q)`,
   REPEAT GEN_TAC THEN REWRITE_TAC[bernoulli_rv] THEN STRIP_TAC THEN
   SUBGOAL_THEN `simple_expectation (p:A prob_space) X = q` ASSUME_TAC THENL
   [MATCH_MP_TAC BERNOULLI_RV_EXPECTATION THEN
    ASM_REWRITE_TAC[bernoulli_rv]; ALL_TAC] THEN
   ASM_SIMP_TAC[SIMPLE_VARIANCE_ALT] THEN
   SUBGOAL_THEN `(\x:A. (X:A->real) x pow 2) = (\x. X x * X x)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; REAL_POW_2]; ALL_TAC] THEN
   SUBGOAL_THEN
     `simple_expectation (p:A prob_space) (\x:A. X x * X x) =
      simple_expectation p X`
     SUBST1_TAC THENL
   [REWRITE_TAC[simple_expectation] THEN
    SUBGOAL_THEN `IMAGE (\x:A. (X:A->real) x * X x) (prob_carrier p) =
      IMAGE X (prob_carrier p)` SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN GEN_TAC THEN
     EQ_TAC THEN STRIP_TAC THENL
     [EXISTS_TAC `x':A` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x':A`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      EXISTS_TAC `x':A` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x':A`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
     AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
     X_GEN_TAC `v:real` THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
     REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `z:A` THEN
     ASM_CASES_TAC `(z:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
     EQ_TAC THEN STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `z:A`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(X:A->real) z * X z = v` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `z:A`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(X:A->real) z = v` THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC]];
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING]);;

(* Indicator functions are Bernoulli RVs *)
let INDICATOR_BERNOULLI = prove
  (`!p:A prob_space a.
      a IN prob_events p
      ==> bernoulli_rv p (indicator_fn a) (prob p a)`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[bernoulli_rv] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[SIMPLE_RV_INDICATOR];
    MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PROB_LE_1 THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[indicator_fn] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    AP_TERM_TAC THEN REWRITE_TAC[indicator_fn; EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `z:A` THEN
    ASM_CASES_TAC `(z:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THENL
    [ASM_CASES_TAC `(z:A) IN a` THEN ASM_REWRITE_TAC[] THEN
     CONV_TAC REAL_RAT_REDUCE_CONV;
     MP_TAC(ISPECL [`p:A prob_space`; `a:A->bool`] PROB_EVENT_SUBSET) THEN
     ASM_REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[]]]);;


(* ========================================================================= *)
(* Binomial random variables                                               *)
(* ========================================================================= *)

(* A Binomial(n,q) random variable takes values in {0,..,n} with
   P(X=k) = C(n,k) * q^k * (1-q)^(n-k) *)
let binomial_rv = new_definition
  `binomial_rv (p:A prob_space) (X:A->real) (n:num) (q:real) <=>
   simple_rv p X /\
   &0 <= q /\ q <= &1 /\
   (!x. x IN prob_carrier p ==> ?k. k <= n /\ X x = &k) /\
   !k. k <= n ==>
     prob p {x | x IN prob_carrier p /\ X x = &k} =
     &(binom(n,k)) * q pow k * (&1 - q) pow (n - k)`;;

(* Bernoulli(q) is Binomial(1, q) *)
let BERNOULLI_IS_BINOMIAL_1 = prove
  (`!p:A prob_space X q.
      bernoulli_rv p X q ==> binomial_rv p X 1 q`,
   REPEAT GEN_TAC THEN REWRITE_TAC[bernoulli_rv; binomial_rv] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:A`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THENL
    [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
     EXISTS_TAC `1` THEN ASM_REWRITE_TAC[LE_REFL]];
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `k = 0 \/ k = 1` STRIP_ASSUME_TAC THENL
    [ASM_ARITH_TAC;
     ASM_REWRITE_TAC[binom; BINOM_REFL; SUB_REFL; SUB] THEN
     CONV_TAC NUM_REDUCE_CONV THEN
     REWRITE_TAC[real_pow; REAL_POW_1; REAL_MUL_LID; REAL_MUL_RID] THEN
     SUBGOAL_THEN
       `{x:A | x IN prob_carrier p /\ X x = &0} =
        prob_carrier p DIFF {x | x IN prob_carrier p /\ X x = &1}`
       SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN
      X_GEN_TAC `z:A` THEN ASM_CASES_TAC `(z:A) IN prob_carrier p` THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:A`) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
     SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ X x = &1} IN prob_events p`
       ASSUME_TAC THENL
     [SUBGOAL_THEN
        `{x:A | x IN prob_carrier p /\ X x = &1} =
         prob_carrier p DIFF {x | x IN prob_carrier p /\ (X:A->real) x <= &0}`
        SUBST1_TAC THENL
      [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN
       X_GEN_TAC `z:A` THEN ASM_CASES_TAC `(z:A) IN prob_carrier p` THEN
       ASM_REWRITE_TAC[] THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `z:A`) THEN ASM_REWRITE_TAC[] THEN
       REAL_ARITH_TAC;
       MATCH_MP_TAC PROB_COMPL_IN_EVENTS THEN
       UNDISCH_TAC `simple_rv (p:A prob_space) (X:A->real)` THEN
       REWRITE_TAC[simple_rv; random_variable] THEN MESON_TAC[]];
      ASM_SIMP_TAC[PROB_COMPL]];
     ASM_REWRITE_TAC[binom; BINOM_REFL] THEN
     CONV_TAC NUM_REDUCE_CONV THEN
     REWRITE_TAC[real_pow; REAL_POW_1; REAL_MUL_LID; REAL_MUL_RID]]]);;


(* ========================================================================= *)
(* Auxiliary: first and second moment identities for binomial sums         *)
(* These are derived from the REAL_BINOMIAL_THEOREM via differentiation.   *)
(* ========================================================================= *)

let SUM_BINOMIAL_FIRST_MOMENT = prove
  (`!n q. sum(0..n)
      (\k. &k * &(binom(n,k)) * q pow k * (&1 - q) pow (n - k)) = &n * q`,
   REPEAT GEN_TAC THEN
   SUBGOAL_THEN
     `!x:real y:real.
       sum(0..n) (\k. &k * &(binom(n,k)) * x pow (k - 1) * y pow (n - k)) =
       &n * (x + y) pow (n - 1)`
     (LABEL_TAC "deriv") THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
    MAP_EVERY EXISTS_TAC
     [`\x:real. sum(0..n)
        (\k. &(binom(n,k)) * x pow k * (y:real) pow (n - k))`;
      `x:real`] THEN
    SUBGOAL_THEN
      `!x:real. sum(0..n)
        (\k. &(binom(n,k)) * x pow k * (y:real) pow (n - k)) =
        (x + y) pow n`
      (LABEL_TAC "bt") THENL
    [REWRITE_TAC[REAL_BINOMIAL_THEOREM]; ALL_TAC] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG];
     ASM_REWRITE_TAC[]] THEN
    REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
   REMOVE_THEN "deriv" (MP_TAC o SPECL [`q:real`; `&1 - q`]) THEN
   REWRITE_TAC[REAL_SUB_ADD2; REAL_POW_ONE; REAL_MUL_RID] THEN
   DISCH_THEN(SUBST1_TAC o SYM) THEN
   REWRITE_TAC[GSYM SUM_RMUL] THEN
   MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
   REWRITE_TAC[REAL_ARITH
     `(k * b * xk * y) * x:real = k * b * (x * xk) * y`] THEN
   REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
   DISJ_CASES_TAC(ARITH_RULE `k = 0 \/ SUC(k - 1) = k`) THEN
   ASM_REWRITE_TAC[REAL_MUL_LZERO]);;

(* Second central moment identity from BERNSTEIN_LEMMA *)
let SUM_BINOMIAL_SECOND_MOMENT = prove
  (`!n q. sum(0..n)
      (\k. (&k - &n * q) pow 2 *
           &(binom(n,k)) * q pow k * (&1 - q) pow (n - k)) =
      &n * q * (&1 - q)`,
   REPEAT GEN_TAC THEN
   MP_TAC(SPECL [`n:num`; `q:real`] BERNSTEIN_LEMMA) THEN
   REWRITE_TAC[bernstein] THEN
   MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
   CONV_TAC REAL_RING);;


(* ========================================================================= *)
(* Binomial expectation and variance via simple_expectation                *)
(* ========================================================================= *)

(* E[X] = n*q for Binomial(n,q) *)
let BINOMIAL_RV_EXPECTATION = prove
  (`!p:A prob_space X n q.
      binomial_rv p X n q ==> simple_expectation p X = &n * q`,
   REPEAT GEN_TAC THEN REWRITE_TAC[binomial_rv] THEN STRIP_TAC THEN
   REWRITE_TAC[simple_expectation] THEN
   SUBGOAL_THEN `IMAGE (X:A->real) (prob_carrier p) SUBSET {&k | k <= n}`
     ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `FINITE (IMAGE (X:A->real) (prob_carrier p))` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `IMAGE (\k:num. &k) (0..n)` THEN CONJ_TAC THENL
    [MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_NUMSEG];
     FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
       (REWRITE_RULE[IMP_CONJ] SUBSET_TRANS)) THEN
     REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE; IN_NUMSEG; LE_0] THEN
     MESON_TAC[]];
    ALL_TAC] THEN
   SUBGOAL_THEN `{v:real | v IN IMAGE (X:A->real) (prob_carrier p)} =
                  IMAGE X (prob_carrier p)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM]; ALL_TAC] THEN
   SUBGOAL_THEN
     `sum (IMAGE (X:A->real) (prob_carrier p))
       (\v. v * prob p {x:A | x IN prob_carrier p /\ (X:A->real) x = v}) =
      sum (IMAGE (\k:num. &k) (0..n))
       (\v. v * prob (p:A prob_space)
                  {x:A | x IN prob_carrier p /\ (X:A->real) x = v})`
     SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN CONJ_TAC THENL
    [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
       (REWRITE_RULE[IMP_CONJ] SUBSET_TRANS)) THEN
     REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE; IN_NUMSEG; LE_0] THEN
     MESON_TAC[];
     X_GEN_TAC `v:real` THEN
     REWRITE_TAC[IN_IMAGE; IN_NUMSEG; LE_0] THEN STRIP_TAC THEN
     SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ (X:A->real) x = v} = {}`
       (fun th -> REWRITE_TAC[th; PROB_EMPTY; REAL_MUL_RZERO]) THEN
     REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
     ASM_MESON_TAC[]];
    ALL_TAC] THEN
   SIMP_TAC[FINITE_NUMSEG; SUM_IMAGE; IN_NUMSEG; LE_0; REAL_OF_NUM_EQ] THEN
   REWRITE_TAC[o_DEF] THEN BETA_TAC THEN
   SUBGOAL_THEN
     `!k. k IN 0..n ==>
       &k * prob (p:A prob_space)
              {x:A | x IN prob_carrier p /\ (X:A->real) x = &k} =
       &k * &(binom(n,k)) * q pow k * (&1 - q) pow (n - k)`
     (fun th -> SIMP_TAC[th; SUM_EQ]) THENL
   [X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_NUMSEG; LE_0] THEN
    DISCH_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUM_BINOMIAL_FIRST_MOMENT]]);;

let SUM_BINOMIAL_SECOND_RAW_MOMENT = prove
  (`!n q. sum(0..n)
      (\k. &k pow 2 * &(binom(n,k)) * q pow k * (&1 - q) pow (n - k)) =
      &n * q * (&1 - q) + (&n * q) pow 2`,
   REPEAT GEN_TAC THEN
   SUBGOAL_THEN
     `!k. k IN 0..n ==>
       &k pow 2 * &(binom(n,k)) * q pow k * (&1 - q) pow (n - k) =
       (&k - &n * q) pow 2 * &(binom(n,k)) * q pow k *
         (&1 - q) pow (n - k) +
       &2 * (&n * q) * &k * &(binom(n,k)) * q pow k *
         (&1 - q) pow (n - k) -
       (&n * q) pow 2 * &(binom(n,k)) * q pow k * (&1 - q) pow (n - k)`
     ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   SUBGOAL_THEN
     `sum(0..n) (\k. &k pow 2 * &(binom(n,k)) * q pow k *
                      (&1 - q) pow (n - k)) =
      sum(0..n) (\k.
        (&k - &n * q) pow 2 * &(binom(n,k)) * q pow k *
          (&1 - q) pow (n - k) +
        &2 * (&n * q) * &k * &(binom(n,k)) * q pow k *
          (&1 - q) pow (n - k) -
        (&n * q) pow 2 * &(binom(n,k)) * q pow k *
          (&1 - q) pow (n - k))`
     SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[IN_NUMSEG] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(REWRITE_RULE[IN_NUMSEG] th)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   REWRITE_TAC[SUM_SUB_NUMSEG; SUM_ADD_NUMSEG; SUM_LMUL] THEN
   REWRITE_TAC[SUM_BINOMIAL_SECOND_MOMENT; SUM_BINOMIAL_FIRST_MOMENT] THEN
   REWRITE_TAC[GSYM bernstein; SUM_BERNSTEIN] THEN REAL_ARITH_TAC);;

(* Var(X) = n*q*(1-q) for Binomial(n,q) *)
let BINOMIAL_RV_VARIANCE = prove
  (`!p:A prob_space X n q.
      binomial_rv p X n q ==> simple_variance p X = &n * q * (&1 - q)`,
   REPEAT GEN_TAC THEN REWRITE_TAC[binomial_rv] THEN STRIP_TAC THEN
   SUBGOAL_THEN `simple_expectation (p:A prob_space) X = &n * q`
     ASSUME_TAC THENL
   [MATCH_MP_TAC BINOMIAL_RV_EXPECTATION THEN
    ASM_REWRITE_TAC[binomial_rv]; ALL_TAC] THEN
   ASM_SIMP_TAC[SIMPLE_VARIANCE_ALT] THEN
   (* Suffices to show E[X^2] = nq(1-q) + (nq)^2 *)
   SUBGOAL_THEN
     `simple_expectation (p:A prob_space) (\x:A. (X:A->real) x pow 2) =
      &n * q * (&1 - q) + (&n * q) pow 2`
     (fun th -> REWRITE_TAC[th] THEN REAL_ARITH_TAC) THEN
   REWRITE_TAC[simple_expectation] THEN
   SUBGOAL_THEN
     `{v:real | v IN IMAGE (\x:A. (X:A->real) x pow 2) (prob_carrier p)} =
      IMAGE (\x. X x pow 2) (prob_carrier p)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM]; ALL_TAC] THEN
   SUBGOAL_THEN
     `IMAGE (\x:A. (X:A->real) x pow 2) (prob_carrier p) SUBSET
      IMAGE (\k:num. (&k) pow 2) (0..n)`
     ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_IMAGE; IN_NUMSEG; LE_0] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
   (* Extend sum to IMAGE (\k. (&k)^2) (0..n) *)
   SUBGOAL_THEN
     `sum (IMAGE (\x:A. (X:A->real) x pow 2) (prob_carrier p))
       (\v. v * prob p
              {x:A | x IN prob_carrier p /\ (X:A->real) x pow 2 = v}) =
      sum (IMAGE (\k:num. (&k) pow 2) (0..n))
       (\v. v * prob (p:A prob_space)
              {x:A | x IN prob_carrier p /\ (X:A->real) x pow 2 = v})`
     SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     X_GEN_TAC `v:real` THEN REWRITE_TAC[IN_IMAGE; IN_NUMSEG; LE_0] THEN
     STRIP_TAC THEN
     SUBGOAL_THEN
       `{x:A | x IN prob_carrier p /\ (X:A->real) x pow 2 = v} = {}`
       (fun th -> REWRITE_TAC[th; PROB_EMPTY; REAL_MUL_RZERO]) THEN
     REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
     X_GEN_TAC `z:A` THEN STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[] THEN
     EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   (* Apply SUM_IMAGE using injectivity of k |-> (&k)^2 on naturals *)
   MP_TAC(ISPECL [`\k:num. (&k) pow 2`;
     `\v:real. v * prob (p:A prob_space)
       {x:A | x IN prob_carrier p /\ (X:A->real) x pow 2 = v}`;
     `0..n`] SUM_IMAGE) THEN
   ANTS_TAC THENL
   [BETA_TAC THEN REWRITE_TAC[IN_NUMSEG; LE_0] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&x = &y` (fun th -> REWRITE_TAC[GSYM REAL_OF_NUM_EQ; th]) THEN
    MATCH_MP_TAC REAL_POW_EQ THEN EXISTS_TAC `2` THEN
    ASM_REWRITE_TAC[REAL_POS] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[o_DEF] THEN BETA_TAC] THEN
   (* Now: sum(0..n)(\k. (&k)^2 * P({X^2 = (&k)^2})) = nq(1-q) + (nq)^2 *)
   (* Show {X^2 = (&k)^2} = {X = &k} using non-negativity, then substitute *)
   SUBGOAL_THEN
     `!k. k IN 0..n ==>
       &k pow 2 * prob (p:A prob_space)
         {x:A | x IN prob_carrier p /\ (X:A->real) x pow 2 = (&k) pow 2} =
       &k pow 2 * &(binom(n,k)) * q pow k * (&1 - q) pow (n - k)`
     (fun th -> SIMP_TAC[th; SUM_EQ]) THENL
   [X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_NUMSEG; LE_0] THEN
    DISCH_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\ (X:A->real) x pow 2 = (&k) pow 2} =
       {x | x IN prob_carrier p /\ X x = &k}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `z:A` THEN
     ASM_CASES_TAC `(z:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
     EQ_TAC THENL
     [DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:A`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(X:A->real) z = &k`
        (fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC REAL_POW_EQ THEN EXISTS_TAC `2` THEN
      ASM_REWRITE_TAC[REAL_POS] THEN ARITH_TAC;
      DISCH_TAC THEN ASM_REWRITE_TAC[]];
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[SUM_BINOMIAL_SECOND_RAW_MOMENT]]);;


(* ========================================================================= *)
(* Poisson distribution                                                     *)
(* ========================================================================= *)

(* The Poisson distribution has infinite support {0,1,2,...}, so it cannot   *)
(* be a simple_rv. We work with its PMF as an analytic object and prove     *)
(* normalization and the Poisson limit theorem.                             *)

(* Real exponential power series: exp(x) = sum_{n=0}^infty x^n/n! *)
let REAL_EXP_CONVERGES = prove
  (`!x. ((\n. x pow n / &(FACT n)) real_sums exp(x)) (from 0)`,
   GEN_TAC THEN REWRITE_TAC[REAL_SUMS_COMPLEX] THEN
   SUBGOAL_THEN `Cx o (\n. x pow n / &(FACT n)) =
     (\n. Cx(x) pow n / Cx(&(FACT n)))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; CX_DIV; CX_POW];
    REWRITE_TAC[CX_EXP] THEN ACCEPT_TAC(SPEC `Cx(x:real)` CEXP_CONVERGES)]);;

(* Poisson PMF: P(X = k) = e^{-lam} * lam^k / k! *)
let poisson_pmf = new_definition
  `poisson_pmf (lam:real) (k:num) = exp(--lam) * lam pow k / &(FACT k)`;;

(* The Poisson PMF sums to 1 *)
let POISSON_PMF_SUMS = prove
  (`!lam. (poisson_pmf lam real_sums &1) (from 0)`,
   GEN_TAC THEN
   SUBGOAL_THEN `poisson_pmf lam =
     (\k. exp(--lam) * lam pow k / &(FACT k))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; poisson_pmf]; ALL_TAC] THEN
   SUBGOAL_THEN `&1 = exp(--lam) * exp(lam)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_ADD_LINV; REAL_EXP_0];
    MATCH_MP_TAC REAL_SERIES_LMUL THEN REWRITE_TAC[REAL_EXP_CONVERGES]]);;

(* Poisson PMF is non-negative *)
let POISSON_PMF_POS = prove
  (`!lam k. &0 <= lam ==> &0 <= poisson_pmf lam k`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[poisson_pmf] THEN
   MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LE];
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_POS]]);;

(* ========================================================================= *)
(* Auxiliary limit lemmas for the Poisson limit theorem                     *)
(* ========================================================================= *)

(* If f(n+1) -> l then f(n) -> l *)
let REALLIM_SHIFT_SUC = prove
  (`!f l. ((\n. f(SUC n)) ---> l) sequentially ==> (f ---> l) sequentially`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   X_GEN_TAC `e:real` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
   DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
   EXISTS_TAC `N + 1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
   SUBGOAL_THEN `?m. n = SUC m /\ N <= m` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `n - 1` THEN ASM_ARITH_TAC; ASM_SIMP_TAC[]]);;

(* (1 - c/n)^n -> e^{-c} for c > 0 (shifted version of REALLIM_POW_EXP_NEG) *)
let REALLIM_POW_EXP_NEG' = prove
  (`!c. &0 < c ==> ((\n. (&1 - c / &n) pow n) ---> exp(--c)) sequentially`,
   REPEAT STRIP_TAC THEN MATCH_MP_TAC REALLIM_SHIFT_SUC THEN
   REWRITE_TAC[ADD1] THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP REALLIM_POW_EXP_NEG) THEN
   REWRITE_TAC[ADD1]);;

(* (n - k) / n -> 1 as n -> infinity *)
let REALLIM_RATIO_TO_1 = prove
  (`!k. ((\n. &(n - k) / &n) ---> &1) sequentially`,
   GEN_TAC THEN
   MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
   EXISTS_TAC `\n:num. &1 - &k / &n` THEN CONJ_TAC THENL
   [REWRITE_TAC[] THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `k + 1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `k <= n /\ 0 < n` STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
    MATCH_MP_TAC(REAL_FIELD `&0 < n ==> &1 - k / n = (n - k) / n`) THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`sequentially:(num)net`; `(\n:num. &1):num->real`;
                    `(\n:num. &k / &n):num->real`; `&1`; `&0`] REALLIM_SUB) THEN
    REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
    [REWRITE_TAC[REALLIM_CONST];
     REWRITE_TAC[real_div] THEN
     SUBGOAL_THEN `&0 = &k * &0` SUBST1_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REALLIM_LMUL THEN REWRITE_TAC[REALLIM_1_OVER_N]]]]);;

(* binom(n,k) / n^k -> 1/k! as n -> infinity *)
let REALLIM_BINOM_OVER_NPOWER = prove
  (`!k. ((\n. &(binom(n,k)) / &n pow k) ---> inv(&(FACT k))) sequentially`,
   INDUCT_TAC THENL
   [REWRITE_TAC[binom; FACT; real_pow; REAL_INV_1; REAL_DIV_1;
                REALLIM_CONST];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `inv(&(FACT(SUC k))) = inv(&(FACT k)) * inv(&(SUC k))`
     SUBST1_TAC THENL
   [REWRITE_TAC[FACT; GSYM REAL_OF_NUM_MUL; REAL_INV_MUL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN
     `((\n. &(binom(n,SUC k)) / &n pow SUC k) --->
       inv(&(FACT k)) * inv(&(SUC k))) sequentially`
     MP_TAC THENL
   [ALL_TAC; REWRITE_TAC[]] THEN
   MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
   EXISTS_TAC `\n. (&(binom(n,k)) / &n pow k) *
                    (&(n - k) / (&n * &(SUC k)))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `SUC k` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `k <= n /\ 0 < n` STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(&n = &0)` ASSUME_TAC THENL
    [REWRITE_TAC[REAL_OF_NUM_EQ] THEN
     UNDISCH_TAC `0 < n` THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(&n pow k = &0)` ASSUME_TAC THENL
    [ASM_SIMP_TAC[REAL_POW_EQ_0] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(&(SUC k) = &0)` ASSUME_TAC THENL
    [REWRITE_TAC[REAL_OF_NUM_EQ; NOT_SUC]; ALL_TAC] THEN
    SUBGOAL_THEN `SUC k * binom(n,SUC k) = (n - k) * binom(n,k)`
      ASSUME_TAC THENL
    [MP_TAC(SPECL [`n:num`; `k:num`] BINOM_BOTTOM_STEP) THEN
     REWRITE_TAC[ADD1]; ALL_TAC] THEN
    SUBGOAL_THEN
      `&(binom(n,SUC k)) = &((n - k) * binom(n,k)) / &(SUC k)`
      SUBST1_TAC THENL
    [SUBGOAL_THEN
       `&(SUC k) * &(binom(n,SUC k)) = &((n - k) * binom(n,k))`
       MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_EQ] THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[REAL_FIELD
        `~(a = &0) ==> (a * b = c <=> b = c / a)`]];
     ALL_TAC] THEN
    REWRITE_TAC[real_pow; GSYM REAL_OF_NUM_MUL] THEN
    ASM_SIMP_TAC[REAL_FIELD
      `~(nk = &0) /\ ~(n = &0) /\ ~(sk = &0) ==>
       ((nk' * bnk) / sk) / (n * nk) =
       (bnk / nk) * (nk' / (n * sk))`];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `inv(&(FACT k)) * inv(&(SUC k)) =
      inv(&(FACT k)) * (&1 * inv(&(SUC k)))`
     SUBST1_TAC THENL
   [REWRITE_TAC[REAL_MUL_LID]; ALL_TAC] THEN
   MATCH_MP_TAC REALLIM_MUL THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN
     `(\n. &(n - k) / (&n * &(SUC k))) =
      (\n. (&(n - k) / &n) * inv(&(SUC k)))`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REALLIM_RMUL THEN REWRITE_TAC[REALLIM_RATIO_TO_1]]);;


(* ========================================================================= *)
(* Poisson limit theorem                                                    *)
(* ========================================================================= *)

(* Bin(n, lam/n) -> Poisson(lam) pointwise as n -> infinity *)
let POISSON_LIMIT = prove
  (`!k lam. &0 < lam ==>
      ((\n. &(binom(n,k)) * (lam / &n) pow k *
            (&1 - lam / &n) pow (n - k))
       ---> poisson_pmf lam k) sequentially`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[poisson_pmf] THEN
   SUBGOAL_THEN
     `exp(--lam) * lam pow k / &(FACT k) =
      inv(&(FACT k)) * (lam pow k * exp(--lam))`
     SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
   EXISTS_TAC `\n. (&(binom(n,k)) / &n pow k) *
     (lam pow k * (&1 - lam / &n) pow (n - k))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    MP_TAC(SPEC `lam:real` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
    EXISTS_TAC `M + k + 1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(&n pow k = &0)` ASSUME_TAC THENL
    [REWRITE_TAC[REAL_POW_EQ_0; REAL_OF_NUM_EQ; DE_MORGAN_THM] THEN
     DISJ1_TAC THEN UNDISCH_TAC `M + k + 1 <= n` THEN ARITH_TAC;
     ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_DIV] THEN
    ASM_SIMP_TAC[REAL_FIELD
      `~(nk = &0) ==> b / nk * (lk * rest) = b * lk / nk * rest`];
    ALL_TAC] THEN
   MATCH_MP_TAC REALLIM_MUL THEN REWRITE_TAC[REALLIM_BINOM_OVER_NPOWER] THEN
   MATCH_MP_TAC REALLIM_LMUL THEN
   MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
   EXISTS_TAC `\n. (&1 - lam / &n) pow n / (&1 - lam / &n) pow k` THEN
   CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    MP_TAC(SPEC `lam:real` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `P:num`) THEN
    EXISTS_TAC `P + k + 1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC(GSYM REAL_POW_SUB) THEN CONJ_TAC THENL
    [SUBGOAL_THEN `lam < &n` ASSUME_TAC THENL
      [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&P` THEN
       ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
       UNDISCH_TAC `P + k + 1 <= n` THEN ARITH_TAC;
       ALL_TAC] THEN
     SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
      [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `lam / &n < &1` MP_TAC THENL
      [ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
       REAL_ARITH_TAC];
     UNDISCH_TAC `P + k + 1 <= n` THEN ARITH_TAC];
    ALL_TAC] THEN
   SUBGOAL_THEN `exp(--lam) = exp(--lam) / &1` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_DIV_1]; ALL_TAC] THEN
   MATCH_MP_TAC REALLIM_DIV THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REALLIM_POW_EXP_NEG']; ALL_TAC] THEN
   CONJ_TAC THENL
   [SUBGOAL_THEN `((\n:num. &1 - lam / &n) ---> &1) sequentially`
      MP_TAC THENL
    [MP_TAC(ISPECL [`sequentially:(num)net`; `(\n:num. &1):num->real`;
                     `(\n:num. lam / &n):num->real`; `&1`; `&0`]
       REALLIM_SUB) THEN
     REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_THEN MATCH_MP_TAC THEN
     CONJ_TAC THENL
     [REWRITE_TAC[REALLIM_CONST];
      REWRITE_TAC[real_div] THEN
      SUBGOAL_THEN `&0 = lam * &0` SUBST1_TAC THENL
      [REAL_ARITH_TAC;
       MATCH_MP_TAC REALLIM_LMUL THEN REWRITE_TAC[REALLIM_1_OVER_N]]];
     DISCH_TAC THEN
     SUBGOAL_THEN `&1 = &1 pow k`
       (fun th -> ONCE_REWRITE_TAC[th]) THENL
     [REWRITE_TAC[REAL_POW_ONE]; ALL_TAC] THEN
     MATCH_MP_TAC REALLIM_POW THEN ASM_REWRITE_TAC[REAL_POW_ONE]];
    REAL_ARITH_TAC]);;


(* ========================================================================= *)
(* Geometric distribution                                                    *)
(* ========================================================================= *)

(* PMF: geometric_pmf p k = p * (1-p)^k for k = 0, 1, 2, ...              *)
(* Counts the number of failures before the first success.                   *)

let geometric_pmf = new_definition
  `geometric_pmf (p:real) (k:num) = p * (&1 - p) pow k`;;

(* The Geometric PMF sums to 1 *)
let GEOMETRIC_PMF_SUMS = prove
  (`!p. &0 < p /\ p <= &1
        ==> (geometric_pmf p real_sums &1) (from 0)`,
   GEN_TAC THEN DISCH_TAC THEN
   SUBGOAL_THEN
     `((\k. p * (&1 - p) pow k) real_sums
       (p * ((&1 - p) pow 0 / (&1 - (&1 - p))))) (from 0)`
     MP_TAC THENL
   [MATCH_MP_TAC REAL_SERIES_LMUL THEN
    MATCH_MP_TAC REAL_SUMS_GP THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `p * (&1 - p) pow 0 / (&1 - (&1 - p)) = &1` SUBST1_TAC THENL
   [REWRITE_TAC[real_pow; REAL_MUL_RID] THEN
    SUBGOAL_THEN `&1 - (&1 - p) = p` SUBST1_TAC THENL
    [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(p = &0)` ASSUME_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_DIV_REFL; REAL_DIV_LMUL];
    ALL_TAC] THEN
   SUBGOAL_THEN `geometric_pmf p = (\k. p * (&1 - p) pow k)`
     (fun th -> REWRITE_TAC[th]) THEN
   REWRITE_TAC[FUN_EQ_THM; geometric_pmf]);;

(* Non-negativity of the Geometric PMF *)
let GEOMETRIC_PMF_POS = prove
  (`!p k. &0 <= p /\ p <= &1 ==> &0 <= geometric_pmf p k`,
   REPEAT GEN_TAC THEN DISCH_TAC THEN
   REWRITE_TAC[geometric_pmf] THEN
   MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC]);;


(* ========================================================================= *)
(* Analytic infrastructure for the Geometric mean                            *)
(* ========================================================================= *)

(* Derivative of the finite geometric sum:                                   *)
(* d/dx[sum_{k=0}^n x^k] = sum_{k=0}^n k*x^{k-1}                          *)
(*                        = (1 - (n+1)*x^n + n*x^{n+1}) / (1-x)^2          *)
let SUM_GP_DERIVATIVE = prove
  (`!n x:real. ~(x = &1) ==>
     sum(0..n) (\k. &k * x pow (k - 1)) =
     (&1 - &(SUC n) * x pow n + &n * x pow (SUC n)) / (&1 - x) pow 2`,
   REPEAT GEN_TAC THEN DISCH_TAC THEN
   MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
   MAP_EVERY EXISTS_TAC
     [`\x:real. sum(0..n) (\k. x pow k)`; `x:real`] THEN
   SUBGOAL_THEN
     `!x:real. sum(0..n) (\k. x pow k) =
       if x = &1 then &(SUC n) else (&1 - x pow (SUC n)) / (&1 - x)`
     (LABEL_TAC "gp") THENL
   [GEN_TAC THEN REWRITE_TAC[SUM_GP] THEN
    SUBGOAL_THEN `~(n < 0)` (fun th -> REWRITE_TAC[th]) THENL
    [ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THENL
    [ASM_REWRITE_TAC[REAL_POW_ONE; SUB_0] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_pow; REAL_MUL_LID; SUB_0];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
   MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
   EXISTS_TAC `\x. (&1 - x pow (SUC n)) / (&1 - x)` THEN
   EXISTS_TAC `abs(x - &1)` THEN
   CONJ_TAC THENL
   [UNDISCH_TAC `~(x = &1)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
   CONJ_TAC THENL
   [X_GEN_TAC `x':real` THEN DISCH_TAC THEN
    REMOVE_THEN "gp" (MP_TAC o SPEC `x':real`) THEN
    SUBGOAL_THEN `~(x' = &1)` (fun th -> REWRITE_TAC[th]) THENL
    [UNDISCH_TAC `abs(x' - x) < abs(x - &1)` THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
   REAL_DIFF_TAC THEN
   CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `SUC n - 1 = n` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[real_pow; REAL_MUL_LID; REAL_MUL_RID] THEN
   SUBGOAL_THEN `&(SUC n) = &n + &1` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   REAL_ARITH_TAC);;

(* Closed form for sum_{k=0}^n k * x^k *)
let SUM_KX_POW = prove
  (`!n z:real. ~(z = &1) ==>
     sum(0..n) (\k. &k * z pow k) =
     z * (&1 - &(SUC n) * z pow n + &n * z pow (SUC n)) /
     (&1 - z) pow 2`,
   REPEAT GEN_TAC THEN DISCH_TAC THEN
   MP_TAC(SPECL [`n:num`; `z:real`] SUM_GP_DERIVATIVE) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   SUBGOAL_THEN
     `sum(0..n) (\k. &k * z pow k) =
      z * sum(0..n) (\k. &k * z pow (k - 1))`
     SUBST1_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
   SPEC_TAC(`n:num`, `n:num`) THEN INDUCT_TAC THENL
   [REWRITE_TAC[SUM_SING_NUMSEG] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
   ASM_REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
   AP_TERM_TAC THEN
   SUBGOAL_THEN `SUC n' - 1 = n'` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[real_pow; REAL_MUL_AC]);;

(* Real version of n * z^n -> 0, derived from complex LIM_N_TIMES_POWN *)
let REALLIM_N_TIMES_POWN = prove
  (`!z:real. abs z < &1 ==> ((\n. &n * z pow n) ---> &0) sequentially`,
   GEN_TAC THEN DISCH_TAC THEN
   REWRITE_TAC[REALLIM_COMPLEX; o_DEF; CX_MUL; CX_POW] THEN
   MP_TAC(SPEC `Cx(z)` LIM_N_TIMES_POWN) THEN
   REWRITE_TAC[COMPLEX_NORM_CX] THEN ASM_REWRITE_TAC[]);;

(* Infinite series: sum_{k=0}^{inf} k * x^k = x / (1-x)^2 *)
let REAL_SUMS_KX_POW = prove
  (`!x. abs(x) < &1 ==>
     ((\k. &k * x pow k) real_sums (x / (&1 - x) pow 2)) (from 0)`,
   GEN_TAC THEN DISCH_TAC THEN
   SUBGOAL_THEN `~(x = &1)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `~((&1 - x) pow 2 = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_EQ_0; ARITH] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[real_sums; FROM_0; INTER_UNIV] THEN
   ASM_SIMP_TAC[SUM_KX_POW] THEN
   SUBGOAL_THEN `x / (&1 - x) pow 2 = x * &1 / (&1 - x) pow 2`
     SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REALLIM_LMUL THEN
   MATCH_MP_TAC REALLIM_DIV THEN ASM_REWRITE_TAC[REALLIM_CONST] THEN
   (* Need (1 - (SUC n)*x^n + n*x^{SUC n}) -> 1 *)
   SUBGOAL_THEN `((\n. &(SUC n) * x pow n) ---> &0) sequentially`
     ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
    SUBGOAL_THEN `&0 = &0 + &0` SUBST1_TAC THENL
    [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
    [MATCH_MP_TAC REALLIM_N_TIMES_POWN THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC REALLIM_POWN THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
   EXISTS_TAC `\n:num. (&1 - &(SUC n) * x pow n) + &n * x pow (SUC n)` THEN
   CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
    REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   MP_TAC(ISPECL [`sequentially:(num)net`;
                   `\n:num. &1 - &(SUC n) * x pow n`;
                   `\n:num. &n * x pow (SUC n)`;
                   `&1`; `&0`] REALLIM_ADD) THEN
   REWRITE_TAC[REAL_ADD_RID] THEN
   DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`sequentially:(num)net`;
                     `\n:num. &1`;
                     `\n:num. &(SUC n) * x pow n`;
                     `&1`; `&0`] REALLIM_SUB) THEN
    REWRITE_TAC[REAL_SUB_RZERO] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[REALLIM_CONST] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   REWRITE_TAC[real_pow] THEN
   SUBGOAL_THEN `(\n. &n * x * x pow n) = (\n. x * (&n * x pow n))`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 = x * &0` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REALLIM_LMUL THEN
   MATCH_MP_TAC REALLIM_N_TIMES_POWN THEN ASM_REWRITE_TAC[]);;

(* Mean of Geometric distribution: E[X] = (1-p)/p *)
let GEOMETRIC_MEAN_SERIES = prove
  (`!p. &0 < p /\ p <= &1
        ==> ((\k. &k * geometric_pmf p k) real_sums (&1 - p) / p) (from 0)`,
   GEN_TAC THEN DISCH_TAC THEN
   SUBGOAL_THEN `(\k. &k * geometric_pmf p k) = (\k. p * (&k * (&1 - p) pow k))`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; geometric_pmf] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `(&1 - p) / p = p * ((&1 - p) / (&1 - (&1 - p)) pow 2)`
     SUBST1_TAC THENL
   [SUBGOAL_THEN `&1 - (&1 - p) = p` SUBST1_TAC THENL
    [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(p = &0)` ASSUME_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    ASM_SIMP_TAC[REAL_FIELD
      `~(p = &0) ==> p * (&1 - p) / (p * p) = (&1 - p) / p`];
    MATCH_MP_TAC REAL_SERIES_LMUL THEN
    MATCH_MP_TAC REAL_SUMS_KX_POW THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
    ASM_REAL_ARITH_TAC]);;

(* ====================================================================== *)
(* Geometric variance: Var(X) = (1-p)/p^2                                 *)
(* ====================================================================== *)

(* Analytic infrastructure: second derivative of finite GP sum *)

let REAL_POW_OFFSET2 = prove
 (`!x:real k. 2 <= k ==> x pow k = x pow 2 * x pow (k - 2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_POW_ADD] THEN
  AP_TERM_TAC THEN ASM_ARITH_TAC);;

let REALLIM_NSQUARED_TIMES_POWN = prove
 (`!z:real. abs z < &1
            ==> ((\n. &n pow 2 * z pow n) ---> &0) sequentially`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. (&n * sqrt(abs z) pow n) pow 2` THEN CONJ_TAC THENL
  [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_NUM] THEN
   REWRITE_TAC[REAL_POW_MUL; REAL_POW_2] THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[GSYM REAL_POW_MUL] THEN
   SUBGOAL_THEN `sqrt(abs z) * sqrt(abs z) = abs z` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_2; SQRT_POW2] THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC];
   ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_NULL_POW THEN CONJ_TAC THENL
  [MATCH_MP_TAC REALLIM_N_TIMES_POWN THEN
   SUBGOAL_THEN `&0 <= sqrt(abs z)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
   SUBGOAL_THEN `&1 = sqrt(&1)` SUBST1_TAC THENL
   [REWRITE_TAC[SQRT_1]; ALL_TAC] THEN
   REWRITE_TAC[SQRT_MONO_LT_EQ] THEN ASM_REAL_ARITH_TAC;
   ARITH_TAC]);;

let POLY_IDENTITY = prove
 (`!A B C N y:real.
     B = A * y /\ C = B * y
     ==> (--((N + &1) * N * A) + N * (N + &1) * B) * (&1 - y) * (&1 - y) -
         (&1 - (N + &1) * B + N * C) * &2 * (&1 - y) * -- &1 =
         (&2 - N * (N + &1) * A +
          &2 * (N - &1) * (N + &1) * B - N * (N - &1) * C) *
         (&1 - y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RING);;

let SUM_GP_SECOND_DERIVATIVE = prove
 (`!n x:real. ~(x = &1) ==>
   sum(0..n) (\k. &k * (&k - &1) * x pow (k - 2)) =
   (&2 - &n * &(SUC n) * x pow (n - 1) +
    &2 * (&n - &1) * &(SUC n) * x pow n -
    &n * (&n - &1) * x pow (SUC n)) / (&1 - x) pow 3`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
  MAP_EVERY EXISTS_TAC
    [`\x:real. sum(0..n) (\k. &k * x pow (k - 1))`; `x:real`] THEN
  SUBGOAL_THEN
    `!x:real. ~(x = &1) ==>
     sum(0..n) (\k. &k * x pow (k - 1)) =
     (&1 - &(SUC n) * x pow n + &n * x pow (SUC n)) / (&1 - x) pow 2`
    (LABEL_TAC "deriv1") THENL
  [MATCH_ACCEPT_TAC SUM_GP_DERIVATIVE; ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
   REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN REWRITE_TAC[REAL_MUL_RID] THEN
   ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `1 <= k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&(k - 1) = &k - &1` SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_OF_NUM_SUB]; ALL_TAC] THEN
   SUBGOAL_THEN `k - 1 - 1 = k - 2` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REFL_TAC];
   ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC
    `\x. (&1 - &(SUC n) * x pow n + &n * x pow (SUC n)) /
         (&1 - x) pow 2` THEN
  EXISTS_TAC `abs(x - &1)` THEN
  CONJ_TAC THENL
  [UNDISCH_TAC `~(x = &1)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
  [X_GEN_TAC `x':real` THEN DISCH_TAC THEN
   SUBGOAL_THEN `~(x' = &1)` ASSUME_TAC THENL
   [UNDISCH_TAC `abs(x' - x) < abs(x - &1)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   REMOVE_THEN "deriv1" (MP_TAC o SPEC `x':real`) THEN
   ASM_REWRITE_TAC[] THEN SIMP_TAC[];
   ALL_TAC] THEN
  REAL_DIFF_TAC THEN
  CONJ_TAC THENL
  [REWRITE_TAC[REAL_POW_EQ_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_SUB_LZERO] THEN
  SUBGOAL_THEN `SUC n - 1 = n` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `2 - 1 = 1` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_1] THEN
  SUBGOAL_THEN `~(&1 - x = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~((&1 - x) pow 4 = &0) /\ ~((&1 - x) pow 3 = &0)`
    ASSUME_TAC THENL
  [REWRITE_TAC[REAL_POW_EQ_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[REAL_FIELD
    `~(c pow 4 = &0) /\ ~(c pow 3 = &0) ==>
     (a / c pow 4 = b / c pow 3 <=> a = b * c)`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_POW_2] THEN
  ASM_CASES_TAC `n = 0` THENL
  [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
   REWRITE_TAC[real_pow; REAL_MUL_LZERO; REAL_MUL_RZERO;
     REAL_ADD_LID; REAL_SUB_RZERO; REAL_SUB_LZERO; REAL_NEG_0;
     REAL_ADD_RID; REAL_MUL_LID; REAL_MUL_RID] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `1 <= n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC POLY_IDENTITY THEN
  CONJ_TAC THENL
  [SUBGOAL_THEN `n = SUC(n - 1)`
     (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
   [ASM_ARITH_TAC; REWRITE_TAC[real_pow; REAL_MUL_AC]];
   REWRITE_TAC[real_pow; REAL_MUL_AC]]);;

let SUM_KK1X_POW = prove
 (`!n z:real. ~(z = &1) ==>
   sum(0..n) (\k. &k * (&k - &1) * z pow k) =
   z pow 2 * (&2 - &n * &(SUC n) * z pow (n - 1) +
              &2 * (&n - &1) * &(SUC n) * z pow n -
              &n * (&n - &1) * z pow (SUC n)) / (&1 - z) pow 3`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `(\k. &k * (&k - &1) * z pow k) =
     (\k. z pow 2 * (&k * (&k - &1) * z pow (k - 2)))` SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
   ASM_CASES_TAC `i < 2` THENL
   [SUBGOAL_THEN `i = 0 \/ i = 1` DISJ_CASES_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `2 <= i` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_POW_OFFSET2] THEN REWRITE_TAC[REAL_MUL_AC];
   ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN
  ASM_SIMP_TAC[SUM_GP_SECOND_DERIVATIVE] THEN
  REWRITE_TAC[real_div; REAL_MUL_AC]);;

let POW_PRED = prove
 (`!x:real n. ~(x = &0) /\ 1 <= n ==> x pow (n - 1) = x pow n * inv x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_EQ_RCANCEL_IMP THEN EXISTS_TAC `x:real` THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(RAND_CONV(REWR_CONV(GSYM REAL_MUL_ASSOC))) THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_MUL_RID] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_POW_1] THEN
  REWRITE_TAC[GSYM REAL_POW_ADD] THEN
  SUBGOAL_THEN `n - 1 + 1 = n` (fun th -> REWRITE_TAC[th]) THEN
  ASM_ARITH_TAC);;

(* Limit of the numerator in the second derivative GP closed form *)
let NUMERATOR_LIMIT = prove
 (`!x:real. abs x < &1
   ==> ((\n. &2 - &n * &(SUC n) * x pow (n - 1) +
             &2 * (&n - &1) * &(SUC n) * x pow n -
             &n * (&n - &1) * x pow (SUC n)) ---> &2) sequentially`,
  GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `x = &0` THENL
  [ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
   EXISTS_TAC `\n:num. &2` THEN CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `2` THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `1 <= n - 1 /\ ~(n - 1 = 0) /\ ~(SUC n = 0) /\ ~(n = 0)`
      STRIP_ASSUME_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_POW_ZERO] THEN REAL_ARITH_TAC;
    REWRITE_TAC[REALLIM_CONST]];
   ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\n:num. &2 + (-- inv(x) + &2 - x) * (&n pow 2 * x pow n) +
                           (-- inv(x) + x) * (&n * x pow n) +
                           (-- &2) * x pow n` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
   REPEAT STRIP_TAC THEN BETA_TAC THEN
   ASM_SIMP_TAC[POW_PRED] THEN
   REWRITE_TAC[real_pow; GSYM REAL_OF_NUM_SUC] THEN
   REWRITE_TAC[REAL_POW_2] THEN
   SUBGOAL_THEN `inv(x) * x = &1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_MUL_LINV]; ALL_TAC] THEN
   CONV_TAC REAL_RING;
   ALL_TAC] THEN
  SUBGOAL_THEN `&2 = &2 + &0`
    (fun th -> GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [th]) THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
  [REWRITE_TAC[REALLIM_CONST]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 = &0 + &0`
    (fun th -> GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [th]) THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
  [SUBGOAL_THEN `&0 = (-- inv x + &2 - x) * &0` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REALLIM_LMUL THEN
   MATCH_MP_TAC REALLIM_NSQUARED_TIMES_POWN THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 = &0 + &0`
    (fun th -> GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [th]) THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
  [SUBGOAL_THEN `&0 = (-- inv x + x) * &0` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REALLIM_LMUL THEN
   MATCH_MP_TAC REALLIM_N_TIMES_POWN THEN ASM_REWRITE_TAC[];
   SUBGOAL_THEN `&0 = (-- &2) * &0` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REALLIM_LMUL THEN
   MATCH_MP_TAC REALLIM_POWN THEN ASM_REWRITE_TAC[]]);;

(* Infinite series: sum of k*(k-1)*x^k *)
let REAL_SUMS_KK1X_POW = prove
 (`!x:real. abs x < &1
   ==> ((\k. &k * (&k - &1) * x pow k) real_sums
        (&2 * x pow 2 / (&1 - x) pow 3)) (from 0)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[real_sums; FROM_INTER_NUMSEG] THEN
  ASM_CASES_TAC `x = &1` THENL
  [ASM_MESON_TAC[REAL_ARITH `~(abs(&1) < &1)`]; ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_KK1X_POW] THEN
  SUBGOAL_THEN `~((&1 - x) pow 3 = &0)` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_POW_EQ_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `(\n. x pow 2 * (&2 - &n * &(SUC n) * x pow (n - 1) +
      &2 * (&n - &1) * &(SUC n) * x pow n -
      &n * (&n - &1) * x pow (SUC n)) / (&1 - x) pow 3) =
     (\n. x pow 2 / (&1 - x) pow 3 *
      (&2 - &n * &(SUC n) * x pow (n - 1) +
       &2 * (&n - &1) * &(SUC n) * x pow n -
       &n * (&n - &1) * x pow (SUC n)))` SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
   ASM_SIMP_TAC[real_div; REAL_INV_MUL; REAL_MUL_AC];
   ALL_TAC] THEN
  SUBGOAL_THEN `&2 * x pow 2 / (&1 - x) pow 3 =
                x pow 2 / (&1 - x) pow 3 * &2` SUBST1_TAC THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_LMUL THEN
  MATCH_MP_TAC NUMERATOR_LIMIT THEN ASM_REWRITE_TAC[]);;

(* Second factorial moment: E[X(X-1)] = 2(1-p)^2/p^2 *)
let GEOMETRIC_SECOND_FACTORIAL_MOMENT = prove
 (`!p. &0 < p /\ p <= &1
   ==> ((\k. &k * (&k - &1) * geometric_pmf p k) real_sums
        (&2 * (&1 - p) pow 2 / p pow 2)) (from 0)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(p = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `(\k. &k * (&k - &1) * geometric_pmf p k) =
     (\k. p * (&k * (&k - &1) * (&1 - p) pow k))` SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; geometric_pmf] THEN GEN_TAC THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `&2 * (&1 - p) pow 2 / p pow 2 =
     p * (&2 * (&1 - p) pow 2 / (&1 - (&1 - p)) pow 3)` SUBST1_TAC THENL
  [SUBGOAL_THEN `&1 - (&1 - p) = p` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_FIELD
     `~(p = &0) ==>
      p * &2 * (&1 - p) pow 2 / p pow 3 =
      &2 * (&1 - p) pow 2 / p pow 2`];
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_SERIES_LMUL THEN
  MATCH_MP_TAC REAL_SUMS_KK1X_POW THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  ASM_REAL_ARITH_TAC);;

(* Second moment: E[X^2] = 2(1-p)^2/p^2 + (1-p)/p *)
let GEOMETRIC_SECOND_MOMENT = prove
 (`!p. &0 < p /\ p <= &1
   ==> ((\k. &k pow 2 * geometric_pmf p k) real_sums
        (&2 * (&1 - p) pow 2 / p pow 2 + (&1 - p) / p)) (from 0)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `(\k. &k pow 2 * geometric_pmf p k) =
     (\k. &k * (&k - &1) * geometric_pmf p k +
          &k * geometric_pmf p k)` SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
   REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_SERIES_ADD THEN
  ASM_SIMP_TAC[GEOMETRIC_SECOND_FACTORIAL_MOMENT; GEOMETRIC_MEAN_SERIES]);;

(* Variance: Var(X) = (1-p)/p^2 *)
let GEOMETRIC_VARIANCE_SERIES = prove
 (`!p. &0 < p /\ p <= &1
   ==> ((\k. (&k - (&1 - p) / p) pow 2 * geometric_pmf p k) real_sums
        (&1 - p) / p pow 2) (from 0)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(p = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `((\k. &k pow 2 * geometric_pmf p k) real_sums
     (&2 * (&1 - p) pow 2 / p pow 2 + (&1 - p) / p)) (from 0)` ASSUME_TAC
    THENL [ASM_SIMP_TAC[GEOMETRIC_SECOND_MOMENT]; ALL_TAC] THEN
  SUBGOAL_THEN
    `((\k. &k * geometric_pmf p k) real_sums (&1 - p) / p) (from 0)`
    ASSUME_TAC THENL
    [ASM_SIMP_TAC[GEOMETRIC_MEAN_SERIES]; ALL_TAC] THEN
  SUBGOAL_THEN `(geometric_pmf p real_sums &1) (from 0)` ASSUME_TAC THENL
    [ASM_SIMP_TAC[GEOMETRIC_PMF_SUMS]; ALL_TAC] THEN
  SUBGOAL_THEN
    `((\k. (-- &2 * (&1 - p) / p) * &k * geometric_pmf p k) real_sums
     (-- &2 * (&1 - p) / p) * (&1 - p) / p) (from 0)` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_SERIES_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `((\k. ((&1 - p) / p) pow 2 * geometric_pmf p k) real_sums
     ((&1 - p) / p) pow 2 * &1) (from 0)` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_SERIES_LMUL THEN ASM_REWRITE_TAC[ETA_AX];
     ALL_TAC] THEN
  SUBGOAL_THEN
    `((\k. &k pow 2 * geometric_pmf p k +
           (-- &2 * (&1 - p) / p) * &k * geometric_pmf p k) real_sums
     (&2 * (&1 - p) pow 2 / p pow 2 + (&1 - p) / p) +
     (-- &2 * (&1 - p) / p) * (&1 - p) / p) (from 0)` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_SERIES_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `((\k. (&k pow 2 * geometric_pmf p k +
            (-- &2 * (&1 - p) / p) * &k * geometric_pmf p k) +
           ((&1 - p) / p) pow 2 * geometric_pmf p k) real_sums
     ((&2 * (&1 - p) pow 2 / p pow 2 + (&1 - p) / p) +
      (-- &2 * (&1 - p) / p) * (&1 - p) / p) +
     ((&1 - p) / p) pow 2 * &1) (from 0)` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_SERIES_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `(\k. (&k - (&1 - p) / p) pow 2 * geometric_pmf p k) =
     (\k. (&k pow 2 * geometric_pmf p k +
           (-- &2 * (&1 - p) / p) * &k * geometric_pmf p k) +
          ((&1 - p) / p) pow 2 * geometric_pmf p k)` SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
   REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `(&1 - p) / p pow 2 =
     ((&2 * (&1 - p) pow 2 / p pow 2 + (&1 - p) / p) +
      (-- &2 * (&1 - p) / p) * (&1 - p) / p) +
     ((&1 - p) / p) pow 2 * &1` SUBST1_TAC THENL
  [REWRITE_TAC[REAL_MUL_RID] THEN
   UNDISCH_TAC `~(p = &0)` THEN CONV_TAC REAL_FIELD;
   ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* ====================================================================== *)
(* Negative binomial distribution: NB(r, p)                               *)
(* Counts failures before the r-th success in Bernoulli(p) trials.        *)
(* PMF: binom(k+r-1, k) * p^r * (1-p)^k                                  *)
(* ====================================================================== *)

(* ---------------------------------------------------------------------- *)
(* Infrastructure: polynomial times geometric -> 0                        *)
(* ---------------------------------------------------------------------- *)

(* General: n^r * z^n -> 0 for |z| < 1, by induction on r.
   Base: z^n -> 0. Step: compare with n * sqrt(|z|)^n using IH. *)
let REALLIM_POW_TIMES_POWN = prove
 (`!r z. abs z < &1
         ==> ((\n. &n pow r * z pow n) ---> &0) sequentially`,
  INDUCT_TAC THENL
  [REWRITE_TAC[real_pow; REAL_MUL_LID] THEN REWRITE_TAC[REALLIM_POWN];
   ALL_TAC] THEN
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(INST_TYPE [`:num`,`:A`] REALLIM_NULL_COMPARISON) THEN
  EXISTS_TAC `\n. &n * sqrt(abs z) pow n` THEN CONJ_TAC THENL
  [SUBGOAL_THEN `abs(sqrt(abs z)) < &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= sqrt(abs z)` ASSUME_TAC THENL
    [MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    SUBGOAL_THEN `&1 = sqrt(&1)` SUBST1_TAC THENL
    [REWRITE_TAC[SQRT_1]; ALL_TAC] THEN
    REWRITE_TAC[SQRT_MONO_LT_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `sqrt(abs z)`) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   SUBGOAL_THEN
     `eventually (\n. &n pow r * sqrt(abs z) pow n <= &1) sequentially`
     MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[REALLIM_SEQUENTIALLY]) THEN
    DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
    REWRITE_TAC[REAL_SUB_RZERO; EVENTUALLY_SEQUENTIALLY] THEN
    MESON_TAC[REAL_ARITH `abs x < &1 ==> x <= &1`];
    ALL_TAC] THEN
   MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
   REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
   REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_NUM] THEN
   SUBGOAL_THEN `abs z pow n = sqrt(abs z) pow n * sqrt(abs z) pow n`
     SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_ADD; GSYM MULT_2; GSYM REAL_POW_POW] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(SPEC `abs(z:real)` SQRT_POW_2) THEN
    REWRITE_TAC[REAL_ABS_POS] THEN MESON_TAC[];
    ALL_TAC] THEN
   REWRITE_TAC[real_pow; REAL_MUL_ASSOC] THEN
   SUBGOAL_THEN
     `((&n * &n pow r) * sqrt(abs z) pow n) * sqrt(abs z) pow n =
      &n * (&n pow r * sqrt(abs z) pow n) * sqrt(abs z) pow n`
     SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `sqrt(abs z) pow n = &1 * sqrt(abs z) pow n`
     (fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC SQRT_POS_LE THEN
    REAL_ARITH_TAC];
   ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_N_TIMES_POWN THEN
  SUBGOAL_THEN `&0 <= sqrt(abs z)` ASSUME_TAC THENL
  [MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  SUBGOAL_THEN `&1 = sqrt(&1)` SUBST1_TAC THENL
  [REWRITE_TAC[SQRT_1]; ALL_TAC] THEN
  REWRITE_TAC[SQRT_MONO_LT_EQ] THEN ASM_REAL_ARITH_TAC);;

(* Binomial coefficient bound: binom(n,k) <= n^k *)
let BINOM_LE_POW = prove
 (`!n k. binom(n,k) <= n EXP k`,
  INDUCT_TAC THENL
  [INDUCT_TAC THEN REWRITE_TAC[binom; EXP; LE_REFL; LE_0]; ALL_TAC] THEN
  INDUCT_TAC THENL
  [REWRITE_TAC[binom; EXP; LE_REFL]; ALL_TAC] THEN
  REWRITE_TAC[binom; EXP] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `n EXP (SUC k) + n EXP k` THEN CONJ_TAC THENL
  [MATCH_MP_TAC LE_ADD2 THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `SUC k`) THEN REWRITE_TAC[];
    ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  REWRITE_TAC[EXP] THEN
  SUBGOAL_THEN `n * n EXP k + n EXP k = SUC n * n EXP k`
    SUBST1_TAC THENL
  [REWRITE_TAC[MULT_CLAUSES]; ALL_TAC] THEN
  MATCH_MP_TAC LE_MULT2 THEN REWRITE_TAC[LE_REFL; LE] THEN
  MATCH_MP_TAC EXP_MONO_LE_IMP THEN ARITH_TAC);;

(* Symmetry of binom on sum: binom(m+n, m) = binom(m+n, n) *)
let BINOM_SYMM_ADD = prove
 (`!m n. binom(m + n, m) = binom(m + n, n)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`n:num`; `m:num`] BINOM_FACT) THEN
  MP_TAC(SPECL [`m:num`; `n:num`] BINOM_FACT) THEN
  REWRITE_TAC[ARITH_RULE `n + m = m + n:num`] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `FACT m * FACT n * binom(m + n, n) =
     FACT m * FACT n * binom(m + n, m)` MP_TAC THENL
  [ASM_MESON_TAC[MULT_AC]; ALL_TAC] THEN
  REWRITE_TAC[EQ_MULT_LCANCEL; MULT_EQ_0; FACT_NZ] THEN
  MESON_TAC[]);;

(* Binomial coefficient times geometric -> 0 *)
let REALLIM_BINOM_POWN = prove
 (`!r z. abs z < &1
         ==> ((\N. &(binom(N + r, r)) * z pow N) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(INST_TYPE [`:num`,`:A`] REALLIM_NULL_COMPARISON) THEN
  EXISTS_TAC `\N. &((N + r) EXP r) * abs(z) pow N` THEN CONJ_TAC THENL
  [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW] THEN
   MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_ABS_NUM; REAL_OF_NUM_LE; BINOM_LE_POW];
    MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  MATCH_MP_TAC(INST_TYPE [`:num`,`:A`] REALLIM_NULL_COMPARISON) THEN
  EXISTS_TAC `\N. &2 pow r * (&N pow r * abs(z) pow N)` THEN CONJ_TAC THENL
  [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `r:num` THEN
   X_GEN_TAC `N:num` THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
   REWRITE_TAC[REAL_ABS_NUM; REAL_ABS_POW] THEN
   REWRITE_TAC[REAL_ARITH `abs(abs z) = abs z`] THEN
   REWRITE_TAC[REAL_MUL_ASSOC] THEN
   MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(2 * N) EXP r` THEN CONJ_TAC THENL
    [MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_ARITH_TAC;
     REWRITE_TAC[MULT_EXP] THEN ARITH_TAC];
    MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 = &2 pow r * &0` SUBST1_TAC THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_LMUL THEN
  MATCH_MP_TAC REALLIM_POW_TIMES_POWN THEN
  ASM_REAL_ARITH_TAC);;

(* ---------------------------------------------------------------------- *)
(* Core series identity: NB generating function                           *)
(* sum_{k=0}^{inf} binom(k+n, k) * x^k = inv((1-x)^{n+1})              *)
(* ---------------------------------------------------------------------- *)

(* binom(n,n) = 1 for all n *)
let BINOM_DIAG = prove
 (`!n. binom(n,n) = 1`,
  GEN_TAC THEN
  MP_TAC(SPECL [`0`; `n:num`] BINOM_FACT) THEN
  REWRITE_TAC[ADD_CLAUSES; FACT; MULT_CLAUSES] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `FACT n * binom(n,n) = FACT n * 1` MP_TAC THENL
  [ASM_REWRITE_TAC[MULT_CLAUSES]; ALL_TAC] THEN
  REWRITE_TAC[EQ_MULT_LCANCEL; FACT_NZ]);;

(* Pascal identity in the form needed for telescoping *)
let BINOM_PASCAL_ADD = prove
 (`!N n. binom(SUC N + SUC n, SUC N) =
         binom(N + SUC n, SUC N) + binom(N + SUC n, N)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `SUC N + SUC n = SUC(N + SUC n)` SUBST1_TAC THENL
  [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[binom]);;

(* Finite telescoping: (1-x) * sum B(k+n+1,k)*x^k = sum B(k+n,k)*x^k - error *)
let NB_SERIES_TELESCOPING = prove
 (`!n x N.
    (&1 - x) * sum(0..N) (\k. &(binom(k + SUC n, k)) * x pow k) =
    sum(0..N) (\k. &(binom(k + n, k)) * x pow k) -
    &(binom(N + SUC n, N)) * x pow (SUC N)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_REFL] THEN
   REWRITE_TAC[ADD_CLAUSES; binom; real_pow; REAL_MUL_RID; REAL_MUL_LID] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `&(binom(SUC N + SUC n, SUC N)) =
                 &(binom(N + SUC n, SUC N)) + &(binom(N + SUC n, N))`
    SUBST1_TAC THENL
  [REWRITE_TAC[GSYM REAL_OF_NUM_ADD; BINOM_PASCAL_ADD]; ALL_TAC] THEN
  SUBGOAL_THEN `N + SUC n = SUC N + n` (fun th -> REWRITE_TAC[th]) THENL
  [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_pow] THEN CONV_TAC REAL_RING);;

(* The negative binomial generating function *)
let NB_SERIES = prove
 (`!n x. abs x < &1 ==>
    ((\k. &(binom(k + n, k)) * x pow k) real_sums
     inv((&1 - x) pow (SUC n))) (from 0)`,
  INDUCT_TAC THENL
  [GEN_TAC THEN DISCH_TAC THEN
   SUBGOAL_THEN `(\k. &(binom(k + 0, k)) * x pow k) = (\k. x pow k)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; ADD_CLAUSES; BINOM_DIAG; REAL_MUL_LID];
    ALL_TAC] THEN
   SUBGOAL_THEN `inv((&1 - x) pow SUC 0) = x pow 0 / (&1 - x)`
     SUBST1_TAC THENL
   [REWRITE_TAC[real_pow; REAL_MUL_LID; REAL_POW_1; real_div; REAL_MUL_LID;
                REAL_MUL_RID]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_SUMS_GP THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(&1 - x = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN
  ASM_REWRITE_TAC[real_sums; FROM_0; INTER_UNIV] THEN DISCH_TAC THEN
  REWRITE_TAC[real_sums; FROM_0; INTER_UNIV] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\N. inv(&1 - x) *
    (sum(0..N) (\k. &(binom(k + n, k)) * x pow k) -
     &(binom(N + SUC n, N)) * x pow (SUC N))` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
   REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
   MP_TAC(SPECL [`n:num`; `x:real`; `n':num`] NB_SERIES_TELESCOPING) THEN
   DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
   ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_MUL_LID];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `inv((&1 - x) pow SUC(SUC n)) =
     inv(&1 - x) * (inv((&1 - x) pow SUC n) - &0)` SUBST1_TAC THENL
  [REWRITE_TAC[REAL_SUB_RZERO; real_pow; REAL_INV_MUL]; ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_LMUL THEN
  MATCH_MP_TAC REALLIM_SUB THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\N. &(binom(N + SUC n, N)) * x pow SUC N) =
                 (\N. x * (&(binom(N + SUC n, SUC n)) * x pow N))` SUBST1_TAC
  THENL
  [REWRITE_TAC[FUN_EQ_THM; BINOM_SYMM_ADD; real_pow] THEN
   GEN_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 = x * &0` SUBST1_TAC THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_LMUL THEN
  MATCH_MP_TAC REALLIM_BINOM_POWN THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Negative Binomial Distribution NB(r, p)                                   *)
(* r = number of successes, p = success probability, k = number of failures  *)
(* PMF: binom(k+r-1, k) * p^r * (1-p)^k                                    *)
(* ========================================================================= *)

let neg_binomial_pmf = new_definition
  `neg_binomial_pmf r p k =
     &(binom(k + r - 1, k)) * p pow r * (&1 - p) pow k`;;

(* Non-negativity of negative binomial PMF *)
let NEG_BINOMIAL_PMF_POS = prove
 (`!r p k. &0 < p /\ p <= &1 ==> &0 <= neg_binomial_pmf r p k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[neg_binomial_pmf] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
  [REAL_ARITH_TAC;
   MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
   MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC]);;

(* Normalization: negative binomial PMF sums to 1 *)
let NEG_BINOMIAL_PMF_SUMS = prove
 (`!r p. 1 <= r /\ &0 < p /\ p <= &1
         ==> ((\k. neg_binomial_pmf r p k) real_sums &1) (from 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[neg_binomial_pmf] THEN
  SUBGOAL_THEN `(\k. &(binom(k + r - 1, k)) * p pow r * (&1 - p) pow k) =
                (\k. p pow r * &(binom(k + r - 1, k)) * (&1 - p) pow k)`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(p pow r = &0)` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_POW_EQ_0; DE_MORGAN_THM] THEN
   DISJ1_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(&1 - p) < &1` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `SUC(r - 1) = r` ASSUME_TAC THENL
  [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`r - 1`; `&1 - p`] NB_SERIES) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&1 - (&1 - p) = p` SUBST1_TAC THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_SERIES_LMUL) THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(p:real) pow r`) THEN
  REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV]);;

(* Geometric distribution is negative binomial with r = 1 *)
let GEOMETRIC_IS_NEG_BINOMIAL_1 = prove
 (`!p k. geometric_pmf p k = neg_binomial_pmf 1 p k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[geometric_pmf; neg_binomial_pmf] THEN
  REWRITE_TAC[ARITH_RULE `k + 1 - 1 = k`; BINOM_DIAG; real_pow] THEN
  REAL_ARITH_TAC);;

(* Binomial coefficient diagonal identity:
   k * binom(k+r-1, k) = r * binom(k+r-1, k-1)
   Used for computing moments of the negative binomial. *)
let BINOM_KBINOM_IDENTITY = prove
 (`!k r. 1 <= k /\ 1 <= r
         ==> k * binom(k + r - 1, k) = r * binom(k + r - 1, k - 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`r - 1`; `k:num`] BINOM_FACT) THEN
  MP_TAC(SPECL [`r:num`; `k - 1`] BINOM_FACT) THEN
  SUBGOAL_THEN `r - 1 + k = k + r - 1` (fun th -> REWRITE_TAC[th]) THENL
  [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r + (k - 1) = k + r - 1` (fun th -> REWRITE_TAC[th]) THENL
  [ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `FACT k = k * FACT(k - 1)` ASSUME_TAC THENL
  [SUBGOAL_THEN `k = SUC(k - 1)` (fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
   [ASM_ARITH_TAC; REWRITE_TAC[FACT]] THEN
   SUBGOAL_THEN `SUC(k - 1) = k` (fun th -> REWRITE_TAC[th]) THEN
   ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `FACT r = r * FACT(r - 1)` ASSUME_TAC THENL
  [SUBGOAL_THEN `r = SUC(r - 1)` (fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
   [ASM_ARITH_TAC; REWRITE_TAC[FACT]] THEN
   SUBGOAL_THEN `SUC(r - 1) = r` (fun th -> REWRITE_TAC[th]) THEN
   ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `FACT(r - 1) * FACT(k - 1) * (k * binom(k + r - 1, k)) =
     FACT(k + r - 1) /\
     FACT(r - 1) * FACT(k - 1) * (r * binom(k + r - 1, k - 1)) =
     FACT(k + r - 1)`
    MP_TAC THENL
  [CONJ_TAC THEN ASM_MESON_TAC[MULT_AC]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
    `FACT(r - 1) * (FACT(k - 1) * (k * binom(k + r - 1, k))) =
     FACT(r - 1) * (FACT(k - 1) * (r * binom(k + r - 1, k - 1)))`
    MP_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[EQ_MULT_LCANCEL; FACT_NZ]);;

(* Mean of negative binomial: E[X] = r * (1-p) / p *)
let NEG_BINOMIAL_MEAN_SERIES = prove
 (`!r p. 1 <= r /\ &0 < p /\ p <= &1
         ==> ((\k. &k * neg_binomial_pmf r p k) real_sums &r * (&1 - p) / p)
             (from 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[neg_binomial_pmf] THEN
  MP_TAC(SPECL
    [`\k. &k * &(binom (k + r - 1,k)) * p pow r * (&1 - p) pow k`;
     `&r * (&1 - p) / p`; `1`; `0`]
    REAL_SUMS_OFFSET_REV) THEN
  REWRITE_TAC[ARITH; SUM_SING_NUMSEG] THEN
  SUBGOAL_THEN `&0 * &(binom (0 + r - 1,0)) * p pow r * (&1 - p) pow 0 = &0`
    (fun th -> REWRITE_TAC[th]) THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RID] THEN
  DISCH_TAC THEN FIRST_ASSUM(fun th -> MATCH_MP_TAC th) THEN
  POP_ASSUM(K ALL_TAC) THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [ARITH_RULE `1 = 0 + 1`] THEN
  REWRITE_TAC[GSYM(SPEC `1` REAL_SUMS_REINDEX)] THEN
  SUBGOAL_THEN `!x:num. (x + 1) + r - 1 = x + r`
    (fun th -> REWRITE_TAC[th]) THENL
  [GEN_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `(\x. &(x + 1) * &(binom (x + r,x + 1)) * p pow r * (&1 - p) pow (x + 1)) =
     (\x. &r * (&1 - p) * p pow r * (&(binom(x + r, x)) * (&1 - p) pow x))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:num` THEN
   SUBGOAL_THEN `(x + 1) * binom(x + r, x + 1) = r * binom(x + r, x)`
     ASSUME_TAC THENL
   [MP_TAC(SPECL [`x + 1`; `r:num`] BINOM_KBINOM_IDENTITY) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(x + 1) + r - 1 = x + r` (fun th -> REWRITE_TAC[th]) THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(x + 1) - 1 = x` (fun th -> REWRITE_TAC[th]) THEN
    ARITH_TAC;
    ALL_TAC] THEN
   FIRST_X_ASSUM(ASSUME_TAC o
     REWRITE_RULE[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_EQ]) THEN
   ONCE_REWRITE_TAC[ARITH_RULE `x + 1 = SUC x`] THEN
   REWRITE_TAC[CONJUNCT2 real_pow; REAL_MUL_ASSOC] THEN
   ONCE_REWRITE_TAC[ADD1] THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `abs(&1 - p) < &1` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`r:num`; `&1 - p`] NB_SERIES) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&1 - (&1 - p) = p` SUBST1_TAC THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_SERIES_LMUL) THEN
  DISCH_THEN(MP_TAC o SPEC `&r * (&1 - p) * p pow r`) THEN REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
    `(\x:num. &r * (&1 - p) * p pow r * &(binom (x + r,x)) * (&1 - p) pow x) =
     (\n. (&r * (&1 - p) * p pow r) * &(binom (n + r,n)) * (&1 - p) pow n)`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `&r * (&1 - p) / p = (&r * (&1 - p) * p pow r) * inv(p pow SUC r)`
    SUBST1_TAC THENL
  [REWRITE_TAC[real_div; real_pow; REAL_INV_MUL] THEN
   SUBGOAL_THEN `~(p = &0)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `~(p pow r = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_EQ_0; DE_MORGAN_THM] THEN
    DISJ1_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `p pow r * inv(p pow r) = &1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_MUL_RINV]; ALL_TAC] THEN
   REWRITE_TAC[REAL_MUL_ASSOC] THEN
   SUBGOAL_THEN `(((&r * (&1 - p)) * p pow r) * inv p) * inv (p pow r) =
                 ((&r * (&1 - p)) * inv p) * (p pow r * inv (p pow r))`
     SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[REAL_MUL_RID];
   ASM_REWRITE_TAC[]]);;

(* Double diagonal identity for second factorial moments *)
let BINOM_KBINOM_IDENTITY2 = prove
 (`!k r. 2 <= k /\ 1 <= r
         ==> k * (k - 1) * binom(k + r - 1, k) =
             r * (r + 1) * binom(k + r - 1, k - 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `k * binom(k + r - 1, k) = r * binom(k + r - 1, k - 1)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC BINOM_KBINOM_IDENTITY THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`k - 1`; `r + 1`] BINOM_KBINOM_IDENTITY) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `k - 1 + (r + 1) - 1 = k + r - 1 /\ k - 1 - 1 = k - 2`
    (fun th -> REWRITE_TAC[th]) THENL
  [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[MULT_ASSOC] THEN
  SUBGOAL_THEN `(k * (k - 1)) * binom(k + r - 1, k) =
                (k - 1) * (k * binom(k + r - 1, k))` SUBST1_TAC THENL
  [ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(k - 1) * r * binom(k + r - 1, k - 1) =
                r * ((k - 1) * binom(k + r - 1, k - 1))` SUBST1_TAC THENL
  [ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* Second factorial moment: E[X(X-1)] = r(r+1)((1-p)/p)^2 *)
let NEG_BINOMIAL_SECOND_FACTORIAL_MOMENT = prove
 (`!r p. 1 <= r /\ &0 < p /\ p <= &1
         ==> ((\k. &k * (&k - &1) * neg_binomial_pmf r p k) real_sums
              &r * (&r + &1) * ((&1 - p) / p) pow 2) (from 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[neg_binomial_pmf] THEN
  ABBREV_TAC
    `f = \k. &k * (&k - &1) * &(binom (k + r - 1,k)) *
             p pow r * (&1 - p) pow k` THEN
  MP_TAC(SPECL [`f:num->real`;
    `&r * (&r + &1) * ((&1 - p) / p) pow 2`; `2`; `0`]
    REAL_SUMS_OFFSET_REV) THEN
  REWRITE_TAC[ARITH] THEN
  SUBGOAL_THEN `sum (0..1) f = &0` (fun th -> REWRITE_TAC[th]) THENL
  [EXPAND_TAC "f" THEN
   REWRITE_TAC[num_CONV `1`; SUM_CLAUSES_NUMSEG; LE_0] THEN
   CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RID] THEN
  DISCH_TAC THEN FIRST_ASSUM(fun th -> MATCH_MP_TAC th) THEN
  POP_ASSUM(K ALL_TAC) THEN EXPAND_TAC "f" THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [ARITH_RULE `2 = 0 + 2`] THEN
  REWRITE_TAC[GSYM(SPEC `2` REAL_SUMS_REINDEX)] THEN
  SUBGOAL_THEN `!x:num. (x + 2) + r - 1 = x + r + 1`
    (fun th -> REWRITE_TAC[th]) THENL
  [GEN_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x:num. &(x + 2) - &1 = &(x + 1)`
    (fun th -> REWRITE_TAC[th]) THENL
  [GEN_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `(\x. &(x + 2) * &(x + 1) * &(binom (x + r + 1,x + 2)) *
          p pow r * (&1 - p) pow (x + 2)) =
     (\x. &r * (&r + &1) * (&1 - p) pow 2 * p pow r *
          (&(binom(x + (r + 1), x)) * (&1 - p) pow x))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:num` THEN
   SUBGOAL_THEN `(x + 2) * (x + 1) * binom(x + r + 1, x + 2) =
                 r * (r + 1) * binom(x + r + 1, x)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`x + 2`; `r:num`] BINOM_KBINOM_IDENTITY2) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(x + 2) + r - 1 = x + r + 1`
      (fun th -> REWRITE_TAC[th]) THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(x + 2) - 1 = x + 1 /\ (x + 2) - 2 = x`
      (fun th -> REWRITE_TAC[th]) THEN
    ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `(&1 - p) pow (x + 2) = (&1 - p) pow 2 * (&1 - p) pow x`
     SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
   FIRST_X_ASSUM(ASSUME_TAC o
     REWRITE_RULE[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_EQ]) THEN
   SUBGOAL_THEN `x + r + 1 = x + (r + 1)` (fun th -> REWRITE_TAC[th]) THENL
   [ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&(r + 1) = &r + &1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[REAL_MUL_ASSOC]) THEN
   REWRITE_TAC[REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `abs(&1 - p) < &1` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`r + 1`; `&1 - p`] NB_SERIES) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&1 - (&1 - p) = p` SUBST1_TAC THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_SERIES_LMUL) THEN
  DISCH_THEN(MP_TAC o SPEC `&r * (&r + &1) * (&1 - p) pow 2 * p pow r`) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `(\x:num. &r * (&r + &1) * (&1 - p) pow 2 * p pow r *
              &(binom (x + (r + 1),x)) * (&1 - p) pow x) =
     (\n. (&r * (&r + &1) * (&1 - p) pow 2 * p pow r) *
          &(binom (n + (r + 1),n)) * (&1 - p) pow n)`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `&r * (&r + &1) * ((&1 - p) / p) pow 2 =
     (&r * (&r + &1) * (&1 - p) pow 2 * p pow r) * inv (p pow SUC (r + 1))`
    SUBST1_TAC THENL
  [REWRITE_TAC[REAL_POW_DIV; real_div; REAL_MUL_ASSOC] THEN
   SUBGOAL_THEN `~(p = &0)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `~(p pow r = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_EQ_0; DE_MORGAN_THM] THEN
    DISJ1_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `SUC(r + 1) = 2 + r` (fun th -> REWRITE_TAC[th]) THENL
   [ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_POW_ADD; REAL_INV_MUL] THEN
   SUBGOAL_THEN `p pow r * inv(p pow r) = &1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_MUL_RINV]; ALL_TAC] THEN
   REWRITE_TAC[REAL_MUL_ASSOC] THEN
   SUBGOAL_THEN
     `((((&r * (&r + &1)) * (&1 - p) pow 2) * p pow r) * inv (p pow 2)) *
      inv (p pow r) =
      (((&r * (&r + &1)) * (&1 - p) pow 2) * inv (p pow 2)) *
      (p pow r * inv(p pow r))`
     SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[REAL_MUL_RID];
   ASM_REWRITE_TAC[]]);;

(* Variance of negative binomial: Var(X) = r(1-p)/p^2 *)
let NEG_BINOMIAL_VARIANCE_SERIES = prove
 (`!r p. 1 <= r /\ &0 < p /\ p <= &1
         ==> ((\k. (&k - &r * (&1 - p) / p) pow 2 * neg_binomial_pmf r p k)
              real_sums &r * (&1 - p) / p pow 2) (from 0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `((\k. &k * (&k - &1) * neg_binomial_pmf r p k) real_sums
     &r * (&r + &1) * ((&1 - p) / p) pow 2) (from 0)` ASSUME_TAC THENL
  [ASM_SIMP_TAC[NEG_BINOMIAL_SECOND_FACTORIAL_MOMENT]; ALL_TAC] THEN
  SUBGOAL_THEN
    `((\k. &k * neg_binomial_pmf r p k) real_sums &r * (&1 - p) / p)
     (from 0)` ASSUME_TAC THENL
  [ASM_SIMP_TAC[NEG_BINOMIAL_MEAN_SERIES]; ALL_TAC] THEN
  SUBGOAL_THEN
    `((\k. neg_binomial_pmf r p k) real_sums &1) (from 0)` ASSUME_TAC THENL
  [ASM_SIMP_TAC[NEG_BINOMIAL_PMF_SUMS]; ALL_TAC] THEN
  SUBGOAL_THEN
    `((\k. (-- &2 * &r * (&1 - p) / p) * &k * neg_binomial_pmf r p k)
      real_sums (-- &2 * &r * (&1 - p) / p) * &r * (&1 - p) / p)
     (from 0)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_SERIES_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `((\k. (&r * (&1 - p) / p) pow 2 * neg_binomial_pmf r p k) real_sums
     (&r * (&1 - p) / p) pow 2 * &1) (from 0)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_SERIES_LMUL THEN ASM_REWRITE_TAC[ETA_AX];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `((\k. &k * (&k - &1) * neg_binomial_pmf r p k +
           &k * neg_binomial_pmf r p k) real_sums
     &r * (&r + &1) * ((&1 - p) / p) pow 2 + &r * (&1 - p) / p)
     (from 0)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_SERIES_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `((\k. (&k * (&k - &1) * neg_binomial_pmf r p k +
            &k * neg_binomial_pmf r p k) +
           (-- &2 * &r * (&1 - p) / p) * &k * neg_binomial_pmf r p k)
      real_sums
     (&r * (&r + &1) * ((&1 - p) / p) pow 2 + &r * (&1 - p) / p) +
     (-- &2 * &r * (&1 - p) / p) * &r * (&1 - p) / p) (from 0)` ASSUME_TAC
    THENL
  [MATCH_MP_TAC REAL_SERIES_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `((\k. ((&k * (&k - &1) * neg_binomial_pmf r p k +
             &k * neg_binomial_pmf r p k) +
            (-- &2 * &r * (&1 - p) / p) * &k * neg_binomial_pmf r p k) +
           (&r * (&1 - p) / p) pow 2 * neg_binomial_pmf r p k) real_sums
     ((&r * (&r + &1) * ((&1 - p) / p) pow 2 + &r * (&1 - p) / p) +
      (-- &2 * &r * (&1 - p) / p) * &r * (&1 - p) / p) +
     (&r * (&1 - p) / p) pow 2 * &1) (from 0)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_SERIES_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `(\k. (&k - &r * (&1 - p) / p) pow 2 * neg_binomial_pmf r p k) =
     (\k. ((&k * (&k - &1) * neg_binomial_pmf r p k +
             &k * neg_binomial_pmf r p k) +
            (-- &2 * &r * (&1 - p) / p) * &k * neg_binomial_pmf r p k) +
           (&r * (&1 - p) / p) pow 2 * neg_binomial_pmf r p k)`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
   REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `&r * (&1 - p) / p pow 2 =
     ((&r * (&r + &1) * ((&1 - p) / p) pow 2 + &r * (&1 - p) / p) +
      (-- &2 * &r * (&1 - p) / p) * &r * (&1 - p) / p) +
     (&r * (&1 - p) / p) pow 2 * &1` SUBST1_TAC THENL
  [REWRITE_TAC[REAL_MUL_RID] THEN
   UNDISCH_TAC `~(p = &0)` THEN CONV_TAC REAL_FIELD;
   ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;
