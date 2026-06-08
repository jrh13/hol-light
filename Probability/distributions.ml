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

(* ========================================================================= *)
(* Standard normal CDF properties                                           *)
(* ========================================================================= *)

(* Phi(-x) + Phi(x) = 1: complement/symmetry property *)
let STD_NORMAL_CDF_COMPLEMENT = prove
 (`!x. std_normal_cdf(--x) + std_normal_cdf x = &1`,
  GEN_TAC THEN REWRITE_TAC[std_normal_cdf] THEN
  SUBGOAL_THEN
    `real_integral {t | t <= --x} std_normal_density =
     real_integral {t:real | x <= t} std_normal_density`
    SUBST1_TAC THENL
  [SUBGOAL_THEN
      `(\t. std_normal_density(--t)) = std_normal_density`
      ASSUME_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM; STD_NORMAL_DENSITY_SYM]; ALL_TAC] THEN
   FIRST_X_ASSUM(fun th ->
     GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM th]) THEN
   REWRITE_TAC[REAL_INTEGRAL_REFLECT_GEN] THEN
   SUBGOAL_THEN `IMAGE ((--):real->real) {t | t <= --x} = {t:real | x <= t}`
      (fun th -> REWRITE_TAC[th]) THEN
   REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
   X_GEN_TAC `y:real` THEN EQ_TAC THEN STRIP_TAC THENL
   [ASM_REAL_ARITH_TAC;
    EXISTS_TAC `--y:real` THEN ASM_REAL_ARITH_TAC];
   MATCH_MP_TAC(ISPEC `std_normal_density` HAS_REAL_INTEGRAL_UNIQUE) THEN
   EXISTS_TAC `(:real)` THEN REWRITE_TAC[STD_NORMAL_DENSITY_INTEGRAL] THEN
   SUBGOAL_THEN `(:real) = {t:real | t <= x} UNION {t | x <= t}`
      SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_UNIV; IN_ELIM_THM] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
   ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
   MATCH_MP_TAC HAS_REAL_INTEGRAL_UNION THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
    REWRITE_TAC[STD_NORMAL_DENSITY_INTEGRABLE_HALFLINE];
    MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
    MATCH_MP_TAC REAL_INTEGRABLE_ON_SUBINTERVAL_GEN THEN
    EXISTS_TAC `(:real)` THEN
    REWRITE_TAC[STD_NORMAL_DENSITY_INTEGRABLE; SUBSET_UNIV] THEN
    REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{x:real}` THEN
    REWRITE_TAC[REAL_NEGLIGIBLE_SING; SUBSET; IN_INTER;
                IN_ELIM_THM; IN_SING] THEN
    REAL_ARITH_TAC]]);;

(* Phi(0) = 1/2 *)
let STD_NORMAL_CDF_ZERO = prove
 (`std_normal_cdf(&0) = &1 / &2`,
  MP_TAC(SPEC `&0` STD_NORMAL_CDF_COMPLEMENT) THEN
  REWRITE_TAC[REAL_NEG_0] THEN REAL_ARITH_TAC);;

(* Helper: integral of density over [-n,n] tends to 1 via MCT *)
let STD_NORMAL_INTEGRAL_INTERVAL_TENDS_1 = prove
 (`((\n. real_integral (real_interval[-- &n, &n]) std_normal_density)
   ---> &1) sequentially`,
  SUBGOAL_THEN
    `real_integral (:real) std_normal_density = &1`
    ASSUME_TAC THENL
  [MATCH_MP_TAC(ISPEC `std_normal_density` HAS_REAL_INTEGRAL_UNIQUE) THEN
   EXISTS_TAC `(:real)` THEN
   REWRITE_TAC[STD_NORMAL_DENSITY_INTEGRAL] THEN
   MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
   REWRITE_TAC[STD_NORMAL_DENSITY_INTEGRABLE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
    `(\n. real_integral (real_interval[-- &n, &n]) std_normal_density) =
     (\n. real_integral (:real)
       (\x. if x IN real_interval[-- &n, &n]
            then std_normal_density x else &0))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; REAL_INTEGRAL_RESTRICT_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 = real_integral (:real) std_normal_density`
    SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL
    [`\k:num. \x:real. if x IN real_interval[-- &k, &k]
                       then std_normal_density x else &0`;
     `std_normal_density`;
     `(:real)`]
    REAL_MONOTONE_CONVERGENCE_INCREASING) THEN
  ANTS_TAC THENL
  [REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* Integrability *)
    GEN_TAC THEN REWRITE_TAC[REAL_INTEGRABLE_RESTRICT_UNIV] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `(:real)` THEN
    REWRITE_TAC[STD_NORMAL_DENSITY_INTEGRABLE; SUBSET_UNIV];
    (* Monotonicity *)
    REPEAT GEN_TAC THEN REWRITE_TAC[IN_UNIV] THEN
    COND_CASES_TAC THENL
    [SUBGOAL_THEN `x IN real_interval[-- &(SUC k), &(SUC k)]`
      (fun th -> REWRITE_TAC[th]) THENL
     [FIRST_X_ASSUM MP_TAC THEN
      REWRITE_TAC[IN_REAL_INTERVAL; GSYM REAL_OF_NUM_SUC] THEN
      REAL_ARITH_TAC;
      REAL_ARITH_TAC];
     COND_CASES_TAC THEN
     REWRITE_TAC[STD_NORMAL_DENSITY_NONNEG; REAL_LE_REFL]];
    (* Pointwise convergence *)
    X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_UNIV] THEN
    REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(SPEC `abs(x:real)` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    EXISTS_TAC `N:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `x IN real_interval[-- &n, &n]`
      (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[IN_REAL_INTERVAL] THEN
     UNDISCH_TAC `abs(x:real) <= &N` THEN
     UNDISCH_TAC `N <= n:num` THEN
     REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
     REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN ASM_REWRITE_TAC[]];
    (* Bounded integrals *)
    REWRITE_TAC[real_bounded; FORALL_IN_GSPEC; IN_UNIV] THEN
    EXISTS_TAC `&1` THEN
    X_GEN_TAC `k:num` THEN
    REWRITE_TAC[REAL_INTEGRAL_RESTRICT_UNIV] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &1 ==> abs x <= &1`) THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC REAL_INTEGRAL_POS THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_ON_SUBINTERVAL THEN
      EXISTS_TAC `(:real)` THEN
      REWRITE_TAC[STD_NORMAL_DENSITY_INTEGRABLE; SUBSET_UNIV];
      REWRITE_TAC[IN_REAL_INTERVAL; STD_NORMAL_DENSITY_NONNEG]];
     MP_TAC(ISPECL [`std_normal_density`;
                      `real_interval[-- &k, &k]`;
                      `(:real)`;
                      `real_integral (real_interval[-- &k, &k])
                       std_normal_density`;
                      `&1`] HAS_REAL_INTEGRAL_SUBSET_LE) THEN
     REWRITE_TAC[SUBSET_UNIV; STD_NORMAL_DENSITY_INTEGRAL;
                  IN_UNIV; STD_NORMAL_DENSITY_NONNEG] THEN
     DISCH_THEN MATCH_MP_TAC THEN
     MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
     MATCH_MP_TAC REAL_INTEGRABLE_ON_SUBINTERVAL THEN
     EXISTS_TAC `(:real)` THEN
     REWRITE_TAC[STD_NORMAL_DENSITY_INTEGRABLE; SUBSET_UNIV]]];
   DISCH_THEN(MP_TAC o CONJUNCT2) THEN
   REWRITE_TAC[REAL_INTEGRAL_RESTRICT_UNIV] THEN
   MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REALLIM_TRANSFORM) THEN
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN
   REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN
   ASM_REWRITE_TAC[]]);;

(* CDF(n) -> 1 sequentially *)
let STD_NORMAL_CDF_SEQ_TENDS_1 = prove
 (`((\n. std_normal_cdf(&n)) ---> &1) sequentially`,
  SUBGOAL_THEN
    `!n:num. real_integral (real_interval[-- &n, &n]) std_normal_density =
             &2 * std_normal_cdf(&n) - &1`
    ASSUME_TAC THENL
  [X_GEN_TAC `n:num` THEN
   SUBGOAL_THEN `-- &n <= &n:real` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_NEG_LE0; REAL_POS]; ALL_TAC] THEN
   MP_TAC(SPECL [`-- &n:real`; `&n:real`] STD_NORMAL_CDF_INTERVAL) THEN
   ASM_REWRITE_TAC[] THEN
   MP_TAC(SPEC `&n:real` STD_NORMAL_CDF_COMPLEMENT) THEN
   REWRITE_TAC[REAL_NEG_NEG] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `(\n. std_normal_cdf(&n)) =
     (\n. (real_integral (real_interval[-- &n, &n]) std_normal_density + &1)
          * inv(&2))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `&1 = (&1 + &1) * inv(&2)`
    (fun th -> GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [th]) THENL
  [CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_RMUL THEN
  MATCH_MP_TAC REALLIM_ADD THEN
  REWRITE_TAC[STD_NORMAL_INTEGRAL_INTERVAL_TENDS_1; REALLIM_CONST]);;

(* Phi(x) -> 1 as x -> +infinity *)
let STD_NORMAL_CDF_LIMIT_POS = prove
 (`(std_normal_cdf ---> &1) at_posinfinity`,
  REWRITE_TAC[REALLIM_AT_POSINFINITY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC STD_NORMAL_CDF_SEQ_TENDS_1 THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `&N` THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `x:real` STD_NORMAL_CDF_BOUNDS) THEN
  MP_TAC(SPECL [`&N:real`; `x:real`] STD_NORMAL_CDF_MONO) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
  REWRITE_TAC[LE_REFL] THEN
  REAL_ARITH_TAC);;

(* Phi(x) -> 0 as x -> -infinity *)
let STD_NORMAL_CDF_LIMIT_NEG = prove
 (`(std_normal_cdf ---> &0) at_neginfinity`,
  REWRITE_TAC[REALLIM_AT_NEGINFINITY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC STD_NORMAL_CDF_LIMIT_POS THEN
  REWRITE_TAC[REALLIM_AT_POSINFINITY] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `b:real`) THEN
  EXISTS_TAC `--b:real` THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `--x:real` STD_NORMAL_CDF_COMPLEMENT) THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_TAC THEN
  MP_TAC(SPEC `x:real` STD_NORMAL_CDF_BOUNDS) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `--x:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* General normal N(mu, sigma^2) distribution                               *)
(* ========================================================================= *)

let normal_density = new_definition
  `normal_density (mu:real) (sigma:real) (x:real) =
   inv(sigma * sqrt(&2 * pi)) *
   exp(--((x - mu) pow 2 / (&2 * sigma pow 2)))`;;

(* CDF defined via standardization: Phi_mu,sigma(x) = Phi((x-mu)/sigma) *)
let normal_cdf = new_definition
  `normal_cdf (mu:real) (sigma:real) (x:real) =
   std_normal_cdf((x - mu) / sigma)`;;

(* Density standardization: phi_mu,sigma(x) = (1/sigma) * phi((x-mu)/sigma) *)
let NORMAL_DENSITY_STANDARDIZE = prove
 (`!mu sigma x. &0 < sigma ==>
    normal_density mu sigma x =
    inv(sigma) * std_normal_density((x - mu) / sigma)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[normal_density; std_normal_density] THEN
  SUBGOAL_THEN `~(sigma = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(sigma pow 2 = &0)` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_POW_EQ_0] THEN ASM_REWRITE_TAC[ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN
    `((x - mu) / sigma) pow 2 / &2 = (x - mu) pow 2 / (&2 * sigma pow 2)`
    SUBST1_TAC THENL
  [REWRITE_TAC[REAL_POW_DIV] THEN
   ASM_SIMP_TAC[REAL_FIELD
     `~(s = &0) ==>
      (x - mu) pow 2 / s pow 2 / &2 =
      (x - mu) pow 2 / (&2 * s pow 2)`];
   ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[REAL_FIELD
    `~(s = &0) ==> inv(s) * inv(sqrt(&2 * pi)) = inv(s * sqrt(&2 * pi))`]);;

(* Standard normal is special case mu=0, sigma=1 *)
let NORMAL_DENSITY_STANDARD = prove
 (`!x. normal_density (&0) (&1) x = std_normal_density x`,
  GEN_TAC THEN REWRITE_TAC[normal_density; std_normal_density] THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_MUL_LID;
              REAL_POW_ONE; REAL_MUL_RID]);;

let NORMAL_CDF_STANDARD = prove
 (`!x. normal_cdf (&0) (&1) x = std_normal_cdf x`,
  GEN_TAC THEN REWRITE_TAC[normal_cdf] THEN
  AP_TERM_TAC THEN REAL_ARITH_TAC);;

(* Density positivity *)
let NORMAL_DENSITY_POS = prove
 (`!mu sigma x. &0 < sigma ==> &0 < normal_density mu sigma x`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[NORMAL_DENSITY_STANDARDIZE] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN
  REWRITE_TAC[STD_NORMAL_DENSITY_POS] THEN
  MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC);;

let NORMAL_DENSITY_NONNEG = prove
 (`!mu sigma x. &0 < sigma ==> &0 <= normal_density mu sigma x`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN
  ASM_SIMP_TAC[NORMAL_DENSITY_POS]);;

(* Density symmetry about the mean *)
let NORMAL_DENSITY_SYM = prove
 (`!mu sigma x. normal_density mu sigma (mu + x) =
                normal_density mu sigma (mu - x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[normal_density] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REAL_ARITH_TAC);;

(* CDF bounds *)
let NORMAL_CDF_BOUNDS = prove
 (`!mu sigma x. &0 < sigma ==>
    &0 <= normal_cdf mu sigma x /\ normal_cdf mu sigma x <= &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[normal_cdf] THEN
  MP_TAC(ISPEC `(x - mu:real) / sigma` STD_NORMAL_CDF_BOUNDS) THEN
  REAL_ARITH_TAC);;

(* CDF monotonicity *)
let NORMAL_CDF_MONO = prove
 (`!mu sigma x y. &0 < sigma /\ x <= y ==>
    normal_cdf mu sigma x <= normal_cdf mu sigma y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[normal_cdf] THEN
  MATCH_MP_TAC STD_NORMAL_CDF_MONO THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
  ASM_REAL_ARITH_TAC);;

(* CDF continuity *)
let NORMAL_CDF_CONTINUOUS = prove
 (`!mu sigma x. &0 < sigma ==>
    normal_cdf mu sigma real_continuous atreal x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `normal_cdf mu sigma =
    std_normal_cdf o (\t. (t - mu) / sigma)`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; o_THM; normal_cdf]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_COMPOSE THEN
  CONJ_TAC THENL
  [REWRITE_TAC[real_div] THEN
   MATCH_MP_TAC REAL_CONTINUOUS_RMUL THEN
   MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN
   REWRITE_TAC[REAL_CONTINUOUS_CONST; REAL_CONTINUOUS_AT_ID];
   REWRITE_TAC[STD_NORMAL_CDF_CONTINUOUS]]);;

(* CDF complement: Phi(mu-x) + Phi(mu+x) = 1 *)
let NORMAL_CDF_COMPLEMENT = prove
 (`!mu sigma x. &0 < sigma ==>
    normal_cdf mu sigma (mu - x) + normal_cdf mu sigma (mu + x) = &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[normal_cdf; real_div] THEN
  SUBGOAL_THEN `(mu - x - mu:real) * inv sigma = --(x * inv sigma)`
    SUBST1_TAC THENL
  [SUBGOAL_THEN `mu - x - mu:real = --x` SUBST1_TAC THENL
   [REAL_ARITH_TAC; REWRITE_TAC[REAL_MUL_LNEG]];
   ALL_TAC] THEN
  SUBGOAL_THEN `((mu + x) - mu:real) * inv sigma = x * inv sigma`
    SUBST1_TAC THENL
  [SUBGOAL_THEN `(mu + x) - mu:real = x` SUBST1_TAC THENL
   [REAL_ARITH_TAC; REWRITE_TAC[]];
   REWRITE_TAC[GSYM real_div; STD_NORMAL_CDF_COMPLEMENT]]);;

(* CDF at the mean = 1/2 *)
let NORMAL_CDF_MEAN = prove
 (`!mu sigma. &0 < sigma ==>
    normal_cdf mu sigma mu = &1 / &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[normal_cdf] THEN
  SUBGOAL_THEN `(mu - mu:real) / sigma = &0` SUBST1_TAC THENL
  [REWRITE_TAC[real_div; REAL_SUB_REFL; REAL_MUL_LZERO];
   REWRITE_TAC[STD_NORMAL_CDF_ZERO]]);;

(* CDF limits *)
let NORMAL_CDF_LIMIT_POS = prove
 (`!mu sigma. &0 < sigma ==>
    (normal_cdf mu sigma ---> &1) at_posinfinity`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `normal_cdf mu sigma = (\x. std_normal_cdf((x - mu) / sigma))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; normal_cdf]; ALL_TAC] THEN
  REWRITE_TAC[REALLIM_AT_POSINFINITY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC STD_NORMAL_CDF_LIMIT_POS THEN
  REWRITE_TAC[REALLIM_AT_POSINFINITY] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `b:real`) THEN
  EXISTS_TAC `mu + sigma * b:real` THEN
  X_GEN_TAC `y:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(y - mu:real) / sigma`) THEN
  ANTS_TAC THENL
  [REWRITE_TAC[real_ge] THEN
   ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
   UNDISCH_TAC `y >= mu + sigma * b` THEN
   REWRITE_TAC[real_ge] THEN REAL_ARITH_TAC;
   REWRITE_TAC[]]);;

let NORMAL_CDF_LIMIT_NEG = prove
 (`!mu sigma. &0 < sigma ==>
    (normal_cdf mu sigma ---> &0) at_neginfinity`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `normal_cdf mu sigma = (\x. std_normal_cdf((x - mu) / sigma))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; normal_cdf]; ALL_TAC] THEN
  REWRITE_TAC[REALLIM_AT_NEGINFINITY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC STD_NORMAL_CDF_LIMIT_NEG THEN
  REWRITE_TAC[REALLIM_AT_NEGINFINITY] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `b:real`) THEN
  EXISTS_TAC `mu + sigma * b:real` THEN
  X_GEN_TAC `y:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(y - mu:real) / sigma`) THEN
  ANTS_TAC THENL
  [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
   UNDISCH_TAC `y <= mu + sigma * b` THEN REAL_ARITH_TAC;
   REWRITE_TAC[]]);;

(* Change of variables for integrals over all of R *)
let HAS_REAL_INTEGRAL_AFFINITY_UNIV = prove
 (`!f i m c. (f has_real_integral i) (:real) /\ ~(m = &0) ==>
    ((\x. f(m * x + c)) has_real_integral (inv(abs m) * i)) (:real)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[has_real_integral; IMAGE_LIFT_UNIV] THEN
  REWRITE_TAC[LIFT_CMUL; DIMINDEX_1; REAL_POW_1] THEN
  SUBGOAL_THEN
    `lift o (\x. f(m * x + c)) o drop =
     (\x:real^1. (lift o f o drop) (m % x + lift c))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; o_THM; DROP_ADD; DROP_CMUL; LIFT_DROP];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `(:real^1) = IMAGE (\x. inv m % x + --(inv m % lift c)) (:real^1)`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_UNIV; IN_IMAGE] THEN
   X_GEN_TAC `y:real^1` THEN
   EXISTS_TAC `m % y + lift c:real^1` THEN
   REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC;
               VECTOR_MUL_RNEG] THEN
   ASM_SIMP_TAC[REAL_MUL_LINV] THEN VECTOR_ARITH_TAC;
   ALL_TAC] THEN
  MP_TAC(ISPECL [`lift o (f:real->real) o drop`; `lift i:real^1`;
      `(:real^1)`; `m:real`; `lift c:real^1`] HAS_INTEGRAL_AFFINITY) THEN
  ASM_REWRITE_TAC[DIMINDEX_1; REAL_POW_1] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC `(f has_real_integral i) (:real)` THEN
  REWRITE_TAC[has_real_integral; IMAGE_LIFT_UNIV]);;

(* Normal density integrates to 1 *)
let NORMAL_DENSITY_INTEGRAL = prove
 (`!mu sigma. &0 < sigma ==>
    (normal_density mu sigma has_real_integral &1) (:real)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(sigma = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `normal_density mu sigma =
     (\x. inv sigma * std_normal_density ((x - mu) / sigma))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
   ASM_SIMP_TAC[NORMAL_DENSITY_STANDARDIZE];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `(\x. inv sigma * std_normal_density ((x - mu) / sigma)) =
     (\x. inv sigma * std_normal_density (inv sigma * x + --(mu / sigma)))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real` THEN
   AP_TERM_TAC THEN AP_TERM_TAC THEN
   UNDISCH_TAC `~(sigma = &0)` THEN CONV_TAC REAL_FIELD;
   ALL_TAC] THEN
  SUBGOAL_THEN `&1 = inv(sigma) * sigma` SUBST1_TAC THENL
  [ASM_SIMP_TAC[REAL_MUL_LINV]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
  MP_TAC(ISPECL [`std_normal_density`; `&1`; `inv(sigma):real`;
      `--(mu / sigma):real`] HAS_REAL_INTEGRAL_AFFINITY_UNIV) THEN
  ASM_SIMP_TAC[REAL_INV_EQ_0; STD_NORMAL_DENSITY_INTEGRAL] THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_ABS_INV] THEN
  ASM_SIMP_TAC[REAL_ABS_REFL; REAL_LT_IMP_LE; REAL_INV_INV] THEN
  SUBGOAL_THEN `abs sigma = sigma` (fun th -> REWRITE_TAC[th]) THEN
  ASM_REAL_ARITH_TAC);;

(* Normal density integrable over R *)
let NORMAL_DENSITY_INTEGRABLE = prove
 (`!mu sigma. &0 < sigma ==>
    normal_density mu sigma real_integrable_on (:real)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_integrable_on] THEN
  EXISTS_TAC `&1` THEN ASM_SIMP_TAC[NORMAL_DENSITY_INTEGRAL]);;

(* Helper: standard normal weighted integral for mean *)
let NORMAL_MEAN_HELPER = prove
 (`!mu sigma. &0 < sigma ==>
    ((\t. (mu + sigma * t) * std_normal_density t) has_real_integral mu)
    (:real)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `((\t. mu * std_normal_density t) has_real_integral mu * &1) (:real) /\
     ((\t. sigma * (t * std_normal_density t)) has_real_integral sigma * &0)
     (:real)`
    (fun th -> MP_TAC(MATCH_MP HAS_REAL_INTEGRAL_ADD th)) THENL
  [CONJ_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
   REWRITE_TAC[STD_NORMAL_DENSITY_INTEGRAL; STD_NORMAL_MEAN_ZERO];
   ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO; REAL_ADD_RID] THEN
  SUBGOAL_THEN
    `(\x:real. mu * std_normal_density x + sigma * x * std_normal_density x) =
     (\t. (mu + sigma * t) * std_normal_density t)`
    (fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC);;

(* Normal mean: E[X] = mu *)
let NORMAL_MEAN = prove
 (`!mu sigma. &0 < sigma ==>
    ((\x. x * normal_density mu sigma x) has_real_integral mu) (:real)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(sigma = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(inv sigma = &0)` ASSUME_TAC THENL
  [ASM_SIMP_TAC[REAL_INV_EQ_0]; ALL_TAC] THEN
  SUBGOAL_THEN
    `(\x. x * normal_density mu sigma x) =
     (\x. inv(sigma) * (x * std_normal_density((x - mu) / sigma)))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real` THEN
   ASM_SIMP_TAC[NORMAL_DENSITY_STANDARDIZE] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `((\x. x * std_normal_density((x - mu) / sigma)) has_real_integral
      sigma * mu) (:real)`
    (fun th ->
      MP_TAC(SPEC `inv(sigma):real` (MATCH_MP HAS_REAL_INTEGRAL_LMUL th)))
  THENL
  [MP_TAC(SPECL [`mu:real`; `sigma:real`] NORMAL_MEAN_HELPER) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`\t:real. (mu + sigma * t) * std_normal_density t`;
                   `mu:real`; `inv(sigma):real`; `--(mu / sigma):real`]
     HAS_REAL_INTEGRAL_AFFINITY_UNIV) THEN
   ASM_SIMP_TAC[REAL_INV_EQ_0] THEN
   SUBGOAL_THEN
     `!x:real. mu + sigma * (inv sigma * x + --(mu / sigma)) = x`
     (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `x:real` THEN
    UNDISCH_TAC `~(sigma = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
   SUBGOAL_THEN
     `!x:real. inv sigma * x + --(mu / sigma) = (x - mu) / sigma`
     (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `x:real` THEN
    UNDISCH_TAC `~(sigma = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
   SUBGOAL_THEN `inv (abs (inv sigma)) * mu = sigma * mu`
     (fun th -> REWRITE_TAC[th]) THEN
   REWRITE_TAC[REAL_ABS_INV] THEN
   SUBGOAL_THEN `abs sigma = sigma` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_INV_INV; REAL_MUL_LID]];
   SUBGOAL_THEN `inv sigma * (sigma * mu) = mu:real`
     (fun th -> REWRITE_TAC[th]) THEN
   UNDISCH_TAC `~(sigma = &0)` THEN CONV_TAC REAL_FIELD]);;

(* Normal mean - integral form *)
let NORMAL_MEAN_INTEGRAL = prove
 (`!mu sigma. &0 < sigma ==>
    real_integral (:real) (\x. x * normal_density mu sigma x) = mu`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  ASM_SIMP_TAC[NORMAL_MEAN]);;

(* Normal variance: Var(X) = sigma^2 *)
let NORMAL_VARIANCE = prove
 (`!mu sigma. &0 < sigma ==>
    ((\x. (x - mu) pow 2 * normal_density mu sigma x) has_real_integral
     sigma pow 2) (:real)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(sigma = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(inv sigma = &0)` ASSUME_TAC THENL
  [ASM_SIMP_TAC[REAL_INV_EQ_0]; ALL_TAC] THEN
  SUBGOAL_THEN
    `(\x. (x - mu) pow 2 * normal_density mu sigma x) =
     (\x. sigma pow 2 * (((x - mu) / sigma) pow 2 *
          (inv sigma * std_normal_density((x - mu) / sigma))))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real` THEN
   ASM_SIMP_TAC[NORMAL_DENSITY_STANDARDIZE; REAL_POW_DIV] THEN
   UNDISCH_TAC `~(sigma = &0)` THEN CONV_TAC REAL_FIELD;
   ALL_TAC] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
  SUBGOAL_THEN
    `(\x. ((x - mu) / sigma) pow 2 *
          inv sigma * std_normal_density ((x - mu) / sigma)) =
     (\x. inv sigma * (((x - mu) / sigma) pow 2 *
          std_normal_density ((x - mu) / sigma)))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `&1 = inv sigma * sigma` SUBST1_TAC THENL
  [ASM_SIMP_TAC[REAL_MUL_LINV]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
  MP_TAC(ISPECL [`\t:real. t pow 2 * std_normal_density t`;
                  `&1`; `inv(sigma):real`; `--(mu / sigma):real`]
    HAS_REAL_INTEGRAL_AFFINITY_UNIV) THEN
  ASM_SIMP_TAC[REAL_INV_EQ_0; STD_NORMAL_SECOND_MOMENT] THEN
  SUBGOAL_THEN
    `!x:real. inv sigma * x + --(mu / sigma) = (x - mu) / sigma`
    (fun th -> REWRITE_TAC[th]) THENL
  [X_GEN_TAC `x:real` THEN
   UNDISCH_TAC `~(sigma = &0)` THEN CONV_TAC REAL_FIELD;
   ALL_TAC] THEN
  SUBGOAL_THEN `inv (abs (inv sigma)) * &1 = sigma`
    (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_ABS_INV] THEN
  SUBGOAL_THEN `abs sigma = sigma` (fun th -> REWRITE_TAC[th]) THENL
  [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_INV_INV]]);;

(* Normal variance - integral form *)
let NORMAL_VARIANCE_INTEGRAL = prove
 (`!mu sigma. &0 < sigma ==>
    real_integral (:real) (\x. (x - mu) pow 2 * normal_density mu sigma x) =
    sigma pow 2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  ASM_SIMP_TAC[NORMAL_VARIANCE]);;

(* ========================================================================= *)
(* Exponential distribution Exp(lambda)                                      *)
(*                                                                           *)
(* Density: lambda * exp(-lambda * x) for x >= 0, 0 otherwise               *)
(* CDF: 1 - exp(-lambda * x) for x >= 0, 0 otherwise                        *)
(* Mean: 1/lambda, Variance: 1/lambda^2                                      *)
(* Key property: memoryless                                                  *)
(* ========================================================================= *)

(* Exponential density function *)
let exponential_density = new_definition
  `exponential_density (l:real) (x:real) =
   if &0 <= x then l * exp(--l * x) else &0`;;

(* Density is non-negative when lambda > 0 *)
let EXPONENTIAL_DENSITY_NONNEG = prove
 (`!l x. &0 < l ==> &0 <= exponential_density l x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[exponential_density] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN
  REWRITE_TAC[REAL_EXP_POS_LE] THEN ASM_REAL_ARITH_TAC);;

(* Density is strictly positive for x > 0 *)
let EXPONENTIAL_DENSITY_POS = prove
 (`!l x. &0 < l /\ &0 < x ==> &0 < exponential_density l x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[exponential_density] THEN
  SUBGOAL_THEN `&0 <= x` (fun th -> REWRITE_TAC[th]) THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN
  ASM_REWRITE_TAC[REAL_EXP_POS_LT]);;

(* Density at x=0 is lambda *)
let EXPONENTIAL_DENSITY_ZERO = prove
 (`!l. exponential_density l (&0) = l`,
  GEN_TAC THEN REWRITE_TAC[exponential_density; REAL_LE_REFL] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_NEG_0; REAL_EXP_0; REAL_MUL_RID]);;

(* Antiderivative of the exponential density *)
(* d/dx[-exp(-l*x)] = l * exp(-l*x) *)
let EXPONENTIAL_HAS_REAL_DERIVATIVE = prove
 (`!l x. ((\x. --exp(--l * x)) has_real_derivative l * exp(--l * x))
         (atreal x)`,
  REPEAT GEN_TAC THEN REAL_DIFF_TAC THEN REAL_ARITH_TAC);;

(* Derivative within an interval *)
let EXPONENTIAL_HAS_REAL_DERIVATIVE_WITHIN = prove
 (`!l x s. ((\x. --exp(--l * x)) has_real_derivative l * exp(--l * x))
            (atreal x within s)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
  REWRITE_TAC[EXPONENTIAL_HAS_REAL_DERIVATIVE]);;

(* Integral of exponential density on [0, a] via FTC *)
let EXPONENTIAL_INTEGRAL_INTERVAL = prove
 (`!l a. &0 <= a ==>
   ((\x. l * exp(--l * x)) has_real_integral (&1 - exp(--l * a)))
   (real_interval[&0,a])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real. --exp(--l * x)`;
                  `\x:real. l * exp(--l * x)`;
                  `&0`; `a:real`]
    REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
  [REPEAT STRIP_TAC THEN
   REWRITE_TAC[EXPONENTIAL_HAS_REAL_DERIVATIVE_WITHIN];
   REWRITE_TAC[REAL_MUL_RZERO; REAL_NEG_0; REAL_EXP_0] THEN
   REWRITE_TAC[REAL_ARITH `--exp(--l * a) - --(&1) = &1 - exp(--l * a)`]]);;

(* Exponential density is continuous *)
let EXPONENTIAL_REAL_CONTINUOUS = prove
 (`!l. (\x. l * exp(--l * x)) real_continuous_on (:real)`,
  GEN_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
  SUBGOAL_THEN
    `(\x:real. exp(--l * x)) = (exp o (\x. --l * x))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON_EXP] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON_ID]);;

(* Exponential density integrable on any interval [0,a] *)
let EXPONENTIAL_INTEGRABLE_INTERVAL = prove
 (`!l a. &0 <= a ==>
   (\x. l * exp(--l * x)) real_integrable_on real_interval[&0,a]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_INTEGRABLE THEN
  EXISTS_TAC `&1 - exp(--l * a)` THEN
  ASM_SIMP_TAC[EXPONENTIAL_INTEGRAL_INTERVAL]);;

(* Key limit: exp(-l*a) -> 0 as a -> +infinity when l > 0 *)
let EXPONENTIAL_LIMIT_POSINFINITY = prove
 (`!l. &0 < l ==> ((\a. exp(--l * a)) ---> &0) at_posinfinity`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REALLIM_AT_POSINFINITY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `(&1 / e + &1) / l:real` THEN
  X_GEN_TAC `a:real` THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_SUB_RZERO; real_abs; REAL_EXP_POS_LE] THEN
  SUBGOAL_THEN `inv e < l * a` ASSUME_TAC THENL
  [SUBGOAL_THEN `inv e < l * ((&1 / e + &1) / l)` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN REAL_ARITH_TAC;
    DISCH_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `l * ((&1 / e + &1) / l):real` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[GSYM real_ge] THEN ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 < l * a` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `inv e:real` THEN
   ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_INV THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `l * a < exp(l * a)` ASSUME_TAC THENL
  [MP_TAC(SPEC `l * a:real` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(l * a):real` THEN
  CONJ_TAC THENL
  [ONCE_REWRITE_TAC[REAL_ARITH `--l * a = --(l * a:real)`] THEN
   REWRITE_TAC[REAL_EXP_NEG] THEN
   MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
   ASM_REAL_ARITH_TAC;
   SUBGOAL_THEN `e = inv(inv e:real)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_INV_INV];
    MATCH_MP_TAC REAL_LT_INV2 THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_INV THEN
    ASM_REWRITE_TAC[]]]);;

(* Helper: the restricted integrals converge to 1 *)
let EXPONENTIAL_INTEGRAL_SEQ_TENDS_1 = prove
 (`!l. &0 < l ==>
   ((\k. &1 - exp(--l * &k)) ---> &1) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((\k:num. exp(--l * &k)) ---> &0) sequentially`
    ASSUME_TAC THENL
  [MP_TAC(SPEC `l:real` EXPONENTIAL_LIMIT_POSINFINITY) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o MATCH_MP REALLIM_POSINFINITY_SEQUENTIALLY) THEN
   REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `&1 = &1 - &0` SUBST1_TAC THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_SUB THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO; REALLIM_CONST]);;

(* Normalization: integral of density over [0,+inf) is 1 *)
let EXPONENTIAL_DENSITY_INTEGRAL = prove
 (`!l. &0 < l ==>
   ((\x. l * exp(--l * x)) has_real_integral &1)
   {x | &0 <= x}`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
  CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  ABBREV_TAC `g = \x:real. if &0 <= x then l * exp(--l * x) else &0` THEN
  ABBREV_TAC
    `f = \k x:real. if &0 <= x /\ x <= &k then l * exp(--l * x) else &0` THEN
  (* Step 1: establish f_k properties via monotone convergence *)
  SUBGOAL_THEN
    `g real_integrable_on (:real) /\
     ((\k. real_integral (:real) (f k)) ---> real_integral (:real) g)
     sequentially`
    STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_MONOTONE_CONVERGENCE_INCREASING THEN
   REPEAT CONJ_TAC THENL
   [(* f_k integrable *)
    X_GEN_TAC `k:num` THEN EXPAND_TAC "f" THEN
    SUBGOAL_THEN
      `(\x. if &0 <= x /\ x <= &k then l * exp(--l * x) else &0) =
       (\x. if x IN real_interval[&0,&k] then l * exp(--l * x) else &0)`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM; IN_REAL_INTERVAL] THEN MESON_TAC[];
     REWRITE_TAC[real_integrable_on] THEN
     EXISTS_TAC `&1 - exp(--l * &k)` THEN
     REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
     MATCH_MP_TAC EXPONENTIAL_INTEGRAL_INTERVAL THEN
     REWRITE_TAC[REAL_POS]];
    (* monotonicity *)
    X_GEN_TAC `k:num` THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    EXPAND_TAC "f" THEN REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]) THEN
    TRY(MATCH_MP_TAC REAL_LE_MUL THEN
        REWRITE_TAC[REAL_EXP_POS_LE] THEN ASM_REAL_ARITH_TAC) THEN
    ASM_REAL_ARITH_TAC;
    (* pointwise convergence *)
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    EXPAND_TAC "f" THEN EXPAND_TAC "g" THEN
    ASM_CASES_TAC `&0 <= x` THENL
    [ASM_REWRITE_TAC[] THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
     X_GEN_TAC `e:real` THEN DISCH_TAC THEN
     MP_TAC(SPEC `x:real` REAL_ARCH_SIMPLE) THEN
     DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
     EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
     SUBGOAL_THEN `x <= &n` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N` THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM] THEN
      ASM_REAL_ARITH_TAC];
     ASM_REWRITE_TAC[] THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
     X_GEN_TAC `e:real` THEN DISCH_TAC THEN EXISTS_TAC `0` THEN
     X_GEN_TAC `n:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
     ASM_REAL_ARITH_TAC];
    (* bounded integrals *)
    REWRITE_TAC[real_bounded; FORALL_IN_GSPEC; IN_UNIV] THEN
    EXISTS_TAC `&1` THEN X_GEN_TAC `k:num` THEN
    SUBGOAL_THEN
      `real_integral (:real) ((f:num->real->real) k) = &1 - exp(--l * &k)`
      SUBST1_TAC THENL
    [EXPAND_TAC "f" THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
     SUBGOAL_THEN
       `(\x. if &0 <= x /\ x <= &k then l * exp(--l * x) else &0) =
        (\x. if x IN real_interval[&0,&k] then l * exp(--l * x) else &0)`
       SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; IN_REAL_INTERVAL] THEN MESON_TAC[];
      REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
      MATCH_MP_TAC EXPONENTIAL_INTEGRAL_INTERVAL THEN
      REWRITE_TAC[REAL_POS]];
     SUBGOAL_THEN `exp(--l * &k) <= &1` MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_0; REAL_EXP_MONO_LE] THEN
      SUBGOAL_THEN `&0 <= l * &k` MP_TAC THENL
      [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
       ASM_REAL_ARITH_TAC;
       REAL_ARITH_TAC];
      MP_TAC(SPEC `--l * &k` REAL_EXP_POS_LE) THEN REAL_ARITH_TAC]]];
   ALL_TAC] THEN
  (* Step 2: show the integral equals 1 *)
  SUBGOAL_THEN `real_integral (:real) g = &1`
    (fun th -> ONCE_REWRITE_TAC[SYM th] THEN
               REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL] THEN
               ASM_REWRITE_TAC[]) THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC `\k:num. real_integral (:real) ((f:num->real->real) k)` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  SUBGOAL_THEN
    `(\k. real_integral (:real) ((f:num->real->real) k)) =
     (\k. &1 - exp(--l * &k))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `k:num` THEN
   EXPAND_TAC "f" THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
   SUBGOAL_THEN
     `(\x. if &0 <= x /\ x <= &k then l * exp(--l * x) else &0) =
      (\x. if x IN real_interval[&0,&k] then l * exp(--l * x) else &0)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; IN_REAL_INTERVAL] THEN MESON_TAC[];
    REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
    MATCH_MP_TAC EXPONENTIAL_INTEGRAL_INTERVAL THEN
    REWRITE_TAC[REAL_POS]];
   ASM_SIMP_TAC[EXPONENTIAL_INTEGRAL_SEQ_TENDS_1]]);;

(* Exponential CDF *)
let exponential_cdf = new_definition
  `exponential_cdf (l:real) (x:real) =
   if &0 <= x then &1 - exp(--l * x) else &0`;;

(* CDF at zero *)
let EXPONENTIAL_CDF_ZERO = prove
 (`!l. exponential_cdf l (&0) = &0`,
  GEN_TAC THEN REWRITE_TAC[exponential_cdf; REAL_LE_REFL;
    REAL_MUL_RZERO; REAL_NEG_0; REAL_EXP_0] THEN
  REAL_ARITH_TAC);;

(* CDF is non-negative *)
let EXPONENTIAL_CDF_NONNEG = prove
 (`!l x. &0 < l /\ &0 <= x ==> &0 <= exponential_cdf l x`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[exponential_cdf] THEN
  SUBGOAL_THEN `exp(--l * x) <= &1` MP_TAC THENL
  [REWRITE_TAC[GSYM REAL_EXP_0; REAL_EXP_MONO_LE] THEN
   SUBGOAL_THEN `&0 <= l * x` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC];
   REAL_ARITH_TAC]);;

(* CDF is at most 1 *)
let EXPONENTIAL_CDF_LE_1 = prove
 (`!l x. &0 < l /\ &0 <= x ==> exponential_cdf l x <= &1`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[exponential_cdf] THEN
  MP_TAC(SPEC `--l * x:real` REAL_EXP_POS_LE) THEN REAL_ARITH_TAC);;

(* Memoryless property: P(X > s+t) = P(X > s) * P(X > t) *)
let EXPONENTIAL_MEMORYLESS = prove
 (`!l s t. &0 < l /\ &0 <= s /\ &0 <= t ==>
   &1 - exponential_cdf l (s + t) =
   (&1 - exponential_cdf l s) * (&1 - exponential_cdf l t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= s + t` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[exponential_cdf] THEN
  REWRITE_TAC[REAL_ARITH `&1 - (&1 - x) = x`] THEN
  REWRITE_TAC[GSYM REAL_EXP_ADD] THEN
  AP_TERM_TAC THEN REAL_ARITH_TAC);;

(* Helper: quadratic lower bound for exp *)
let REAL_EXP_QUADRATIC_BOUND = prove
 (`!x. &0 <= x ==> x pow 2 / &4 <= exp x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x = x / &2 + x / &2` SUBST1_TAC THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_ADD] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(x / &2) pow 2` THEN CONJ_TAC THENL
  [REWRITE_TAC[REAL_POW_DIV] THEN REAL_ARITH_TAC;
   REWRITE_TAC[REAL_POW_2] THEN
   MATCH_MP_TAC REAL_LE_MUL2 THEN
   REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MP_TAC(SPEC `x / &2` REAL_EXP_LE_X) THEN REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    MP_TAC(SPEC `x / &2` REAL_EXP_LE_X) THEN REAL_ARITH_TAC]]);;

(* Helper: k * exp(-l*k) -> 0 as k -> infinity *)
let EXPONENTIAL_LINEAR_DECAY_SEQ = prove
 (`!l. &0 < l ==> ((\k:num. &k * exp(--l * &k)) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\k. &k * exp(--l * &k)) = (\k. &k pow 1 * exp(--l) pow k)`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; REAL_POW_1] THEN
   GEN_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[GSYM REAL_EXP_N] THEN
   AP_TERM_TAC THEN REAL_ARITH_TAC;
   MATCH_MP_TAC REALLIM_POW_TIMES_POWN THEN
   SUBGOAL_THEN `abs(exp(--l)) = exp(--l)` SUBST1_TAC THENL
   [REWRITE_TAC[real_abs; REAL_EXP_POS_LE];
    REWRITE_TAC[GSYM REAL_EXP_0; REAL_EXP_MONO_LT] THEN
    ASM_REAL_ARITH_TAC]]);;

(* Antiderivative for x * l * exp(-l*x) *)
let EXPONENTIAL_MEAN_ANTIDERIV = prove
 (`!l x. ~(l = &0) ==>
  ((\x. --(x + inv l) * exp(--l * x)) has_real_derivative
   l * x * exp(--l * x)) (atreal x)`,
  REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_ADD_RID;
    REAL_ARITH `-- &1 * e = --e`; REAL_MUL_LNEG; REAL_MUL_RNEG;
    REAL_NEG_NEG] THEN
  ONCE_REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_MUL_LID] THEN
  REAL_ARITH_TAC);;

(* Integral of x * l * exp(-l*x) on [0, a] *)
let EXPONENTIAL_MEAN_INTEGRAL_INTERVAL = prove
 (`!l a. &0 < l /\ &0 <= a ==>
  ((\x. l * x * exp(--l * x)) has_real_integral
   (inv l - (a + inv l) * exp(--l * a)))
  (real_interval[&0,a])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real. --(x + inv l) * exp(--l * x)`;
                  `\x:real. l * x * exp(--l * x)`;
                  `&0`; `a:real`]
    REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
   MP_TAC(SPECL [`l:real`; `x:real`] EXPONENTIAL_MEAN_ANTIDERIV) THEN
   ASM_SIMP_TAC[REAL_LT_IMP_NZ];
   REWRITE_TAC[REAL_MUL_LZERO; REAL_NEG_0; REAL_EXP_0; REAL_ADD_LID;
     REAL_MUL_RID; REAL_MUL_RZERO; REAL_NEG_NEG] THEN
   SUBGOAL_THEN
     `--(a + inv l) * exp(--l * a) - --inv l =
      inv l - (a + inv l) * exp(--l * a:real)`
     (fun th -> REWRITE_TAC[th]) THEN
   ABBREV_TAC `e = exp(--l * a:real)` THEN REAL_ARITH_TAC]);;

(* Helper: mean integral sequence tends to inv(l) *)
let EXPONENTIAL_MEAN_SEQ_TENDS = prove
 (`!l. &0 < l ==>
  ((\k:num. inv l - (&k + inv l) * exp(--l * &k)) ---> inv l) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((\k:num. exp(--l * &k)) ---> &0) sequentially` ASSUME_TAC THENL
  [MP_TAC(SPEC `l:real` EXPONENTIAL_LIMIT_POSINFINITY) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o MATCH_MP REALLIM_POSINFINITY_SEQUENTIALLY) THEN
   REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `inv l = inv l - &0` SUBST1_TAC THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_SUB THEN CONJ_TAC THENL
  [REWRITE_TAC[REAL_SUB_RZERO; REALLIM_CONST]; ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  SUBGOAL_THEN
    `(\k. (&k + inv l) * exp(--l * &k)) =
     (\k. &k * exp(--l * &k) + inv l * exp(--l * &k))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; REAL_ADD_RDISTRIB]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 = &0 + &0` SUBST1_TAC THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
  [ASM_SIMP_TAC[EXPONENTIAL_LINEAR_DECAY_SEQ]; ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_NULL_LMUL THEN ASM_REWRITE_TAC[]);;

(* Mean of exponential distribution = 1/lambda *)
let EXPONENTIAL_MEAN = prove
 (`!l. &0 < l ==>
   ((\x. x * exponential_density l x) has_real_integral inv l)
   {x | &0 <= x}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[exponential_density] THEN
  REWRITE_TAC[REAL_ARITH `x * (if &0 <= x then l * e else &0) =
    (if &0 <= x then x * l * e else &0)`] THEN
  ONCE_REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
  CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN
    `(\x:real. if &0 <= x then if &0 <= x then x * l * exp(--l * x) else &0
               else &0) =
     (\x. if &0 <= x then x * l * exp(--l * x) else &0)`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
   COND_CASES_TAC THEN REWRITE_TAC[];
   ALL_TAC] THEN
  ABBREV_TAC
    `g = \x:real. if &0 <= x then l * x * exp(--l * x) else &0` THEN
  ABBREV_TAC
    `f = \k x:real. if &0 <= x /\ x <= &k then l * x * exp(--l * x)
                    else &0` THEN
  SUBGOAL_THEN
    `(\x:real. if &0 <= x then x * l * exp(--l * x) else &0) = g`
    SUBST1_TAC THENL
  [EXPAND_TAC "g" THEN REWRITE_TAC[FUN_EQ_THM] THEN
   GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_AC];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `g real_integrable_on (:real) /\
     ((\k. real_integral (:real) (f k)) ---> real_integral (:real) g)
     sequentially`
    STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_MONOTONE_CONVERGENCE_INCREASING THEN
   REPEAT CONJ_TAC THENL
   [(* f_k integrable *)
    X_GEN_TAC `k:num` THEN EXPAND_TAC "f" THEN
    SUBGOAL_THEN
      `(\x. if &0 <= x /\ x <= &k then l * x * exp(--l * x) else &0) =
       (\x. if x IN real_interval[&0,&k] then l * x * exp(--l * x) else &0)`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM; IN_REAL_INTERVAL] THEN MESON_TAC[];
     REWRITE_TAC[real_integrable_on] THEN
     EXISTS_TAC `inv l - (&k + inv l) * exp(--l * &k)` THEN
     REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
     MATCH_MP_TAC EXPONENTIAL_MEAN_INTEGRAL_INTERVAL THEN
     ASM_REWRITE_TAC[REAL_POS]];
    (* monotonicity: f_k(x) <= f_{k+1}(x) *)
    X_GEN_TAC `k:num` THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    EXPAND_TAC "f" THEN REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]) THEN
    TRY(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
        [ASM_REAL_ARITH_TAC;
         MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_EXP_POS_LE]]]) THEN
    ASM_REAL_ARITH_TAC;
    (* pointwise convergence *)
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    EXPAND_TAC "f" THEN EXPAND_TAC "g" THEN
    ASM_CASES_TAC `&0 <= x` THENL
    [ASM_REWRITE_TAC[] THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
     X_GEN_TAC `e:real` THEN DISCH_TAC THEN
     MP_TAC(SPEC `x:real` REAL_ARCH_SIMPLE) THEN
     DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
     EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
     SUBGOAL_THEN `x <= &n` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N` THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM] THEN
      ASM_REAL_ARITH_TAC];
     ASM_REWRITE_TAC[] THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
     X_GEN_TAC `e:real` THEN DISCH_TAC THEN EXISTS_TAC `0` THEN
     X_GEN_TAC `n:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
     ASM_REAL_ARITH_TAC];
    (* bounded integrals *)
    REWRITE_TAC[real_bounded; FORALL_IN_GSPEC; IN_UNIV] THEN
    EXISTS_TAC `inv(l:real)` THEN X_GEN_TAC `k:num` THEN
    SUBGOAL_THEN
      `real_integral (:real) ((f:num->real->real) k) =
       inv l - (&k + inv l) * exp(--l * &k)`
      SUBST1_TAC THENL
    [EXPAND_TAC "f" THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
     SUBGOAL_THEN
       `(\x. if &0 <= x /\ x <= &k then l * x * exp(--l * x) else &0) =
        (\x. if x IN real_interval[&0,&k] then l * x * exp(--l * x)
             else &0)`
       SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; IN_REAL_INTERVAL] THEN MESON_TAC[];
      REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
      MATCH_MP_TAC EXPONENTIAL_MEAN_INTEGRAL_INTERVAL THEN
      ASM_REWRITE_TAC[REAL_POS]];
     SUBGOAL_THEN
       `&0 <= inv l - (&k + inv l) * exp(--l * &k)`
       MP_TAC THENL
     [MATCH_MP_TAC HAS_REAL_INTEGRAL_POS THEN
      EXISTS_TAC `\x:real. l * x * exp(--l * x)` THEN
      EXISTS_TAC `real_interval[&0,&k]` THEN CONJ_TAC THENL
      [MATCH_MP_TAC EXPONENTIAL_MEAN_INTEGRAL_INTERVAL THEN
       ASM_REWRITE_TAC[REAL_POS];
       REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
       MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
        [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_EXP_POS_LE]]]];
      SUBGOAL_THEN `&0 <= (&k + inv l) * exp(--l * &k)` MP_TAC THENL
      [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
       MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_POS] THEN
       MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
       REAL_ARITH_TAC]]]];
   ALL_TAC] THEN
  SUBGOAL_THEN `real_integral (:real) g = inv l`
    (fun th -> ONCE_REWRITE_TAC[SYM th] THEN
               REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL] THEN
               ASM_REWRITE_TAC[]) THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC `\k:num. real_integral (:real) ((f:num->real->real) k)` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  SUBGOAL_THEN
    `(\k. real_integral (:real) ((f:num->real->real) k)) =
     (\k. inv l - (&k + inv l) * exp(--l * &k))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `k:num` THEN
   EXPAND_TAC "f" THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
   SUBGOAL_THEN
     `(\x. if &0 <= x /\ x <= &k then l * x * exp(--l * x) else &0) =
      (\x. if x IN real_interval[&0,&k] then l * x * exp(--l * x) else &0)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; IN_REAL_INTERVAL] THEN MESON_TAC[];
    REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
    MATCH_MP_TAC EXPONENTIAL_MEAN_INTEGRAL_INTERVAL THEN
    ASM_REWRITE_TAC[REAL_POS]];
   ASM_SIMP_TAC[EXPONENTIAL_MEAN_SEQ_TENDS]]);;

(* Mean as an integral value *)
let EXPONENTIAL_MEAN_INTEGRAL = prove
 (`!l. &0 < l ==>
   real_integral {x | &0 <= x} (\x. x * exponential_density l x) = inv l`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  ASM_SIMP_TAC[EXPONENTIAL_MEAN]);;

(* Quadratic decay: k^2 * exp(-lk) -> 0 *)
let EXPONENTIAL_QUADRATIC_DECAY_SEQ = prove
 (`!l. &0 < l
       ==> ((\k:num. &k pow 2 * exp(--l * &k)) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\k. &k pow 2 * exp(--l * &k)) =
                (\k. &k pow 2 * exp(--l) pow k)` SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[GSYM REAL_EXP_N] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
   MATCH_MP_TAC REALLIM_POW_TIMES_POWN THEN
   SUBGOAL_THEN `abs(exp(--l)) = exp(--l)` SUBST1_TAC THENL
   [REWRITE_TAC[real_abs; REAL_EXP_POS_LE];
    REWRITE_TAC[GSYM REAL_EXP_0; REAL_EXP_MONO_LT] THEN
    ASM_REAL_ARITH_TAC]]);;

(* Product (k^2 + 2k/l + 2/l^2) * exp(-lk) -> 0 *)
let EXPONENTIAL_PRODUCT_DECAY_SEQ = prove
 (`!l. &0 < l ==>
  ((\k:num. (&k pow 2 + &2 * &k * inv l + &2 * inv l pow 2) *
            exp(--l * &k)) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < inv l` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `((\k:num. exp(--l * &k)) ---> &0) sequentially` ASSUME_TAC THENL
  [MP_TAC(SPEC `l:real` EXPONENTIAL_LIMIT_POSINFINITY) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o MATCH_MP REALLIM_POSINFINITY_SEQUENTIALLY) THEN
   REWRITE_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
  SUBGOAL_THEN
    `((\k:num. &k pow 2 * exp(--l * &k)) ---> &0) sequentially`
    ASSUME_TAC THENL
  [ASM_SIMP_TAC[EXPONENTIAL_QUADRATIC_DECAY_SEQ]; ALL_TAC] THEN
  SUBGOAL_THEN
    `((\k:num. (&2 * &k * inv l) * exp(--l * &k)) ---> &0) sequentially`
    ASSUME_TAC THENL
  [SUBGOAL_THEN
     `(\k:num. (&2 * &k * inv l) * exp(--l * &k)) =
      (\k. (&2 * inv l) * (&k * exp(--l * &k)))`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM REAL_MUL_ASSOC] THEN GEN_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[REAL_MUL_AC];
    MATCH_MP_TAC REALLIM_NULL_LMUL THEN
    ASM_SIMP_TAC[EXPONENTIAL_LINEAR_DECAY_SEQ]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `((\k:num. (&2 * inv l pow 2) * exp(--l * &k)) ---> &0) sequentially`
    ASSUME_TAC THENL
  [MATCH_MP_TAC REALLIM_NULL_LMUL THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_ASSOC] THEN
  SUBGOAL_THEN `&0 = &0 + &0` (fun th -> ONCE_REWRITE_TAC[th]) THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
  [SUBGOAL_THEN `&0 = &0 + &0` (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REALLIM_ADD THEN ASM_REWRITE_TAC[];
   ASM_REWRITE_TAC[]]);;

(* Antiderivative for x^2 * l * exp(-l*x) *)
let EXPONENTIAL_SECOND_MOMENT_ANTIDERIV = prove
 (`!l x. ~(l = &0) ==>
  ((\x. --(x pow 2 + &2 * x * inv l + &2 * inv l pow 2) * exp(--l * x))
   has_real_derivative
   l * x pow 2 * exp(--l * x)) (atreal x)`,
  REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_ADD_RID; REAL_MUL_LID;
              ARITH_RULE `2 - 1 = 1`; REAL_POW_1] THEN
  ONCE_REWRITE_TAC[REAL_MUL_ASSOC] THEN
  SUBGOAL_THEN
    `!a b c:real. a * c + b * c = (a + b) * c`
    (fun th -> ONCE_REWRITE_TAC[th]) THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_NEG_MUL2] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_MUL_RID] THEN
  REWRITE_TAC[REAL_POW_2] THEN
  ONCE_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_MUL_RID] THEN
  REAL_ARITH_TAC);;

(* Integral of x^2 * l * exp(-l*x) on [0, a] *)
let EXPONENTIAL_SECOND_MOMENT_INTEGRAL_INTERVAL = prove
 (`!l a. &0 < l /\ &0 <= a ==>
  ((\x. l * x pow 2 * exp(--l * x)) has_real_integral
   (&2 * inv l pow 2 -
    (a pow 2 + &2 * a * inv l + &2 * inv l pow 2) * exp(--l * a)))
  (real_interval[&0,a])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
    [`\x:real. --(x pow 2 + &2 * x * inv l + &2 * inv l pow 2) *
               exp(--l * x)`;
     `\x:real. l * x pow 2 * exp(--l * x)`;
     `&0`; `a:real`]
    REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
   MP_TAC(SPECL [`l:real`; `x:real`]
     EXPONENTIAL_SECOND_MOMENT_ANTIDERIV) THEN
   ASM_SIMP_TAC[REAL_LT_IMP_NZ];
   REWRITE_TAC[REAL_POW_ZERO; ARITH_EQ; REAL_MUL_LZERO; REAL_MUL_RZERO;
     REAL_ADD_LID; REAL_NEG_0; REAL_EXP_0; REAL_MUL_RID] THEN
   SUBGOAL_THEN
     `--(a pow 2 + &2 * a * inv l + &2 * inv l pow 2) * exp(--l * a) -
      --(&2 * inv l pow 2) =
      &2 * inv l pow 2 -
      (a pow 2 + &2 * a * inv l + &2 * inv l pow 2) * exp(--l * a:real)`
     (fun th -> REWRITE_TAC[th]) THEN
   ABBREV_TAC `e = exp(--l * a:real)` THEN REAL_ARITH_TAC]);;

(* Second moment integral sequence tends to 2/l^2 *)
let EXPONENTIAL_SECOND_MOMENT_SEQ_TENDS = prove
 (`!l. &0 < l ==>
  ((\k:num. &2 * inv l pow 2 -
    (&k pow 2 + &2 * &k * inv l + &2 * inv l pow 2) * exp(--l * &k))
   ---> &2 * inv l pow 2) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&2 * inv l pow 2 = &2 * inv l pow 2 - &0` SUBST1_TAC THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_SUB THEN CONJ_TAC THENL
  [REWRITE_TAC[REAL_SUB_RZERO; REALLIM_CONST]; ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  ASM_SIMP_TAC[EXPONENTIAL_PRODUCT_DECAY_SEQ]);;

(* Second moment: E[X^2] = 2/l^2 *)
let EXPONENTIAL_SECOND_MOMENT = prove
 (`!l. &0 < l ==>
   ((\x. x pow 2 * exponential_density l x) has_real_integral
    &2 * inv l pow 2)
   {x | &0 <= x}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[exponential_density] THEN
  REWRITE_TAC[REAL_ARITH `x2 * (if &0 <= x then l * e else &0) =
    (if &0 <= x then x2 * l * e else &0)`] THEN
  ONCE_REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
  CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN
    `(\x:real. if &0 <= x
               then if &0 <= x then x pow 2 * l * exp(--l * x) else &0
               else &0) =
     (\x. if &0 <= x then x pow 2 * l * exp(--l * x) else &0)`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
   COND_CASES_TAC THEN REWRITE_TAC[];
   ALL_TAC] THEN
  ABBREV_TAC
    `g = \x:real. if &0 <= x then l * x pow 2 * exp(--l * x) else &0` THEN
  ABBREV_TAC
    `f = \k x:real. if &0 <= x /\ x <= &k then l * x pow 2 * exp(--l * x)
                    else &0` THEN
  SUBGOAL_THEN
    `(\x:real. if &0 <= x then x pow 2 * l * exp(--l * x) else &0) = g`
    SUBST1_TAC THENL
  [EXPAND_TAC "g" THEN REWRITE_TAC[FUN_EQ_THM] THEN
   GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_AC];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `g real_integrable_on (:real) /\
     ((\k. real_integral (:real) (f k)) ---> real_integral (:real) g)
     sequentially`
    STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_MONOTONE_CONVERGENCE_INCREASING THEN
   REPEAT CONJ_TAC THENL
   [(* f_k integrable *)
    X_GEN_TAC `k:num` THEN EXPAND_TAC "f" THEN
    SUBGOAL_THEN
      `(\x. if &0 <= x /\ x <= &k
            then l * x pow 2 * exp(--l * x) else &0) =
       (\x. if x IN real_interval[&0,&k]
            then l * x pow 2 * exp(--l * x) else &0)`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM; IN_REAL_INTERVAL] THEN MESON_TAC[];
     REWRITE_TAC[real_integrable_on] THEN
     EXISTS_TAC `&2 * inv l pow 2 -
       (&k pow 2 + &2 * &k * inv(l:real) + &2 * inv l pow 2) *
       exp(--l * &k)` THEN
     REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
     MATCH_MP_TAC EXPONENTIAL_SECOND_MOMENT_INTEGRAL_INTERVAL THEN
     ASM_REWRITE_TAC[REAL_POS]];
    (* monotonicity *)
    X_GEN_TAC `k:num` THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    EXPAND_TAC "f" THEN REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]) THEN
    TRY(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
        [ASM_REAL_ARITH_TAC;
         MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [REWRITE_TAC[REAL_LE_POW_2];
          REWRITE_TAC[REAL_EXP_POS_LE]]]) THEN
    ASM_REAL_ARITH_TAC;
    (* pointwise convergence *)
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    EXPAND_TAC "f" THEN EXPAND_TAC "g" THEN
    ASM_CASES_TAC `&0 <= x` THENL
    [ASM_REWRITE_TAC[] THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
     X_GEN_TAC `e:real` THEN DISCH_TAC THEN
     MP_TAC(SPEC `x:real` REAL_ARCH_SIMPLE) THEN
     DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
     EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
     SUBGOAL_THEN `x <= &n` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N` THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM] THEN
      ASM_REAL_ARITH_TAC];
     ASM_REWRITE_TAC[] THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
     X_GEN_TAC `e:real` THEN DISCH_TAC THEN EXISTS_TAC `0` THEN
     X_GEN_TAC `n:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
     ASM_REAL_ARITH_TAC];
    (* bounded integrals *)
    REWRITE_TAC[real_bounded; FORALL_IN_GSPEC; IN_UNIV] THEN
    EXISTS_TAC `&2 * inv(l:real) pow 2` THEN X_GEN_TAC `k:num` THEN
    SUBGOAL_THEN
      `real_integral (:real) ((f:num->real->real) k) =
       &2 * inv l pow 2 -
       (&k pow 2 + &2 * &k * inv l + &2 * inv l pow 2) * exp(--l * &k)`
      SUBST1_TAC THENL
    [EXPAND_TAC "f" THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
     SUBGOAL_THEN
       `(\x. if &0 <= x /\ x <= &k
             then l * x pow 2 * exp(--l * x) else &0) =
        (\x. if x IN real_interval[&0,&k]
             then l * x pow 2 * exp(--l * x) else &0)`
       SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; IN_REAL_INTERVAL] THEN MESON_TAC[];
      REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
      MATCH_MP_TAC EXPONENTIAL_SECOND_MOMENT_INTEGRAL_INTERVAL THEN
      ASM_REWRITE_TAC[REAL_POS]];
     SUBGOAL_THEN
       `&0 <= &2 * inv l pow 2 -
        (&k pow 2 + &2 * &k * inv l + &2 * inv l pow 2) * exp(--l * &k)`
       MP_TAC THENL
     [MATCH_MP_TAC HAS_REAL_INTEGRAL_POS THEN
      EXISTS_TAC `\x:real. l * x pow 2 * exp(--l * x)` THEN
      EXISTS_TAC `real_interval[&0,&k]` THEN CONJ_TAC THENL
      [MATCH_MP_TAC EXPONENTIAL_SECOND_MOMENT_INTEGRAL_INTERVAL THEN
       ASM_REWRITE_TAC[REAL_POS];
       REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
       MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
        [REWRITE_TAC[REAL_LE_POW_2];
         REWRITE_TAC[REAL_EXP_POS_LE]]]];
      SUBGOAL_THEN
        `&0 <= (&k pow 2 + &2 * &k * inv l + &2 * inv l pow 2) *
               exp(--l * &k)` MP_TAC THENL
      [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
       MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
       MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
        [REAL_ARITH_TAC;
         MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [REWRITE_TAC[REAL_POS];
          MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC]];
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
        [REAL_ARITH_TAC; REWRITE_TAC[REAL_LE_POW_2]]];
       REAL_ARITH_TAC]]]];
   ALL_TAC] THEN
  SUBGOAL_THEN `real_integral (:real) g = &2 * inv l pow 2`
    (fun th -> ONCE_REWRITE_TAC[SYM th] THEN
               REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL] THEN
               ASM_REWRITE_TAC[]) THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC `\k:num. real_integral (:real) ((f:num->real->real) k)` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  SUBGOAL_THEN
    `(\k. real_integral (:real) ((f:num->real->real) k)) =
     (\k. &2 * inv l pow 2 -
      (&k pow 2 + &2 * &k * inv l + &2 * inv l pow 2) * exp(--l * &k))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `k:num` THEN
   EXPAND_TAC "f" THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
   SUBGOAL_THEN
     `(\x. if &0 <= x /\ x <= &k
           then l * x pow 2 * exp(--l * x) else &0) =
      (\x. if x IN real_interval[&0,&k]
           then l * x pow 2 * exp(--l * x) else &0)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; IN_REAL_INTERVAL] THEN MESON_TAC[];
    REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
    MATCH_MP_TAC EXPONENTIAL_SECOND_MOMENT_INTEGRAL_INTERVAL THEN
    ASM_REWRITE_TAC[REAL_POS]];
   ASM_SIMP_TAC[EXPONENTIAL_SECOND_MOMENT_SEQ_TENDS]]);;

(* Second moment as integral value *)
let EXPONENTIAL_SECOND_MOMENT_INTEGRAL = prove
 (`!l. &0 < l ==>
   real_integral {x | &0 <= x}
     (\x. x pow 2 * exponential_density l x) = &2 * inv l pow 2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  ASM_SIMP_TAC[EXPONENTIAL_SECOND_MOMENT]);;

(* Variance: Var(X) = E[X^2] - (E[X])^2 = 2/l^2 - 1/l^2 = 1/l^2 *)
let EXPONENTIAL_VARIANCE_INTEGRAL = prove
 (`!l. &0 < l ==>
   real_integral {x | &0 <= x}
     (\x. (x - inv l) pow 2 * exponential_density l x) = inv l pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `(\x. (x - inv l) pow 2 * exponential_density l x) =
     (\x. x pow 2 * exponential_density l x -
          &2 * inv l * (x * exponential_density l x) +
          inv l pow 2 * exponential_density l x)`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
   REWRITE_TAC[REAL_POW_2;
     REAL_ARITH `(x - c) * (x - c) = x * x - &2 * c * x + c * c`] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `((\x. x pow 2 * exponential_density l x) has_real_integral
     &2 * inv l pow 2) {x | &0 <= x}`
    ASSUME_TAC THENL
  [ASM_SIMP_TAC[EXPONENTIAL_SECOND_MOMENT]; ALL_TAC] THEN
  SUBGOAL_THEN
    `((\x. x * exponential_density l x) has_real_integral inv l)
     {x | &0 <= x}`
    ASSUME_TAC THENL
  [ASM_SIMP_TAC[EXPONENTIAL_MEAN]; ALL_TAC] THEN
  SUBGOAL_THEN
    `(exponential_density l has_real_integral &1) {x | &0 <= x}`
    ASSUME_TAC THENL
  [MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
   EXISTS_TAC `\x:real. l * exp(--l * x)` THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; exponential_density] THEN MESON_TAC[];
    ASM_SIMP_TAC[EXPONENTIAL_DENSITY_INTEGRAL]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `((\x. x pow 2 * exponential_density l x -
           &2 * inv l * (x * exponential_density l x) +
           inv l pow 2 * exponential_density l x) has_real_integral
     (&2 * inv l pow 2 - &2 * inv l * inv l + inv l pow 2 * &1))
    {x | &0 <= x}`
    (fun th -> MP_TAC(MATCH_MP REAL_INTEGRAL_UNIQUE th) THEN
      SUBGOAL_THEN
        `&2 * inv l pow 2 - &2 * inv l * inv l + inv l pow 2 * &1 =
         inv(l:real) pow 2`
        SUBST1_TAC THENL
      [REWRITE_TAC[REAL_POW_2; REAL_MUL_RID] THEN REAL_ARITH_TAC;
       SIMP_TAC[]]) THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_ADD THEN CONJ_TAC THENL
  [MATCH_MP_TAC HAS_REAL_INTEGRAL_SUB THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN ASM_REWRITE_TAC[]];
   MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
   REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]]);;

(* ===================================================================== *)
(* Continuous Uniform Distribution on [a,b]                              *)
(* ===================================================================== *)

let uniform_density = new_definition
  `uniform_density (a:real) (b:real) (x:real) =
   if a <= x /\ x <= b then inv(b - a) else &0`;;

let uniform_cdf = new_definition
  `uniform_cdf (a:real) (b:real) (x:real) =
   if x < a then &0
   else if b <= x then &1
   else (x - a) / (b - a)`;;

(* Basic properties of the density *)

let UNIFORM_DENSITY_NONNEG = prove
 (`!a b x. a < b ==> &0 <= uniform_density a b x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[uniform_density] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC);;

let UNIFORM_DENSITY_POS = prove
 (`!a b x. a < b /\ a <= x /\ x <= b ==> &0 < uniform_density a b x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[uniform_density] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC);;

let UNIFORM_DENSITY_ZERO = prove
 (`!a b x. x < a \/ b < x ==> uniform_density a b x = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[uniform_density] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let UNIFORM_DENSITY_VALUE = prove
 (`!a b x. a <= x /\ x <= b ==> uniform_density a b x = inv(b - a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[uniform_density] THEN
  ASM_REWRITE_TAC[]);;

(* Density integrates to 1 *)

let UNIFORM_DENSITY_INTEGRAL = prove
 (`!a b. a < b ==>
   (uniform_density a b has_real_integral &1) (:real)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(b - a = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `uniform_density a b =
     (\x:real. if x IN real_interval[a,b] then inv(b - a) else &0)`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; IN_REAL_INTERVAL; uniform_density]; ALL_TAC] THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
  SUBGOAL_THEN `&1 = inv(b - a) * (b - a:real)` SUBST1_TAC THENL
  [ASM_SIMP_TAC[REAL_MUL_LINV]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_CONST THEN ASM_REAL_ARITH_TAC);;

let UNIFORM_DENSITY_INTEGRABLE = prove
 (`!a b. a < b ==> uniform_density a b real_integrable_on (:real)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_INTEGRABLE THEN
  EXISTS_TAC `&1` THEN ASM_SIMP_TAC[UNIFORM_DENSITY_INTEGRAL]);;

(* CDF properties *)

let UNIFORM_CDF_LEFT = prove
 (`!a b. a < b ==> uniform_cdf a b a = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[uniform_cdf] THEN
  REWRITE_TAC[REAL_LT_REFL] THEN
  SUBGOAL_THEN `~(b <= a)` (fun th -> REWRITE_TAC[th]) THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_REFL; real_div; REAL_MUL_LZERO]);;

let UNIFORM_CDF_RIGHT = prove
 (`!a b. a < b ==> uniform_cdf a b b = &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[uniform_cdf] THEN
  SUBGOAL_THEN `~(b < a)` (fun th -> REWRITE_TAC[th]) THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_LE_REFL]);;

let UNIFORM_CDF_BOUNDS = prove
 (`!a b x. a < b ==> &0 <= uniform_cdf a b x /\ uniform_cdf a b x <= &1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[uniform_cdf] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN
  TRY REAL_ARITH_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
   REWRITE_TAC[real_div] THEN
   SUBGOAL_THEN `&0 < inv(b - a)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `(x - a) * inv(b - a) <= (b - a) * inv(b - a)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_ARITH `a < b ==> ~(b - a = &0)`]]]);;

let UNIFORM_CDF_MONO = prove
 (`!a b x y. a < b /\ x <= y ==> uniform_cdf a b x <= uniform_cdf a b y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[uniform_cdf] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN
  TRY REAL_ARITH_TAC THEN
  TRY(ASM_REAL_ARITH_TAC) THEN
  TRY(MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC) THEN
  REWRITE_TAC[real_div] THEN
  TRY(MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC]) THEN
  SUBGOAL_THEN `&0 < inv(b - a)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(x - a) * inv(b - a) <= (b - a) * inv(b - a)` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
   ASM_SIMP_TAC[REAL_MUL_RINV; REAL_ARITH `a < b ==> ~(b - a = &0)`]]);;

(* Integration helper: integral of identity on [a,b] *)

let IDENTITY_HAS_REAL_INTEGRAL = prove
 (`!a b. a <= b ==>
   ((\x. x) has_real_integral (b pow 2 - a pow 2) / &2)
   (real_interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real. x pow 2 / &2`; `\x:real. x`;
                  `a:real`; `b:real`]
    REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
   REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
   REWRITE_TAC[REAL_ARITH `b / &2 - a / &2 = (b - a) / &2`]]);;

(* Mean of uniform distribution *)

let UNIFORM_MEAN = prove
 (`!a b. a < b ==>
   ((\x. x * uniform_density a b x) has_real_integral (a + b) / &2)
   (:real)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(b - a = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `(\x:real. x * uniform_density a b x) =
     (\x. if x IN real_interval[a,b] then inv(b - a) * x else &0)`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; IN_REAL_INTERVAL; uniform_density] THEN
   GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
  SUBGOAL_THEN
    `(a + b) / &2 = inv(b - a) * ((b pow 2 - a pow 2) / &2)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC(REAL_FIELD
     `~(b - a = &0) ==>
      (a + b) / &2 = inv(b - a) * ((b pow 2 - a pow 2) / &2)`) THEN
   ASM_REWRITE_TAC[];
   MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
   MATCH_MP_TAC IDENTITY_HAS_REAL_INTEGRAL THEN ASM_REAL_ARITH_TAC]);;

let UNIFORM_MEAN_INTEGRAL = prove
 (`!a b. a < b ==>
   real_integral (:real) (\x. x * uniform_density a b x) = (a + b) / &2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  ASM_SIMP_TAC[UNIFORM_MEAN]);;

(* Integration helper: integral of x^2 on [a,b] *)

let SQUARE_HAS_REAL_INTEGRAL = prove
 (`!a b. a <= b ==>
   ((\x. x pow 2) has_real_integral (b pow 3 - a pow 3) / &3)
   (real_interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real. x pow 3 / &3`; `\x:real. x pow 2`;
                  `a:real`; `b:real`]
    REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
   REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
   REWRITE_TAC[REAL_ARITH `b / &3 - a / &3 = (b - a) / &3`]]);;

(* Second moment of uniform distribution *)

let UNIFORM_SECOND_MOMENT = prove
 (`!a b. a < b ==>
   ((\x. x pow 2 * uniform_density a b x) has_real_integral
    (a pow 2 + a * b + b pow 2) / &3) (:real)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(b - a = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `(\x:real. x pow 2 * uniform_density a b x) =
     (\x. if x IN real_interval[a,b] then inv(b - a) * x pow 2 else &0)`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; IN_REAL_INTERVAL; uniform_density] THEN
   GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
  SUBGOAL_THEN
    `(a pow 2 + a * b + b pow 2) / &3 =
     inv(b - a) * ((b pow 3 - a pow 3) / &3)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC(REAL_FIELD
     `~(b - a = &0) ==>
      (a pow 2 + a * b + b pow 2) / &3 =
      inv(b - a) * ((b pow 3 - a pow 3) / &3)`) THEN
   ASM_REWRITE_TAC[];
   MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
   MATCH_MP_TAC SQUARE_HAS_REAL_INTEGRAL THEN ASM_REAL_ARITH_TAC]);;

let UNIFORM_SECOND_MOMENT_INTEGRAL = prove
 (`!a b. a < b ==>
   real_integral (:real) (\x. x pow 2 * uniform_density a b x) =
   (a pow 2 + a * b + b pow 2) / &3`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  ASM_SIMP_TAC[UNIFORM_SECOND_MOMENT]);;

(* Variance of uniform distribution *)

let UNIFORM_VARIANCE_INTEGRAL = prove
 (`!a b. a < b ==>
   real_integral (:real)
     (\x. (x - (a + b) / &2) pow 2 * uniform_density a b x) =
   (b - a) pow 2 / &12`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(b - a = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `mu = (a + b) / &2` THEN
  SUBGOAL_THEN
    `(\x. (x - mu) pow 2 * uniform_density a b x) =
     (\x. x pow 2 * uniform_density a b x -
          &2 * mu * (x * uniform_density a b x) +
          mu pow 2 * uniform_density a b x)`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
   REWRITE_TAC[REAL_POW_2;
     REAL_ARITH `(x - c) * (x - c) = x * x - &2 * c * x + c * c`] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `((\x. x pow 2 * uniform_density a b x) has_real_integral
     (a pow 2 + a * b + b pow 2) / &3) (:real)`
    ASSUME_TAC THENL
  [ASM_SIMP_TAC[UNIFORM_SECOND_MOMENT]; ALL_TAC] THEN
  SUBGOAL_THEN
    `((\x. x * uniform_density a b x) has_real_integral (a + b) / &2)
     (:real)`
    ASSUME_TAC THENL
  [ASM_SIMP_TAC[UNIFORM_MEAN]; ALL_TAC] THEN
  SUBGOAL_THEN
    `(uniform_density a b has_real_integral &1) (:real)`
    ASSUME_TAC THENL
  [ASM_SIMP_TAC[UNIFORM_DENSITY_INTEGRAL]; ALL_TAC] THEN
  SUBGOAL_THEN
    `((\x. x pow 2 * uniform_density a b x -
           &2 * mu * (x * uniform_density a b x) +
           mu pow 2 * uniform_density a b x) has_real_integral
     ((a pow 2 + a * b + b pow 2) / &3 -
      &2 * mu * ((a + b) / &2) +
      mu pow 2 * &1))
    (:real)`
    (fun th -> MP_TAC(MATCH_MP REAL_INTEGRAL_UNIQUE th) THEN
      EXPAND_TAC "mu" THEN
      SUBGOAL_THEN
        `(a pow 2 + a * b + b pow 2) / &3 -
         &2 * ((a + b) / &2) * ((a + b) / &2) +
         ((a + b) / &2) pow 2 * &1 =
         (b - a) pow 2 / &12`
        SUBST1_TAC THENL
      [REWRITE_TAC[REAL_POW_2; REAL_MUL_RID] THEN REAL_ARITH_TAC;
       SIMP_TAC[]]) THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_ADD THEN CONJ_TAC THENL
  [MATCH_MP_TAC HAS_REAL_INTEGRAL_SUB THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN ASM_REWRITE_TAC[]];
   MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
   REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Characteristic function formulas for distributions                        *)
(* ========================================================================= *)

(* ---- General Normal char fn ---- *)

(* Strategy: derive from STD_NORMAL_CHAR_FN_RE/IM via affine substitution.
   The general normal char fn is:
     phi(t) = exp(-sigma^2 * t^2 / 2) * (cos(mu*t) + i*sin(mu*t))
   We first show the shifted integrals (with cos(t*(x-mu)) and sin(t*(x-mu)))
   and then use cos/sin addition to get the final formulas. *)

(* Helper: integral of normal_density * cos(t*(x-mu)) via affine substitution *)
let NORMAL_SHIFTED_COS_INTEGRAL = prove
 (`!mu sigma t. &0 < sigma ==>
    ((\x. normal_density mu sigma x * cos(t * (x - mu)))
     has_real_integral exp(--(sigma pow 2 * t pow 2 / &2))) (:real)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(sigma = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(inv sigma = &0)` ASSUME_TAC THENL
  [ASM_SIMP_TAC[REAL_INV_EQ_0]; ALL_TAC] THEN
  SUBGOAL_THEN
    `(\x. normal_density mu sigma x * cos(t * (x - mu))) =
     (\x. inv(sigma) * (std_normal_density((x - mu) / sigma) *
          cos(t * (x - mu))))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real` THEN
   ASM_SIMP_TAC[NORMAL_DENSITY_STANDARDIZE] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `exp(--(sigma pow 2 * t pow 2 / &2)) =
     inv(sigma) * (sigma * exp(--(sigma pow 2 * t pow 2 / &2)))`
    SUBST1_TAC THENL
  [UNDISCH_TAC `~(sigma = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
  MP_TAC(SPEC `t * sigma:real` STD_NORMAL_CHAR_FN_RE) THEN
  SUBGOAL_THEN
    `(t * sigma) pow 2 / &2 = sigma pow 2 * t pow 2 / &2`
    (fun th -> REWRITE_TAC[th]) THENL
  [REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`\u:real. std_normal_density u * cos((t * sigma) * u)`;
                  `exp(--(sigma pow 2 * t pow 2 / &2)):real`;
                  `inv(sigma):real`; `--(mu / sigma):real`]
    HAS_REAL_INTEGRAL_AFFINITY_UNIV) THEN
  ASM_SIMP_TAC[REAL_INV_EQ_0] THEN
  SUBGOAL_THEN
    `!x:real. inv sigma * x + --(mu / sigma) = (x - mu) / sigma`
    (fun th -> REWRITE_TAC[th]) THENL
  [X_GEN_TAC `x:real` THEN
   UNDISCH_TAC `~(sigma = &0)` THEN CONV_TAC REAL_FIELD;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!x:real. (t * sigma) * ((x - mu) / sigma) = t * (x - mu)`
    (fun th -> REWRITE_TAC[th]) THENL
  [X_GEN_TAC `x:real` THEN
   UNDISCH_TAC `~(sigma = &0)` THEN CONV_TAC REAL_FIELD;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `inv(abs(inv sigma)) * exp(--(sigma pow 2 * t pow 2 / &2)) =
     sigma * exp(--(sigma pow 2 * t pow 2 / &2))`
    (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[REAL_ABS_INV] THEN
  SUBGOAL_THEN `abs sigma = sigma` (fun th -> REWRITE_TAC[th]) THENL
  [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_INV_INV; REAL_MUL_LID]]);;

(* Helper: integral of normal_density * sin(t*(x-mu)) = 0 *)
let NORMAL_SHIFTED_SIN_INTEGRAL = prove
 (`!mu sigma t. &0 < sigma ==>
    ((\x. normal_density mu sigma x * sin(t * (x - mu)))
     has_real_integral &0) (:real)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(sigma = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(inv sigma = &0)` ASSUME_TAC THENL
  [ASM_SIMP_TAC[REAL_INV_EQ_0]; ALL_TAC] THEN
  SUBGOAL_THEN
    `(\x. normal_density mu sigma x * sin(t * (x - mu))) =
     (\x. inv(sigma) * (std_normal_density((x - mu) / sigma) *
          sin(t * (x - mu))))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real` THEN
   ASM_SIMP_TAC[NORMAL_DENSITY_STANDARDIZE] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 = inv(sigma) * &0:real` SUBST1_TAC THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
  MP_TAC(SPEC `t * sigma:real` STD_NORMAL_CHAR_FN_IM) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`\u:real. std_normal_density u * sin((t * sigma) * u)`;
                  `&0:real`;
                  `inv(sigma):real`; `--(mu / sigma):real`]
    HAS_REAL_INTEGRAL_AFFINITY_UNIV) THEN
  ASM_SIMP_TAC[REAL_INV_EQ_0] THEN
  REWRITE_TAC[REAL_MUL_RZERO] THEN
  SUBGOAL_THEN
    `!x:real. inv sigma * x + --(mu / sigma) = (x - mu) / sigma`
    (fun th -> REWRITE_TAC[th]) THENL
  [X_GEN_TAC `x:real` THEN
   UNDISCH_TAC `~(sigma = &0)` THEN CONV_TAC REAL_FIELD;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!x:real. (t * sigma) * ((x - mu) / sigma) = t * (x - mu)`
    (fun th -> REWRITE_TAC[th]) THEN
  X_GEN_TAC `x:real` THEN
  UNDISCH_TAC `~(sigma = &0)` THEN CONV_TAC REAL_FIELD);;

(* Real part of general normal char fn:
   integral of normal_density(x) * cos(t*x) = exp(-sigma^2*t^2/2) * cos(mu*t) *)
let NORMAL_CHAR_FN_RE = prove
 (`!mu sigma t. &0 < sigma ==>
    ((\x. normal_density mu sigma x * cos(t * x)) has_real_integral
     exp(--(sigma pow 2 * t pow 2 / &2)) * cos(mu * t)) (:real)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `!x:real. cos(t * x) =
       cos(t * (x - mu)) * cos(t * mu) - sin(t * (x - mu)) * sin(t * mu)`
    (fun th -> ONCE_REWRITE_TAC[th]) THENL
  [X_GEN_TAC `x:real` THEN
   MP_TAC(SPECL [`t * (x - mu):real`; `t * mu:real`] COS_ADD) THEN
   DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
   AP_TERM_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH
    `d * (c1 * cm - s1 * sm):real = d * c1 * cm - d * s1 * sm`] THEN
  SUBGOAL_THEN
    `exp(--(sigma pow 2 * t pow 2 / &2)) * cos(mu * t) =
     exp(--(sigma pow 2 * t pow 2 / &2)) * cos(t * mu) -
     &0 * sin(t * mu)`
    SUBST1_TAC THENL
  [REWRITE_TAC[REAL_MUL_LZERO; REAL_SUB_RZERO; REAL_MUL_AC]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_SUB THEN CONJ_TAC THENL
  [ONCE_REWRITE_TAC[REAL_ARITH
    `d * c * cm:real = (d * c) * cm`] THEN
   MATCH_MP_TAC HAS_REAL_INTEGRAL_RMUL THEN
   ASM_SIMP_TAC[NORMAL_SHIFTED_COS_INTEGRAL];
   ONCE_REWRITE_TAC[REAL_ARITH
    `d * s * sm:real = (d * s) * sm`] THEN
   MATCH_MP_TAC HAS_REAL_INTEGRAL_RMUL THEN
   ASM_SIMP_TAC[NORMAL_SHIFTED_SIN_INTEGRAL]]);;

(* Imaginary part of general normal char fn:
   integral of normal_density(x) * sin(t*x) = exp(-sigma^2*t^2/2) * sin(mu*t) *)
let NORMAL_CHAR_FN_IM = prove
 (`!mu sigma t. &0 < sigma ==>
    ((\x. normal_density mu sigma x * sin(t * x)) has_real_integral
     exp(--(sigma pow 2 * t pow 2 / &2)) * sin(mu * t)) (:real)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `!x:real. sin(t * x) =
       sin(t * (x - mu)) * cos(t * mu) + cos(t * (x - mu)) * sin(t * mu)`
    (fun th -> ONCE_REWRITE_TAC[th]) THENL
  [X_GEN_TAC `x:real` THEN
   MP_TAC(SPECL [`t * (x - mu):real`; `t * mu:real`] SIN_ADD) THEN
   DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
   AP_TERM_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH
    `d * (s1 * cm + c1 * sm):real = d * s1 * cm + d * c1 * sm`] THEN
  SUBGOAL_THEN
    `exp(--(sigma pow 2 * t pow 2 / &2)) * sin(mu * t) =
     &0 * cos(t * mu) +
     exp(--(sigma pow 2 * t pow 2 / &2)) * sin(t * mu)`
    SUBST1_TAC THENL
  [REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID; REAL_MUL_AC]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_ADD THEN CONJ_TAC THENL
  [ONCE_REWRITE_TAC[REAL_ARITH
    `d * s * cm:real = (d * s) * cm`] THEN
   MATCH_MP_TAC HAS_REAL_INTEGRAL_RMUL THEN
   ASM_SIMP_TAC[NORMAL_SHIFTED_SIN_INTEGRAL];
   ONCE_REWRITE_TAC[REAL_ARITH
    `d * c * sm:real = (d * c) * sm`] THEN
   MATCH_MP_TAC HAS_REAL_INTEGRAL_RMUL THEN
   ASM_SIMP_TAC[NORMAL_SHIFTED_COS_INTEGRAL]]);;

(* ---- Uniform char fn ---- *)

(* FTC helper: integral of cos(t*x) on [a,b] *)
let COS_HAS_REAL_INTEGRAL = prove
 (`!a b t. a <= b /\ ~(t = &0) ==>
    ((\x. cos(t * x)) has_real_integral
     (sin(t * b) - sin(t * a)) / t) (real_interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real. sin(t * x) / t`; `\x:real. cos(t * x)`;
                  `a:real`; `b:real`]
    REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
   REAL_DIFF_TAC THEN UNDISCH_TAC `~(t = &0)` THEN CONV_TAC REAL_FIELD;
   REWRITE_TAC[REAL_ARITH `b / t - a / t = (b - a) / t:real`]]);;

(* FTC helper: integral of sin(t*x) on [a,b] *)
let SIN_HAS_REAL_INTEGRAL = prove
 (`!a b t. a <= b /\ ~(t = &0) ==>
    ((\x. sin(t * x)) has_real_integral
     (cos(t * a) - cos(t * b)) / t) (real_interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real. --(cos(t * x)) / t`; `\x:real. sin(t * x)`;
                  `a:real`; `b:real`]
    REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
   REAL_DIFF_TAC THEN UNDISCH_TAC `~(t = &0)` THEN CONV_TAC REAL_FIELD;
   REWRITE_TAC[REAL_ARITH
     `--(c2:real) / t - --(c1) / t = (c1 - c2) / t`]]);;

(* Real part of uniform char fn *)
let UNIFORM_CHAR_FN_RE = prove
 (`!a b t. a < b /\ ~(t = &0) ==>
    ((\x. uniform_density a b x * cos(t * x)) has_real_integral
     (sin(t * b) - sin(t * a)) / (t * (b - a))) (:real)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(b - a = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `(\x:real. uniform_density a b x * cos(t * x)) =
     (\x. if x IN real_interval[a,b] then inv(b - a) * cos(t * x) else &0)`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; IN_REAL_INTERVAL; uniform_density] THEN
   GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
  SUBGOAL_THEN
    `(sin(t * b) - sin(t * a)) / (t * (b - a)) =
     inv(b - a) * ((sin(t * b) - sin(t * a)) / t)`
    SUBST1_TAC THENL
  [UNDISCH_TAC `~(b - a = &0)` THEN UNDISCH_TAC `~(t = &0)` THEN
   CONV_TAC REAL_FIELD;
   MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
   MATCH_MP_TAC COS_HAS_REAL_INTEGRAL THEN ASM_REAL_ARITH_TAC]);;

(* Imaginary part of uniform char fn *)
let UNIFORM_CHAR_FN_IM = prove
 (`!a b t. a < b /\ ~(t = &0) ==>
    ((\x. uniform_density a b x * sin(t * x)) has_real_integral
     (cos(t * a) - cos(t * b)) / (t * (b - a))) (:real)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(b - a = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `(\x:real. uniform_density a b x * sin(t * x)) =
     (\x. if x IN real_interval[a,b] then inv(b - a) * sin(t * x) else &0)`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; IN_REAL_INTERVAL; uniform_density] THEN
   GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
  SUBGOAL_THEN
    `(cos(t * a) - cos(t * b)) / (t * (b - a)) =
     inv(b - a) * ((cos(t * a) - cos(t * b)) / t)`
    SUBST1_TAC THENL
  [UNDISCH_TAC `~(b - a = &0)` THEN UNDISCH_TAC `~(t = &0)` THEN
   CONV_TAC REAL_FIELD;
   MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
   MATCH_MP_TAC SIN_HAS_REAL_INTEGRAL THEN ASM_REAL_ARITH_TAC]);;

(* ---- Exponential char fn ---- *)

(* Antiderivative for exp(-l*x) * cos(t*x) *)
let EXP_COS_ANTIDERIV = prove
 (`!l t x. &0 < l ==>
    ((\x. exp(--l * x) * (--l * cos(t * x) + t * sin(t * x)) /
          (l pow 2 + t pow 2))
     has_real_derivative (exp(--l * x) * cos(t * x))) (atreal x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(l pow 2 + t pow 2 = &0)` ASSUME_TAC THENL
  [MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 <= b ==> ~(a + b = &0)`) THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_LE_POW_2]];
   ALL_TAC] THEN
  REAL_DIFF_TAC THEN
  UNDISCH_TAC `~(l pow 2 + t pow 2 = &0)` THEN
  UNDISCH_TAC `&0 < l` THEN
  CONV_TAC REAL_FIELD);;

(* Antiderivative for exp(-l*x) * sin(t*x) *)
let EXP_SIN_ANTIDERIV = prove
 (`!l t x. &0 < l ==>
    ((\x. exp(--l * x) * (--l * sin(t * x) - t * cos(t * x)) /
          (l pow 2 + t pow 2))
     has_real_derivative (exp(--l * x) * sin(t * x))) (atreal x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(l pow 2 + t pow 2 = &0)` ASSUME_TAC THENL
  [MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 <= b ==> ~(a + b = &0)`) THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_LE_POW_2]];
   ALL_TAC] THEN
  REAL_DIFF_TAC THEN
  UNDISCH_TAC `~(l pow 2 + t pow 2 = &0)` THEN
  UNDISCH_TAC `&0 < l` THEN
  CONV_TAC REAL_FIELD);;

(* FTC: integral of exp(-l*x) * cos(t*x) on [0,k] *)
let EXP_COS_INTEGRAL_INTERVAL = prove
 (`!l t k. &0 < l /\ &0 <= k ==>
    ((\x. exp(--l * x) * cos(t * x)) has_real_integral
     (l - exp(--l * k) * (l * cos(t * k) - t * sin(t * k))) /
     (l pow 2 + t pow 2))
    (real_interval[&0,k])`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(l pow 2 + t pow 2 = &0)` ASSUME_TAC THENL
  [MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 <= b ==> ~(a + b = &0)`) THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_LE_POW_2]];
   ALL_TAC] THEN
  MP_TAC(ISPECL
    [`\x:real. exp(--l * x) * (--l * cos(t * x) + t * sin(t * x)) /
              (l pow 2 + t pow 2)`;
     `\x:real. exp(--l * x) * cos(t * x)`;
     `&0`; `k:real`]
    REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
   MATCH_MP_TAC EXP_COS_ANTIDERIV THEN ASM_REWRITE_TAC[];
   SUBGOAL_THEN
     `exp(--l * k) * (--l * cos(t * k) + t * sin(t * k)) /
      (l pow 2 + t pow 2) -
      exp(--l * &0) * (--l * cos(t * &0) + t * sin(t * &0)) /
      (l pow 2 + t pow 2) =
      (l - exp(--l * k) * (l * cos(t * k) - t * sin(t * k))) /
      (l pow 2 + t pow 2)`
     (fun th -> REWRITE_TAC[th]) THEN
   REWRITE_TAC[COS_0; SIN_0; REAL_EXP_0; REAL_MUL_RZERO; REAL_NEG_0;
               REAL_MUL_LID; REAL_ADD_RID; REAL_MUL_RID] THEN
   UNDISCH_TAC `~(l pow 2 + t pow 2 = &0)` THEN
   CONV_TAC REAL_FIELD]);;

(* FTC: integral of exp(-l*x) * sin(t*x) on [0,k] *)
let EXP_SIN_INTEGRAL_INTERVAL = prove
 (`!l t k. &0 < l /\ &0 <= k ==>
    ((\x. exp(--l * x) * sin(t * x)) has_real_integral
     (t - exp(--l * k) * (l * sin(t * k) + t * cos(t * k))) /
     (l pow 2 + t pow 2))
    (real_interval[&0,k])`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(l pow 2 + t pow 2 = &0)` ASSUME_TAC THENL
  [MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 <= b ==> ~(a + b = &0)`) THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_LE_POW_2]];
   ALL_TAC] THEN
  MP_TAC(ISPECL
    [`\x:real. exp(--l * x) * (--l * sin(t * x) - t * cos(t * x)) /
              (l pow 2 + t pow 2)`;
     `\x:real. exp(--l * x) * sin(t * x)`;
     `&0`; `k:real`]
    REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
   MATCH_MP_TAC EXP_SIN_ANTIDERIV THEN ASM_REWRITE_TAC[];
   SUBGOAL_THEN
     `exp(--l * k) * (--l * sin(t * k) - t * cos(t * k)) /
      (l pow 2 + t pow 2) -
      exp(--l * &0) * (--l * sin(t * &0) - t * cos(t * &0)) /
      (l pow 2 + t pow 2) =
      (t - exp(--l * k) * (l * sin(t * k) + t * cos(t * k))) /
      (l pow 2 + t pow 2)`
     (fun th -> REWRITE_TAC[th]) THEN
   REWRITE_TAC[COS_0; SIN_0; REAL_EXP_0; REAL_MUL_RZERO; REAL_NEG_0;
               REAL_MUL_LID; REAL_SUB_RZERO; REAL_MUL_RID] THEN
   UNDISCH_TAC `~(l pow 2 + t pow 2 = &0)` THEN
   CONV_TAC REAL_FIELD]);;

(* Exponential density integrable on {x | 0 <= x} - reusable from existing *)
let EXPONENTIAL_DENSITY_INTEGRABLE_NONNEG = prove
 (`!l. &0 < l ==>
    (\x. if &0 <= x then l * exp(--l * x) else &0)
    real_integrable_on (:real)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_INTEGRABLE THEN
  EXISTS_TAC `&1` THEN
  SUBGOAL_THEN
    `(\x:real. if &0 <= x then l * exp(--l * x) else &0) =
     (\x. if x IN {x | &0 <= x} then l * exp(--l * x) else &0)`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; IN_ELIM_THM]; ALL_TAC] THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
  ASM_SIMP_TAC[EXPONENTIAL_DENSITY_INTEGRAL]);;

(* Real part of exponential char fn via dominated convergence *)
let EXPONENTIAL_CHAR_FN_RE = prove
 (`!l t. &0 < l ==>
    ((\x. exponential_density l x * cos(t * x)) has_real_integral
     l pow 2 / (l pow 2 + t pow 2)) {x | &0 <= x}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(l pow 2 + t pow 2 = &0)` ASSUME_TAC THENL
  [MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 <= b ==> ~(a + b = &0)`) THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_LE_POW_2]];
   ALL_TAC] THEN
  REWRITE_TAC[exponential_density] THEN
  REWRITE_TAC[REAL_ARITH
    `(if &0 <= x then l * e else &0) * c =
     (if &0 <= x then l * e * c else &0)`] THEN
  ONCE_REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN
    `(\x:real. if &0 <= x then if &0 <= x then l * exp(--l * x) * cos(t * x)
               else &0 else &0) =
     (\x. if &0 <= x then l * exp(--l * x) * cos(t * x) else &0)`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
   COND_CASES_TAC THEN REWRITE_TAC[];
   ALL_TAC] THEN
  ABBREV_TAC
    `g = \x:real. if &0 <= x then l * exp(--l * x) * cos(t * x) else &0` THEN
  ABBREV_TAC
    `f = \k x:real. if &0 <= x /\ x <= &k then l * exp(--l * x) * cos(t * x)
                    else &0` THEN
  ABBREV_TAC
    `h = \x:real. if &0 <= x then l * exp(--l * x) else &0` THEN
  (* Apply dominated convergence *)
  SUBGOAL_THEN
    `g real_integrable_on (:real) /\
     ((\k. real_integral (:real) (f k)) ---> real_integral (:real) g)
     sequentially`
    STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_DOMINATED_CONVERGENCE THEN
   EXISTS_TAC `h:real->real` THEN REPEAT CONJ_TAC THENL
   [(* f_k integrable *)
    X_GEN_TAC `k:num` THEN EXPAND_TAC "f" THEN
    SUBGOAL_THEN
      `(\x. if &0 <= x /\ x <= &k then l * exp(--l * x) * cos(t * x)
            else &0) =
       (\x. if x IN real_interval[&0,&k]
            then l * exp(--l * x) * cos(t * x) else &0)`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM; IN_REAL_INTERVAL] THEN MESON_TAC[];
     REWRITE_TAC[real_integrable_on] THEN
     EXISTS_TAC `l * (l - exp(--l * &k) *
       (l * cos(t * &k) - t * sin(t * &k))) /
       (l pow 2 + t pow 2)` THEN
     REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
     ONCE_REWRITE_TAC[REAL_ARITH
       `l * e * c:real = l * (e * c)`] THEN
     MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
     MATCH_MP_TAC EXP_COS_INTEGRAL_INTERVAL THEN
     ASM_REWRITE_TAC[REAL_POS]];
    (* h integrable *)
    EXPAND_TAC "h" THEN ASM_SIMP_TAC[EXPONENTIAL_DENSITY_INTEGRABLE_NONNEG];
    (* |f_k(x)| <= h(x) *)
    X_GEN_TAC `k:num` THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    EXPAND_TAC "f" THEN EXPAND_TAC "h" THEN
    ASM_CASES_TAC `&0 <= x` THENL
    [ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL
     [REWRITE_TAC[REAL_ABS_MUL] THEN
      SUBGOAL_THEN `abs l = l` (fun th -> REWRITE_TAC[th]) THENL
      [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `abs(exp(--l * x)) = exp(--l * x)`
        (fun th -> REWRITE_TAC[th]) THENL
      [REWRITE_TAC[REAL_ABS_REFL; REAL_EXP_POS_LE]; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_EXP_POS_LE]];
       REWRITE_TAC[COS_BOUND]];
      REWRITE_TAC[REAL_ABS_NUM] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
      [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_EXP_POS_LE]]];
     ASM_REWRITE_TAC[REAL_ABS_NUM; REAL_LE_REFL]];
    (* pointwise convergence *)
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    EXPAND_TAC "f" THEN EXPAND_TAC "g" THEN
    ASM_CASES_TAC `&0 <= x` THENL
    [ASM_REWRITE_TAC[] THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
     X_GEN_TAC `e:real` THEN DISCH_TAC THEN
     MP_TAC(SPEC `x:real` REAL_ARCH_SIMPLE) THEN
     DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
     EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
     SUBGOAL_THEN `x <= &n` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N` THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM] THEN
      ASM_REAL_ARITH_TAC];
     ASM_REWRITE_TAC[] THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
     X_GEN_TAC `e:real` THEN DISCH_TAC THEN EXISTS_TAC `0` THEN
     X_GEN_TAC `n:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
     ASM_REAL_ARITH_TAC]];
   ALL_TAC] THEN
  (* Now extract the integral value *)
  SUBGOAL_THEN `real_integral (:real) g = l pow 2 / (l pow 2 + t pow 2)`
    (fun th -> ONCE_REWRITE_TAC[SYM th] THEN
               REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL] THEN
               ASM_REWRITE_TAC[]) THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC `\k:num. real_integral (:real) ((f:num->real->real) k)` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  (* Show the sequence of integrals equals the closed-form expressions *)
  SUBGOAL_THEN
    `(\k. real_integral (:real) ((f:num->real->real) k)) =
     (\k. l * (l - exp(--l * &k) *
       (l * cos(t * &k) - t * sin(t * &k))) /
       (l pow 2 + t pow 2))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `k:num` THEN
   EXPAND_TAC "f" THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
   SUBGOAL_THEN
     `(\x. if &0 <= x /\ x <= &k then l * exp(--l * x) * cos(t * x)
           else &0) =
      (\x. if x IN real_interval[&0,&k]
           then l * exp(--l * x) * cos(t * x) else &0)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; IN_REAL_INTERVAL] THEN MESON_TAC[];
    REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
    ONCE_REWRITE_TAC[REAL_ARITH
      `l * e * c:real = l * (e * c)`] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
    MATCH_MP_TAC EXP_COS_INTEGRAL_INTERVAL THEN
    ASM_REWRITE_TAC[REAL_POS]];
   ALL_TAC] THEN
  (* Show limit of closed-form = l^2 / (l^2 + t^2) *)
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [real_div] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o RATOR_CONV o RAND_CONV)
    [REAL_POW_2] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REALLIM_LMUL THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM real_div] THEN
  SUBGOAL_THEN
    `l / (l pow 2 + t pow 2) =
     (l - &0) / (l pow 2 + t pow 2)`
    SUBST1_TAC THENL
  [REWRITE_TAC[REAL_SUB_RZERO]; ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_DIV THEN
  ASM_REWRITE_TAC[REALLIM_CONST] THEN
  MATCH_MP_TAC REALLIM_SUB THEN
  REWRITE_TAC[REALLIM_CONST] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\k:num. (abs l + abs t) * exp(--l * &k)` THEN CONJ_TAC THENL
  [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
   X_GEN_TAC `n:num` THEN DISCH_TAC THEN
   REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_EXP] THEN
   GEN_REWRITE_TAC (RAND_CONV) [REAL_MUL_SYM] THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
   MATCH_MP_TAC(REAL_ARITH
     `abs(a * c) <= abs a /\ abs(b * s) <= abs b
      ==> abs(a * c - b * s) <= abs a + abs b`) THEN
   CONJ_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
   GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN
   REWRITE_TAC[REAL_ABS_POS] THEN REWRITE_TAC[COS_BOUND; SIN_BOUND];
   MATCH_MP_TAC REALLIM_NULL_LMUL THEN
   MP_TAC(SPEC `l:real` EXPONENTIAL_LIMIT_POSINFINITY) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o MATCH_MP REALLIM_POSINFINITY_SEQUENTIALLY) THEN
   REWRITE_TAC[]]);;

(* Imaginary part of exponential char fn *)
let EXPONENTIAL_CHAR_FN_IM = prove
 (`!l t. &0 < l ==>
    ((\x. exponential_density l x * sin(t * x)) has_real_integral
     l * t / (l pow 2 + t pow 2)) {x | &0 <= x}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(l pow 2 + t pow 2 = &0)` ASSUME_TAC THENL
  [MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 <= b ==> ~(a + b = &0)`) THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_LE_POW_2]];
   ALL_TAC] THEN
  REWRITE_TAC[exponential_density] THEN
  REWRITE_TAC[REAL_ARITH
    `(if &0 <= x then l * e else &0) * s =
     (if &0 <= x then l * e * s else &0)`] THEN
  ONCE_REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN
    `(\x:real. if &0 <= x then if &0 <= x then l * exp(--l * x) * sin(t * x)
               else &0 else &0) =
     (\x. if &0 <= x then l * exp(--l * x) * sin(t * x) else &0)`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
   COND_CASES_TAC THEN REWRITE_TAC[];
   ALL_TAC] THEN
  ABBREV_TAC
    `g = \x:real. if &0 <= x then l * exp(--l * x) * sin(t * x) else &0` THEN
  ABBREV_TAC
    `f = \k x:real. if &0 <= x /\ x <= &k then l * exp(--l * x) * sin(t * x)
                    else &0` THEN
  ABBREV_TAC
    `h = \x:real. if &0 <= x then l * exp(--l * x) else &0` THEN
  SUBGOAL_THEN
    `g real_integrable_on (:real) /\
     ((\k. real_integral (:real) (f k)) ---> real_integral (:real) g)
     sequentially`
    STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_DOMINATED_CONVERGENCE THEN
   EXISTS_TAC `h:real->real` THEN REPEAT CONJ_TAC THENL
   [(* f_k integrable *)
    X_GEN_TAC `k:num` THEN EXPAND_TAC "f" THEN
    SUBGOAL_THEN
      `(\x. if &0 <= x /\ x <= &k then l * exp(--l * x) * sin(t * x)
            else &0) =
       (\x. if x IN real_interval[&0,&k]
            then l * exp(--l * x) * sin(t * x) else &0)`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM; IN_REAL_INTERVAL] THEN MESON_TAC[];
     REWRITE_TAC[real_integrable_on] THEN
     EXISTS_TAC `l * (t - exp(--l * &k) *
       (l * sin(t * &k) + t * cos(t * &k))) /
       (l pow 2 + t pow 2)` THEN
     REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
     ONCE_REWRITE_TAC[REAL_ARITH
       `l * e * s:real = l * (e * s)`] THEN
     MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
     MATCH_MP_TAC EXP_SIN_INTEGRAL_INTERVAL THEN
     ASM_REWRITE_TAC[REAL_POS]];
    (* h integrable *)
    EXPAND_TAC "h" THEN ASM_SIMP_TAC[EXPONENTIAL_DENSITY_INTEGRABLE_NONNEG];
    (* |f_k(x)| <= h(x) *)
    X_GEN_TAC `k:num` THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    EXPAND_TAC "f" THEN EXPAND_TAC "h" THEN
    ASM_CASES_TAC `&0 <= x` THENL
    [ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL
     [REWRITE_TAC[REAL_ABS_MUL] THEN
      SUBGOAL_THEN `abs l = l` (fun th -> REWRITE_TAC[th]) THENL
      [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `abs(exp(--l * x)) = exp(--l * x)`
        (fun th -> REWRITE_TAC[th]) THENL
      [REWRITE_TAC[REAL_ABS_REFL; REAL_EXP_POS_LE]; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_EXP_POS_LE]];
       REWRITE_TAC[SIN_BOUND]];
      REWRITE_TAC[REAL_ABS_NUM] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
      [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_EXP_POS_LE]]];
     ASM_REWRITE_TAC[REAL_ABS_NUM; REAL_LE_REFL]];
    (* pointwise convergence *)
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    EXPAND_TAC "f" THEN EXPAND_TAC "g" THEN
    ASM_CASES_TAC `&0 <= x` THENL
    [ASM_REWRITE_TAC[] THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
     X_GEN_TAC `e:real` THEN DISCH_TAC THEN
     MP_TAC(SPEC `x:real` REAL_ARCH_SIMPLE) THEN
     DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
     EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
     SUBGOAL_THEN `x <= &n` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N` THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM] THEN
      ASM_REAL_ARITH_TAC];
     ASM_REWRITE_TAC[] THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
     X_GEN_TAC `e:real` THEN DISCH_TAC THEN EXISTS_TAC `0` THEN
     X_GEN_TAC `n:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
     ASM_REAL_ARITH_TAC]];
   ALL_TAC] THEN
  SUBGOAL_THEN `real_integral (:real) g = l * t / (l pow 2 + t pow 2)`
    (fun th -> ONCE_REWRITE_TAC[SYM th] THEN
               REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL] THEN
               ASM_REWRITE_TAC[]) THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC `\k:num. real_integral (:real) ((f:num->real->real) k)` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  SUBGOAL_THEN
    `(\k. real_integral (:real) ((f:num->real->real) k)) =
     (\k. l * (t - exp(--l * &k) *
       (l * sin(t * &k) + t * cos(t * &k))) /
       (l pow 2 + t pow 2))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `k:num` THEN
   EXPAND_TAC "f" THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
   SUBGOAL_THEN
     `(\x. if &0 <= x /\ x <= &k then l * exp(--l * x) * sin(t * x)
           else &0) =
      (\x. if x IN real_interval[&0,&k]
           then l * exp(--l * x) * sin(t * x) else &0)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; IN_REAL_INTERVAL] THEN MESON_TAC[];
    REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
    ONCE_REWRITE_TAC[REAL_ARITH
      `l * e * s:real = l * (e * s)`] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
    MATCH_MP_TAC EXP_SIN_INTEGRAL_INTERVAL THEN
    ASM_REWRITE_TAC[REAL_POS]];
   ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_LMUL THEN
  SUBGOAL_THEN
    `t / (l pow 2 + t pow 2) =
     (t - &0) / (l pow 2 + t pow 2)`
    SUBST1_TAC THENL
  [REWRITE_TAC[REAL_SUB_RZERO]; ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_DIV THEN
  ASM_REWRITE_TAC[REALLIM_CONST] THEN
  MATCH_MP_TAC REALLIM_SUB THEN
  REWRITE_TAC[REALLIM_CONST] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\k:num. (abs l + abs t) * exp(--l * &k)` THEN CONJ_TAC THENL
  [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
   X_GEN_TAC `n:num` THEN DISCH_TAC THEN
   REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_EXP] THEN
   GEN_REWRITE_TAC (RAND_CONV) [REAL_MUL_SYM] THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
   MATCH_MP_TAC(REAL_ARITH
     `abs(a * s) <= abs a /\ abs(b * c) <= abs b
      ==> abs(a * s + b * c) <= abs a + abs b`) THEN
   CONJ_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
   GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN
   REWRITE_TAC[REAL_ABS_POS] THEN REWRITE_TAC[SIN_BOUND; COS_BOUND];
   MATCH_MP_TAC REALLIM_NULL_LMUL THEN
   MP_TAC(SPEC `l:real` EXPONENTIAL_LIMIT_POSINFINITY) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o MATCH_MP REALLIM_POSINFINITY_SEQUENTIALLY) THEN
   REWRITE_TAC[]]);;

(* ------------------------------------------------------------------ *)
(*   Bernoulli characteristic function                                  *)
(* ------------------------------------------------------------------ *)

let BERNOULLI_CHAR_FN_RE = prove
 (`!p:A prob_space X q t. bernoulli_rv p X q ==>
     simple_char_fn_re p X t = (&1 - q) + q * cos t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bernoulli_rv]) THEN
  REWRITE_TAC[simple_char_fn_re] THEN
  FIRST_ASSUM(fun th ->
    MP_TAC(MATCH_MP SIMPLE_EXPECTATION_COMPOSE_SUM th)) THEN
  DISCH_THEN(MP_TAC o SPEC `\u:real. cos(t * u)`) THEN
  BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
    `IMAGE (X:A->real) (prob_carrier p) SUBSET IMAGE (\k:num. &k) (0..1)`
    ASSUME_TAC THENL
  [REWRITE_TAC[SUBSET; IN_IMAGE; IN_NUMSEG; LE_0] THEN
   ASM_MESON_TAC[ARITH_RULE `0 <= 1`; LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN
    `sum (IMAGE (X:A->real) (prob_carrier p))
       (\u. cos(t * u) * prob p {x | x IN prob_carrier p /\ X x = u}) =
     sum (IMAGE (\k:num. &k) (0..1))
       (\u. cos(t * u) * prob (p:A prob_space)
              {x:A | x IN prob_carrier p /\ (X:A->real) x = u})`
    SUBST1_TAC THENL
  [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    X_GEN_TAC `v:real` THEN REWRITE_TAC[IN_IMAGE; IN_NUMSEG; LE_0] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ (X:A->real) x = v} = {}`
      (fun th -> REWRITE_TAC[th; PROB_EMPTY; REAL_MUL_RZERO]) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[]]; ALL_TAC] THEN
  SIMP_TAC[FINITE_NUMSEG; SUM_IMAGE; IN_NUMSEG; LE_0; REAL_OF_NUM_EQ] THEN
  REWRITE_TAC[o_DEF] THEN BETA_TAC THEN
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`; SUM_CLAUSES_NUMSEG; LE_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_MUL_RZERO; COS_0; REAL_MUL_LID; REAL_MUL_RID] THEN
  SUBGOAL_THEN
    `prob (p:A prob_space) {x:A | x IN prob_carrier p /\ (X:A->real) x = &0} =
     &1 - q`
    SUBST1_TAC THENL
  [MATCH_MP_TAC BERNOULLI_RV_PROB_ZERO THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let BERNOULLI_CHAR_FN_IM = prove
 (`!p:A prob_space X q t. bernoulli_rv p X q ==>
     simple_char_fn_im p X t = q * sin t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bernoulli_rv]) THEN
  REWRITE_TAC[simple_char_fn_im] THEN
  FIRST_ASSUM(fun th ->
    MP_TAC(MATCH_MP SIMPLE_EXPECTATION_COMPOSE_SUM th)) THEN
  DISCH_THEN(MP_TAC o SPEC `\u:real. sin(t * u)`) THEN
  BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
    `IMAGE (X:A->real) (prob_carrier p) SUBSET IMAGE (\k:num. &k) (0..1)`
    ASSUME_TAC THENL
  [REWRITE_TAC[SUBSET; IN_IMAGE; IN_NUMSEG; LE_0] THEN
   ASM_MESON_TAC[ARITH_RULE `0 <= 1`; LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN
    `sum (IMAGE (X:A->real) (prob_carrier p))
       (\u. sin(t * u) * prob p {x | x IN prob_carrier p /\ X x = u}) =
     sum (IMAGE (\k:num. &k) (0..1))
       (\u. sin(t * u) * prob (p:A prob_space)
              {x:A | x IN prob_carrier p /\ (X:A->real) x = u})`
    SUBST1_TAC THENL
  [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    X_GEN_TAC `v:real` THEN REWRITE_TAC[IN_IMAGE; IN_NUMSEG; LE_0] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ (X:A->real) x = v} = {}`
      (fun th -> REWRITE_TAC[th; PROB_EMPTY; REAL_MUL_RZERO]) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[]]; ALL_TAC] THEN
  SIMP_TAC[FINITE_NUMSEG; SUM_IMAGE; IN_NUMSEG; LE_0; REAL_OF_NUM_EQ] THEN
  REWRITE_TAC[o_DEF] THEN BETA_TAC THEN
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`; SUM_CLAUSES_NUMSEG; LE_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_MUL_RZERO; SIN_0; REAL_MUL_LZERO; REAL_ADD_LID;
              REAL_MUL_RID] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------ *)
(*   Binomial characteristic function                                   *)
(* ------------------------------------------------------------------ *)

let BINOMIAL_CHAR_FN_RE = prove
 (`!p:A prob_space X n q t. binomial_rv p X n q ==>
     simple_char_fn_re p X t =
     sum (0..n) (\k. &(binom(n,k)) * q pow k * (&1 - q) pow (n - k) *
                     cos(t * &k))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[binomial_rv] THEN STRIP_TAC THEN
  REWRITE_TAC[simple_char_fn_re] THEN
  FIRST_ASSUM(fun th ->
    MP_TAC(MATCH_MP SIMPLE_EXPECTATION_COMPOSE_SUM th)) THEN
  DISCH_THEN(MP_TAC o SPEC `\u:real. cos(t * u)`) THEN
  BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `IMAGE (X:A->real) (prob_carrier p) SUBSET {&k | k <= n}`
    ASSUME_TAC THENL
  [REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `sum (IMAGE (X:A->real) (prob_carrier p))
       (\u. cos(t * u) * prob p {x | x IN prob_carrier p /\ X x = u}) =
     sum (IMAGE (\k:num. &k) (0..n))
       (\u. cos(t * u) * prob (p:A prob_space)
              {x:A | x IN prob_carrier p /\ (X:A->real) x = u})`
    SUBST1_TAC THENL
  [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
      (REWRITE_RULE[IMP_CONJ] SUBSET_TRANS)) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE; IN_NUMSEG; LE_0] THEN
    MESON_TAC[];
    X_GEN_TAC `v:real` THEN REWRITE_TAC[IN_IMAGE; IN_NUMSEG; LE_0] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ (X:A->real) x = v} = {}`
      (fun th -> REWRITE_TAC[th; PROB_EMPTY; REAL_MUL_RZERO]) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[]];
   ALL_TAC] THEN
  SIMP_TAC[FINITE_NUMSEG; SUM_IMAGE; IN_NUMSEG; LE_0; REAL_OF_NUM_EQ] THEN
  REWRITE_TAC[o_DEF] THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:num` THEN
  REWRITE_TAC[IN_NUMSEG; LE_0] THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `prob (p:A prob_space) {x:A | x IN prob_carrier p /\ (X:A->real) x = &k} =
     &(binom(n,k)) * q pow k * (&1 - q) pow (n - k)`
    SUBST1_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
   REAL_ARITH_TAC]);;

let BINOMIAL_CHAR_FN_IM = prove
 (`!p:A prob_space X n q t. binomial_rv p X n q ==>
     simple_char_fn_im p X t =
     sum (0..n) (\k. &(binom(n,k)) * q pow k * (&1 - q) pow (n - k) *
                     sin(t * &k))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[binomial_rv] THEN STRIP_TAC THEN
  REWRITE_TAC[simple_char_fn_im] THEN
  FIRST_ASSUM(fun th ->
    MP_TAC(MATCH_MP SIMPLE_EXPECTATION_COMPOSE_SUM th)) THEN
  DISCH_THEN(MP_TAC o SPEC `\u:real. sin(t * u)`) THEN
  BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `IMAGE (X:A->real) (prob_carrier p) SUBSET {&k | k <= n}`
    ASSUME_TAC THENL
  [REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `sum (IMAGE (X:A->real) (prob_carrier p))
       (\u. sin(t * u) * prob p {x | x IN prob_carrier p /\ X x = u}) =
     sum (IMAGE (\k:num. &k) (0..n))
       (\u. sin(t * u) * prob (p:A prob_space)
              {x:A | x IN prob_carrier p /\ (X:A->real) x = u})`
    SUBST1_TAC THENL
  [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
      (REWRITE_RULE[IMP_CONJ] SUBSET_TRANS)) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE; IN_NUMSEG; LE_0] THEN
    MESON_TAC[];
    X_GEN_TAC `v:real` THEN REWRITE_TAC[IN_IMAGE; IN_NUMSEG; LE_0] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ (X:A->real) x = v} = {}`
      (fun th -> REWRITE_TAC[th; PROB_EMPTY; REAL_MUL_RZERO]) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[]];
   ALL_TAC] THEN
  SIMP_TAC[FINITE_NUMSEG; SUM_IMAGE; IN_NUMSEG; LE_0; REAL_OF_NUM_EQ] THEN
  REWRITE_TAC[o_DEF] THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:num` THEN
  REWRITE_TAC[IN_NUMSEG; LE_0] THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `prob (p:A prob_space) {x:A | x IN prob_carrier p /\ (X:A->real) x = &k} =
     &(binom(n,k)) * q pow k * (&1 - q) pow (n - k)`
    SUBST1_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
   REAL_ARITH_TAC]);;

(* --------------------------------------------------------------------- *)
(* Poisson characteristic function (infinite series via complex exp)      *)
(* --------------------------------------------------------------------- *)

let POISSON_CHAR_FN_RE = prove
 (`!lam t. &0 <= lam ==>
    ((\k. cos(t * &k) * poisson_pmf lam k) real_sums
     exp(lam * (cos t - &1)) * cos(lam * sin t)) (from 0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `Cx(lam) * cexp(ii * Cx(t))` CEXP_CONVERGES) THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_SUMS_RE) THEN
  DISCH_THEN(MP_TAC o SPEC `exp(--lam)` o MATCH_MP REAL_SERIES_LMUL) THEN
  SUBGOAL_THEN
    `exp(--lam) * Re(cexp(Cx(lam) * cexp(ii * Cx(t)))) =
     exp(lam * (cos t - &1)) * cos(lam * sin t)`
    ASSUME_TAC THENL
  [REWRITE_TAC[RE_CEXP; RE_MUL_CX; IM_MUL_CX; RE_CEXP; IM_CEXP;
               RE_MUL_II; IM_MUL_II; RE_CX; IM_CX;
               REAL_NEG_0; REAL_MUL_RZERO; REAL_EXP_0; REAL_MUL_RID;
               REAL_MUL_LID] THEN
   ONCE_REWRITE_TAC[REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM REAL_EXP_ADD] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_SUMS_EQ THEN
  EXISTS_TAC `\n:num. exp(--lam) *
    (Re o (\n. (Cx lam * cexp (ii * Cx t)) pow n /
               Cx (&(FACT n)))) n` THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_FROM] THEN DISCH_TAC THEN
  REWRITE_TAC[o_THM] THEN BETA_TAC THEN
  REWRITE_TAC[COMPLEX_POW_MUL; GSYM CX_POW; GSYM CEXP_N;
              complex_div; GSYM CX_INV; RE_MUL_CX] THEN
  REWRITE_TAC[RE_CEXP; IM_MUL_CX; RE_MUL_CX; RE_MUL_II; IM_MUL_II;
              RE_CX; IM_CX; REAL_NEG_0; REAL_MUL_RZERO; REAL_EXP_0;
              REAL_MUL_RID; REAL_MUL_LID] THEN
  REWRITE_TAC[poisson_pmf; real_div; REAL_MUL_AC]);;

let POISSON_CHAR_FN_IM = prove
 (`!lam t. &0 <= lam ==>
    ((\k. sin(t * &k) * poisson_pmf lam k) real_sums
     exp(lam * (cos t - &1)) * sin(lam * sin t)) (from 0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `Cx(lam) * cexp(ii * Cx(t))` CEXP_CONVERGES) THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_SUMS_IM) THEN
  DISCH_THEN(MP_TAC o SPEC `exp(--lam)` o MATCH_MP REAL_SERIES_LMUL) THEN
  SUBGOAL_THEN
    `exp(--lam) * Im(cexp(Cx(lam) * cexp(ii * Cx(t)))) =
     exp(lam * (cos t - &1)) * sin(lam * sin t)`
    ASSUME_TAC THENL
  [REWRITE_TAC[IM_CEXP; RE_MUL_CX; IM_MUL_CX; RE_CEXP; IM_CEXP;
               RE_MUL_II; IM_MUL_II; RE_CX; IM_CX;
               REAL_NEG_0; REAL_MUL_RZERO; REAL_EXP_0; REAL_MUL_RID;
               REAL_MUL_LID] THEN
   ONCE_REWRITE_TAC[REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM REAL_EXP_ADD] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_SUMS_EQ THEN
  EXISTS_TAC `\n:num. exp(--lam) *
    (Im o (\n. (Cx lam * cexp (ii * Cx t)) pow n /
               Cx (&(FACT n)))) n` THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_FROM] THEN DISCH_TAC THEN
  REWRITE_TAC[o_THM] THEN BETA_TAC THEN
  REWRITE_TAC[COMPLEX_POW_MUL; GSYM CX_POW; GSYM CEXP_N;
              complex_div; GSYM CX_INV; IM_MUL_CX] THEN
  REWRITE_TAC[IM_CEXP; RE_MUL_CX; IM_MUL_CX; RE_MUL_II; IM_MUL_II;
              RE_CX; IM_CX; REAL_NEG_0; REAL_MUL_RZERO; REAL_EXP_0;
              REAL_MUL_RID; REAL_MUL_LID] THEN
  REWRITE_TAC[poisson_pmf; real_div; REAL_MUL_AC]);;

(* --------------------------------------------------------------------- *)
(* Geometric characteristic function (infinite series via complex GP)     *)
(* --------------------------------------------------------------------- *)

let GEOMETRIC_CHAR_FN_RE = prove
 (`!p t. &0 < p /\ p <= &1 ==>
    ((\k. cos(t * &k) * geometric_pmf p k) real_sums
     p * (&1 - (&1 - p) * cos t) /
     (&1 - &2 * (&1 - p) * cos t + (&1 - p) pow 2)) (from 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(Cx(&1 - p) * cexp(ii * Cx t)) < &1` ASSUME_TAC THENL
  [REWRITE_TAC[COMPLEX_NORM_MUL; NORM_CEXP_II; REAL_MUL_RID;
               COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `0` o MATCH_MP SUMS_GP) THEN
  REWRITE_TAC[complex_pow; COMPLEX_DIV_1] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_SUMS_RE) THEN
  DISCH_THEN(MP_TAC o SPEC `p:real` o MATCH_MP REAL_SERIES_LMUL) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
    `p * Re(Cx(&1) / (Cx(&1) - Cx(&1 - p) * cexp(ii * Cx t))) =
     p * (&1 - (&1 - p) * cos t) /
     (&1 - &2 * (&1 - p) * cos t + (&1 - p) pow 2)`
    ASSUME_TAC THENL
  [ONCE_REWRITE_TAC[complex_div] THEN REWRITE_TAC[COMPLEX_MUL_LID] THEN
   ONCE_REWRITE_TAC[COMPLEX_INV_CNJ] THEN
   ONCE_REWRITE_TAC[complex_div] THEN
   REWRITE_TAC[GSYM CX_POW; GSYM CX_INV; RE_MUL_CX; RE_CNJ] THEN
   REWRITE_TAC[RE_SUB; RE_CX; RE_MUL_CX; RE_CEXP;
               IM_MUL_II; RE_MUL_II; IM_CX; RE_CX;
               REAL_NEG_0; REAL_EXP_0; REAL_MUL_LID] THEN
   REWRITE_TAC[COMPLEX_SQNORM; RE_SUB; IM_SUB; RE_CX; IM_CX;
               RE_MUL_CX; IM_MUL_CX; RE_CEXP; IM_CEXP;
               RE_MUL_II; IM_MUL_II; RE_CX; IM_CX;
               REAL_NEG_0; REAL_EXP_0; REAL_MUL_LID] THEN
   SUBGOAL_THEN
     `(&1 - (&1 - p) * cos t) pow 2 + (&0 - (&1 - p) * sin t) pow 2 =
      &1 - &2 * (&1 - p) * cos t + (&1 - p) pow 2`
     SUBST1_TAC THENL
   [MP_TAC(SPEC `t:real` SIN_CIRCLE) THEN CONV_TAC REAL_RING;
    REWRITE_TAC[real_div; REAL_MUL_AC]]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_SUMS_EQ THEN
  EXISTS_TAC `\n:num. p *
    (Re o (\k. (Cx(&1 - p) * cexp(ii * Cx t)) pow k)) n` THEN
  CONJ_TAC THENL
  [X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_FROM] THEN DISCH_TAC THEN
   REWRITE_TAC[o_THM] THEN BETA_TAC THEN
   REWRITE_TAC[COMPLEX_POW_MUL; GSYM CX_POW; GSYM CEXP_N;
               RE_MUL_CX; RE_CEXP; IM_MUL_CX; RE_MUL_II; IM_MUL_II;
               RE_CX; IM_CX; REAL_NEG_0; REAL_MUL_RZERO; REAL_EXP_0;
               REAL_MUL_RID; REAL_MUL_LID] THEN
   REWRITE_TAC[geometric_pmf; REAL_MUL_AC];
   ASM_MESON_TAC[]]);;

let GEOMETRIC_CHAR_FN_IM = prove
 (`!p t. &0 < p /\ p <= &1 ==>
    ((\k. sin(t * &k) * geometric_pmf p k) real_sums
     p * (&1 - p) * sin t /
     (&1 - &2 * (&1 - p) * cos t + (&1 - p) pow 2)) (from 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(Cx(&1 - p) * cexp(ii * Cx t)) < &1` ASSUME_TAC THENL
  [REWRITE_TAC[COMPLEX_NORM_MUL; NORM_CEXP_II; REAL_MUL_RID;
               COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `0` o MATCH_MP SUMS_GP) THEN
  REWRITE_TAC[complex_pow; COMPLEX_DIV_1] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_SUMS_IM) THEN
  DISCH_THEN(MP_TAC o SPEC `p:real` o MATCH_MP REAL_SERIES_LMUL) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
    `p * Im(Cx(&1) / (Cx(&1) - Cx(&1 - p) * cexp(ii * Cx t))) =
     p * (&1 - p) * sin t /
     (&1 - &2 * (&1 - p) * cos t + (&1 - p) pow 2)`
    ASSUME_TAC THENL
  [ONCE_REWRITE_TAC[complex_div] THEN REWRITE_TAC[COMPLEX_MUL_LID] THEN
   ONCE_REWRITE_TAC[COMPLEX_INV_CNJ] THEN
   ONCE_REWRITE_TAC[complex_div] THEN
   REWRITE_TAC[GSYM CX_POW; GSYM CX_INV; IM_MUL_CX; IM_CNJ] THEN
   REWRITE_TAC[IM_SUB; IM_CX; IM_MUL_CX; IM_CEXP;
               RE_MUL_II; IM_MUL_II; RE_CX; IM_CX;
               REAL_NEG_0; REAL_EXP_0; REAL_MUL_LID] THEN
   REWRITE_TAC[COMPLEX_SQNORM; RE_SUB; IM_SUB; RE_CX; IM_CX;
               RE_MUL_CX; IM_MUL_CX; RE_CEXP; IM_CEXP;
               RE_MUL_II; IM_MUL_II; RE_CX; IM_CX;
               REAL_NEG_0; REAL_EXP_0; REAL_MUL_LID] THEN
   SUBGOAL_THEN
     `(&1 - (&1 - p) * cos t) pow 2 + (&0 - (&1 - p) * sin t) pow 2 =
      &1 - &2 * (&1 - p) * cos t + (&1 - p) pow 2`
     SUBST1_TAC THENL
   [MP_TAC(SPEC `t:real` SIN_CIRCLE) THEN CONV_TAC REAL_RING;
    REWRITE_TAC[real_div; REAL_MUL_AC] THEN REAL_ARITH_TAC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_SUMS_EQ THEN
  EXISTS_TAC `\n:num. p *
    (Im o (\k. (Cx(&1 - p) * cexp(ii * Cx t)) pow k)) n` THEN
  CONJ_TAC THENL
  [X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_FROM] THEN DISCH_TAC THEN
   REWRITE_TAC[o_THM] THEN BETA_TAC THEN
   REWRITE_TAC[COMPLEX_POW_MUL; GSYM CX_POW; GSYM CEXP_N;
               IM_MUL_CX; IM_CEXP;
               RE_MUL_CX; IM_MUL_CX; RE_MUL_II; IM_MUL_II;
               RE_CX; IM_CX; REAL_NEG_0; REAL_MUL_RZERO; REAL_EXP_0;
               REAL_MUL_RID; REAL_MUL_LID] THEN
   REWRITE_TAC[geometric_pmf; REAL_MUL_AC];
   ASM_MESON_TAC[]]);;

(* ========================================================================= *)
(* LOTUS and Distribution Characteristic Function Bridge                     *)
(*                                                                           *)
(* Connects the probability-space char fn (expectation) to the analytical    *)
(* integral formulas for specific distributions.                             *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Definition: X has absolutely continuous distribution with density f.       *)
(*                                                                           *)
(* The 5th condition (LOTUS for bounded continuous functions) follows from    *)
(* conditions 1-4 by standard step-function approximation + BCT + DCT.       *)
(* Including it directly makes the bridge theorems efficient.                *)
(* ------------------------------------------------------------------------- *)

let has_density = new_definition
  `has_density (p:A prob_space) (X:A->real) (f:real->real) <=>
   random_variable p X /\
   (!u. &0 <= f u) /\
   (f has_real_integral &1) (:real) /\
   (!a b. a <= b ==>
     prob p {x | x IN prob_carrier p /\ a < X x /\ X x <= b} =
     real_integral (real_interval[a,b]) f) /\
   (!g M. (!u. abs(g u) <= M) /\ g real_continuous_on (:real) /\
          random_variable p (\x. g(X x))
     ==> integrable p (\x. g(X x)) /\
         expectation p (\x. g(X x)) =
         real_integral (:real) (\u. g u * f u))`;;

(* Basic consequences *)

let HAS_DENSITY_RV = prove
 (`!p:A prob_space X f. has_density p X f ==> random_variable p X`,
  REWRITE_TAC[has_density] THEN MESON_TAC[]);;

let HAS_DENSITY_NONNEG = prove
 (`!p:A prob_space X f. has_density p X f ==> !u. &0 <= f u`,
  REWRITE_TAC[has_density] THEN MESON_TAC[]);;

let HAS_DENSITY_INTEGRAL_ONE = prove
 (`!p:A prob_space X f. has_density p X f
   ==> (f has_real_integral &1) (:real)`,
  REWRITE_TAC[has_density] THEN MESON_TAC[]);;

let HAS_DENSITY_INTERVAL_PROB = prove
 (`!p:A prob_space X f a b.
   has_density p X f /\ a <= b
   ==> prob p {x | x IN prob_carrier p /\ a < X x /\ X x <= b} =
       real_integral (real_interval[a,b]) f`,
  REWRITE_TAC[has_density] THEN MESON_TAC[]);;

let HAS_DENSITY_INTEGRABLE = prove
 (`!p:A prob_space X f. has_density p X f
   ==> f real_integrable_on (:real)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_integrable_on] THEN
  EXISTS_TAC `&1` THEN ASM_MESON_TAC[HAS_DENSITY_INTEGRAL_ONE]);;

(* LOTUS: Law of the Unconscious Statistician for bounded continuous g *)

let LOTUS_BOUNDED_CONTINUOUS = prove
 (`!p:A prob_space X f g M.
   has_density p X f /\
   (!u. abs(g u) <= M) /\
   g real_continuous_on (:real) /\
   random_variable p (\x. g(X x))
   ==> integrable p (\x. g(X x)) /\
       expectation p (\x. g(X x)) =
       real_integral (:real) (\u. g u * f u)`,
  REWRITE_TAC[has_density] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`g:real->real`; `M:real`]) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* LOTUS for nonneg continuous g (not necessarily bounded) *)

let LOTUS_NONNEG_CONTINUOUS = prove
 (`!p:A prob_space X f g.
   has_density p X f /\
   g real_continuous_on (:real) /\
   (!u. &0 <= g u) /\
   integrable p (\x. g(X x))
   ==> (\u. g u * f u) real_integrable_on (:real) /\
       expectation p (\x. g(X x)) =
       real_integral (:real) (\u. g u * f u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `random_variable p (X:A->real)` ASSUME_TAC THENL
  [ASM_MESON_TAC[HAS_DENSITY_RV]; ALL_TAC] THEN
  SUBGOAL_THEN `!u. &0 <= (f:real->real) u` ASSUME_TAC THENL
  [ASM_MESON_TAC[HAS_DENSITY_NONNEG]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real->real) real_integrable_on (:real)` ASSUME_TAC THENL
  [ASM_MESON_TAC[HAS_DENSITY_INTEGRABLE]; ALL_TAC] THEN
  (* Establish LOTUS for bounded truncations *)
  SUBGOAL_THEN
    `!n. expectation p (\x:A. min ((g:real->real)((X:A->real) x)) (&n)) =
         real_integral (:real) (\u. min (g u) (&n) * f u)` ASSUME_TAC THENL
  [GEN_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `f:real->real`;
                   `\u:real. min ((g:real->real) u) (&n)`; `&n`]
     LOTUS_BOUNDED_CONTINUOUS) THEN
   BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= n ==> abs x <= n`) THEN
     CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_MIN] THEN ASM_REWRITE_TAC[REAL_POS];
      REWRITE_TAC[REAL_MIN_LE] THEN DISJ2_TAC THEN REAL_ARITH_TAC];
     MATCH_MP_TAC REAL_CONTINUOUS_ON_MIN THEN
     ASM_REWRITE_TAC[REAL_CONTINUOUS_ON_CONST];
     MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
     ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN
     MATCH_MP_TAC RANDOM_VARIABLE_COMP_CONTINUOUS THEN ASM_REWRITE_TAC[]];
    STRIP_TAC THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* Apply REAL_MONOTONE_CONVERGENCE_INCREASING to get integrability + convergence *)
  MP_TAC(ISPECL
    [`\n:num. (\u:real. min ((g:real->real) u) (&n) * (f:real->real) u)`;
     `\u:real. (g:real->real) u * (f:real->real) u`;
     `(:real)`] REAL_MONOTONE_CONVERGENCE_INCREASING) THEN
  BETA_TAC THEN ANTS_TAC THENL
  [REPEAT CONJ_TAC THENL
   [(* Each min(g, &n) * f is real_integrable_on (:real) *)
    GEN_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
    REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET THEN
     REWRITE_TAC[REAL_CLOSED_UNIV] THEN
     MATCH_MP_TAC REAL_CONTINUOUS_ON_MIN THEN
     ASM_REWRITE_TAC[REAL_CONTINUOUS_ON_CONST];
     REWRITE_TAC[real_bounded; IN_IMAGE; IN_UNIV] THEN
     EXISTS_TAC `&k` THEN GEN_TAC THEN
     DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
     MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= n ==> abs x <= n`) THEN
     CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_MIN] THEN ASM_REWRITE_TAC[REAL_POS];
      REWRITE_TAC[REAL_MIN_LE] THEN DISJ2_TAC THEN REAL_ARITH_TAC];
     MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_REAL_INTEGRABLE THEN
     ASM_SIMP_TAC[IN_UNIV; REAL_LE_MUL; REAL_POS]];
    (* Monotonicity: min(g u, &k) * f u <= min(g u, &(SUC k)) * f u *)
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[IN_UNIV] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> min x a <= min x b`) THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
    (* Pointwise convergence: min(g u, &k) * f u -> g u * f u *)
    X_GEN_TAC `u:real` THEN REWRITE_TAC[IN_UNIV] THEN
    MATCH_MP_TAC REALLIM_EVENTUALLY THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    MP_TAC(SPEC `(g:real->real) u` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[real_min] THEN COND_CASES_TAC THENL
    [REFL_TAC;
     ASM_MESON_TAC[REAL_LE_ANTISYM; REAL_NOT_LT; REAL_LE_TRANS;
                    REAL_OF_NUM_LE]];
    (* Bounded: integrals are bounded *)
    REWRITE_TAC[real_bounded; FORALL_IN_GSPEC; IN_UNIV] THEN
    EXISTS_TAC `expectation p (\x:A. (g:real->real)((X:A->real) x))` THEN
    GEN_TAC THEN
    ONCE_REWRITE_TAC[GSYM(ASSUME
      `!n. expectation p (\x:A. min ((g:real->real)((X:A->real) x)) (&n)) =
           real_integral (:real) (\u. min (g u) (&n) * f u)`)] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC EXPECTATION_POS THEN BETA_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `&k` THEN
      BETA_TAC THEN CONJ_TAC THENL
      [MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
       ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN
       MATCH_MP_TAC RANDOM_VARIABLE_COMP_CONTINUOUS THEN ASM_REWRITE_TAC[];
       GEN_TAC THEN DISCH_TAC THEN
       MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= n ==> abs x <= n`) THEN
       CONJ_TAC THENL
       [REWRITE_TAC[REAL_LE_MIN] THEN ASM_REWRITE_TAC[REAL_POS];
        REWRITE_TAC[REAL_MIN_LE] THEN DISJ2_TAC THEN REAL_ARITH_TAC]];
      GEN_TAC THEN DISCH_TAC THEN
      REWRITE_TAC[REAL_LE_MIN] THEN ASM_REWRITE_TAC[REAL_POS]];
     MATCH_MP_TAC EXPECTATION_MONO THEN BETA_TAC THEN
     ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `&k` THEN
      BETA_TAC THEN CONJ_TAC THENL
      [MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
       ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN
       MATCH_MP_TAC RANDOM_VARIABLE_COMP_CONTINUOUS THEN ASM_REWRITE_TAC[];
       GEN_TAC THEN DISCH_TAC THEN
       MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= n ==> abs x <= n`) THEN
       CONJ_TAC THENL
       [REWRITE_TAC[REAL_LE_MIN] THEN ASM_REWRITE_TAC[REAL_POS];
        REWRITE_TAC[REAL_MIN_LE] THEN DISJ2_TAC THEN REAL_ARITH_TAC]];
      GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_MIN_LE] THEN
      DISJ1_TAC THEN REAL_ARITH_TAC]]];
   ALL_TAC] THEN
  (* Rewrite integral sequence to expectation sequence *)
  ONCE_REWRITE_TAC[GSYM(ASSUME
    `!n. expectation p (\x:A. min ((g:real->real)((X:A->real) x)) (&n)) =
         real_integral (:real) (\u. min (g u) (&n) * f u)`)] THEN
  STRIP_TAC THEN
  (* Now have: g*f integrable + convergence of E[min(g(X),&n)] -> integral(g*f) *)
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Prove E[g(X)] = integral(g*f) via limit uniqueness *)
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC `\n. expectation p (\x:A. min ((g:real->real)((X:A->real) x)) (&n))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
  [(* E[min(g(X), &n)] -> E[g(X)] by dominated convergence *)
   MP_TAC(ISPECL [`p:A prob_space`;
                   `\n:num. (\x:A. min ((g:real->real)((X:A->real) x)) (&n))`;
                   `\x:A. (g:real->real)((X:A->real) x)`;
                   `\x:A. (g:real->real)((X:A->real) x)`]
     DOMINATED_CONVERGENCE) THEN
   BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
    [(* Each min(g(X), &n) is integrable *)
     GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
     EXISTS_TAC `&n` THEN BETA_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN
      ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN
      MATCH_MP_TAC RANDOM_VARIABLE_COMP_CONTINUOUS THEN
      ASM_REWRITE_TAC[];
      GEN_TAC THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= n ==> abs x <= n`) THEN
      CONJ_TAC THENL
      [REWRITE_TAC[REAL_LE_MIN] THEN ASM_REWRITE_TAC[REAL_POS];
       REWRITE_TAC[REAL_MIN_LE] THEN DISJ2_TAC THEN REAL_ARITH_TAC]];
     (* g(X) is integrable (dominator) *)
     ASM_REWRITE_TAC[];
     (* |min(g(X x), &n)| <= g(X x) *)
     REPEAT STRIP_TAC THEN
     MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN
     CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_MIN] THEN ASM_REWRITE_TAC[REAL_POS];
      REWRITE_TAC[REAL_MIN_LE] THEN DISJ1_TAC THEN REAL_ARITH_TAC];
     (* min(g(X x), &n) -> g(X x) pointwise *)
     GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
     X_GEN_TAC `e:real` THEN DISCH_TAC THEN
     MP_TAC(SPEC `(g:real->real)((X:A->real) x)` REAL_ARCH_SIMPLE) THEN
     DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
     X_GEN_TAC `m:num` THEN DISCH_TAC THEN
     SUBGOAL_THEN `(g:real->real)((X:A->real) x) <= &m` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N` THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      SUBGOAL_THEN `min ((g:real->real)((X:A->real) x)) (&m) = g(X x)`
        SUBST1_TAC THENL
      [REWRITE_TAC[real_min] THEN ASM_REWRITE_TAC[GSYM REAL_NOT_LT] THEN
       ASM_REAL_ARITH_TAC;
       ASM_REAL_ARITH_TAC]]];
    STRIP_TAC THEN ASM_REWRITE_TAC[]];
   (* E[min(g(X), &n)] -> integral(g*f) from RMCI *)
   ASM_REWRITE_TAC[]]);;

(* General LOTUS for continuous g (not necessarily nonneg) *)

let LOTUS_CONTINUOUS = prove
 (`!p:A prob_space X f g.
   has_density p X f /\
   g real_continuous_on (:real) /\
   integrable p (\x. g(X x))
   ==> (\u. g u * f u) real_integrable_on (:real) /\
       expectation p (\x. g(X x)) =
       real_integral (:real) (\u. g u * f u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `integrable p (\x:A. max ((g:real->real)((X:A->real) x)) (&0))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_MAX THEN ASM_REWRITE_TAC[INTEGRABLE_CONST];
   ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (\x:A. max (--((g:real->real)((X:A->real) x))) (&0))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_MAX THEN ASM_REWRITE_TAC[INTEGRABLE_CONST] THEN
   MATCH_MP_TAC INTEGRABLE_NEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `f:real->real`;
                  `\u:real. max ((g:real->real) u) (&0)`]
   LOTUS_NONNEG_CONTINUOUS) THEN
  BETA_TAC THEN ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_MAX THEN
    ASM_REWRITE_TAC[REAL_CONTINUOUS_ON_CONST];
    GEN_TAC THEN REWRITE_TAC[REAL_LE_MAX] THEN DISJ2_TAC THEN
    REAL_ARITH_TAC];
   ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `f:real->real`;
                  `\u:real. max (--((g:real->real) u)) (&0)`]
   LOTUS_NONNEG_CONTINUOUS) THEN
  BETA_TAC THEN ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_MAX THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_NEG THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN REWRITE_TAC[REAL_LE_MAX] THEN DISJ2_TAC THEN
    REAL_ARITH_TAC];
   ALL_TAC] THEN
  STRIP_TAC THEN
  CONJ_TAC THENL
  [SUBGOAL_THEN `(\u:real. (g:real->real) u * (f:real->real) u) =
     (\u. max (g u) (&0) * f u - max (--(g u)) (&0) * f u)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    REWRITE_TAC[GSYM REAL_SUB_RDISTRIB] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN ASM_REWRITE_TAC[]];
   SUBGOAL_THEN
     `expectation p (\x:A. (g:real->real)((X:A->real) x)) =
      expectation p (\x. max (g(X x)) (&0)) -
      expectation p (\x. max (--(g(X x))) (&0))` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`;
                    `\x:A. max ((g:real->real)((X:A->real) x)) (&0)`;
                    `\x:A. max (--((g:real->real)((X:A->real) x))) (&0)`]
     EXPECTATION_SUB) THEN
    BETA_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o GSYM) THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
      `real_integral (:real) (\u:real. max ((g:real->real) u) (&0) * (f:real->real) u) -
       real_integral (:real) (\u. max (--g u) (&0) * f u) =
       real_integral (:real) (\u. max (g u) (&0) * f u - max (--g u) (&0) * f u)`
      SUBST1_TAC THENL
    [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INTEGRAL_SUB THEN
     ASM_REWRITE_TAC[];
     AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
     REWRITE_TAC[GSYM REAL_SUB_RDISTRIB] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     REAL_ARITH_TAC]]]);;

(* Specialized LOTUS for cos and sin (the cases needed for char fn) *)

let LOTUS_COS = prove
 (`!p:A prob_space X f t.
   has_density p X f
   ==> integrable p (\x. cos(t * X x)) /\
       expectation p (\x. cos(t * X x)) =
       real_integral (:real) (\u. cos(t * u) * f u)`,
  REPEAT STRIP_TAC THENL
  [FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[has_density]) THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`\u:real. cos(t * u)`; `&1`]) THEN
   REWRITE_TAC[COS_BOUND] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
    [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
     MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
      REWRITE_TAC[REAL_CONTINUOUS_ON_COS]];
     MATCH_MP_TAC RANDOM_VARIABLE_COS THEN
     MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[]];
    SIMP_TAC[]];
   FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[has_density]) THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`\u:real. cos(t * u)`; `&1`]) THEN
   REWRITE_TAC[COS_BOUND] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
    [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
     MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
      REWRITE_TAC[REAL_CONTINUOUS_ON_COS]];
     MATCH_MP_TAC RANDOM_VARIABLE_COS THEN
     MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[]];
    SIMP_TAC[]]]);;

let LOTUS_SIN = prove
 (`!p:A prob_space X f t.
   has_density p X f
   ==> integrable p (\x. sin(t * X x)) /\
       expectation p (\x. sin(t * X x)) =
       real_integral (:real) (\u. sin(t * u) * f u)`,
  REPEAT STRIP_TAC THENL
  [FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[has_density]) THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`\u:real. sin(t * u)`; `&1`]) THEN
   REWRITE_TAC[SIN_BOUND] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
    [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
     MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
      REWRITE_TAC[REAL_CONTINUOUS_ON_SIN]];
     MATCH_MP_TAC RANDOM_VARIABLE_SIN THEN
     MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[]];
    SIMP_TAC[]];
   FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[has_density]) THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`\u:real. sin(t * u)`; `&1`]) THEN
   REWRITE_TAC[SIN_BOUND] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
    [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
     MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
      REWRITE_TAC[REAL_CONTINUOUS_ON_SIN]];
     MATCH_MP_TAC RANDOM_VARIABLE_SIN THEN
     MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[]];
    SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Distribution predicates                                                   *)
(* ------------------------------------------------------------------------- *)

let normal_distributed = new_definition
  `normal_distributed (p:A prob_space) (X:A->real) mu sigma <=>
   has_density p X (normal_density mu sigma) /\ &0 < sigma`;;

let uniform_distributed = new_definition
  `uniform_distributed (p:A prob_space) (X:A->real) a b <=>
   has_density p X (uniform_density a b) /\ a < b`;;

let exponential_distributed = new_definition
  `exponential_distributed (p:A prob_space) (X:A->real) l <=>
   has_density p X (exponential_density l) /\ &0 < l`;;

(* ------------------------------------------------------------------------- *)
(* Bridge theorems: char fn of normally distributed RV                       *)
(* ------------------------------------------------------------------------- *)

let CHAR_FN_RE_NORMAL_DIST = prove
 (`!p:A prob_space X mu sigma t.
   normal_distributed p X mu sigma
   ==> char_fn_re p X t =
       exp(--(sigma pow 2 * t pow 2 / &2)) * cos(mu * t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[normal_distributed] THEN STRIP_TAC THEN
  REWRITE_TAC[char_fn_re] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LOTUS_COS th]) THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  SUBGOAL_THEN `(\u:real. cos(t * u) * normal_density mu sigma u) =
                (\u. normal_density mu sigma u * cos(t * u))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
   ASM_SIMP_TAC[NORMAL_CHAR_FN_RE]]);;

let CHAR_FN_IM_NORMAL_DIST = prove
 (`!p:A prob_space X mu sigma t.
   normal_distributed p X mu sigma
   ==> char_fn_im p X t =
       exp(--(sigma pow 2 * t pow 2 / &2)) * sin(mu * t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[normal_distributed] THEN STRIP_TAC THEN
  REWRITE_TAC[char_fn_im] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LOTUS_SIN th]) THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  SUBGOAL_THEN `(\u:real. sin(t * u) * normal_density mu sigma u) =
                (\u. normal_density mu sigma u * sin(t * u))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
   ASM_SIMP_TAC[NORMAL_CHAR_FN_IM]]);;

(* ------------------------------------------------------------------------- *)
(* Bridge theorems: char fn of uniformly distributed RV                      *)
(* ------------------------------------------------------------------------- *)

let CHAR_FN_RE_UNIFORM_DIST = prove
 (`!p:A prob_space X a b t.
   uniform_distributed p X a b /\ ~(t = &0)
   ==> char_fn_re p X t = (sin(t * b) - sin(t * a)) / (t * (b - a))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[uniform_distributed] THEN STRIP_TAC THEN
  REWRITE_TAC[char_fn_re] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LOTUS_COS th]) THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  SUBGOAL_THEN `(\u:real. cos(t * u) * uniform_density a b u) =
                (\u. uniform_density a b u * cos(t * u))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
   ASM_SIMP_TAC[UNIFORM_CHAR_FN_RE]]);;

let CHAR_FN_IM_UNIFORM_DIST = prove
 (`!p:A prob_space X a b t.
   uniform_distributed p X a b /\ ~(t = &0)
   ==> char_fn_im p X t = (cos(t * a) - cos(t * b)) / (t * (b - a))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[uniform_distributed] THEN STRIP_TAC THEN
  REWRITE_TAC[char_fn_im] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LOTUS_SIN th]) THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  SUBGOAL_THEN `(\u:real. sin(t * u) * uniform_density a b u) =
                (\u. uniform_density a b u * sin(t * u))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
   ASM_SIMP_TAC[UNIFORM_CHAR_FN_IM]]);;

(* ------------------------------------------------------------------------- *)
(* Bridge theorems: char fn of exponentially distributed RV                  *)
(* ------------------------------------------------------------------------- *)

let CHAR_FN_RE_EXPONENTIAL_DIST = prove
 (`!p:A prob_space X l t.
   exponential_distributed p X l
   ==> char_fn_re p X t = l pow 2 / (l pow 2 + t pow 2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[exponential_distributed] THEN STRIP_TAC THEN
  REWRITE_TAC[char_fn_re] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LOTUS_COS th]) THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  SUBGOAL_THEN `(\u:real. cos(t * u) * exponential_density l u) =
    (\x. if x IN {x | &0 <= x}
         then exponential_density l x * cos(t * x) else &0)`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; IN_ELIM_THM] THEN GEN_TAC THEN
   COND_CASES_TAC THENL [REAL_ARITH_TAC;
   REWRITE_TAC[exponential_density] THEN ASM_REWRITE_TAC[] THEN
   REAL_ARITH_TAC];
   REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
   ASM_SIMP_TAC[EXPONENTIAL_CHAR_FN_RE]]);;

let CHAR_FN_IM_EXPONENTIAL_DIST = prove
 (`!p:A prob_space X l t.
   exponential_distributed p X l
   ==> char_fn_im p X t = l * t / (l pow 2 + t pow 2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[exponential_distributed] THEN STRIP_TAC THEN
  REWRITE_TAC[char_fn_im] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LOTUS_SIN th]) THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  SUBGOAL_THEN `(\u:real. sin(t * u) * exponential_density l u) =
    (\x. if x IN {x | &0 <= x}
         then exponential_density l x * sin(t * x) else &0)`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; IN_ELIM_THM] THEN GEN_TAC THEN
   COND_CASES_TAC THENL [REAL_ARITH_TAC;
   REWRITE_TAC[exponential_density] THEN ASM_REWRITE_TAC[] THEN
   REAL_ARITH_TAC];
   REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
   ASM_SIMP_TAC[EXPONENTIAL_CHAR_FN_IM]]);;

(* ========================================================================= *)
(* Expectation and Variance bridge theorems for continuous distributions    *)
(* ========================================================================= *)

let EXPECTATION_NORMAL_DIST = prove
 (`!p:A prob_space X mu sigma.
   normal_distributed p X mu sigma /\ integrable p X
   ==> expectation p X = mu`,
  REPEAT GEN_TAC THEN REWRITE_TAC[normal_distributed] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`;
                  `normal_density mu sigma`; `\u:real. u`]
   LOTUS_CONTINUOUS) THEN
  BETA_TAC THEN ANTS_TAC THENL
  [ASM_REWRITE_TAC[REAL_CONTINUOUS_ON_ID; ETA_AX];
   REWRITE_TAC[ETA_AX] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   MP_TAC(ISPECL [`mu:real`; `sigma:real`] NORMAL_MEAN_INTEGRAL) THEN
   ASM_REWRITE_TAC[]]);;

let VARIANCE_NORMAL_DIST = prove
 (`!p:A prob_space X mu sigma.
   normal_distributed p X mu sigma /\
   integrable p X /\ integrable p (\x. (X x - mu) pow 2)
   ==> variance p X = sigma pow 2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[normal_distributed] THEN STRIP_TAC THEN
  REWRITE_TAC[variance] THEN
  SUBGOAL_THEN `expectation p (X:A->real) = mu` SUBST1_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `mu:real`; `sigma:real`]
    EXPECTATION_NORMAL_DIST) THEN
   ASM_REWRITE_TAC[normal_distributed];
   MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`;
                   `normal_density mu sigma`; `\u:real. (u - mu) pow 2`]
    LOTUS_CONTINUOUS) THEN
   BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_ID; REAL_CONTINUOUS_ON_CONST];
    REWRITE_TAC[ETA_AX] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`mu:real`; `sigma:real`] NORMAL_VARIANCE_INTEGRAL) THEN
    ASM_REWRITE_TAC[]]]);;

let EXPECTATION_UNIFORM_DIST = prove
 (`!p:A prob_space X a b.
   uniform_distributed p X a b /\ integrable p X
   ==> expectation p X = (a + b) / &2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[uniform_distributed] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`;
                  `uniform_density a b`; `\u:real. u`]
   LOTUS_CONTINUOUS) THEN
  BETA_TAC THEN ANTS_TAC THENL
  [ASM_REWRITE_TAC[REAL_CONTINUOUS_ON_ID; ETA_AX];
   REWRITE_TAC[ETA_AX] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   MP_TAC(ISPECL [`a:real`; `b:real`] UNIFORM_MEAN_INTEGRAL) THEN
   ASM_REWRITE_TAC[]]);;

let VARIANCE_UNIFORM_DIST = prove
 (`!p:A prob_space X a b.
   uniform_distributed p X a b /\
   integrable p X /\ integrable p (\x. (X x - (a + b) / &2) pow 2)
   ==> variance p X = (b - a) pow 2 / &12`,
  REPEAT GEN_TAC THEN REWRITE_TAC[uniform_distributed] THEN STRIP_TAC THEN
  REWRITE_TAC[variance] THEN
  SUBGOAL_THEN `expectation p (X:A->real) = (a + b) / &2` SUBST1_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `a:real`; `b:real`]
    EXPECTATION_UNIFORM_DIST) THEN
   ASM_REWRITE_TAC[uniform_distributed];
   MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`;
                   `uniform_density a b`; `\u:real. (u - (a + b) / &2) pow 2`]
    LOTUS_CONTINUOUS) THEN
   BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_ID; REAL_CONTINUOUS_ON_CONST];
    REWRITE_TAC[ETA_AX] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`a:real`; `b:real`] UNIFORM_VARIANCE_INTEGRAL) THEN
    ASM_REWRITE_TAC[]]]);;

let EXPECTATION_EXPONENTIAL_DIST = prove
 (`!p:A prob_space X l.
   exponential_distributed p X l /\ integrable p X
   ==> expectation p X = inv l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[exponential_distributed] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`;
                  `exponential_density l`; `\u:real. u`]
   LOTUS_CONTINUOUS) THEN
  BETA_TAC THEN ANTS_TAC THENL
  [ASM_REWRITE_TAC[REAL_CONTINUOUS_ON_ID; ETA_AX];
   REWRITE_TAC[ETA_AX] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN
     `(\u:real. u * exponential_density l u) =
      (\u. if u IN {x | &0 <= x} then u * exponential_density l u else &0)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; IN_ELIM_THM] THEN GEN_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[exponential_density] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_INTEGRAL_RESTRICT_UNIV] THEN
    MP_TAC(SPEC `l:real` EXPONENTIAL_MEAN_INTEGRAL) THEN
    ASM_REWRITE_TAC[]]]);;

let VARIANCE_EXPONENTIAL_DIST = prove
 (`!p:A prob_space X l.
   exponential_distributed p X l /\
   integrable p X /\ integrable p (\x. (X x - inv l) pow 2)
   ==> variance p X = inv l pow 2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[exponential_distributed] THEN STRIP_TAC THEN
  REWRITE_TAC[variance] THEN
  SUBGOAL_THEN `expectation p (X:A->real) = inv l` SUBST1_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `l:real`]
    EXPECTATION_EXPONENTIAL_DIST) THEN
   ASM_REWRITE_TAC[exponential_distributed];
   MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`;
                   `exponential_density l`; `\u:real. (u - inv l) pow 2`]
    LOTUS_CONTINUOUS) THEN
   BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_ID; REAL_CONTINUOUS_ON_CONST];
    REWRITE_TAC[ETA_AX] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
      `(\u:real. (u - inv l) pow 2 * exponential_density l u) =
       (\u. if u IN {x | &0 <= x} then (u - inv l) pow 2 * exponential_density l u else &0)`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM; IN_ELIM_THM] THEN GEN_TAC THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[exponential_density] THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
     ASM_REAL_ARITH_TAC;
     REWRITE_TAC[REAL_INTEGRAL_RESTRICT_UNIV] THEN
     MP_TAC(SPEC `l:real` EXPONENTIAL_VARIANCE_INTEGRAL) THEN
     ASM_REWRITE_TAC[]]]]);;

(* ========================================================================= *)
(* Poisson mean and variance analytical series                              *)
(* ========================================================================= *)

(* Key recursion: (k+1) * poisson_pmf lam (k+1) = lam * poisson_pmf lam k *)
let POISSON_PMF_RECURSION = prove
 (`!lam k. &(SUC k) * poisson_pmf lam (SUC k) = lam * poisson_pmf lam k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[poisson_pmf] THEN
  SUBGOAL_THEN `~(&(FACT k) = &0)` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_OF_NUM_EQ; FACT_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `~(&(SUC k) = &0)` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_OF_NUM_EQ; NOT_SUC]; ALL_TAC] THEN
  REWRITE_TAC[FACT; GSYM REAL_OF_NUM_MUL; real_pow] THEN
  ASM_SIMP_TAC[REAL_FIELD
    `~(fk = &0) /\ ~(sk = &0)
     ==> sk * (e * (l * lp) / (sk * fk)) = l * (e * lp / fk)`]);;


(* E[X] = lam for Poisson(lam) *)
let POISSON_MEAN_SERIES = prove
 (`!lam. &0 <= lam ==>
   ((\k. &k * poisson_pmf lam k) real_sums lam) (from 0)`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE
    [REAL_MUL_LZERO; REAL_ADD_RID; SUM_SING_NUMSEG;
     ARITH_RULE `1 - 1 = 0`]
    (SPECL [`\k:num. &k * poisson_pmf lam k`; `lam:real`; `1`; `0`]
           REAL_SUMS_OFFSET_REV)) THEN
  CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
  MATCH_MP_TAC REAL_SUMS_EQ THEN
  EXISTS_TAC `\k:num. lam * poisson_pmf lam (k - 1)` THEN CONJ_TAC THENL
  [X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_FROM] THEN DISCH_TAC THEN
   BETA_TAC THEN
   SUBGOAL_THEN `k = SUC(k - 1)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[ARITH_RULE `SUC k - 1 = k`; GSYM POISSON_PMF_RECURSION] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `((\k. poisson_pmf lam (k - 1)) real_sums &1) (from 1)`
    MP_TAC THENL
  [REWRITE_TAC[real_sums; FROM_INTER_NUMSEG; REALLIM_SEQUENTIALLY] THEN
   MP_TAC(SPEC `lam:real` POISSON_PMF_SUMS) THEN
   REWRITE_TAC[real_sums; FROM_INTER_NUMSEG; REALLIM_SEQUENTIALLY] THEN
   DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN EXISTS_TAC `M + 1` THEN
   X_GEN_TAC `n:num` THEN DISCH_TAC THEN
   SUBGOAL_THEN `1 <= n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `sum(1..n) (\k. poisson_pmf lam (k - 1)) =
                 sum(0..n-1) (poisson_pmf lam)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[SUM_OFFSET_0] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[IN_NUMSEG; LE_0] THEN DISCH_TAC THEN BETA_TAC THEN
    AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]]; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`\k:num. poisson_pmf lam (k - 1)`; `&1`;
                `lam:real`; `from 1`] REAL_SERIES_LMUL) THEN
  ASM_REWRITE_TAC[REAL_MUL_RID]);;

(* Second factorial moment: E[X(X-1)] = lam^2 *)
let POISSON_SECOND_FACTORIAL_MOMENT = prove
 (`!lam. &0 <= lam ==>
   ((\k. &k * (&k - &1) * poisson_pmf lam k) real_sums lam pow 2) (from 0)`,
  GEN_TAC THEN DISCH_TAC THEN
  (* Series from 0 = series from 2, since f(0) = f(1) = 0 *)
  SUBGOAL_THEN
    `!f:num->real l. (f real_sums l) (from 2) /\ f 0 = &0 /\ f 1 = &0
     ==> (f real_sums l) (from 0)` MATCH_MP_TAC THENL
  [REPEAT GEN_TAC THEN STRIP_TAC THEN
   MP_TAC(SPECL [`f:num->real`; `l:real`; `2:num`; `0:num`]
     REAL_SUMS_OFFSET_REV) THEN
   ASM_REWRITE_TAC[ARITH_RULE `0 < 2`; ARITH_RULE `2 - 1 = 1`] THEN
   REWRITE_TAC[num_CONV `1`; SUM_CLAUSES_NUMSEG; LE_0] THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `f (SUC 0) = &0` (fun th -> REWRITE_TAC[th]) THENL
   [SUBGOAL_THEN `SUC 0 = 1` (fun th -> ASM_REWRITE_TAC[th]) THEN
    ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_ADD_LID; REAL_ADD_RID]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
  [(* Series from 2: reindex to from 0 *)
   SUBGOAL_THEN `(from 2) = from (0 + 2)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[ADD]; ALL_TAC] THEN
   REWRITE_TAC[GSYM(SPEC `2` REAL_SUMS_REINDEX)] THEN
   MATCH_MP_TAC REAL_SUMS_EQ THEN
   EXISTS_TAC `\k:num. lam pow 2 * poisson_pmf lam k` THEN CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_FROM] THEN DISCH_TAC THEN
    BETA_TAC THEN
    SUBGOAL_THEN `k + 2 = SUC(SUC k)` (fun th -> REWRITE_TAC[th]) THENL
    [ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&(SUC(SUC k)) - &1 = &(SUC k)`
      (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN
    SUBGOAL_THEN `&(SUC(SUC k)) * &(SUC k) * poisson_pmf lam (SUC(SUC k)) =
      &(SUC k) * (&(SUC(SUC k)) * poisson_pmf lam (SUC(SUC k)))` SUBST1_TAC THENL
    [REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     MATCH_ACCEPT_TAC REAL_MUL_SYM; ALL_TAC] THEN
    REWRITE_TAC[POISSON_PMF_RECURSION] THEN
    SUBGOAL_THEN `&(SUC k) * (lam * poisson_pmf lam (SUC k)) =
      lam * (&(SUC k) * poisson_pmf lam (SUC k))` SUBST1_TAC THENL
    [REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     MATCH_ACCEPT_TAC REAL_MUL_SYM; ALL_TAC] THEN
    REWRITE_TAC[POISSON_PMF_RECURSION] THEN
    REWRITE_TAC[REAL_POW_2; GSYM REAL_MUL_ASSOC]; ALL_TAC] THEN
   MP_TAC(REWRITE_RULE[REAL_MUL_RID]
     (SPEC `(lam:real) pow 2`
       (MATCH_MP REAL_SERIES_LMUL (SPEC `lam:real` POISSON_PMF_SUMS)))) THEN
   REWRITE_TAC[ETA_AX];
   (* f(0) = 0 *)
   BETA_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
   (* f(1) = 0 *)
   BETA_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC]);;

(* Second moment: E[X^2] = lam^2 + lam *)
let POISSON_SECOND_MOMENT = prove
 (`!lam. &0 <= lam ==>
   ((\k. &k pow 2 * poisson_pmf lam k) real_sums (lam pow 2 + lam)) (from 0)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `((\k. &k * (&k - &1) * poisson_pmf lam k) real_sums lam pow 2) (from 0)`
    ASSUME_TAC THENL [ASM_SIMP_TAC[POISSON_SECOND_FACTORIAL_MOMENT]; ALL_TAC] THEN
  SUBGOAL_THEN
    `((\k. &k * poisson_pmf lam k) real_sums lam) (from 0)`
    ASSUME_TAC THENL [ASM_SIMP_TAC[POISSON_MEAN_SERIES]; ALL_TAC] THEN
  SUBGOAL_THEN
    `((\k. &k * (&k - &1) * poisson_pmf lam k + &k * poisson_pmf lam k)
      real_sums (lam pow 2 + lam)) (from 0)` MP_TAC THENL
  [MATCH_MP_TAC REAL_SERIES_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_SUMS_EQ) THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_FROM] THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

(* Variance: Var(X) = lam for Poisson(lam) *)
let POISSON_VARIANCE_SERIES = prove
 (`!lam. &0 <= lam ==>
   ((\k. (&k - lam) pow 2 * poisson_pmf lam k) real_sums lam) (from 0)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `((\k. &k pow 2 * poisson_pmf lam k) real_sums (lam pow 2 + lam)) (from 0)`
    ASSUME_TAC THENL [ASM_SIMP_TAC[POISSON_SECOND_MOMENT]; ALL_TAC] THEN
  SUBGOAL_THEN
    `((\k. &k * poisson_pmf lam k) real_sums lam) (from 0)`
    ASSUME_TAC THENL [ASM_SIMP_TAC[POISSON_MEAN_SERIES]; ALL_TAC] THEN
  SUBGOAL_THEN `(poisson_pmf lam real_sums &1) (from 0)` ASSUME_TAC THENL
  [REWRITE_TAC[POISSON_PMF_SUMS]; ALL_TAC] THEN
  SUBGOAL_THEN
    `((\k. (-- &2 * lam) * &k * poisson_pmf lam k) real_sums
     (-- &2 * lam) * lam) (from 0)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_SERIES_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `((\k. lam pow 2 * poisson_pmf lam k) real_sums
     lam pow 2 * &1) (from 0)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_SERIES_LMUL THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  SUBGOAL_THEN
    `((\k. &k pow 2 * poisson_pmf lam k +
           (-- &2 * lam) * &k * poisson_pmf lam k) real_sums
     (lam pow 2 + lam) + (-- &2 * lam) * lam) (from 0)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_SERIES_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `((\k. (&k pow 2 * poisson_pmf lam k +
            (-- &2 * lam) * &k * poisson_pmf lam k) +
           lam pow 2 * poisson_pmf lam k) real_sums
     ((lam pow 2 + lam) + (-- &2 * lam) * lam) +
     lam pow 2 * &1) (from 0)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_SERIES_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `((lam pow 2 + lam) + (-- &2 * lam) * lam) + lam pow 2 * &1 = lam`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
  [REWRITE_TAC[REAL_MUL_RID; REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `(\k. (&k - lam) pow 2 * poisson_pmf lam k) =
     (\k. (&k pow 2 * poisson_pmf lam k +
           (-- &2 * lam) * &k * poisson_pmf lam k) +
          lam pow 2 * poisson_pmf lam k)` SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
   REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
   ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Discrete LOTUS and Distribution Characteristic Function Bridge            *)
(*                                                                           *)
(* Connects the probability-space char fn (expectation) to the analytical    *)
(* series formulas for discrete distributions (Poisson, Geometric).          *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Definition: X has discrete distribution with PMF on {0, 1, 2, ...}.       *)
(*                                                                           *)
(* Condition 5: LOTUS for bounded functions (used for char fn bridges).      *)
(* Condition 6: LOTUS for integrable functions (used for E/Var bridges).     *)
(* ------------------------------------------------------------------------- *)

let has_pmf = new_definition
  `has_pmf (p:A prob_space) (X:A->real) (pmf:num->real) <=>
   random_variable p X /\
   (!k. &0 <= pmf k) /\
   (pmf real_sums &1) (from 0) /\
   (!k. prob p {x | x IN prob_carrier p /\ X x = &k} = pmf k) /\
   (!g M. (!u. abs(g u) <= M) /\ random_variable p (\x. g(X x))
     ==> integrable p (\x. g(X x)) /\
         ((\k. g(&k) * pmf k) real_sums
          expectation p (\x. g(X x))) (from 0)) /\
   (!g. integrable p (\x. g(X x))
     ==> ((\k. g(&k) * pmf k) real_sums
          expectation p (\x. g(X x))) (from 0))`;;

(* Basic consequences *)

let HAS_PMF_RV = prove
 (`!p:A prob_space X pmf. has_pmf p X pmf ==> random_variable p X`,
  REWRITE_TAC[has_pmf] THEN MESON_TAC[]);;

let HAS_PMF_NONNEG = prove
 (`!p:A prob_space X pmf. has_pmf p X pmf ==> !k. &0 <= pmf k`,
  REWRITE_TAC[has_pmf] THEN MESON_TAC[]);;

let HAS_PMF_SUMS_ONE = prove
 (`!p:A prob_space X pmf. has_pmf p X pmf
   ==> (pmf real_sums &1) (from 0)`,
  REWRITE_TAC[has_pmf] THEN MESON_TAC[]);;

let HAS_PMF_PROB = prove
 (`!p:A prob_space X pmf k.
   has_pmf p X pmf
   ==> prob p {x | x IN prob_carrier p /\ X x = &k} = pmf k`,
  REWRITE_TAC[has_pmf] THEN MESON_TAC[]);;

(* LOTUS for cos and sin (the cases needed for char fn) *)

let LOTUS_PMF_COS = prove
 (`!p:A prob_space X (pmf:num->real) t.
   has_pmf p X pmf
   ==> integrable p (\x. cos(t * X x)) /\
       ((\k. cos(t * &k) * pmf k) real_sums
        expectation p (\x. cos(t * X x))) (from 0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[has_pmf]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`\u:real. cos(t * u)`; `&1`]) THEN
  REWRITE_TAC[COS_BOUND] THEN ANTS_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_COS THEN
   MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[];
   SIMP_TAC[]]);;

let LOTUS_PMF_SIN = prove
 (`!p:A prob_space X (pmf:num->real) t.
   has_pmf p X pmf
   ==> integrable p (\x. sin(t * X x)) /\
       ((\k. sin(t * &k) * pmf k) real_sums
        expectation p (\x. sin(t * X x))) (from 0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[has_pmf]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`\u:real. sin(t * u)`; `&1`]) THEN
  REWRITE_TAC[SIN_BOUND] THEN ANTS_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_SIN THEN
   MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[];
   SIMP_TAC[]]);;

(* LOTUS for integrable functions (needed for E/Var) *)

let LOTUS_PMF_INTEGRABLE = prove
 (`!p:A prob_space X (pmf:num->real) g.
   has_pmf p X pmf /\ integrable p (\x. g(X x))
   ==> ((\k. g(&k) * pmf k) real_sums
        expectation p (\x. g(X x))) (from 0)`,
  REWRITE_TAC[has_pmf] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Distribution predicates                                                   *)
(* ------------------------------------------------------------------------- *)

let poisson_distributed = new_definition
  `poisson_distributed (p:A prob_space) (X:A->real) lam <=>
   has_pmf p X (poisson_pmf lam) /\ &0 <= lam /\
   integrable p X /\
   integrable p (\x. (X x - lam) pow 2)`;;

let geometric_distributed = new_definition
  `geometric_distributed (p:A prob_space) (X:A->real) q <=>
   has_pmf p X (geometric_pmf q) /\ &0 < q /\ q <= &1 /\
   integrable p X /\
   integrable p (\x. (X x - (&1 - q) / q) pow 2)`;;

(* ------------------------------------------------------------------------- *)
(* Bridge theorems: char fn of Poisson distributed RV                        *)
(* ------------------------------------------------------------------------- *)

let CHAR_FN_RE_POISSON_DIST = prove
 (`!p:A prob_space X lam t.
   poisson_distributed p X lam
   ==> char_fn_re p X t =
       exp(lam * (cos t - &1)) * cos(lam * sin t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[poisson_distributed] THEN STRIP_TAC THEN
  REWRITE_TAC[char_fn_re] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `t:real` o MATCH_MP LOTUS_PMF_COS) THEN
  MATCH_MP_TAC REAL_SERIES_UNIQUE THEN
  EXISTS_TAC `\k:num. cos(t * &k) * poisson_pmf lam k` THEN
  EXISTS_TAC `from 0` THEN
  CONJ_TAC THENL
  [FIRST_ASSUM ACCEPT_TAC;
   MATCH_MP_TAC POISSON_CHAR_FN_RE THEN ASM_REWRITE_TAC[]]);;

let CHAR_FN_IM_POISSON_DIST = prove
 (`!p:A prob_space X lam t.
   poisson_distributed p X lam
   ==> char_fn_im p X t =
       exp(lam * (cos t - &1)) * sin(lam * sin t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[poisson_distributed] THEN STRIP_TAC THEN
  REWRITE_TAC[char_fn_im] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `t:real` o MATCH_MP LOTUS_PMF_SIN) THEN
  MATCH_MP_TAC REAL_SERIES_UNIQUE THEN
  EXISTS_TAC `\k:num. sin(t * &k) * poisson_pmf lam k` THEN
  EXISTS_TAC `from 0` THEN
  CONJ_TAC THENL
  [FIRST_ASSUM ACCEPT_TAC;
   MATCH_MP_TAC POISSON_CHAR_FN_IM THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Bridge theorems: char fn of Geometrically distributed RV                  *)
(* ------------------------------------------------------------------------- *)

let CHAR_FN_RE_GEOMETRIC_DIST = prove
 (`!p:A prob_space X q t.
   geometric_distributed p X q
   ==> char_fn_re p X t =
       q * (&1 - (&1 - q) * cos t) /
       (&1 - &2 * (&1 - q) * cos t + (&1 - q) pow 2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[geometric_distributed] THEN STRIP_TAC THEN
  REWRITE_TAC[char_fn_re] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `t:real` o MATCH_MP LOTUS_PMF_COS) THEN
  MATCH_MP_TAC REAL_SERIES_UNIQUE THEN
  EXISTS_TAC `\k:num. cos(t * &k) * geometric_pmf q k` THEN
  EXISTS_TAC `from 0` THEN
  CONJ_TAC THENL
  [FIRST_ASSUM ACCEPT_TAC;
   MATCH_MP_TAC GEOMETRIC_CHAR_FN_RE THEN ASM_REWRITE_TAC[]]);;

let CHAR_FN_IM_GEOMETRIC_DIST = prove
 (`!p:A prob_space X q t.
   geometric_distributed p X q
   ==> char_fn_im p X t =
       q * (&1 - q) * sin t /
       (&1 - &2 * (&1 - q) * cos t + (&1 - q) pow 2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[geometric_distributed] THEN STRIP_TAC THEN
  REWRITE_TAC[char_fn_im] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `t:real` o MATCH_MP LOTUS_PMF_SIN) THEN
  MATCH_MP_TAC REAL_SERIES_UNIQUE THEN
  EXISTS_TAC `\k:num. sin(t * &k) * geometric_pmf q k` THEN
  EXISTS_TAC `from 0` THEN
  CONJ_TAC THENL
  [FIRST_ASSUM ACCEPT_TAC;
   MATCH_MP_TAC GEOMETRIC_CHAR_FN_IM THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Bridge theorems: Expectation and Variance                                 *)
(* ------------------------------------------------------------------------- *)

let EXPECTATION_POISSON_DIST = prove
 (`!p:A prob_space X lam.
   poisson_distributed p X lam
   ==> expectation p X = lam`,
  REPEAT GEN_TAC THEN REWRITE_TAC[poisson_distributed] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_SERIES_UNIQUE THEN
  EXISTS_TAC `\k:num. &k * poisson_pmf lam k` THEN
  EXISTS_TAC `from 0` THEN CONJ_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `poisson_pmf lam`;
                   `\u:real. u`] LOTUS_PMF_INTEGRABLE) THEN
   BETA_TAC THEN REWRITE_TAC[ETA_AX] THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  ASM_SIMP_TAC[POISSON_MEAN_SERIES]);;

let VARIANCE_POISSON_DIST = prove
 (`!p:A prob_space X lam.
   poisson_distributed p X lam
   ==> variance p X = lam`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `expectation p (X:A->real) = lam` ASSUME_TAC THENL
  [ASM_MESON_TAC[EXPECTATION_POISSON_DIST]; ALL_TAC] THEN
  REWRITE_TAC[variance] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `poisson_distributed p (X:A->real) lam` THEN
  REWRITE_TAC[poisson_distributed] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_SERIES_UNIQUE THEN
  EXISTS_TAC `\k:num. (&k - lam) pow 2 * poisson_pmf lam k` THEN
  EXISTS_TAC `from 0` THEN CONJ_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `poisson_pmf lam`;
                   `\u:real. (u - lam) pow 2`] LOTUS_PMF_INTEGRABLE) THEN
   BETA_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  ASM_SIMP_TAC[POISSON_VARIANCE_SERIES]);;

let EXPECTATION_GEOMETRIC_DIST = prove
 (`!p:A prob_space X q.
   geometric_distributed p X q
   ==> expectation p X = (&1 - q) / q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[geometric_distributed] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_SERIES_UNIQUE THEN
  EXISTS_TAC `\k:num. &k * geometric_pmf q k` THEN
  EXISTS_TAC `from 0` THEN CONJ_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `geometric_pmf q`;
                   `\u:real. u`] LOTUS_PMF_INTEGRABLE) THEN
   BETA_TAC THEN REWRITE_TAC[ETA_AX] THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  ASM_SIMP_TAC[GEOMETRIC_MEAN_SERIES]);;

let VARIANCE_GEOMETRIC_DIST = prove
 (`!p:A prob_space X q.
   geometric_distributed p X q
   ==> variance p X = (&1 - q) / q pow 2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `expectation p (X:A->real) = (&1 - q) / q` ASSUME_TAC THENL
  [ASM_MESON_TAC[EXPECTATION_GEOMETRIC_DIST]; ALL_TAC] THEN
  REWRITE_TAC[variance] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `geometric_distributed p (X:A->real) q` THEN
  REWRITE_TAC[geometric_distributed] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_SERIES_UNIQUE THEN
  EXISTS_TAC `\k:num. (&k - (&1 - q) / q) pow 2 * geometric_pmf q k` THEN
  EXISTS_TAC `from 0` THEN CONJ_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `geometric_pmf q`;
                   `\u:real. (u - (&1 - q) / q) pow 2`]
    LOTUS_PMF_INTEGRABLE) THEN
   BETA_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  ASM_SIMP_TAC[GEOMETRIC_VARIANCE_SERIES]);;

(* ------------------------------------------------------------------------- *)
(* Bridge theorems: Binomial characteristic function                         *)
(* ------------------------------------------------------------------------- *)

let CHAR_FN_RE_BINOMIAL_RV = prove
 (`!p:A prob_space X n q t. binomial_rv p X n q ==>
   char_fn_re p X t =
   sum (0..n) (\k. &(binom(n,k)) * q pow k * (&1 - q) pow (n - k) *
                   cos(t * &k))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `simple_rv p (X:A->real)` ASSUME_TAC THENL
  [ASM_MESON_TAC[binomial_rv]; ALL_TAC] THEN
  SUBGOAL_THEN `char_fn_re p (X:A->real) t = simple_char_fn_re p X t`
    SUBST1_TAC THENL
  [ASM_SIMP_TAC[CHAR_FN_RE_SIMPLE]; ALL_TAC] THEN
  ASM_SIMP_TAC[BINOMIAL_CHAR_FN_RE]);;

let CHAR_FN_IM_BINOMIAL_RV = prove
 (`!p:A prob_space X n q t. binomial_rv p X n q ==>
   char_fn_im p X t =
   sum (0..n) (\k. &(binom(n,k)) * q pow k * (&1 - q) pow (n - k) *
                   sin(t * &k))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `simple_rv p (X:A->real)` ASSUME_TAC THENL
  [ASM_MESON_TAC[binomial_rv]; ALL_TAC] THEN
  SUBGOAL_THEN `char_fn_im p (X:A->real) t = simple_char_fn_im p X t`
    SUBST1_TAC THENL
  [ASM_SIMP_TAC[CHAR_FN_IM_SIMPLE]; ALL_TAC] THEN
  ASM_SIMP_TAC[BINOMIAL_CHAR_FN_IM]);;
